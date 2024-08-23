# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys

import io 
import z3

from functools import reduce
from . import ast, int
import random

class DynamicSymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.sym_env = dict()
        self.con_env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()
        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        con_dict = dict()
        for (k, v) in self.sym_env.items():
            # Get the values to be concrete
            con_dict[k] = model.eval(v, model_completion=True).as_long()
        return con_dict
    
    def pick_concrete(self):
        return self.pick_concerete()

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = DynamicSymState()
        child.sym_env = dict(self.sym_env)
        child.con_env = dict(self.con_env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.sym_env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class DynamicSymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        kwargs = dict()
        kwargs["state"] = state
        kwargs["env"] = "concrete"
        args = []
        return [kwarg["state"] for kwarg in self.visit(ast, *args, **kwargs) if not kwarg["state"].is_error()]

    def visit_IntVar(self, node, *args, **kwargs):
        if kwargs["env"] == "concrete":
            return kwargs["state"].con_env[node.name]
        elif kwargs["env"] == "symbolic":
            return kwargs["state"].sym_env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        if kwargs["env"] == "concrete":
            return node.val
        elif kwargs["env"] == "symbolic":
            return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        if kwargs["env"] == "concrete":
            return node.val
        elif kwargs["env"] == "symbolic":
            return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        # print(node.arg(0), node.arg(1), "WOWWW")
        # print(kwargs["env"])
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        # print(kwargs["env"], type(lhs), type(rhs), type(lhs <= rhs))
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs
        assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        if kwargs["env"] == "symbolic":
            if node.op == 'and':
                fn = lambda x, y: z3.And(x, y)
            elif node.op == 'or':
                fn = lambda x, y: z3.Or(x, y)
            elif node.op == 'not':
                assert len(kids) == 1
                assert node.is_unary()
                return z3.Not(kids[0])
            assert fn is not None
            return reduce(fn, kids)
        else:
            if node.op == "not":
                assert node.is_unary()
                assert len(kids) == 1
                return not kids[0]
            fn = None
            base = None
            if node.op == "and":
                fn = lambda x, y: x and y
                base = True
            elif node.op == "or":
                fn = lambda x, y: x or y
                base = False
            assert fn is not None
            return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None
        if node.op == "+":
            fn = lambda x, y: x + y
        elif node.op == "-":
            fn = lambda x, y: x - y
        elif node.op == "*":
            fn = lambda x, y: x * y
        elif node.op == "/":
            fn = lambda x, y: x / y
        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
        return [kwargs]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs["state"]

        sym_dict = kwargs.copy()
        sym_dict["env"] = "symbolic"
        st.sym_env[node.lhs.name] = self.visit(node.rhs, *args, **sym_dict)

        con_dict = kwargs.copy()
        con_dict["env"] = "concrete"
        st.con_env[node.lhs.name] = self.visit(node.rhs, *args, **con_dict)

        res_dict = kwargs.copy()
        res_dict["state"] = st
        return [res_dict]


    def visit_IfStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        # cond = self.visit(node.cond, state=state)  # Evaluate the condition 
        
        all_kwargs = []
        sym_kwarg = kwargs.copy()
        sym_kwarg["env"] = "symbolic"
        sym_cond = self.visit(node.cond, *args, **sym_kwarg)
        # print(sym_cond, type(sym_cond), "WOW")
        st1, st2 = state.fork()
        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))

        # Concrete Execution    
        conc_kwarg = kwargs.copy()
        conc_kwarg["env"] = "concrete"
        conc_cond = self.visit(node.cond, *args, **conc_kwarg)
        # for key in conc_kwarg["state"].con_env:
        #     print(key, conc_kwarg["state"].con_env[key], type(conc_kwarg["state"].con_env[key]))
        # print(conc_cond, type(conc_cond), "LOL")

        if conc_cond:
            con_if_dict = kwargs.copy()
            con_if_dict["state"] = st1
            all_kwargs.extend(self.visit(node.then_stmt, *args, **con_if_dict))
        else:
            con_else_dict = kwargs.copy()
            con_else_dict["state"] = st2
            # print(con_else_dict["env"])
            if node.has_else():
                all_kwargs.extend(self.visit(node.else_stmt, *args, **con_else_dict))
            # else:
            #     all_kwargs.extend([con_else_dict])

        # Symbolic Execution
        if not st1.is_empty():
            then_true_dict = kwargs.copy()
            st1.con_env = st1.pick_concrete()
            then_true_dict["state"] = st1
            all_kwargs.extend(self.visit(node.then_stmt, *args, **then_true_dict))
        else:
            st1.mk_error()
            then_false_dict = kwargs.copy()
            then_false_dict["state"] = st1
            # all_kwargs.extend([then_false_dict])
        
        if not st2.is_empty():
            else_true_dict = kwargs.copy()
            st2.con_env = st2.pick_concrete()
            else_true_dict["state"] = st2
            if node.has_else():
                all_kwargs.extend(self.visit(node.else_stmt, *args, **else_true_dict))
            else:
                all_kwargs.extend([else_true_dict])
        else:
            st2.mk_error()
            else_false_dict = kwargs.copy()
            else_false_dict["state"] = st2
            # all_kwargs.extend([else_false_dict])

        return all_kwargs

    def visit_WhileStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        loop_limit = 10  # Set the maximum number of loop iterations to consider
        all_kwargs = []

        sym_kwarg = kwargs.copy()
        sym_kwarg["env"] = "symbolic"
        sym_cond = self.visit(node.cond, *args, **sym_kwarg)
        st1, st2 = state.fork()
        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))
        loop_cnt = 0 if len(args) == 0 else args[0]

        conc_kwarg = kwargs.copy()
        conc_kwarg["env"] = "concrete"
        # print(type(node.cond))
        conc_cond = self.visit(node.cond, *args, **conc_kwarg)
        
        # Concrete Execution
        if conc_cond:
            if loop_cnt < 10:
                body_conc_kwarg = kwargs.copy()
                body_conc_kwarg["state"] = st1

                body_conc_dict = self.visit(node.body, 0, **body_conc_kwarg)
                for i in range(len(body_conc_dict)):
                    if not body_conc_dict[i]["state"].is_error():
                        all_kwargs.extend(self.visit(node, loop_cnt+1, **body_conc_dict[i]))
                # loop_conc_dict = self.visit(node, loop_cnt+1, **body_conc_dict[0])
                # all_kwargs.extend(loop_conc_dict)
        
        else:
            # st2.mk_error()
            exit_conc_kwarg = kwargs.copy()
            exit_conc_kwarg["state"] = st2
            # all_kwargs.extend([exit_conc_kwarg])

        # Symbolic Execution
        if not st1.is_empty() and loop_cnt < loop_limit:
            body_sym_kwarg = kwargs.copy()
            st1.con_env = st1.pick_concrete()
            body_sym_kwarg["state"] = st1
            body_sym_kwarg["env"] = "symbolic"
            body_sym_dict = self.visit(node.body, 0, **body_sym_kwarg)

            # new_kwargs_list = []
            for i in range(len(body_sym_dict)):
                if not body_sym_dict[i]["state"].is_error():
                    all_kwargs.extend(self.visit(node, loop_cnt+1, **body_sym_dict[i]))
        else:
            st1.mk_error()
        #     body_sym_kwarg = kwargs.copy()
        #     body_sym_kwarg["state"] = st1
            # all_kwargs.extend([body_sym_kwarg])

        if not st2.is_empty():
            exit_sym_kwarg = kwargs.copy()
            st2.con_env = st2.pick_concrete()
            exit_sym_kwarg["state"] = st2
            all_kwargs.extend([exit_sym_kwarg])
        else:
            st2.mk_error()
            # exit_sym_kwarg = kwargs.copy()
            # exit_sym_kwarg["state"] = st2
            # all_kwargs.extend([exit_sym_kwarg])

        return all_kwargs


    def visit_AssertStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        sym_kwarg = kwargs.copy()
        sym_kwarg["env"] = "symbolic"
        sym_cond = self.visit(node.cond, *args, **sym_kwarg)
        st1, st2 = state.fork()
        st1.add_pc(sym_cond)
        st2.add_pc(z3.Not(sym_cond))

        con_kwarg = kwargs.copy()
        con_kwarg["env"] = "concrete"
        con_cond = self.visit(node.cond, *args, **con_kwarg)
        all_kwargs = []

        if con_cond:
            con_kwarg["state"] = st1
            all_kwargs.extend([con_kwarg])
        # else:
        #     st1.mk_error()

        if not st1.is_empty():
            assert_true_sym = kwargs.copy()
            st1.con_env = st1.pick_concrete()
            assert_true_sym["state"] = st1
            all_kwargs.extend([assert_true_sym])
        else:
            st1.mk_error()

        if not st2.is_empty():
            st2.mk_error()
            assert_false_sym = kwargs.copy()
            assert_false_sym["state"] = st2
            all_kwargs.extend([assert_false_sym])
        
        return all_kwargs

    def visit_AssumeStmt(self, node, *args, **kwargs):
        return self.visit_AssertStmt(node, *args, **kwargs)

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        for v in node.vars:
            state.sym_env[v.name] = z3.FreshInt(v.name)
            state.con_env[v.name] = 0
        res = kwargs.copy()
        res["state"] = state
        return [res]
    
    def visit_StmtList(self, node, *args, **kwargs):
        kwarg_dict = [kwargs.copy()]
        if node.stmts is None:
            return
        for stmt in node.stmts:
            kwarg_dict_new = []
            for i in range(len(kwarg_dict)):
                if not kwarg_dict[i]["state"].is_error():
                    kwarg_dict_new.extend(self.visit(stmt, *args, **kwarg_dict[i]))
            kwarg_dict = kwarg_dict_new
        return [kwarg for kwarg in kwarg_dict if not kwarg["state"].is_error()]


def _parse_args(): # pragma: no cover
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main(): # pragma: no cover
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = DynamicSymState()
    sym = DynamicSymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__': # pragma: no cover
    sys.exit(main())
