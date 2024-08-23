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


class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
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
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st
    
    def pick_concrete(self):
        return self.pick_concerete()

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class SymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return [st for st in self.visit(ast, state=state) if not st.is_error()]
        # return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs["state"].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
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

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        # if isinstance(state, list):
        #     return [self.visit(node, state=s) for s in state]
        # Handle boolean expressions with logical operators
        if node.op == 'and':
            fn = lambda x, y: z3.And(x, y)
        elif node.op == 'or':
            fn = lambda x, y: z3.Or(x, y)
        elif node.op == 'not':
            assert len(kids) == 1
            assert node.is_unary()
            return z3.Not(kids[0])
        
        return reduce(fn, kids)

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
        return [kwargs["state"]]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
        return [kwargs["state"]]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        state.env[node.lhs.name] = self.visit(node.rhs, state=state)
        return [state]

    def visit_IfStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        cond = self.visit(node.cond, state=state)  # Evaluate the condition
        st1, st2 = state.fork()
        st1.add_pc(cond)
        st2.add_pc(z3.Not(cond))
        all_states = []
        
        if not st1.is_empty():
            st1 = self.visit(node.then_stmt, state=st1)
            all_states.extend(st1)
        else:
            st1.mk_error()
            all_states.extend([st1])
        
        # Fork the state for the false branch
        if not st2.is_empty():
            if node.has_else():
                st2 = self.visit(node.else_stmt, state=st2)
                all_states.extend(st2)
            else:
                all_states.extend([st2])
        else:
            st2.mk_error()
            all_states.extend([st2])

        return all_states

    def visit_WhileStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        loop_limit = 10  # Set the maximum number of loop iterations to consider
        all_states = []
        # add invariants
        if not node.inv == None:
            st_inv1, st_inv2 = state.fork()
            inv = self.visit(node.inv, state=state)
            st_inv1.add_pc(inv)
            st_inv2.add_pc(z3.Not(inv))
            if st_inv1.is_empty():
                st_inv1.mk_error()
                return [st_inv1]
            if not st_inv2.is_empty():
                st_inv2.mk_error()
            state = st_inv1

        cond = self.visit(node.cond, state=state)
        st1, st2 = state.fork()
        st1.add_pc(cond)
        st2.add_pc(z3.Not(cond))
        loop_cnt = 0 if len(args) == 0 else args[0]

        if not st1.is_empty() and loop_cnt < loop_limit:
            st1 = self.visit(node.body, 0, state=st1)
            new_states = []
            for i in range(len(st1)):
                if not st1[i].is_error():
                    new_states.extend(self.visit_WhileStmt(node, loop_cnt+1, state=st1[i]))
            st1 = new_states
            all_states = st1
        else:
            st1.mk_error()
            all_states = [st1]
        
        if not st2.is_empty():
            all_states.extend([st2])
        else:
            st2.mk_error()
            all_states.extend([st2])
        return all_states


    def visit_AssertStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        cond = self.visit(node.cond, state=state)
        st1, st2 = state.fork()

        st1.add_pc(cond)
        st2.add_pc(z3.Not(cond))

        all_states = []
        if not st1.is_empty():
            all_states.extend([st1])

        if not st2.is_empty():
            st2.mk_error()
            all_states.extend([st2])
        
        return all_states

    def visit_AssumeStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        cond = self.visit(node.cond, state=state)
        state.add_pc(cond)
        if state.is_empty():
            state.mk_error()
        
        return [state]

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        for v in node.vars:
            state.env[v.name] = z3.FreshInt(v.name)
        return [state]
    
    def visit_StmtList(self, node, *args, **kwargs):
        states = [kwargs['state']]
        if node.stmts is None:
            return
        for stmt in node.stmts:
            new_states = []
            for i in range(len(states)):
                if not states[i].is_error():
                    new_states.extend(self.visit(stmt, state=states[i]))
            states = new_states
        return [st for st in states if not st.is_error()]


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
    st = SymState()
    sym = SymExec()

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
