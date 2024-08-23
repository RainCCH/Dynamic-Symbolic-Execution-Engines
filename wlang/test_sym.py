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

import unittest
import os
from . import ast, sym


class TestSym (unittest.TestCase):
    def test_one(self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
        self.assertFalse(out[0].is_error())
        self.assertFalse(out[0].is_empty())
        self.assertIsNotNone(out[0].pick_concrete())
        self.assertEqual(str(st), repr(st))
        self.assertEqual(st.to_smt2(), st._solver.to_smt2())
        
    def test_two(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test2.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertIsNotNone(out[0].pick_concerete())
        self.assertEquals(len(out), 3)

    def test_three(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test3.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_four(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test4.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_five(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test5.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        # print("test 5:", len(out))
        self.assertEquals(len(out), 10)

    def test_seven(self):
        prg1 = "havoc x; havoc z; if x > 10 then {x := x + 1; z := 10}  else y := x + 1 ; x := z + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 2)

    def test_fault(self):
        prg1 = "assert false"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)
        # with self.assertRaises(SystemExit):
        #     sym.main()

    def test_inv(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test_inv.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)

        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test_inv2.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test_inv3.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        # self.assertEquals(len(out), 1)

        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/q4b.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)

        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/q4d.prg'))
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        # print("q4d: {}".format(len(out)))
        self.assertEquals(len(out), 1)