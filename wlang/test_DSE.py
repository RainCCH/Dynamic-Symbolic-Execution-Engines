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
from . import ast, DSE


class TestDSE (unittest.TestCase):
    def test_one(self):
        prg1 = "havoc x; if x = 0 then x := 5 else x := 10; print_state"
        ast1 = ast.parse_string(prg1)
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        print(len(out))
        
    def test_two(self):
        ast1 = ast.parse_file(os.path.join(os.getcwd(), 'wlang/test6.prg'))
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        # print(len(out))
        print("test 2:", len(out))
        # self.assertEquals(len(out), 10)

    def test_three(self):
        prg1 = "havoc x, y"
        # prg1 += "; if x + y < 15 then skip else skip"
        prg1 += "; if x + y < 15 then { x := x + 7; y := y - 12} else { y := y + 10; x := x - 2 }"
        prg1 += "; x := x + 2"
        # prg1 += "; if x > 15 then skip else skip"
        prg1 += "; if 2 * (x + y) > 21 then { x := x * 3; y := y * 2 } else {x := x * 4; y := y * 3 + x }"
        # prg1 += "; skip"
        engine = DSE.DynamicSymExec()
        ast1 = ast.parse_string(prg1)
        st1 = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st1)]
        print("Test 3:", len(out))
        # self.assertEquals(len(out), 2)

    def test_four(self):
        prg1 = "x := 8; havoc y; if (x > 0 and y < 0) then x := x + 1 else y := y - 1; assume y > x; assert y > x + 100; while y > x do {havoc x; y := y + x}"
        ast1 = ast.parse_string(prg1)
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        print("test 4:", len(out))

    def test_five(self):
        prg1 = "havoc x; r := 0"
        prg1 += "; if x > 8 then r := x - 7"
        prg1 += "; if x < 5 then r := x - 2"
        ast1 = ast.parse_string(prg1)
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        print("test 5:", len(out))

        prg1 = "while false do skip"
        ast1 = ast.parse_string(prg1)
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        print("test 6:", len(out))

        prg1 = "assert 0 = 1"
        ast1 = ast.parse_string(prg1)
        engine = DSE.DynamicSymExec()
        st = DSE.DynamicSymState()
        out = [s for s in engine.run(ast1, st)]
        print("test 7:", len(out))