havoc x, y;
if x + y > 15 then {x := x + 7; y := y - 12} else {x := x - 2; y := y + 12};
x := x + 10;
if 2*(x + y) > 21 then { x := x * 3; y := y * 2 } else {x := x * 4; y := y * 3 + x }