havoc x, y; 
if (x > 0 and y < 0) then x := x + 1 else y := y - 1; 
assume y > x; 
assert y > x + 100; 
while y > x do {havoc x; y := y + x}