a := 3;
b := 5;
x := a;
y := b;
z := 0;

while z < x and z < y inv (z = a - x and z = b - y) do
{
z := z + 1;
x := x - 1;
y := y - 1
};
print_state