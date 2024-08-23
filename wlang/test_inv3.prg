havoc n;
v := 1;
if (n <= 1) then skip else {i := 2; while i <= n inv not (i <= n + 1) do {v := i * v; i := i + 1}}