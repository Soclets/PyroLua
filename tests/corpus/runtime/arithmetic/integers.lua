-- Integer arithmetic: wrapping, floor division and modulo with every sign.
local max = 9223372036854775807
local min = -max - 1
print(1 + 2, 7 - 10, 6 * 7, max + 1, min - 1, max * 2)
local function show(a, b)
  print(a, b, a // b, a % b, a / b)
end
show(7, 3) show(-7, 3) show(7, -3) show(-7, -3) show(0, 5) show(min, -1)
print(min // -1, min % -1, -min, - -5)
print(2 ^ 10, 10 / 2, 3 // 0.0, -3 // 0.0)
local x = 5
print(x + 1, x - 1, x * x, x // 2, x % 2, x / 2, x ^ 2)
print(x + 0.5, x - 0.5, x * 0.5, x // 0.5, x % 0.5)
print(1 + 1.0, 3 - 1.0, 2 * 2.5, 7 // 2.0, 7 % 2.5, -7 % 2.5, 7 % -2.5)
print(x + 300, x - 300, 300 - x, x * 1000, x // 7, 7 // x, x % -3, -3 % x)
