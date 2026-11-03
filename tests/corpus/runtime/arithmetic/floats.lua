-- Float arithmetic and how floats print.
local zero = 0.0
print(1 / zero, -1 / zero, 0.1 + 0.2, 1e15, 1e16, 2^53, 2^63, -2^63)
print(3.0, -0.0, 100 / 3, 1 / 3, 1e300 * 1e10, -1e300 * 1e10)
local x = 2.5
print(-x, x // 1, x % 1, -x // 1, -x % 1, x ^ 0.5, 8 ^ (1 / 3))
print(5 // zero, -5 // zero, 5 % (1 / zero), -5 % (1 / zero))
print(7.5 // 2, 7.5 % 2, -7.5 // 2, -7.5 % 2, 7.5 % -2)
print(x + 1, x - 1, x * 2, x / 2, x // 2, x % 2, x ^ 2, 2 ^ x)
