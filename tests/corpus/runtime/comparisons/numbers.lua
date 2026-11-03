-- Comparisons of numbers: integers, floats, mixed, exactly; NaN; -0.0.
local i, f, big = 3, 3.0, 9007199254740993
local nan = 0 / 0.0
print(i == f, i < f, i <= f, 2 < f, f < 4, -0.0 == 0.0, nan == nan, nan < nan, nan <= 1)
print(big == 2^53, big < 2^53 + 2, big > 2^53, 2^53 < big, 2^63 > 9223372036854775807)
print(-9223372036854775807 - 1 == -2^63, 9223372036854775807 < 2^63, 1/0 > 9223372036854775807)
local a, b = 10, 20
print(a < b, a <= b, a > b, a >= b, a == b, a ~= b)
print(a < 15, a <= 10, a > 5, a >= 11, a == 10, a ~= 10, a < 10.5, a > 9.5, a == 10.0)
print(f < 15, f <= 3, f > 5, f >= 3, f == 3, nan < 1, nan > 1, nan == 1)
if a < b then print("less") else print("not less") end
while a < 13 do a = a + 1 end
print(a)
