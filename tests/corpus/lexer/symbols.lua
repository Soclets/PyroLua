local a, b = 1, 2
local c = a + b - a * b / a // b % a ^ b
local d = a & b | b ~ a << 1 >> 1 .. ''
local e = a == b, a ~= b, a <= b, a >= b, a < b, a > b, #'x', -a, ~a
local t = {[1] = 2; x = 3}
local y = t.x, t[1]
