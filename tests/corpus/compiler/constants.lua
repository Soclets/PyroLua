-- Constant folding and constant operands (lcode.c constfolding, validop, exp2K).
local a = 1 + 2 * 3 - 4 // 2 % 3
local b = 2^10, 7 / 2, -7 // 2, 7 % -3, -7 % 3, 7.5 % -2
local c = 1 / 0, -1 / 0, 0 / 0, 0.0 * -1, 1 // 0, 1 % 0
local d = 3 & 5 | 6 ~ 9, ~0, 1 << 63, 1 << 64, -1 >> 1, 2.0 & 3, 2.5 & 3
local e = "x" .. "y", -(-9223372036854775807 - 1), math.huge
local f <const> = 42
local g <const> = "a long string constant that is longer than forty bytes in total"
local h <const> = f * 2 + 0.5
local i = f + h, g .. g, -f, not f, #g
local j = 0.1 + 0.2, 1e308 * 10, -0.0, 1e-320, 3.0, -3.0, 65536.0, 65537.0, -65535.0
local k = 9007199254740993, 2^53, 2^63, -2^63, 1e15, 123456789012345
local l = 127, 128, -127, -128, 65535, 65536, -65535, -65536, 131071
local x, y = ...
local m = x + 1, x + 127, x + 128, x - 127, x - 128, 1 + x, x * 2, 2 * x, x / 3, x // 3
local n = x % 3, x ^ 2, x & 1, 1 & x, x | 2, x ~ 3, x << 1, x << 200, 1 << x, x >> 2, x >> -2
local o = x + 0.5, x - 1.5, x * 1e10, x + "s", x + y, x .. y .. "z" .. 1
local p = x == 1, x ~= 1.0, x == "s", x == nil, x == true, x == y, 1 == x, x < 1, 1 < x
local q = x <= 127, x > 128, x >= -1, 1.5 < x, x < 2.0, "a" < x, x > y, x >= y
local r = not x, not nil, not 1, not not x, -x, ~x, #x
return a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r
