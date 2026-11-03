-- Bitwise operators: integers, integral floats, shifts past 63 and negative shifts.
local a, b = 0xF0F0, 0x0FF0
print(a & b, a | b, a ~ b, ~a, ~0)
print(1 << 62, 1 << 63, 1 << 64, 1 << -1, 256 >> 4, 256 >> -4, -1 >> 1, -1 >> 64)
local n = 3
print(n << 2, n >> 1, 2 << n, 1024 >> n, n & 1, n | 4, n ~ 1, ~n)
print(3.0 & 1, 2.0 | 1.0, 1 << 2.0, ~5.0)
local f = 6.0
print(f & 3, f | 1, f ~ 2, f << 1, f >> 1, 1 << f, ~f)
print(n << 70, n >> 70, n << -1, n >> -1, -1 << 63)
