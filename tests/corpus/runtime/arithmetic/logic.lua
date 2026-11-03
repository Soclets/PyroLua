-- not, and unary minus on numbers.
local t, f, n = true, false, nil
print(not t, not f, not n, not 0, not "")
local i, x = 42, 4.5
print(-i, -x, - -i, -(-x), -0, -0.0)
local z = 0.0
print(-z, - -z)
