-- a <= b without __le: not (b < a) through __lt, as reference Lua built with
-- LUA_COMPAT_5_3 does; with neither, an error.

local log = {}
local Ordered = {}
Ordered.__lt = function (a, b)
  log[#log + 1] = a.n .. "<" .. b.n
  return a.n < b.n
end
local function new (n)
  return setmetatable ({n = n}, Ordered)
end
local one, two = new (1), new (2)
print (one <= two, two <= one, one <= one)
print (one >= two, two >= one)
print (not (one <= two), one < two, two > one)
for i = 1, #log do
  print (log[i])
end

-- Only the second operand has __lt: its __lt is used for both orders.
local plain = {n = 5}
print (pcall (function () return plain <= two end))
print (pcall (function () return two <= plain end))

-- __le, when present, is used instead.
local Both = {__lt = function () return true end, __le = function () return false end}
local x, y = setmetatable ({}, Both), setmetatable ({}, Both)
print (x <= y, x < y)

-- With immediate operands (LEI, GEI) and constants.
local Number = {__lt = function (a, b)
  local left = type (a) == "table" and a.n or a
  local right = type (b) == "table" and b.n or b
  return left < right
end}
local three = setmetatable ({n = 3}, Number)
print (three <= 3, three <= 2, three >= 4, three >= 3, 2 <= three, 4 <= three)

-- Neither metamethod: the order error.
print (pcall (function () return {} <= {} end))
print (pcall (function () return setmetatable ({}, {}) <= 1 end))
