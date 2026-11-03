-- next and pairs, with keys sorted (the order of a hash part is not Lua's).
local function sorted_keys(t)
  local keys, n = {}, 0
  local k = next(t)
  while k ~= nil do
    n = n + 1
    keys[n] = k
    k = next(t, k)
  end
  local i = 2
  while i <= n do
    local j, key = i, keys[i]
    while j > 1 and tostring(keys[j - 1]) > tostring(key) do
      keys[j] = keys[j - 1]
      j = j - 1
    end
    keys[j] = key
    i = i + 1
  end
  return keys, n
end
local t = {1, 2, 3, a = "x", b = "y", c = "z", [10] = "ten"}
local keys, n = sorted_keys(t)
local i = 1
while i <= n do print(keys[i], t[keys[i]]); i = i + 1 end
print(next({}), next({}, nil))
local f, s, init = pairs(t)
print(f == next, s == t, init)
local custom = setmetatable({}, {__pairs = function (self) return "iter", self, "start" end})
local cf, cs, ci = pairs(custom)
print(cf, cs == custom, ci)
local g, gs, gi = ipairs({5, 6})
print(gs[1], gi, g(gs, 0))
print(g(gs, 1))
print(g(gs, 2))
local indexed = setmetatable({}, {__index = function (_, k) if k < 4 then return k * 100 end end})
print(g(indexed, 0), g(indexed, 2), g(indexed, 3))
print(pcall(next, {}, "missing"))
