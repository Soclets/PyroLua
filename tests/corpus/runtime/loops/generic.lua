-- Generic for loops over ipairs, pairs (sorted) and custom iterators.
local list = {10, 20, 30, nil, 50}
for i, v in ipairs(list) do print(i, v) end
local function range(n)
  local i = 0
  return function () i = i + 1; if i <= n then return i, i * i end end
end
for i, sq in range(4) do print(i, sq) end
local function stateless(limit, control)
  if control < limit then return control + 1 end
end
for i in stateless, 3, 0 do print(i) end
local t = {x = 1, y = 2, z = 3}
local keys = {}
for k in pairs(t) do keys[#keys + 1] = k end
local i = 2
while i <= #keys do
  local j, key = i, keys[i]
  while j > 1 and keys[j - 1] > key do keys[j] = keys[j - 1]; j = j - 1 end
  keys[j] = key
  i = i + 1
end
for _, k in ipairs(keys) do print(k, t[k]) end
local proxy = setmetatable({}, {__index = function (_, k) if k <= 3 then return k * 2 end end})
for i, v in ipairs(proxy) do print(i, v) end
for i, v in ipairs({}) do print("never") end
local count = 0
for _ in pairs({1, 2, 3, a = 4}) do count = count + 1 end
print(count)
local seen = 0
for k, v in next, {7, 8, 9} do seen = seen + v end
print(seen)
