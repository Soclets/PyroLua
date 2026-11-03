-- Closures capture variables, not values: shared, closed when their block ends, fresh per
-- iteration.
local function counter()
  local n = 0
  return function () n = n + 1; return n end, function () return n end
end
local inc, get = counter()
inc(); inc()
print(get(), inc(), get())
local other = counter()
print(other(), get())
local fns = {}
local i = 1
while i <= 3 do
  local j = i * 10
  fns[i] = function () return j end
  i = i + 1
end
print(fns[1](), fns[2](), fns[3]())
local shared = {}
do
  local x = 1
  shared.get = function () return x end
  shared.set = function (v) x = v end
end
shared.set(42)
print(shared.get())
local function outer()
  local a = 1
  local function middle()
    local b = 2
    local function inner()
      a = a + 1
      b = b + 1
      return a, b
    end
    return inner
  end
  return middle(), function () return a end
end
local inner, read_a = outer()
print(inner())
print(inner())
print(read_a())
local k = 0
local captured = {}
while true do
  k = k + 1
  local v = k
  captured[k] = function () v = v + 100; return v end
  if k == 3 then break end
end
print(captured[1](), captured[1](), captured[2](), captured[3]())
local function recursive(n)
  if n == 0 then return 0 end
  return n + recursive(n - 1)
end
print(recursive(100))
local function make_adders()
  local list = {}
  local n = 1
  while n <= 3 do
    local step = n
    list[n] = function (x) return x + step end
    n = n + 1
  end
  return list
end
local adders = make_adders()
print(adders[1](10), adders[2](10), adders[3](10))
