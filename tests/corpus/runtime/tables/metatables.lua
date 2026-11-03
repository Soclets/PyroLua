-- Metatables: __index and __newindex chains, raw access, operators, __call, __len.
local base = {greeting = "hello"}
local mid = setmetatable({}, {__index = base})
local top = setmetatable({}, {__index = mid})
print(top.greeting, rawget(top, "greeting"), top.missing)
local computed = setmetatable({}, {__index = function (t, k) return k * 2 end})
print(computed[21], rawget(computed, 21))
local log = {}
local guarded = setmetatable({}, {__newindex = function (t, k, v) rawset(t, k, v * 10) end})
guarded.a = 1
print(guarded.a, rawget(guarded, "a"))
local store = {}
local proxy = setmetatable({}, {__newindex = store})
proxy.x = 5
print(rawget(proxy, "x"), store.x)
local existing = setmetatable({y = 1}, {__newindex = function () print("not called") end})
existing.y = 2
print(existing.y)
local V = {}
V.__index = V
local function n_of(x) if type(x) == "table" then return x.n end return x end
V.__add = function (a, b) return "add", n_of(a), n_of(b) end
V.__sub = function (a, b) return "sub" end
V.__mul = function (a, b) return "mul" end
V.__div = function (a, b) return "div" end
V.__mod = function (a, b) return "mod" end
V.__pow = function (a, b) return "pow" end
V.__idiv = function (a, b) return "idiv" end
V.__band = function (a, b) return "band" end
V.__bor = function (a, b) return "bor" end
V.__bxor = function (a, b) return "bxor" end
V.__shl = function (a, b) return "shl" end
V.__shr = function (a, b) return "shr" end
V.__unm = function (a) return "unm", a.n end
V.__bnot = function (a) return "bnot" end
V.__len = function (a) return 42 end
V.__eq = function (a, b) return n_of(a) == n_of(b) end
V.__lt = function (a, b) return n_of(a) < n_of(b) end
V.__le = function (a, b) return n_of(a) <= n_of(b) end
V.__call = function (self, x, y) return "called", self.n, x, y end
local function new(n) return setmetatable({n = n}, V) end
local one, two = new(1), new(2)
print(one + two, one + 5, 5 + one, one - 1, 2 * one, one / two, one % 3, one ^ 2)
print(one // two, one & 1, 1 | one, one ~ one, one << 1, 1 >> one, -one, ~one, #one)
print(one == two, one == new(1), one ~= new(1), one < two, two < one, one <= two)
print(one > two, one >= two, 1.5 < one, one(7, 8))
print(getmetatable(one) == V, getmetatable("x"), getmetatable(1))
local protected = setmetatable({}, {__metatable = "locked"})
print(getmetatable(protected))
print(pcall(setmetatable, protected, {}))
print(rawequal(one, one), rawequal(one, new(1)), rawlen({1, 2, 3}), rawlen("four"))
print(rawequal(1, 1.0), rawequal("a", "a"), rawequal(0/0, 0/0))
local named = setmetatable({}, {__name = "MyType"})
print(pcall(setmetatable, named))
local shown = setmetatable({}, {__tostring = function () return "shown!" end})
print(shown, tostring(shown))
print(setmetatable({}, nil) ~= nil, getmetatable(setmetatable({}, nil)))
