-- Functions, upvalues, varargs, methods, calls, assignments and tables.
local a, b, c = 1
local function outer(x, ...)
  local y = ...
  local function middle(z)
    local function inner()
      return x, y, z, a, b, outer, print
    end
    return inner
  end
  return middle, select('#', ...), {...}, ...
end
function outer2(self, ...) return ... end
local obj = {}
function obj.f(p) return p end
function obj:m(q) return self, q end
function obj.nested.deep:method() end
obj:m(1)(2)("s"){}
print(obj.f(1), obj:m(2), outer(1, 2, 3))
local t = {1, 2, 3; x = 1, ["y"] = 2, [3] = 3, f(), g(), ...}
local u = {f()}
local v = {x = 1, y = 2, z = 3, w = 4}
local w = {[1] = 1, [2] = 2, 3, 4}
a, b, c = c, b, a
a.x, a = 1, 2
a, a.x = 1, 2
local s, s2
s, s.x, s[s] = 1, 2, 3
t[1], t[2], t[3] = f()
a, b = f(), g()
a, b, c = (f())
x, y = ...
local q = (...)
return f(...)
