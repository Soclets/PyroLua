-- error with levels, positions of calls that span lines, and non-string errors.
local function f(level) error("message", level) end
print(pcall(f, 1))
print(pcall(f, 2))
print(pcall(f, 0))
local function g()
  f(
    2
  )
end
print(pcall(g))
print(pcall(error))
print(pcall(error, nil))
local ok2, e2 = pcall(error, {code = 1})
print(ok2, type(e2), e2.code)
print(select('#', pcall(error)))
local ok, e = pcall(error, setmetatable({}, {__tostring = function () return "custom" end}))
print(ok, tostring(e))
print(pcall(error, 42))
print(pcall(error, "with level", 1))
local function deep() local x = nil; return x.field end
local function middle() return deep() end
print(pcall(middle))
error({})
