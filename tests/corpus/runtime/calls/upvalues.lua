-- Closures share their upvalues, which outlive the function that declared them.
local function make(value)
  local function get() return value end
  local function set(new) value = new end
  return get, set
end
local get, set = make("a")
print(get())
set("b")
print(get())
local get2, set2 = make("c")
print(get(), get2())
set2("d")
print(get(), get2())
local shared = "outer"
local function read() return shared end
shared = "changed"
print(read())
local function nest()
  local inner = "in"
  return function() return function() return inner end end
end
print(nest()()())
