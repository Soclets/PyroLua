-- To-be-closed variables: normal exits, break, return, errors, and the generic for.
local function closer(name)
  return setmetatable({}, {__close = function (self, err) print("close", name, err) end})
end
do
  local a <close> = closer("a")
  local b <close> = closer("b")
  local c <close> = nil
  local d <close> = false
  print("in block")
end
local function returns()
  local x <close> = closer("x")
  return 1, 2, 3
end
print(returns())
local function open_returns(...)
  local y <close> = closer("y")
  return ...
end
print(open_returns(4, 5, 6))
for i = 1, 3 do
  local z <close> = closer("z" .. i)
  if i == 2 then break end
end
local i = 0
while true do
  i = i + 1
  local w <close> = closer("w" .. i)
  if i == 2 then break end
end
print(pcall(function ()
  local e <close> = closer("e")
  error("boom")
end))
print(pcall(function ()
  local first <close> = closer("first")
  local failing <close> = setmetatable({}, {__close = function (self, err)
    print("failing sees", err)
    error("from close")
  end})
  error("original")
end))
print(pcall(function ()
  local ok <close> = setmetatable({}, {__close = function () error("close error on success") end})
  return "unreached"
end))
local function iter(state, control)
  if control < 3 then return control + 1 end
end
for k in iter, nil, 0, closer("for") do print("k", k) end
for k in iter, nil, 0, closer("for break") do if k == 2 then break end end
print(pcall(function () local bad <close> = {} end))
print(pcall(function () local bad <close> = 42 end))
local nested = function ()
  local outer <close> = closer("outer")
  do
    local inner <close> = closer("inner")
  end
  print("between")
end
nested()
print(pcall(function () for k in iter, nil, 0, 7 do end end))
-- (Not the error: lua.c's message handler adds a traceback to it before closing.)
local top <close> = setmetatable({}, {__close = function () print("close top") end})
error("at the top")
