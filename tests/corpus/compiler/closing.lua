-- To-be-closed variables and constants.
local function f()
  local x <close> = nil
  local y <const> = 10
  local z <const> = {}
  do
    local w <close> = setmetatable({}, {__close = print})
    return w, y, z
  end
end
local function g(...)
  local a <close> = ...
  return g(...)
end
local function h()
  local a <close> = nil
  return h()
end
for k, v in pairs({}) do return k end
return f, g, h
