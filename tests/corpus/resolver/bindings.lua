local a = 1
local function f(b)
  local c = a + b
  return function() return a, b, c, d end
end
function t:m() return self end
