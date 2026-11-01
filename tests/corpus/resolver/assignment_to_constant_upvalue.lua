local x <const> = 1
local function f()
  return function() x = 2 end
end
