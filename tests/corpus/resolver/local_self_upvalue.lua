local function f()
  local self = 1
  return function() self = 2 end
end
