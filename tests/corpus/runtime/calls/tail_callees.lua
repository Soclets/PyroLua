-- Tail calls of every kind of callee (tail_calls.lua has the plain ones): Lua functions, host functions (which run above the
-- frame that calls them), and values with __call, in loops deep enough that only proper
-- tail calls finish.

local function count (n, total)
  if n == 0 then
    return total
  end
  return count (n - 1, total + 1)
end
print (count (300000, 0))

-- Through __call, to a Lua function: still a proper tail call.
local counter = setmetatable ({}, {__call = function (self, n, total)
  if n == 0 then
    return total
  end
  return self (n - 1, total + 2)
end})
print (counter (300000, 0))

-- To host functions, directly and through __call: all their results are returned.
local function last (...)
  return select (-1, ...)
end
local function host (...)
  return select ("#", ...), select (2, ...)
end
print (host (1, 2, 3))
local lengths = setmetatable ({1, 2, 3}, {__call = rawlen})
local function length ()
  return lengths ()
end
print (length ())
print (last (1, 2, 3))
-- __call gives the host function the object as its first argument.
local selecting = setmetatable ({}, {__call = select})
local function through (...)
  return selecting (...)
end
print (pcall (through, "#", "a", "b"))

-- Errors in a host function called in a tail call give the line of the call and its name.
local function failing ()
  return setmetatable (
    1)
end
print (pcall (failing))
local function hidden ()
  local fn = rawlen
  return fn (1)
end
print (pcall (hidden))
local function not_callable ()
  local value = {}
  return value (1)
end
print (pcall (not_callable))
local object = {method = rawlen}
local function method ()
  return object:method (2)
end
print (pcall (method))
