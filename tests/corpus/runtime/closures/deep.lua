-- Deep recursion within the limits, and a stack overflow caught.
local function depth(n) if n == 0 then return 0 end return 1 + depth(n - 1) end
print(depth(10000))
local function forever(n) return 1 + forever(n + 1) end
local ok, message = pcall(forever, 1)
print(ok, message)
local function tail(n) if n == 0 then return "done" end return tail(n - 1) end
print(tail(1000000))
