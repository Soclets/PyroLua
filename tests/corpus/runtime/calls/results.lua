-- Multiple results, adjusted to what the call site wants.
local function none() end
local function one() return 1 end
local function three() return 1, 2, 3 end
print(none())
print(three())
print(three(), "last")
print("first", three())
print((three()))
local a, b, c, d = three()
print(a, b, c, d)
local e = none()
print(e)
print(one(), one(), three())
