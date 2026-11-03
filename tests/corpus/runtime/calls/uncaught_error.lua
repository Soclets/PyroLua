-- An error nothing catches ends the program with its message.
print("before")
local function fail() error("stopped here") end
fail()
print("not reached")
