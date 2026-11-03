-- Tail calls, through Lua and host functions.
local function last(...) return select('#', ...), ... end
local function middle(...) return last(...) end
local function outer(...) return middle("x", ...) end
print(outer(1, 2))
local function to_host(...) return select(2, ...) end
print(to_host("a", "b", "c"))
local function to_print(...) return print(...) end
print(to_print("printed"))
