-- Varargs: select, passing them on, and fixed parameters before them.
local function count(...) return select('#', ...) end
local function pass(...) return ... end
local function first(a, ...) return a, select('#', ...) end
print(count(), count(nil), count(1, nil, 3), count(nil, nil))
print(pass(1, 2, 3))
print(pass())
print(first(1, 2, 3))
print(first())
print(select(2, "a", "b", "c"))
print(select(-1, "a", "b", "c"))
print(select('#', pass(1, nil)))
