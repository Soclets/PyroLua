-- Equality of other values, strings ordered byte by byte, and the logical operators.
local s, t = "abc", "abd"
print(s < t, s <= t, s > t, "" < "a", "a" < "", "Z" < "a", "abc" == "abc")
print("a\0b" < "a\0c", "a\0" > "a", "10" < "9", s == s, s ~= t)
local f1, f2 = print, type
print(f1 == f1, f1 == f2, nil == false, true == true, 1 == "1")
local x, y, z = nil, false, 0
print(x or "default", y or z, z and "zero", x and 1, y and 1, z or 1)
print(not x and "yes", (x or y) == false, 1 and 2 or 3, nil and 2 or 3)
