-- # on tables built by constructors, with nils inside: NEWTABLE sizes the array part as
-- PUC Lua does, and SETLIST grows it to hold its last key, so the border found is the same.

print (#{1, nil, 3}, #{nil, nil, 3}, #{1, 2, nil}, #{nil}, #{})
print (#{1, nil, 3, n = 3}, #{x = 1, y = 2}, #{nil, 2, x = 1})

-- {...} gets an array part of exactly select ("#", ...) places.
local function count (...)
  local args = {...}
  return #args, select ("#", ...)
end
print (count (1, nil, 3))
print (count (nil, nil, nil, 4))
print (count (1, 2, nil))
print (count (nil))
print (count ())
local function pack (...)
  return {n = select ("#", ...), ...}
end
local packed = pack (nil, "b", nil)
print (#packed, packed.n, packed[2])

-- Values after a call in a constructor (an open SETLIST), and a call in the middle.
local function three () return 1, nil, 3 end
print (#{three ()}, #{three (), three ()}, #{0, three ()})

-- More than 50 items (several SETLISTs) and more than 255 (an extra argument), with holes.
local long = {1, 2, 3, 4, 5, 6, nil, 8, 9, 10, 11, 12, 13, nil, 15, 16, 17, 18, 19, 20,
  nil, 22, 23, 24, 25, 26, 27, nil, 29, 30, 31, 32, 33, 34, nil, 36, 37, 38, 39, 40, 41,
  nil, 43, 44, 45, 46, 47, 48, nil, 50, 51, 52, 53, 54, 55, nil, 57, 58, 59, 60, 61, 62,
  nil, 64, 65, 66, 67, 68, 69, nil, 71, 72, 73, 74, 75, 76, nil, 78, 79, 80, 81, 82, 83,
  nil, 85, 86, 87, 88, 89, 90, nil, 92, 93, 94, 95, 96, 97, nil, 99, 100, 101, 102, 103,
  104, nil, 106, 107, 108, 109, 110, 111, nil, 113, 114, 115, 116, 117, 118, nil, 120, 121,
  122, 123, 124, 125, nil, 127, 128, 129, 130, 131, 132, nil, 134, 135, 136, 137, 138, 139,
  nil, 141, 142, 143, 144, 145, 146, nil, 148, 149, 150, 151, 152, 153, nil, 155, 156, 157,
  158, 159, 160, nil, 162, 163, 164, 165, 166, 167, nil, 169, 170, 171, 172, 173, 174, nil,
  176, 177, 178, 179, 180, 181, nil, 183, 184, 185, 186, 187, 188, nil, 190, 191, 192, 193,
  194, 195, nil, 197, 198, 199, 200, 201, 202, nil, 204, 205, 206, 207, 208, 209, nil, 211,
  212, 213, 214, 215, 216, nil, 218, 219, 220, 221, 222, 223, nil, 225, 226, 227, 228, 229,
  230, nil, 232, 233, 234, 235, 236, 237, nil, 239, 240, 241, 242, 243, 244, nil, 246, 247,
  248, 249, 250, 251, nil, 253, 254, 255, 256, 257, 258, nil, 260, 261, 262, 263, 264, 265,
  nil, 267, 268, 269, 270, 271, 272, nil, 274, 275, 276, 277, 278, 279, nil, 281, 282, 283,
  284, 285, 286, nil, 288, 289, 290, 291, 292, 293, nil, 295, 296, 297, 298, 299, 300}
print (#long, long[300], long[294])
local wide = {}
for i = 1, 120 do
  wide[#wide + 1] = i
end
print (#wide)

-- A presized table that changes afterwards.
local t = {1, 2, 3, nil, 5, nil, nil, 8}
print (#t)
t[9] = 9
print (#t)
t[8] = nil
t[9] = nil
print (#t)
t[4] = 4
print (#t)
local grown = {1, nil, 3}
for i = 4, 20 do
  grown[i] = i
end
print (#grown)

-- Nested constructors.
local nested = {{1, nil, 3}, {nil, nil}, {...}}
print (#nested, #nested[1], #nested[2], #nested[3])
