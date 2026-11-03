-- Table constructors, fields, integer keys, lengths and list stores.
local t = {10, 20, 30, x = 1, ["y"] = 2, [3.0] = "three", [-1] = "minus"}
print(t[1], t[2], t[3], t.x, t.y, t[-1], #t, t[4], t.z)
t[4] = 40; t.z = "zed"; t[2.0] = "two"
print(t[4], t.z, t[2], #t)
local empty = {}
print(#empty, empty[1], empty.x)
local function three() return 1, 2, 3 end
local function none() end
local a = {three()}
local b = {three(), three()}
local c = {none(), none()}
local d = {(three())}
print(#a, #b, #c, #d, b[4], d[2])
local big = {
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
  21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
  41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60,
}
print(#big, big[1], big[50], big[51], big[60])
local nested = {inner = {deep = {value = "found"}}}
print(nested.inner.deep.value)
local function pack(...) return {...} end
local p = pack(nil, 2, nil)
print(p[1], p[2], p[3])
local holes = {1, 2, nil, 4}
print(#holes)
local key = {}
local by_table = {[key] = "table key", [print] = "function key", [true] = "true key"}
print(by_table[key], by_table[print], by_table[true], by_table[false])
local s = "text"
local obj = {name = "object"}
function obj.get(self) return self.name end
function obj:shout() return self.name, "!" end
print(obj:get(), obj:shout())
local i = 1
local list = {}
while i <= 100 do list[i] = i * i; i = i + 1 end
print(#list, list[10], list[100])
list[#list + 1] = "last"
print(#list, list[101])
