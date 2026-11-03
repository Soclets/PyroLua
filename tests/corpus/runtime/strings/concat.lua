-- Concatenation of strings and numbers, chains, and __concat.
local a, b, c = "x", "y", "z"
print(a .. b, a .. b .. c, a .. 1 .. 2.5, 1 .. 2, -0.0 .. "", 2^63 .. "", 10 // 3 .. "")
local s = ""
local i = 1
while i <= 10 do s = s .. i .. ","; i = i + 1 end
print(s, #s)
print("" .. "", #("" .. ""))
local V = setmetatable({}, {__concat = function (l, r)
  local function name(x) if type(x) == "table" then return "V" end return x end
  return name(l) .. "+" .. name(r)
end})
print(V .. "s", "s" .. V, 1 .. V, V .. V)
print("a" .. "b" .. V .. "c" .. "d")
print("a" .. V .. "b" .. V .. "c")
local parts = {}
for k = 1, 5 do parts[k] = "p" .. k end
print(parts[1] .. parts[2] .. parts[3] .. parts[4] .. parts[5])
local long = "abc"
for k = 1, 10 do long = long .. long end
print(#long)
local t = setmetatable({}, {__concat = function () return 42 end})
print(t .. "x", "x" .. t)
print(pcall(function () return "a" .. {} end))
print(pcall(function () return {} .. "a" end))
print(pcall(function () return 1 .. nil end))
print(pcall(function () return true .. "x" end))
