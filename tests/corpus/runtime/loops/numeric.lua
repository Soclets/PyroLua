-- Numeric for loops: integers, floats, negative steps, overflow-safe counts, strings.
local sum = 0
for i = 1, 10 do sum = sum + i end
print(sum)
for i = 10, 1, -3 do print(i) end
for i = 1, 0 do print("never") end
for i = 1.0, 2.0, 0.25 do print(i) end
for i = 1, 2.5 do print(i) end
for i = 3, 1.5, -1 do print(i) end
local max = 9223372036854775807
local min = -max - 1
for i = max - 2, max do print(i) end
for i = min, min + 2 do print(i) end
for i = min + 2, min, -1 do print(i) end
local n = 0
for i = 1, max, max // 4 do n = n + 1 end
print(n)
for i = 0, 2^53, 2^52 do print(i) end
for i = 1, math_huge or 1 / 0 do if i > 3 then break end print(i) end
for i = 1, -1 / 0 do print("never") end
for i = "1", 2 do print(i) end
for i = 1, "2" do print(i) end
for i = 1, 3, " 1 " do print(i) end
for i = 0x10, 0x12 do print(i) end
local fns = {}
for i = 1, 3 do fns[i] = function () return i end end
print(fns[1](), fns[2](), fns[3]())
for i = 1, 3 do
  local j = i
  i = i * 100
  print(i, j)
end
