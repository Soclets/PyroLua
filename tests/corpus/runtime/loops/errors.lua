-- Errors of for loops.
print(pcall(function () for i = 1, 2, 0 do end end))
print(pcall(function () for i = 1.0, 2, 0 do end end))
print(pcall(function () for i = nil, 2 do end end))
print(pcall(function () for i = 1, {} do end end))
print(pcall(function () for i = 1, 2, "x" do end end))
print(pcall(function () for i = "a", 2 do end end))
for i = 1, 10, false do end
