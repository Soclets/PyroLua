-- Integer division by zero is an error; the message has the position.
local a, b = 7, 0
print(pcall(function () return a // b end))
print(pcall(function () return a % b end))
print(a // 0.0, a % 0.0)
print(a // b)
