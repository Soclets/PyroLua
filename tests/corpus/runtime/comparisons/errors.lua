-- Values that cannot be ordered.
print(pcall(function () return 1 < "2" end))
print(pcall(function () local a = nil; return a <= 1 end))
print(pcall(function () local a = true; return 5 > a end))
print(pcall(function () local a = "x"; return a >= 1 end))
print(1 < nil)
