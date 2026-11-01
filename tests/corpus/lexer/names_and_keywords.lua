local _ok, x1, andx, End = 1, 2, 3, 4
if x1 then goto done elseif andx then else end
::done::
while false do break end
repeat until true
for i = 1, 2 do end
local function f(...) return not nil or true and false end
