local function f() return end
local function g() return 1, 2; end
local function h() do return end end
return f(), g()
