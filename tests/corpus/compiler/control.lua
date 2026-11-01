-- Control structures: conditions, loops, break, goto, labels, closing upvalues.
local t = {}
for i = 1, 10 do t[i] = function () return i end end
for i = 10, 1, -1 do if i == 5 then break end end
for i = 1.0, 2 do end
for k, v in pairs(t) do t[k] = v end
for k, v, w, z in next, t do local a = k end
while #t > 0 do table.remove(t) if #t == 3 then break end end
repeat local x = #t until x == 0
repeat local y = 1; local f = function () return y end until f() == 1
local n = 0
::top::
n = n + 1
if n < 3 then goto top end
do
  local u = 1
  local g = function () return u end
  goto skip
  print(g)
  ::skip::
end
for i = 1, 3 do
  local v = i
  local h = function () return v end
  if i == 2 then goto continue end
  print(h())
  ::continue::
end
while true do
  if n then break end
  if n > 1 then break; end
  if not n then break; print(n) end
end
if n == 1 then print(1) elseif n == 2 then print(2) elseif n then print(3) else print(4) end
if n and t or not n then print(n) end
local z = n and 1 or 2
local w = (n > 1) and (n < 3) or (n == 0)
local v = n or nil
print(z, w, v, n == 1 and t)
do ::a:: ::b:: ; ::c:: end
while n do
  if false then break end
  if nil then break; n = 1 end
  if true then break end
end
goto done
local function unused() end
::done::
