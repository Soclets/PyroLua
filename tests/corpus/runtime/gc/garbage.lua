-- Garbage of every kind, some of it kept: what survives a collection must be intact.
local keep = {}
for i = 1, 2000 do
  local t = {i, i * 2, name = "item" .. i}
  local f = function () return t.name end
  local s = "s" .. i .. "-" .. (i * i)
  if i % 100 == 0 then keep[#keep + 1] = {t = t, f = f, s = s} end
end
local total = 0
for _, k in ipairs(keep) do total = total + k.t[2] + #k.s end
print(#keep, total, keep[5].f(), keep[20].s)
local chain = nil
for i = 1, 500 do chain = {next = chain, value = i} end
local sum = 0
while chain do sum = sum + chain.value; chain = chain.next end
print(sum)
local mt = {__index = function (_, k) return k .. "!" end}
local proxies = {}
for i = 1, 300 do proxies[i] = setmetatable({}, mt) end
print(proxies[300].hello, getmetatable(proxies[1]) == mt)
local counter = 0
local function make() local n = 0 return function () n = n + 1; counter = counter + 1 return n end end
local fs = {}
for i = 1, 100 do fs[i] = make() end
for i = 1, 100 do fs[i](); fs[i]() end
print(counter, fs[50]())
