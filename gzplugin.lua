--[[--
gzplugin 1.0.0-release <br>
The gzip plugin provides some functionality to open and save .gz files
such that .gz files can be processed as if they were text files. Other
text editors such as vim also provide such functionality.

@file gzplugin.lua
@author Haoqian He (Github: SafeteeWoW; World of Warcraft: Safetyy-Illidan(US)), Daniela MANTOVANI (github: dzmanto), David Manura
@license MIT license

This plugin requires Lua 5.1/5.2/5.3/5.4 interpreter or LuaJIT v2.0+.
--]]

local micro = import("micro")
local buffer = import("micro/buffer")
local bufpane = import("micro/bufpane")
local config = import("micro/config")
local util = import("micro/util")

-- from compress/deflatelua
local assert = assert
local error = error
local ipairs = ipairs
local pairs = pairs
local print = print
local require = require
local tostring = tostring
local type = type
local setmetatable = setmetatable
local io = io
local math = math
local table_sort = table.sort
local math_max = math.max
local string_char = string.char

local floor = math.floor

local MOD = 2^32
local MODM = MOD-1

local DEBUG = false

-- Whether to use `bit` library functions in current module.
-- Unlike the crc32 library, it doesn't make much difference in this module.
local NATIVE_BITOPS = (bit ~= nil)

local band, lshift, rshift
if NATIVE_BITOPS then
  band = bit.band
  lshift = bit.lshift
  rshift = bit.rshift
end


local function warn(s)
  io.stderr:write(s, '\n')
end


local function debug(...)
  print('DEBUG', ...)
end


local function runtime_error(s, level)
  level = level or 1
  error({s}, level+1)
end


local function make_outstate(outbs)
  local outstate = {}
  outstate.outbs = outbs
  outstate.window = {}
  outstate.window_pos = 1
  return outstate
end

local function output(outstate, byte)
  -- debug('OUTPUT:', s)
  local window_pos = outstate.window_pos
  outstate.outbs(byte)
  outstate.window[window_pos] = byte
  outstate.window_pos = window_pos % 32768 + 1  -- 32K
end


local function noeof(val)
  return assert(val, 'unexpected end of file')
end


local function hasbit(bits, bit)
  return bits % (bit + bit) >= bit
end


local function memoize(f)
  local mt = {}
  local t = setmetatable({}, mt)
  function mt:__index(k)
    local v = f(k)
    t[k] = v
    return v
  end
  return t
end


-- small optimization (lookup table for powers of 2)
local pow2 = memoize(function(n) return 2^n end)

--local tbits = memoize(
--  function(bits)
--    return memoize( function(bit) return getbit(bits, bit) end )
--  end )

-- weak metatable marking objects as bitstream type
local is_bitstream = setmetatable({}, {__mode='k'})


-- DEBUG
-- prints LSB first
--[[
local function bits_tostring(bits, nbits)
  local s = ''
  local tmp = bits
  local function f()
    local b = tmp % 2 == 1 and 1 or 0
    s = s .. b
    tmp = (tmp - b) / 2
  end
  if nbits then
    for i=1,nbits do f() end
  else
    while tmp ~= 0 do f() end
  end

  return s
end
--]]

local function bytestream_from_file(fh)
  local o = {}
  function o:read()
    local sb = fh:read(1)
    if sb then return sb:byte() end
  end
  return o
end


local function bytestream_from_string(s)
  local i = 1
  local o = {}
  function o:read()
    local by
    if i <= #s then
      by = s:byte(i)
      i = i + 1
    end
    return by
  end
  return o
end


local function bytestream_from_function(f)
  local i = 0
  local buffer = ''
  local o = {}
  function o:read()
    i = i + 1
    if i > #buffer then
      buffer = f()
      if not buffer then return end
      i = 1
    end
    return buffer:byte(i,i)
  end
  return o
end

local function bitstream_from_bytestream(bys)
  local buf_byte = 0
  local buf_nbit = 0
  local o = {}

  function o:nbits_left_in_byte()
    return buf_nbit
  end

  if NATIVE_BITOPS then
    function o:read(nbits)
      nbits = nbits or 1
      while buf_nbit < nbits do
        local byte = bys:read()
        if not byte then return end  -- note: more calls also return nil
        buf_byte = buf_byte + lshift(byte, buf_nbit)
        buf_nbit = buf_nbit + 8
      end
      local bits
      if nbits == 0 then
        bits = 0
      elseif nbits == 32 then
        bits = buf_byte
        buf_byte = 0
      else
        bits = band(buf_byte, rshift(0xffffffff, 32 - nbits))
        buf_byte = rshift(buf_byte, nbits)
      end
      buf_nbit = buf_nbit - nbits
      return bits
    end
  else
    function o:read(nbits)
      nbits = nbits or 1
      while buf_nbit < nbits do
        local byte = bys:read()
        if not byte then return end  -- note: more calls also return nil
        buf_byte = buf_byte + pow2[buf_nbit] * byte
        buf_nbit = buf_nbit + 8
      end
      local m = pow2[nbits]
      local bits = buf_byte % m
      buf_byte = (buf_byte - bits) / m
      buf_nbit = buf_nbit - nbits
      return bits
    end
  end
  
  is_bitstream[o] = true

  return o
end

local function get_bitstream(o)
  local bs
  if is_bitstream[o] then
    return o
  elseif io.type(o) == 'file' then
    bs = bitstream_from_bytestream(bytestream_from_file(o))
  elseif type(o) == 'string' then
    bs = bitstream_from_bytestream(bytestream_from_string(o))
  elseif type(o) == 'function' then
    bs = bitstream_from_bytestream(bytestream_from_function(o))
  else
    runtime_error 'unrecognized type'
  end
  return bs
end


local function get_obytestream(o)
  local bs
  if io.type(o) == 'file' then
    bs = function(sbyte) o:write(string_char(sbyte)) end
  elseif type(o) == 'function' then
    bs = o
  else
    runtime_error('unrecognized type: ' .. tostring(o))
  end
  return bs
end

local function HuffmanTable(init, is_full)
  local t = {}
  if is_full then
    for val,nbits in pairs(init) do
      if nbits ~= 0 then
        t[#t+1] = {val=val, nbits=nbits}
        --debug('*',val,nbits)
      end
    end
  else
    for i=1,#init-2,2 do
      local firstval, nbits, nextval = init[i], init[i+1], init[i+2]
      --debug(val, nextval, nbits)
      if nbits ~= 0 then
        for val=firstval,nextval-1 do
          t[#t+1] = {val=val, nbits=nbits}
        end
      end
    end
  end
  table_sort(t, function(a,b)
    return a.nbits == b.nbits and a.val < b.val or a.nbits < b.nbits
  end)

  -- assign codes
  local code = 1  -- leading 1 marker
  local nbits = 0
  for i,s in ipairs(t) do
    if s.nbits ~= nbits then
      code = code * pow2[s.nbits - nbits]
      nbits = s.nbits
    end
    s.code = code
    --debug('huffman code:', i, s.nbits, s.val, code, bits_tostring(code))
    code = code + 1
  end

  local minbits = math.huge
  local look = {}
  for i,s in ipairs(t) do
    minbits = math.min(minbits, s.nbits)
    look[s.code] = s.val
  end

  --for _,o in ipairs(t) do
  --  debug(':', o.nbits, o.val)
  --end

  -- function t:lookup(bits) return look[bits] end

  local msb = NATIVE_BITOPS and function(bits, nbits)
    local res = 0
    for i=1,nbits do
      res = lshift(res, 1) + band(bits, 1)
      bits = rshift(bits, 1)
    end
    return res
  end or function(bits, nbits)
    local res = 0
    for i=1,nbits do
      local b = bits % 2
      bits = (bits - b) / 2
      res = res * 2 + b
    end
    return res
  end
  
  local tfirstcode = memoize(
    function(bits) return pow2[minbits] + msb(bits, minbits) end)

  function t:read(bs)
    local code = 1 -- leading 1 marker
    local nbits = 0
    while 1 do
      if nbits == 0 then  -- small optimization (optional)
        code = tfirstcode[noeof(bs:read(minbits))]
        nbits = nbits + minbits
      else
        local b = noeof(bs:read())
        nbits = nbits + 1
        code = code * 2 + b   -- MSB first
        --[[NATIVE_BITOPS
        code = lshift(code, 1) + b   -- MSB first
        --]]
      end
      --debug('code?', code, bits_tostring(code))
      local val = look[code]
      if val then
        --debug('FOUND', val)
        return val
      end
    end
  end

  return t
end

local function parse_gzip_header(bs)
  -- local FLG_FTEXT = 2^0
  local FLG_FHCRC = 2^1
  local FLG_FEXTRA = 2^2
  local FLG_FNAME = 2^3
  local FLG_FCOMMENT = 2^4

  local id1 = bs:read(8)
  local id2 = bs:read(8)
  if id1 ~= 31 or id2 ~= 139 then
    -- runtime_error 'not in gzip format'
    return false
  end
  local cm = bs:read(8)  -- compression method
  local flg = bs:read(8) -- FLaGs
  local mtime = bs:read(32) -- Modification TIME
  local xfl = bs:read(8) -- eXtra FLags
  local os = bs:read(8) -- Operating System

  if DEBUG then
    debug("CM=", cm)
    debug("FLG=", flg)
    debug("MTIME=", mtime)
    -- debug("MTIME_str=",os.date("%Y-%m-%d %H:%M:%S",mtime)) -- non-portable
    debug("XFL=", xfl)
    debug("OS=", os)
  end

  if not os then runtime_error 'invalid header' end

  if hasbit(flg, FLG_FEXTRA) then
    local xlen = bs:read(16)
    local extra = 0
    for i=1,xlen do
      extra = bs:read(8)
    end
    if not extra then runtime_error 'invalid header' end
  end

  local function parse_zstring(bs)
    repeat
      local by = bs:read(8)
      if not by then runtime_error 'invalid header' end
    until by == 0
  end

  if hasbit(flg, FLG_FNAME) then
    parse_zstring(bs)
  end

  if hasbit(flg, FLG_FCOMMENT) then
    parse_zstring(bs)
  end

  if hasbit(flg, FLG_FHCRC) then
    local crc16 = bs:read(16)
    if not crc16 then runtime_error 'invalid header' end
    -- IMPROVE: check CRC.  where is an example .gz file that
    -- has this set?
    if DEBUG then
      debug("CRC16=", crc16)
    end
  end
end

local function parse_zlib_header(bs)
  local cm = bs:read(4) -- Compression Method
  local cinfo = bs:read(4) -- Compression info
  local fcheck = bs:read(5) -- FLaGs: FCHECK (check bits for CMF and FLG)
  local fdict = bs:read(1) -- FLaGs: FDICT (present dictionary)
  local flevel = bs:read(2) -- FLaGs: FLEVEL (compression level)
  local cmf = cinfo * 16  + cm -- CMF (Compresion Method and flags)
  local flg = fcheck + fdict * 32 + flevel * 64 -- FLaGs
  
  if cm ~= 8 then -- not "deflate"
    runtime_error("unrecognized zlib compression method: " + cm)
  end
  if cinfo > 7 then
    runtime_error("invalid zlib window size: cinfo=" + cinfo)
  end
  local window_size = 2^(cinfo + 8)
  
  if (cmf*256 + flg) %  31 ~= 0 then
    runtime_error("invalid zlib header (bad fcheck sum)")
  end
  
  if fdict == 1 then
    runtime_error("FIX:TODO - FDICT not currently implemented")
    local dictid_ = bs:read(32)
  end
  
  return window_size
end

local function parse_huffmantables(bs)
    local hlit = bs:read(5)  -- # of literal/length codes - 257
    local hdist = bs:read(5) -- # of distance codes - 1
    local hclen = noeof(bs:read(4)) -- # of code length codes - 4

    local ncodelen_codes = hclen + 4
    local codelen_init = {}
    local codelen_vals = {
      16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15}
    for i=1,ncodelen_codes do
      local nbits = bs:read(3)
      local val = codelen_vals[i]
      codelen_init[val] = nbits
    end
    local codelentable = HuffmanTable(codelen_init, true)

    local function decode(ncodes)
      local init = {}
      local nbits
      local val = 0
      while val < ncodes do
        local codelen = codelentable:read(bs)
        --FIX:check nil?
        local nrepeat
        if codelen <= 15 then
          nrepeat = 1
          nbits = codelen
          --debug('w', nbits)
        elseif codelen == 16 then
          nrepeat = 3 + noeof(bs:read(2))
          -- nbits unchanged
        elseif codelen == 17 then
          nrepeat = 3 + noeof(bs:read(3))
          nbits = 0
        elseif codelen == 18 then
          nrepeat = 11 + noeof(bs:read(7))
          nbits = 0
        else
          error 'ASSERT'
        end
        for i=1,nrepeat do
          init[val] = nbits
          val = val + 1
        end
      end
      local huffmantable = HuffmanTable(init, true)
      return huffmantable
    end

    local nlit_codes = hlit + 257
    local ndist_codes = hdist + 1

    local littable = decode(nlit_codes)
    local disttable = decode(ndist_codes)

    return littable, disttable
end

local tdecode_len_base
local tdecode_len_nextrabits
local tdecode_dist_base
local tdecode_dist_nextrabits
local function parse_compressed_item(bs, outstate, littable, disttable)
  local val = littable:read(bs)
  --debug(val, val < 256 and string_char(val))
  if val < 256 then -- literal
    output(outstate, val)
  elseif val == 256 then -- end of block
    return true
  else
    if not tdecode_len_base then
      local t = {[257]=3}
      local skip = 1
      for i=258,285,4 do
        for j=i,i+3 do t[j] = t[j-1] + skip end
        if i ~= 258 then skip = skip * 2 end
      end
      t[285] = 258
      tdecode_len_base = t
      --for i=257,285 do debug('T1',i,t[i]) end
    end
    if not tdecode_len_nextrabits then
      local t = {}
      if NATIVE_BITOPS then
        for i=257,285 do
          local j = math_max(i - 261, 0)
          t[i] = rshift(j, 2)
        end
      else
        for i=257,285 do
          local j = math_max(i - 261, 0)
          t[i] = (j - (j % 4)) / 4
        end
      end
      t[285] = 0
      tdecode_len_nextrabits = t
      --for i=257,285 do debug('T2',i,t[i]) end
    end
    local len_base = tdecode_len_base[val]
    local nextrabits = tdecode_len_nextrabits[val]
    local extrabits = bs:read(nextrabits)
    local len = len_base + extrabits

    if not tdecode_dist_base then
      local t = {[0]=1}
      local skip = 1
      for i=1,29,2 do
        for j=i,i+1 do t[j] = t[j-1] + skip end
        if i ~= 1 then skip = skip * 2 end
      end
      tdecode_dist_base = t
      --for i=0,29 do debug('T3',i,t[i]) end
    end
    if not tdecode_dist_nextrabits then
      local t = {}
      if NATIVE_BITOPS then
        for i=0,29 do
          local j = math_max(i - 2, 0)
          t[i] = rshift(j, 1)
        end
      else
        for i=0,29 do
          local j = math_max(i - 2, 0)
          t[i] = (j - (j % 2)) / 2
        end
      end
      tdecode_dist_nextrabits = t
      --for i=0,29 do debug('T4',i,t[i]) end
    end
    local dist_val = disttable:read(bs)
    local dist_base = tdecode_dist_base[dist_val]
    local dist_nextrabits = tdecode_dist_nextrabits[dist_val]
    local dist_extrabits = bs:read(dist_nextrabits)
    local dist = dist_base + dist_extrabits

    --debug('BACK', len, dist)
    for i=1,len do
      local pos = (outstate.window_pos - 1 - dist) % 32768 + 1  -- 32K
      output(outstate, assert(outstate.window[pos], 'invalid distance'))
    end
  end
  return false
end

local function parse_block(bs, outstate)
  local bfinal = bs:read(1)
  local btype = bs:read(2)

  local BTYPE_NO_COMPRESSION = 0
  local BTYPE_FIXED_HUFFMAN = 1
  local BTYPE_DYNAMIC_HUFFMAN = 2
  local BTYPE_RESERVED_ = 3

  if DEBUG then
    debug('bfinal=', bfinal)
    debug('btype=', btype)
  end

  if btype == BTYPE_NO_COMPRESSION then
    bs:read(bs:nbits_left_in_byte())
    local len = bs:read(16)
    local nlen_ = noeof(bs:read(16))

    for i=1,len do
      local by = noeof(bs:read(8))
      output(outstate, by)
    end
  elseif btype == BTYPE_FIXED_HUFFMAN or btype == BTYPE_DYNAMIC_HUFFMAN then
    local littable, disttable
    if btype == BTYPE_DYNAMIC_HUFFMAN then
      littable, disttable = parse_huffmantables(bs)
    else
      littable  = HuffmanTable {0,8, 144,9, 256,7, 280,8, 288,nil}
      disttable = HuffmanTable {0,5, 32,nil}
    end

    repeat
      local is_done = parse_compressed_item(
        bs, outstate, littable, disttable)
    until is_done
  else
    runtime_error 'unrecognized compression type'
  end

  return bfinal ~= 0
end

local function inflate_gunzip(t)
  local bs = get_bitstream(t.input)
  local outbs = get_obytestream(t.output)
  local outstate = make_outstate(outbs)

  repeat
    local is_final = parse_block(bs, outstate)
  until is_final
end

local function gunzip(t)
  local bs = get_bitstream(t.input)
  local outbs = get_obytestream(t.output)
  local disable_crc = t.disable_crc
  if disable_crc == nil then disable_crc = false end

  if not parse_gzip_header(bs) then
    -- return false
  end

  local data_crc32 = 0

  inflate_gunzip{input=bs, output=
    disable_crc and outbs or
      function(byte)
        data_crc32 = crc32(byte, data_crc32)
        outbs(byte)
      end
  }

  bs:read(bs:nbits_left_in_byte())

  local expected_crc32 = bs:read(32)
  local isize = bs:read(32) -- ignored
  
  if DEBUG then
    debug('crc32=', expected_crc32)
    debug('isize=', isize)
  end
  if not disable_crc and data_crc32 then
    if data_crc32 ~= expected_crc32 then
      t.output = t.input
      runtime_error('invalid compressed data--crc error')
    end    
  end
  if bs:read() then
    -- warn 'trailing garbage ignored'
  end
end

-- from LibDeflate
-- localize Lua api for faster access.
local assert = assert
local error = error
local pairs = pairs
local string_byte = string.byte
local string_char = string.char
local string_find = string.find
local string_gsub = string.gsub
local string_sub = string.sub
local table_concat = table.concat
local table_sort = table.sort
local tostring = tostring
local type = type

-- Converts i to 2^i, (0<=i<=32)
-- This is used to implement bit left shift and bit right shift.
-- "x >> y" in C:   "(x-x%_pow2[y])/_pow2[y]" in Lua
-- "x << y" in C:   "x*_pow2[y]" in Lua
local _pow2 = {}

-- Converts any byte to a character, (0<=byte<=255)
local _byte_to_char = {}

-- _reverseBitsTbl[len][val] stores the bit reverse of
-- the number with bit length "len" and value "val"
-- For example, decimal number 6 with bits length 5 is binary 00110
-- It's reverse is binary 01100,
-- which is decimal 12 and 12 == _reverseBitsTbl[5][6]
-- 1<=len<=9, 0<=val<=2^len-1
-- The reason for 1<=len<=9 is that the max of min bitlen of huffman code
-- of a huffman alphabet is 9?
local _reverse_bits_tbl = {}

-- Convert a LZ77 length (3<=len<=258) to
-- a deflate literal/LZ77_length code (257<=code<=285)
local _length_to_deflate_code = {}

-- convert a LZ77 length (3<=len<=258) to
-- a deflate literal/LZ77_length code extra bits.
local _length_to_deflate_extra_bits = {}

-- Convert a LZ77 length (3<=len<=258) to
-- a deflate literal/LZ77_length code extra bit length.
local _length_to_deflate_extra_bitlen = {}

-- Convert a small LZ77 distance (1<=dist<=256) to a deflate code.
local _dist256_to_deflate_code = {}

-- Convert a small LZ77 distance (1<=dist<=256) to
-- a deflate distance code extra bits.
local _dist256_to_deflate_extra_bits = {}

-- Convert a small LZ77 distance (1<=dist<=256) to
-- a deflate distance code extra bit length.
local _dist256_to_deflate_extra_bitlen = {}

-- Convert a literal/LZ77_length deflate code to LZ77 base length
-- The key of the table is (code - 256), 257<=code<=285
local _literal_deflate_code_to_base_len = {
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67,
    83, 99, 115, 131, 163, 195, 227, 258
  }

-- Convert a literal/LZ77_length deflate code to base LZ77 length extra bits
-- The key of the table is (code - 256), 257<=code<=285
local _literal_deflate_code_to_extra_bitlen = {
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5,
    5, 5, 5, 0
  }

-- Convert a distance deflate code to base LZ77 distance. (0<=code<=29)
local _dist_deflate_code_to_base_dist = {
  [0] = 1,
  2,
  3,
  4,
  5,
  7,
  9,
  13,
  17,
  25,
  33,
  49,
  65,
  97,
  129,
  193,
  257,
  385,
  513,
  769,
  1025,
  1537,
  2049,
  3073,
  4097,
  6145,
  8193,
  12289,
  16385,
  24577
}

-- Convert a distance deflate code to LZ77 bits length. (0<=code<=29)
local _dist_deflate_code_to_extra_bitlen =
  {
    [0] = 0,
    0,
    0,
    0,
    1,
    1,
    2,
    2,
    3,
    3,
    4,
    4,
    5,
    5,
    6,
    6,
    7,
    7,
    8,
    8,
    9,
    9,
    10,
    10,
    11,
    11,
    12,
    12,
    13,
    13
  }

-- The code order of the first huffman header in the dynamic deflate block.
-- See the page 12 of RFC1951
local _rle_codes_huffman_bitlen_order = {
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
}

-- The following tables are used by fixed deflate block.
-- The value of these tables are assigned at the bottom of the source.

-- The huffman code of the literal/LZ77_length deflate codes,
-- in fixed deflate block.
local _fix_block_literal_huffman_code

-- Convert huffman code of the literal/LZ77_length to deflate codes,
-- in fixed deflate block.
local _fix_block_literal_huffman_to_deflate_code

-- The bit length of the huffman code of literal/LZ77_length deflate codes,
-- in fixed deflate block.
local _fix_block_literal_huffman_bitlen

-- The count of each bit length of the literal/LZ77_length deflate codes,
-- in fixed deflate block.
local _fix_block_literal_huffman_bitlen_count

-- The huffman code of the distance deflate codes,
-- in fixed deflate block.
local _fix_block_dist_huffman_code

-- Convert huffman code of the distance to deflate codes,
-- in fixed deflate block.
local _fix_block_dist_huffman_to_deflate_code

-- The bit length of the huffman code of the distance deflate codes,
-- in fixed deflate block.
local _fix_block_dist_huffman_bitlen

-- The count of each bit length of the huffman code of
-- the distance deflate codes,
-- in fixed deflate block.
local _fix_block_dist_huffman_bitlen_count

for i = 0, 255 do _byte_to_char[i] = string_char(i) end

do
  local pow = 1
  for i = 0, 32 do
    _pow2[i] = pow
    pow = pow * 2
  end
end

for i = 1, 9 do
  _reverse_bits_tbl[i] = {}
  for j = 0, _pow2[i + 1] - 1 do
    local reverse = 0
    local value = j
    for _ = 1, i do
      -- The following line is equivalent to "res | (code %2)" in C.
      reverse = reverse - reverse % 2 +
                  (((reverse % 2 == 1) or (value % 2) == 1) and 1 or 0)
      value = (value - value % 2) / 2
      reverse = reverse * 2
    end
    _reverse_bits_tbl[i][j] = (reverse - reverse % 2) / 2
  end
end

-- The source code is written according to the pattern in the numbers
-- in RFC1951 Page10.
do
  local a = 18
  local b = 16
  local c = 265
  local bitlen = 1
  for len = 3, 258 do
    if len <= 10 then
      _length_to_deflate_code[len] = len + 254
      _length_to_deflate_extra_bitlen[len] = 0
    elseif len == 258 then
      _length_to_deflate_code[len] = 285
      _length_to_deflate_extra_bitlen[len] = 0
    else
      if len > a then
        a = a + b
        b = b * 2
        c = c + 4
        bitlen = bitlen + 1
      end
      local t = len - a - 1 + b / 2
      _length_to_deflate_code[len] = (t - (t % (b / 8))) / (b / 8) + c
      _length_to_deflate_extra_bitlen[len] = bitlen
      _length_to_deflate_extra_bits[len] = t % (b / 8)
    end
  end
end

-- The source code is written according to the pattern in the numbers
-- in RFC1951 Page11.
do
  _dist256_to_deflate_code[1] = 0
  _dist256_to_deflate_code[2] = 1
  _dist256_to_deflate_extra_bitlen[1] = 0
  _dist256_to_deflate_extra_bitlen[2] = 0

  local a = 3
  local b = 4
  local code = 2
  local bitlen = 0
  for dist = 3, 256 do
    if dist > b then
      a = a * 2
      b = b * 2
      code = code + 2
      bitlen = bitlen + 1
    end
    _dist256_to_deflate_code[dist] = (dist <= a) and code or (code + 1)
    _dist256_to_deflate_extra_bitlen[dist] = (bitlen < 0) and 0 or bitlen
    if b >= 8 then
      _dist256_to_deflate_extra_bits[dist] = (dist - b / 2 - 1) % (b / 4)
    end
  end
end

--- Calculate the Adler-32 checksum of the string. <br>
-- See RFC1950 Page 9 https://tools.ietf.org/html/rfc1950 for the
-- definition of Adler-32 checksum.
-- @param str [string] the input string to calcuate its Adler-32 checksum.
-- @return [integer] The Adler-32 checksum, which is greater or equal to 0,
-- and less than 2^32 (4294967296).
local function Adler32(str)
  -- This function is loop unrolled by better performance.
  --
  -- Here is the minimum code:
  --
  -- local a = 1
  -- local b = 0
  -- for i=1, #str do
  --            local s = string.byte(str, i, i)
  --            a = (a+s)%65521
  --            b = (b+a)%65521
  --            end
  -- return b*65536+a
  if type(str) ~= "string" then
    error(("Usage: Adler32(str):" ..
            " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  local strlen = #str

  local i = 1
  local a = 1
  local b = 0
  while i <= strlen - 15 do
    local x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16 =
      string_byte(str, i, i + 15)
    b =
      (b + 16 * a + 16 * x1 + 15 * x2 + 14 * x3 + 13 * x4 + 12 * x5 + 11 * x6 +
        10 * x7 + 9 * x8 + 8 * x9 + 7 * x10 + 6 * x11 + 5 * x12 + 4 * x13 + 3 *
        x14 + 2 * x15 + x16) % 65521
    a =
      (a + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 +
        x14 + x15 + x16) % 65521
    i = i + 16
  end
  while (i <= strlen) do
    local x = string_byte(str, i, i)
    a = (a + x) % 65521
    b = (b + a) % 65521
    i = i + 1
  end
  return (b * 65536 + a) % 4294967296
end

-- Compare adler32 checksum.
-- adler32 should be compared with a mod to avoid sign problem
-- 4072834167 (unsigned) is the same adler32 as -222133129
local function IsEqualAdler32(actual, expected)
  return (actual % 4294967296) == (expected % 4294967296)
end

--- Create a preset dictionary.
--
-- This function is not fast, and the memory consumption of the produced
-- dictionary is about 50 times of the input string. Therefore, it is suggestted
-- to run this function only once in your program.
--
-- It is very important to know that if you do use a preset dictionary,
-- compressors and decompressors MUST USE THE SAME dictionary. That is,
-- dictionary must be created using the same string. If you update your program
-- with a new dictionary, people with the old version won't be able to transmit
-- data with people with the new version. Therefore, changing the dictionary
-- must be very careful.
--
-- The parameters "strlen" and "adler32" add a layer of verification to ensure
-- the parameter "str" is not modified unintentionally during the program
-- development.
--
-- @usage local dict_str = "1234567890"
--
-- -- print(dict_str:len(), LibDeflate:Adler32(dict_str))
-- -- Hardcode the print result below to verify it to avoid acciently
-- -- modification of 'str' during the program development.
-- -- string length: 10, Adler-32: 187433486,
-- -- Don't calculate string length and its Adler-32 at run-time.
--
-- local dict = LibDeflate:CreateDictionary(dict_str, 10, 187433486)
--
-- @param str [string] The string used as the preset dictionary. <br>
-- You should put stuffs that frequently appears in the dictionary
-- string and preferablely put more frequently appeared stuffs toward the end
-- of the string. <br>
-- Empty string and string longer than 32768 bytes are not allowed.
-- @param strlen [integer] The length of 'str'. Please pass in this parameter
-- as a hardcoded constant, in order to verify the content of 'str'. The value
-- of this parameter should be known before your program runs.
-- @param adler32 [integer] The Adler-32 checksum of 'str'. Please pass in this
-- parameter as a hardcoded constant, in order to verify the content of 'str'.
-- The value of this parameter should be known before your program runs.
-- @return  [table] The dictionary used for preset dictionary compression and
-- decompression.
-- @raise error if 'strlen' does not match the length of 'str',
-- or if 'adler32' does not match the Adler-32 checksum of 'str'.

local function CreateDictionary(str, strlen, adler32)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  if type(strlen) ~= "number" then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'strlen' - number expected got '%s'."):format(type(strlen)), 2)
  end
  if type(adler32) ~= "number" then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'adler32' - number expected got '%s'."):format(type(adler32)), 2)
  end
  if strlen ~= #str then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'strlen' does not match the actual length of 'str'." ..
            " 'strlen': %u, '#str': %u ." ..
            " Please check if 'str' is modified unintentionally."):format(
            strlen, #str))
  end
  if strlen == 0 then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'str' - Empty string is not allowed."), 2)
  end
  if strlen > 32768 then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'str' - string longer than 32768 bytes is not allowed." ..
            " Got %d bytes."):format(strlen), 2)
  end
  local actual_adler32 = self:Adler32(str)
  if not IsEqualAdler32(adler32, actual_adler32) then
    error(("Usage: LibDeflate:CreateDictionary(str, strlen, adler32):" ..
            " 'adler32' does not match the actual adler32 of 'str'." ..
            " 'adler32': %u, 'Adler32(str)': %u ." ..
            " Please check if 'str' is modified unintentionally."):format(
            adler32, actual_adler32))
  end

  local dictionary = {}
  dictionary.adler32 = adler32
  dictionary.hash_tables = {}
  dictionary.string_table = {}
  dictionary.strlen = strlen
  local string_table = dictionary.string_table
  local hash_tables = dictionary.hash_tables
  string_table[1] = string_byte(str, 1, 1)
  string_table[2] = string_byte(str, 2, 2)
  if strlen >= 3 then
    local i = 1
    local hash = string_table[1] * 256 + string_table[2]
    while i <= strlen - 2 - 3 do
      local x1, x2, x3, x4 = string_byte(str, i + 2, i + 5)
      string_table[i + 2] = x1
      string_table[i + 3] = x2
      string_table[i + 4] = x3
      string_table[i + 5] = x4
      hash = (hash * 256 + x1) % 16777216
      local t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = i - strlen
      i = i + 1
      hash = (hash * 256 + x2) % 16777216
      t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = i - strlen
      i = i + 1
      hash = (hash * 256 + x3) % 16777216
      t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = i - strlen
      i = i + 1
      hash = (hash * 256 + x4) % 16777216
      t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = i - strlen
      i = i + 1
    end
    while i <= strlen - 2 do
      local x = string_byte(str, i + 2)
      string_table[i + 2] = x
      hash = (hash * 256 + x) % 16777216
      local t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = i - strlen
      i = i + 1
    end
  end
  return dictionary
end

-- Check if the dictionary is valid.
-- @param dictionary The preset dictionary for compression and decompression.
-- @return true if valid, false if not valid.
-- @return if not valid, the error message.
local function IsValidDictionary(dictionary)
  if type(dictionary) ~= "table" then
    return false,
           ("'dictionary' - table expected got '%s'."):format(type(dictionary))
  end
  if type(dictionary.adler32) ~= "number" or type(dictionary.string_table) ~=
    "table" or type(dictionary.strlen) ~= "number" or dictionary.strlen <= 0 or
    dictionary.strlen > 32768 or dictionary.strlen ~= #dictionary.string_table or
    type(dictionary.hash_tables) ~= "table" then
    return false,
           ("'dictionary' - corrupted dictionary."):format(type(dictionary))
  end
  return true, ""
end

--[[
        key of the configuration table is the compression level,
        and its value stores the compression setting.
        These numbers come from zlib source code.

        Higher compression level usually means better compression.
        (Because LibDeflate uses a simplified version of zlib algorithm,
        there is no guarantee that higher compression level does not create
        bigger file than lower level, but I can say it's 99% likely)

        Be careful with the high compression level. This is a pure lua
        implementation compressor/decompressor, which is significant slower than
        a C/C++ equivalant compressor/decompressor. Very high compression level
        costs significant more CPU time, and usually compression size won't be
        significant smaller when you increase compression level by 1, when the
        level is already very high. Benchmark yourself if you can afford it.

        See also https://github.com/madler/zlib/blob/master/doc/algorithm.txt,
        https://github.com/madler/zlib/blob/master/deflate.c for more information.

        The meaning of each field:
        @field 1 use_lazy_evaluation:
                true/false. Whether the program uses lazy evaluation.
                See what is "lazy evaluation" in the link above.
                lazy_evaluation improves ratio, but relatively slow.
        @field 2 good_prev_length:
                Only effective if lazy is set, Only use 1/4 of max_chain,
                if prev length of lazy match is above this.
        @field 3 max_insert_length/max_lazy_match:
                If not using lazy evaluation,
                insert new strings in the hash table only if the match length is not
                greater than this length.
                If using lazy evaluation, only continue lazy evaluation,
                if previous match length is strictly smaller than this value.
        @field 4 nice_length:
                Number. Don't continue to go down the hash chain,
                if match length is above this.
        @field 5 max_chain:
                Number. The maximum number of hash chains we look.
--]]

local _compression_level_configs = {
  [0] = {false, nil, 0, 0, 0}, -- level 0, no compression
  [1] = {false, nil, 4, 8, 4}, -- level 1, similar to zlib level 1
  [2] = {false, nil, 5, 18, 8}, -- level 2, similar to zlib level 2
  [3] = {false, nil, 6, 32, 32}, -- level 3, similar to zlib level 3
  [4] = {true, 4, 4, 16, 16}, -- level 4, similar to zlib level 4
  [5] = {true, 8, 16, 32, 32}, -- level 5, similar to zlib level 5
  [6] = {true, 8, 16, 128, 128}, -- level 6, similar to zlib level 6
  [7] = {true, 8, 32, 128, 256}, -- (SLOW) level 7, similar to zlib level 7
  [8] = {true, 32, 128, 258, 1024}, -- (SLOW) level 8,similar to zlib level 8
  [9] = {true, 32, 258, 258, 4096}
  -- (VERY SLOW) level 9, similar to zlib level 9
}

-- Check if the compression/decompression arguments is valid
-- @param str The input string.
-- @param check_dictionary if true, check if dictionary is valid.
-- @param dictionary The preset dictionary for compression and decompression.
-- @param check_configs if true, check if config is valid.
-- @param configs The compression configuration table
-- @return true if valid, false if not valid.
-- @return if not valid, the error message.
local function IsValidArguments(str, check_dictionary, dictionary,
                                check_configs, configs)

  if type(str) ~= "string" then
    return false, ("'str' - string expected got '%s'."):format(type(str))
  end
  if check_dictionary then
    local dict_valid, dict_err = IsValidDictionary(dictionary)
    if not dict_valid then return false, dict_err end
  end
  if check_configs then
    local type_configs = type(configs)
    if type_configs ~= "nil" and type_configs ~= "table" then
      return false, ("'configs' - nil or table expected got '%s'."):format(
               type(configs))
    end
    if type_configs == "table" then
      for k, v in pairs(configs) do
        if k ~= "level" and k ~= "strategy" then
          return false,
                 ("'configs' - unsupported table key in the configs: '%s'."):format(
                   k)
        elseif k == "level" and not _compression_level_configs[v] then
          return false,
                 ("'configs' - unsupported 'level': %s."):format(tostring(v))
        elseif k == "strategy" and v ~= "fixed" and v ~= "huffman_only" and v ~=
          "dynamic" then
          -- random_block_type is for testing purpose
          return false, ("'configs' - unsupported 'strategy': '%s'."):format(
                   tostring(v))
        end
      end
    end
  end
  return true, ""
end

--[[ --------------------------------------------------------------------------
        Compress code
--]] --------------------------------------------------------------------------

-- partial flush to save memory
local _FLUSH_MODE_MEMORY_CLEANUP = 0
-- full flush with partial bytes
local _FLUSH_MODE_OUTPUT = 1
-- write bytes to get to byte boundary
local _FLUSH_MODE_BYTE_BOUNDARY = 2
-- no flush, just get num of bits written so far
local _FLUSH_MODE_NO_FLUSH = 3

--[[
        Create an empty writer to easily write stuffs as the unit of bits.
        Return values:
        1. WriteBits(code, bitlen):
        2. WriteString(str):
        3. Flush(mode):
--]]

local function CreateWriter()
  local buffer_size = 0
  local cache = 0
  local cache_bitlen = 0
  local total_bitlen = 0
  local buffer = {}
  -- When buffer is big enough, flush into result_buffer to save memory.
  local result_buffer = {}

  -- Write bits with value "value" and bit length of "bitlen" into writer.
  -- @param value: The value being written
  -- @param bitlen: The bit length of "value"
  -- @return nil
  local function WriteBits(value, bitlen)
    cache = cache + value * _pow2[cache_bitlen]
    cache_bitlen = cache_bitlen + bitlen
    total_bitlen = total_bitlen + bitlen
    -- Only bulk to buffer every 4 bytes. This is quicker.
    if cache_bitlen >= 32 then
      buffer_size = buffer_size + 1
      buffer[buffer_size] = _byte_to_char[cache % 256] ..
                              _byte_to_char[((cache - cache % 256) / 256 % 256)] ..
                              _byte_to_char[((cache - cache % 65536) / 65536 %
                                256)] ..
                              _byte_to_char[((cache - cache % 16777216) /
                                16777216 % 256)]
      local rshift_mask = _pow2[32 - cache_bitlen + bitlen]
      cache = (value - value % rshift_mask) / rshift_mask
      cache_bitlen = cache_bitlen - 32
    end
  end

  -- Write the entire string into the writer.
  -- @param str The string being written
  -- @return nil
  local function WriteString(str)
    for _ = 1, cache_bitlen, 8 do
      buffer_size = buffer_size + 1
      buffer[buffer_size] = string_char(cache % 256)
      cache = (cache - cache % 256) / 256
    end
    cache_bitlen = 0
    buffer_size = buffer_size + 1
    buffer[buffer_size] = str
    total_bitlen = total_bitlen + #str * 8
  end

  -- Flush current stuffs in the writer and return it.
  -- This operation will free most of the memory.
  -- @param mode See the descrtion of the constant and the source code.
  -- @return The total number of bits stored in the writer right now.
  -- for byte boundary mode, it includes the padding bits.
  -- for output mode, it does not include padding bits.
  -- @return Return the outputs if mode is output.
  local function FlushWriter(mode)
    if mode == _FLUSH_MODE_NO_FLUSH then return total_bitlen end

    if mode == _FLUSH_MODE_OUTPUT or mode == _FLUSH_MODE_BYTE_BOUNDARY then
      -- Full flush, also output cache.
      -- Need to pad some bits if cache_bitlen is not multiple of 8.
      local padding_bitlen = (8 - cache_bitlen % 8) % 8

      if cache_bitlen > 0 then
        -- padding with all 1 bits, mainly because "\000" is not
        -- good to be tranmitted. I do this so "\000" is a little bit
        -- less frequent.
        cache = cache - _pow2[cache_bitlen] +
                  _pow2[cache_bitlen + padding_bitlen]
        for _ = 1, cache_bitlen, 8 do
          buffer_size = buffer_size + 1
          buffer[buffer_size] = _byte_to_char[cache % 256]
          cache = (cache - cache % 256) / 256
        end

        cache = 0
        cache_bitlen = 0
      end
      if mode == _FLUSH_MODE_BYTE_BOUNDARY then
        total_bitlen = total_bitlen + padding_bitlen
        return total_bitlen
      end
    end
    
    local size2 = 0
    for _ in pairs(buffer) do size2 = size2 + 1 end
    
    -- local flushed = table_concat(buffer)
    local flushed = ''
    for i, v in ipairs(buffer) do flushed = flushed..v end
    -- local flushed = ""
    buffer = {}
    buffer_size = 0
    result_buffer[#result_buffer + 1] = flushed

    if mode == _FLUSH_MODE_MEMORY_CLEANUP then
      return total_bitlen
    else
      return total_bitlen, table_concat(result_buffer)
    end
  end

  return WriteBits, WriteString, FlushWriter
end

-- Push an element into a max heap
-- @param heap A max heap whose max element is at index 1.
-- @param e The element to be pushed. Assume element "e" is a table
--  and comparison is done via its first entry e[1]
-- @param heap_size current number of elements in the heap.
--  NOTE: There may be some garbage stored in
--  heap[heap_size+1], heap[heap_size+2], etc..
-- @return nil
local function MinHeapPush(heap, e, heap_size)
  heap_size = heap_size + 1
  heap[heap_size] = e
  local value = e[1]
  local pos = heap_size
  local parent_pos = (pos - pos % 2) / 2

  while (parent_pos >= 1 and heap[parent_pos][1] > value) do
    local t = heap[parent_pos]
    heap[parent_pos] = e
    heap[pos] = t
    pos = parent_pos
    parent_pos = (parent_pos - parent_pos % 2) / 2
  end
end

-- Pop an element from a max heap
-- @param heap A max heap whose max element is at index 1.
-- @param heap_size current number of elements in the heap.
-- @return the poped element
-- Note: This function does not change table size of "heap" to save CPU time.

local function MinHeapPop(heap, heap_size)
  local top = heap[1]
  local e = heap[heap_size]
  local value = e[1]
  heap[1] = e
  heap[heap_size] = top
  heap_size = heap_size - 1

  local pos = 1
  local left_child_pos = pos * 2
  local right_child_pos = left_child_pos + 1

  while (left_child_pos <= heap_size) do
    local left_child = heap[left_child_pos]
    if (right_child_pos <= heap_size and heap[right_child_pos][1] <
      left_child[1]) then
      local right_child = heap[right_child_pos]
      if right_child[1] < value then
        heap[right_child_pos] = e
        heap[pos] = right_child
        pos = right_child_pos
        left_child_pos = pos * 2
        right_child_pos = left_child_pos + 1
      else
        break
      end
    else
      if left_child[1] < value then
        heap[left_child_pos] = e
        heap[pos] = left_child
        pos = left_child_pos
        left_child_pos = pos * 2
        right_child_pos = left_child_pos + 1
      else
        break
      end
    end
  end

  return top
end

-- Deflate defines a special huffman tree, which is unique once the bit length
-- of huffman code of all symbols are known.
-- @param bitlen_count Number of symbols with a specific bitlen
-- @param symbol_bitlen The bit length of a symbol
-- @param max_symbol The max symbol among all symbols,
--              which is (number of symbols - 1)
-- @param max_bitlen The max huffman bit length among all symbols.
-- @return The huffman code of all symbols.
local function GetHuffmanCodeFromBitlen(bitlen_counts, symbol_bitlens,
                                        max_symbol, max_bitlen)
  local huffman_code = 0
  local next_codes = {}
  local symbol_huffman_codes = {}
  for bitlen = 1, max_bitlen do
    huffman_code = (huffman_code + (bitlen_counts[bitlen - 1] or 0)) * 2
    next_codes[bitlen] = huffman_code
  end
  for symbol = 0, max_symbol do
    local bitlen = symbol_bitlens[symbol]
    if bitlen then
      huffman_code = next_codes[bitlen]
      next_codes[bitlen] = huffman_code + 1

      -- Reverse the bits of huffman code,
      -- because most signifant bits of huffman code
      -- is stored first into the compressed data.
      -- @see RFC1951 Page5 Section 3.1.1
      if bitlen <= 9 then -- Have cached reverse for small bitlen.
        symbol_huffman_codes[symbol] = _reverse_bits_tbl[bitlen][huffman_code]
      else
        local reverse = 0
        for _ = 1, bitlen do
          reverse = reverse - reverse % 2 +
                      (((reverse % 2 == 1) or (huffman_code % 2) == 1) and 1 or
                        0)
          huffman_code = (huffman_code - huffman_code % 2) / 2
          reverse = reverse * 2
        end
        symbol_huffman_codes[symbol] = (reverse - reverse % 2) / 2
      end
    end
  end
  return symbol_huffman_codes
end

-- A helper function to sort heap elements
-- a[1], b[1] is the huffman frequency
-- a[2], b[2] is the symbol value.
local function SortByFirstThenSecond(a, b)
  return a[1] < b[1] or (a[1] == b[1] and a[2] < b[2])
end

-- Calculate the huffman bit length and huffman code.
-- @param symbol_count: A table whose table key is the symbol, and table value
--              is the symbol frenquency (nil means 0 frequency).
-- @param max_bitlen: See description of return value.
-- @param max_symbol: The maximum symbol
-- @return a table whose key is the symbol, and the value is the huffman bit
--              bit length. We guarantee that all bit length <= max_bitlen.
--              For 0<=symbol<=max_symbol, table value could be nil if the frequency
--              of the symbol is 0 or nil.
-- @return a table whose key is the symbol, and the value is the huffman code.
-- @return a number indicating the maximum symbol whose bitlen is not 0.
local function GetHuffmanBitlenAndCode(symbol_counts, max_bitlen, max_symbol)
  local heap_size
  local max_non_zero_bitlen_symbol = -1
  local leafs = {}
  local heap = {}
  local symbol_bitlens = {}
  local symbol_codes = {}
  local bitlen_counts = {}

  --[[
                tree[1]: weight, temporarily used as parent and bitLengths
                tree[2]: symbol
                tree[3]: left child
                tree[4]: right child
        --]]
  local number_unique_symbols = 0
  for symbol, count in pairs(symbol_counts) do
    number_unique_symbols = number_unique_symbols + 1
    leafs[number_unique_symbols] = {count, symbol}
  end

  if (number_unique_symbols == 0) then
    -- no code.
    return {}, {}, -1
  elseif (number_unique_symbols == 1) then
    -- Only one code. In this case, its huffman code
    -- needs to be assigned as 0, and bit length is 1.
    -- This is the only case that the return result
    -- represents an imcomplete huffman tree.
    local symbol = leafs[1][2]
    symbol_bitlens[symbol] = 1
    symbol_codes[symbol] = 0
    return symbol_bitlens, symbol_codes, symbol
  else
    table_sort(leafs, SortByFirstThenSecond)
    heap_size = number_unique_symbols
    for i = 1, heap_size do heap[i] = leafs[i] end
    
    while (heap_size > 1) do
      -- Note: pop does not change table size of heap
      local leftChild = MinHeapPop(heap, heap_size)
      heap_size = heap_size - 1
      local rightChild = MinHeapPop(heap, heap_size)
      heap_size = heap_size - 1
      local newNode = {leftChild[1] + rightChild[1], -1, leftChild, rightChild}
      MinHeapPush(heap, newNode, heap_size)
      heap_size = heap_size + 1
    end

    -- Number of leafs whose bit length is greater than max_len.
    local number_bitlen_overflow = 0

    -- Calculate bit length of all nodes
    local fifo = {heap[1], 0, 0, 0} -- preallocate some spaces.
    local fifo_size = 1
    local index = 1
    heap[1][1] = 0
    while (index <= fifo_size) do -- Breath first search
      local e = fifo[index]
      local bitlen = e[1]
      local symbol = e[2]
      local left_child = e[3]
      local right_child = e[4]
      if left_child then
        fifo_size = fifo_size + 1
        fifo[fifo_size] = left_child
        left_child[1] = bitlen + 1
      end
      if right_child then
        fifo_size = fifo_size + 1
        fifo[fifo_size] = right_child
        right_child[1] = bitlen + 1
      end
      index = index + 1

      if (bitlen > max_bitlen) then
        number_bitlen_overflow = number_bitlen_overflow + 1
        bitlen = max_bitlen
      end
      if symbol >= 0 then
        symbol_bitlens[symbol] = bitlen
        max_non_zero_bitlen_symbol = (symbol > max_non_zero_bitlen_symbol) and
                                       symbol or max_non_zero_bitlen_symbol
        bitlen_counts[bitlen] = (bitlen_counts[bitlen] or 0) + 1
      end
    end

    -- Resolve bit length overflow
    -- @see ZLib/trees.c:gen_bitlen(s, desc), for reference
    if (number_bitlen_overflow > 0) then
      repeat
        local bitlen = max_bitlen - 1
        while ((bitlen_counts[bitlen] or 0) == 0) do bitlen = bitlen - 1 end
        -- move one leaf down the tree
        bitlen_counts[bitlen] = bitlen_counts[bitlen] - 1
        -- move one overflow item as its brother
        bitlen_counts[bitlen + 1] = (bitlen_counts[bitlen + 1] or 0) + 2
        bitlen_counts[max_bitlen] = bitlen_counts[max_bitlen] - 1
        number_bitlen_overflow = number_bitlen_overflow - 2
      until (number_bitlen_overflow <= 0)

      index = 1
      for bitlen = max_bitlen, 1, -1 do
        local n = bitlen_counts[bitlen] or 0
        while (n > 0) do
          local symbol = leafs[index][2]
          symbol_bitlens[symbol] = bitlen
          n = n - 1
          index = index + 1
        end
      end
    end

    symbol_codes = GetHuffmanCodeFromBitlen(bitlen_counts, symbol_bitlens,
                                            max_symbol, max_bitlen)
    return symbol_bitlens, symbol_codes, max_non_zero_bitlen_symbol
  end
end
     
-- Calculate the first huffman header in the dynamic huffman block
-- @see RFC1951 Page 12
-- @param lcode_bitlen: The huffman bit length of literal/LZ77_length.
-- @param max_non_zero_bitlen_lcode: The maximum literal/LZ77_length symbol
--              whose huffman bit length is not zero.
-- @param dcode_bitlen: The huffman bit length of LZ77 distance.
-- @param max_non_zero_bitlen_dcode: The maximum LZ77 distance symbol
--              whose huffman bit length is not zero.
-- @return The run length encoded codes.
-- @return The extra bits. One entry for each rle code that needs extra bits.
--              (code == 16 or 17 or 18).
-- @return The count of appearance of each rle codes.
local function RunLengthEncodeHuffmanBitlen(lcode_bitlens,
                                            max_non_zero_bitlen_lcode,
                                            dcode_bitlens,
                                            max_non_zero_bitlen_dcode)
  local rle_code_tblsize = 0
  local rle_codes = {}
  local rle_code_counts = {}
  local rle_extra_bits_tblsize = 0
  local rle_extra_bits = {}
  local prev = nil
  local count = 0

  -- If there is no distance code, assume one distance code of bit length 0.
  -- RFC1951: One distance code of zero bits means that
  -- there are no distance codes used at all (the data is all literals).
  max_non_zero_bitlen_dcode = (max_non_zero_bitlen_dcode < 0) and 0 or
                                max_non_zero_bitlen_dcode
  local max_code = max_non_zero_bitlen_lcode + max_non_zero_bitlen_dcode + 1

  for code = 0, max_code + 1 do
    local len = (code <= max_non_zero_bitlen_lcode) and
                  (lcode_bitlens[code] or 0) or ((code <= max_code) and
                  (dcode_bitlens[code - max_non_zero_bitlen_lcode - 1] or 0) or
                  nil)
    if len == prev then
      count = count + 1
      if len ~= 0 and count == 6 then
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = 16
        rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
        rle_extra_bits[rle_extra_bits_tblsize] = 3
        rle_code_counts[16] = (rle_code_counts[16] or 0) + 1
        count = 0
      elseif len == 0 and count == 138 then
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = 18
        rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
        rle_extra_bits[rle_extra_bits_tblsize] = 127
        rle_code_counts[18] = (rle_code_counts[18] or 0) + 1
        count = 0
      end
    else
      if count == 1 then
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = prev
        rle_code_counts[prev] = (rle_code_counts[prev] or 0) + 1
      elseif count == 2 then
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = prev
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = prev
        rle_code_counts[prev] = (rle_code_counts[prev] or 0) + 2
      elseif count >= 3 then
        rle_code_tblsize = rle_code_tblsize + 1
        local rleCode = (prev ~= 0) and 16 or (count <= 10 and 17 or 18)
        rle_codes[rle_code_tblsize] = rleCode
        rle_code_counts[rleCode] = (rle_code_counts[rleCode] or 0) + 1
        rle_extra_bits_tblsize = rle_extra_bits_tblsize + 1
        rle_extra_bits[rle_extra_bits_tblsize] =
          (count <= 10) and (count - 3) or (count - 11)
      end

      prev = len
      if len and len ~= 0 then
        rle_code_tblsize = rle_code_tblsize + 1
        rle_codes[rle_code_tblsize] = len
        rle_code_counts[len] = (rle_code_counts[len] or 0) + 1
        count = 0
      else
        count = 1
      end
    end
  end

  return rle_codes, rle_extra_bits, rle_code_counts
end

-- Load the string into a table, in order to speed up LZ77.
-- Loop unrolled 16 times to speed this function up.
-- @param str The string to be loaded.
-- @param t The load destination
-- @param start str[index] will be the first character to be loaded.
-- @param end str[index] will be the last character to be loaded
-- @param offset str[index] will be loaded into t[index-offset]
-- @return t
local function LoadStringToTable(str, t, start, stop, offset)
  local i = start - offset
  while i <= stop - 15 - offset do
    t[i], t[i + 1], t[i + 2], t[i + 3], t[i + 4], t[i + 5], t[i + 6], t[i + 7], t[i +
      8], t[i + 9], t[i + 10], t[i + 11], t[i + 12], t[i + 13], t[i + 14], t[i +
      15] = string_byte(str, i + offset, i + 15 + offset)
    i = i + 16
  end
  while (i <= stop - offset) do
    t[i] = string_byte(str, i + offset, i + offset)
    i = i + 1
  end
  return t
end

-- Do LZ77 process. This function uses the majority of the CPU time.
-- @see zlib/deflate.c:deflate_fast(), zlib/deflate.c:deflate_slow()
-- @see https://github.com/madler/zlib/blob/master/doc/algorithm.txt
-- This function uses the algorithms used above. You should read the
-- algorithm.txt above to understand what is the hash function and the
-- lazy evaluation.
--
-- The special optimization used here is hash functions used here.
-- The hash function is just the multiplication of the three consective
-- characters. So if the hash matches, it guarantees 3 characters are matched.
-- This optimization can be implemented because Lua table is a hash table.
--
-- @param level integer that describes compression level.
-- @param string_table table that stores the value of string to be compressed.
--                      The index of this table starts from 1.
--                      The caller needs to make sure all values needed by this function
--                      are loaded.
--                      Assume "str" is the origin input string into the compressor
--                      str[block_start]..str[block_end+3] needs to be loaded into
--                      string_table[block_start-offset]..string_table[block_end-offset]
--                      If dictionary is presented, the last 258 bytes of the dictionary
--                      needs to be loaded into sing_table[-257..0]
--                      (See more in the description of offset.)
-- @param hash_tables. The table key is the hash value (0<=hash<=16777216=256^3)
--                      The table value is an array0 that stores the indexes of the
--                      input data string to be compressed, such that
--                      hash == str[index]*str[index+1]*str[index+2]
--                      Indexes are ordered in this array.
-- @param block_start The indexes of the input data string to be compressed.
--                              that starts the LZ77 block.
-- @param block_end The indexes of the input data string to be compressed.
--                              that stores the LZ77 block.
-- @param offset str[index] is stored in string_table[index-offset],
--                      This offset is mainly an optimization to limit the index
--                      of string_table, so lua can access this table quicker.
-- @param dictionary See LibDeflate:CreateDictionary
-- @return literal/LZ77_length deflate codes.
-- @return the extra bits of literal/LZ77_length deflate codes.
-- @return the count of each literal/LZ77 deflate code.
-- @return LZ77 distance deflate codes.
-- @return the extra bits of LZ77 distance deflate codes.
-- @return the count of each LZ77 distance deflate code.
local function GetBlockLZ77Result(level, string_table, hash_tables, block_start,
                                  block_end, offset, dictionary)
  local config = _compression_level_configs[level]
  local config_use_lazy, config_good_prev_length, config_max_lazy_match,
        config_nice_length, config_max_hash_chain = config[1], config[2],
                                                    config[3], config[4],
                                                    config[5]

  local config_max_insert_length = (not config_use_lazy) and
                                     config_max_lazy_match or 2147483646
  local config_good_hash_chain =
    (config_max_hash_chain - config_max_hash_chain % 4 / 4)

  local hash

  local dict_hash_tables
  local dict_string_table
  local dict_string_len = 0

  if dictionary then
    dict_hash_tables = dictionary.hash_tables
    dict_string_table = dictionary.string_table
    dict_string_len = dictionary.strlen
    assert(block_start == 1)
    if block_end >= block_start and dict_string_len >= 2 then
      hash = dict_string_table[dict_string_len - 1] * 65536 +
               dict_string_table[dict_string_len] * 256 + string_table[1]
      local t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = -1
    end
    if block_end >= block_start + 1 and dict_string_len >= 1 then
      hash =
        dict_string_table[dict_string_len] * 65536 + string_table[1] * 256 +
          string_table[2]
      local t = hash_tables[hash]
      if not t then
        t = {};
        hash_tables[hash] = t
      end
      t[#t + 1] = 0
    end
  end

  local dict_string_len_plus3 = dict_string_len + 3

  hash = (string_table[block_start - offset] or 0) * 256 +
           (string_table[block_start + 1 - offset] or 0)

  local lcodes = {}
  local lcode_tblsize = 0
  local lcodes_counts = {}
  local dcodes = {}
  local dcodes_tblsize = 0
  local dcodes_counts = {}

  local lextra_bits = {}
  local lextra_bits_tblsize = 0
  local dextra_bits = {}
  local dextra_bits_tblsize = 0

  local match_available = false
  local prev_len
  local prev_dist
  local cur_len = 0
  local cur_dist = 0

  local index = block_start
  local index_end = block_end + (config_use_lazy and 1 or 0)
  -- the zlib source code writes separate code for lazy evaluation and
  -- not lazy evaluation, which is easier to understand.
  -- I put them together, so it is a bit harder to understand.
  -- because I think this is easier for me to maintain it.
  while (index <= index_end) do
    local string_table_index = index - offset
    local offset_minus_three = offset - 3
    prev_len = cur_len
    prev_dist = cur_dist
    cur_len = 0

    hash = (hash * 256 + (string_table[string_table_index + 2] or 0)) % 16777216

    local chain_index
    local cur_chain
    local hash_chain = hash_tables[hash]
    local chain_old_size
    if not hash_chain then
      chain_old_size = 0
      hash_chain = {}
      hash_tables[hash] = hash_chain
      if dict_hash_tables then
        cur_chain = dict_hash_tables[hash]
        chain_index = cur_chain and #cur_chain or 0
      else
        chain_index = 0
      end
    else
      chain_old_size = #hash_chain
      cur_chain = hash_chain
      chain_index = chain_old_size
    end

    if index <= block_end then hash_chain[chain_old_size + 1] = index end
    if (chain_index > 0 and index + 2 <= block_end and
      (not config_use_lazy or prev_len < config_max_lazy_match)) then

      local depth =
        (config_use_lazy and prev_len >= config_good_prev_length) and
          config_good_hash_chain or config_max_hash_chain

      local max_len_minus_one = block_end - index
      max_len_minus_one = (max_len_minus_one >= 257) and 257 or
                            max_len_minus_one
      max_len_minus_one = max_len_minus_one + string_table_index
      local string_table_index_plus_three = string_table_index + 3

      while chain_index >= 1 and depth > 0 do
        local prev = cur_chain[chain_index]

        if index - prev > 32768 then break end
        if prev < index then
          local sj = string_table_index_plus_three

          if prev >= -257 then
            local pj = prev - offset_minus_three
            while (sj <= max_len_minus_one and string_table[pj] ==
              string_table[sj]) do
              sj = sj + 1
              pj = pj + 1
            end
          else
            local pj = dict_string_len_plus3 + prev
            while (sj <= max_len_minus_one and dict_string_table[pj] ==
              string_table[sj]) do
              sj = sj + 1
              pj = pj + 1
            end
          end
          local j = sj - string_table_index
          if j > cur_len then
            cur_len = j
            cur_dist = index - prev
          end
          if cur_len >= config_nice_length then break end
        end

        chain_index = chain_index - 1
        depth = depth - 1
        if chain_index == 0 and prev > 0 and dict_hash_tables then
          cur_chain = dict_hash_tables[hash]
          chain_index = cur_chain and #cur_chain or 0
        end
      end
    end

    if not config_use_lazy then prev_len, prev_dist = cur_len, cur_dist end
    if ((not config_use_lazy or match_available) and
      (prev_len > 3 or (prev_len == 3 and prev_dist < 4096)) and cur_len <=
      prev_len) then
      local code = _length_to_deflate_code[prev_len]
      local length_extra_bits_bitlen = _length_to_deflate_extra_bitlen[prev_len]
      local dist_code, dist_extra_bits_bitlen, dist_extra_bits
      if prev_dist <= 256 then -- have cached code for small distance.
        dist_code = _dist256_to_deflate_code[prev_dist]
        dist_extra_bits = _dist256_to_deflate_extra_bits[prev_dist]
        dist_extra_bits_bitlen = _dist256_to_deflate_extra_bitlen[prev_dist]
      else
        dist_code = 16
        dist_extra_bits_bitlen = 7
        local a = 384
        local b = 512

        while true do
          if prev_dist <= a then
            dist_extra_bits = (prev_dist - (b / 2) - 1) % (b / 4)
            break
          elseif prev_dist <= b then
            dist_extra_bits = (prev_dist - (b / 2) - 1) % (b / 4)
            dist_code = dist_code + 1
            break
          else
            dist_code = dist_code + 2
            dist_extra_bits_bitlen = dist_extra_bits_bitlen + 1
            a = a * 2
            b = b * 2
          end
        end
      end
      lcode_tblsize = lcode_tblsize + 1
      lcodes[lcode_tblsize] = code
      lcodes_counts[code] = (lcodes_counts[code] or 0) + 1

      dcodes_tblsize = dcodes_tblsize + 1
      dcodes[dcodes_tblsize] = dist_code
      dcodes_counts[dist_code] = (dcodes_counts[dist_code] or 0) + 1

      if length_extra_bits_bitlen > 0 then
        local lenExtraBits = _length_to_deflate_extra_bits[prev_len]
        lextra_bits_tblsize = lextra_bits_tblsize + 1
        lextra_bits[lextra_bits_tblsize] = lenExtraBits
      end
      if dist_extra_bits_bitlen > 0 then
        dextra_bits_tblsize = dextra_bits_tblsize + 1
        dextra_bits[dextra_bits_tblsize] = dist_extra_bits
      end

      for i = index + 1, index + prev_len - (config_use_lazy and 2 or 1) do
        hash = (hash * 256 + (string_table[i - offset + 2] or 0)) % 16777216
        if prev_len <= config_max_insert_length then
          hash_chain = hash_tables[hash]
          if not hash_chain then
            hash_chain = {}
            hash_tables[hash] = hash_chain
          end
          hash_chain[#hash_chain + 1] = i
        end
      end
      index = index + prev_len - (config_use_lazy and 1 or 0)
      match_available = false
    elseif (not config_use_lazy) or match_available then
      local code = string_table[config_use_lazy and (string_table_index - 1) or
                     string_table_index]
      lcode_tblsize = lcode_tblsize + 1
      lcodes[lcode_tblsize] = code
      lcodes_counts[code] = (lcodes_counts[code] or 0) + 1
      index = index + 1
    else
      match_available = true
      index = index + 1
    end
  end

  -- Write "end of block" symbol
  lcode_tblsize = lcode_tblsize + 1
  lcodes[lcode_tblsize] = 256
  lcodes_counts[256] = (lcodes_counts[256] or 0) + 1

  return lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts
end

-- Get the header data of dynamic block.
-- @param lcodes_count The count of each literal/LZ77_length codes.
-- @param dcodes_count The count of each Lz77 distance codes.
-- @return a lots of stuffs.
-- @see RFC1951 Page 12
local function GetBlockDynamicHuffmanHeader(lcodes_counts, dcodes_counts)
  local lcodes_huffman_bitlens, lcodes_huffman_codes, max_non_zero_bitlen_lcode =
    GetHuffmanBitlenAndCode(lcodes_counts, 15, 285)
  local dcodes_huffman_bitlens, dcodes_huffman_codes, max_non_zero_bitlen_dcode =
    GetHuffmanBitlenAndCode(dcodes_counts, 15, 29)

  local rle_deflate_codes, rle_extra_bits, rle_codes_counts =
    RunLengthEncodeHuffmanBitlen(lcodes_huffman_bitlens,
                                 max_non_zero_bitlen_lcode,
                                 dcodes_huffman_bitlens,
                                 max_non_zero_bitlen_dcode)

  local rle_codes_huffman_bitlens, rle_codes_huffman_codes =
    GetHuffmanBitlenAndCode(rle_codes_counts, 7, 18)

  local HCLEN = 0
  for i = 1, 19 do
    local symbol = _rle_codes_huffman_bitlen_order[i]
    local length = rle_codes_huffman_bitlens[symbol] or 0
    if length ~= 0 then HCLEN = i end
  end

  HCLEN = HCLEN - 4
  local HLIT = max_non_zero_bitlen_lcode + 1 - 257
  local HDIST = max_non_zero_bitlen_dcode + 1 - 1
  if HDIST < 0 then HDIST = 0 end

  return HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens, rle_codes_huffman_codes,
         rle_deflate_codes, rle_extra_bits, lcodes_huffman_bitlens,
         lcodes_huffman_codes, dcodes_huffman_bitlens, dcodes_huffman_codes
end

-- Get the size of dynamic block without writing any bits into the writer.
-- @param ... Read the source code of GetBlockDynamicHuffmanHeader()
-- @return the bit length of the dynamic block
local function GetDynamicHuffmanBlockSize(lcodes, dcodes, HCLEN,
                                          rle_codes_huffman_bitlens,
                                          rle_deflate_codes,
                                          lcodes_huffman_bitlens,
                                          dcodes_huffman_bitlens)

  local block_bitlen = 17 -- 1+2+5+5+4
  block_bitlen = block_bitlen + (HCLEN + 4) * 3

  for i = 1, #rle_deflate_codes do
    local code = rle_deflate_codes[i]
    block_bitlen = block_bitlen + rle_codes_huffman_bitlens[code]
    if code >= 16 then
      block_bitlen = block_bitlen +
                       ((code == 16) and 2 or (code == 17 and 3 or 7))
    end
  end

  local length_code_count = 0
  for i = 1, #lcodes do
    local code = lcodes[i]
    local huffman_bitlen = lcodes_huffman_bitlens[code]
    block_bitlen = block_bitlen + huffman_bitlen
    if code > 256 then -- Length code
      length_code_count = length_code_count + 1
      if code > 264 and code < 285 then -- Length code with extra bits
        local extra_bits_bitlen = _literal_deflate_code_to_extra_bitlen[code -
                                    256]
        block_bitlen = block_bitlen + extra_bits_bitlen
      end
      local dist_code = dcodes[length_code_count]
      local dist_huffman_bitlen = dcodes_huffman_bitlens[dist_code]
      block_bitlen = block_bitlen + dist_huffman_bitlen

      if dist_code > 3 then -- dist code with extra bits
        local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
        block_bitlen = block_bitlen + dist_extra_bits_bitlen
      end
    end
  end
  return block_bitlen
end

-- Write dynamic block.
-- @param ... Read the source code of GetBlockDynamicHuffmanHeader()
local function CompressDynamicHuffmanBlock(WriteBits, is_last_block, lcodes,
                                           lextra_bits, dcodes, dextra_bits,
                                           HLIT, HDIST, HCLEN,
                                           rle_codes_huffman_bitlens,
                                           rle_codes_huffman_codes,
                                           rle_deflate_codes, rle_extra_bits,
                                           lcodes_huffman_bitlens,
                                           lcodes_huffman_codes,
                                           dcodes_huffman_bitlens,
                                           dcodes_huffman_codes)

  WriteBits(is_last_block and 1 or 0, 1) -- Last block identifier
  WriteBits(2, 2) -- Dynamic Huffman block identifier

  WriteBits(HLIT, 5)
  WriteBits(HDIST, 5)
  WriteBits(HCLEN, 4)

  for i = 1, HCLEN + 4 do
    local symbol = _rle_codes_huffman_bitlen_order[i]
    local length = rle_codes_huffman_bitlens[symbol] or 0
    WriteBits(length, 3)
  end

  local rleExtraBitsIndex = 1
  for i = 1, #rle_deflate_codes do
    local code = rle_deflate_codes[i]
    WriteBits(rle_codes_huffman_codes[code], rle_codes_huffman_bitlens[code])
    if code >= 16 then
      local extraBits = rle_extra_bits[rleExtraBitsIndex]
      WriteBits(extraBits, (code == 16) and 2 or (code == 17 and 3 or 7))
      rleExtraBitsIndex = rleExtraBitsIndex + 1
    end
  end

  local length_code_count = 0
  local length_code_with_extra_count = 0
  local dist_code_with_extra_count = 0

  for i = 1, #lcodes do
    local deflate_codee = lcodes[i]
    local huffman_code = lcodes_huffman_codes[deflate_codee]
    local huffman_bitlen = lcodes_huffman_bitlens[deflate_codee]
    WriteBits(huffman_code, huffman_bitlen)
    if deflate_codee > 256 then -- Length code
      length_code_count = length_code_count + 1
      if deflate_codee > 264 and deflate_codee < 285 then
        -- Length code with extra bits
        length_code_with_extra_count = length_code_with_extra_count + 1
        local extra_bits = lextra_bits[length_code_with_extra_count]
        local extra_bits_bitlen =
          _literal_deflate_code_to_extra_bitlen[deflate_codee - 256]
        WriteBits(extra_bits, extra_bits_bitlen)
      end
      -- Write distance code
      local dist_deflate_code = dcodes[length_code_count]
      local dist_huffman_code = dcodes_huffman_codes[dist_deflate_code]
      local dist_huffman_bitlen = dcodes_huffman_bitlens[dist_deflate_code]
      WriteBits(dist_huffman_code, dist_huffman_bitlen)

      if dist_deflate_code > 3 then -- dist code with extra bits
        dist_code_with_extra_count = dist_code_with_extra_count + 1
        local dist_extra_bits = dextra_bits[dist_code_with_extra_count]
        local dist_extra_bits_bitlen = (dist_deflate_code - dist_deflate_code %
                                         2) / 2 - 1
        WriteBits(dist_extra_bits, dist_extra_bits_bitlen)
      end
    end
  end
end

-- Get the size of fixed block without writing any bits into the writer.
-- @param lcodes literal/LZ77_length deflate codes
-- @param decodes LZ77 distance deflate codes
-- @return the bit length of the fixed block
local function GetFixedHuffmanBlockSize(lcodes, dcodes)
  local block_bitlen = 3
  local length_code_count = 0
  for i = 1, #lcodes do
    local code = lcodes[i]
    local huffman_bitlen = _fix_block_literal_huffman_bitlen[code]
    block_bitlen = block_bitlen + huffman_bitlen
    if code > 256 then -- Length code
      length_code_count = length_code_count + 1
      if code > 264 and code < 285 then -- Length code with extra bits
        local extra_bits_bitlen = _literal_deflate_code_to_extra_bitlen[code -
                                    256]
        block_bitlen = block_bitlen + extra_bits_bitlen
      end
      local dist_code = dcodes[length_code_count]
      block_bitlen = block_bitlen + 5

      if dist_code > 3 then -- dist code with extra bits
        local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
        block_bitlen = block_bitlen + dist_extra_bits_bitlen
      end
    end
  end
  return block_bitlen
end

-- Write fixed block.
-- @param lcodes literal/LZ77_length deflate codes
-- @param decodes LZ77 distance deflate codes
local function CompressFixedHuffmanBlock(WriteBits, is_last_block, lcodes,
                                         lextra_bits, dcodes, dextra_bits)
  WriteBits(is_last_block and 1 or 0, 1) -- Last block identifier
  WriteBits(1, 2) -- Fixed Huffman block identifier
  local length_code_count = 0
  local length_code_with_extra_count = 0
  local dist_code_with_extra_count = 0
  for i = 1, #lcodes do
    local deflate_code = lcodes[i]
    local huffman_code = _fix_block_literal_huffman_code[deflate_code]
    local huffman_bitlen = _fix_block_literal_huffman_bitlen[deflate_code]
    WriteBits(huffman_code, huffman_bitlen)
    if deflate_code > 256 then -- Length code
      length_code_count = length_code_count + 1
      if deflate_code > 264 and deflate_code < 285 then
        -- Length code with extra bits
        length_code_with_extra_count = length_code_with_extra_count + 1
        local extra_bits = lextra_bits[length_code_with_extra_count]
        local extra_bits_bitlen =
          _literal_deflate_code_to_extra_bitlen[deflate_code - 256]
        WriteBits(extra_bits, extra_bits_bitlen)
      end
      -- Write distance code
      local dist_code = dcodes[length_code_count]
      local dist_huffman_code = _fix_block_dist_huffman_code[dist_code]
      WriteBits(dist_huffman_code, 5)

      if dist_code > 3 then -- dist code with extra bits
        dist_code_with_extra_count = dist_code_with_extra_count + 1
        local dist_extra_bits = dextra_bits[dist_code_with_extra_count]
        local dist_extra_bits_bitlen = (dist_code - dist_code % 2) / 2 - 1
        WriteBits(dist_extra_bits, dist_extra_bits_bitlen)
      end
    end
  end
end

-- Get the size of store block without writing any bits into the writer.
-- @param block_start The start index of the origin input string
-- @param block_end The end index of the origin input string
-- @param Total bit lens had been written into the compressed result before,
-- because store block needs to shift to byte boundary.
-- @return the bit length of the fixed block
local function GetStoreBlockSize(block_start, block_end, total_bitlen)
  assert(block_end - block_start + 1 <= 65535)
  local block_bitlen = 3
  total_bitlen = total_bitlen + 3
  local padding_bitlen = (8 - total_bitlen % 8) % 8
  block_bitlen = block_bitlen + padding_bitlen
  block_bitlen = block_bitlen + 32
  block_bitlen = block_bitlen + (block_end - block_start + 1) * 8
  return block_bitlen
end

-- Write the store block.
-- @param ... lots of stuffs
-- @return nil
local function CompressStoreBlock(WriteBits, WriteString, is_last_block, str,
                                  block_start, block_end, total_bitlen)
  assert(block_end - block_start + 1 <= 65535)
  WriteBits(is_last_block and 1 or 0, 1) -- Last block identifer.
  WriteBits(0, 2) -- Store block identifier.
  total_bitlen = total_bitlen + 3
  local padding_bitlen = (8 - total_bitlen % 8) % 8
  if padding_bitlen > 0 then
    WriteBits(_pow2[padding_bitlen] - 1, padding_bitlen)
  end
  local size = block_end - block_start + 1
  WriteBits(size, 16)

  -- Write size's one's complement
  local comp = (255 - size % 256) + (255 - (size - size % 256) / 256) * 256
  WriteBits(comp, 16)

  WriteString(str:sub(block_start, block_end))
end

-- Do the deflate
-- Currently using a simple way to determine the block size
-- (This is why the compression ratio is little bit worse than zlib when
-- the input size is very large
-- The first block is 64KB, the following block is 32KB.
-- After each block, there is a memory cleanup operation.
-- This is not a fast operation, but it is needed to save memory usage, so
-- the memory usage does not grow unboundly. If the data size is less than
-- 64KB, then memory cleanup won't happen.
-- This function determines whether to use store/fixed/dynamic blocks by
-- calculating the block size of each block type and chooses the smallest one.
local function Deflate(configs, WriteBits, WriteString, FlushWriter, str,
                       dictionary)
  local string_table = {}
  local hash_tables = {}
  local is_last_block = nil
  local block_start
  local block_end
  local bitlen_written
  local total_bitlen = FlushWriter(_FLUSH_MODE_NO_FLUSH)
  local strlen = #str
  local offset

  local level
  local strategy
  if configs then
    if configs.level then level = configs.level end
    if configs.strategy then strategy = configs.strategy end
  end

  if not level then
    if strlen < 2048 then
      level = 7
    elseif strlen > 65536 then
      level = 3
    else
      level = 5
    end
  end

  while not is_last_block do
    if not block_start then
      block_start = 1
      block_end = 64 * 1024 - 1
      offset = 0
    else
      block_start = block_end + 1
      block_end = block_end + 32 * 1024
      offset = block_start - 32 * 1024 - 1
    end

    if block_end >= strlen then
      block_end = strlen
      is_last_block = true
    else
      is_last_block = false
    end

    local lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts

    local HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens,
          rle_codes_huffman_codes, rle_deflate_codes, rle_extra_bits,
          lcodes_huffman_bitlens, lcodes_huffman_codes, dcodes_huffman_bitlens,
          dcodes_huffman_codes

    local dynamic_block_bitlen
    local fixed_block_bitlen
    local store_block_bitlen

    if level ~= 0 then

      -- GetBlockLZ77 needs block_start to block_end+3 to be loaded.
      LoadStringToTable(str, string_table, block_start, block_end + 3, offset)
      if block_start == 1 and dictionary then
        local dict_string_table = dictionary.string_table
        local dict_strlen = dictionary.strlen
        for i = 0, (-dict_strlen + 1) < -257 and -257 or (-dict_strlen + 1), -1 do
          string_table[i] = dict_string_table[dict_strlen + i]
        end
      end

      if strategy == "huffman_only" then
        lcodes = {}
        LoadStringToTable(str, lcodes, block_start, block_end, block_start - 1)
        lextra_bits = {}
        lcodes_counts = {}
        lcodes[block_end - block_start + 2] = 256 -- end of block
        for i = 1, block_end - block_start + 2 do
          local code = lcodes[i]
          lcodes_counts[code] = (lcodes_counts[code] or 0) + 1
        end
        dcodes = {}
        dextra_bits = {}
        dcodes_counts = {}
      else
        lcodes, lextra_bits, lcodes_counts, dcodes, dextra_bits, dcodes_counts =
          GetBlockLZ77Result(level, string_table, hash_tables, block_start,
                             block_end, offset, dictionary)
      end

      -- LuaFormatter off
      HLIT, HDIST, HCLEN, rle_codes_huffman_bitlens, rle_codes_huffman_codes, rle_deflate_codes,
       rle_extra_bits, lcodes_huffman_bitlens, lcodes_huffman_codes, dcodes_huffman_bitlens, dcodes_huffman_codes =
      -- LuaFormatter on
      GetBlockDynamicHuffmanHeader(lcodes_counts, dcodes_counts)
      dynamic_block_bitlen = GetDynamicHuffmanBlockSize(lcodes, dcodes, HCLEN,
                                                        rle_codes_huffman_bitlens,
                                                        rle_deflate_codes,
                                                        lcodes_huffman_bitlens,
                                                        dcodes_huffman_bitlens)
      fixed_block_bitlen = GetFixedHuffmanBlockSize(lcodes, dcodes)
    end

    store_block_bitlen = GetStoreBlockSize(block_start, block_end, total_bitlen)

    local min_bitlen = store_block_bitlen
    min_bitlen = (fixed_block_bitlen and fixed_block_bitlen < min_bitlen) and
                   fixed_block_bitlen or min_bitlen
    min_bitlen =
      (dynamic_block_bitlen and dynamic_block_bitlen < min_bitlen) and
        dynamic_block_bitlen or min_bitlen

    if level == 0 or
      (strategy ~= "fixed" and strategy ~= "dynamic" and store_block_bitlen ==
        min_bitlen) then
      CompressStoreBlock(WriteBits, WriteString, is_last_block, str,
                         block_start, block_end, total_bitlen)
      total_bitlen = total_bitlen + store_block_bitlen
    elseif strategy ~= "dynamic" and
      (strategy == "fixed" or fixed_block_bitlen == min_bitlen) then
      CompressFixedHuffmanBlock(WriteBits, is_last_block, lcodes, lextra_bits,
                                dcodes, dextra_bits)
      total_bitlen = total_bitlen + fixed_block_bitlen
    elseif strategy == "dynamic" or dynamic_block_bitlen == min_bitlen then
      CompressDynamicHuffmanBlock(WriteBits, is_last_block, lcodes, lextra_bits,
                                  dcodes, dextra_bits, HLIT, HDIST, HCLEN,
                                  rle_codes_huffman_bitlens,
                                  rle_codes_huffman_codes, rle_deflate_codes,
                                  rle_extra_bits, lcodes_huffman_bitlens,
                                  lcodes_huffman_codes, dcodes_huffman_bitlens,
                                  dcodes_huffman_codes)
      total_bitlen = total_bitlen + dynamic_block_bitlen
    end

    if is_last_block then
      bitlen_written = FlushWriter(_FLUSH_MODE_NO_FLUSH)
    else
      bitlen_written = FlushWriter(_FLUSH_MODE_MEMORY_CLEANUP)
    end

    assert(bitlen_written == total_bitlen)

    -- Memory clean up, so memory consumption does not always grow linearly
    -- , even if input string is > 64K.
    -- Not a very efficient operation, but this operation won't happen
    -- when the input data size is less than 64K.
    if not is_last_block then
      local j
      if dictionary and block_start == 1 then
        j = 0
        while (string_table[j]) do
          string_table[j] = nil
          j = j - 1
        end
      end
      dictionary = nil
      j = 1
      for i = block_end - 32767, block_end do
        string_table[j] = string_table[i - offset]
        j = j + 1
      end

      for k, t in pairs(hash_tables) do
        local tSize = #t
        if tSize > 0 and block_end + 1 - t[1] > 32768 then
          if tSize == 1 then
            hash_tables[k] = nil
          else
            local new = {}
            local newSize = 0
            for i = 2, tSize do
              j = t[i]
              if block_end + 1 - j <= 32768 then
                newSize = newSize + 1
                new[newSize] = j
              end
            end
            hash_tables[k] = new
          end
        end
      end
    end
  end
end

--- The description to compression configuration table. <br>
-- Any field can be nil to use its default. <br>
-- Table with keys other than those below is an invalid table.
-- @class table
-- @name compression_configs
-- @field level The compression level ranged from 0 to 9. 0 is no compression.
-- 9 is the slowest but best compression. Use nil for default level.
-- @field strategy The compression strategy. "fixed" to only use fixed deflate
-- compression block. "dynamic" to only use dynamic block. "huffman_only" to
-- do no LZ77 compression. Only do huffman compression.

-- @see LibDeflate:CompressDeflate(str, configs)
-- @see LibDeflate:CompressDeflateWithDict(str, dictionary, configs)
local function CompressDeflateInternal(str, dictionary, configs)
  local WriteBits, WriteString, FlushWriter = CreateWriter()
  Deflate(configs, WriteBits, WriteString, FlushWriter, str, dictionary)
  local total_bitlen, result = FlushWriter(_FLUSH_MODE_OUTPUT)
  local padding_bitlen = (8 - total_bitlen % 8) % 8
  return result, padding_bitlen
end

-- @see LibDeflate:CompressZlib
-- @see LibDeflate:CompressZlibWithDict
local function CompressZlibInternal(str, dictionary, configs)
  local WriteBits, WriteString, FlushWriter = CreateWriter()

  local CM = 8 -- Compression method
  local CINFO = 7 -- Window Size = 32K
  local CMF = CINFO * 16 + CM
  WriteBits(CMF, 8)

  local FDIST = dictionary and 1 or 0
  local FLEVEL = 2 -- Default compression
  local FLG = FLEVEL * 64 + FDIST * 32
  local FCHECK = (31 - (CMF * 256 + FLG) % 31)
  -- The FCHECK value must be such that CMF and FLG,
  -- when viewed as a 16-bit unsigned integer stored
  -- in MSB order (CMF*256 + FLG), is a multiple of 31.
  FLG = FLG + FCHECK
  WriteBits(FLG, 8)

  if FDIST == 1 then
    local adler32 = dictionary.adler32
    local byte0 = adler32 % 256
    adler32 = (adler32 - byte0) / 256
    local byte1 = adler32 % 256
    adler32 = (adler32 - byte1) / 256
    local byte2 = adler32 % 256
    adler32 = (adler32 - byte2) / 256
    local byte3 = adler32 % 256
    WriteBits(byte3, 8)
    WriteBits(byte2, 8)
    WriteBits(byte1, 8)
    WriteBits(byte0, 8)
  end

  Deflate(configs, WriteBits, WriteString, FlushWriter, str, dictionary)
  FlushWriter(_FLUSH_MODE_BYTE_BOUNDARY)

  local adler32 = Adler32(str)

  -- Most significant byte first
  local byte3 = adler32 % 256
  adler32 = (adler32 - byte3) / 256
  local byte2 = adler32 % 256
  adler32 = (adler32 - byte2) / 256
  local byte1 = adler32 % 256
  adler32 = (adler32 - byte1) / 256
  local byte0 = adler32 % 256

  WriteBits(byte0, 8)
  WriteBits(byte1, 8)
  WriteBits(byte2, 8)
  WriteBits(byte3, 8)
  local total_bitlen, result = FlushWriter(_FLUSH_MODE_OUTPUT)
  local padding_bitlen = (8 - total_bitlen % 8) % 8
  return result, padding_bitlen
end

--- Compress using the raw deflate format.
-- @param str [string] The data to be compressed.
-- @param configs [table/nil] The configuration table to control the compression
-- . If nil, use the default configuration.
-- @return [string] The compressed data.
-- @return [integer] The number of bits padded at the end of output.
-- 0 <= bits < 8  <br>
-- This means the most significant "bits" of the last byte of the returned
-- compressed data are padding bits and they don't affect decompression.
-- You don't need to use this value unless you want to do some postprocessing
-- to the compressed data.
-- @see compression_configs
-- @see LibDeflate:DecompressDeflate
local function CompressDeflate(str, configs)
  local arg_valid, arg_err = IsValidArguments(str, false, nil, true, configs)
  if not arg_valid then
    error(("Usage: LibDeflate:CompressDeflate(str, configs): " .. arg_err), 2)
  end
  return CompressDeflateInternal(str, nil, configs)
end

--- Compress using the raw deflate format with a preset dictionary.
-- @param str [string] The data to be compressed.
-- @param dictionary [table] The preset dictionary produced by
-- LibDeflate:CreateDictionary
-- @param configs [table/nil] The configuration table to control the compression
-- . If nil, use the default configuration.
-- @return [string] The compressed data.
-- @return [integer] The number of bits padded at the end of output.
-- 0 <= bits < 8  <br>
-- This means the most significant "bits" of the last byte of the returned
-- compressed data are padding bits and they don't affect decompression.
-- You don't need to use this value unless you want to do some postprocessing
-- to the compressed data.
-- @see compression_configs
-- @see LibDeflate:CreateDictionary
-- @see LibDeflate:DecompressDeflateWithDict
local function CompressDeflateWithDict(str, dictionary, configs)
  local arg_valid, arg_err = IsValidArguments(str, true, dictionary, true,
                                              configs)
  if not arg_valid then
    error(("Usage: LibDeflate:CompressDeflateWithDict" ..
            "(str, dictionary, configs): " .. arg_err), 2)
  end
  return CompressDeflateInternal(str, dictionary, configs)
end

--- Compress using the zlib format.
-- @param str [string] the data to be compressed.
-- @param configs [table/nil] The configuration table to control the compression
-- . If nil, use the default configuration.
-- @return [string] The compressed data.
-- @return [integer] The number of bits padded at the end of output.
-- Should always be 0.
-- Zlib formatted compressed data never has padding bits at the end.
-- @see compression_configs
-- @see LibDeflate:DecompressZlib
local function CompressZlib(str, configs)
  local arg_valid, arg_err = IsValidArguments(str, false, nil, true, configs)
  if not arg_valid then
    error(("Usage: LibDeflate:CompressZlib(str, configs): " .. arg_err), 2)
  end
  return CompressZlibInternal(str, nil, configs)
end

--- Compress using the zlib format with a preset dictionary.
-- @param str [string] the data to be compressed.
-- @param dictionary [table] A preset dictionary produced
-- by LibDeflate:CreateDictionary()
-- @param configs [table/nil] The configuration table to control the compression
-- . If nil, use the default configuration.
-- @return [string] The compressed data.
-- @return [integer] The number of bits padded at the end of output.
-- Should always be 0.
-- Zlib formatted compressed data never has padding bits at the end.
-- @see compression_configs
-- @see LibDeflate:CreateDictionary
-- @see LibDeflate:DecompressZlibWithDict
local function CompressZlibWithDict(str, dictionary, configs)
  local arg_valid, arg_err = IsValidArguments(str, true, dictionary, true,
                                              configs)
  if not arg_valid then
    error(("Usage: LibDeflate:CompressZlibWithDict" ..
            "(str, dictionary, configs): " .. arg_err), 2)
  end
  return CompressZlibInternal(str, dictionary, configs)
end

--[[ --------------------------------------------------------------------------
        Decompress code
--]] --------------------------------------------------------------------------

--[[
        Create a reader to easily reader stuffs as the unit of bits.
        Return values:
        1. ReadBits(bitlen)
        2. ReadBytes(bytelen, buffer, buffer_size)
        3. Decode(huffman_bitlen_count, huffman_symbol, min_bitlen)
        4. ReaderBitlenLeft()
        5. SkipToByteBoundary()
--]]

local function CreateReader(input_string)
  local input = input_string
  local input_strlen = #input_string
  local input_next_byte_pos = 1
  local cache_bitlen = 0
  local cache = 0

  -- Read some bits.
  -- To improve speed, this function does not
  -- check if the input has been exhausted.
  -- Use ReaderBitlenLeft() < 0 to check it.
  -- @param bitlen the number of bits to read
  -- @return the data is read.
  local function ReadBits(bitlen)
    local rshift_mask = _pow2[bitlen]
    local code
    if bitlen <= cache_bitlen then
      code = cache % rshift_mask
      cache = (cache - code) / rshift_mask
      cache_bitlen = cache_bitlen - bitlen
    else -- Whether input has been exhausted is not checked.
      local lshift_mask = _pow2[cache_bitlen]
      local byte1, byte2, byte3, byte4 =
        string_byte(input, input_next_byte_pos, input_next_byte_pos + 3)
      -- This requires lua number to be at least double ()
      cache = cache +
                ((byte1 or 0) + (byte2 or 0) * 256 + (byte3 or 0) * 65536 +
                  (byte4 or 0) * 16777216) * lshift_mask
      input_next_byte_pos = input_next_byte_pos + 4
      cache_bitlen = cache_bitlen + 32 - bitlen
      code = cache % rshift_mask
      cache = (cache - code) / rshift_mask
    end
    return code
  end

  -- Read some bytes from the reader.
  -- Assume reader is on the byte boundary.
  -- @param bytelen The number of bytes to be read.
  -- @param buffer The byte read will be stored into this buffer.
  -- @param buffer_size The buffer will be modified starting from
  --    buffer[buffer_size+1], ending at buffer[buffer_size+bytelen-1]
  -- @return the new buffer_size
  local function ReadBytes(bytelen, buffer, buffer_size)
    assert(cache_bitlen % 8 == 0)

    local byte_from_cache =
      (cache_bitlen / 8 < bytelen) and (cache_bitlen / 8) or bytelen
    for _ = 1, byte_from_cache do
      local byte = cache % 256
      buffer_size = buffer_size + 1
      buffer[buffer_size] = string_char(byte)
      cache = (cache - byte) / 256
    end
    cache_bitlen = cache_bitlen - byte_from_cache * 8
    bytelen = bytelen - byte_from_cache
    if (input_strlen - input_next_byte_pos - bytelen + 1) * 8 + cache_bitlen < 0 then
      return -1 -- out of input
    end
    for i = input_next_byte_pos, input_next_byte_pos + bytelen - 1 do
      buffer_size = buffer_size + 1
      buffer[buffer_size] = string_sub(input, i, i)
    end

    input_next_byte_pos = input_next_byte_pos + bytelen
    return buffer_size
  end

  -- Decode huffman code
  -- To improve speed, this function does not check
  -- if the input has been exhausted.
  -- Use ReaderBitlenLeft() < 0 to check it.
  -- Credits for Mark Adler. This code is from puff:Decode()
  -- @see puff:Decode(...)
  -- @param huffman_bitlen_count
  -- @param huffman_symbol
  -- @param min_bitlen The minimum huffman bit length of all symbols
  -- @return The decoded deflate code.
  --    Negative value is returned if decoding fails.
  local function Decode(huffman_bitlen_counts, huffman_symbols, min_bitlen)
    local code = 0
    local first = 0
    local index = 0
    local count
    if min_bitlen > 0 then
      if cache_bitlen < 15 and input then
        local lshift_mask = _pow2[cache_bitlen]
        local byte1, byte2, byte3, byte4 =
          string_byte(input, input_next_byte_pos, input_next_byte_pos + 3)
        -- This requires lua number to be at least double ()
        cache = cache +
                  ((byte1 or 0) + (byte2 or 0) * 256 + (byte3 or 0) * 65536 +
                    (byte4 or 0) * 16777216) * lshift_mask
        input_next_byte_pos = input_next_byte_pos + 4
        cache_bitlen = cache_bitlen + 32
      end

      local rshift_mask = _pow2[min_bitlen]
      cache_bitlen = cache_bitlen - min_bitlen
      code = cache % rshift_mask
      cache = (cache - code) / rshift_mask
      -- Reverse the bits
      code = _reverse_bits_tbl[min_bitlen][code]

      count = huffman_bitlen_counts[min_bitlen]
      if code < count then return huffman_symbols[code] end
      index = count
      first = count * 2
      code = code * 2
    end

    for bitlen = min_bitlen + 1, 15 do
      local bit
      bit = cache % 2
      cache = (cache - bit) / 2
      cache_bitlen = cache_bitlen - 1

      code = (bit == 1) and (code + 1 - code % 2) or code
      count = huffman_bitlen_counts[bitlen] or 0
      local diff = code - first
      if diff < count then return huffman_symbols[index + diff] end
      index = index + count
      first = first + count
      first = first * 2
      code = code * 2
    end
    -- invalid literal/length or distance code
    -- in fixed or dynamic block (run out of code)
    return -10
  end

  local function ReaderBitlenLeft()
    return (input_strlen - input_next_byte_pos + 1) * 8 + cache_bitlen
  end

  local function SkipToByteBoundary()
    local skipped_bitlen = cache_bitlen % 8
    local rshift_mask = _pow2[skipped_bitlen]
    cache_bitlen = cache_bitlen - skipped_bitlen
    cache = (cache - cache % rshift_mask) / rshift_mask
  end

  return ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary
end

-- Create a deflate state, so I can pass in less arguments to functions.
-- @param str the whole string to be decompressed.
-- @param dictionary The preset dictionary. nil if not provided.
--              This dictionary should be produced by LibDeflate:CreateDictionary(str)
-- @return The decomrpess state.
local function CreateDecompressState(str, dictionary)
  local ReadBits, ReadBytes, Decode, ReaderBitlenLeft, SkipToByteBoundary =
    CreateReader(str)
  local state = {
    ReadBits = ReadBits,
    ReadBytes = ReadBytes,
    Decode = Decode,
    ReaderBitlenLeft = ReaderBitlenLeft,
    SkipToByteBoundary = SkipToByteBoundary,
    buffer_size = 0,
    buffer = {},
    result_buffer = {},
    dictionary = dictionary
  }
  return state
end

-- Get the stuffs needed to decode huffman codes
-- @see puff.c:construct(...)
-- @param huffman_bitlen The huffman bit length of the huffman codes.
-- @param max_symbol The maximum symbol
-- @param max_bitlen The min huffman bit length of all codes
-- @return zero or positive for success, negative for failure.
-- @return The count of each huffman bit length.
-- @return A table to convert huffman codes to deflate codes.
-- @return The minimum huffman bit length.

local function GetHuffmanForDecode(huffman_bitlens, max_symbol, max_bitlen)
  local huffman_bitlen_counts = {}
  local min_bitlen = max_bitlen
  for symbol = 0, max_symbol do
    local bitlen = huffman_bitlens[symbol] or 0
    min_bitlen = (bitlen > 0 and bitlen < min_bitlen) and bitlen or min_bitlen
    huffman_bitlen_counts[bitlen] = (huffman_bitlen_counts[bitlen] or 0) + 1
  end

  if huffman_bitlen_counts[0] == max_symbol + 1 then -- No Codes
    return 0, huffman_bitlen_counts, {}, 0 -- Complete, but decode will fail
  end

  local left = 1
  for len = 1, max_bitlen do
    left = left * 2
    left = left - (huffman_bitlen_counts[len] or 0)
    if left < 0 then
      return left -- Over-subscribed, return negative
    end
  end

  -- Generate offsets info symbol table for each length for sorting
  local offsets = {}
  offsets[1] = 0
  for len = 1, max_bitlen - 1 do
    offsets[len + 1] = offsets[len] + (huffman_bitlen_counts[len] or 0)
  end

  local huffman_symbols = {}
  for symbol = 0, max_symbol do
    local bitlen = huffman_bitlens[symbol] or 0
    if bitlen ~= 0 then
      local offset = offsets[bitlen]
      huffman_symbols[offset] = symbol
      offsets[bitlen] = offsets[bitlen] + 1
    end
  end

  -- Return zero for complete set, positive for incomplete set.
  return left, huffman_bitlen_counts, huffman_symbols, min_bitlen
end

-- Decode a fixed or dynamic huffman blocks, excluding last block identifier
-- and block type identifer.
-- @see puff.c:codes()
-- @param state decompression state that will be modified by this function.
--      @see CreateDecompressState
-- @param ... Read the source code
-- @return 0 on success, other value on failure.
local function DecodeUntilEndOfBlock(state, lcodes_huffman_bitlens,
                                     lcodes_huffman_symbols,
                                     lcodes_huffman_min_bitlen,
                                     dcodes_huffman_bitlens,
                                     dcodes_huffman_symbols,
                                     dcodes_huffman_min_bitlen)
  local buffer, buffer_size, ReadBits, Decode, ReaderBitlenLeft, result_buffer =
    state.buffer, state.buffer_size, state.ReadBits, state.Decode,
    state.ReaderBitlenLeft, state.result_buffer
  local dictionary = state.dictionary
  local dict_string_table
  local dict_strlen

  local buffer_end = 1
  if dictionary and not buffer[0] then
    -- If there is a dictionary, copy the last 258 bytes into
    -- the string_table to make the copy in the main loop quicker.
    -- This is done only once per decompression.
    dict_string_table = dictionary.string_table
    dict_strlen = dictionary.strlen
    buffer_end = -dict_strlen + 1
    for i = 0, (-dict_strlen + 1) < -257 and -257 or (-dict_strlen + 1), -1 do
      buffer[i] = _byte_to_char[dict_string_table[dict_strlen + i]]
    end
  end

  repeat
    local symbol = Decode(lcodes_huffman_bitlens, lcodes_huffman_symbols,
                          lcodes_huffman_min_bitlen)
    if symbol < 0 or symbol > 285 then
      -- invalid literal/length or distance code in fixed or dynamic block
      return -10
    elseif symbol < 256 then -- Literal
      buffer_size = buffer_size + 1
      buffer[buffer_size] = _byte_to_char[symbol]
    elseif symbol > 256 then -- Length code
      symbol = symbol - 256
      local bitlen = _literal_deflate_code_to_base_len[symbol]
      bitlen = (symbol >= 8) and
                 (bitlen +
                   ReadBits(_literal_deflate_code_to_extra_bitlen[symbol])) or
                 bitlen
      symbol = Decode(dcodes_huffman_bitlens, dcodes_huffman_symbols,
                      dcodes_huffman_min_bitlen)
      if symbol < 0 or symbol > 29 then
        -- invalid literal/length or distance code in fixed or dynamic block
        return -10
      end
      local dist = _dist_deflate_code_to_base_dist[symbol]
      dist = (dist > 4) and
               (dist + ReadBits(_dist_deflate_code_to_extra_bitlen[symbol])) or
               dist

      local char_buffer_index = buffer_size - dist + 1
      if char_buffer_index < buffer_end then
        -- distance is too far back in fixed or dynamic block
        return -11
      end
      if char_buffer_index >= -257 then
        for _ = 1, bitlen do
          buffer_size = buffer_size + 1
          buffer[buffer_size] = buffer[char_buffer_index]
          char_buffer_index = char_buffer_index + 1
        end
      else
        char_buffer_index = dict_strlen + char_buffer_index
        for _ = 1, bitlen do
          buffer_size = buffer_size + 1
          buffer[buffer_size] =
            _byte_to_char[dict_string_table[char_buffer_index]]
          char_buffer_index = char_buffer_index + 1
        end
      end
    end

    if ReaderBitlenLeft() < 0 then
      return 2 -- available inflate data did not terminate
    end

    if buffer_size >= 65536 then
      -- result_buffer[#result_buffer + 1] = table_concat(buffer, "", 1, 32768)
      
      local next_result_buffer = ''
      for i,v in ipairs(buffer) do
        if i > 32768 then break end
        next_result_buffer  = next_result_buffer..v
      end
      result_buffer[#result_buffer + 1] = next_result_buffer
      
      for i = 32769, buffer_size do buffer[i - 32768] = buffer[i] end
      buffer_size = buffer_size - 32768
      buffer[buffer_size + 1] = nil
      -- NOTE: buffer[32769..end] and buffer[-257..0] are not cleared.
      -- This is why "buffer_size" variable is needed.
    end
  until symbol == 256

  state.buffer_size = buffer_size

  return 0
end

-- Decompress a store block
-- @param state decompression state that will be modified by this function.
-- @return 0 if succeeds, other value if fails.
local function DecompressStoreBlock(state)
  local buffer, buffer_size, ReadBits, ReadBytes, ReaderBitlenLeft,
        SkipToByteBoundary, result_buffer = state.buffer, state.buffer_size,
                                            state.ReadBits, state.ReadBytes,
                                            state.ReaderBitlenLeft,
                                            state.SkipToByteBoundary,
                                            state.result_buffer

  SkipToByteBoundary()
  local bytelen = ReadBits(16)
  if ReaderBitlenLeft() < 0 then
    return 2 -- available inflate data did not terminate
  end
  local bytelenComp = ReadBits(16)
  if ReaderBitlenLeft() < 0 then
    return 2 -- available inflate data did not terminate
  end

  if bytelen % 256 + bytelenComp % 256 ~= 255 then
    return -2 -- Not one's complement
  end
  if (bytelen - bytelen % 256) / 256 + (bytelenComp - bytelenComp % 256) / 256 ~=
    255 then
    return -2 -- Not one's complement
  end

  -- Note that ReadBytes will skip to the next byte boundary first.
  buffer_size = ReadBytes(bytelen, buffer, buffer_size)
  if buffer_size < 0 then
    return 2 -- available inflate data did not terminate
  end

  -- memory clean up when there are enough bytes in the buffer.
  if buffer_size >= 65536 then
    result_buffer[#result_buffer + 1] = table_concat(buffer, "", 1, 32768)
    for i = 32769, buffer_size do buffer[i - 32768] = buffer[i] end
    buffer_size = buffer_size - 32768
    buffer[buffer_size + 1] = nil
  end
  state.buffer_size = buffer_size
  return 0
end

-- Decompress a fixed block
-- @param state decompression state that will be modified by this function.
-- @return 0 if succeeds other value if fails.
local function DecompressFixBlock(state)
  return DecodeUntilEndOfBlock(state, _fix_block_literal_huffman_bitlen_count,
                               _fix_block_literal_huffman_to_deflate_code, 7,
                               _fix_block_dist_huffman_bitlen_count,
                               _fix_block_dist_huffman_to_deflate_code, 5)
end

-- Decompress a dynamic block
-- @param state decompression state that will be modified by this function.
-- @return 0 if success, other value if fails.
local function DecompressDynamicBlock(state)
  local ReadBits, Decode = state.ReadBits, state.Decode
  local nlen = ReadBits(5) + 257
  local ndist = ReadBits(5) + 1
  local ncode = ReadBits(4) + 4
  if nlen > 286 or ndist > 30 then
    -- dynamic block code description: too many length or distance codes
    return -3
  end

  local rle_codes_huffman_bitlens = {}

  for i = 1, ncode do
    rle_codes_huffman_bitlens[_rle_codes_huffman_bitlen_order[i]] = ReadBits(3)
  end

  local rle_codes_err, rle_codes_huffman_bitlen_counts,
        rle_codes_huffman_symbols, rle_codes_huffman_min_bitlen =
    GetHuffmanForDecode(rle_codes_huffman_bitlens, 18, 7)
  if rle_codes_err ~= 0 then -- Require complete code set here
    -- dynamic block code description: code lengths codes incomplete
    return -4
  end

  local lcodes_huffman_bitlens = {}
  local dcodes_huffman_bitlens = {}
  -- Read length/literal and distance code length tables
  local index = 0
  while index < nlen + ndist do
    local symbol -- Decoded value
    local bitlen -- Last length to repeat

    symbol = Decode(rle_codes_huffman_bitlen_counts, rle_codes_huffman_symbols,
                    rle_codes_huffman_min_bitlen)

    if symbol < 0 then
      return symbol -- Invalid symbol
    elseif symbol < 16 then
      if index < nlen then
        lcodes_huffman_bitlens[index] = symbol
      else
        dcodes_huffman_bitlens[index - nlen] = symbol
      end
      index = index + 1
    else
      bitlen = 0
      if symbol == 16 then
        if index == 0 then
          -- dynamic block code description: repeat lengths
          -- with no first length
          return -5
        end
        if index - 1 < nlen then
          bitlen = lcodes_huffman_bitlens[index - 1]
        else
          bitlen = dcodes_huffman_bitlens[index - nlen - 1]
        end
        symbol = 3 + ReadBits(2)
      elseif symbol == 17 then -- Repeat zero 3..10 times
        symbol = 3 + ReadBits(3)
      else -- == 18, repeat zero 11.138 times
        symbol = 11 + ReadBits(7)
      end
      if index + symbol > nlen + ndist then
        -- dynamic block code description:
        -- repeat more than specified lengths
        return -6
      end
      while symbol > 0 do -- Repeat last or zero symbol times
        symbol = symbol - 1
        if index < nlen then
          lcodes_huffman_bitlens[index] = bitlen
        else
          dcodes_huffman_bitlens[index - nlen] = bitlen
        end
        index = index + 1
      end
    end
  end

  if (lcodes_huffman_bitlens[256] or 0) == 0 then
    -- dynamic block code description: missing end-of-block code
    return -9
  end
  local lcodes_err, lcodes_huffman_bitlen_counts, lcodes_huffman_symbols,
        lcodes_huffman_min_bitlen = GetHuffmanForDecode(lcodes_huffman_bitlens,
                                                        nlen - 1, 15)
  -- dynamic block code description: invalid literal/length code lengths,
  -- Incomplete code ok only for single length 1 code
  if (lcodes_err ~= 0 and
    (lcodes_err < 0 or nlen ~= (lcodes_huffman_bitlen_counts[0] or 0) +
      (lcodes_huffman_bitlen_counts[1] or 0))) then return -7 end

  local dcodes_err, dcodes_huffman_bitlen_counts, dcodes_huffman_symbols,
        dcodes_huffman_min_bitlen = GetHuffmanForDecode(dcodes_huffman_bitlens,
                                                        ndist - 1, 15)
  -- dynamic block code description: invalid distance code lengths,
  -- Incomplete code ok only for single length 1 code
  if (dcodes_err ~= 0 and
    (dcodes_err < 0 or ndist ~= (dcodes_huffman_bitlen_counts[0] or 0) +
      (dcodes_huffman_bitlen_counts[1] or 0))) then return -8 end

  -- Build buffman table for literal/length codes
  return DecodeUntilEndOfBlock(state, lcodes_huffman_bitlen_counts,
                               lcodes_huffman_symbols,
                               lcodes_huffman_min_bitlen,
                               dcodes_huffman_bitlen_counts,
                               dcodes_huffman_symbols, dcodes_huffman_min_bitlen)
end

-- Decompress a deflate stream
-- @param state: a decompression state
-- @return the decompressed string if succeeds. nil if fails.
local function Inflate(state)
  local ReadBits = state.ReadBits

  local is_last_block
  while not is_last_block do
    is_last_block = (ReadBits(1) == 1)
    local block_type = ReadBits(2)
    local status
    if block_type == 0 then
      status = DecompressStoreBlock(state)
    elseif block_type == 1 then
      status = DecompressFixBlock(state)
    elseif block_type == 2 then
      status = DecompressDynamicBlock(state)
    else
      return nil, -1 -- invalid block type (type == 3)
    end
    if status ~= 0 then return nil, status end
  end

  -- state.result_buffer[#state.result_buffer + 1] =
  --  table_concat(state.buffer, "", 1, state.buffer_size)
  
  local next_state_result_buffer = ''
  for i,v in ipairs(state.buffer) do
    if i > state.buffer_size then break end
    next_state_result_buffer = next_state_result_buffer..v
  end
  state.result_buffer[#state.result_buffer + 1] = next_state_result_buffer
  
  local result = ''
  for i,v in ipairs(state.result_buffer) do
    result  = result..v
  end
  
  return result
end

-- @see LibDeflate:DecompressDeflate(str)
-- @see LibDeflate:DecompressDeflateWithDict(str, dictionary)
local function DecompressDeflateInternal(str, dictionary)
  local state = CreateDecompressState(str, dictionary)
  local result, status = Inflate(state)
  if not result then return nil, status end

  local bitlen_left = state.ReaderBitlenLeft()
  local bytelen_left = (bitlen_left - bitlen_left % 8) / 8
  return result, bytelen_left
end

-- @see LibDeflate:DecompressZlib(str)
-- @see LibDeflate:DecompressZlibWithDict(str)
local function DecompressZlibInternal(str, dictionary)
  local state = CreateDecompressState(str, dictionary)
  local ReadBits = state.ReadBits

  local CMF = ReadBits(8)
  if state.ReaderBitlenLeft() < 0 then
    return nil, 2 -- available inflate data did not terminate
  end
  local CM = CMF % 16
  local CINFO = (CMF - CM) / 16
  if CM ~= 8 then
    return nil, -12 -- invalid compression method
  end
  if CINFO > 7 then
    return nil, -13 -- invalid window size
  end

  local FLG = ReadBits(8)
  if state.ReaderBitlenLeft() < 0 then
    return nil, 2 -- available inflate data did not terminate
  end
  if (CMF * 256 + FLG) % 31 ~= 0 then
    return nil, -14 -- invalid header checksum
  end

  local FDIST = ((FLG - FLG % 32) / 32 % 2)
  local FLEVEL = ((FLG - FLG % 64) / 64 % 4) -- luacheck: ignore FLEVEL

  if FDIST == 1 then
    if not dictionary then
      return nil, -16 -- need dictonary, but dictionary is not provided.
    end
    local byte3 = ReadBits(8)
    local byte2 = ReadBits(8)
    local byte1 = ReadBits(8)
    local byte0 = ReadBits(8)
    local actual_adler32 = byte3 * 16777216 + byte2 * 65536 + byte1 * 256 +
                             byte0
    if state.ReaderBitlenLeft() < 0 then
      return nil, 2 -- available inflate data did not terminate
    end

    if not IsEqualAdler32(actual_adler32, dictionary.adler32) then
      return nil, -17 -- dictionary adler32 does not match
    end
  end
  local result, status = Inflate(state)
  if not result then return nil, status end
  state.SkipToByteBoundary()

  local adler_byte0 = ReadBits(8)
  local adler_byte1 = ReadBits(8)
  local adler_byte2 = ReadBits(8)
  local adler_byte3 = ReadBits(8)
  if state.ReaderBitlenLeft() < 0 then
    return nil, 2 -- available inflate data did not terminate
  end

  local adler32_expected = adler_byte0 * 16777216 + adler_byte1 * 65536 +
                             adler_byte2 * 256 + adler_byte3
  local adler32_actual = Adler32(result)
  if not IsEqualAdler32(adler32_expected, adler32_actual) then
    return nil, -15 -- Adler32 checksum does not match
  end

  local bitlen_left = state.ReaderBitlenLeft()
  local bytelen_left = (bitlen_left - bitlen_left % 8) / 8
  return result, bytelen_left
end

--- Decompress a raw deflate compressed data.
-- @param str [string] The data to be decompressed.
-- @return [string/nil] If the decompression succeeds, return the decompressed
-- data. If the decompression fails, return nil. You should check if this return
-- value is non-nil to know if the decompression succeeds.
-- @return [integer] If the decompression succeeds, return the number of
-- unprocessed bytes in the input compressed data. This return value is a
-- positive integer if the input data is a valid compressed data appended by an
-- arbitary non-empty string. This return value is 0 if the input data does not
-- contain any extra bytes.<br>
-- If the decompression fails (The first return value of this function is nil),
-- this return value is undefined.
-- @see LibDeflate:CompressDeflate
local function DecompressDeflate(str)
  local arg_valid, arg_err = IsValidArguments(str)
  if not arg_valid then
    error(("Usage: LibDeflate:DecompressDeflate(str): " .. arg_err), 2)
  end
  return DecompressDeflateInternal(str)
end

--- Decompress a zlib compressed data.
-- @param str [string] The data to be decompressed
-- @return [string/nil] If the decompression succeeds, return the decompressed
-- data. If the decompression fails, return nil. You should check if this return
-- value is non-nil to know if the decompression succeeds.
-- @return [integer] If the decompression succeeds, return the number of
-- unprocessed bytes in the input compressed data. This return value is a
-- positive integer if the input data is a valid compressed data appended by an
-- arbitary non-empty string. This return value is 0 if the input data does not
-- contain any extra bytes.<br>
-- If the decompression fails (The first return value of this function is nil),
-- this return value is undefined.
-- @see LibDeflate:CompressZlib
local function DecompressZlib(str)
  local arg_valid, arg_err = IsValidArguments(str)
  if not arg_valid then
    error(("Usage: LibDeflate:DecompressZlib(str): " .. arg_err), 2)
  end
  return DecompressZlibInternal(str)
end

--- Decompress a zlib compressed data with a preset dictionary.
-- @param str [string] The data to be decompressed
-- @param dictionary [table] The preset dictionary used by
-- LibDeflate:CompressDeflateWithDict when the compressed data is produced.
-- Decompression and compression must use the same dictionary.
-- Otherwise wrong decompressed data could be produced without generating any
-- error.
-- @return [string/nil] If the decompression succeeds, return the decompressed
-- data. If the decompression fails, return nil. You should check if this return
-- value is non-nil to know if the decompression succeeds.
-- @return [integer] If the decompression succeeds, return the number of
-- unprocessed bytes in the input compressed data. This return value is a
-- positive integer if the input data is a valid compressed data appended by an
-- arbitary non-empty string. This return value is 0 if the input data does not
-- contain any extra bytes.<br>
-- If the decompression fails (The first return value of this function is nil),
-- this return value is undefined.
-- @see LibDeflate:CompressZlibWithDict
local function DecompressZlibWithDict(str, dictionary)
  local arg_valid, arg_err = IsValidArguments(str, true, dictionary)
  if not arg_valid then
    error(("Usage: LibDeflate:DecompressZlibWithDict(str, dictionary): " ..
            arg_err), 2)
  end
  return DecompressZlibInternal(str, dictionary)
end

-- Calculate the huffman code of fixed block
do
  _fix_block_literal_huffman_bitlen = {}
  for sym = 0, 143 do _fix_block_literal_huffman_bitlen[sym] = 8 end
  for sym = 144, 255 do _fix_block_literal_huffman_bitlen[sym] = 9 end
  for sym = 256, 279 do _fix_block_literal_huffman_bitlen[sym] = 7 end
  for sym = 280, 287 do _fix_block_literal_huffman_bitlen[sym] = 8 end

  _fix_block_dist_huffman_bitlen = {}
  for dist = 0, 31 do _fix_block_dist_huffman_bitlen[dist] = 5 end
  local status
  status, _fix_block_literal_huffman_bitlen_count, _fix_block_literal_huffman_to_deflate_code =
    GetHuffmanForDecode(_fix_block_literal_huffman_bitlen, 287, 9)
  assert(status == 0)
  status, _fix_block_dist_huffman_bitlen_count, _fix_block_dist_huffman_to_deflate_code =
    GetHuffmanForDecode(_fix_block_dist_huffman_bitlen, 31, 5)
  assert(status == 0)

  _fix_block_literal_huffman_code = GetHuffmanCodeFromBitlen(
                                      _fix_block_literal_huffman_bitlen_count,
                                      _fix_block_literal_huffman_bitlen, 287, 9)
  _fix_block_dist_huffman_code = GetHuffmanCodeFromBitlen(
                                   _fix_block_dist_huffman_bitlen_count,
                                   _fix_block_dist_huffman_bitlen, 31, 5)
end

-- Prefix encoding algorithm
-- Credits to LibCompress.
-- The code has been rewritten by the author of LibDeflate.
------------------------------------------------------------------------------

-- to be able to match any requested byte value, the search
-- string must be preprocessed characters to escape with %:
-- ( ) . % + - * ? [ ] ^ $
-- "illegal" byte values:
-- 0 is replaces %z
local _gsub_escape_table = {
  ["\000"] = "%z",
  ["("] = "%(",
  [")"] = "%)",
  ["."] = "%.",
  ["%"] = "%%",
  ["+"] = "%+",
  ["-"] = "%-",
  ["*"] = "%*",
  ["?"] = "%?",
  ["["] = "%[",
  ["]"] = "%]",
  ["^"] = "%^",
  ["$"] = "%$"
}

local function escape_for_gsub(str)
  return str:gsub("([%z%(%)%.%%%+%-%*%?%[%]%^%$])", _gsub_escape_table)
end

--- Create a custom codec with encoder and decoder. <br>
-- This codec is used to convert an input string to make it not contain
-- some specific bytes.
-- This created codec and the parameters of this function do NOT take
-- localization into account. One byte (0-255) in the string is exactly one
-- character (0-255).
-- Credits to LibCompress.
-- The code has been rewritten by the author of LibDeflate. <br>
-- @param reserved_chars [string] The created encoder will ensure encoded
-- data does not contain any single character in reserved_chars. This parameter
-- should be non-empty.
-- @param escape_chars [string] The escape character(s) used in the created
-- codec. The codec converts any character included in reserved\_chars /
-- escape\_chars / map\_chars to (one escape char + one character not in
-- reserved\_chars / escape\_chars / map\_chars).
-- You usually only need to provide a length-1 string for this parameter.
-- Length-2 string is only needed when
-- reserved\_chars + escape\_chars + map\_chars is longer than 127.
-- This parameter should be non-empty.
-- @param map_chars [string] The created encoder will map every
-- reserved\_chars:sub(i, i) (1 <= i <= #map\_chars) to map\_chars:sub(i, i).
-- This parameter CAN be empty string.
-- @return [table/nil] If the codec cannot be created, return nil.<br>
-- If the codec can be created according to the given
-- parameters, return the codec, which is a encode/decode table.
-- The table contains two functions: <br>
-- t:Encode(str) returns the encoded string. <br>
-- t:Decode(str) returns the decoded string if succeeds. nil if fails.
-- @return [nil/string] If the codec is successfully created, return nil.
-- If not, return a string that describes the reason why the codec cannot be
-- created.
-- @usage
-- -- Create an encoder/decoder that maps all "\000" to "\003",
-- -- and escape "\001" (and "\002" and "\003") properly
-- local codec = LibDeflate:CreateCodec("\000\001", "\002", "\003")
--
-- local encoded = codec:Encode(SOME_STRING)
-- -- "encoded" does not contain "\000" or "\001"
-- local decoded = codec:Decode(encoded)
-- -- assert(decoded == SOME_STRING)
local function CreateCodec(reserved_chars, escape_chars, map_chars)
  if type(reserved_chars) ~= "string" or type(escape_chars) ~= "string" or
    type(map_chars) ~= "string" then
    error("Usage: LibDeflate:CreateCodec(reserved_chars," ..
            " escape_chars, map_chars):" .. " All arguments must be string.", 2)
  end

  if escape_chars == "" then return nil, "No escape characters supplied." end
  if #reserved_chars < #map_chars then
    return nil, "The number of reserved characters must be" ..
             " at least as many as the number of mapped chars."
  end
  if reserved_chars == "" then return nil, "No characters to encode." end

  local encode_bytes = reserved_chars .. escape_chars .. map_chars
  -- build list of bytes not available as a suffix to a prefix byte
  local taken = {}
  for i = 1, #encode_bytes do
    local byte = string_byte(encode_bytes, i, i)
    if taken[byte] then
      return nil, "There must be no duplicate characters in the" ..
               " concatenation of reserved_chars, escape_chars and" ..
               " map_chars."
    end
    taken[byte] = true
  end

  local decode_patterns = {}
  local decode_repls = {}

  -- the encoding can be a single gsub
  -- , but the decoding can require multiple gsubs
  local encode_search = {}
  local encode_translate = {}

  -- map single byte to single byte
  if #map_chars > 0 then
    local decode_search = {}
    local decode_translate = {}
    for i = 1, #map_chars do
      local from = string_sub(reserved_chars, i, i)
      local to = string_sub(map_chars, i, i)
      encode_translate[from] = to
      encode_search[#encode_search + 1] = from
      decode_translate[to] = from
      decode_search[#decode_search + 1] = to
    end
    decode_patterns[#decode_patterns + 1] =
      "([" .. escape_for_gsub(table_concat(decode_search)) .. "])"
    decode_repls[#decode_repls + 1] = decode_translate
  end

  local escape_char_index = 1
  local escape_char = string_sub(escape_chars, escape_char_index,
                                 escape_char_index)
  -- map single byte to double-byte
  local r = 0 -- suffix char value to the escapeChar

  local decode_search = {}
  local decode_translate = {}
  for i = 1, #encode_bytes do
    local c = string_sub(encode_bytes, i, i)
    if not encode_translate[c] then
      while r >= 256 or taken[r] do
        r = r + 1
        if r > 255 then -- switch to next escapeChar
          decode_patterns[#decode_patterns + 1] =
            escape_for_gsub(escape_char) .. "([" ..
              escape_for_gsub(table_concat(decode_search)) .. "])"
          decode_repls[#decode_repls + 1] = decode_translate

          escape_char_index = escape_char_index + 1
          escape_char = string_sub(escape_chars, escape_char_index,
                                   escape_char_index)
          r = 0
          decode_search = {}
          decode_translate = {}

          if not escape_char or escape_char == "" then
            -- actually I don't need to check
            -- "not ecape_char", but what if Lua changes
            -- the behavior of string.sub() in the future?
            -- we are out of escape chars and we need more!
            return nil, "Out of escape characters."
          end
        end
      end

      local char_r = _byte_to_char[r]
      encode_translate[c] = escape_char .. char_r
      encode_search[#encode_search + 1] = c
      decode_translate[char_r] = c
      decode_search[#decode_search + 1] = char_r
      r = r + 1
    end
    if i == #encode_bytes then
      decode_patterns[#decode_patterns + 1] =
        escape_for_gsub(escape_char) .. "([" ..
          escape_for_gsub(table_concat(decode_search)) .. "])"
      decode_repls[#decode_repls + 1] = decode_translate
    end
  end

  local codec = {}

  local encode_pattern = "([" .. escape_for_gsub(table_concat(encode_search)) ..
                           "])"
  local encode_repl = encode_translate

  function codec:Encode(str)
    if type(str) ~= "string" then
      error(
        ("Usage: codec:Encode(str):" .. " 'str' - string expected got '%s'."):format(
          type(str)), 2)
    end
    return string_gsub(str, encode_pattern, encode_repl)
  end

  local decode_tblsize = #decode_patterns
  local decode_fail_pattern = "([" .. escape_for_gsub(reserved_chars) .. "])"

  function codec:Decode(str)
    if type(str) ~= "string" then
      error(
        ("Usage: codec:Decode(str):" .. " 'str' - string expected got '%s'."):format(
          type(str)), 2)
    end
    if string_find(str, decode_fail_pattern) then return nil end
    for i = 1, decode_tblsize do
      str = string_gsub(str, decode_patterns[i], decode_repls[i])
    end
    return str
  end

  return codec
end

local _addon_channel_codec

local function GenerateWoWAddonChannelCodec()
  return CreateCodec("\000", "\001", "")
end

--- Encode the string to make it ready to be transmitted in World of
-- Warcraft addon channel. <br>
-- The encoded string is guaranteed to contain no NULL ("\000") character.
-- @param str [string] The string to be encoded.
-- @return The encoded string.
-- @see LibDeflate:DecodeForWoWAddonChannel
local function EncodeForWoWAddonChannel(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:EncodeForWoWAddonChannel(str):" .. " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  if not _addon_channel_codec then
    _addon_channel_codec = GenerateWoWAddonChannelCodec()
  end
  return _addon_channel_codec:Encode(str)
end

--- Decode the string produced by LibDeflate:EncodeForWoWAddonChannel
-- @param str [string] The string to be decoded.
-- @return [string/nil] The decoded string if succeeds. nil if fails.
-- @see LibDeflate:EncodeForWoWAddonChannel
local function DecodeForWoWAddonChannel(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:DecodeForWoWAddonChannel(str):" .. " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  if not _addon_channel_codec then
    _addon_channel_codec = GenerateWoWAddonChannelCodec()
  end
  return _addon_channel_codec:Decode(str)
end

-- For World of Warcraft Chat Channel Encoding
-- Credits to LibCompress.
-- The code has been rewritten by the author of LibDeflate. <br>
-- Following byte values are not allowed:
-- \000, s, S, \010, \013, \124, %
-- Because SendChatMessage will error
-- if an UTF8 multibyte character is incomplete,
-- all character values above 127 have to be encoded to avoid this.
-- This costs quite a bit of bandwidth (about 13-14%)
-- Also, because drunken status is unknown for the received
-- , strings used with SendChatMessage should be terminated with
-- an identifying byte value, after which the server MAY add "...hic!"
-- or as much as it can fit(!).
-- Pass the identifying byte as a reserved character to this function
-- to ensure the encoding doesn't contain that value.
-- or use this: local message, match = arg1:gsub("^(.*)\029.-$", "%1")
-- arg1 is message from channel, \029 is the string terminator
-- , but may be used in the encoded datastream as well. :-)
-- This encoding will expand data anywhere from:
-- 0% (average with pure ascii text)
-- 53.5% (average with random data valued zero to 255)
-- 100% (only encoding data that encodes to two bytes)
local function GenerateWoWChatChannelCodec()
  local r = {}
  for i = 128, 255 do r[#r + 1] = _byte_to_char[i] end

  local reserved_chars = "sS\000\010\013\124%" .. table_concat(r)
  return CreateCodec(reserved_chars, "\029\031", "\015\020")
end

local _chat_channel_codec

--- Encode the string to make it ready to be transmitted in World of
-- Warcraft chat channel. <br>
-- See also https://wow.gamepedia.com/ValidChatMessageCharacters
-- @param str [string] The string to be encoded.
-- @return [string] The encoded string.
-- @see LibDeflate:DecodeForWoWChatChannel
local function EncodeForWoWChatChannel(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:EncodeForWoWChatChannel(str):" .. " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  if not _chat_channel_codec then
    _chat_channel_codec = GenerateWoWChatChannelCodec()
  end
  return _chat_channel_codec:Encode(str)
end

--- Decode the string produced by LibDeflate:EncodeForWoWChatChannel.
-- @param str [string] The string to be decoded.
-- @return [string/nil] The decoded string if succeeds. nil if fails.
-- @see LibDeflate:EncodeForWoWChatChannel
local function DecodeForWoWChatChannel(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:DecodeForWoWChatChannel(str):" .. " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  if not _chat_channel_codec then
    _chat_channel_codec = GenerateWoWChatChannelCodec()
  end
  return _chat_channel_codec:Decode(str)
end

-- Credits to WeakAuras2 and Galmok for the 6 bit encoding algorithm.
-- The code has been rewritten by the author of LibDeflate.
-- The result of encoding will be 25% larger than the
-- origin string, but every single byte of the encoding result will be
-- printable characters as the following.
local _byte_to_6bit_char = {
  [0] = "a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z","A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z","0","1","2","3","4","5","6","7","8","9","(",")"
}

local _6bit_to_byte = {
  [97] = 0, [98] = 1, [99] = 2, [100] = 3, [101] = 4, [102] = 5, [103] = 6, [104] = 7, [105] = 8, [106] = 9, [107] = 10, [108] = 11, [109] = 12, [110] = 13, [111] = 14, [112] = 15,
 [113] = 16, [114] = 17, [115] = 18, [116] = 19, [117] = 20, [118] = 21, [119] = 22, [120] = 23, [121] = 24, [122] = 25, [65] = 26, [66] = 27, [67] = 28, [68] = 29, [69] = 30,
 [70] = 31, [71] = 32, [72] = 33, [73] = 34, [74] = 35, [75] = 36, [76] = 37, [77] = 38, [78] = 39, [79] = 40, [80] = 41, [81] = 42, [82] = 43, [83] = 44, [84] = 45, [85] = 46,
 [86] = 47, [87] = 48, [88] = 49, [89] = 50, [90] = 51, [48] = 52, [49] = 53, [50] = 54, [51] = 55, [52] = 56, [53] = 57, [54] = 58, [55] = 59, [56] = 60, [57] = 61, [40] = 62,
 [41] = 63
}

--- Encode the string to make it printable. <br>
--
-- Credit to WeakAuras2, this function is equivalant to the implementation
-- it is using right now. <br>
-- The code has been rewritten by the author of LibDeflate. <br>
-- The encoded string will be 25% larger than the origin string. However, every
-- single byte of the encoded string will be one of 64 printable ASCII
-- characters, which are can be easier copied, pasted and displayed.
-- (26 lowercase letters, 26 uppercase letters, 10 numbers digits,
-- left parenthese, or right parenthese)
-- @param str [string] The string to be encoded.
-- @return [string] The encoded string.
local function EncodeForPrint(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:EncodeForPrint(str):" .. " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  local strlen = #str
  local strlenMinus2 = strlen - 2
  local i = 1
  local buffer = {}
  local buffer_size = 0
  while i <= strlenMinus2 do
    local x1, x2, x3 = string_byte(str, i, i + 2)
    i = i + 3
    local cache = x1 + x2 * 256 + x3 * 65536
    local b1 = cache % 64
    cache = (cache - b1) / 64
    local b2 = cache % 64
    cache = (cache - b2) / 64
    local b3 = cache % 64
    local b4 = (cache - b3) / 64
    buffer_size = buffer_size + 1
    buffer[buffer_size] = _byte_to_6bit_char[b1] .. _byte_to_6bit_char[b2] ..
                            _byte_to_6bit_char[b3] .. _byte_to_6bit_char[b4]
  end
  
  local cache = 0
  local cache_bitlen = 0
  while i <= strlen do
    local x = string_byte(str, i, i)
    cache = cache + x * _pow2[cache_bitlen]
    cache_bitlen = cache_bitlen + 8
    i = i + 1
  end
  while cache_bitlen > 0 do
    local bit6 = cache % 64
    buffer_size = buffer_size + 1
    buffer[buffer_size] = _byte_to_6bit_char[bit6]
    cache = (cache - bit6) / 64
    cache_bitlen = cache_bitlen - 6
  end

  return table_concat(buffer)
end

--- Decode the printable string produced by LibDeflate:EncodeForPrint.
-- "str" will have its prefixed and trailing control characters or space
-- removed before it is decoded, so it is easier to use if "str" comes form
-- user copy and paste with some prefixed or trailing spaces.
-- Then decode fails if the string contains any characters cant be produced by
-- LibDeflate:EncodeForPrint. That means, decode fails if the string contains a
-- characters NOT one of 26 lowercase letters, 26 uppercase letters,
-- 10 numbers digits, left parenthese, or right parenthese.
-- @param str [string] The string to be decoded
-- @return [string/nil] The decoded string if succeeds. nil if fails.
local function DecodeForPrint(str)
  if type(str) ~= "string" then
    error(("Usage: LibDeflate:DecodeForPrint(str):" ..
            " 'str' - string expected got '%s'."):format(type(str)), 2)
  end
  str = str:gsub("^[%c ]+", "")
  str = str:gsub("[%c ]+$", "")

  local strlen = #str
  if strlen == 1 then return nil end
  local strlenMinus3 = strlen - 3
  local i = 1
  local buffer = {}
  local buffer_size = 0
  while i <= strlenMinus3 do
    local x1, x2, x3, x4 = string_byte(str, i, i + 3)
    x1 = _6bit_to_byte[x1]
    x2 = _6bit_to_byte[x2]
    x3 = _6bit_to_byte[x3]
    x4 = _6bit_to_byte[x4]
    if not (x1 and x2 and x3 and x4) then return nil end
    i = i + 4
    local cache = x1 + x2 * 64 + x3 * 4096 + x4 * 262144
    local b1 = cache % 256
    cache = (cache - b1) / 256
    local b2 = cache % 256
    local b3 = (cache - b2) / 256
    buffer_size = buffer_size + 1
    buffer[buffer_size] = _byte_to_char[b1] .. _byte_to_char[b2] .. _byte_to_char[b3]
  end

  local cache = 0
  local cache_bitlen = 0
  while i <= strlen do
    local x = string_byte(str, i, i)
    x = _6bit_to_byte[x]
    if not x then return nil end
    cache = cache + x * _pow2[cache_bitlen]
    cache_bitlen = cache_bitlen + 6
    i = i + 1
  end

  while cache_bitlen >= 8 do
    local byte = cache % 256
    buffer_size = buffer_size + 1
    buffer[buffer_size] = _byte_to_char[byte]
    cache = (cache - byte) / 256
    cache_bitlen = cache_bitlen - 8
  end

  return table_concat(buffer)
end

local function InternalClearCache()
  _chat_channel_codec = nil
  _addon_channel_codec = nil
end

-- For test. Don't use the functions in this table for real application.
-- Stuffs in this table is subject to change.
internals = {
  LoadStringToTable = LoadStringToTable,
  IsValidDictionary = IsValidDictionary,
  IsEqualAdler32 = IsEqualAdler32,
  _byte_to_6bit_char = _byte_to_6bit_char,
  _6bit_to_byte = _6bit_to_byte,
  InternalClearCache = InternalClearCache
}

--[[-- Commandline options
@class table
@name CommandlineOptions
@usage lua LibDeflate.lua [OPTION] [INPUT] [OUTPUT]
\-0    store only. no compression.
\-1    fastest compression.
\-9    slowest and best compression.
\-d    do decompression instead of compression.
\--dict <filename> specify the file that contains
the entire preset dictionary.
\-h    give this help.
\--strategy <fixed/huffman_only/dynamic> specify a special compression strategy.
\-v    print the version and copyright info.
\--zlib  use zlib format instead of raw deflate.
]]

-- currently no plan to support stdin and stdout.
-- Because Lua in Windows does not set stdout with binary mode.
if io and os and debug and _G.arg then
  local io = io
  local os = os
  local debug = debug
  local arg = _G.arg
  local debug_info = debug.getinfo(1)
  if debug_info.source == arg[0] or debug_info.short_src == arg[0] then
    -- We are indeed runnning THIS file from the commandline.
    local input
    local output
    local i = 1
    local status
    local is_zlib = false
    local is_decompress = false
    local level
    local strategy
    local dictionary
    while (arg[i]) do
      local a = arg[i]
      if a == "-h" then
        print(LibDeflate._COPYRIGHT ..
                "\nUsage: lua LibDeflate.lua [OPTION] [INPUT] [OUTPUT]\n" ..
                "  -0    store only. no compression.\n" ..
                "  -1    fastest compression.\n" ..
                "  -9    slowest and best compression.\n" ..
                "  -d    do decompression instead of compression.\n" ..
                "  --dict <filename> specify the file that contains" ..
                " the entire preset dictionary.\n" ..
                "  -h    give this help.\n" ..
                "  --strategy <fixed/huffman_only/dynamic>" ..
                " specify a special compression strategy.\n" ..
                "  -v    print the version and copyright info.\n" ..
                "  --zlib  use zlib format instead of raw deflate.\n")
        os.exit(0)
      elseif a == "-v" then
        print(LibDeflate._COPYRIGHT)
        os.exit(0)
      elseif a:find("^%-[0-9]$") then
        level = tonumber(a:sub(2, 2))
      elseif a == "-d" then
        is_decompress = true
      elseif a == "--dict" then
        i = i + 1
        local dict_filename = arg[i]
        if not dict_filename then
          io.stderr:write("You must speicify the dict filename")
          os.exit(1)
        end
        local dict_file, dict_status = io.open(dict_filename, "rb")
        if not dict_file then
          io.stderr:write(
            ("LibDeflate: Cannot read the dictionary file '%s': %s"):format(dict_filename, dict_status))
          os.exit(1)
        end
        local dict_str = dict_file:read("*all")
        dict_file:close()
        -- In your lua program, you should pass in adler32 as a CONSTANT
        -- , so it actually prevent you from modifying dictionary
        -- unintentionally during the program development. I do this
        -- here just because no convenient way to verify in commandline.
        dictionary = CreateDictionary(dict_str, #dict_str, Adler32(dict_str))
      elseif a == "--strategy" then
        -- Not sure if I should check error here
        -- If I do, redudant code.
        i = i + 1
        strategy = arg[i]
      elseif a == "--zlib" then
        is_zlib = true
      elseif a:find("^%-") then
        io.stderr:write(("LibDeflate: Invalid argument: %s"):format(a))
        os.exit(1)
      else
        if not input then
          input, status = io.open(a, "rb")
          if not input then
            io.stderr:write(
              ("LibDeflate: Cannot read the file '%s': %s"):format(a, tostring(
                                                                     status)))
            os.exit(1)
          end
        elseif not output then
          output, status = io.open(a, "wb")
          if not output then
            io.stderr:write(
              ("LibDeflate: Cannot write the file '%s': %s"):format(a, tostring(
                                                                      status)))
            os.exit(1)
          end
        end
      end
      i = i + 1
    end -- while (arg[i])

    if not input or not output then
      io.stderr:write("LibDeflate:" .. " You must specify both input and output files.")
      os.exit(1)
    end

    local input_data = input:read("*all")
    local configs = {level = level, strategy = strategy}
    local output_data
    if not is_decompress then
      if not is_zlib then
        if not dictionary then
          output_data = CompressDeflate(input_data, configs)
        else
          output_data = CompressDeflateWithDict(input_data,
                                                           dictionary, configs)
        end
      else
        if not dictionary then
          output_data = CompressZlib(input_data, configs)
        else
          output_data = CompressZlibWithDict(input_data, dictionary,
                                                        configs)
        end
      end
    else
      if not is_zlib then
        if not dictionary then
          output_data = DecompressDeflate(input_data)
        else
          output_data = DecompressDeflateWithDict(input_data,
                                                             dictionary)
        end
      else
        if not dictionary then
          output_data = DecompressZlib(input_data)
        else
          output_data = DecompressZlibWithDict(input_data, dictionary)
        end
      end
    end

    if not output_data then
      io.stderr:write("LibDeflate: Decompress fails.")
      os.exit(1)
    end

    output:write(output_data)
    if input and input ~= io.stdin then input:close() end
    if output and output ~= io.stdout then output:close() end

    io.stderr:write(("Successfully writes %d bytes"):format(output_data:len()))
    os.exit(0)
  end
end

-- other code
local function make_bitop_uncached(t, m)
  local function bitop(a, b)
    local res,p = 0,1
    while a ~= 0 and b ~= 0 do
      local am, bm = a%m, b%m
      res = res + t[am][bm]*p
      a = (a - am) / m
      b = (b - bm) / m
      p = p*m
    end
    res = res + (a+b)*p
    return res
  end
  return bitop
end

local function make_bitop(t)
  local op1 = make_bitop_uncached(t,2^1)
  local op2 = memoize(function(a)
    return memoize(function(b)
      return op1(a, b)
    end)
  end)
  return make_bitop_uncached(op2, 2^(t.n or 1))
end

local bxor = make_bitop {[0]={[0]=0,[1]=1},[1]={[0]=1,[1]=0}, n=4}

local function bnot(a) return MODM - a end

local function band(a,b) return ((a+b) - bxor(a,b))/2 end

local function rshift(a,disp) -- Lua5.2 insipred
  if disp < 0 then return lshift(a,-disp) end
  return floor(a % 2^32 / 2^disp)
end

-- CRC-32-IEEE 802.3 (V.42)
local POLY = 0xEDB88320




-- weak metatable marking objects as bitstream type
local is_bitstream = setmetatable({}, {__mode='k'})

local ofss=''

local function StartsWith(String,Start)
    String = String:upper()
    Start = Start:upper() 
    return string.sub(String,1,string.len(Start))==Start
end

local function complete(input)
    local allCompletions = {"Hello", "World", "Foo", "Bar"}
    local result = {}

    for i,v in pairs(allCompletions) do
        if StartsWith(v, input) then
            table.insert(result, v)
        end
    end
    return result
end

-- from crc32, CRC table.
local crc_table = memoize(function(i)
  local crc = i
  for _=1,8 do
    local b = band(crc, 1)
    crc = rshift(crc, 1)
    if b == 1 then crc = bxor(crc, POLY) end
  end
  return crc
end)

-- from crc32
local function crc32_byte(byte, crc)
  crc = bnot(crc or 0)
  local v1 = rshift(crc, 8)
  local v2 = crc_table[bxor(crc % 256, byte)]
  return bnot(bxor(v1, v2))
end
local crc32_byte = crc32_byte

-- from crc32
local function crc32_string(s, crc)
  crc = crc or 0
  for i=1,#s do
    crc = crc32_byte(s:byte(i), crc)
  end
  return crc
end
local crc32_string = crc32_string

-- from crc32
local function crc32(s, crc)
  if type(s) == 'string' then
    return crc32_string(s, crc)
  else
    return crc32_byte(s, crc)
  end
end

local function get_bitstream(o)
  local bs
  if is_bitstream[o] then
    return o
  elseif io.type(o) == 'file' then
    bs = bitstream_from_bytestream(bytestream_from_file(o))
  elseif type(o) == 'string' then
    bs = bitstream_from_bytestream(bytestream_from_string(o))
  elseif type(o) == 'function' then
    bs = bitstream_from_bytestream(bytestream_from_function(o))
  else
    runtime_error 'unrecognized type'
  end
  return bs
end

-- Returns Loc-tuple w/ current marked text or whole line (begin, end)
local function getTextLoc(c)
    local v = micro.CurPane()
    local a, b = nil, nil
    if c:HasSelection() then
        if c.CurSelection[1]:GreaterThan(-c.CurSelection[2]) then
            a, b = c.CurSelection[2], c.CurSelection[1]
        else
            a, b = c.CurSelection[1], c.CurSelection[2]
        end
    else
        local eol = string.len(v.Buf:Line(c.Loc.Y))
        a, b = c.Loc, buffer.Loc(eol, c.Y)
    end
    return buffer.Loc(a.X, a.Y), buffer.Loc(b.X, b.Y)
end


-- Returns the text of the buffer buf
local function getAllText(buf)
    -- local buf = micro.CurPane().Buf
    local i
    local result = ''
    local txt = {}

    for i=0, buf:End().Y do
        table.insert(txt, buf:Line(i))
    end
    
    -- return table.concat(txt, "\n")
    
    for i, v in ipairs(txt) do
    	if i==1 then
    		result=v
    	else
    		result = result.."\n"..v
    	end
    end
    return result
end

-- Returns the current marked text or whole line
local function getText(a, b)
    local txt, buf = {}, micro.CurPane().Buf

    -- Editing a single line?
    if a.Y == b.Y then
        return buf:Line(a.Y):sub(a.X+1, b.X)
    end

    -- Add first part of text selection (a.X+1 as Lua is 1-indexed)
    table.insert(txt, buf:Line(a.Y):sub(a.X+1))

    -- Stuff in the middle
    for lineNo = a.Y+1, b.Y-1 do
        table.insert(txt, buf:Line(lineNo))
    end

    -- Insert last part of selection
    table.insert(txt, buf:Line(b.Y):sub(1, b.X))

    return table.concat(txt, "\n")
end

local function num24bytes(num)
  num = num % 2^32
  local str = string.char(floor(num % 2^8))..string.char(floor(num % 2^16) / 2^8)..string.char(floor((num % 2^24) / 2^16))..string.char(floor(num / 2^24))
  return str
end

local function ofs(inp)
  ofss=ofss..string.char(inp)
end

local function parse_gzip_header(bs)
  -- local FLG_FTEXT = 2^0
  local FLG_FHCRC = 2^1
  local FLG_FEXTRA = 2^2
  local FLG_FNAME = 2^3
  local FLG_FCOMMENT = 2^4

  local id1 = bs:read(8)
  local id2 = bs:read(8)
  if id1 ~= 31 or id2 ~= 139 then
    -- runtime_error 'not in gzip format'
    return false
  end
  local cm = bs:read(8)  -- compression method
  local flg = bs:read(8) -- FLaGs
  local mtime = bs:read(32) -- Modification TIME
  local xfl = bs:read(8) -- eXtra FLags
  local os = bs:read(8) -- Operating System

  if DEBUG then
    debug("CM=", cm)
    debug("FLG=", flg)
    debug("MTIME=", mtime)
    -- debug("MTIME_str=",os.date("%Y-%m-%d %H:%M:%S",mtime)) -- non-portable
    debug("XFL=", xfl)
    debug("OS=", os)
  end

  if not os then runtime_error 'invalid header' end

  if hasbit(flg, FLG_FEXTRA) then
    local xlen = bs:read(16)
    local extra = 0
    for i=1,xlen do
      extra = bs:read(8)
    end
    if not extra then runtime_error 'invalid header' end
  end

  local function parse_zstring(bs)
    repeat
      local by = bs:read(8)
      if not by then runtime_error 'invalid header' end
    until by == 0
  end

  if hasbit(flg, FLG_FNAME) then
    parse_zstring(bs)
  end

  if hasbit(flg, FLG_FCOMMENT) then
    parse_zstring(bs)
  end

  if hasbit(flg, FLG_FHCRC) then
    local crc16 = bs:read(16)
    if not crc16 then runtime_error 'invalid header' end
    -- IMPROVE: check CRC.  where is an example .gz file that
    -- has this set?
    if DEBUG then
      debug("CRC16=", crc16)
    end
  end
end

-- from lancelijade
local function crc32_table_lancelijade(x)
	if x == 1 then
		return 0x00000000
	elseif x == 2 then
		return 0x77073096
	elseif x == 3 then
		return 0xee0e612c
	elseif x == 4 then
		return 0x990951ba
	elseif x == 5 then
		return 0x076dc419
	elseif x == 6 then
		return 0x706af48f
	elseif x == 7 then
		return 0xe963a535
	elseif x == 8 then
		return 0x9e6495a3
	elseif x == 9 then
		return 0x0edb8832
	elseif x == 10 then
		return 0x79dcb8a4
	elseif x == 11 then
		return 0xe0d5e91e
	elseif x == 12 then
		return 0x97d2d988
	elseif x == 13 then
		return 0x09b64c2b
	elseif x == 14 then
		return 0x7eb17cbd
	elseif x == 15 then
		return 0xe7b82d07
	elseif x == 16 then
		return 0x90bf1d91
	elseif x == 17 then
		return 0x1db71064
	elseif x == 18 then
		return 0x6ab020f2
	elseif x == 19 then
		return 0xf3b97148
	elseif x == 20 then
		return 0x84be41de
	elseif x == 21 then
		return 0x1adad47d
	elseif x == 22 then
		return 0x6ddde4eb
	elseif x == 23 then
		return 0xf4d4b551
	elseif x == 24 then
		return 0x83d385c7
	elseif x == 25 then
		return 0x136c9856
	elseif x == 26 then
		return 0x646ba8c0
	elseif x == 27 then
		return 0xfd62f97a
	elseif x == 28 then
		return 0x8a65c9ec
	elseif x == 29 then
		return 0x14015c4f
	elseif x == 30 then
		return 0x63066cd9
	elseif x == 31 then
		return 0xfa0f3d63
	elseif x == 32 then
		return 0x8d080df5
	elseif x == 33 then
		return 0x3b6e20c8
	elseif x == 34 then
		return 0x4c69105e
	elseif x == 35 then
		return 0xd56041e4
	elseif x == 36 then
		return 0xa2677172
	elseif x == 37 then
		return 0x3c03e4d1
	elseif x == 38 then
		return 0x4b04d447
	elseif x == 39 then
		return 0xd20d85fd
	elseif x == 40 then
		return 0xa50ab56b
	elseif x == 41 then
		return 0x35b5a8fa
	elseif x == 42 then
		return 0x42b2986c
	elseif x == 43 then
		return 0xdbbbc9d6
	elseif x == 44 then
		return 0xacbcf940
	elseif x == 45 then
		return 0x32d86ce3
	elseif x == 46 then
		return 0x45df5c75
	elseif x == 47 then
		return 0xdcd60dcf
	elseif x == 48 then
		return 0xabd13d59
	elseif x == 49 then
		return 0x26d930ac
	elseif x == 50 then
		return 0x51de003a
	elseif x == 51 then
		return 0xc8d75180
	elseif x == 52 then
		return 0xbfd06116
	elseif x == 53 then
		return 0x21b4f4b5
	elseif x == 54 then
		return 0x56b3c423
	elseif x == 55 then
		return 0xcfba9599
	elseif x == 56 then
		return 0xb8bda50f
	elseif x == 57 then
		return 0x2802b89e
	elseif x == 58 then
		return 0x5f058808
	elseif x == 59 then
		return 0xc60cd9b2
	elseif x == 60 then
		return 0xb10be924
	elseif x == 61 then
		return 0x2f6f7c87
	elseif x == 62 then
		return 0x58684c11
	elseif x == 63 then
		return 0xc1611dab
	elseif x == 64 then
		return 0xb6662d3d
	elseif x == 65 then
		return 0x76dc4190
	elseif x == 66 then
		return 0x01db7106
	elseif x == 67 then
		return 0x98d220bc
	elseif x == 68 then
		return 0xefd5102a
	elseif x == 69 then
		return 0x71b18589
	elseif x == 70 then
		return 0x06b6b51f
	elseif x == 71 then
		return 0x9fbfe4a5
	elseif x == 72 then
		return 0xe8b8d433
	elseif x == 73 then
		return 0x7807c9a2
	elseif x == 74 then
		return 0x0f00f934
	elseif x == 75 then
		return 0x9609a88e
	elseif x == 76 then
		return 0xe10e9818
	elseif x == 77 then
		return 0x7f6a0dbb
	elseif x == 78 then
		return 0x086d3d2d
	elseif x == 79 then
		return 0x91646c97
	elseif x == 80 then
		return 0xe6635c01
	elseif x == 81 then
		return 0x6b6b51f4
	elseif x == 82 then
		return 0x1c6c6162
	elseif x == 83 then
		return 0x856530d8
	elseif x == 84 then
		return 0xf262004e
	elseif x == 85 then
		return 0x6c0695ed
	elseif x == 86 then
		return 0x1b01a57b
	elseif x == 87 then
		return 0x8208f4c1
	elseif x == 88 then
		return 0xf50fc457
	elseif x == 89 then
		return 0x65b0d9c6
	elseif x == 90 then
		return 0x12b7e950
	elseif x == 91 then
		return 0x8bbeb8ea
	elseif x == 92 then
		return 0xfcb9887c
	elseif x == 93 then
		return 0x62dd1ddf
	elseif x == 94 then
		return 0x15da2d49
	elseif x == 95 then
		return 0x8cd37cf3
	elseif x == 96 then
		return 0xfbd44c65
	elseif x == 97 then
		return 0x4db26158
	elseif x == 98 then
		return 0x3ab551ce
	elseif x == 99 then
		return 0xa3bc0074
	elseif x == 100 then
		return 0xd4bb30e2
	elseif x == 101 then
		return 0x4adfa541
	elseif x == 102 then
		return 0x3dd895d7
	elseif x == 103 then
		return 0xa4d1c46d
	elseif x == 104 then
		return 0xd3d6f4fb
	elseif x == 105 then
		return 0x4369e96a
	elseif x == 106 then
		return 0x346ed9fc
	elseif x == 107 then
		return 0xad678846
	elseif x == 108 then
		return 0xda60b8d0
	elseif x == 109 then
		return 0x44042d73
	elseif x == 110 then
		return 0x33031de5
	elseif x == 111 then
		return 0xaa0a4c5f
	elseif x == 112 then
		return 0xdd0d7cc9
	elseif x == 113 then
		return 0x5005713c
	elseif x == 114 then
		return 0x270241aa
	elseif x == 115 then
		return 0xbe0b1010
	elseif x == 116 then
		return 0xc90c2086
	elseif x == 117 then
		return 0x5768b525
	elseif x == 118 then
		return 0x206f85b3
	elseif x == 119 then
		return 0xb966d409
	elseif x == 120 then
		return 0xce61e49f
	elseif x == 121 then
		return 0x5edef90e
	elseif x == 122 then
		return 0x29d9c998
	elseif x == 123 then
		return 0xb0d09822
	elseif x == 124 then
		return 0xc7d7a8b4
	elseif x == 125 then
		return 0x59b33d17
	elseif x == 126 then
		return 0x2eb40d81
	elseif x == 127 then
		return 0xb7bd5c3b
	elseif x == 128 then
		return 0xc0ba6cad
	elseif x == 129 then
		return 0xedb88320
	elseif x == 130 then
		return 0x9abfb3b6
	elseif x == 131 then
		return 0x03b6e20c
	elseif x == 132 then
		return 0x74b1d29a
	elseif x == 133 then
		return 0xead54739
	elseif x == 134 then
		return 0x9dd277af
	elseif x == 135 then
		return 0x04db2615
	elseif x == 136 then
		return 0x73dc1683
	elseif x == 137 then
		return 0xe3630b12
	elseif x == 138 then
		return 0x94643b84
	elseif x == 139 then
		return 0x0d6d6a3e
	elseif x == 140 then
		return 0x7a6a5aa8
	elseif x == 141 then
		return 0xe40ecf0b
	elseif x == 142 then
		return 0x9309ff9d
	elseif x == 143 then
		return 0x0a00ae27
	elseif x == 144 then
		return 0x7d079eb1
	elseif x == 145 then
		return 0xf00f9344
	elseif x == 146 then
		return 0x8708a3d2
	elseif x == 147 then
		return 0x1e01f268
	elseif x == 148 then
		return 0x6906c2fe
	elseif x == 149 then
		return 0xf762575d
	elseif x == 150 then
		return 0x806567cb
	elseif x == 151 then
		return 0x196c3671
	elseif x == 152 then
		return 0x6e6b06e7
	elseif x == 153 then
		return 0xfed41b76
	elseif x == 154 then
		return 0x89d32be0
	elseif x == 155 then
		return 0x10da7a5a
	elseif x == 156 then
		return 0x67dd4acc
	elseif x == 157 then
		return 0xf9b9df6f
	elseif x == 158 then
		return 0x8ebeeff9
	elseif x == 159 then
		return 0x17b7be43
	elseif x == 160 then
		return 0x60b08ed5
	elseif x == 161 then
		return 0xd6d6a3e8
	elseif x == 162 then
		return 0xa1d1937e
	elseif x == 163 then
		return 0x38d8c2c4
	elseif x == 164 then
		return 0x4fdff252
	elseif x == 165 then
		return 0xd1bb67f1
	elseif x == 166 then
		return 0xa6bc5767
	elseif x == 167 then
		return 0x3fb506dd
	elseif x == 168 then
		return 0x48b2364b
	elseif x == 169 then
		return 0xd80d2bda
	elseif x == 170 then
		return 0xaf0a1b4c
	elseif x == 171 then
		return 0x36034af6
	elseif x == 172 then
		return 0x41047a60
	elseif x == 173 then
		return 0xdf60efc3
	elseif x == 174 then
		return 0xa867df55
	elseif x == 175 then
		return 0x316e8eef
	elseif x == 176 then
		return 0x4669be79
	elseif x == 177 then
		return 0xcb61b38c
	elseif x == 178 then
		return 0xbc66831a
	elseif x == 179 then
		return 0x256fd2a0
	elseif x == 180 then
		return 0x5268e236
	elseif x == 181 then
		return 0xcc0c7795
	elseif x == 182 then
		return 0xbb0b4703
	elseif x == 183 then
		return 0x220216b9
	elseif x == 184 then
		return 0x5505262f
	elseif x == 185 then
		return 0xc5ba3bbe
	elseif x == 186 then
		return 0xb2bd0b28
	elseif x == 187 then
		return 0x2bb45a92
	elseif x == 188 then
		return 0x5cb36a04
	elseif x == 189 then
		return 0xc2d7ffa7
	elseif x == 190 then
		return 0xb5d0cf31
	elseif x == 191 then
		return 0x2cd99e8b
	elseif x == 192 then
		return 0x5bdeae1d
	elseif x == 193 then
		return 0x9b64c2b0
	elseif x == 194 then
		return 0xec63f226
	elseif x == 195 then
		return 0x756aa39c
	elseif x == 196 then
		return 0x026d930a
	elseif x == 197 then
		return 0x9c0906a9
	elseif x == 198 then
		return 0xeb0e363f
	elseif x == 199 then
		return 0x72076785
	elseif x == 200 then
		return 0x05005713
	elseif x == 201 then
		return 0x95bf4a82
	elseif x == 202 then
		return 0xe2b87a14
	elseif x == 203 then
		return 0x7bb12bae
	elseif x == 204 then
		return 0x0cb61b38
	elseif x == 205 then
		return 0x92d28e9b
	elseif x == 206 then
		return 0xe5d5be0d
	elseif x == 207 then
		return 0x7cdcefb7
	elseif x == 208 then
		return 0x0bdbdf21
	elseif x == 209 then
		return 0x86d3d2d4
	elseif x == 210 then
		return 0xf1d4e242
	elseif x == 211 then
		return 0x68ddb3f8
	elseif x == 212 then
		return 0x1fda836e
	elseif x == 213 then
		return 0x81be16cd
	elseif x == 214 then
		return 0xf6b9265b
	elseif x == 215 then
		return 0x6fb077e1
	elseif x == 216 then
		return 0x18b74777
	elseif x == 217 then
		return 0x88085ae6
	elseif x == 218 then
		return 0xff0f6a70
	elseif x == 219 then
		return 0x66063bca
	elseif x == 220 then
		return 0x11010b5c
	elseif x == 221 then
		return 0x8f659eff
	elseif x == 222 then
		return 0xf862ae69
	elseif x == 223 then
		return 0x616bffd3
	elseif x == 224 then
		return 0x166ccf45
	elseif x == 225 then
		return 0xa00ae278
	elseif x == 226 then
		return 0xd70dd2ee
	elseif x == 227 then
		return 0x4e048354
	elseif x == 228 then
		return 0x3903b3c2
	elseif x == 229 then
		return 0xa7672661
	elseif x == 230 then
		return 0xd06016f7
	elseif x == 231 then
		return 0x4969474d
	elseif x == 232 then
		return 0x3e6e77db
	elseif x == 233 then
		return 0xaed16a4a
	elseif x == 234 then
		return 0xd9d65adc
	elseif x == 235 then
		return 0x40df0b66
	elseif x == 236 then
		return 0x37d83bf0
	elseif x == 237 then
		return 0xa9bcae53
	elseif x == 238 then
		return 0xdebb9ec5
	elseif x == 239 then
		return 0x47b2cf7f
	elseif x == 240 then
		return 0x30b5ffe9
	elseif x == 241 then
		return 0xbdbdf21c
	elseif x == 242 then
		return 0xcabac28a
	elseif x == 243 then
		return 0x53b39330
	elseif x == 244 then
		return 0x24b4a3a6
	elseif x == 245 then
		return 0xbad03605
	elseif x == 246 then
		return 0xcdd70693
	elseif x == 247 then
		return 0x54de5729
	elseif x == 248 then
		return 0x23d967bf
	elseif x == 249 then
		return 0xb3667a2e
	elseif x == 250 then
		return 0xc4614ab8
	elseif x == 251 then
		return 0x5d681b02
	elseif x == 252 then
		return 0x2a6f2b94
	elseif x == 253 then
		return 0xb40bbe37
	elseif x == 254 then
		return 0xc30c8ea1
	elseif x == 255 then
		return 0x5a05df1b
	elseif x == 256 then
		return 0x2d02ef8d
	end
end

local function crc32_lancelijade(str)
    str = tostring(str)
    local count = string.len(str)
    local crc = 2 ^ 32 - 1 
    local i = 1

    while count > 0 do
        local byte = string.byte(str, i)
        crc = bxor(rshift(crc, 8), crc32_table_lancelijade(bxor(band(crc, 0xFF), byte) + 1))
        i = i + 1
        count = count - 1
    end
    crc = bxor(crc, 0xFFFFFFFF)
    -- dirty hack for bitop return number < 0
    if crc < 0 then crc = crc + 2 ^ 32 end 

    return crc
end


local function read_file(path)
    local file = io.open(path, "rb") -- r read mode and b binary mode
    if not file then return nil end
    local content = file:read "*a" -- *a or *all reads the whole file
    file:close()
    return content
end

local function write_file(path, content)
    local file = io.open(path, "wb+") -- r read mode and b binary mode
    if not file then return nil end
    local content = file:write(content)
    file:flush()
    assert(file:close())
end

local function write_gz_file(path, content)
	local header=string.char(31)..string.char(139)..string.char(8)..string.char(0)..num24bytes(os.time(os.date("*t", os.time()+3600*(os.date("*t").hour-os.date("!*t").hour))))
	local data_compressed_zlib=CompressZlib(content)
	local data_writeout = header..string.sub(data_compressed_zlib,1,#data_compressed_zlib-4)
	local mcrc32 = 0
	mcrc32 = crc32(content,mcrc32)
	data_writeout = data_writeout..num24bytes(mcrc32)..num24bytes(#content)
	write_file(path,data_writeout)
end

function init()
    micro.CurPane().Buf:Close()
    if ofss~='' then
        local bp = micro.CurPane()
        local buf = bp.Buf
        local path=buf.path
        local AbsPath=buf.AbsPath
    	local newbuffer=buffer.NewBuffer(ofss,path)
    	newbuffer.path=path
    	newbuffer.AbsPath=AbsPath
    	micro.CurPane():OpenBuffer(newbuffer)
    end
    ofss = ''
end

function onBufferOpen(buf)
    
    local suffix = ''
    local done = false
    if buf:GetName():len()> 3 then
    	suffix=string.sub(buf:GetName(),buf:GetName():len()-2,buf:GetName():len())
    end
    
    if suffix == '.gz' and ofss == '' then
    	local data=read_file(buf.path)
    	-- local byss=bytestream_from_string(data)
    	-- local bss=bitstream_from_bytestream(byss)
    	
    	local firstbyte = string.byte(data,1)
    	local secondbyte = string.byte(data,2)
    	local flagbyte = string.byte(data, 4)
    	
    	if (firstbyte == 31 and secondbyte == 139) then
    	    local headerbyte = -1
    	    local pos = 11
    	    local state
    	    -- handle gzip type headers having filenames
	    if flagbyte == 8 then
		    while headerbyte ~=0 do
		    	headerbyte=string.byte(data,pos)
		    	pos = pos+1
		    end
		    state = CreateDecompressState(string.sub(data,9,10)..string.sub(data,pos,#data-8))
	    else   
		    state = CreateDecompressState(string.sub(data,9,#data-8))
	    end		    
	    
  	    local ReadBits = state.ReadBits
  	    local dummy0 = ReadBits(8)
  	    local FLG = ReadBits(8)
  	    -- local FDIST = ((FLG - FLG % 32) / 32 % 2)
  	    local testresult, teststatus = Inflate(state)
    	    if testresult ~= nil and type(testresult) == 'string' then
    	    	local mcrc32 = 0
    	    	-- mcrc32 = crc32_lancelijade(testresult)
    	    	mcrc32 = crc32(testresult,mcrc32)
    	    	local ecrc32 = string.sub(data,#data-7,#data-4)
    	    	if num24bytes(mcrc32) == ecrc32 then
    	    	    ofss=testresult
    	    	    done = true
    	    	end
    	    end
    	    
    	    if not done then
	    	    local gzfile = io.open(buf.path, "rb") -- r read mode and b binary mode
	    	    -- local bys=bytestream_from_file(gzfile)
	    	    -- local bs=bitstream_from_bytestream(bys)
	    	    ofss=''
	    	    gunzip({input=gzfile, output=ofs,disable_crc=true})
	    	    gzfile:close()
	    end
    	end
    end
    
    data=nil
    -- decompress_deflate=nil
    -- loc1=nil
end

function onSave(bp)
    if bp.Buf:FileType() == "go" then
        if bp.Buf.Settings["go.goimports"] then
            goimports(bp)
        elseif bp.Buf.Settings["go.gofmt"] then
            gofmt(bp)
        end
    end
    return true
end

function preQuit(view)
    local result = false
    if view.Buf:modified() then     	    	
    	local suffix = ''
        if view.Buf:GetName():len()> 3 then
    		suffix=string.sub(view.buf:GetName(),view.buf:GetName():len()-2,view.buf:GetName():len())
    	end
    	if suffix == '.gz' and view ~= nil then
    	    micro.InfoBar():YNPrompt('Save changes to '..view.Buf:GetName()..' before closing? (y,n,esc)', function(yes, canceled)
    	    	     if yes and not canceled then
                        local editortext=getAllText(view.Buf)
                        write_gz_file(view.Buf:GetName(),editortext)
                        -- a quit is necessary, micro will run an unnecessary save if true is returned, yet not quit if false is returned
    	    	     	view:ForceQuit()
                        result = true    	    	     	
    	    	     elseif canceled then
    	    	     else
    	    	     	view:ForceQuit()
    	    	     end
    	    end)
    	    return false
    	end
    end
    return true
end

function preSave(bp)
	local result = false
	local suffix = ''
	if bp.Buf:GetName():len()> 3 then
		suffix=string.sub(bp.buf:GetName(),bp.buf:GetName():len()-2,bp.buf:GetName():len())
	end
	if suffix == '.gz' then
    		micro.InfoBar():YNPrompt('Save changes to '..bp.Buf:GetName()..'? (y,n,esc)', function(yes, canceled) 			
	    	    	if yes and not canceled then
	    	    		-- save procedure
	    	        	local editortext=getAllText(bp.Buf)
	    	    	     	write_gz_file(bp.Buf:GetName(),editortext)
	    	        	result= true
	    	    	elseif canceled then
	    	    		result = true
	    	   	end
    	   	end)
    	end
	return result
end
