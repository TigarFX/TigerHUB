local hmac;

do

    local unpack, table_concat, byte, char, string_rep, sub, string_format, floor, ceil, min, max =
       table.unpack or unpack, table.concat, string.byte, string.char, string.rep, string.sub, string.format, math.floor, math.ceil, math.min, math.max;shared.unpack = unpack;


    local AND, OR, XOR, SHL, SHR, ROL, ROR, HEX

    local function SHL(x, n)
       return (x * 2^n) % 4294967296
    end

    local function SHR(x, n)
       x = x % 4294967296 / 2^n
       return x - x % 1
    end

    local function ROL(x, n)
       x = x % 4294967296 * 2^n
       local r = x % 4294967296
       return r + (x - r) / 4294967296
    end

    local function ROR(x, n)
       x = x % 4294967296 / 2^n
       local r = x % 1
       return r * 4294967296 + (x - r)
    end

    local AND_of_two_bytes = {}  -- look-up table (256*256 entries)
    for idx = 0, 65535 do
       local x = idx % 256
       local y = (idx - x) / 256
       local res = 0
       local w = 1
       while x * y ~= 0 do
          local rx = x % 2
          local ry = y % 2
          res = res + rx * ry * w
          x = (x - rx) / 2
          y = (y - ry) / 2
          w = w * 2
       end
       AND_of_two_bytes[idx] = res
    end

    local function and_or_xor(x, y, operation)
       -- operation: nil = AND, 1 = OR, 2 = XOR
       local x0 = x % 4294967296
       local y0 = y % 4294967296
       local rx = x0 % 256
       local ry = y0 % 256
       local res = AND_of_two_bytes[rx + ry * 256]
       x = x0 - rx
       y = (y0 - ry) / 256
       rx = x % 65536
       ry = y % 256
       res = res + AND_of_two_bytes[rx + ry] * 256
       x = (x - rx) / 256
       y = (y - ry) / 256
       rx = x % 65536 + y % 256
       res = res + AND_of_two_bytes[rx] * 65536
       res = res + AND_of_two_bytes[(x + y - rx) / 256] * 16777216
       if operation then
          res = x0 + y0 - operation * res
       end
       return res
    end

    local function AND(x, y)
       return and_or_xor(x, y)
    end

    local function OR(x, y)
       return and_or_xor(x, y, 1)
    end

    local function XOR(x, y, z)          -- 2 or 3 arguments
       if z then
          y = and_or_xor(y, z, 2)
       end
       return and_or_xor(x, y, 2)
    end

    local function HEX(x)
       return string_format("%08x", x % 4294967296)
    end

    -- Arrays of SHA2 "magic numbers"
    local sha2_K_lo, sha2_K_hi, sha2_H_lo, sha2_H_hi = {}, {}, {}, {}
    local sha2_H_ext256 = {[224] = {}, [256] = sha2_H_hi}
    local sha2_H_ext512_lo, sha2_H_ext512_hi = {[384] = {}, [512] = sha2_H_lo}, {[384] = {}, [512] = sha2_H_hi}

    local common_W = {}  -- a temporary table shared between all calculations

    local function sha256_feed_64(H, K, str, W, offs, size)
       -- offs >= 0, size >= 0, size is multiple of 64
       for pos = offs, size + offs - 1, 64 do
          for j = 1, 16 do
             pos = pos + 4
             local a, b, c, d = byte(str, pos - 3, pos)
             W[j] = ((a * 256 + b) * 256 + c) * 256 + d
          end
          for j = 17, 64 do
             local a, b = W[j-15], W[j-2]
             W[j] = XOR(ROR(a, 7), ROL(a, 14), SHR(a, 3)) + XOR(ROL(b, 15), ROL(b, 13), SHR(b, 10)) + W[j-7] + W[j-16]
          end
          local a, b, c, d, e, f, g, h, z = H[1], H[2], H[3], H[4], H[5], H[6], H[7], H[8]
          for j = 1, 64 do
             z = XOR(ROR(e, 6), ROR(e, 11), ROL(e, 7)) + AND(e, f) + AND(-1-e, g) + h + K[j] + W[j]
             h = g
             g = f
             f = e
             e = z + d
             d = c
             c = b
             b = a
             a = z + AND(d, c) + AND(a, XOR(d, c)) + XOR(ROR(a, 2), ROR(a, 13), ROL(a, 10))
          end
          H[1], H[2], H[3], H[4] = (a + H[1]) % 4294967296, (b + H[2]) % 4294967296, (c + H[3]) % 4294967296, (d + H[4]) % 4294967296
          H[5], H[6], H[7], H[8] = (e + H[5]) % 4294967296, (f + H[6]) % 4294967296, (g + H[7]) % 4294967296, (h + H[8]) % 4294967296
       end
    end

    local function sha512_feed_128(H_lo, H_hi, K_lo, K_hi, str, W, offs, size)
       -- offs >= 0, size >= 0, size is multiple of 128
       -- W1_hi, W1_lo, W2_hi, W2_lo, ...   Wk_hi = W[2*k-1], Wk_lo = W[2*k]
       for pos = offs, size + offs - 1, 128 do
          for j = 1, 32 do
             pos = pos + 4
             local a, b, c, d = byte(str, pos - 3, pos)
             W[j] = ((a * 256 + b) * 256 + c) * 256 + d
          end
          local tmp1, tmp2
          for jj = 17 * 2, 80 * 2, 2 do
             local a_lo, a_hi, b_lo, b_hi = W[jj-30], W[jj-31], W[jj-4], W[jj-5]
             tmp1 = XOR(SHR(a_lo, 1) + SHL(a_hi, 31), SHR(a_lo, 8) + SHL(a_hi, 24), SHR(a_lo, 7) + SHL(a_hi, 25)) + XOR(SHR(b_lo, 19) + SHL(b_hi, 13), SHL(b_lo, 3) + SHR(b_hi, 29), SHR(b_lo, 6) + SHL(b_hi, 26)) + W[jj-14] + W[jj-32]
             tmp2 = tmp1 % 4294967296
             W[jj-1] = XOR(SHR(a_hi, 1) + SHL(a_lo, 31), SHR(a_hi, 8) + SHL(a_lo, 24), SHR(a_hi, 7)) + XOR(SHR(b_hi, 19) + SHL(b_lo, 13), SHL(b_hi, 3) + SHR(b_lo, 29), SHR(b_hi, 6)) + W[jj-15] + W[jj-33] + (tmp1 - tmp2) / 4294967296
             W[jj] = tmp2
          end
          local a_lo, b_lo, c_lo, d_lo, e_lo, f_lo, g_lo, h_lo, z_lo = H_lo[1], H_lo[2], H_lo[3], H_lo[4], H_lo[5], H_lo[6], H_lo[7], H_lo[8]
          local a_hi, b_hi, c_hi, d_hi, e_hi, f_hi, g_hi, h_hi, z_hi = H_hi[1], H_hi[2], H_hi[3], H_hi[4], H_hi[5], H_hi[6], H_hi[7], H_hi[8]
          for j = 1, 80 do
             local jj = 2 * j
             tmp1 = XOR(SHR(e_lo, 14) + SHL(e_hi, 18), SHR(e_lo, 18) + SHL(e_hi, 14), SHL(e_lo, 23) + SHR(e_hi, 9)) + AND(e_lo, f_lo) + AND(-1-e_lo, g_lo) + h_lo + K_lo[j] + W[jj]
             z_lo = tmp1 % 4294967296
             z_hi = XOR(SHR(e_hi, 14) + SHL(e_lo, 18), SHR(e_hi, 18) + SHL(e_lo, 14), SHL(e_hi, 23) + SHR(e_lo, 9)) + AND(e_hi, f_hi) + AND(-1-e_hi, g_hi) + h_hi + K_hi[j] + W[jj-1] + (tmp1 - z_lo) / 4294967296
             h_lo = g_lo
             h_hi = g_hi
             g_lo = f_lo
             g_hi = f_hi
             f_lo = e_lo
             f_hi = e_hi
             tmp1 = z_lo + d_lo
             e_lo = tmp1 % 4294967296
             e_hi = z_hi + d_hi + (tmp1 - e_lo) / 4294967296
             d_lo = c_lo
             d_hi = c_hi
             c_lo = b_lo
             c_hi = b_hi
             b_lo = a_lo
             b_hi = a_hi
             tmp1 = z_lo + AND(d_lo, c_lo) + AND(b_lo, XOR(d_lo, c_lo)) + XOR(SHR(b_lo, 28) + SHL(b_hi, 4), SHL(b_lo, 30) + SHR(b_hi, 2), SHL(b_lo, 25) + SHR(b_hi, 7))
             a_lo = tmp1 % 4294967296
             a_hi = z_hi + (AND(d_hi, c_hi) + AND(b_hi, XOR(d_hi, c_hi))) + XOR(SHR(b_hi, 28) + SHL(b_lo, 4), SHL(b_hi, 30) + SHR(b_lo, 2), SHL(b_hi, 25) + SHR(b_lo, 7)) + (tmp1 - a_lo) / 4294967296
          end
          tmp1 = H_lo[1] + a_lo
          tmp2 = tmp1 % 4294967296
          H_lo[1], H_hi[1] = tmp2, (H_hi[1] + a_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[2] + b_lo
          tmp2 = tmp1 % 4294967296
          H_lo[2], H_hi[2] = tmp2, (H_hi[2] + b_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[3] + c_lo
          tmp2 = tmp1 % 4294967296
          H_lo[3], H_hi[3] = tmp2, (H_hi[3] + c_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[4] + d_lo
          tmp2 = tmp1 % 4294967296
          H_lo[4], H_hi[4] = tmp2, (H_hi[4] + d_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[5] + e_lo
          tmp2 = tmp1 % 4294967296
          H_lo[5], H_hi[5] = tmp2, (H_hi[5] + e_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[6] + f_lo
          tmp2 = tmp1 % 4294967296
          H_lo[6], H_hi[6] = tmp2, (H_hi[6] + f_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[7] + g_lo
          tmp2 = tmp1 % 4294967296
          H_lo[7], H_hi[7] = tmp2, (H_hi[7] + g_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
          tmp1 = H_lo[8] + h_lo
          tmp2 = tmp1 % 4294967296
          H_lo[8], H_hi[8] = tmp2, (H_hi[8] + h_hi + (tmp1 - tmp2) / 4294967296) % 4294967296
       end
    end

    --------------------------------------------------------------------------------
    -- CALCULATING THE MAGIC NUMBERS (roots of primes)
    --------------------------------------------------------------------------------

    do
       local function mul(src1, src2, factor, result_length)
          -- Long arithmetic multiplication: src1 * src2 * factor
          -- src1, src2 - long integers (arrays of digits in base 2^24)
          -- factor - short integer
          local result = {}
          local carry = 0
          local value = 0.0
          local weight = 1.0
          for j = 1, result_length do
             local prod = 0
             for k = max(1, j + 1 - #src2), min(j, #src1) do
                prod = prod + src1[k] * src2[j + 1 - k]
             end
             carry = carry + prod * factor
             local digit = carry % 16777216
             result[j] = digit
             carry = floor(carry / 16777216)
             value = value + digit * weight
             weight = weight * 2^24
          end
          return
             result,    -- long integer
             value      -- and its floating point approximation
       end

       local idx, step, p, one  = 0, {4, 1, 2, -2, 2}, 4, {1}
       local sqrt_hi, sqrt_lo, idx_disp = sha2_H_hi, sha2_H_lo, 0
       repeat
          p = p + step[p % 6]
          local d = 1
          repeat
             d = d + step[d % 6]
             if d * d > p then
                idx = idx + 1
                local root = p^(1/3)
                local R = mul({floor(root * 2^40)}, one, 1, 2)
                local _, delta = mul(R, mul(R, R, 1, 4), -1, 4)
                local hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                local lo = R[1] % 256 * 16777216 + floor(delta * (2^-56 / 3) * root / p)
                sha2_K_hi[idx], sha2_K_lo[idx] = hi, lo
                if idx < 17 then
                   root = p^(1/2)
                   R = mul({floor(root * 2^40)}, one, 1, 2)
                   _, delta = mul(R, R, -1, 2)
                   hi = R[2] % 65536 * 65536 + floor(R[1] / 256)
                   lo = R[1] % 256 * 16777216 + floor(delta * 2^-17 / root)
                   sha2_H_ext256[224][idx + idx_disp] = lo
                   sqrt_hi[idx + idx_disp], sqrt_lo[idx + idx_disp] = hi, lo
                   if idx == 8 then
                      sqrt_hi, sqrt_lo, idx_disp = sha2_H_ext512_hi[384], sha2_H_ext512_lo[384], -8
                   end
                end
                break
             end
          until p % d == 0
       until idx > 79
    end

    -- Calculating IV for SHA512/224 and SHA512/256
    for width = 224, 256, 32 do
       local H_lo, H_hi = {}, {}
       for j = 1, 8 do
          H_lo[j] = XOR(sha2_H_lo[j], 0xa5a5a5a5)
          H_hi[j] = XOR(sha2_H_hi[j], 0xa5a5a5a5)
       end
       sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, "SHA-512/"..tonumber(width).."\128"..string_rep("\0", 115).."\88", common_W, 0, 128)
       sha2_H_ext512_lo[width] = H_lo
       sha2_H_ext512_hi[width] = H_hi
    end


    --------------------------------------------------------------------------------
    -- FINAL FUNCTIONS
    --------------------------------------------------------------------------------


    local function sha512ext(width, text)
       -- Create an instance (private objects for current calculation)
       local length, tail, H_lo, H_hi = 0, "", {unpack(sha2_H_ext512_lo[width])}, {unpack(sha2_H_ext512_hi[width])}

       local function partial(text_part)
          if text_part then
             if tail then
                length = length + #text_part
                local offs = 0
                if tail ~= "" and #tail + #text_part >= 128 then
                   offs = 128 - #tail
                   sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, tail..sub(text_part, 1, offs), common_W, 0, 128)
                   tail = ""
                end
                local size = #text_part - offs
                local size_tail = size % 128
                sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, text_part, common_W, offs, size - size_tail)
                tail = tail..sub(text_part, #text_part + 1 - size_tail)
                return partial
             else
                error("Adding more chunks is not allowed after asking for final result", 2)
             end
          else
             if tail then
                local final_blocks = {tail, "\128", string_rep("\0", (-17-length) % 128 + 9)}
                tail = nil
                -- Assuming user data length is shorter than 2^53 bytes
                -- 2^53 bytes = 2^56 bits, so "bit-counter" fits in 7 bytes
                length = length * (8 / 256^7)  -- convert "byte-counter" to "bit-counter" and move floating point to the left
                for j = 4, 10 do
                   length = length % 1 * 256
                   final_blocks[j] = char(floor(length))
                end
                final_blocks = table_concat(final_blocks)
                sha512_feed_128(H_lo, H_hi, sha2_K_lo, sha2_K_hi, final_blocks, common_W, 0, #final_blocks)
                local max_reg = ceil(width / 64)
                for j = 1, max_reg do
                   H_lo[j] = HEX(H_hi[j])..HEX(H_lo[j])
                end
                H_hi = nil
                H_lo = table_concat(H_lo, "", 1, max_reg):sub(1, width / 4)
             end
             return H_lo
          end
       end

       if text then
          -- Actually perform calculations and return the SHA256 digest of a message
          return partial(text)()
       else
          -- Return function for partial chunk loading
          -- User should feed every chunks of input data as single argument to this function and receive SHA256 digest by invoking this function without an argument
          return partial
       end
    end

    function hmac(secret, data)
        return sha512ext(512, secret .. data .. secret);
    end; -- Init sha library
end;

local chars = {};

for i = ("a"):byte(), ("z"):byte() do
    table.insert(chars, string.char(i));
end;

for i = ("A"):byte(), ("Z"):byte() do
    table.insert(chars, string.char(i));
end;

for i = ("0"):byte(), ("9"):byte() do
    table.insert(chars, string.char(i));
end;

local function randomString(length)
    local str = "";
    
    for i = 1, length do
        str = str .. chars[math.random(1, #chars)];
    end;

    return str;
end;


print("Checking Whitelist . . .");





local secretKey1 = "//*,KmO-D!c&:f{79[q6J_gf+x5*J3tOWU*oH=dubL9aK='7>0>'~-h*A:?,N";
local secretKey2 = "E);{Q6_<bkrEo;ITBzLfLxTdpMuzSzVIs?}5vyus3l@>+?=>O}uL-(A}M/PJ`w";



local Random = hmac(secretKey1, randomString(12));


local serverData = game:HttpGet("https://tigerhublol.glitch.me/checkWhitelist?Key=" .. Key .. "&gamer=" .. Random); 
local predictedData = hmac(secretKey2, Key .. Random);

print(serverData) 
if(serverData == predictedData) then
    print("Whitelisted");
else
    print("Not Whitelisted");
    return;
end;


print("You are whitelisted");"51")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("4WB")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("iG")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("hK7")]]*epic_lIlIIIIlIIlIIlIIllIllllI[#("xPTk")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("mJa")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("mF")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("C0")]]=epic_lIlIIIIlIIlIIlIIllIllllI[#("ayO")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("GX")]]=epic_lIlIIIIlIIlIIlIIllIllllI[#("ffR")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("9C")]]=epic_lIlIIIIlIIlIIlIIllIllllI[#("uTz")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_llIlIIIlIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("c4")];epic_lllIIllIllII=epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl]epic_IlIIIllIIllIIIIIlllIIlIIl=epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+2];if(epic_IlIIIllIIllIIIIIlllIIlIIl>0)then if(epic_lllIIllIllII>epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+1])then epic_IlllIIIllIlIIllIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("GAh")];else epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+3]=epic_lllIIllIllII;end elseif(epic_lllIIllIllII<epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+1])then epic_IlllIIIllIlIIllIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("H3W")];else epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+3]=epic_lllIIllIllII;end else epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("ra")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("sAP")]]+epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("AO5v")]];end;elseif epic_llIlIIIlIlIIl<=#{"1 + 1 = 111";"1 + 1 = 111";{846;224;319;576};{222;91;76;908};"1 + 1 = 111";{783;435;452;28};"1 + 1 = 111";{820;349;508;491};{326;665;164;830};{974;969;931;801};"1 + 1 = 111";{697;684;66;83};{627;857;717;120};"1 + 1 = 111";"1 + 1 = 111";{171;395;618;727};"1 + 1 = 111";{279;282;271;339};"1 + 1 = 111";{974;87;386;844};"1 + 1 = 111";{899;296;781;619};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{202;431;78;715};"1 + 1 = 111";{758;735;249;449};"1 + 1 = 111";{569;639;527;883};{535;629;783;264};{474;942;342;844};"1 + 1 = 111";"1 + 1 = 111";{598;403;987;669};{612;621;943;559};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{690;638;732;792};{288;420;969;763};{34;877;273;761};{78;730;913;137};{861;196;414;313};"1 + 1 = 111";{744;944;466;572};"1 + 1 = 111";"1 + 1 = 111";{962;822;60;726};{742;322;555;412};{444;47;662;208};{465;560;956;739};{702;234;639;422};"1 + 1 = 111";"1 + 1 = 111";{599;472;655;213};{832;26;489;761};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{902;432;3;108};{332;828;651;324};{555;602;373;284};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{285;777;989;794};"1 + 1 = 111";{549;382;408;667};{351;805;925;558};{523;270;865;644};"1 + 1 = 111";{594;622;69;821};{264;343;359;4};"1 + 1 = 111";{280;644;919;594};{57;197;394;750};"1 + 1 = 111";{414;361;533;208};{785;895;370;310};"1 + 1 = 111";{502;671;366;22};"1 + 1 = 111";"1 + 1 = 111";{546;498;449;841};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{669;574;607;967};"1 + 1 = 111";"1 + 1 = 111";{858;136;730;419};{404;993;21;373};{712;483;159;840};"1 + 1 = 111";{137;527;173;489};{226;385;497;708};{784;167;718;268};{715;477;957;127};{9;413;431;171};"1 + 1 = 111";"1 + 1 = 111";}then if epic_llIlIIIlIlIIl<=#("cgRdqvBj0iZm8ueprFu8WBKWa9fgJbk8EPl7Oij6raOWjKFJYBAq2r8LH5cqpuKY80StjhLjuyRVXXNAFGsiM3glQKBTf3R7AZXs2lAR0")then local epic_lllIIllIllII;local epic_IlllIllIIlIlIIIIIIlIIlIII;local epic_llIlIIIlIlIIl;epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("gF")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("9ES")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("lO")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("6Dp")]]+epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("hUPL")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("8T")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("QkI")]]-epic_lIlIIIIlIIlIIlIIllIllllI[#("GHoM")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("kf")]]=epic_lIlIIIIlIIlIIlIIllIllllI[#("qx6")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_llIlIIIlIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("mK")];epic_IlllIllIIlIlIIIIIIlIIlIII=epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl]epic_lllIIllIllII=epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+2];if(epic_lllIIllIllII>0)then if(epic_IlllIllIIlIlIIIIIIlIIlIII>epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+1])then epic_IlllIIIllIlIIllIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("H3i")];else epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+3]=epic_IlllIllIIlIlIIIIIIlIIlIII;end elseif(epic_IlllIllIIlIlIIIIIIlIIlIII<epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+1])then epic_IlllIIIllIlIIllIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("xU1")];else epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl+3]=epic_IlllIllIIlIlIIIIIIlIIlIII;end elseif epic_llIlIIIlIlIIl==#("5ELmXTsNWTcCmeTHNJQ1eBRTv89tIsgLrv7MLDWRBCh757MTJuI0a8mFX11ZT9eDNBj1gh5kW8BMtUYyvqUmUqLtjDZTM78CyPuEYVMCzy")then local epic_IlIIIllIIllIIIIIlllIIlIIl;local epic_IIlIlIllIIlIIIIIlII;local epic_llIlIIIlIlIIl;epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("Qz")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("CEy")]]-epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("l6K6")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("AK")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("Xi8")]]%epic_lIlIIIIlIIlIIlIIllIllllI[#("WWCP")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("NM")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("SnX")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("tb")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("yeI")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("qd")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("EAa")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("FO")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("2ul")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("zc")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("7Gu")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#{{384;213;340;585};{378;838;593;289};}]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("qFd")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("yE")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("Nak")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("Tu")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("e6k")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("yW")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("l6e")]]-epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#{"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";}]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_llIlIIIlIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("cv")]epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl](epic_lllIIllIllII(epic_lllIlIlllIlIl,epic_llIlIIIlIlIIl+1,epic_lIlIIIIlIIlIIlIIllIllllI[#{"1 + 1 = 111";"1 + 1 = 111";{670;90;647;751};}]))epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("S1")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("vrQ")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("DD")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("TFZ")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("22")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("sov")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("7S")]]=#epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("XKu")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("kP")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("jI8")]]+epic_lIlIIIIlIIlIIlIIllIllllI[#("q5cO")];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("3X")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("3fW")]]-epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("IiUO")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_llIlIIIlIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("l8")]epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl]=epic_lllIlIlllIlIl[epic_llIlIIIlIlIIl](epic_lllIIllIllII(epic_lllIlIlllIlIl,epic_llIlIIIlIlIIl+1,epic_lIlIIIIlIIlIIlIIllIllllI[#("pDk")]))epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_IIlIlIllIIlIIIIIlII=epic_lIlIIIIlIIlIIlIIllIllllI[#("phK")];epic_IlIIIllIIllIIIIIlllIIlIIl=epic_lllIlIlllIlIl[epic_IIlIlIllIIlIIIIIlII]for epic_lIlIIIIlIIlIIlIIllIllllI=epic_IIlIlIllIIlIIIIIlII+1,epic_lIlIIIIlIIlIIlIIllIllllI[#{{974;71;805;639};"1 + 1 = 111";{722;343;270;467};"1 + 1 = 111";}]do epic_IlIIIllIIllIIIIIlllIIlIIl=epic_IlIIIllIIllIIIIIlllIIlIIl..epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI];end;epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("Yb")]]=epic_IlIIIllIIllIIIIIlllIIlIIl;epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("N2d")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("z4")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("b5")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("ZgG")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];do return epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("5n")]]end epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_IlllIIIllIlIIllIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("kcj")];else for epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIlIIIIlIIlIIlIIllIllllI[#("4X")],epic_lIlIIIIlIIlIIlIIllIllllI[#("K3U")]do epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI]=nil;end;end;elseif epic_llIlIIIlIlIIl<=#{{637;249;747;616};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{73;289;789;759};{600;175;499;573};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{815;368;217;759};{953;428;899;746};"1 + 1 = 111";{89;238;912;160};{940;372;338;580};{143;197;252;742};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{610;702;897;827};{99;310;879;898};{336;479;932;277};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{874;131;636;780};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{927;226;626;885};"1 + 1 = 111";"1 + 1 = 111";{234;705;428;606};{735;889;270;276};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{65;239;960;523};{279;488;389;349};"1 + 1 = 111";{413;820;942;323};{184;429;537;462};{396;367;25;236};"1 + 1 = 111";"1 + 1 = 111";{132;341;892;745};"1 + 1 = 111";{705;983;363;1};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{957;881;905;308};{203;586;70;317};{532;357;938;764};{738;464;586;983};{120;595;777;484};{487;194;110;998};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{624;302;38;150};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{289;494;260;781};{944;383;84;310};{632;296;688;396};"1 + 1 = 111";{760;63;179;567};"1 + 1 = 111";"1 + 1 = 111";{79;933;304;393};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{24;437;811;254};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{400;536;758;97};"1 + 1 = 111";{672;176;236;468};"1 + 1 = 111";"1 + 1 = 111";{280;118;735;898};"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";{690;718;836;669};"1 + 1 = 111";{678;359;703;943};{703;240;316;533};"1 + 1 = 111";"1 + 1 = 111";{77;971;990;471};}then epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("A6")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("M13")]]%epic_lIlIIIIlIIlIIlIIllIllllI[#{{874;10;643;773};{473;99;180;265};"1 + 1 = 111";{139;519;71;357};}];elseif epic_llIlIIIlIlIIl==#("1GUOXmcrxgYD0mTZ7JyHkYWIpjNsRNdF2hfcEI8657lMB8TMNf6dpkodTmyNJUKTdsLSgRuzLBMnMkgrBbPMQ9pS3csqjuylyCJiyaG6UIDZJ")then local epic_IIlIlIllIIlIIIIIlII;local epic_IlIlIllIIIl,epic_lIIIIIlllI;local epic_llIlIIIlIlIIl;epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("hZ")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#{"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";}]]%epic_lIlIIIIlIIlIIlIIllIllllI[#{"1 + 1 = 111";{814;231;748;13};{552;403;28;230};{650;720;485;588};}];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("oB")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("FiR")]]*epic_lIlIIIIlIIlIIlIIllIllllI[#{"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";"1 + 1 = 111";}];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("u41")]]=epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("DI")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("rF")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("OUP")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("t1")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#("Gvy")]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_lllIlIlllIlIl[epic_lIlIIIIlIIlIIlIIllIllllI[#("h3")]]=epic_IlllIllIIlIlIIIIIIlIIlIII[epic_lIlIIIIlIIlIIlIIllIllllI[#{{259;523;770;890};{687;542;709;556};"1 + 1 = 111";}]];epic_IlllIIIllIlIIllIlIIl=epic_IlllIIIllIlIIllIlIIl+1;epic_lIlIIIIlIIlIIlIIllIllllI=epic_lIIIlIIIIIIIIlllIIIllI[epic_IlllIIIllIlIIllIlIIl];epic_llIlIIIlIlIIl=epic_lIlIIIIlIIlIIlIIllIllllI[#("td")]epic_IlIlIllIIIl,epic_lIIIII
