/* Programming Langauge Lab, Department of Computer Science, National Tsing-Hua University, Taiwan */
/* Academia Sinica, Taiwan*/
/* Andes Technology Corporation*/

/* *****************************************************************/
/* This file specifies the instruction added by the 'P' extension. */
/* *****************************************************************/

/* *****************************************************************/
/************************ additional types *************************/
/* *****************************************************************/

type byte = bits(8)
type dword = bits(64)

let PEXT_SIG = 0b1110111

/* *****************************************************************/
/* ************************* shorthands ****************************/
/* *****************************************************************/

val rB : forall 'sidx,
  (0 <= 'sidx & 'sidx < xlen_bytes).
  (regidx, int('sidx)) -> byte effect {escape, rreg}

function rB (ridx, sidx) = slice (X(ridx), 8 * sidx, 8)

val rH : forall 'sidx,
  (0 <= 'sidx & 2 * 'sidx < xlen_bytes).
  (regidx, int('sidx)) -> half effect {escape, rreg}

function rH (ridx, sidx) = slice (X(ridx), sidx * 16, 16)

val rW : forall 'sidx,
  (0 <= 'sidx & 4 * 'sidx < xlen_bytes).
  (regidx, int('sidx)) -> word effect {escape, rreg}

function rW (ridx, sidx) = slice (X(ridx), sidx * 32, 32)

val rD : regidx -> dword effect {escape, rreg}

function rD (ridx) =
  if sizeof (xlen) == 32 then
    X(ridx | 0b00001) @ X(ridx & 0b11110)
  else
    X(ridx)

val set_rD : (regidx, bits (64)) -> unit effect {escape, wreg}

function set_rD (ridx, value) =
  if sizeof (xlen) == 32 then
    { X(ridx & 0b11110) = slice (value,  0, 32);
      X(ridx | 0b00001) = slice (value, 32, 32) }
  else
    X(ridx) = value

mapping pext_width_mnemonic : word_width <-> string = {
    BYTE <->  "8",
    HALF <-> "16",
    WORD <-> "32",
  DOUBLE <-> "64"
}

/* *****************************************************************/
/* ********************* auxiliary functions ***********************/
/* *****************************************************************/

/* add auxiliary functions */
val radd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function radd (v1, v2) =
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val uradd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function uradd (v1, v2) =
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val kadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function kadd (v1, v2) =
  let ub : bits(66) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  let sumext = v1ext + v2ext in
  if sumext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s sumext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (sumext, 0, 'n) }

val ukadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function ukadd (v1, v2) =
  let ub : bits(66) = EXTZ(sail_ones ('n)) in
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  let sumext = v1ext + v2ext in
  if ub <_u sumext then { pext_write_OV (0b1); ones('n) }
  else { slice (sumext, 0, 'n) }

/* sub auxiliary functions */
val rsub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function rsub (v1, v2) =
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

val ursub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n)
function ursub (v1, v2) =
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

val ksub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function ksub (v1, v2) =
  let ub : bits(66) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(66) = not_vec (ub) in
  let v1ext : bits(66) = EXTS(v1) in
  let v2ext : bits(66) = EXTS(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s diffext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (diffext, 0, 'n) }


val uksub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function uksub (v1, v2) =
  let ub : bits(66) = EXTZ(sail_ones ('n)) in
  let v1ext : bits(66) = EXTZ(v1) in
  let v2ext : bits(66) = EXTZ(v2) in
  let diffext = v1ext - v2ext in
  if ub <_u diffext then { pext_write_OV (0b1); zeros('n) }
  else { slice (diffext, 0, 'n) }

/* mul auxiliary functions */ 
val smul : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function smul (v1, v2) =
  to_bits (2 * 'n, signed(v1) * signed(v2))

val umul : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits(2 * 'n)
function umul (v1, v2) =
  to_bits (2 * 'n, unsigned(v1) * unsigned(v2))

val khm : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function khm (v1, v2) =
  let lb : bits('n) = not_vec(EXTS(sail_ones ('n) >> 1)) in
  if v1 == lb & v2 == lb then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { if 'n == 8 then { to_bits (2 * 'n, signed(v1) * signed(v2))[14..7] }
         else { to_bits (2 * 'n, signed(v1) * signed(v2))[30..15] } }

val umul33_64 :
  (bits(33), bits(33)) -> bits(64)
function umul33_64 (v1, v2) =
  to_bits (66, unsigned(v1) * unsigned(v2))[63..0]

val mul32_64 :
  (bits(32), bits(32)) -> bits(64)
function mul32_64 (v1, v2) =
  to_bits (64, signed(v1) * signed(v2))

val mulb :
  (bits(32), bits(32)) -> bits(32)
function mulb (v1, v2) =
  to_bits (64, unsigned(v1) * unsigned(v2))[31..0]

/* shift auxiliary functions */ 
val shift_right_arith : forall 'n, 'n == 8 | 'n == 9 | 'n == 16 | 'n == 17 | 'n == 32 | 'n == 33 | 'n == 64.
  (bits ('n), byte) -> bits ('n)
function shift_right_arith (v, m) =
  let extv : bits(xlen + 65) = EXTS (v) in
  slice (extv >> m, 0, 'n)

val shift_right_arith_u : forall 'n, 'n == 8 | 'n == 16 | 'n == 32 | 'n == 64.
  (bits ('n), byte) -> bits ('n)
function shift_right_arith_u (v, m) =
  if m == 0x00 then v
  else let res : bits(65) = add_bits(EXTS(shift_right_arith(v, m - 0x01)), EXTZ(0b1)) in
  slice(res >> 1, 0, 'n)

val shift_right_logic : forall 'n, 'n == 8 | 'n == 9 | 'n == 16 | 'n == 17 | 'n == 32 | 'n == 33 | 'n == 64.
  (bits ('n), byte) -> bits ('n)
function shift_right_logic (v, m) =
  let extv : bits(xlen + 65) = EXTZ (v) in
  slice (extv >> m, 0, 'n)

val shift_right_logic_u : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), byte) -> bits ('n)
function shift_right_logic_u (v, m) =
  if m == 0x00 then v
  else let res : bits(65) = add_bits(EXTZ(shift_right_logic(v, m - 0x01)), EXTZ(0b1)) in slice(res >> 1, 0, 'n)

val shift_left_logic : forall 'n, 'n == 8 | 'n == 9 | 'n == 16 | 'n == 17 | 'n == 32 | 'n == 33.
  (bits ('n), byte) -> bits ('n)
function shift_left_logic (v, m) =
  let extv : bits(xlen + 32) = EXTZ (v) in
  slice (extv << m, 0, 'n)

val kshift_left_logic : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), byte) -> bits ('n) effect {rreg,wreg}
function kshift_left_logic (v, m) =
  let ub : bits(xlen + 32) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(xlen + 32) = not_vec (ub) in
  let vext : bits(xlen + 32) = EXTS(v) in
  let shiftext : bits(xlen + 32) = vext << m in
  if shiftext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s shiftext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (shiftext, 0, 'n) }

val kslra : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), byte) -> bits ('n) effect {rreg,wreg}
function kslra (v, m) =
  let rev : byte = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  let sa : byte = if rev == to_bits(8, 'n) then to_bits(8, 'n) - 0x01 else rev in
  if m <_s 0x00 then shift_right_arith(v, sa)
  else kshift_left_logic(v, sa)

val kslra_u : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits ('n), byte) -> bits ('n) effect {rreg,wreg}
function kslra_u (v, m) =
  let rev : byte = if m <_s 0x00 then not_vec (m) + 0x01 else m in
  let sa : byte = if rev == to_bits(8, 'n) then to_bits(8, 'n) - 0x01 else rev in
  if m <_s 0x00 then shift_right_arith_u(v, sa)
  else kshift_left_logic(v, sa)

/* cmp auxiliary functions */
val cmpeq : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function cmpeq (v, m) =
  if v == m
  then ones('n)
  else zeros('n)

val scmple : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function scmple (v, m) =
  if signed(v) <= signed(m)
  then ones('n)
  else zeros('n)

val scmplt : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function scmplt (v, m) =
  if signed(v) < signed(m)
  then ones('n)
  else zeros('n)

val ucmple : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function ucmple (v, m) =
  if unsigned(v) <= unsigned(m)
  then ones('n)
  else zeros('n)

val ucmplt : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function ucmplt (v, m) =
  if unsigned(v) < unsigned(m)
  then ones('n)
  else zeros('n)

/* misc auxiliary functions */
val smax : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function smax (v, m) =
  if signed(v) < signed(m)
  then m
  else v

val smin : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function smin (v, m) =
  if signed(v) < signed(m)
  then v
  else m

val umax : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function umax (v, m) =
  if unsigned(v) < unsigned(m)
  then m
  else v

val umin : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function umin (v, m) =
  if unsigned(v) < unsigned(m)
  then v
  else m

val sclip : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), byte) -> bits('n) effect {rreg, wreg}
function sclip (v, m) =
  let ub : bits('n) = ((zeros('n) + 1) << m) - 1 in
  let lb : bits('n) = not_vec (ub) in
  if v <_s lb then { pext_write_OV (0b1); lb }
  else if ub <_s v then { pext_write_OV (0b1); ub }
  else v

val uclip : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), byte) -> bits('n) effect {rreg, wreg}
function uclip (v, m) =
  let ub : bits('n) = ((zeros('n) + 1) << m) - 1 in
  let lb : bits('n) = zeros('n) in
  if ub <_s v then { pext_write_OV (0b1); ub }
  else if v <_s lb then { pext_write_OV (0b1); lb }
  else v

val kabs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n) effect {rreg, wreg}
function kabs (v) =
  let lb : bits('n) = not_vec( sail_ones ('n) >> 1) in
  if v == lb then { pext_write_OV (0b1); not_vec(lb) }
  else if v <_s zeros('n) then { pext_write_OV (0b1); not_vec(v) + 1 }
  else v

val clrs : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n)
function clrs (v) = {
  var vpos : bits(32) = if v <_s zeros('n) then not_vec(EXTS(v)) else EXTZ(v);
  if vpos == zeros(32) then to_bits('n, 'n - 1)
  else {
  var cnt : bits('n) = zeros('n);
  if vpos[31..16] == 0x0000 then { cnt = cnt + 16; vpos = vpos << 16 };
  if vpos[31..24] == 0x00   then { cnt = cnt + 8;  vpos = vpos << 8 };
  if vpos[31..28] == 0x0    then { cnt = cnt + 4;  vpos = vpos << 4 };
  if vpos[31..30] == 0b00   then { cnt = cnt + 2;  vpos = vpos << 2 };
  if vpos[31..31] == 0b0    then { cnt = cnt + 1 };
  cnt = cnt + 'n - 33; cnt } }

val clz : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n)
function clz (v) = {
  var vext : bits(32) = EXTZ(v);
  if vext == zeros(32) then to_bits('n, 'n)
  else {
  var cnt : bits('n) = zeros('n);
  if vext[31..16] == 0x0000 then { cnt = cnt + 16; vext = vext << 16 };
  if vext[31..24] == 0x00   then { cnt = cnt + 8;  vext = vext << 8 };
  if vext[31..28] == 0x0    then { cnt = cnt + 4;  vext = vext << 4 };
  if vext[31..30] == 0b00   then { cnt = cnt + 2;  vext = vext << 2 };
  if vext[31..31] == 0b0    then { cnt = cnt + 1 };
  cnt = cnt + 'n - 32; cnt } }

val clo : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n)) -> bits('n)
function clo (v) = {
  var vcpl : bits(32) = not_vec(EXTZ(not_vec(v)));
  if vcpl == ones(32) then to_bits('n, 'n)
  else {
  var cnt : bits('n) = zeros('n);
  if vcpl[31..16] == 0xFFFF then { cnt = cnt + 16; vcpl = vcpl << 16 };
  if vcpl[31..24] == 0xFF   then { cnt = cnt + 8;  vcpl = vcpl << 8 };
  if vcpl[31..28] == 0xF    then { cnt = cnt + 4;  vcpl = vcpl << 4 };
  if vcpl[31..30] == 0b11   then { cnt = cnt + 2;  vcpl = vcpl << 2 };
  if vcpl[31..31] == 0b1    then { cnt = cnt + 1 };
  cnt = cnt + 'n - 32; cnt } }

/* q15 auxiliary functions */
val q15 : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15 (v) =
  let ub : bits(33) = EXTS(0x7FFF) in
  let lb : bits(33) = EXTS(0x8000) in
  if v <_s lb then { pext_write_OV (0b1); 0x8000;}
  else if ub <_s v then { pext_write_OV (0b1); 0x7FFF;}
  else v[15..0]

val q15_l_u : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15_l_u (v) =
  let ub : bits(33) = EXTZ(0xFFFF) in
  if ub <_u v then { pext_write_OV (0b1); 0xFFFF;}
  else v[15..0]

val q15_s_u : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15_s_u (v) =
  let ub : bits(33) = EXTZ(0xFFFF) in
  let lb : bits(33) = EXTZ(0x0000) in
  if ub <_s v then { pext_write_OV (0b1); 0xFFFF;}
  else if v <_s lb then { pext_write_OV (0b1); 0x0000;}
  else v[15..0]
  
val sshm :
  (bits(16), bits(16)) -> bits(16) effect {rreg, wreg}
function sshm (v1, v2)=
  if (v1 != 0x8000) | (v2 != 0x8000)
  then 
  let res : bits(32) = to_bits(32, signed(v1) * signed(v2)) in
  let rshift : bits(32) = EXTS(res >> 15) in 
  rshift[15..0]
  else { pext_write_OV (0b1); 0x7FFF;}

/* q31 auxiliary functions */
val kdm :
  (bits(16), bits(16)) -> bits(32) effect {rreg,wreg}
function kdm (v1, v2) =
  let lb : bits(16) = not_vec(EXTS(sail_ones (16) >> 1)) in
  if v1 == lb & v2 == lb then { pext_write_OV (0b1); ones (32) >> 1 }
  else { to_bits (31, signed(v1) * signed(v2)) @ 0b0 }

val kdmaw :
  (bits(16), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kdmaw (v1, v2, rd) = {
  let resQ31 : bits(32) = kdm(v1, v2);
  let tmp : bits(33) = EXTS(resQ31) + EXTS(rd);
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if tmp <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s tmp then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice (tmp, 0, 32) }
}

/* bit reverse auxiliary functions */
val bitrev32 :
  (bits(32)) -> bits(32)
function bitrev32 (v) = {
  var tmp : bits(64) = 0x0000 @ v @ 0x0000;
  tmp = 0x0000 @ ((tmp[48..17] & 0x55555555) | (tmp[46..15] & 0xAAAAAAAA)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[49..18] & 0x33333333) | (tmp[45..14] & 0xCCCCCCCC)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[51..20] & 0x0F0F0F0F) | (tmp[43..12] & 0xF0F0F0F0)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[55..24] & 0x00FF00FF) | (tmp[39..8]  & 0xFF00FF00)) @ 0x0000;
  ((tmp[63..32] & 0x0000FFFF) | (tmp[31..0]  & 0xFFFF0000))
}

val bitrev64 :
  (bits(64)) -> bits(64)
function bitrev64 (v) = {
  var tmp : bits(128) = 0x00000000 @ v @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[96..33]  & 0x5555555555555555) | (tmp[94..31] & 0xAAAAAAAAAAAAAAAA)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[97..34]  & 0x3333333333333333) | (tmp[93..30] & 0xCCCCCCCCCCCCCCCC)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[99..36]  & 0x0F0F0F0F0F0F0F0F) | (tmp[91..28] & 0xF0F0F0F0F0F0F0F0)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[103..40] & 0x00FF00FF00FF00FF) | (tmp[87..24] & 0xFF00FF00FF00FF00)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[111..48] & 0x0000FFFF0000FFFF) | (tmp[79..16] & 0xFFFF0000FFFF0000)) @ 0x00000000;
  ((tmp[127..64] & 0x00000000FFFFFFFF) | (tmp[63..0]  & 0xFFFFFFFF00000000))
}

/* insb auxiliary functions */
val insb :
  (byte, byte, bits(64)) -> bits(64)
function insb (vbyte, vbpos, vrd) = {
  let insbyte : bits(64) = (0x00000000000000 @ vbyte) << (vbpos << 3);
  let mask : bits(64) = not_vec((0x00000000000000FF) << (vbpos << 3));
  (vrd & mask) + insbyte
}

/* msb mul add auxiliary function */
val msbsmul :
  (bits(32), bits(32)) -> bits(32)
function msbsmul (v1, v2) =
  to_bits (64, signed(v1) * signed(v2))[63..32]

val msbsmul_u :
  (bits(32), bits(32)) -> bits(32)
function msbsmul_u (v1, v2) =
  add_bits(to_bits (64, signed(v1) * signed(v2))[63..31] , 0x00000000 @ 0b1)[32..1]

val kmsbmac :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbmac (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = add_bits(EXTS(msbsmul(v1, v2)), EXTS(rd)) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmsbmac_u :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbmac_u (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = add_bits(EXTS(msbsmul_u(v1, v2)), EXTS(rd)) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmsbsb :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbsb (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = sub_bits(EXTS(rd), EXTS(msbsmul(v1, v2))) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmsbsb_u :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbsb_u (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = sub_bits(EXTS(rd), EXTS(msbsmul_u(v1, v2))) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kwmsbmul :
  (bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kwmsbmul (v1, v2) =
  if (v1 != 0x80000000) | (v2 != 0x80000000)
  then smul(v1, v2)[62..31]
  else { pext_write_OV (0b1); 0x7FFFFFFF }

val kwmsbmul_u :
  (bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kwmsbmul_u (v1, v2) =
  if (v1 != 0x80000000) | (v2 != 0x80000000)
  then
  let mres : bits(64) = smul(v1, v2) in
  let round33 : bits(34) = add_bits(mres[63..30], EXTZ(0x1)) in
  round33[32..1]
  else { pext_write_OV (0b1); 0x7FFFFFFF }

val smmw :
  (bits(32), bits(16)) -> bits(32)
function smmw (v1, v2) =
  to_bits (48, signed(v1) * signed(v2))[47..16]

val smmw_u :
  (bits(32), bits(16)) -> bits(32)
function smmw_u (v1, v2) =
  add_bits(to_bits (48, signed(v1) * signed(v2))[47..15] , EXTZ(0x1))[32..1]

val kmmaw :
  (bits(32), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kmmaw (v1, v2, rd) =
  let mres : bits(48) = to_bits(48, signed(v1) * signed(v2)) in
  let res : bits(33) = add_bits(EXTS(rd), EXTS(mres[47..16])) in
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmmaw_u :
  (bits(32), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kmmaw_u (v1, v2, rd) =
  let mres : bits(48) = to_bits(48, signed(v1) * signed(v2)) in
  let round33 : bits(33) = add_bits(mres[47..15], EXTS(0x1)) in
  let res : bits(33) = add_bits(EXTS(rd), EXTS(round33[32..1])) in
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmmaw2 :
  (bits(32), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kmmaw2 (v1, v2, rd) =
  let addop : bits(32) =
  if (v1 != 0x80000000) | (v2 != 0x8000)
  then to_bits(48, signed(v1) * signed(v2))[46..15]
  else {pext_write_OV (0b1); 0x7FFFFFFF} in
  let res : bits(33) = add_bits(EXTS(rd), EXTS(addop)) in
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmmaw2_u :
  (bits(32), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kmmaw2_u (v1, v2, rd) =
  let round34 : bits(34) = add_bits(to_bits(48, signed(v1) * signed(v2))[47..14], EXTS(0x1)) in
  let addop : bits(32) =
  if (v1 != 0x80000000) | (v2 != 0x8000)
  then round34[32..1]
  else {pext_write_OV (0b1); 0x7FFFFFFF} in
  let res : bits(33) = add_bits(EXTS(rd), EXTS(addop)) in
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice(res, 0, 32) }

val kmmw2 :
  (bits(32), bits(16)) -> bits(32) effect {rreg,wreg}
function kmmw2 (v1, v2) =
  if (v1 == 0x80000000) & (v2 == 0x8000)
  then { pext_write_OV (0b1); 0x7FFFFFFF }
  else to_bits(48, signed(v1) * signed(v2))[46..15]

val kmmw2_u :
  (bits(32), bits(16)) -> bits(32) effect {rreg,wreg}
function kmmw2_u (v1, v2) =
  if (v1 == 0x80000000) & (v2 == 0x8000)
  then { pext_write_OV (0b1); 0x7FFFFFFF }
  else
  let round : bits(33) = add_bits( to_bits(48, signed(v1) * signed(v2))[46..14], EXTS(0x1)) in
  round[32..1]

/* 16 * 32 mul add auxility function */
val kmda : forall 'n, 'n == 16 | 'n == 32.
  (bits ('n), bits ('n), bits ('n), bits ('n)) -> bits ('n + 'n)
  effect {rreg,wreg}
function kmda (a, b, c, d) =
  let lb : bits ('n) = if 'n == 16 then 0x8000 else 0x80000000 in
  if (a == lb & b == lb & c == lb & d == lb) then {
    pext_write_OV (0b1);
    sail_ones (2 * 'n) >> 1
  } else
    let ab = to_bits (2 * 'n, signed (a) * signed (b)) in
    let cd = to_bits (2 * 'n, signed (c) * signed (d)) in
    ab + cd

val kmada : forall 'n, 'n == 16 | 'n == 32.
  (bits(2 * 'n), bits ('n), bits ('n), bits ('n), bits ('n)) -> bits (2 * 'n)
  effect {rreg,wreg}
function kmada (rd, rs11, rs21, rs10, rs20) =
  let lb : bits(66) = not_vec(EXTS(sail_ones (2 * 'n) >> 1)) in
  let ub : bits(66) = EXTS(sail_ones (2 * 'n) >> 1) in
  let res : bits(66) = EXTS(rd) + EXTS(smul(rs11, rs21)) + EXTS(smul(rs10, rs20)) in
  if res <_s lb then { pext_write_OV (0b1); slice(lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice(ub, 0, 2 * 'n) }
  else { slice(res, 0, 2 * 'n) }

val kmads : forall 'n, 'n == 16 | 'n == 32.
  (bits(2 * 'n), bits ('n), bits ('n), bits ('n), bits ('n)) -> bits (2 * 'n)
  effect {rreg,wreg}
function kmads (rd, rs11, rs21, rs10, rs20) =
  let lb : bits(66) = not_vec(EXTS(sail_ones (2 * 'n) >> 1)) in
  let ub : bits(66) = EXTS(sail_ones (2 * 'n) >> 1) in
  let res : bits(66) = EXTS(rd) + EXTS(smul(rs11, rs21)) - EXTS(smul(rs10, rs20)) in
  if res <_s lb then { pext_write_OV (0b1); slice(lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice(ub, 0, 2 * 'n) }
  else { slice(res, 0, 2 * 'n) }

val kmsda : forall 'n, 'n == 16 | 'n == 32.
  (bits(2 * 'n), bits ('n), bits ('n), bits ('n), bits ('n)) -> bits (2 * 'n)
  effect {rreg,wreg}
function kmsda (rd, rs11, rs21, rs10, rs20) =
  let lb : bits(66) = not_vec(EXTS(sail_ones (2 * 'n) >> 1)) in
  let ub : bits(66) = EXTS(sail_ones (2 * 'n) >> 1) in
  let res : bits(66) = EXTS(rd) - EXTS(smul(rs11, rs21)) - EXTS(smul(rs10, rs20)) in
  if res <_s lb then { pext_write_OV (0b1); slice(lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice(ub, 0, 2 * 'n) }
  else { slice(res, 0, 2 * 'n) }

val sumul : forall 'n, 'n == 8.
  (bits('n), bits('n)) -> bits(32)
function sumul (v1, v2) =
  to_bits (32, signed(v1) * signed(0b0 @ v2))
