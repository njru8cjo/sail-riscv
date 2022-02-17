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
val radd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function radd (v1, v2) =
  let v1ext : bits(64) = EXTS(v1) in
  let v2ext : bits(64) = EXTS(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val uradd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function uradd (v1, v2) =
  let v1ext : bits(64) = EXTZ(v1) in
  let v2ext : bits(64) = EXTZ(v2) in
  slice ((v1ext + v2ext) >> 1, 0, 'n)

val kadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function kadd (v1, v2) =
  let ub : bits(64) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(64) = not_vec (ub) in
  let v1ext : bits(64) = EXTS(v1) in
  let v2ext : bits(64) = EXTS(v2) in
  let sumext = v1ext + v2ext in
  if sumext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s sumext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (sumext, 0, 'n) }

val ukadd : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function ukadd (v1, v2) =
  let ub : bits(64) = EXTZ(sail_ones ('n)) in
  let v1ext : bits(64) = EXTZ(v1) in
  let v2ext : bits(64) = EXTZ(v2) in
  let sumext = v1ext + v2ext in
  if ub <_u sumext then { pext_write_OV (0b1); ones('n) }
  else { slice (sumext, 0, 'n) }

/* sub auxiliary functions */
val rsub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function rsub (v1, v2) =
  let v1ext : bits(64) = EXTS(v1) in
  let v2ext : bits(64) = EXTS(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

val ursub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n)
function ursub (v1, v2) =
  let v1ext : bits(64) = EXTZ(v1) in
  let v2ext : bits(64) = EXTZ(v2) in
  slice ((v1ext - v2ext) >> 1, 0, 'n)

val ksub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function ksub (v1, v2) =
  let ub : bits(64) = EXTS(sail_ones ('n) >> 1) in
  let lb : bits(64) = not_vec (ub) in
  let v1ext : bits(64) = EXTS(v1) in
  let v2ext : bits(64) = EXTS(v2) in
  let diffext = v1ext - v2ext in
  if diffext <_s lb then { pext_write_OV (0b1); not_vec (ones ('n) >> 1) }
  else if ub <_s diffext then { pext_write_OV (0b1); ones ('n) >> 1 }
  else { slice (diffext, 0, 'n) }


val uksub : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), bits('n)) -> bits('n) effect {rreg,wreg}
function uksub (v1, v2) =
  let ub : bits(64) = EXTZ(sail_ones ('n)) in
  let v1ext : bits(64) = EXTZ(v1) in
  let v2ext : bits(64) = EXTZ(v2) in
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
val smax : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function smax (v, m) =
  if signed(v) < signed(m)
  then m
  else v

val smin : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function smin (v, m) =
  if signed(v) < signed(m)
  then v
  else m

val umax : forall 'n, 'n == 8 | 'n == 16.
  (bits('n), bits('n)) -> bits('n) effect {rreg, wreg}
function umax (v, m) =
  if unsigned(v) < unsigned(m)
  then m
  else v

val umin : forall 'n, 'n == 8 | 'n == 16.
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