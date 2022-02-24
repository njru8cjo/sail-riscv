
/* 
16-bit ALU Instructions
*/

/* *****************************************************************/
/* ********************* auxiliary functions ***********************/
/* *****************************************************************/
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



/*
 16 bit Shift Instruction
*/


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

val uclip : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), byte) -> bits('n) effect {rreg, wreg}
function uclip (v, m) =
  let ub : bits('n) = ((zeros('n) + 1) << m) - 1 in
  let lb : bits('n) = zeros('n) in
  if ub <_s v then { pext_write_OV (0b1); ub }
  else if v <_s lb then { pext_write_OV (0b1); lb }
  else v

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

val sclip : forall 'n, 'n == 8 | 'n == 16 | 'n == 32.
  (bits('n), byte) -> bits('n) effect {rreg, wreg}
function sclip (v, m) =
  let ub : bits('n) = ((zeros('n) + 1) << m) - 1 in
  let lb : bits('n) = not_vec (ub) in
  if v <_s lb then { pext_write_OV (0b1); lb }
  else if ub <_s v then { pext_write_OV (0b1); ub }
  else v


/* *****************************************************************/



/* ############ */
union clause ast = PEXT_ALU16 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RADD16) <->
  0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, ADD16) <->
  0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KADD16) <->
  0b0001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSUB16) <->
  0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RSUB16) <->
  0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SUB16) <->
  0b0100001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKADD16) <->
  0b0011000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKSUB16) <->
  0b0011001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URADD16) <->
  0b0010000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URSUB16) <->
  0b0010001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, CMPEQ16) <->
  0b0100110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSLL16) <->
  0b0110010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSLRA16) <->
  0b0101011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSLRA16_U) <->
  0b0110011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SCMPLE16) <->
  0b0001110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SCMPLT16) <->
  0b0000110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SLL16) <->
  0b0101010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SMAX16) <->
  0b1000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SMIN16) <->
  0b1000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SRA16) <->
  0b0101000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SRA16_U) <->
  0b0110000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SRL16) <->
  0b0101001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SRL16_U) <->
  0b0110001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UCMPLE16) <->
  0b0011110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UCMPLT16) <->
  0b0010110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UMAX16) <->
  0b1001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UMIN16) <->
  0b1001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_ALU16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let sa4 : byte = 0x0 @ X(rs2)[3..0];
  let sa5 : byte = EXTS(X(rs2)[4..0]);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_16 =  slice (rs1_val, i, 16);
    let rs2_16 =  slice (rs2_val, i, 16);
    result[(i+15)..i] = match op {
      ADD16    => rs1_16 + rs2_16,
      RADD16   => radd(rs1_16,rs2_16),
      URADD16  => uradd(rs1_16,rs2_16),
      KADD16   => kadd(rs1_16,rs2_16), 
      UKADD16  => ukadd(rs1_16,rs2_16),
      SUB16    => rs1_16 - rs2_16,
      RSUB16   => rsub(rs1_16,rs2_16),
      URSUB16  => ursub(rs1_16,rs2_16),
      KSUB16   => ksub(rs1_16,rs2_16),
      UKSUB16  => uksub(rs1_16,rs2_16),
      SLL16    => shift_left_logic(rs1_16, sa4),
      KSLL16   => kshift_left_logic(rs1_16, sa4),
      KSLRA16  => kslra(rs1_16, sa5),
      KSLRA16_U=> kslra_u(rs1_16, sa5),
      SRA16    => shift_right_arith(rs1_16, sa4),
      SRA16_U  => shift_right_arith_u(rs1_16, sa4),
      SRL16    => shift_right_logic(rs1_16, sa4),
      SRL16_U  => shift_right_logic_u(rs1_16, sa4),
      CMPEQ16  => if   rs1_16 == rs2_16 
                  then 0xFFFF 
                  else 0x0000,
      SCMPLT16 => if signed(rs1_16) < signed(rs2_16)
                  then 0xFFFF
                  else 0x0000,
      SCMPLE16 => if signed(rs1_16) <= signed(rs2_16)
                  then 0xFFFF
                  else 0x0000,
      UCMPLT16 => if unsigned(rs1_16) < unsigned(rs2_16)
                  then 0xFFFF
                  else 0x0000,
      UCMPLE16 => if unsigned(rs1_16) <= unsigned(rs2_16)
                  then 0xFFFF
                  else 0x0000,
      SMAX16   => if rs2_16 <_s rs1_16 then rs1_16
                  else rs2_16,
      SMIN16   => if rs1_16 <_s rs2_16 then rs1_16
                  else rs2_16,
      UMAX16   => if rs2_16 <_u rs1_16 then rs1_16
                  else rs2_16,
      UMIN16   => if rs1_16 <_u rs2_16 then rs1_16
                  else rs2_16
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ALU16_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD16    <-> "ADD16",
    RADD16   <-> "RADD16",
    URADD16  <-> "URADD16",
    KADD16   <-> "KADD16",
    UKADD16  <-> "UKADD16",
    SUB16    <-> "SUB16",
    RSUB16   <-> "RSUB16",
    URSUB16  <-> "URSUB16",
    KSUB16   <-> "KSUB16",
    UKSUB16  <-> "UKSUB16",
    SLL16    <-> "SLL16",
    KSLL16   <-> "KSLL16",
    KSLRA16  <-> "KSLRA16",
    KSLRA16_U  <-> "KSLRA16_U",
    SRA16    <-> "SRA16",
    SRA16_U  <-> "SRA16_U",
    SRL16    <-> "SRL16",
    SRL16_U  <-> "SRL16_U",
    CMPEQ16  <-> "CMPEQ16",
    SCMPLT16 <-> "SCMPLT16",
    SCMPLE16 <-> "SCMPLE16",
    UCMPLT16 <-> "UCMPLT16",
    UCMPLE16 <-> "UCMPLE16",
    SMAX16   <-> "SMAX16",
    SMIN16   <-> "SMIN16",
    UMAX16   <-> "UMAX16",
    UMIN16   <-> "UMIN16"
}

mapping clause assembly = PEXT_ALU16(rs2, rs1, rd, p_inst)
  <-> p_ALU16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
 Cross Instruction

*/
union clause ast = PEXT_CROSS_16 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)


mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, CRAS16) <->
  0b0100010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, CRSA16) <->
  0b0100011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KCRAS16) <->
  0b0001010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KCRSA16) <->
  0b0001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KSTAS16) <->
  0b1100010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KSTSA16) <->
  0b1100011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, RCRAS16) <->
  0b0000010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, RCRSA16) <->
  0b0000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, RSTAS16) <->
  0b1011010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, RSTSA16) <->
  0b1011011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, STAS16) <->
  0b1111010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, STSA16) <->
  0b1111011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, UKCRAS16) <->
  0b0011010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, UKCRSA16) <->
  0b0011011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, UKSTAS16) <->
  0b1110010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, UKSTSA16) <->
  0b1110011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, URCRAS16) <->
  0b0010010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, URCRSA16) <->
  0b0010011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, URSTAS16) <->
  0b1101010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, URSTSA16) <->
  0b1101011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, PKBB16) <->
  0b0000111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, PKBT16) <->
  0b0001111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, PKTT16) <->
  0b0010111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, PKTB16) <->
  0b0011111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KHM16) <->
  0b1000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KHMX16) <->
  0b1001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_CROSS_16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_0 =  slice (rs1_val, i, 16);
    let rs1_1 =  slice (rs1_val, i+16, 16);   
    let rs2_0 =  slice (rs2_val, i, 16);
    let rs2_1 =  slice (rs2_val, i+16, 16);
    result[(i+31)..i] = match op {
      CRAS16   => rs1_1 + rs2_0 @ rs1_0 - rs2_1,
      RCRAS16  => radd(rs1_1,rs2_0) @ rsub(rs1_0,rs2_1),
      URCRAS16 => uradd(rs1_1,rs2_0) @ ursub(rs1_0,rs2_1),
      KCRAS16  => kadd(rs1_1,rs2_0) @ ksub(rs1_0,rs2_1),
      UKCRAS16 => ukadd(rs1_1,rs2_0) @ uksub(rs1_0,rs2_1),
      CRSA16   => rs1_1 - rs2_0 @ rs1_0 + rs2_1,
      RCRSA16  => rsub(rs1_1,rs2_0) @ radd(rs1_0,rs2_1),
      URCRSA16 => ursub(rs1_1,rs2_0) @ uradd(rs1_0,rs2_1),
      KCRSA16  => ksub(rs1_1,rs2_0) @ kadd(rs1_0,rs2_1),
      UKCRSA16 => uksub(rs1_1,rs2_0) @ ukadd(rs1_0,rs2_1),
      STAS16   => rs1_1 + rs2_1 @ rs1_0 - rs2_0,
      RSTAS16  => radd(rs1_1,rs2_1) @ rsub(rs1_0,rs2_0),
      URSTAS16 => uradd(rs1_1,rs2_1) @ ursub(rs1_0,rs2_0),
      KSTAS16  => kadd(rs1_1,rs2_1) @ ksub(rs1_0,rs2_0),
      UKSTAS16 => ukadd(rs1_1,rs2_1) @ uksub(rs1_0,rs2_0),
      STSA16   => rs1_1 - rs2_1   @ rs1_0 + rs2_0,
      RSTSA16  => rsub(rs1_1,rs2_1) @ radd(rs1_0,rs2_0),
      URSTSA16 => ursub(rs1_1,rs2_1) @ uradd(rs1_0,rs2_0),
      KSTSA16  => ksub(rs1_1,rs2_1) @ kadd(rs1_0,rs2_0),
      UKSTSA16 => uksub(rs1_1,rs2_1) @ ukadd(rs1_0,rs2_0),
      KHM16    => khm (rs1_1, rs2_1) @ khm (rs1_0, rs2_0), 
      KHMX16   => khm (rs1_1, rs2_0) @ khm (rs1_0, rs2_1),
      PKBB16   => rs1_0 @ rs2_0,
      PKBT16   => rs1_0 @ rs2_1,
      PKTB16   => rs1_1 @ rs2_0,
      PKTT16   => rs1_1 @ rs2_1
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_CROSS_16_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    CRAS16   <-> "CRAS16",
    RCRAS16  <-> "RCRAS16",
    URCRAS16 <-> "URCRAS16",
    KCRAS16  <-> "KCRAS16",
    UKCRAS16 <-> "UKCRAS16",
    CRSA16   <-> "CRSA16",
    RCRSA16  <-> "RCRSA16",
    URCRSA16 <-> "URCRSA16",
    KCRSA16  <-> "KCRSA16",
    UKCRSA16 <-> "UKCRSA16",
    STAS16   <-> "STAS16",
    RSTAS16  <-> "RSTAS16",
    URSTAS16 <-> "URSTAS16",
    KSTAS16  <-> "KSTAS16",
    UKSTAS16 <-> "UKSTAS16",
    STSA16   <-> "STSA16",
    RSTSA16  <-> "RSTSA16",
    URSTSA16 <-> "URSTSA16",
    KSTSA16  <-> "KSTSA16",
    UKSTSA16 <-> "UKSTSA16",
    KHM16  <-> "KHM16",
    KHMX16  <-> "KHMX16",
    PKBB16  <-> "PKBB16",
    PKBT16 <-> "PKBT16",
    PKTB16  <-> "PKTB16",
    PKTT16  <-> "PKTT16"

}

mapping clause assembly = PEXT_CROSS_16(rs2, rs1, rd, p_inst)
  <-> p_CROSS_16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
16bit MUL Instruction
KHM & KHMX write in CROSS AST 
*/

union clause ast = PEXT_MUL_16 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_MUL_16(rs2, rs1, rd, SMUL16) <->
  0b1010000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL_16(rs2, rs1, rd, SMULX16) <->
  0b1010001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL_16(rs2, rs1, rd, UMUL16) <->
  0b1011000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL_16(rs2, rs1, rd, UMULX16) <->
  0b1011001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_MUL_16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_0 =  slice (rs1_val, 0, 16);
  let rs1_1 =  slice (rs1_val, 16, 16);
  let rs2_0 =  slice (rs2_val, 0, 16);
  let rs2_1 =  slice (rs2_val, 16, 16);
  
  if sizeof(xlen) == 32 
  then {
    let rd0 = (rd >> 1) << 1 ;
    let rd1 = rd0 + 1 ;
    result : xlenbits = zeros();
    result1 : xlenbits = zeros();
    Zero : xlenbits = zeros();
    match (op) {
      SMUL16  => { result  =  smul (rs1_0, rs2_0); result1 =  smul (rs1_1, rs2_1)},
      SMULX16 => { result  =  smul (rs1_0, rs2_1); result1 =  smul (rs1_1, rs2_0)},
      UMUL16  => { result  =  umul (rs1_0, rs2_0); result1 =  umul (rs1_1, rs2_1)},
      UMULX16 => { result  =  umul (rs1_0, rs2_1); result1 =  umul (rs1_1, rs2_0)}
      };
    X(rd0) = result;
    X(rd1) = result1;
    RETIRE_SUCCESS
  }
  else  {
    result : xlenbits = zeros();
    result = match (op) {
      SMUL16  =>   smul(rs1_1, rs2_1) @ smul(rs1_0, rs2_0),
      SMULX16 =>   smul(rs1_1, rs2_0) @ smul(rs1_0, rs2_1),
      UMUL16  =>   umul(rs1_1, rs2_1) @ umul(rs1_0, rs2_0),
      UMULX16 =>   umul(rs1_1, rs2_0) @ umul(rs1_0, rs2_1)
    };
    X(rd) = result;
    RETIRE_SUCCESS
  }
  
}

mapping p_MUL_16_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMUL16   <-> "SMUL16",
    SMULX16  <-> "SMULX16",
    UMUL16   <-> "UMUL16",
    UMULX16  <-> "UMULX16"
}

mapping clause assembly = PEXT_MUL_16(rs2, rs1, rd, p_inst)
  <-> p_MUL_16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)





/*
  4bit Immediate instruction
*/



union clause ast = P_INST_IMM4_RS1_RD : (bits(4), regidx, regidx, p_inst_imm4_rs1_rd_op)
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, KSLLI16) <->
  0b0111010 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SCLIP16) <->
  0b1000010 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SLLI16) <->
  0b0111010 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SRAI16) <->
  0b0111000 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SRAI16_U) <->
  0b0111000 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SRLI16) <->
  0b0111001 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, SRLI16_U) <->
  0b0111001 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM4_RS1_RD(imm4, rs1, rd, UCLIP16) <->
  0b1000010 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (P_INST_IMM4_RS1_RD(imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : byte = EXTZ(imm4);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_16 =  slice (rs1_val, i, 16);
    

    result[(i+15)..i] = match op {
      KSLLI16    =>  kshift_left_logic(rs1_16, sa),
      SCLIP16    =>  sclip(rs1_16, sa),
      SLLI16    =>  shift_left_logic(rs1_16, sa),
      SRAI16    =>  shift_right_arith(rs1_16, sa),
      SRAI16_U    =>  shift_right_arith_u(rs1_16, sa),
      SRLI16    =>  shift_right_logic(rs1_16, sa),
      SRLI16_U    =>  shift_right_logic_u(rs1_16, sa),
      UCLIP16    =>  uclip(rs1_16, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_imm4_rs1_rd_mapping : p_inst_imm4_rs1_rd_op <-> string = {
  KSLLI16 <-> "KSLLI16",
  SCLIP16 <-> "SCLIP16",
  SLLI16  <-> "SLLI16",
  SRAI16  <-> "SRAI16",
  SRAI16_U <-> "SRAI16_U",
  SRLI16 <-> "SRLI16",
  SRLI16_U <-> "SRLI16_U",
  UCLIP16 <-> "UCLIP16"
}

mapping clause assembly = P_INST_IMM4_RS1_RD(imm4, rs1, rd, p_inst)
  <-> p_inst_imm4_rs1_rd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)




