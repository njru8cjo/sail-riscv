/* 
16-bit Addition & Subtraction Instructions
*/
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




union clause ast = PEXT_ALU16 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RADD16) <->
  0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, ADD16) <->
  0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, CRAS16) <->
  0b0100010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, CRSA16) <->
  0b0100011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KADD16) <->
  0b0001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KCRAS16) <->
  0b0001010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KCRSA16) <->
  0b0001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSTAS16) <->
  0b1100010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSTSA16) <->
  0b1100011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, KSUB16) <->
  0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RCRAS16) <->
  0b0000010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RCRSA16) <->
  0b0000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RSTAS16) <->
  0b1011010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RSTSA16) <->
  0b1011011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, RSUB16) <->
  0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, STAS16) <->
  0b1111010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, STSA16) <->
  0b1111011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, SUB16) <->
  0b0100001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKADD16) <->
  0b0011000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKCRAS16) <->
  0b0011010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKCRSA16) <->
  0b0011011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKSTAS16) <->
  0b1110010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKSTSA16) <->
  0b1110011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, UKSUB16) <->
  0b0011001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URADD16) <->
  0b0010000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URCRAS16) <->
  0b0010010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URCRSA16) <->
  0b0010011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URSTAS16) <->
  0b1101010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URSTSA16) <->
  0b1101011 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU16(rs2, rs1, rd, URSUB16) <->
  0b0010001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_ALU16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_byte =  slice (rs1_val, i, 16);   
    let rs2_byte =  slice (rs2_val, i, 16);  
    result[(i+15)..i] = match op {
      ADD16  => rs1_byte+rs2_byte,
      RADD16 => radd(rs1_byte,rs2_byte),
      URADD16 => uradd(rs1_byte,rs2_byte),
      KADD16 => kadd(rs1_byte,rs2_byte), 
      UKADD16 => ukadd(rs1_byte,rs2_byte),
      SUB16  => rs1_byte-rs2_byte,
      RSUB16 => rsub(rs1_byte,rs2_byte),
      URSUB16 => ursub(rs1_byte,rs2_byte),
      KSUB16 => ksub(rs1_byte,rs2_byte),
      UKSUB16 => uksub(rs1_byte,rs2_byte),
      CRSA16 => uksub(rs1_byte,rs2_byte),

    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_rs2_rs1_rd_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    RADD16 <-> "RADD16"

}

mapping clause assembly = PEXT_ALU16(rs2, rs1, rd, p_inst)
  <-> p_inst_rs2_rs1_rd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)