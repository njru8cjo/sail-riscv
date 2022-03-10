
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
  else { slice (res, 0, 32) }

val kmsbmac_u :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbmac_u (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = add_bits(EXTS(msbsmul_u(v1, v2)), EXTS(rd)) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice (res, 0, 32) }

val kmsbsb :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbsb (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = sub_bits(EXTS(rd), EXTS(msbsmul(v1, v2))) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice (res, 0, 32) }

val kmsbsb_u :
  (bits (32), bits (32), bits (32)) -> bits (32) effect {rreg,wreg}
function kmsbsb_u (v1, v2, rd) =
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  let res : bits(33) = sub_bits(EXTS(rd), EXTS(msbsmul_u(v1, v2))) in
  if res <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s res then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice (res, 0, 32) }

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
  else { slice (res, 0, 32) }

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
  else { slice (res, 0, 32) }

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
  else { slice (res, 0, 32) }

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
  else { slice (res, 0, 32) }

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


/*
Most Significant Word “32x32” Multiply & Add Instructions
*/
union clause ast = PEXT_32_32_MUL_ADD : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, SMMUL) <->
  0b0100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, SMMUL_U) <->
  0b0101000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KMMAC) <->
  0b0110000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KMMAC_U) <->
  0b0111000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KMMSB) <->
  0b0100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KMMSB_U) <->
  0b0101001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KWMMUL) <->
  0b0110001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_32_MUL_ADD(rs2, rs1, rd, KWMMUL_U) <->
  0b0111001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111


function clause execute (PEXT_32_32_MUL_ADD(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val  = X(rd);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_32 =  slice (rs1_val, i, 32);
    let rs2_32 =  slice (rs2_val, i, 32);
    let rd_32  =  slice (rd_val, i, 32);
    result[(i+31)..i] = match op {
      SMMUL    => msbsmul(rs1_32, rs2_32),
      SMMUL_U  => msbsmul_u(rs1_32, rs2_32),
      KMMAC    => kmsbmac(rs1_32, rs2_32, rd_32),
      KMMAC_U    => kmsbmac_u(rs1_32, rs2_32, rd_32),
      KMMSB    => kmsbsb(rs1_32, rs2_32, rd_32),
      KMMSB_U  => kmsbsb_u(rs1_32, rs2_32, rd_32),
      KWMMUL   => kwmsbmul(rs1_32, rs2_32 ),
      KWMMUL_U => kwmsbmul_u(rs1_32, rs2_32)

    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_32_32_muladd_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMMUL    <-> "SMMUL",
    SMMUL_U   <-> "SMMUL_U",
    KMMAC  <-> "KMMAC",
    KMMAC_U   <-> "KMMAC_U",
    KMMSB  <-> "KMMSB",
    KMMSB_U    <-> "KMMSB_U",
    KWMMUL   <-> "KWMMUL",
    KWMMUL_U  <-> "KWMMUL_U"
}

mapping clause assembly = PEXT_32_32_MUL_ADD(rs2, rs1, rd, p_inst)
  <-> p_32_32_muladd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
Most Significant Word “32x16” Multiply & Add Instructions
16 instruction
*/


union clause ast = PEXT_32_16_MUL_ADD : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, SMMWB) <->
  0b0100010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, SMMWB_U) <->
  0b0101010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, SMMWT) <->
  0b0110010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, SMMWT_U) <->
  0b0111010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWB) <->
  0b0100011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWB_U) <->
  0b0101011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWT) <->
  0b0110011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWT_U) <->
  0b0111011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMWB2) <->
  0b1000111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMWB2_U) <->
  0b1001111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMWT2) <->
  0b1010111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMWT2_U) <->
  0b1011111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWB2) <->
  0b1100111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWB2_U) <->
  0b1101111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWT2) <->
  0b1110111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_16_MUL_ADD(rs2, rs1, rd, KMMAWT2_U) <->
  0b1111111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111


function clause execute (PEXT_32_16_MUL_ADD(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val  = X(rd);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_32 =  slice (rs1_val, i, 32);
    let rs2_32 =  slice (rs2_val, i, 32);
    let rd_32  =  slice (rd_val, i, 32);
    result[(i+31)..i] = match op {
      SMMWB    => smmw(rs1_32, slice (rs2_32, 0, 16)),
      SMMWB_U  => smmw_u(rs1_32, slice (rs2_32, 0, 16)),
      SMMWT    => smmw(rs1_32, slice (rs2_32, 16, 16)),
      SMMWT_U  => smmw_u(rs1_32, slice (rs2_32, 16, 16)),
      KMMAWB   => kmmaw(rs1_32, slice (rs2_32, 0, 16), rd_32),
      KMMAWB_U => kmmaw_u(rs1_32, slice (rs2_32, 0, 16), rd_32),
      KMMAWT   => kmmaw(rs1_32, slice (rs2_32, 16, 16), rd_32),
      KMMAWT_U => kmmaw_u(rs1_32, slice (rs2_32, 16, 16), rd_32),
      KMMWB2   => kmmw2(rs1_32, slice (rs2_32, 0, 16)),
      KMMWB2_U => kmmw2_u(rs1_32, slice (rs2_32, 0, 16)),
      KMMWT2   => kmmw2(rs1_32, slice (rs2_32, 16, 16)),
      KMMWT2_U => kmmw2_u(rs1_32, slice (rs2_32, 16, 16)),
      KMMAWB2  => kmmaw2(rs1_32, slice (rs2_32, 0, 16), rd_32),
      KMMAWB2_U=> kmmaw2_u(rs1_32, slice (rs2_32, 0, 16), rd_32),
      KMMAWT2  => kmmaw2(rs1_32, slice (rs2_32, 16, 16), rd_32),
      KMMAWT2_U=> kmmaw2_u(rs1_32, slice (rs2_32, 16, 16), rd_32)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_32_16_muladd_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMMWB    <-> "SMMWB",
    SMMWB_U   <-> "SMMWB_U",
    SMMWT  <-> "SMMWT",
    SMMWT_U   <-> "SMMWT_U",
    KMMAWB  <-> "KMMAWB",
    KMMAWB_U    <-> "KMMAWB_U",
    KMMAWT   <-> "KMMAWT",
    KMMAWT_U  <-> "KMMAWT_U",
    KMMWB2    <-> "KMMWB2",
    KMMWB2_U   <-> "KMMWB2_U",
    KMMWT2  <-> "KMMWT2",
    KMMWT2_U   <-> "KMMWT2_U",
    KMMAWB2  <-> "KMMAWB2",
    KMMAWB2_U    <-> "KMMAWB2_U",
    KMMAWT2   <-> "KMMAWT2",
    KMMAWT2_U  <-> "KMMAWT2_U"
}

mapping clause assembly = PEXT_32_16_MUL_ADD(rs2, rs1, rd, p_inst)
  <-> p_32_16_muladd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
Signed 16-bit Multiply with 32-bit Add/Subtract Instructions
*/
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
  if res <_s lb then { pext_write_OV (0b1); slice (lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice (ub, 0, 2 * 'n) }
  else { slice (res, 0, 2 * 'n) }

val kmads : forall 'n, 'n == 16 | 'n == 32.
  (bits(2 * 'n), bits ('n), bits ('n), bits ('n), bits ('n)) -> bits (2 * 'n)
  effect {rreg,wreg}
function kmads (rd, rs11, rs21, rs10, rs20) =
  let lb : bits(66) = not_vec(EXTS(sail_ones (2 * 'n) >> 1)) in
  let ub : bits(66) = EXTS(sail_ones (2 * 'n) >> 1) in
  let res : bits(66) = EXTS(rd) + EXTS(smul(rs11, rs21)) - EXTS(smul(rs10, rs20)) in
  if res <_s lb then { pext_write_OV (0b1); slice (lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice (ub, 0, 2 * 'n) }
  else { slice (res, 0, 2 * 'n) }

val kmsda : forall 'n, 'n == 16 | 'n == 32.
  (bits(2 * 'n), bits ('n), bits ('n), bits ('n), bits ('n)) -> bits (2 * 'n)
  effect {rreg,wreg}
function kmsda (rd, rs11, rs21, rs10, rs20) =
  let lb : bits(66) = not_vec(EXTS(sail_ones (2 * 'n) >> 1)) in
  let ub : bits(66) = EXTS(sail_ones (2 * 'n) >> 1) in
  let res : bits(66) = EXTS(rd) - EXTS(smul(rs11, rs21)) - EXTS(smul(rs10, rs20)) in
  if res <_s lb then { pext_write_OV (0b1); slice (lb, 0, 2 * 'n) }
  else if ub <_s res then { pext_write_OV (0b1); slice (ub, 0, 2 * 'n) }
  else { slice (res, 0, 2 * 'n) }

val sumul : forall 'n, 'n == 8.
  (bits('n), bits('n)) -> bits(32)
function sumul (v1, v2) =
  to_bits (32, signed(v1) * signed(0b0 @ v2))


union clause ast = PEXT_16_32_MULADD : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMBB16) <->
  0b0000100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMBT16) <->
  0b0001100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMTT16) <->
  0b0010100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMDA) <->
  0b0011100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMXDA) <->
  0b0011101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMDS) <->
  0b0101100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMDRS) <->
  0b0110100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, SMXDS) <->
  0b0111100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMABB) <->
  0b0101101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMABT) <->
  0b0110101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMATT) <->
  0b0111101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMADA) <->
  0b0100100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMAXDA) <->
  0b0100101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMADS) <->
  0b0101110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMADRS) <->
  0b0110110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMAXDS) <->
  0b0111110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMSDA) <->
  0b0100110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_16_32_MULADD(rs2, rs1, rd, KMSXDA) <->
  0b0100111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

  
function clause execute (PEXT_16_32_MULADD(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val  = X(rd);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_32 =  slice (rs1_val, i, 32);
    let rs2_32 =  slice (rs2_val, i, 32);
    let rd_32  =  slice (rd_val, i, 32);
    result[(i+31)..i] = match op {
      SMBB16    => smul(slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      SMBT16    => smul(slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)),
      SMTT16    => smul(slice (rs1_32, 16, 16), slice (rs2_32, 16, 16)),
      KMDA      => kmda(slice (rs1_32, 16, 16), slice (rs2_32, 16, 16), slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      KMXDA     => kmda(slice (rs1_32, 16, 16), slice (rs2_32, 0, 16), slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)),
      SMDS      => smul(slice (rs1_32, 16, 16), slice (rs2_32, 16, 16)) - smul(slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      SMDRS     => smul(slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)) - smul(slice (rs1_32, 16, 16), slice (rs2_32, 16, 16)),
      SMXDS     => smul(slice (rs1_32, 16, 16), slice (rs2_32, 0, 16)) - smul(slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)),
      KMABB     => kadd (smul(slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)), rd_32),
      KMABT     => kadd (smul(slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)), rd_32),
      KMATT     => kadd (smul(slice (rs1_32, 16, 16), slice (rs2_32, 16, 16)), rd_32), 
      KMADA     => kmada (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 16, 16), slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      KMAXDA    => kmada (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 0, 16), slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)),
      KMADS     => kmads (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 16, 16), slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      KMADRS    => kmads (rd_32, slice (rs1_32, 0, 16), slice (rs2_32, 0, 16), slice (rs1_32, 16, 16), slice (rs2_32, 16, 16)),
      KMAXDS    => kmads (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 0, 16), slice (rs1_32, 0, 16), slice (rs2_32, 16, 16)),
      KMSDA     => kmsda (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 16, 16), slice (rs1_32, 0, 16), slice (rs2_32, 0, 16)),
      KMSXDA    => kmsda (rd_32, slice (rs1_32, 16, 16), slice (rs2_32, 0, 16), slice (rs1_32, 0, 16), slice (rs2_32, 16, 16))
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_16_32_muladd_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMBB16    <-> "SMBB16",
    SMBT16   <-> "SMBT16",
    SMTT16  <-> "SMTT16",
    KMDA   <-> "KMDA",
    KMXDA  <-> "KMXDA",
    SMDS    <-> "SMDS",
    SMDRS   <-> "SMDRS",
    SMXDS  <-> "SMXDS",
    KMABB    <-> "KMABB",
    KMABT   <-> "KMABT",
    KMATT  <-> "KMATT",
    KMADA   <-> "KMADA",
    KMAXDA  <-> "KMAXDA",
    KMADS    <-> "KMADS",
    KMADRS   <-> "KMADRS",
    KMAXDS  <-> "KMAXDS",
    KMSDA    <-> "KMSDA",
    KMSXDA   <-> "KMSXDA"
}

mapping clause assembly = PEXT_16_32_MULADD(rs2, rs1, rd, p_inst)
  <-> p_16_32_muladd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
Signed 16-bit Multiply with 64-bit Add/Subtract Instructions
*/
union clause ast = PEXT_SMAL : (regidx, regidx, regidx)

mapping clause encdec = PEXT_SMAL(rs2, rs1, rd) <->
  0b0101111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_SMAL(rs2, rs1, rd)) = {
    let rs1_val = X(rs1);
    let rs2_val = X(rs2);
    
    if sizeof(xlen) == 32
    then {
        let rs10 = (rs1 >> 1) << 1 ;
        let rs11 = rs10 + 1 ;
        let rd0 = (rd >> 1) << 1 ;
        let rd1 = rd0 + 1 ;
        let result : bits(64) = (X(rs11) @ X(rs10)) + EXTS(smul(slice (rs2_val, 16, 16), slice (rs2_val, 0, 16))); 
        X(rd1) = result[63..32];
        X(rd0) = result[31..0];
    } else
        X(rd)  = rs1_val + EXTS(smul(slice (rs2_val, 48, 16), slice (rs2_val, 32, 16))) + EXTS(smul(slice (rs2_val, 16, 16), slice (rs2_val, 0, 16)));
    RETIRE_SUCCESS
}

mapping clause assembly = PEXT_SMAL(rs2, rs1, rd)
  <-> "SMAL" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
2.3.6. Miscellaneous Instructions

*/
union clause ast = PEXT_MISCELLANEOUS : (bits(5), regidx, regidx, p_inst_imm5_rs1_rd_op)

mapping clause encdec = PEXT_MISCELLANEOUS(imm5, rs1, rd, SCLIP32) <->
  0b1110010 @ imm5 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MISCELLANEOUS(imm5, rs1, rd, UCLIP32) <->
  0b1111010 @ imm5 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_MISCELLANEOUS(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let u_imm5 : byte = EXTZ(imm5);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      SCLIP32   =>  sclip(rs1_word, u_imm5),
      UCLIP32   =>  uclip(rs1_word, u_imm5)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_miscellaneous_mapping : p_inst_imm5_rs1_rd_op <-> string = {
  SCLIP32  <->  "SCLIP32",
  UCLIP32  <->  "UCLIP32"
}

mapping clause assembly = PEXT_MISCELLANEOUS(imm5, rs1, rd, p_inst)
  <-> p_miscellaneous_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/*
2.3.7. 8-bit Multiply with 32-bit Add Instructions

*/
union clause ast = PEXT_8_32_MUL_ADD : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_8_32_MUL_ADD(rs2, rs1, rd, SMAQA) <->
  0b1100100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_8_32_MUL_ADD(rs2, rs1, rd, SMAQA_SU) <->
  0b1100101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_8_32_MUL_ADD(rs2, rs1, rd, UMAQA) <->
  0b1100110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_8_32_MUL_ADD(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val  = X(rd);
  result : xlenbits = zeros();
  tmp_value : bits(32) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_8 =  slice (rs1_val, i, 8);
    let rs2_8 =  slice (rs2_val, i, 8);
    
    tmp_value = match op {
      SMAQA    => tmp_value + EXTS(smul(rs1_8,rs2_8)),
      UMAQA    => tmp_value + EXTZ(umul(rs1_8,rs2_8)),
      SMAQA_SU => tmp_value + EXTS(sumul(rs1_8,rs2_8))
    };
    if( i==24 | i==56)
    then {
      let rd_32  =  slice (rd_val, (i + 8 - 32), 32);
      result[(i + 7)..(i - 24)] = rd_32 + tmp_value;
      tmp_value = zeros();
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_8_32_muladd_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMAQA    <-> "SMAQA",
    UMAQA   <-> "UMAQA",
    SMAQA_SU  <-> "SMAQA_SU"
}

mapping clause assembly = PEXT_8_32_MUL_ADD(rs2, rs1, rd, p_inst)
  <-> p_8_32_muladd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* 8-bit one register instructions */
union clause ast = PEXT_ONE_REGISTER_32 : (regidx, regidx, p_inst_rs1_rd_op)

mapping clause encdec = PEXT_ONE_REGISTER_32(rs1, rd, CLRS32) <->
  0b1010111 @ 0b11000 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ONE_REGISTER_32(rs1, rd, CLO32) <->
  0b1010111 @ 0b11011 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ONE_REGISTER_32(rs1, rd, CLZ32) <->
  0b1010111 @ 0b11001 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_ONE_REGISTER_32(rs1, rd, op)) = {
  let rs1_val = X(rs1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i + 31)..i] = match op {
      CLRS32 => clrs(rs1_word),
      CLO32  => clo(rs1_word),
      CLZ32  => clz(rs1_word)
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_one_register_32_mapping : p_inst_rs1_rd_op <-> string = {
    CLRS32 <-> "CLRS32",
    CLO32  <-> "CLO32",
    CLZ32  <-> "CLZ32"
}

mapping clause assembly = PEXT_ONE_REGISTER_32(rs1, rd, p_inst)
  <-> p_one_register_32_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)


union clause ast = PEXT_PBSAD : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_PBSAD(rs2, rs1, rd, PBSAD) <->
  0b1111110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_PBSAD(rs2, rs1, rd, PBSADA) <->
  0b1111111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_PBSAD(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    tmp : xlenbits = zeros();
    tmp = { 
      let v1ext : bits(9) = EXTZ(rs1_byte) ;
      let v2ext : bits(9) = EXTZ(rs2_byte) ;
      let pos : xlenbits = EXTS (v1ext - v2ext) ;
      xlen_zeros : xlenbits = zeros();
      if pos <_s xlen_zeros then not_vec(pos) + 1 else pos
    };
    result = result + tmp ;
  };
  result = match op {
    PBSAD  => result ,
    PBSADA => X(rd) + result
  };

  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_pbsad_mapping : p_inst_rs2_rs1_rd_op <-> string = {
  PBSAD <-> "PBSAD",
  PBSADA  <-> "PBSADA"
}


mapping clause assembly = PEXT_PBSAD(rs2, rs1, rd, p_inst)
  <-> p_inst_pbsad_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)



/* 16-bit pack instructions */
union clause ast = PEXT_PACK_16 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_PACK_16(rs2, rs1, rd, PKBB16) <->
  0b0000111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_PACK_16(rs2, rs1, rd, PKBT16) <->
  0b0001111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_PACK_16(rs2, rs1, rd, PKTT16) <->
  0b0010111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_PACK_16(rs2, rs1, rd, PKTB16) <->
  0b0011111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_PACK_16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_bottom =  slice (rs1_val, i, 16);
    let rs1_top =  slice (rs1_val, i+16, 16);   
    let rs2_bottom =  slice (rs2_val, i, 16);
    let rs2_top =  slice (rs2_val, i+16, 16);
    result[(i + 31)..i] = match op {
      PKBB16 => rs1_bottom @ rs2_bottom,
      PKBT16 => rs1_bottom @ rs2_top,
      PKTB16 => rs1_top @ rs2_bottom,
      PKTT16 => rs1_top @ rs2_top
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_pack_16_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    PKBB16 <-> "PKBB16",
    PKTB16 <-> "PKTB16",
    PKBT16 <-> "PKBT16",
    PKTT16 <-> "PKTT16"
}

mapping clause assembly = PEXT_PACK_16(rs2, rs1, rd, p_inst)
  <-> p_pack_16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)