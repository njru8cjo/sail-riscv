/* SIMD 32bits add/sub instructions  */
union clause ast = PEXT_INST_32BITS_SIMD_ADD_SUB : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, ADD32) <->
  0b0100000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, KADD32) <->
  0b0001000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, RADD32) <->
  0b0000000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, UKADD32) <->
  0b0011000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, URADD32) <->
  0b0010000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, SUB32) <->
  0b0100001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, KSUB32) <->
  0b0001001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, RSUB32) <->
  0b0000001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, UKSUB32) <->
  0b0011001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, URSUB32) <->
  0b0010001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111


function clause execute (PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      ADD32   =>  rs1_word + rs2_word,
      RADD32  =>  radd(rs1_word, rs2_word),
      KADD32  =>  kadd(rs1_word, rs2_word),
      URADD32 =>  uradd(rs1_word, rs2_word),
      UKADD32 =>  ukadd(rs1_word, rs2_word),
      SUB32   =>  rs1_word - rs2_word,
      RSUB32  =>  rsub(rs1_word, rs2_word),
      KSUB32  =>  ksub(rs1_word, rs2_word),
      URSUB32 =>  ursub(rs1_word, rs2_word),
      UKSUB32 =>  uksub(rs1_word, rs2_word)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_32bits_SIMD_add_sub_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD32    <-> "ADD32",
    RADD32   <-> "RADD32",
    URADD32  <-> "URADD32",
    KADD32   <-> "KADD32",
    UKADD32  <-> "UKADD32",
    SUB32    <-> "SUB32",
    RSUB32   <-> "RSUB32",
    URSUB32  <-> "URSUB32",
    KSUB32   <-> "KSUB32",
    UKSUB32  <-> "UKSUB32"
}

mapping clause assembly = PEXT_INST_32BITS_SIMD_ADD_SUB(rs2, rs1, rd, p_inst)
  <-> p_32bits_SIMD_add_sub_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* SIMD 32bits shift instructions  */
/*union clause ast = PEXT_INST_32BITS_SIMD_SHIFT : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = P_INST_RS2_RS1_RD(rs2, rs1, rd, SRA32) <->
  0b0101000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS2_RS1_RD(rs2, rs1, rd, SRA32_U) <->
  0b0110000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS2_RS1_RD(rs2, rs1, rd, SRL32) <->
  0b0101001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS2_RS1_RD(rs2, rs1, rd, SRL32_U) <->
  0b0110001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b1110111*/