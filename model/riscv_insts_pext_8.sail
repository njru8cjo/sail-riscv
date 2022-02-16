/* 
8-bit ALU Instructions
*/

/* *****************************************************************/


union clause ast = PEXT_ALU8 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, ADD8) <->
  0b0100100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, CMPEQ8) <->
  0b0100111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KADD8) <->
  0b0001100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KHM8) <->
  0b1000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KHMX8) <->
  0b1001111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KSLL8) <->
  0b0110110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KSLRA8) <->
  0b0101111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KSLRA8_U) <->
  0b0110111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KSUB8) <->
  0b0001101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, RADD8) <->
  0b0000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, RSUB8) <->
  0b0000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SCMPLE8) <->
  0b0001111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SCMPLT8) <->
  0b0000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SLL8) <->
  0b0101110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMAX8) <->
  0b1000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMIN8) <->
  0b1000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMUL8) <->
  0b1010100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMULX8) <->
  0b1010101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SRA8) <->
  0b0101100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SRA8_U) <->
  0b0110100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SRL8) <->
  0b0101101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SRL8_U) <->
  0b0110101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SUB8) <->
  0b0100101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UCMPLE8) <->
  0b0011111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UCMPLT8) <->
  0b0010111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UKADD8) <->
  0b0011100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UKSUB8) <->
  0b0011101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMAX8) <->
  0b1001101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMIN8) <->
  0b1001100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMUL8) <->
  0b1011100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMULX8) <->
  0b1011101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, URADD8) <->
  0b0010100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, URSUB8) <->
  0b0010101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_ALU8(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_0 =  slice (rs1_val, i, 8);
    let rs1_1 =  slice (rs1_val, i+8, 8);
    let rs1_2 =  slice (rs1_val, i+16, 8);
    let rs1_3 =  slice (rs1_val, i+24, 8);    
    let rs2_0 =  slice (rs2_val, i, 8);
    let rs2_1 =  slice (rs2_val, i+8, 8);
    let rs2_2 =  slice (rs2_val, i+16, 8);
    let rs2_3 =  slice (rs2_val, i+24, 8); 
    result[(i+31)..i] = match op {
      ADD8    => rs1_3 + rs2_3 @ rs1_2 + rs2_2 @ rs1_1 + rs2_1 @ rs1_0 + rs2_0,
      RADD8   => radd(rs1_3,rs2_3) @ radd(rs1_2,rs2_2) @ radd(rs1_1,rs2_1) @ radd(rs1_0,rs2_0),
      URADD8  => uradd(rs1_3,rs2_3) @ uradd(rs1_2,rs2_2) @ uradd(rs1_1,rs2_1) @ uradd(rs1_0,rs2_0),
      KADD8   => kadd(rs1_3,rs2_3) @ kadd(rs1_2,rs2_2) @ kadd(rs1_1,rs2_1) @ kadd(rs1_0,rs2_0), 
      UKADD8  => ukadd(rs1_3,rs2_3) @ ukadd(rs1_2,rs2_2) @ ukadd(rs1_1,rs2_1) @ ukadd(rs1_0,rs2_0),
      SUB8    => rs1_3 - rs2_3 @ rs1_2 - rs2_2 @ rs1_1 - rs2_1 @ rs1_0 - rs2_0,
      RSUB8   => rsub(rs1_3,rs2_3) @ rsub(rs1_2,rs2_2) @ rsub(rs1_1,rs2_1) @ rsub(rs1_0,rs2_0),
      URSUB8  => ursub(rs1_3,rs2_3) @ ursub(rs1_2,rs2_2) @ ursub(rs1_1,rs2_1) @ ursub(rs1_0,rs2_0),
      KSUB8   => ksub(rs1_3,rs2_3) @ ksub(rs1_2,rs2_2) @ ksub(rs1_1,rs2_1) @ ksub(rs1_0,rs2_0),
      UKSUB8  => uksub(rs1_3,rs2_3) @ uksub(rs1_2,rs2_2) @ uksub(rs1_1,rs2_1) @ uksub(rs1_0,rs2_0)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping pPEXT_ALU8_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD8    <-> "ADD8",
    RADD8   <-> "RADD8",
    URADD8  <-> "URADD8",
    KADD8   <-> "KADD8",
    UKADD8  <-> "UKADD8",
    SUB8    <-> "SUB8",
    RSUB8   <-> "RSUB8",
    URSUB8  <-> "URSUB8",
    KSUB8   <-> "KSUB8",
    UKSUB8  <-> "UKSUB8"
}

mapping clause assembly = PEXT_ALU8(rs2, rs1, rd, p_inst)
  <-> pPEXT_ALU8_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)