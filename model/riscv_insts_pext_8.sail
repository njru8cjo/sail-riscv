/* 
8-bit ALU Instructions
*/

/* 8bits add, sub and compare instructions */
union clause ast = PEXT_ALU8 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, ADD8) <->
  0b0100100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KADD8) <->
  0b0001100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, RADD8) <->
  0b0000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UKADD8) <->
  0b0011100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, URADD8) <->
  0b0010100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SUB8) <->
  0b0100101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, KSUB8) <->
  0b0001101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, RSUB8) <->
  0b0000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UKSUB8) <->
  0b0011101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, URSUB8) <->
  0b0010101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, CMPEQ8) <->
  0b0100111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SCMPLE8) <->
  0b0001111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SCMPLT8) <->
  0b0000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMAX8) <->
  0b1000101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, SMIN8) <->
  0b1000100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UCMPLE8) <->
  0b0011111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UCMPLT8) <->
  0b0010111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMAX8) <->
  0b1001101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU8(rs2, rs1, rd, UMIN8) <->
  0b1001100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_ALU8(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      ADD8    => rs1_byte + rs2_byte,
      RADD8   => radd(rs1_byte, rs2_byte),
      URADD8  => uradd(rs1_byte, rs2_byte),
      KADD8   => kadd(rs1_byte, rs2_byte),
      UKADD8  => ukadd(rs1_byte, rs2_byte),
      SUB8    => rs1_byte - rs2_byte,
      RSUB8   => rsub(rs1_byte, rs2_byte),
      URSUB8  => ursub(rs1_byte, rs2_byte),
      KSUB8   => ksub(rs1_byte, rs2_byte),
      UKSUB8  => uksub(rs1_byte, rs2_byte),
      CMPEQ8  => cmpeq(rs1_byte, rs2_byte),
      SCMPLE8  => scmple(rs1_byte, rs2_byte),
      SCMPLT8  => scmplt(rs1_byte, rs2_byte),
      UCMPLE8  => ucmple(rs1_byte, rs2_byte),
      UCMPLT8  => ucmplt(rs1_byte, rs2_byte)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ALU8_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD8    <-> "ADD8",
    RADD8   <-> "RADD8",
    URADD8  <-> "URADD8",
    KADD8   <-> "KADD8",
    UKADD8  <-> "UKADD8",
    SUB8    <-> "SUB8",
    RSUB8   <-> "RSUB8",
    URSUB8  <-> "URSUB8",
    KSUB8   <-> "KSUB8",
    UKSUB8  <-> "UKSUB8",
    CMPEQ8  <-> "CMPEQ8",
    SCMPLE8 <-> "SCMPLE8",
    SCMPLT8 <-> "SCMPLT8",
    UCMPLE8 <-> "UCMPLE8",
    UCMPLT8 <-> "UCMPLT8"
}

mapping clause assembly = PEXT_ALU8(rs2, rs1, rd, p_inst)
  <-> p_ALU8_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)



/* 8bits mul instruction */
union clause ast = PEXT_MUL8 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, KHM8) <->
  0b1000111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, KHMX8) <->
  0b1001111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, SMUL8) <->
  0b1010100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, SMULX8) <->
  0b1010101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, UMUL8) <->
  0b1011100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_MUL8(rs2, rs1, rd, UMULX8) <->
  0b1011101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_MUL8(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_byte0 = slice(rs1_val, 0, 8);
  let rs1_byte1 = slice(rs1_val, 8, 8);
  let rs1_byte2 = slice(rs1_val, 16, 8);
  let rs1_byte3 = slice(rs1_val, 24, 8); 
  let rs2_byte0 = slice(rs2_val, 0, 8);
  let rs2_byte1 = slice(rs2_val, 8, 8);
  let rs2_byte2 = slice(rs2_val, 16, 8);
  let rs2_byte3 = slice(rs2_val, 24, 8);
  if sizeof(xlen) == 32
  then {
    let rd0 = (rd >> 1) << 1 ;
    let rd1 = rd0 + 1 ;
    result : xlenbits = zeros();
    result1 : xlenbits = zeros();
    match op {  
      SMUL8   => {result1 = smul(rs1_byte3, rs2_byte3) @ smul(rs1_byte2, rs2_byte2);
                 result = smul(rs1_byte1, rs2_byte1) @ smul(rs1_byte0, rs2_byte0)},
      SMULX8  => {result1 = smul(rs1_byte3, rs2_byte2) @ smul(rs1_byte2, rs2_byte3);
                 result = smul(rs1_byte1, rs2_byte0) @ smul(rs1_byte0, rs2_byte1)},
      UMUL8   => {result1 = umul(rs1_byte3, rs2_byte3) @ umul(rs1_byte2, rs2_byte2);
                 result = umul(rs1_byte1, rs2_byte1) @ umul(rs1_byte0, rs2_byte0)},
      UMULX8  => {result1 = umul(rs1_byte3, rs2_byte2) @ umul(rs1_byte2, rs2_byte3);
                 result = umul(rs1_byte1, rs2_byte0) @ umul(rs1_byte0, rs2_byte1)}
    }; 
    X(rd0) = result;
    X(rd1) = result1;
  }
  else {
    result : xlenbits = zeros();
    match op {  
      SMUL8   => {result = smul(rs1_byte3, rs2_byte3) @ smul(rs1_byte2, rs2_byte2) @
                 smul(rs1_byte1, rs2_byte1) @ smul(rs1_byte0, rs2_byte0)},
      SMULX8  => {result = smul(rs1_byte3, rs2_byte2) @ smul(rs1_byte2, rs2_byte3) @
                 smul(rs1_byte1, rs2_byte0) @ smul(rs1_byte0, rs2_byte1)},
      UMUL8   => {result = umul(rs1_byte3, rs2_byte3) @ umul(rs1_byte2, rs2_byte2) @
                 umul(rs1_byte1, rs2_byte1) @ umul(rs1_byte0, rs2_byte0)},
      UMULX8  => {result= umul(rs1_byte3, rs2_byte2) @ umul(rs1_byte2, rs2_byte3) @
                 umul(rs1_byte1, rs2_byte0) @ umul(rs1_byte0, rs2_byte1)}
    }; 
    X(rd) = result;
  };
  RETIRE_SUCCESS 
}

mapping p_MUL8_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMUL8   <-> "SMUL8",
    SMULX8  <-> "SMULX8",
    UMUL8   <-> "UMUL8",
    UMULX8  <-> "UMULX8"
}

mapping clause assembly = PEXT_MUL8(rs2, rs1, rd, p_inst)
  <-> p_MUL8_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* 8bits shift instructions */
union clause ast = PEXT_SHIFT8 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, SRA8) <->
  0b0101100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, SRA8_U) <->
  0b0110100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, SRL8) <->
  0b0101101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, SRL8_U) <->
  0b0110101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, SLL8) <->
  0b0101110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, KSLL8) <->
  0b0110110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, KSLRA8) <->
  0b0101111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_SHIFT8(rs2, rs1, rd, KSLRA8_U) <->
  0b0110111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_SHIFT8(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      SRA8     => shift_right_arith(rs1_byte, EXTZ(rs2_val[2..0])),
      SRA8_U   => shift_right_arith_u(rs1_byte, EXTZ(rs2_val[2..0])),
      SRL8     => shift_right_logic(rs1_byte, EXTZ(rs2_val[2..0])),
      SRL8_U   => shift_right_logic_u(rs1_byte, EXTZ(rs2_val[2..0])),
      SLL8     => shift_left_logic(rs1_byte, EXTZ(rs2_val[2..0])),
      KSLL8     => kshift_left_logic(rs1_byte, EXTZ(rs2_val[2..0])),
      KSLRA8     => shift_right_arith(rs1_byte, EXTZ(rs2_val[3..0])),
      KSLRA8_U   => shift_right_arith_u(rs1_byte, EXTZ(rs2_val[3..0]))
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_SHIFT8_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SRA8   <-> "SRA8",
    SRA8_U  <-> "SRA8_U",
    SRL8   <-> "SRL8",
    SRL8_U  <-> "SRL8_U",
    SLL8   <-> "SLL8",
    KSLL8  <-> "KSLL8",
    KSLRA8  <-> "KSLRA8",
    KSLRA8_U  <-> "KSLRA8_U"
}

mapping clause assembly = PEXT_SHIFT8(rs2, rs1, rd, p_inst)
  <-> p_SHIFT8_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)