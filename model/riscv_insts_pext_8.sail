/* 
8-bit ALU Instructions
*/

/* 8bits add, sub, compare and misc instructions */
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
      KSLRA8     => kslra(rs1_byte, EXTS(rs2_val[3..0])),
      KSLRA8_U   => kslra_u(rs1_byte, EXTS(rs2_val[3..0]))

    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

/*
      KSLRA8     => shift_right_arith(rs1_byte, EXTS(rs2_val[3..0])),
      KSLRA8_U   => shift_right_arith_u(rs1_byte, EXTS(rs2_val[3..0]))
*/

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

/* 8bits imm3 instructions */
union clause ast = P_INST_IMM3_RS1_RD : (bits(3), regidx, regidx, p_inst_imm3_rs1_rd_op)

mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, KSLLI8) <->
  0b0111110 @ 0b01 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SCLIP8) <->
  0b1000110 @ 0b00 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SLLI8) <->
  0b0111110 @ 0b00 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SRAI8) <->
  0b0111100 @ 0b00 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SRAI8_U) <->
  0b0111100 @ 0b01 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SRLI8) <->
  0b0111101 @ 0b00 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, SRLI8_U) <->
  0b0111101 @ 0b01 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_IMM3_RS1_RD(imm3, rs1, rd, UCLIP8) <->
  0b1000110 @ 0b10 @ imm3 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (P_INST_IMM3_RS1_RD(imm3, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : byte = EXTZ(imm3);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      SRAI8     => shift_right_arith(rs1_byte, sa),
      SRAI8_U   => shift_right_arith_u(rs1_byte, sa),
      SRLI8     => shift_right_logic(rs1_byte, sa),
      SRLI8_U   => shift_right_logic_u(rs1_byte, sa),
      SLLI8     => shift_left_logic(rs1_byte, sa),
      KSLLI8    => kshift_left_logic(rs1_byte, sa),
      SCLIP8    => sclip(rs1_byte, sa),
      UCLIP8    => uclip(rs1_byte, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_imm3_rs1_rd_mapping : p_inst_imm3_rs1_rd_op <-> string = {
  KSLLI8 <-> "KSLLI8",
  SLLI8  <-> "SLLI8",
  SRAI8  <-> "SRAI8",
  SRAI8_U <-> "SRAI8_U",
  SRLI8 <-> "SRLI8",
  SRLI8_U <-> "SRLI8_U",
  SCLIP8 <-> "SCLIP8",
  UCLIP8 <-> "UCLIP8"
}

mapping clause assembly = P_INST_IMM3_RS1_RD(imm3, rs1, rd, p_inst)
  <-> p_inst_imm3_rs1_rd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_3(imm3)

/* 8bits one register instructions */
union clause ast = P_INST_RS1_RD : (regidx, regidx, p_inst_rs1_rd_op)

mapping clause encdec = P_INST_RS1_RD(rs1, rd, CLRS8) <->
  0b1010111 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS1_RD(rs1, rd, CLO8) <->
  0b1010111 @ 0b00011 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS1_RD(rs1, rd, CLZ8) <->
  0b1010111 @ 0b00001 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_RS1_RD(rs1, rd, KABS8) <->
  0b1010110 @ 0b10000 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (P_INST_RS1_RD(rs1, rd, op)) = {
  let rs1_val = X(rs1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      CLRS8    => clrs(rs1_byte),
      CLO8     => clo(rs1_byte),
      CLZ8     => clz(rs1_byte),
      KABS8    => kabs(rs1_byte)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_rs1_rd_mapping : p_inst_rs1_rd_op <-> string = {
  CLRS8 <-> "CLRS8",
  CLO8  <-> "CLO8",
  CLZ8  <-> "CLZ8",
  KABS8 <-> "KABS8"
}

mapping clause assembly = P_INST_RS1_RD(rs1, rd, p_inst)
  <-> p_inst_rs1_rd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* 8bits swap and unpack instructions */
union clause ast = P_INST_SWAP_UNPACK : (regidx, regidx, p_inst_rs1_rd_op)

mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SUNPKD810) <->
  0b1010110 @ 0b01000 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SUNPKD820) <->
  0b1010110 @ 0b01001 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SUNPKD830) <->
  0b1010110 @ 0b01010 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SUNPKD831) <->
  0b1010110 @ 0b01011 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SUNPKD832) <->
  0b1010110 @ 0b10011 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, SWAP8) <->
  0b1010110 @ 0b11000 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, ZUNPKD810) <->
  0b1010110 @ 0b01100 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, ZUNPKD820) <->
  0b1010110 @ 0b01101 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, ZUNPKD830) <->
  0b1010110 @ 0b01110 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, ZUNPKD831) <->
  0b1010110 @ 0b01111 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = P_INST_SWAP_UNPACK(rs1, rd, ZUNPKD832) <->
  0b1010110 @ 0b10111 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (P_INST_SWAP_UNPACK(rs1, rd, op)) = {
  let rs1_val = X(rs1);
  result : xlenbits = zeros();
  resultH : bits(16) = zeros();
  resultL : bits(16) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_byte0 = slice(rs1_val, i, 8);
    let rs1_byte1 = slice(rs1_val, i+8, 8);
    let rs1_byte2 = slice(rs1_val, i+16, 8);
    let rs1_byte3 = slice(rs1_val, i+24, 8);

    result[(i+31)..i] = match op {
      SWAP8      =>  rs1_byte2 @ rs1_byte3 @ rs1_byte0 @ rs1_byte1,
      SUNPKD810  =>  { resultH = EXTS(rs1_byte1); 
                       resultL = EXTS(rs1_byte0);
                       resultH @ resultL},
      SUNPKD820  =>  { resultH = EXTS(rs1_byte2); 
                     resultL = EXTS(rs1_byte0);
                     resultH @ resultL },
      SUNPKD830  =>  { resultH = EXTS(rs1_byte3); 
                     resultL = EXTS(rs1_byte0);
                     resultH @ resultL },
      SUNPKD831  =>  { resultH = EXTS(rs1_byte3); 
                     resultL = EXTS(rs1_byte1);
                     resultH @ resultL },
      SUNPKD832  =>  { resultH = EXTS(rs1_byte3); 
                     resultL = EXTS(rs1_byte2);
                     resultH @ resultL },
      ZUNPKD810  =>  { resultH = EXTZ(rs1_byte1); 
                     resultL = EXTZ(rs1_byte0);
                     resultH @ resultL },
      ZUNPKD820  =>  { resultH = EXTZ(rs1_byte2); 
                     resultL = EXTZ(rs1_byte0);
                     resultH @ resultL },
      ZUNPKD830  =>  { resultH = EXTZ(rs1_byte3); 
                     resultL = EXTZ(rs1_byte0);
                     resultH @ resultL },
      ZUNPKD831  =>  { resultH = EXTZ(rs1_byte3); 
                     resultL = EXTZ(rs1_byte1);
                     resultH @ resultL },
      ZUNPKD832  =>  { resultH = EXTZ(rs1_byte3); 
                     resultL = EXTZ(rs1_byte2);
                     resultH @ resultL }
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_swap_unpack_mapping : p_inst_rs1_rd_op <-> string = {
  SWAP8     <-> "SWAP8",
  SUNPKD810 <-> "SUNPKD810",
  SUNPKD820 <-> "SUNPKD820",
  SUNPKD830 <-> "SUNPKD830",
  SUNPKD831 <-> "SUNPKD831",
  SUNPKD832 <-> "SUNPKD832",
  ZUNPKD810 <-> "ZUNPKD810",
  ZUNPKD820 <-> "ZUNPKD820",
  ZUNPKD830 <-> "ZUNPKD830",
  ZUNPKD831 <-> "ZUNPKD831",
  ZUNPKD832 <-> "ZUNPKD832"
}

mapping clause assembly = P_INST_SWAP_UNPACK(rs1, rd, p_inst)
  <-> p_inst_swap_unpack_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)