/* 
64-bits profile instructions
*/

/* 8bits add, sub, compare and misc instructions */
union clause ast = PEXT_INST_64BITS_PROFILE : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, ADD64) <->
  0b1100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, KADD64) <->
  0b1001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, RADD64) <->
  0b1000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, UKADD64) <->
  0b1011000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, URADD64) <->
  0b1010000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, SUB64) <->
  0b1100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, KSUB64) <->
  0b1001001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, RSUB64) <->
  0b1000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, UKSUB64) <->
  0b1011001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, URSUB64) <->
  0b1010001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, op)) = {
  results : bits(64) = zeros();
  rs1_val : bits(64) = zeros();
  rs2_val : bits(64) = zeros();
  if sizeof(xlen) == 32
  then {
    rs1_val = X(rs1 | 0b00001) @ X(rs1 & 0b11110);
    rs2_val = X(rs2 | 0b00001) @ X(rs2 & 0b11110);
  }  
  else {
    rs1_val = X(rs1);
    rs2_val = X(rs2);
  }; 
  results = match op {
    ADD64    =>  rs1_val + rs2_val,
    KADD64   =>  kadd(rs1_val, rs2_val),
    RADD64   =>  radd(rs1_val, rs2_val),
    UKADD64  =>  ukadd(rs1_val, rs2_val),
    URADD64  =>  uradd(rs1_val, rs2_val),
    SUB64    =>  rs1_val - rs2_val,
    KSUB64   =>  ksub(rs1_val, rs2_val),
    RSUB64   =>  rsub(rs1_val, rs2_val),
    UKSUB64  =>  uksub(rs1_val, rs2_val),
    URSUB64  =>  ursub(rs1_val, rs2_val)
  };
  if sizeof(xlen) == 32
  then {
    X(rd | 0b00001) = results[63..32];
    X(rd & 0b11110) = results[31..0];
  }  
  else X(rd) = results;
  RETIRE_SUCCESS
}

mapping p_64bits_profile_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD64    <-> "ADD64",
    RADD64   <-> "RADD64",
    URADD64  <-> "URADD64",
    KADD64   <-> "KADD64",
    UKADD64  <-> "UKADD64",
    SUB64    <-> "SUB64",
    RSUB64   <-> "RSUB64",
    URSUB64  <-> "URSUB64",
    KSUB64   <-> "KSUB64",
    UKSUB64  <-> "UKSUB64"
}

mapping clause assembly = PEXT_INST_64BITS_PROFILE(rs2, rs1, rd, p_inst)
  <-> p_64bits_profile_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
