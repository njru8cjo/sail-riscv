/* 
64-bits profile instructions
*/

/* 64bits profile add, sub instructions */
union clause ast = PEXT_INST_64BITS_ADD_SUB : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

/* 64 bits profile ADD encode decode */
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, ADD64) <->
  0b1100000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, KADD64) <->
  0b1001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, RADD64) <->
  0b1000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, UKADD64) <->
  0b1011000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, URADD64) <->
  0b1010000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
/* 64 bits profile SUB encode decode */
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, SUB64) <->
  0b1100001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, KSUB64) <->
  0b1001001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, RSUB64) <->
  0b1000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, UKSUB64) <->
  0b1011001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, URSUB64) <->
  0b1010001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, op)) = {
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

mapping p_64bits_add_sub_mapping : p_inst_rs2_rs1_rd_op <-> string = {
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

mapping clause assembly = PEXT_INST_64BITS_ADD_SUB(rs2, rs1, rd, p_inst)
  <-> p_64bits_add_sub_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* 64bits profile 32 bits mul with 64bits add/sub instructions */
union clause ast = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, SMAR64) <->
  0b1000010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, SMSR64) <->
  0b1000011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, UMAR64) <->
  0b1010010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, UMSR64) <->
  0b1010011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, KMAR64) <->
  0b1001010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, KMSR64) <->
  0b1001011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, UKMAR64) <->
  0b1011010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, UKMSR64) <->
  0b1011011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : bits(64) = zeros();
  if sizeof(xlen) == 32
  then {
      let rs1_word = slice(rs1_val, 0, 32);
      let rs2_word = slice(rs2_val, 0, 32);
      result = match op {
      SMAR64   => (X(rd | 0b00001) @ X(rd & 0b11110)) + smul(rs1_word, rs2_word),
      SMSR64   => (X(rd | 0b00001) @ X(rd & 0b11110)) - smul(rs1_word, rs2_word),
      UMAR64   => (X(rd | 0b00001) @ X(rd & 0b11110)) + umul(rs1_word, rs2_word),
      UMSR64   => (X(rd | 0b00001) @ X(rd & 0b11110)) - umul(rs1_word, rs2_word),
      KMAR64   => kadd((X(rd | 0b00001) @ X(rd & 0b11110)), smul(rs1_word, rs2_word)),
      KMSR64   => ksub((X(rd | 0b00001) @ X(rd & 0b11110)), smul(rs1_word, rs2_word)),
      UKMAR64  => ukadd((X(rd | 0b00001) @ X(rd & 0b11110)), umul(rs1_word, rs2_word)),
      UKMSR64  => uksub((X(rd | 0b00001) @ X(rd & 0b11110)), umul(rs1_word, rs2_word))
    };
    X(rd | 0b00001) = result[63..32];
    X(rd & 0b11110) = result[31..0];
  }
  else {
      let rs1_word_B = slice(rs1_val, 0, 32);
      let rs2_word_B = slice(rs2_val, 0, 32);
      let rs1_word_T = slice(rs1_val, 32, 32);
      let rs2_word_T = slice(rs2_val, 32, 32);
      result = match op {
      SMAR64   => X(rd) + ( smul(rs1_word_B, rs2_word_B) + smul(rs1_word_T, rs2_word_T) ),
      SMSR64   => X(rd) - ( smul(rs1_word_B, rs2_word_B) + smul(rs1_word_T, rs2_word_T) ),
      UMAR64   => X(rd) + ( umul(rs1_word_B, rs2_word_B) + umul(rs1_word_T, rs2_word_T) ),
      UMSR64   => X(rd) - ( umul(rs1_word_B, rs2_word_B) + umul(rs1_word_T, rs2_word_T) ),
      KMAR64   => kadd(X(rd), (smul(rs1_word_B, rs2_word_B) + smul(rs1_word_T, rs2_word_T) )),
      KMSR64   => ksub(X(rd), (smul(rs1_word_B, rs2_word_B) + smul(rs1_word_T, rs2_word_T) )),
      UKMAR64  => ukadd(X(rd), (umul(rs1_word_B, rs2_word_B) + umul(rs1_word_T, rs2_word_T) )),
      UKMSR64  => uksub(X(rd), (umul(rs1_word_B, rs2_word_B) + umul(rs1_word_T, rs2_word_T) ))
    };
    X(rd) = result;
  };
  RETIRE_SUCCESS
}

mapping p_32bits_mul_with_64bits_add_sub_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMAR64   <-> "SMAR64",
    SMSR64   <-> "SMSR64",
    UMAR64   <-> "UMAR64",
    UMSR64   <-> "UMSR64",
    KMAR64   <-> "KMAR64",
    KMSR64   <-> "KMSR64",
    UKMAR64  <-> "UKMAR64",
    UKMSR64  <-> "UKMSR64"
}

mapping clause assembly = PEXT_INST_32BITS_MUL_WITH_64BITS_ADD_SUB(rs2, rs1, rd, p_inst)
  <-> p_32bits_mul_with_64bits_add_sub_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* 64bits profile 16 bits mul with 64bits add/sub instructions */
union clause ast = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALBB) <->
  0b1000100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALBT) <->
  0b1001100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALTT) <->
  0b1010100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALDA) <->
  0b1000110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALXDA) <->
  0b1001110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALDS) <->
  0b1000101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALDRS) <->
  0b1001101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, SMALXDS) <->
  0b1010101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111 

function clause execute (PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_half_top = slice(rs1_val, i+16, 16);
    let rs1_half_bottom = slice(rs1_val, i, 16);
    let rs2_half_top = slice(rs2_val, i+16, 16);
    let rs2_half_bottom = slice(rs2_val, i, 16);
    match op {
      SMALBB   =>  { result = result + EXTS(smul(rs1_half_bottom, rs2_half_bottom));},
      SMALBT   =>  { result = result + EXTS(smul(rs1_half_bottom, rs2_half_top));},
      SMALTT   =>  { result = result + EXTS(smul(rs1_half_top, rs2_half_top));},
      SMALDA   =>  { result = result + EXTS(smul(rs1_half_top, rs2_half_top)) + EXTS(smul(rs1_half_bottom, rs2_half_bottom));},
      SMALXDA  =>  { result = result + EXTS(smul(rs1_half_top, rs2_half_bottom)) + EXTS(smul(rs1_half_bottom, rs2_half_top));},
      SMALDS   =>  { result = result + EXTS(smul(rs1_half_top, rs2_half_top)) - EXTS(smul(rs1_half_bottom, rs2_half_bottom));},
      SMALDRS  =>  { result = result + EXTS(smul(rs1_half_bottom, rs2_half_bottom)) - EXTS(smul(rs1_half_top, rs2_half_top));},
      SMALXDS  =>  { result = result + EXTS(smul(rs1_half_top, rs2_half_bottom)) - EXTS(smul(rs1_half_bottom, rs2_half_top));},
      SMSLDA   =>  { result = result - EXTS(smul(rs1_half_top, rs2_half_top)) - EXTS(smul(rs1_half_bottom, rs2_half_bottom));},
      SMSLXDA  =>  { result = result - EXTS(smul(rs1_half_top, rs2_half_bottom)) - EXTS(smul(rs1_half_bottom, rs2_half_top));}
    };
  };
  if sizeof(xlen) == 32
  then {
    result = result + (X(rd | 0b00001) @ X(rd & 0b11110));
    X(rd | 0b00001) = result[63..32];
    X(rd & 0b11110) = result[31..0];
  }
  else {
    X(rd) = X(rd) + result;
  };
  RETIRE_SUCCESS
}
/*
function clause execute (PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : bits(64) = zeros();
    let rs1_half_top = slice(rs1_val, 16, 16);
    let rs1_half_bottom = slice(rs1_val, 0, 16);
    let rs2_half_top = slice(rs2_val, 16, 16);
    let rs2_half_bottom = slice(rs2_val, 0, 16);
  result =  match op {
      SMALBB   =>   EXTS(smul(rs1_half_bottom, rs2_half_bottom)),
      SMALBT   =>   EXTS(smul(rs1_half_bottom, rs2_half_top)),
      SMALTT   =>   EXTS(smul(rs1_half_top, rs2_half_top)),
      SMALDA   =>   EXTS(smul(rs1_half_top, rs2_half_top)) + EXTS(smul(rs1_half_bottom, rs2_half_bottom)),
      SMALXDA  =>   EXTS(smul(rs1_half_top, rs2_half_bottom)) + EXTS(smul(rs1_half_bottom, rs2_half_top)),
      SMALDS   =>   EXTS(smul(rs1_half_top, rs2_half_top)) - EXTS(smul(rs1_half_bottom, rs2_half_bottom)),
      SMALDRS  =>   EXTS(smul(rs1_half_bottom, rs2_half_bottom)) - EXTS(smul(rs1_half_top, rs2_half_top)),
      SMALXDS  =>   EXTS(smul(rs1_half_top, rs2_half_bottom)) - EXTS(smul(rs1_half_bottom, rs2_half_top)),
      SMSLDA   =>   EXTS(smul(rs1_half_top, rs2_half_top)) - EXTS(smul(rs1_half_bottom, rs2_half_bottom)),
      SMSLXDA  =>   EXTS(smul(rs1_half_top, rs2_half_bottom)) - EXTS(smul(rs1_half_bottom, rs2_half_top))
    };
  if sizeof(xlen) == 32
  then {
    result = result + (X(rd | 0b00001) @ X(rd & 0b11110));
    X(rd | 0b00001) = result[63..32];
    X(rd & 0b11110) = result[31..0];
  }
  else {
    X(rd) = X(rd) + result;
  };
  RETIRE_SUCCESS
}
*/
mapping p_16bits_mul_64bits_add_sub_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    SMALBB   <-> "SMALBB",
    SMALBT   <-> "SMALBT",
    SMALTT   <-> "SMALTT",
    SMALDA   <-> "SMALDA",
    SMALXDA  <-> "SMALXDA",
    SMALDS   <-> "SMALDS",
    SMALDRS  <-> "SMALDRS",
    SMALXDS  <-> "SMALXDS",
    SMSLDA   <-> "SMSLDA",
    SMSLXDA  <-> "SMSLXDA"
}

mapping clause assembly = PEXT_INST_16BITS_MUL_64BITS_ADD_SUB(rs2, rs1, rd, p_inst)
  <-> p_16bits_mul_64bits_add_sub_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)