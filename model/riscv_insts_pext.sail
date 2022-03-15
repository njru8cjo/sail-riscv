/* 
16-bit ALU Instructions
*/

/* ############ */
union clause ast = PEXT_ALU_CMP_16  : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, RADD16) <->
  0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, ADD16) <->
  0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, KADD16) <->
  0b0001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, KSUB16) <->
  0b0001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, RSUB16) <->
  0b0000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SUB16) <->
  0b0100001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UKADD16) <->
  0b0011000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UKSUB16) <->
  0b0011001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, URADD16) <->
  0b0010000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, URSUB16) <->
  0b0010001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, CMPEQ16) <->
  0b0100110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, KSLL16) <->
  0b0110010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, KSLRA16) <->
  0b0101011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, KSLRA16_U) <->
  0b0110011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SCMPLE16) <->
  0b0001110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SCMPLT16) <->
  0b0000110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SLL16) <->
  0b0101010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SMAX16) <->
  0b1000001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SMIN16) <->
  0b1000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SRA16) <->
  0b0101000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SRA16_U) <->
  0b0110000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SRL16) <->
  0b0101001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, SRL16_U) <->
  0b0110001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UCMPLE16) <->
  0b0011110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UCMPLT16) <->
  0b0010110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UMAX16) <->
  0b1001001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ALU_CMP_16 (rs2, rs1, rd, UMIN16) <->
  0b1001000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111


function clause execute (PEXT_ALU_CMP_16 (rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_half =  slice(rs1_val, i, 16);
    let rs2_half =  slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      ADD16     => rs1_half + rs2_half,
      RADD16    => radd(rs1_half,rs2_half),
      URADD16   => uradd(rs1_half,rs2_half),
      KADD16    => kadd(rs1_half,rs2_half), 
      UKADD16   => ukadd(rs1_half,rs2_half),
      SUB16     => rs1_half - rs2_half,
      RSUB16    => rsub(rs1_half,rs2_half),
      URSUB16   => ursub(rs1_half,rs2_half),
      KSUB16    => ksub(rs1_half,rs2_half),
      UKSUB16   => uksub(rs1_half,rs2_half),
      SLL16     => shift_left_logic(rs1_half, 0x0 @ X(rs2)[3..0]),
      KSLL16    => kshift_left_logic(rs1_half, 0x0 @ X(rs2)[3..0]),
      KSLRA16   => kslra(rs1_half, EXTS(X(rs2)[4..0])),
      KSLRA16_U => kslra_u(rs1_half, EXTS(X(rs2)[4..0])),
      SRA16     => shift_right_arith(rs1_half, 0x0 @ X(rs2)[3..0]),
      SRA16_U   => shift_right_arith_u(rs1_half, 0x0 @ X(rs2)[3..0]),
      SRL16     => shift_right_logic(rs1_half, 0x0 @ X(rs2)[3..0]),
      SRL16_U   => shift_right_logic_u(rs1_half, 0x0 @ X(rs2)[3..0]),
      CMPEQ16   => if   rs1_half == rs2_half 
                   then 0xFFFF 
                   else 0x0000,
      SCMPLT16  => if   signed(rs1_half) < signed(rs2_half)
                   then 0xFFFF
                   else 0x0000,
      SCMPLE16  => if   signed(rs1_half) <= signed(rs2_half)
                   then 0xFFFF
                   else 0x0000,
      UCMPLT16  => if   unsigned(rs1_half) < unsigned(rs2_half)
                   then 0xFFFF
                   else 0x0000,
      UCMPLE16  => if   unsigned(rs1_half) <= unsigned(rs2_half)
                   then 0xFFFF
                   else 0x0000,
      SMAX16    => if   rs2_half <_s rs1_half then rs1_half
                   else rs2_half,
      SMIN16    => if   rs1_half <_s rs2_half then rs1_half
                   else rs2_half,
      UMAX16    => if   rs2_half <_u rs1_half then rs1_half
                   else rs2_half,
      UMIN16    => if   rs1_half <_u rs2_half then rs1_half
                   else rs2_half
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ALU16_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    ADD16     <-> "ADD16",
    RADD16    <-> "RADD16",
    URADD16   <-> "URADD16",
    KADD16    <-> "KADD16",
    UKADD16   <-> "UKADD16",
    SUB16     <-> "SUB16",
    RSUB16    <-> "RSUB16",
    URSUB16   <-> "URSUB16",
    KSUB16    <-> "KSUB16",
    UKSUB16   <-> "UKSUB16",
    SLL16     <-> "SLL16",
    KSLL16    <-> "KSLL16",
    KSLRA16   <-> "KSLRA16",
    KSLRA16_U <-> "KSLRA16_U",
    SRA16     <-> "SRA16",
    SRA16_U   <-> "SRA16_U",
    SRL16     <-> "SRL16",
    SRL16_U   <-> "SRL16_U",
    CMPEQ16   <-> "CMPEQ16",
    SCMPLT16  <-> "SCMPLT16",
    SCMPLE16  <-> "SCMPLE16",
    UCMPLT16  <-> "UCMPLT16",
    UCMPLE16  <-> "UCMPLE16",
    SMAX16    <-> "SMAX16",
    SMIN16    <-> "SMIN16",
    UMAX16    <-> "UMAX16",
    UMIN16    <-> "UMIN16"
}

mapping clause assembly = PEXT_ALU_CMP_16 (rs2, rs1, rd, p_inst)
  <-> p_ALU16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
 16bit Cross Instruction
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
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KHM16) <->
  0b1000011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_CROSS_16(rs2, rs1, rd, KHMX16) <->
  0b1001011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_CROSS_16(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_half_bottom =  slice(rs1_val, i, 16);
    let rs1_half_top =  slice(rs1_val, i+16, 16);   
    let rs2_half_bottom =  slice(rs2_val, i, 16);
    let rs2_half_top =  slice(rs2_val, i+16, 16);
    result[(i+31)..i] = match op {
      CRAS16   => rs1_half_top + rs2_half_bottom @ rs1_half_bottom - rs2_half_top,
      RCRAS16  => radd(rs1_half_top,rs2_half_bottom) @ rsub(rs1_half_bottom, rs2_half_top),
      URCRAS16 => uradd(rs1_half_top,rs2_half_bottom) @ ursub(rs1_half_bottom, rs2_half_top),
      KCRAS16  => kadd(rs1_half_top,rs2_half_bottom) @ ksub(rs1_half_bottom, rs2_half_top),
      UKCRAS16 => ukadd(rs1_half_top,rs2_half_bottom) @ uksub(rs1_half_bottom, rs2_half_top),
      CRSA16   => rs1_half_top - rs2_half_bottom @ rs1_half_bottom + rs2_half_top,
      RCRSA16  => rsub(rs1_half_top,rs2_half_bottom) @ radd(rs1_half_bottom, rs2_half_top),
      URCRSA16 => ursub(rs1_half_top,rs2_half_bottom) @ uradd(rs1_half_bottom, rs2_half_top),
      KCRSA16  => ksub(rs1_half_top,rs2_half_bottom) @ kadd(rs1_half_bottom, rs2_half_top),
      UKCRSA16 => uksub(rs1_half_top,rs2_half_bottom) @ ukadd(rs1_half_bottom, rs2_half_top),
      STAS16   => rs1_half_top + rs2_half_top @ rs1_half_bottom - rs2_half_bottom,
      RSTAS16  => radd(rs1_half_top, rs2_half_top) @ rsub(rs1_half_bottom, rs2_half_bottom),
      URSTAS16 => uradd(rs1_half_top, rs2_half_top) @ ursub(rs1_half_bottom, rs2_half_bottom),
      KSTAS16  => kadd(rs1_half_top, rs2_half_top) @ ksub(rs1_half_bottom, rs2_half_bottom),
      UKSTAS16 => ukadd(rs1_half_top, rs2_half_top) @ uksub(rs1_half_bottom, rs2_half_bottom),
      STSA16   => rs1_half_top - rs2_half_top   @ rs1_half_bottom + rs2_half_bottom,
      RSTSA16  => rsub(rs1_half_top, rs2_half_top) @ radd(rs1_half_bottom, rs2_half_bottom),
      URSTSA16 => ursub(rs1_half_top, rs2_half_top) @ uradd(rs1_half_bottom, rs2_half_bottom),
      KSTSA16  => ksub(rs1_half_top, rs2_half_top) @ kadd(rs1_half_bottom, rs2_half_bottom),
      UKSTSA16 => uksub(rs1_half_top, rs2_half_top) @ ukadd(rs1_half_bottom, rs2_half_bottom),
      KHM16    => khm (rs1_half_top, rs2_half_top) @ khm (rs1_half_bottom, rs2_half_bottom), 
      KHMX16   => khm (rs1_half_top, rs2_half_bottom) @ khm (rs1_half_bottom, rs2_half_top)
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
    KHM16    <-> "KHM16",
    KHMX16   <-> "KHMX16"
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
  let rs1_half_bottom =  slice(rs1_val, 0, 16);
  let rs1_half_top =  slice(rs1_val, 16, 16);
  let rs2_half_bottom =  slice(rs2_val, 0, 16);
  let rs2_half_top =  slice(rs2_val, 16, 16);
  if sizeof(xlen) == 32 
  then {
    let rd0 = (rd >> 1) << 1 ;
    let rd1 = rd0 + 1 ;
    result : xlenbits = zeros();
    result1 : xlenbits = zeros();
    Zero : xlenbits = zeros();
    match (op) {
      SMUL16  => {
        result  =  smul (rs1_half_bottom, rs2_half_bottom);
        result1 =  smul (rs1_half_top, rs2_half_top)
      },
      SMULX16 => {
        result  =  smul (rs1_half_bottom, rs2_half_top);
        result1 =  smul (rs1_half_top, rs2_half_bottom)
        },
      UMUL16  => {
        result  =  umul (rs1_half_bottom, rs2_half_bottom);
        result1 =  umul (rs1_half_top, rs2_half_top)
        },
      UMULX16 => {
        result  =  umul (rs1_half_bottom, rs2_half_top);
        result1 =  umul (rs1_half_top, rs2_half_bottom)
        }
      };
    X(rd0) = result;
    X(rd1) = result1;
    RETIRE_SUCCESS
  }
  else  {
    result : xlenbits = zeros();
    result = match (op) {
      SMUL16  => smul(rs1_half_top, rs2_half_top) @ smul(rs1_half_bottom, rs2_half_bottom),
      SMULX16 => smul(rs1_half_top, rs2_half_bottom) @ smul(rs1_half_bottom, rs2_half_top),
      UMUL16  => umul(rs1_half_top, rs2_half_top) @ umul(rs1_half_bottom, rs2_half_bottom),
      UMULX16 => umul(rs1_half_top, rs2_half_bottom) @ umul(rs1_half_bottom, rs2_half_top)
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
union clause ast = PEXT_IMM4  : (bits(4), regidx, regidx, p_inst_imm4_rs1_rd_op)
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, KSLLI16) <->
  0b0111010 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SCLIP16) <->
  0b1000010 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SLLI16) <->
  0b0111010 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SRAI16) <->
  0b0111000 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SRAI16_U) <->
  0b0111000 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SRLI16) <->
  0b0111001 @ 0b0 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, SRLI16_U) <->
  0b0111001 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_IMM4 (imm4, rs1, rd, UCLIP16) <->
  0b1000010 @ 0b1 @ imm4 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_IMM4 (imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_half =  slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      KSLLI16  =>  kshift_left_logic(rs1_half, sa),
      SCLIP16  =>  sclip(rs1_half, sa),
      SLLI16   =>  shift_left_logic(rs1_half, sa),
      SRAI16   =>  shift_right_arith(rs1_half, sa),
      SRAI16_U =>  shift_right_arith_u(rs1_half, sa),
      SRLI16   =>  shift_right_logic(rs1_half, sa),
      SRLI16_U =>  shift_right_logic_u(rs1_half, sa),
      UCLIP16  =>  uclip(rs1_half, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_imm4_rs1_rd_mapping : p_inst_imm4_rs1_rd_op <-> string = {
  KSLLI16  <-> "KSLLI16",
  SCLIP16  <-> "SCLIP16",
  SLLI16   <-> "SLLI16",
  SRAI16   <-> "SRAI16",
  SRAI16_U <-> "SRAI16_U",
  SRLI16   <-> "SRLI16",
  SRLI16_U <-> "SRLI16_U",
  UCLIP16  <-> "UCLIP16"
}

mapping clause assembly = PEXT_IMM4 (imm4, rs1, rd, p_inst)
  <-> p_inst_imm4_rs1_rd_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

/* 16bits one register instructions */
union clause ast = PEXT_ONE_REGISTER_16  : (regidx, regidx, p_inst_rs1_rd_op)

mapping clause encdec = PEXT_ONE_REGISTER_16 (rs1, rd, CLRS16) <->
  0b1010111 @ 0b01000 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ONE_REGISTER_16 (rs1, rd, CLO16) <->
  0b1010111 @ 0b01011 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ONE_REGISTER_16 (rs1, rd, CLZ16) <->
  0b1010111 @ 0b01001 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_ONE_REGISTER_16 (rs1, rd, KABS16) <->
  0b1010110 @ 0b10001 @ rs1 @ 0b000 @ rd @ 0b1110111

function clause execute (PEXT_ONE_REGISTER_16 (rs1, rd, op)) = {
  let rs1_val = X(rs1);
  result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_half = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      CLRS16    => clrs(rs1_half),
      CLO16     => clo(rs1_half),
      CLZ16     => clz(rs1_half),
      KABS16    => kabs(rs1_half)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_inst_rs1_rd_16_mapping : p_inst_rs1_rd_op <-> string = {
  CLRS16 <-> "CLRS16",
  CLO16  <-> "CLO16",
  CLZ16  <-> "CLZ16",
  KABS16 <-> "KABS16"
}

mapping clause assembly = PEXT_ONE_REGISTER_16 (rs1, rd, p_inst)
  <-> p_inst_rs1_rd_16_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
