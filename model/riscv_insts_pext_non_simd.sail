
val q15 : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15 (v) =
  let ub : bits(33) = EXTS(0x7FFF) in
  let lb : bits(33) = EXTS(0x8000) in
  if v <_s lb then { pext_write_OV (0b1); 0x8000;}
  else if ub <_s v then { pext_write_OV (0b1); 0x7FFF;}
  else v[15..0]

val q15_l_u : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15_l_u (v) =
  let ub : bits(33) = EXTZ(0xFFFF) in
  if ub <_u v then { pext_write_OV (0b1); 0xFFFF;}
  else v[15..0]

val q15_s_u : 
  bits(33) -> bits(16) effect {rreg, wreg}
function q15_s_u (v) =
  let ub : bits(33) = EXTZ(0xFFFF) in
  let lb : bits(33) = EXTZ(0x0000) in
  if ub <_s v then { pext_write_OV (0b1); 0xFFFF;}
  else if v <_s lb then { pext_write_OV (0b1); 0x0000;}
  else v[15..0]
  
val sshm :
  (bits(16), bits(16)) -> bits(16) effect {rreg, wreg}
function sshm (v1, v2)=
  if (v1 != 0x8000) | (v2 != 0x8000)
  then 
  let res : bits(32) = to_bits(32, signed(v1) * signed(v2)) in
  let rshift : bits(32) = EXTS(res >> 15) in 
  rshift[15..0]
  else { pext_write_OV (0b1); 0x7FFF;}

/*
2.5.1. Q15 saturation instructions
*/

union clause ast = PEXT_Q15 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_Q15(rs2, rs1, rd, KADDH)  <->
  0b0000010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, KSUBH)  <->
  0b0000011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, KHMBB)  <->
  0b0000110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, KHMBT)  <->
  0b0001110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, KHMTT)  <->
  0b0010110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, UKADDH) <->
  0b0001010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q15(rs2, rs1, rd, UKSUBH) <->
  0b0001011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111


function clause execute (PEXT_Q15(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();
  tmp : bits(33) = zeros();
  result = match op {
      KADDH   => { tmp = add_bits(EXTS(slice(rs1_val,0,32)), EXTS(slice(rs2_val,0,32))) ; EXTS(q15(tmp)) }, 
      KSUBH   => { tmp = sub_bits(EXTS(slice(rs1_val,0,32)), EXTS(slice(rs2_val,0,32))) ; EXTS(q15(tmp)) }, 
      KHMBB   => EXTS(sshm(slice(rs1_val,0,16), slice(rs2_val,0,16))),
      KHMBT   => EXTS(sshm(slice(rs1_val,0,16), slice(rs2_val,16,16))),
      KHMTT   => EXTS(sshm(slice(rs1_val,16,16), slice(rs2_val,16,16))),
      UKADDH  => { tmp = add_bits(EXTZ(slice(rs1_val,0,32)), EXTZ(slice(rs2_val,0,32))) ; EXTS(q15_l_u(tmp)) }, 
      UKSUBH  => { tmp = sub_bits(EXTZ(slice(rs1_val,0,32)), EXTZ(slice(rs2_val,0,32))) ; EXTS(q15_s_u(tmp)) }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_q15_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    KADDH     <-> "KADDH ",
    KSUBH    <-> "KSUBH ",
    KHMBB   <-> "KHMBB ",
    KHMBT    <-> "KHMBT ",
    KHMTT   <-> "KHMTT ",
    UKADDH     <-> "UKADDH ",
    UKSUBH    <-> "UKSUBH "
}

mapping clause assembly = PEXT_Q15(rs2, rs1, rd, p_inst)
  <-> p_q15_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/*
2.5.2. Q31 saturation Instructions
KSLLIW  write in imm5
KABSW write in rd rs1 
*/

val kdm :
  (bits(16), bits(16)) -> bits(32) effect {rreg,wreg}
function kdm (v1, v2) =
  let lb : bits(16) = not_vec(EXTS(sail_ones (16) >> 1)) in
  if v1 == lb & v2 == lb then { pext_write_OV (0b1); ones (32) >> 1 }
  else { to_bits (31, signed(v1) * signed(v2)) @ 0b0 }

val kdmaw :
  (bits(16), bits(16), bits(32)) -> bits(32) effect {rreg,wreg}
function kdmaw (v1, v2, rd) = {
  let resQ31 : bits(32) = kdm(v1, v2);
  let tmp : bits(33) = EXTS(resQ31) + EXTS(rd);
  let ub : bits(33) = EXTS(sail_ones (32) >> 1) in
  let lb : bits(33) = not_vec (ub) in
  if tmp <_s lb then { pext_write_OV (0b1); not_vec (ones (32) >> 1) }
  else if ub <_s tmp then { pext_write_OV (0b1); ones (32) >> 1 }
  else { slice (tmp, 0, 32) }
}

union clause ast = PEXT_Q31 : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KADDW) <->
  0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, UKADDW) <->
  0b0001000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KSUBW) <->
  0b0000001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, UKSUBW) <->
  0b0001001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMBB) <->
  0b0000101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMBT) <->
  0b0001101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMTT) <->
  0b0010101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KSLRAW) <->
  0b0110111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KSLRAW_U) <->
  0b0111111 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KSLLW) <->
  0b0010011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMABB) <->
  0b1101001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMABT) <->
  0b1110001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_Q31(rs2, rs1, rd, KDMATT) <->
  0b1111001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111





function clause execute (PEXT_Q31(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val  = X(rd);
  result : xlenbits = zeros();
  result = match op {
      KADDW     => kadd(slice(rs1_val,0,32), slice(rs2_val,0,32)),
      UKADDW    => ukadd(slice(rs1_val,0,32), slice(rs2_val,0,32)),
      KSUBW     => ksub(slice(rs1_val,0,32), slice(rs2_val,0,32)),
      UKSUBW    => uksub(slice(rs1_val,0,32), slice(rs2_val,0,32)),
      KDMBB     => kdm(slice(rs1_val, 0, 16), slice(rs2_val, 0, 16)),
      KDMBT     => kdm(slice(rs1_val, 0, 16), slice(rs2_val, 16, 16)),
      KDMTT     => kdm(slice(rs1_val, 16, 16), slice(rs2_val, 16, 16)),
      KSLRAW    => { let sa : bits(8) = EXTS(X(rs2)[5..0]); kslra (slice(rs1_val, 0, 32), sa) },
      KSLRAW_U  => { let sa : bits(8) = EXTS(X(rs2)[5..0]); kslra_u (slice(rs1_val, 0, 32), sa) },
      KSLLW     => { let sa : bits(8) = EXTZ(X(rs2)[4..0]); kshift_left_logic (slice(rs1_val, 0, 32), sa) },
      KDMABB    => kdmaw(slice(rs1_val, 0, 16), slice(rs2_val, 0, 16), slice(rd_val, 0, 32)),
      KDMABT    => kdmaw(slice(rs1_val, 0, 16), slice(rs2_val, 16, 16), slice(rd_val, 0, 32)),
      KDMATT    => kdmaw(slice(rs1_val, 16, 16), slice(rs2_val, 16, 16), slice(rd_val, 0, 32))
  };
  if sizeof(xlen) == 32
  then {
      X(rd) = result;
      RETIRE_SUCCESS
  }
  else {
      X(rd) = EXTS(result);
      RETIRE_SUCCESS
  }
}

mapping p_q31_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    KADDW    <-> "KADDW ",
    UKADDW   <-> "UKADDW",
    KSUBW    <-> "KSUBW ",
    UKSUBW   <-> "UKSUBW ",
    KDMBB    <-> "KDMBB ",
    KDMBT    <-> "KDMBT ",
    KDMTT    <-> "KDMTT ",
    KSLRAW   <-> "KSLRAW ",
    KSLRAW_U <-> "KSLRAW_U ",
    KSLLW    <-> "KSLLW ",
    KDMABB   <-> "KDMABB ",
    KDMABT   <-> "KDMABT ",
    KDMATT   <-> "KDMATT "
}

mapping clause assembly = PEXT_Q31(rs2, rs1, rd, p_inst)
  <-> p_q31_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/*
2.5.3. 32-bit Computation Instructions
*/
val umul33_64 :
  (bits(33), bits(33)) -> bits(64)
function umul33_64 (v1, v2) =
  to_bits (66, unsigned(v1) * unsigned(v2))[63..0]

val mul32_64 :
  (bits(32), bits(32)) -> bits(64)
function mul32_64 (v1, v2) =
  to_bits (64, signed(v1) * signed(v2))

val mulb :
  (bits(32), bits(32)) -> bits(32)
function mulb (v1, v2) =
  to_bits (64, unsigned(v1) * unsigned(v2))[31..0]


union clause ast = PEXT_32_COMPUTE : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, RADDW) <->
  0b0010000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, URADDW) <->
  0b0011000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, RSUBW) <->
  0b0010001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, URSUBW) <->
  0b0011001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, MAXW) <->
  0b1111001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, MINW) <->
  0b1111000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_COMPUTE(rs2, rs1, rd, MSUBR32) <->
  0b1100011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111



function clause execute (PEXT_32_COMPUTE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_32  = slice(rs1_val, 0, 32);
  let rs2_32  = slice(rs2_val, 0, 32);
  result : bits(32) = zeros();
  result = match op {
        MAXW      => if rs1_32 <_s rs2_32 then rs2_32 else rs1_32,
        MINW      => if rs1_32 <_s rs2_32 then rs1_32 else rs2_32,
        MSUBR32   => sub_bits(slice (X(rd), 0, 32),  mulb(rs1_32, rs2_32)),
        RADDW     => { let res : bits(33) = add_bits(EXTS(rs1_32), EXTS(rs2_32)); slice (res, 1, 32) },
        RSUBW     => { let res : bits(33) = sub_bits(EXTS(rs1_32), EXTS(rs2_32)); slice (res, 1, 32) },
        URADDW    => { let res : bits(33) = add_bits(EXTZ(rs1_32), EXTZ(rs2_32)); slice (res, 1, 32) },
        URRSUBW   => { let res : bits(33) = sub_bits(EXTZ(rs1_32), EXTZ(rs2_32)); slice (res, 1, 32) }

    };  
  if sizeof(xlen) == 32
  then {
      X(rd) = result;
      RETIRE_SUCCESS
  }
  else {
      X(rd) = EXTS(result);
      RETIRE_SUCCESS
  }
  
}

mapping p_32_compute_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    RADDW    <-> "RADDW ",
    URADDW    <-> "URADDW ",
    RSUBW    <-> "RSUBW ",
    URSUBW    <-> "URSUBW ",
    MAXW    <-> "MAXW ",
    MINW    <-> "MINW ",
    MSUBR32   <-> "MSUBR32 "
}

mapping clause assembly = PEXT_32_COMPUTE(rs2, rs1, rd, p_inst)
  <-> p_32_compute_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)



union clause ast = PEXT_32_PAIR_RD_COMPUTE : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_32_PAIR_RD_COMPUTE(rs2, rs1, rd, MULR64) <->
  0b1111000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_32_PAIR_RD_COMPUTE(rs2, rs1, rd, MULSR64) <->
  0b1110000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_32_PAIR_RD_COMPUTE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rs1_32  = slice(rs1_val, 0, 32);
  let rs2_32  = slice(rs2_val, 0, 32);
  result : bits(64) = zeros();  
  result = match op {
          MULR64  => umul33_64(EXTZ(rs1_32), EXTZ(rs2_32)),
          MULSR64 => mul32_64(rs1_32, rs2_32)
    };

  if sizeof(xlen) == 32
  then {
      let rd0 = (rd >> 1) << 1 ;
      let rd1 = rd0 + 1 ;
      X(rd0) = result[31..0]; 
      X(rd1) = result[63..32];
  }
  else X(rd) = result;  

  RETIRE_SUCCESS
}

mapping p_32_pair_compute_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    MULR64    <-> "MULR64 ",
    MULSR64    <-> "MULSR64 "
}

mapping clause assembly = PEXT_32_PAIR_RD_COMPUTE(rs2, rs1, rd, p_inst)
  <-> p_32_pair_compute_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)


/*
2.5.5. Miscellaneous Instructions
SRAI BITREVI WEXTI write in imm5u
BPICK
INSB write in imm3u
*/

val bitrev32 :
  (bits(32)) -> bits(32)
function bitrev32 (v) = {
  var tmp : bits(64) = 0x0000 @ v @ 0x0000;
  tmp = 0x0000 @ ((tmp[48..17] & 0x55555555) | (tmp[46..15] & 0xAAAAAAAA)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[49..18] & 0x33333333) | (tmp[45..14] & 0xCCCCCCCC)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[51..20] & 0x0F0F0F0F) | (tmp[43..12] & 0xF0F0F0F0)) @ 0x0000;
  tmp = 0x0000 @ ((tmp[55..24] & 0x00FF00FF) | (tmp[39..8]  & 0xFF00FF00)) @ 0x0000;
  ((tmp[63..32] & 0x0000FFFF) | (tmp[31..0]  & 0xFFFF0000))
}

val bitrev64 :
  (bits(64)) -> bits(64)
function bitrev64 (v) = {
  var tmp : bits(128) = 0x00000000 @ v @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[96..33]  & 0x5555555555555555) | (tmp[94..31] & 0xAAAAAAAAAAAAAAAA)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[97..34]  & 0x3333333333333333) | (tmp[93..30] & 0xCCCCCCCCCCCCCCCC)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[99..36]  & 0x0F0F0F0F0F0F0F0F) | (tmp[91..28] & 0xF0F0F0F0F0F0F0F0)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[103..40] & 0x00FF00FF00FF00FF) | (tmp[87..24] & 0xFF00FF00FF00FF00)) @ 0x00000000;
  tmp = 0x00000000 @ ((tmp[111..48] & 0x0000FFFF0000FFFF) | (tmp[79..16] & 0xFFFF0000FFFF0000)) @ 0x00000000;
  ((tmp[127..64] & 0x00000000FFFFFFFF) | (tmp[63..0]  & 0xFFFFFFFF00000000))
}

union clause ast = PEXT_NONSIMD_MISC : (regidx, regidx, regidx, p_inst_rs2_rs1_rd_op)

mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, AVE) <->
  0b1110000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, SRA_U) <->
  0b0010010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, BITREV) <->
  0b1110011 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, WEXT) <->
  0b1100111 @ rs2 @ rs1 @ 0b000 @ rd @ 0b1110111
mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, MADDR32) <->
  0b1100010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111
mapping clause encdec = PEXT_NONSIMD_MISC(rs2, rs1, rd, MSUBR32) <->
  0b1100011 @ rs2 @ rs1 @ 0b001 @ rd @ 0b1110111

function clause execute (PEXT_NONSIMD_MISC(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  result : xlenbits = zeros();  

  if sizeof(xlen) == 32
  then {
       result = match op {
          AVE     => { let tmp : bits(xlen + 1) = EXTS(rs1_val) + EXTS(rs2_val) + EXTS(0x1); tmp[32..1] },
          SRA_U   => { let sa : bits(8)  = EXTZ(X(rs2)[4..0]) ; shift_right_arith_u (rs1_val, sa)},
          BITREV  => { let msb : bits(8) = EXTZ(rs2_val[4..0]) ; shift_right_logic(bitrev32(rs1_val), 0x1F - msb)},
          MADDR32 =>  X(rd) + smul(rs1_val, rs2_val)[31..0],
          MSUBR32 =>  X(rd) - smul(rs1_val, rs2_val)[31..0]
        };
    }
   else {
       result = match op {
          AVE     => { let tmp : bits(xlen + 1) = EXTS(rs1_val) + EXTS(rs2_val) + EXTS(0x1); tmp[64..1] },
          SRA_U   => { let sa  : bits(8)  = EXTZ(X(rs2)[5..0]) ; shift_right_arith_u (rs1_val, sa)},
          BITREV  => { let msb : bits(8) = EXTZ(rs2_val[5..0]) ; shift_right_logic(bitrev64(rs1_val), 0x3F - msb)},
          MADDR32 =>  EXTS(X(rd) + smul(rs1_val, rs2_val)[31..0]),
          MSUBR32 =>  EXTS(X(rd) - smul(rs1_val, rs2_val)[31..0])
       }
   };
   X(rd) = result;
   RETIRE_SUCCESS

/*32
          WEXT    => { let rs10 = (rs1 >> 1) << 1 ; let rs11 = rs10 + 1 ;
                                 let lsb : byte = EXTZ(rB(rs2, 0)[4..0]); EXTS(shift_right_logic(rs1_val, lsb)[31..0]) } ,

  64
          WEXT    => { let lsb : byte = EXTZ(rB(rs2, 0)[4..0]); EXTS(shift_right_logic(rs1_val, lsb)[31..0]) } ,

*/

    
}

mapping p_nonsimd_misc_mapping : p_inst_rs2_rs1_rd_op <-> string = {
    AVE     <-> "AVE ",
    SRA_U    <-> "SRA_U ",
    BITREV    <-> "BITREV ",
    MADDR32    <-> "MADDR32 ",
    MSUBR32    <-> "MSUBR32 "
}

mapping clause assembly = PEXT_NONSIMD_MISC(rs2, rs1, rd, p_inst)
  <-> p_32_pair_compute_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
