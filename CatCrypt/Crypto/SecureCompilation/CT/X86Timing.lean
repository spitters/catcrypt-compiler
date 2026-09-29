/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore

/-!
# The x86 timing table of the owned backends

The vendor allowlist for instruction timing on x86. An instruction is data-operand
independent (`TimingClass.doit`) when it is on Intel's Data Operand Independent
Timing list, document ID 768547, "Data Operand Independent Timing Instructions",
last updated 2026-02-23 (retrieved 2026-09-28):
https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html

Under that document, with DOITM enabled (`IA32_UARCH_MISC_CTL[0]`, MSR 1B01H), or
on a Core or Atom processor that does not enumerate `IA32_UARCH_MISC_CTL`, a listed
instruction executes in a number of cycles independent of the data values in its
register, flag and mask sources. The guarantee excludes memory addresses (which
the leakage model records separately as address events), immediates and other
code bytes, masked memory operations and the `REP` string forms, and says nothing
about power, thermal or frequency channels.

Every instruction that is not on the list is `TimingClass.varTime`: its data
operands are observable. Control transfers are `TimingClass.control`: their
outcome is observable as a branch event, not as an operand event.

* `X86Mnem` is one constructor per mnemonic the owned x86 backends emit, plus
  `div` and `idiv`, which no owned path emits and which carry the classification
  of the division that `VarTimeOpDetector` names.
* `SimdMnem` lists the SIMD mnemonics of the AVX2, AVX-512 and crypto-extension
  paths.
* `X86Mnem.timing` is the table, one group per block of the Intel list, each
  group's docstring naming the table entries and opcode bytes.
* `JInstr.mnem` and `YmmOp.mnem` project the backend's instruction types onto
  the table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

/-! ## 1. Timing classes -/

/-- The timing class of an instruction under the vendor allowlist. -/
inductive TimingClass where
  /-- On Intel's DOIT list (document 768547, 2026-02-23): the latency is
      independent of the register, flag and mask inputs while DOITM holds. -/
  | doit
  /-- Not on the list: every data operand is observable. -/
  | varTime
  /-- A control transfer, observable through its branch outcome. -/
  | control
  deriving DecidableEq, Repr

/-! ## 2. Mnemonics -/

/-- The SIMD mnemonics emitted by the owned x86 backends: the AVX2 path
    (`YmmOp` and `YmmInstr`), the AVX-512 path (`ZmmTextModel.Instr`) and the
    crypto-extension encoders (`CryptoExtEncoder`). Immediates and lane widths
    are operands, not constructors. -/
inductive SimdMnem where
  -- AVX2 path
  | vpmuldq | vmovshdup | vpsubq | vpaddd | vpsubd | vpblendd | vpshufd | vpermq
  | vpmuludq | vpaddq | vpmullq | vpand | vpor | vpxor | vpshufb | vpsrlq | vpsllq
  | vpsrld | vpslld | vpsrlvd | vpsllvd | vpandn | vprolq | vpmulld | vpsrad
  | vpaddw | vpsubw | vpmullw | vpmulhw | vpmaddwd | vpcmpgtw | vpcmpgtd | vpcmpeqd
  | vpsllw | vpsrlw | vpsraw | vpabsd | vpsignd | vpacksswb | vpackssdw | vpermd
  | vpunpckldq | vpunpckhdq | vpunpcklqdq | vpunpckhqdq | vpblendw | vpsrldq
  | vperm2i128 | vpsrlvq | vpsllvq | vmovdqu | vpternlogq
  -- AVX-512 path
  | vmovdqu64 | vmovdqa64 | vpbroadcastq | vpbroadcastd | vpblendmd | vprold
  | vpternlogd | vmovsldup | vpandq | vporq | vpxorq | vpandnq | vpminud | vpminuq
  | vpermt2q | vpermpd | vpslldq | vzeroupper | kmovw
  -- crypto extensions
  | sha256rnds2 | sha256msg1 | sha256msg2 | pclmulqdq | vpclmulqdq | vaesenc
  | vaesenclast | vaesdec | vaesdeclast | vaeskeygenassist | gf2p8mulb
  | gf2p8affineqb | vgf2p8mulb | vgf2p8affineqb | vpaddb
  deriving DecidableEq, Repr

/-- The x86 mnemonics of the owned backends, one constructor per mnemonic;
    condition codes, operand widths and addressing forms are operands of the
    instruction, not constructors. `div` and `idiv` are not emitted by any owned
    path; they are present so that division has a row in the table. -/
inductive X86Mnem where
  | mov | add | sub | adc | sbb | imul | mul | neg | not | inc | dec
  | and | or | xor | test | cmp | andn
  | rol | ror | rorx | shl | shr | sar | shlx | shrx | sarx | shld | shrd | rcl | rcr
  | movzx | movsx | movsxd | lea | setcc | cmovcc | mulx | adcx | adox
  | bt | btr | bts | bzhi | xchg | clc | stc | push | pop
  | div | idiv
  | jmp | jcc | call | ret
  | simd (m : SimdMnem)
  deriving DecidableEq, Repr

/-! ## 3. The table -/

/-- The timing class of a SIMD mnemonic. Every SIMD mnemonic the backends emit
    is on the DOIT list (document 768547, 2026-02-23). -/
def SimdMnem.timing : SimdMnem → TimingClass
  /- DOIT list, packed integer (legacy encodings with their V forms):
     PADDB/W/D/Q, PSUBW/D/Q, PMULDQ, PMULUDQ, PMULLD, PMULLW, PMULHW, PMADDWD,
     PAND, PANDN, POR, PXOR, PSHUFB, PSHUFD, PSLLW/D/Q, PSLLDQ, PSRLW/D/Q, PSRLDQ,
     PSRAW/D, PCMPGTW/D, PCMPEQD, PABSD, PSIGND, PACKSSWB, PACKSSDW, PBLENDW,
     PUNPCK{L,H}{DQ,QDQ}; legacy SSE moves MOVSHDUP, MOVSLDUP. -/
  | .vpmuldq | .vmovshdup | .vpsubq | .vpaddd | .vpsubd | .vpshufd | .vpmuludq
  | .vpaddq | .vpand | .vpor | .vpxor | .vpshufb | .vpsrlq | .vpsllq | .vpsrld
  | .vpslld | .vpandn | .vpmulld | .vpsrad | .vpaddw | .vpsubw | .vpmullw
  | .vpmulhw | .vpmaddwd | .vpcmpgtw | .vpcmpgtd | .vpcmpeqd | .vpsllw | .vpsrlw
  | .vpsraw | .vpabsd | .vpsignd | .vpacksswb | .vpackssdw | .vpunpckldq
  | .vpunpckhdq | .vpunpcklqdq | .vpunpckhqdq | .vpblendw | .vpsrldq | .vpslldq
  | .vmovsldup | .vpaddb => .doit
  /- DOIT list, VEX/EVEX only: VPBLENDD, VPERMQ, VPERMD, VPERM2I128, VPERMPD,
     VPERMT2Q, VPSRLVD/Q, VPSLLVD/Q, VPMULLQ, VPROLD/Q, VPTERNLOGD/Q, VMOVDQU8/16/
     32/64 and VMOVDQA32/64 (with the legacy MOVDQU), VPBROADCASTD/Q, VPBLENDMD,
     VPANDQ, VPORQ, VPXORQ, VPANDNQ, VPMINUD, VPMINUQ, VZEROUPPER; mask
     registers KMOVW. -/
  | .vpblendd | .vpermq | .vpermd | .vperm2i128 | .vpermpd | .vpermt2q | .vpsrlvd
  | .vpsllvd | .vpsrlvq | .vpsllvq | .vpmullq | .vprolq | .vprold | .vpternlogq
  | .vpternlogd | .vmovdqu | .vmovdqu64 | .vmovdqa64 | .vpbroadcastq
  | .vpbroadcastd | .vpblendmd | .vpandq | .vporq | .vpxorq | .vpandnq | .vpminud
  | .vpminuq | .vzeroupper | .kmovw => .doit
  /- DOIT list, crypto and carry-less: SHA256RNDS2, SHA256MSG1, SHA256MSG2,
     PCLMULQDQ, VPCLMULQDQ, VAESENC, VAESENCLAST, VAESDEC, VAESDECLAST,
     VAESKEYGENASSIST, GF2P8MULB, GF2P8AFFINEQB, VGF2P8MULB, VGF2P8AFFINEQB. -/
  | .sha256rnds2 | .sha256msg1 | .sha256msg2 | .pclmulqdq | .vpclmulqdq | .vaesenc
  | .vaesenclast | .vaesdec | .vaesdeclast | .vaeskeygenassist | .gf2p8mulb
  | .gf2p8affineqb | .vgf2p8mulb | .vgf2p8affineqb => .doit

/-- The timing table of the owned x86 mnemonics under the Intel DOIT allowlist
    (document 768547, 2026-02-23). -/
def X86Mnem.timing : X86Mnem → TimingClass
  /- DOIT list, general purpose arithmetic and logic: MOV (88–8B, A0–A3, B0–BF,
     C6, C7), ADD (00–05, 80–83), ADC (10–15, 80–83), SUB (28–2D, 80–83), SBB
     (18–1D, 80–83), IMUL (69, 6B, AF, F6, F7), MUL (F6, F7), NEG (F6, F7), NOT
     (F6, F7), INC (40–47, FE, FF), DEC (48–4F, FE, FF), AND (20–25, 80–83), OR
     (08–0D, 80–83), XOR (30–35, 80–83), TEST (84, 85, A8, A9, F6, F7), CMP
     (38–3D, 80–83), ANDN (F2). -/
  | .mov | .add | .sub | .adc | .sbb | .imul | .mul | .neg | .not | .inc | .dec
  | .and | .or | .xor | .test | .cmp | .andn => .doit
  /- DOIT list, shifts and rotates: ROL, ROR, SHL, SHR, SAR (C0, C1, D0–D3);
     RORX (F0); SHLX, SHRX (F7); SHLD (24, A4, A5); SHRD (2C, AC, AD). -/
  | .rol | .ror | .rorx | .shl | .shr | .sar | .shlx | .shrx | .shld | .shrd => .doit
  /- DOIT list, moves, flags to registers, conditional moves, wide multiply and
     carry chains, bit tests, stack: MOVZX (B6, B7), MOVSX (BE, BF), MOVSXD (63),
     LEA (8D), SETcc (90–9F), CMOVcc (40–4F), MULX (F6), ADCX (F6), ADOX (F6), BT
     (A3, BA), BTR (B3, BA), BTS (AB, BA), PUSH (50–57, 68, 6A, FF), POP (58–5F,
     8F). -/
  | .movzx | .movsx | .movsxd | .lea | .setcc | .cmovcc | .mulx | .adcx | .adox
  | .bt | .btr | .bts | .push | .pop => .doit
  /- Absent from the DOIT list: SARX (VEX.F3 F7), BZHI (VEX F5), XCHG (87), RCL
     and RCR (C0, C1, D0–D3 with /2, /3), CLC (F8), STC (F9), DIV and IDIV (F6,
     F7 with /6, /7). -/
  | .sarx | .bzhi | .xchg | .rcl | .rcr | .clc | .stc | .div | .idiv => .varTime
  /- Control transfers, observable through their branch outcome: JMP (E9), Jcc
     (0F 80–8F), CALL (E8), RET (C3). -/
  | .jmp | .jcc | .call | .ret => .control
  | .simd m => m.timing

/-- A mnemonic is data-operand independent when the table classes it `doit`. -/
def X86Mnem.isDataIndependent (m : X86Mnem) : Bool :=
  match m.timing with
  | .doit => true
  | _ => false

theorem X86Mnem.isDataIndependent_iff (m : X86Mnem) :
    m.isDataIndependent = true ↔ m.timing = .doit := by
  unfold X86Mnem.isDataIndependent
  cases m.timing <;> simp

/-- Every SIMD mnemonic the backends emit is data-operand independent. -/
theorem SimdMnem.timing_eq_doit (m : SimdMnem) : m.timing = .doit := by
  cases m <;> rfl

/-- The mnemonics the table classes variable time are exactly `sarx`, `bzhi`,
    `xchg`, `rcl`, `rcr`, `clc`, `stc`, `div` and `idiv`. -/
theorem X86Mnem.timing_eq_varTime_iff (m : X86Mnem) :
    m.timing = .varTime ↔
      m = .sarx ∨ m = .bzhi ∨ m = .xchg ∨ m = .rcl ∨ m = .rcr ∨ m = .clc ∨
        m = .stc ∨ m = .div ∨ m = .idiv := by
  cases m <;> simp [X86Mnem.timing, SimdMnem.timing_eq_doit]

/-! ## 4. Projections from the backend's instruction types -/

/-- The mnemonic of a scalar `JInstr`. The memory forms carry the mnemonic of
    their register form (`loadMem` is `MOV 8B`, `addMem` is `ADD 03`); `setc` is
    `SETB` followed by `MOVZX`, both `doit`, and is classed as `setcc`;
    `loadSym` is a RIP-relative `LEA`. -/
def _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.JInstr.mnem {w : Nat} :
    JInstr w → X86Mnem
  | .mov _ _ => .mov
  | .add _ _ => .add
  | .sub _ _ => .sub
  | .adc _ _ => .adc
  | .sbb _ _ => .sbb
  | .imul _ _ => .imul
  | .neg _ => .neg
  | .setc _ => .setcc
  | .and_ _ _ => .and
  | .test _ _ => .test
  | .cmp _ _ => .cmp
  | .not_ _ => .not
  | .andn _ _ _ => .andn
  | .rol _ _ => .rol
  | .ror _ _ => .ror
  | .rorx _ _ _ => .rorx
  | .shlx _ _ _ => .shlx
  | .shrx _ _ _ => .shrx
  | .sarx _ _ _ => .sarx
  | .movzx _ _ _ => .movzx
  | .movsx _ _ _ => .movsx
  | .lea _ _ _ _ _ => .lea
  | .or_ _ _ => .or
  | .xor_ _ _ => .xor
  | .shl _ _ => .shl
  | .shr _ _ => .shr
  | .sar _ _ => .sar
  | .cmove _ _ => .cmovcc
  | .cmovne _ _ => .cmovcc
  | .cmovb _ _ => .cmovcc
  | .mulx _ _ _ _ => .mulx
  | .mulxMem _ _ _ _ _ => .mulx
  | .adcx _ _ => .adcx
  | .adox _ _ => .adox
  | .loadMem _ _ _ => .mov
  | .storeMem _ _ _ => .mov
  | .loadMemIdx _ _ _ _ => .mov
  | .storeMemIdx _ _ _ _ => .mov
  | .loadSym _ _ => .lea
  | .inc _ => .inc
  | .dec _ => .dec
  | .clc => .clc
  | .stc => .stc
  | .xchg _ _ => .xchg
  | .imulri _ _ _ => .imul
  | .mul _ _ _ => .mul
  | .imulWide _ _ _ => .imul
  | .shld _ _ _ => .shld
  | .shrd _ _ _ => .shrd
  | .rcl _ _ => .rcl
  | .rcr _ _ => .rcr
  | .cmovcc _ _ _ => .cmovcc
  | .setcc _ _ => .setcc
  | .testN _ _ _ => .test
  | .bt _ _ => .bt
  | .btr _ _ => .btr
  | .bts _ _ => .bts
  | .addMem _ _ _ => .add
  | .addToMem _ _ _ => .add
  | .adcxMem _ _ _ => .adcx
  | .adoxMem _ _ _ => .adox
  | .imulMem _ _ _ => .imul
  | .imulriMem _ _ _ _ => .imul
  | .cmpMem _ _ _ => .cmp
  | .bzhi _ _ _ => .bzhi

/-- The SIMD mnemonic of an AVX2 dialect op. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect.YmmOp.simdMnem :
    YmmOp → SimdMnem
  | .vpmuldq => .vpmuldq
  | .vmovshdup => .vmovshdup
  | .vpsubq => .vpsubq
  | .vpaddd => .vpaddd
  | .vpsubd => .vpsubd
  | .vpblendd _ => .vpblendd
  | .vpshufd _ => .vpshufd
  | .vpermq _ => .vpermq
  | .vpmuludq => .vpmuludq
  | .vpaddq => .vpaddq
  | .vpmullq => .vpmullq
  | .vpand => .vpand
  | .vpor => .vpor
  | .vpxor => .vpxor
  | .vpshufb => .vpshufb
  | .vpsrlq _ => .vpsrlq
  | .vpsllq _ => .vpsllq
  | .vpsrld _ => .vpsrld
  | .vpslld _ => .vpslld
  | .vpsrlvd => .vpsrlvd
  | .vpsllvd => .vpsllvd
  | .vpandn => .vpandn
  | .vprolq _ => .vprolq
  | .vpmulld => .vpmulld
  | .vpsrad _ => .vpsrad
  | .vpaddw => .vpaddw
  | .vpsubw => .vpsubw
  | .vpmullw => .vpmullw
  | .vpmulhw => .vpmulhw
  | .vpmaddwd => .vpmaddwd
  | .vpcmpgtw => .vpcmpgtw
  | .vpcmpgtd => .vpcmpgtd
  | .vpcmpeqd => .vpcmpeqd
  | .vpsllw _ => .vpsllw
  | .vpsrlw _ => .vpsrlw
  | .vpsraw _ => .vpsraw
  | .vpabsd => .vpabsd
  | .vpsignd => .vpsignd
  | .vpacksswb => .vpacksswb
  | .vpackssdw => .vpackssdw
  | .vpermd => .vpermd
  | .vpunpckldq => .vpunpckldq
  | .vpunpckhdq => .vpunpckhdq
  | .vpunpcklqdq => .vpunpcklqdq
  | .vpunpckhqdq => .vpunpckhqdq
  | .vpblendw _ => .vpblendw
  | .vpsrldq _ => .vpsrldq
  | .vperm2i128 _ => .vperm2i128
  | .vpsrlvq => .vpsrlvq
  | .vpsllvq => .vpsllvq

/-- The x86 mnemonic of an AVX2 dialect op. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect.YmmOp.mnem (op : YmmOp) :
    X86Mnem :=
  .simd op.simdMnem

/-- Every AVX2 dialect op is data-operand independent. -/
theorem ymmOp_isDataIndependent (op : YmmOp) : op.mnem.isDataIndependent = true := by
  rw [X86Mnem.isDataIndependent_iff]
  exact SimdMnem.timing_eq_doit _

/-- The scalar instructions classed variable time are exactly `sarx`, `bzhi`,
    `xchg`, `rcl`, `rcr`, `clc` and `stc`; no `JInstr` is a control transfer. -/
theorem JInstr.mnem_timing_varTime_iff {w : Nat} (i : JInstr w) :
    i.mnem.timing = .varTime ↔
      i.mnem = .sarx ∨ i.mnem = .bzhi ∨ i.mnem = .xchg ∨ i.mnem = .rcl ∨
        i.mnem = .rcr ∨ i.mnem = .clc ∨ i.mnem = .stc := by
  cases i <;> simp [JInstr.mnem, X86Mnem.timing]

/-- No scalar `JInstr` is a control transfer. -/
theorem JInstr.mnem_timing_ne_control {w : Nat} (i : JInstr w) :
    i.mnem.timing ≠ .control := by
  cases i <;> simp [JInstr.mnem, X86Mnem.timing]

end CatCrypt.Crypto.SecureCompilation.CT
