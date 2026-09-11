/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# A native-Lean x86-64 target model for the emitted scalar subset (task #148/#281)

This is the **proof-of-concept first step** toward owning the verified back-end
(#148): a Lean-checked `lprog → x86` lowering on the small scalar instruction
subset our kernels actually emit. It is *not* the full verified backend (which
is CompCert-for-the-backend research scale); it establishes the framework and
de-risks it.

## Trust story (#281 — read this first)

This model's instruction semantics are **not self-evidently authoritative**.
Their faithfulness rests on **agreement with Jasmin's Rocq x86 model**
(`x86_instr_decl.v`: the `x86_ADD`/`x86_ADC`/`x86_IMULt`/`x86_SHL`/… semantic
functions invoked by `eval_instr`/`eval_op` in `arch_sem.v`), which is the
authoritative anchor because Jasmin is the like-for-like backend we replace:
the verified pipeline currently hands `lprog` to jasminc, whose CT theorem
(`jasminc_preserves_ct`, arXiv:2511.11292) is stated *over that same Rocq
model*. Matching it is therefore translation validation against the exact
semantics the existing trust story depends on.

The correspondence is recorded and machine-checked in
`TranslationValidation.lean`:

* For `MOV`, `ADD`, `SUB`, `AND`, `OR`, `XOR`, `IMULt` (low word), `SHL`,
  `SHR`, `CMOVcc`, `ADC` the data-result effect of our `step` is pinned by a
  Lean `example` to the *exact numeric value* the Jasmin Rocq `x86_*` function
  computes on shared concrete inputs — a **differential check** driven through
  `rocq-mcp` against the compiled `x86_instr_decl.vo` (the Jasmin outputs are
  quoted there). `SUB`/`SBB` are validated as the two's-complement wrap that
  `wrepr` / `sub_borrow` produce.
* `JasminModel.lean` is the **faithful line-for-line transcription** of the
  Rocq (full five-flag state + the `x86_*` functions + `evalInstr`/`runBlock`);
  this `Model.lean` `step` is reconciled with it on the data result in
  `TranslationValidation.lean`'s `Jasmin` section.
* `CT-CompCert` and `K-x86` have been read side by side against this model, on
  paper and not as a machine-checked equivalence, so neither constrains what is
  proved here. A **second independent machine-checked anchor**, the Sail x86
  model derived from the ACL2 `x86isa` model
  (`rems-project/sail-x86-from-acl2`), is wired in `SailX86Validation.lean`
  (#437): the owned `step`/`evalInstr` are pinned to the Sail spec functions'
  exact data + flag outputs on the same concrete inputs used against Jasmin.

What is **assumed by inspection** (not differentially validated) and what is
**out of scope** is stated below and in `TranslationValidation.lean`. No
"axiom-free / authoritative" claim is made for the model itself; only the
preservation theorems are axiom-clean *relative to* this modeled semantics.

## What already exists, and what this adds

The current verified pipeline ends at jasmin's `Linear.lprog`
(`VIR/JasminLprogExport.lean`) and then hands off to one of:

* **jasminc** — the Coq-verified `compile_lprog_to_asm`, cited via the *opaque*
  predicates `Jasminc.compilesTo`/`n.isCT` in `JasminCompilerBridge.lean`. The
  x86 target `n` there is an `opaque Type` with an `opaque n.isCT : n → Prop`:
  uninterpreted. Trust currently rests on jasminc being correct.
* **Veir/MLIR → LLVM** — unverified once it leaves Lean.

This module does **not** duplicate `n` (there is nothing concrete to duplicate —
it is opaque). It provides the *missing concrete artifact*: an x86 instruction
datatype with a register/flag machine and an executable `step` semantics, so
that a lowering target has real meaning Lean-side. The companion
`Lowering.lean` lowers the scalar `lprog` `Lopn` fragment to it, and
`Preservation.lean` proves the lowered step matches the source op denotation
(`JasminBinOp.apply`) for a handful of representative instructions.

## The emitted instruction subset (what our compiler actually emits)

Determined by inspecting the emitters and the committed artifacts:

* **lprog opcode vocabulary** our emit path produces (`JasminLprogExport`'s
  `binOpName` / `opToLinstrR`): `ADD`, `SUB`, `MUL`, `AND`, `OR`, `XOR`,
  `SHL`, `SHR` (the `JasminBinOp` two-address arms), plus `MOV` and the
  `LOAD`/`STORE` (stack), `ZEROEXT`/`TRUNC` (cast), `CALL:` (extCall),
  `CONST:` (materialise constant) pseudo-ops.
* **What jasminc then lowers these to**, as seen in the committed `.s`
  (`bench/gmp_perf/mpn_add_n_adc.s`, `bench/mpn_mulbase_cwhile4_compare/*.s`,
  `bench/x25519_compare/*.s`): `mov(q)`, `add(q)`, `adc(q)` (the carry chain
  the bignum kernels rely on — e.g. `addq $-1,%rax; adcq %r9,%r8`),
  `sub`/`sbb`, `imul`/`mulx`/`adcx`/`adox` (ADX bignum leaves), `shl`/`shr`/
  `sar`, `cmovcc`, `and`/`or`/`xor`/`not`/`neg`, `lea`, plus `cmp`/`test`/
  `jcc`/`jmp`/`call`/`ret` (control flow) and the AVX2/AVX-512 SIMD ops of the
  vector dialect (`vpaddq`, `vpshufb`, `vgf2p8mulb`, …).

## Scope of *this* model

We model the **scalar GP-register data subset**: `MOV`, `ADD`/`SUB`,
`ADC`/`SBB` (carry chain), `MUL`/`IMUL` (low word), logical `AND`/`OR`/`XOR`,
the shifts `SHL`/`SHR`/`SAR`, `CMOV`, and the **ADX/BMI2 bignum trio**
`MULX`/`ADCX`/`ADOX` (the two-independent-carry-chain multiply idiom the
safegcd and mpn kernels emit — `bench/mpn_adxblk_carry_compare/*.jazz`,
`bench/mpn_invert_safegcd_compare/gen_divstep/wmul_hi.jazz`). All operate on a
fixed machine word width `w` (the source `reg w`). We track the **carry flag**
`CF` (set by `ADD`/`SUB`/`ADC`/`SBB`/`ADCX`; `CMOV` conditions read it) and the
**overflow flag** `OF` (set by `ADOX`, its independent second carry
accumulator); `MULX` touches no flag. We also model the **easy-tier unary
arms** `NOT` (bitwise complement, no flag) and `NEG` (two's-complement negate,
sets `CF = dst ≠ 0`) — the `not`/`neg` the kernels emit (committed `.s`,
header below). The rest of the flag ALU (`SF`/`PF`/`ZF`) is **modeled inert**
and stated so. `DIV`/`IDIV`, rotates, `LEA`, `SETcc`, `TEST`/`CMP`, memory
operands + addressing modes, SIMD/AVX, calls/jumps and the byte encoder are
deliberately **out of scope** — see `README.md` for the path to the full
backend and the #260 cross-object-call story.

## Honesty

* `MOV`, `ADD`, `SUB`, `AND`, `OR`, `XOR`, `MUL`, `IMUL`, `SHL`, `SHR`, `CMOV`
  data-result preservation against the source `lprog` op denotation
  (`JasminBinOp.apply`) is *proved* in `Preservation.lean` (axiom-clean modulo
  Lean/Mathlib core), and each is *differentially validated* against the
  Jasmin Rocq `x86_*` function in `TranslationValidation.lean`.
* `ADC`/`SBB` have **no `JasminBinOp` source op** (the source IR carries only
  carry-free `add`/`sub`); their data effect is validated directly against
  Jasmin's `x86_ADC`/`x86_SBB` (`add_carry`/`sub_borrow` = `wrepr (x±y±c)`),
  not against `lprog`. Stated, not hidden.
* `MULX`/`ADCX`/`ADOX` likewise have no `JasminBinOp` source op (they are
  emitted as Jasmin `Copn` intrinsics, not arithmetic `lprog` ops). Their
  effect is validated directly against Jasmin's `x86_MULX_lo_hi` (= `wumul`,
  swapped to `(lo, hi)`) and `x86_ADCX` (= `waddcarry`, the *same* function for
  both `ADCX` and `ADOX`, differing only in the flag routed by the
  instruction): `ADCX` reads/writes `CF` only, `ADOX` reads/writes `OF` only,
  `MULX` no flag. The differential pins and the flag-routing effect theorems
  are in `TranslationValidation.lean`.
* `NOT`/`NEG` are unary arms with no `JasminBinOp` source op (the source IR has
  no unary complement/negate); their effect is validated directly against
  Jasmin's `x86_NOT` (`= wnot`, no flag) and `x86_NEG` (data `= (-w)%w`, with
  `CF = Some (w != 0)`). The differential pins are in `TranslationValidation.lean`.
* `SAR` (arithmetic right shift) is *modeled but its `lprog` preservation is
  not proved* — the source `JasminBinOp` only has logical `shr`. It is
  included for completeness and flagged modeled-only.
* **Shift-count correspondence caveat:** Jasmin's `x86_SHL`/`SHR`/`SAR` mask
  the count by `x86_shift_mask sz` (`& 63` at `U64`) before shifting; our
  `step` shifts by the raw `(src.eval).toNat`. The two agree **iff the count
  is `< w`** (the only case our compiler emits — shift amounts are
  compile-time bounded). For counts `≥ w` they differ (e.g. `SHL 1 by 68`:
  Jasmin → `16`, our model → `0`). This precondition is recorded in
  `TranslationValidation.lean` rather than papered over.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Registers and machine state

We use a `String`-named register file, matching `lprog`'s post-register-alloc
operand names (`"RAX"`, `"r3"`, …). A more faithful model would use the 16
physical GP enum; `String` keeps the POC lowering total without committing to a
specific allocation, and is sufficient for the per-instruction preservation
theorems (which quantify over the names). -/

/-- An x86 general-purpose register, identified by name (e.g. `"RAX"`, `"r3"`). -/
abbrev Reg := String

/-- The architectural flags we model. The carry/zero/sign flags the modeled
    ALU sets (sufficient for `CMOV` conditions), plus the overflow flag `of`,
    which the ADX `ADOX` carry chain uses as its second, independent carry
    accumulator (`ADCX` → `CF`, `ADOX` → `OF`). The remaining flag ALU
    (`PF`, the signed/zero parts beyond what is set here) is a deliberate POC
    simplification (see module header). -/
structure Flags where
  cf : Bool := false
  of : Bool := false
  zf : Bool := false
  sf : Bool := false
  deriving DecidableEq, Repr

/-- The machine state at word width `w`: a register file and the flags.
    Registers default to `0`; an absent name reads as `0`. -/
structure State (w : Nat) where
  regs : Reg → BitVec w
  flags : Flags := {}

/-- Read register `r`. -/
@[simp] def State.get {w : Nat} (s : State w) (r : Reg) : BitVec w := s.regs r

/-- Write `v` to register `r`, leaving all others and the flags unchanged. -/
def State.set {w : Nat} (s : State w) (r : Reg) (v : BitVec w) : State w :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

@[simp] theorem State.get_set_same {w : Nat} (s : State w) (r : Reg) (v : BitVec w) :
    (s.set r v).get r = v := by
  simp [State.set, State.get]

@[simp] theorem State.get_set_other {w : Nat} (s : State w) (r r' : Reg) (v : BitVec w)
    (h : r' ≠ r) : (s.set r v).get r' = s.get r' := by
  simp [State.set, State.get, h]

/-- Write `v` to register `r` *and* set the carry flag, leaving the other
    registers and flags unchanged. Used by the carry-producing ALU ops. -/
def State.setCF {w : Nat} (s : State w) (r : Reg) (v : BitVec w) (cf : Bool) :
    State w :=
  { (s.set r v) with flags := { s.flags with cf := cf } }

@[simp] theorem State.get_setCF_same {w : Nat} (s : State w) (r : Reg)
    (v : BitVec w) (cf : Bool) : (s.setCF r v cf).get r = v := by
  simp [State.setCF, State.set, State.get]

@[simp] theorem State.setCF_flags_of {w : Nat} (s : State w) (r : Reg)
    (v : BitVec w) (cf : Bool) : (s.setCF r v cf).flags.of = s.flags.of := by
  simp [State.setCF, State.set]

/-- Write `v` to register `r` *and* set the overflow flag, leaving the other
    registers and flags (in particular `CF`) unchanged. Used by `ADOX`, whose
    Jasmin instruction (`Ox86_ADOX_instr`, output list `[F OF; Ea 0]`) writes
    only `OF` and its destination. -/
def State.setOF {w : Nat} (s : State w) (r : Reg) (v : BitVec w) (of : Bool) :
    State w :=
  { (s.set r v) with flags := { s.flags with of := of } }

@[simp] theorem State.get_setOF_same {w : Nat} (s : State w) (r : Reg)
    (v : BitVec w) (of : Bool) : (s.setOF r v of).get r = v := by
  simp [State.setOF, State.set, State.get]

@[simp] theorem State.setOF_flags_cf {w : Nat} (s : State w) (r : Reg)
    (v : BitVec w) (of : Bool) : (s.setOF r v of).flags.cf = s.flags.cf := by
  simp [State.setOF, State.set]

/-- Write the low word `lo` to `dst` and the high word `hi` to `dstHi`,
    leaving every other register and **all flags** unchanged. This is the
    two-output, flag-free effect of `MULX` (Jasmin `Ox86_MULX_lo_hi_instr`,
    which touches no flag). Requires the two destinations to be distinct (the
    bignum idiom always allocates them so); if `dstHi = dst` the high word
    wins, matching x86 (the high destination is written last). -/
def State.setLoHi {w : Nat} (s : State w) (dst dstHi : Reg) (lo hi : BitVec w) :
    State w :=
  (s.set dst lo).set dstHi hi

@[simp] theorem State.setLoHi_flags {w : Nat} (s : State w)
    (dst dstHi : Reg) (lo hi : BitVec w) : (s.setLoHi dst dstHi lo hi).flags = s.flags := by
  simp [State.setLoHi, State.set]

@[simp] theorem State.get_setLoHi_hi {w : Nat} (s : State w)
    (dst dstHi : Reg) (lo hi : BitVec w) : (s.setLoHi dst dstHi lo hi).get dstHi = hi := by
  simp [State.setLoHi, State.set, State.get]

@[simp] theorem State.get_setLoHi_lo {w : Nat} (s : State w)
    (dst dstHi : Reg) (lo hi : BitVec w) (h : dst ≠ dstHi) :
    (s.setLoHi dst dstHi lo hi).get dst = lo := by
  simp [State.setLoHi, State.set, State.get, h]

/-! ### Carry / borrow predicates

The unsigned carry-out of `a + b` (`+ c`) and borrow of `a - b` (`- c`),
matching the `CF` Jasmin's `rflags_of_aluop` records as `wunsigned w != vu`
(the word differs from the unbounded integer sum/difference, i.e. it wrapped).
-/

/-- Unsigned carry-out of `a + b + (c : carry-in)`. -/
def addCarry {w : Nat} (a b : BitVec w) (c : Bool) : Bool :=
  decide (a.toNat + b.toNat + (if c then 1 else 0) ≥ 2 ^ w)

/-- Unsigned borrow of `a - b - (c : borrow-in)`. -/
def subBorrow {w : Nat} (a b : BitVec w) (c : Bool) : Bool :=
  decide (a.toNat < b.toNat + (if c then 1 else 0))

/-- High word of the full unsigned product `a * b` (the `hi` output of `MULX`).
    Matches Jasmin `wumul`'s `high_bits sz (wunsigned a * wunsigned b)
    = wrepr sz ((a*b) >> w)`, i.e. `(a.toNat * b.toNat) / 2 ^ w`. -/
def mulHi {w : Nat} (a b : BitVec w) : BitVec w :=
  BitVec.ofNat w (a.toNat * b.toNat / 2 ^ w)

/-! ## 2. Operands

An operand is either a named register or a compile-time immediate. (Memory
operands are out of scope for the POC.) This mirrors the `LOperand.reg`/`.imm`
arms of `lprog` exactly; `LOperand.arr` is the memory case we do not model. -/

/-- An x86 operand: a register or an immediate. -/
inductive Operand where
  | reg (r : Reg)
  | imm (v : Nat)
  deriving DecidableEq, Repr

/-- Evaluate an operand against the state at width `w`. -/
@[simp] def Operand.eval {w : Nat} (s : State w) : Operand → BitVec w
  | .reg r => s.get r
  | .imm v => BitVec.ofNat w v

/-! ## 3. The instruction datatype

Two-address form: each arithmetic/logical instruction writes its first
(destination) register, reading the destination and a source operand — the
shape `lprog` produces after the destructive `mov dst,src0; op dst,src1`
two-address lowering (`Com.toLprogPhys`). `MOV` is the unary load. `CMOV`
conditionally moves based on a `Cond` over the flags. -/

/-- Conditions for `CMOV`, over the modeled flags. -/
inductive Cond where
  /-- Move if zero flag set (`CMOVE`). -/
  | e
  /-- Move if zero flag clear (`CMOVNE`). -/
  | ne
  /-- Move if carry set (`CMOVB`). -/
  | b
  deriving DecidableEq, Repr

/-- Evaluate a condition against the flags. -/
@[simp] def Cond.eval : Cond → Flags → Bool
  | .e,  f => f.zf
  | .ne, f => !f.zf
  | .b,  f => f.cf

/-- The modeled scalar x86 instruction subset (two-address). All operate at the
    fixed machine word width `w` of the enclosing program. -/
inductive Instr (w : Nat) where
  /-- `MOV dst, src`. -/
  | mov (dst : Reg) (src : Operand)
  /-- `ADD dst, src` : `dst := dst + src`; sets `CF` to the unsigned carry-out. -/
  | add (dst : Reg) (src : Operand)
  /-- `SUB dst, src` : `dst := dst - src`; sets `CF` to the unsigned borrow. -/
  | sub (dst : Reg) (src : Operand)
  /-- `ADC dst, src` : `dst := dst + src + CF`; sets `CF` to the new carry-out.
      The bignum add-with-carry instruction (no `JasminBinOp` source
      counterpart; validated directly against Jasmin's `x86_ADC`). -/
  | adc (dst : Reg) (src : Operand)
  /-- `SBB dst, src` : `dst := dst - src - CF`; sets `CF` to the new borrow.
      Validated directly against Jasmin's `x86_SBB`. -/
  | sbb (dst : Reg) (src : Operand)
  /-- `MUL`/`IMUL` low word : `dst := dst * src` (low `w` bits; the two agree on
      the low word). -/
  | mul (dst : Reg) (src : Operand)
  /-- `AND dst, src`. -/
  | and_ (dst : Reg) (src : Operand)
  /-- `OR dst, src`. -/
  | or_ (dst : Reg) (src : Operand)
  /-- `XOR dst, src`. -/
  | xor_ (dst : Reg) (src : Operand)
  /-- `SHL dst, src` : logical left shift by `src.toNat`. -/
  | shl (dst : Reg) (src : Operand)
  /-- `SHR dst, src` : logical right shift by `src.toNat`. -/
  | shr (dst : Reg) (src : Operand)
  /-- `SAR dst, src` : arithmetic right shift by `src.toNat`. Modeled only;
      preservation not proved (no logical-`shr` source counterpart). -/
  | sar (dst : Reg) (src : Operand)
  /-- `CMOVcc dst, src` : `dst := if cc(flags) then src else dst`. -/
  | cmov (cc : Cond) (dst : Reg) (src : Operand)
  /-- `MULX dstHi, dstLo, a, b` (BMI2 unsigned widening multiply): computes the
      full `2w`-bit product `a * b` and splits it into the low word (written to
      `dstLo`) and high word (written to `dstHi`). Mirrors the emitted
      `hi, lo = #MULX(a, b)` (on x86 one factor is the implicit `RDX`; we make
      both explicit). **Does not touch any flag** — matching Jasmin
      `Ox86_MULX_lo_hi_instr`, whose output list `[Eu 1; Eu 0]` is registers
      only. -/
  | mulx (dstHi dstLo : Reg) (a b : Operand)
  /-- `ADCX dst, src` : `dst := dst + src + CF`; sets **only** `CF` to the new
      carry-out, leaving `OF` and every other flag untouched. The CF-chain
      accumulator of the two-independent-carry-chain bignum-multiply idiom.
      Validated against Jasmin's `x86_ADCX` (= `waddcarry`) with `Ox86_ADCX_instr`
      routing the carry to `CF` only (output list `[F CF; Ea 0]`). -/
  | adcx (dst : Reg) (src : Operand)
  /-- `ADOX dst, src` : `dst := dst + src + OF`; sets **only** `OF` to the new
      carry-out, leaving `CF` and every other flag untouched. The parallel
      OF-chain accumulator. Same `x86_ADCX` data/carry semantics as `ADCX`, but
      `Ox86_ADOX_instr` reads/writes `OF` (output list `[F OF; Ea 0]`). -/
  | adox (dst : Reg) (src : Operand)
  /-- `NOT dst` : `dst := ~dst` (bitwise complement). Touches **no flag** —
      matching Jasmin `x86_NOT = wnot v` (`Ox86_NOT_instr`, output list `[Eu 0]`
      is the register only). Easy-tier scalar arm (item 1, `not`/`neg` group);
      differentially validated against `x86_NOT` in `TranslationValidation.lean`. -/
  | not_ (dst : Reg)
  /-- `NEG dst` : `dst := -dst` (two's-complement negate); sets `CF` to
      `dst ≠ 0` (the unsigned borrow of `0 - dst`), matching Jasmin `x86_NEG`'s
      `CF = Some (w != 0)`. The other Jasmin flags (`OF/SF/PF/ZF`) are part of
      `x86_NEG`'s `b5w` tuple but are outside the modeled flag set (POC
      simplification, as for the ALU arms). Easy-tier scalar arm (item 1);
      differentially validated against `x86_NEG`'s data + `CF`. -/
  | neg (dst : Reg)
  deriving Repr

/-! ## 4. Step semantics

Each instruction maps a state to the next state. `ADD`/`SUB`/`ADC`/`SBB`/`ADCX`
update the destination register **and the carry flag** (`CF`); `ADOX` updates
its destination **and the overflow flag** (`OF`) instead, leaving `CF`
untouched — the two carry chains are independent. The remaining flags
(`SF`/`PF`/`ZF`, and the unused one of `CF`/`OF`) are left inert (modeled
simplification, stated in the header). The logical/shift/`MOV`/`MUL`/`MULX`
arms touch no flag. `CMOV` reads the *current* flags. The data result is the
part the source IR denotes and against which `Preservation.lean` /
`TranslationValidation.lean` validate. -/

/-- One-instruction step at width `w`. -/
def step {w : Nat} (s : State w) : Instr w → State w
  | .mov dst src  => s.set dst (src.eval s)
  | .add dst src  =>
      s.setCF dst (s.get dst + src.eval s) (addCarry (s.get dst) (src.eval s) false)
  | .sub dst src  =>
      s.setCF dst (s.get dst - src.eval s) (subBorrow (s.get dst) (src.eval s) false)
  | .adc dst src  =>
      let c := s.flags.cf
      s.setCF dst (s.get dst + src.eval s + (if c then 1 else 0))
        (addCarry (s.get dst) (src.eval s) c)
  | .sbb dst src  =>
      let c := s.flags.cf
      s.setCF dst (s.get dst - src.eval s - (if c then 1 else 0))
        (subBorrow (s.get dst) (src.eval s) c)
  | .mul dst src  => s.set dst (s.get dst * src.eval s)
  | .and_ dst src => s.set dst (s.get dst &&& src.eval s)
  | .or_ dst src  => s.set dst (s.get dst ||| src.eval s)
  | .xor_ dst src => s.set dst (s.get dst ^^^ src.eval s)
  | .shl dst src  => s.set dst (s.get dst <<< (src.eval s).toNat)
  | .shr dst src  => s.set dst (s.get dst >>> (src.eval s).toNat)
  | .sar dst src  => s.set dst (BitVec.sshiftRight (s.get dst) (src.eval s).toNat)
  | .cmov cc dst src =>
      s.set dst (if cc.eval s.flags then src.eval s else s.get dst)
  | .mulx dstHi dstLo a b =>
      let x := a.eval s
      let y := b.eval s
      s.setLoHi dstLo dstHi (x * y) (mulHi x y)
  | .adcx dst src =>
      let c := s.flags.cf
      s.setCF dst (s.get dst + src.eval s + (if c then 1 else 0))
        (addCarry (s.get dst) (src.eval s) c)
  | .adox dst src =>
      let c := s.flags.of
      s.setOF dst (s.get dst + src.eval s + (if c then 1 else 0))
        (addCarry (s.get dst) (src.eval s) c)
  | .not_ dst => s.set dst (~~~ s.get dst)
  | .neg dst =>
      s.setCF dst (0 - s.get dst) (decide (s.get dst ≠ 0))

/-- Run a straight-line block of instructions left-to-right. -/
def run {w : Nat} (s : State w) : List (Instr w) → State w
  | [] => s
  | i :: is => run (step s i) is

@[simp] theorem run_nil {w : Nat} (s : State w) : run s [] = s := rfl

@[simp] theorem run_cons {w : Nat} (s : State w) (i : Instr w) (is : List (Instr w)) :
    run s (i :: is) = run (step s i) is := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend
