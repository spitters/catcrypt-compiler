/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The literal `CMP`/flag-guarded back-edge over the memref state

The memref interpreter stack (`JasminLsemMemLoop.evalInstrPMemL` and everything
built on it) guards a loop back-edge by reading the **counter register**
directly: `loopLinstrRM`'s `Lcond (.reg nReg) top` evaluates `condNZ` on `nReg`.
The lowering `JasminLprogExport.forLoopLcmdNRt` / `forLoopLcmdNRtNested` emits a
different — semantically equal but syntactically distinct — guard idiom:

    Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]   -- cmpq $0, %ctr
    Lcond (.reg "NZ") top                                        -- jne .L<top>

i.e. a flag-materialising compare (`CMP` is `SUB` discarding its result — it
writes `ZF`, never its operand; `LprogAsmPrinter.attBase "CMP" = cmp`) followed
by a conditional jump whose operand is a **condition-code name**, not a register
(`LprogAsmPrinter.attCC`: `"NZ" → jne`, `"Z" → je`).  The runtime-count form
additionally carries a **zero-trip top guard** `CMP ctr,#0 ; Lcond (.reg "Z")
endL … Llabel endL` (skip the whole do-while when the runtime count is `0`).
Neither instruction runs under `evalInstrPMemL`: the `CMP` `Lopn` reaches
`applyOpnN` (no `"CMP"` arm — `none`), and the `Lcond (.reg "NZ")` reads a
never-written register named `"NZ"` (miss ⇒ `false` — the back-edge would never
be taken).

This module extends the interpreter with the emitted idiom — **purely
additively** (`evalInstrPMemL` / `LstatePM` / the memref loop theorems are imported,
never edited):

* **`LstateMF`** — the flag-extended program state: a wrapped `LstatePM` plus a
  single zero-flag `zf : Bool`.  The flag lives OUTSIDE the register file
  (`jne` reads `ZF`, not a register), so a flag-machine run tracks the
  unextended machine's base state exactly — no pseudo-register pollution of
  `lvm` — which is what makes the re-tie below an *equality* on the register
  store and the array carrier.
* **`evalInstrPMemF`** — three additive arms in front of a verbatim delegate to
  `evalInstrPMemL`:
  1. the emitted flag-`CMP` (`cmpArgs?`: exactly `Lopn [_] (withWidthTag 64
     "CMP") [a, b]`) sets `zf := (⟦a⟧ = ⟦b⟧)` at width 64 and advances the pc,
     leaving the store untouched;
  2. the emitted register-copy `MOV` (`movRegArgs?`: `Lopn [.reg dst] "MOV…"
     [.reg src]` — the accumulator/counter seed and feedback moves the lowering
     emits, which `lsemStepN` has no arm for), and the array-ABI moves `MOVQ`,
     `LOAD:64`, `STORE:64` between register-shaped names (`copyQ`, each printed as
     `movq`), write `dst := src`;
  3. the flag-reading conditional (`flagCondCC?`: `Lcond (.reg "NZ") l` = `jne`,
     `Lcond (.reg "Z") l` = `je`) jumps iff `zf` matches the condition's
     polarity.  Every other instruction delegates to `evalInstrPMemL` on the
     wrapped state, threading `zf` unchanged.
* **Carry and overflow flags** (`stepMemF`): the base state carries `CF` and `OF`
  (`LstateM.cf`, `LstateM.of`). The 64-bit `ADD`, `SUB`, `AND`, `OR`, `XOR` write
  them (`withALUFlags`), and the carry family `ADC`, `SBB`, `ADCX`, `ADOX`
  (`carryArgs?`, `carryStep`) reads and writes them, with the values of the decoder
  machine's `x86_ADD`, `x86_SUB`, `x86_AND`, `x86_OR`, `x86_XOR`, `x86_ADC`, `x86_SBB`,
  `x86_ADCX`. The flag-`CMP` writes `zf` only: no emitted instruction reads the
  `CF` a compare writes. The flag-quiet lift instructions (`wideArgs?`, `wideStep`) are
  the two-source `MOV:64 [d] [d, b]` (`d := b`) and `MULX:64`/`MULXMEM:64 [lo, hi] [b]`
  with the implicit first source `RDX` and the values of `x86_MULX_lo_hi`.
* **Conservativity square** (`lsemFuelMemF_conservative`): on a program none of
  whose instructions is recognised by the flag arms, the flag machine *is*
  the counter-register machine — `lsemFuelMemF P fuel ⟨s, zf⟩ = (lsemFuelMemL P
  fuel s).map (⟨·, zf⟩)`.
* **Guard equivalence + re-tie** (`flagLoop_runBounded`): the flag-guarded loop
  `flagLoopLinstrRM top nReg body = Llabel top :: body ++ [CMP nReg,#0 ; Lcond
  NZ top]` — the EMITTED back-edge idiom, pinned to the lowering by
  `forLoopLcmdNRt_backedge` — realises the fold `runBoundedLoopMemF` of the flag
  body-fold `lsemStraightMemF`, which agrees with the straight-line body-fold up to
  the two flags (`lsemStraightMemF_of_lsemStraightMem`).  The guard equivalence
  is `zf`-after-`CMP nReg,#0` `= ¬ condNZ nReg` (`zf_after_cmp_eq_not_condNZ`):
  comparing the counter against zero materialises exactly the bit the
  counter-register guard reads.
* **Zero-trip top-guard skip** (`guardedFlagLoop_zeroTrip`): the runtime-count
  shape `guardedFlagLoopLinstrRM` (the `forLoopLcmdNRt` skeleton: top guard
  `CMP ctr,#0 ; Lcond Z endL`, the loop, `Llabel endL`; pin:
  `forLoopLcmdNRt_guard`) with a **zero** counter jumps over the whole loop and
  halts with the register store and array carrier untouched — the `m = 0` fold.

## Validate (the REAL rendered lowering, not an imitation)

`rtLoopRM` is `JasminLprogExport.loopSmokeRtBody` — the actual `comLToBody`
rendering of a `ComL.forLoopNRt` node (runtime-count squaring loop) — lifted to
the typed instruction list (trailing `Lret` dropped: function return is outside
the loop idiom, and program-end is the interpreter's halt).  `native_decide`
checks the flag machine runs it end to end: the accumulator decodes to
`ComL.denote` (`3^(2²) = 81` at runtime count `2`), and at runtime count `0` the
zero-trip guard skips the body (accumulator = seed).

**All goals closed; axioms ⊆ {propext, Classical.choice, Quot.sound}** for every named
theorem (+ `Lean.ofReduceBool` for the `native_decide` validates).
A carry chain (`ADD`, `ADC`; `XOR`, `ADCX`, `ADOX`; `SUB`, `SBB`) runs under the flag
machine with the machine's values (`#kat` checks in section 12).
Scope: the generic re-tie takes a `CMP`-free, reg-`MOV`-free body (the fold side
is `lsemStraightMemF`, which steps neither); the invariant-touch compares
(`CMP ctr, invBase`, emitted only when the loop carries invariant base
registers) and bodies with feedback `MOV`s are covered by the machine (see the
validate, whose body has a feedback `MOV`) but not by the generic fold tie.
The loop exit needs a **zero read** of the counter (`getW = some 0`) —
the emitted `CMP` evaluates its operand, whereas the counter-register guard falls
through even on a read miss; this is the one strengthening of the
schedule hypotheses.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
  (B5W x86_ADD x86_SUB x86_AND x86_OR x86_XOR x86_ADC x86_SBB x86_ADCX x86_MULX_lo_hi)

/-! ## 1. Recognizers for the three emitted forms -/

/-- The emitted flag-`CMP` recognizer: exactly `Lopn [_] (withWidthTag 64 "CMP")
    [a, b]` — the mnemonic the loop lowerings emit (`forLoopLcmd`,
    `forLoopLcmdN`, `forLoopLcmdNRt`, `forLoopLcmdNRtNested` all render the
    back-edge compare as `withWidthTag 64 "CMP"`, and the invariant touches as
    the same mnemonic with a register second operand).  Returns the two compared
    operands. -/
def cmpArgs? (i : LinstrRM) : Option (LOperand × LOperand) :=
  match i.fst with
  | .Lopn [_] opn [a, b] => if opn = withWidthTag 64 "CMP" then some (a, b) else none
  | _ => none

/-- The whole-word move mnemonics of the array ABI between register-shaped names:
    `MOVQ` (a copy between registers and `qsave.<R>` save slots), `LOAD:64` (a load
    from an ABI cell `mem.<B>.<off>`) and `STORE:64` (a store to one).  The printer
    renders each as the 64-bit `movq` (`LprogAsmPrinter.attBase` maps `MOVQ`, `LOAD`
    and `STORE` to `mov`, and `LprogAsmPrinter.mnemWidth` is `64` for `MOVQ` and for a
    `:64` tag); the name of a cell resolves to its memory operand. -/
@[simp] def copyQ (opn : String) : Bool := opn == "MOVQ" || opn == "LOAD:64" || opn == "STORE:64"

/-- A mnemonic whose first two characters are none of `MO`, `LO`, `ST` is not a
    `copyQ` mnemonic. -/
theorem copyQ_eq_false_of_toList {x : String} {c₁ c₂ : Char} {t : List Char}
    (hx : x.toList = c₁ :: c₂ :: t)
    (h : ¬ (c₁ = 'M' ∧ c₂ = 'O') ∧ ¬ (c₁ = 'L' ∧ c₂ = 'O') ∧ ¬ (c₁ = 'S' ∧ c₂ = 'T')) :
    copyQ x = false := by
  obtain ⟨hM, hL, hS⟩ := h
  unfold copyQ
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨⟨fun he => hM ?_, fun he => hL ?_⟩, fun he => hS ?_⟩ <;> subst he
  · rw [show "MOVQ".toList = ['M', 'O', 'V', 'Q'] from by decide] at hx
    simp only [List.cons.injEq] at hx
    exact ⟨hx.1.symm, hx.2.1.symm⟩
  · rw [show "LOAD:64".toList = ['L', 'O', 'A', 'D', ':', '6', '4'] from by decide] at hx
    simp only [List.cons.injEq] at hx
    exact ⟨hx.1.symm, hx.2.1.symm⟩
  · rw [show "STORE:64".toList = ['S', 'T', 'O', 'R', 'E', ':', '6', '4'] from by decide] at hx
    simp only [List.cons.injEq] at hx
    exact ⟨hx.1.symm, hx.2.1.symm⟩

/-- A width-tagged mnemonic whose base starts with none of `MO`, `LO`, `ST` is not a
    `copyQ` mnemonic. -/
theorem copyQ_withWidthTag (w : Nat) {m : String} {c₁ c₂ : Char} {t : List Char}
    (hm : m.toList = c₁ :: c₂ :: t)
    (h : ¬ (c₁ = 'M' ∧ c₂ = 'O') ∧ ¬ (c₁ = 'L' ∧ c₂ = 'O') ∧ ¬ (c₁ = 'S' ∧ c₂ = 'T')) :
    copyQ (withWidthTag w m) = false := by
  by_cases hw : w = 64
  · subst hw
    exact copyQ_eq_false_of_toList (by rw [toList_withWidthTag_64, hm]; rfl) h
  · exact copyQ_eq_false_of_toList (by rw [toList_withWidthTag_of_ne hw, hm]; rfl) h

/-- The emitted register-copy recognizer: `Lopn [.reg dst] opn [.reg src]` with
    stripped mnemonic `"MOV"` — the accumulator seed (`MOV acc, a<k>`), runtime
    counter seed (`MOV Lctr, a<k>`), and feedback (`MOV acc, L<d>_r<k>`) moves the
    loop lowerings emit — or with a `copyQ` mnemonic, the array-ABI moves `MOVQ`,
    `LOAD:64` and `STORE:64` between register-shaped names.  (`lsemStepN` covers
    only the immediate `MOV dst, #n`; the register-copy form has no arm anywhere in
    the `lsemStepMem` delegate chain.) -/
def movRegArgs? (i : LinstrRM) : Option (String × String) :=
  match i.fst with
  | .Lopn [.reg dst] opn [.reg src] =>
      if stripWidthTag opn = "MOV" then some (dst, src)
      else if copyQ opn then some (dst, src) else none
  | _ => none

/-- The flag-reading conditional recognizer: the condition operand is a
    **condition-code name**, not a register — `LprogAsmPrinter.attCC` renders
    `Lcond (.reg "NZ") l` as `jne .L<l>` and `Lcond (.reg "Z") l` as `je .L<l>`.
    Returns the polarity (`true` = jump iff `zf`, i.e. `je`; `false` = jump iff
    `¬ zf`, i.e. `jne`) and the target label.  Any other condition operand (in
    particular a counter register, as in `loopLinstrRM`) is not recognised
    and keeps its `condNZ` register-read semantics. -/
def flagCondCC? (i : LinstrRM) : Option (Bool × LLabel) :=
  match i.fst with
  | .Lcond (.reg "Z") lbl => some (true, lbl)
  | .Lcond (.reg "NZ") lbl => some (false, lbl)
  | _ => none

/-! ## 1b. The carry and overflow flags

The flags `CF` and `OF` are the fields `LstateM.cf` and `LstateM.of` of the base state, so
the straight-line step `stepMemF` reads and writes them. Their values are those of the
decoder's machine (`X86Backend.Jasmin.evalInstr`, the instruction semantics of
`Ascent.RInstrAddrMem.aMachine`): the flag records of `x86_ADD`, `x86_SUB`, `x86_AND`,
`x86_OR`, `x86_XOR`, `x86_ADC`, `x86_SBB` and the carry pair of `x86_ADCX`. -/

/-- The two-source carry-family operations of the field-arithmetic lift
    (`Fe25519LfundefBridge.jinstrToLinstrR`: `.adc`, `.sbb`, `.adcx`, `.adox`). -/
inductive CarryOp where
  /-- `ADC`: add with carry-in `CF`, writes `CF` and `OF`. -/
  | adc
  /-- `SBB`: subtract with borrow-in `CF`, writes `CF` and `OF`. -/
  | sbb
  /-- `ADCX`: add with carry-in `CF`, writes only `CF`. -/
  | adcx
  /-- `ADOX`: add with carry-in `OF`, writes only `OF`. -/
  | adox
  deriving DecidableEq, Repr

/-- The carry-family recognizer: exactly `Lopn [.reg d] (withWidthTag 64 m) [a, b]` with
    `m` one of `ADC`, `SBB`, `ADCX`, `ADOX`. The printer renders `m b, d`
    (`LprogAsmPrinter.attBase`: `adc`, `sbb`, `adcx`, `adox`) when `a = d`; the flag
    machine reads the instruction as `d := a m b` with the flag carry-in, the
    three-address reading it gives `ADD`. The three-source forms `ADCX`/`ADOX` with an
    explicit carry register are not recognised. -/
def carryArgs? (i : LinstrRM) : Option (CarryOp × String × LOperand × LOperand) :=
  match i.fst with
  | .Lopn [.reg d] opn [a, b] =>
      if opn = withWidthTag 64 "ADC" then some (.adc, d, a, b)
      else if opn = withWidthTag 64 "SBB" then some (.sbb, d, a, b)
      else if opn = withWidthTag 64 "ADCX" then some (.adcx, d, a, b)
      else if opn = withWidthTag 64 "ADOX" then some (.adox, d, a, b)
      else none
  | _ => none

/-- The flag-writing two-source arithmetic and logical operations at width `64`. -/
inductive AluOp where
  /-- `ADD`. -/
  | add
  /-- `SUB`. -/
  | sub
  /-- `AND`. -/
  | and
  /-- `OR`. -/
  | or
  /-- `XOR`. -/
  | xor
  deriving DecidableEq, Repr

/-- The recognizer of the 64-bit arithmetic and logical operations whose `CF` and `OF`
    the flag machine records: `Lopn [.reg _] (withWidthTag 64 m) [a, b]` with `m` one of
    `ADD`, `SUB`, `AND`, `OR`, `XOR`. -/
def aluFlagOp? (i : LinstrRM) : Option (AluOp × LOperand × LOperand) :=
  match i.fst with
  | .Lopn [.reg _] opn [a, b] =>
      if opn = withWidthTag 64 "ADD" then some (.add, a, b)
      else if opn = withWidthTag 64 "SUB" then some (.sub, a, b)
      else if opn = withWidthTag 64 "AND" then some (.and, a, b)
      else if opn = withWidthTag 64 "OR" then some (.or, a, b)
      else if opn = withWidthTag 64 "XOR" then some (.xor, a, b)
      else none
  | _ => none

/-- The machine's flag record of an arithmetic or logical operation. -/
def aluB5 : AluOp → BitVec 64 → BitVec 64 → B5W 64
  | .add, a, b => x86_ADD a b
  | .sub, a, b => x86_SUB a b
  | .and, a, b => x86_AND a b
  | .or, a, b => x86_OR a b
  | .xor, a, b => x86_XOR a b

/-- The flags an instruction writes onto its post-state `s1`, computed from its
    pre-state `s0`: for a recognised arithmetic or logical operation with both sources
    readable at width `64`, `CF` and `OF` of its machine flag record; otherwise `s1`. -/
def withALUFlags (i : LinstrRM) (s0 s1 : LstateM) : LstateM :=
  match aluFlagOp? i with
  | some (op, a, b) =>
      match evalOperandN s0.reg 64 a, evalOperandN s0.reg 64 b with
      | some va, some vb =>
          { s1 with cf := (aluB5 op va vb).cf.getD false,
                    of := (aluB5 op va vb).of.getD false }
      | _, _ => s1
  | none => s1

/-- One carry-family step: read both sources at width `64`, compute the machine's result
    with the carry-in flag, write the destination and the flags the instruction writes,
    and advance the pc. -/
def carryStep (op : CarryOp) (d : String) (a b : LOperand) (s : LstateM) :
    Option LstateM :=
  match evalOperandN s.reg 64 a, evalOperandN s.reg 64 b with
  | some va, some vb =>
      match op with
      | .adc =>
          some { (s.setReg d (x86_ADC va vb s.cf).word).nextPc with
                   cf := (x86_ADC va vb s.cf).cf.getD false,
                   of := (x86_ADC va vb s.cf).of.getD false }
      | .sbb =>
          some { (s.setReg d (x86_SBB va vb s.cf).word).nextPc with
                   cf := (x86_SBB va vb s.cf).cf.getD false,
                   of := (x86_SBB va vb s.cf).of.getD false }
      | .adcx =>
          some { (s.setReg d (x86_ADCX va vb s.cf).2).nextPc with
                   cf := (x86_ADCX va vb s.cf).1.getD false }
      | .adox =>
          some { (s.setReg d (x86_ADCX va vb s.of).2).nextPc with
                   of := (x86_ADCX va vb s.of).1.getD false }
  | _, _ => none

/-- The flag-quiet instructions of the field-arithmetic lift that `lsemStepMem` does not
    step (`Fe25519LfundefBridge.jinstrToLinstrR`: `.mov`, `.mulx`, `.mulxMem`). -/
inductive WideOp where
  /-- The two-source copy `MOV:64 [d] [d, b]`, printed `mov b, d`: `d := b`. -/
  | mov (d : String) (b : LOperand)
  /-- The widening multiply `MULX:64 [lo, hi] [b]` (or `MULXMEM:64`), printed
      `mulx b, lo, hi`: `(lo, hi) := RDX * b`, the implicit first source `RDX`. -/
  | mulx (lo hi : String) (b : LOperand)

/-- The recognizer of the flag-quiet lift instructions: the two-source `MOV:64` and the
    widening multiplies `MULX:64` and `MULXMEM:64` (a `MULXMEM` source is the name of an ABI
    cell, which the machine reads as a register-shaped name). -/
def wideArgs? (i : LinstrRM) : Option WideOp :=
  match i.fst with
  | .Lopn [.reg d] opn [_, b] =>
      if opn = withWidthTag 64 "MOV" then some (.mov d b) else none
  | .Lopn [.reg lo, .reg hi] opn [b] =>
      if opn = withWidthTag 64 "MULX" ∨ opn = withWidthTag 64 "MULXMEM" then
        some (.mulx lo hi b)
      else none
  | _ => none

/-- The implicit first source of `MULX`. -/
def mulxSrc : String := "RDX"

/-- One flag-quiet lift step: read the sources at width `64`, write the destinations with
    the values of the decoder machine (`MOV` copies its source; `MULX` writes the low and
    then the high word of `x86_MULX_lo_hi`, so the high word wins when `lo = hi`), keep the
    flags, and advance the pc. -/
def wideStep (w : WideOp) (s : LstateM) : Option LstateM :=
  match w with
  | .mov d b =>
      match evalOperandN s.reg 64 b with
      | some v => some ((s.setReg d v).nextPc)
      | none => none
  | .mulx lo hi b =>
      match evalOperandN s.reg 64 (.reg mulxSrc), evalOperandN s.reg 64 b with
      | some x, some y =>
          some (((s.setReg lo (x86_MULX_lo_hi x y).1).setReg hi (x86_MULX_lo_hi x y).2).nextPc)
      | _, _ => none

/-- **The flag machine's straight-line step on the base state**: the straight-line step
    `lsemStepMem` with the flags of `withALUFlags`; an instruction `lsemStepMem` does not
    step is a carry-family step (`carryArgs?`, `carryStep`), a flag-quiet lift step
    (`wideArgs?`, `wideStep`) or stuck. The carry family has no `lsemStepMem` step
    (`applyOpnN` has no `ADC`, `SBB`, `ADCX` or `ADOX` arm). -/
def stepMemF (i : LinstrRM) (s : LstateM) : Option LstateM :=
  match lsemStepMem i s with
  | some b => some (withALUFlags i s b)
  | none =>
      match carryArgs? i with
      | some (op, d, a, b) => carryStep op d a b s
      | none =>
          match wideArgs? i with
          | some w => wideStep w s
          | none => none

@[simp] theorem withALUFlags_reg (i : LinstrRM) (s0 s1 : LstateM) :
    (withALUFlags i s0 s1).reg = s1.reg := by
  unfold withALUFlags; split
  · split <;> rfl
  · rfl

@[simp] theorem withALUFlags_larr (i : LinstrRM) (s0 s1 : LstateM) :
    (withALUFlags i s0 s1).larr = s1.larr := by
  unfold withALUFlags; split
  · split <;> rfl
  · rfl

@[simp] theorem withALUFlags_lmem (i : LinstrRM) (s0 s1 : LstateM) :
    (withALUFlags i s0 s1).lmem = s1.lmem := by
  unfold withALUFlags; split
  · split <;> rfl
  · rfl

@[simp] theorem withALUFlags_lpc (i : LinstrRM) (s0 s1 : LstateM) :
    (withALUFlags i s0 s1).lpc = s1.lpc := by
  simp [LstateM.lpc]

/-- `withALUFlags` changes at most the two flags. -/
theorem withALUFlags_eq (i : LinstrRM) (s0 s1 : LstateM) :
    ∃ c o, withALUFlags i s0 s1 = { s1 with cf := c, of := o } := by
  unfold withALUFlags; split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨s1.cf, s1.of, rfl⟩
  · exact ⟨s1.cf, s1.of, rfl⟩

/-- An instruction that is not a recognised arithmetic or logical operation writes no
    flag. -/
theorem withALUFlags_of_none {i : LinstrRM} (h : aluFlagOp? i = none) (s0 s1 : LstateM) :
    withALUFlags i s0 s1 = s1 := by
  unfold withALUFlags; rw [h]

/-- Every carry-family step advances the pc by one. -/
theorem carryStep_lpc (op : CarryOp) (d : String) (a b : LOperand) (s s' : LstateM)
    (h : carryStep op d a b s = some s') : s'.lpc = s.lpc + 1 := by
  unfold carryStep at h
  split at h
  · cases op <;> (obtain rfl := Option.some.inj h; simp [LstateM.lpc, LstateM.nextPc,
      LstateM.setReg])
  · simp at h

/-- Every flag-quiet lift step advances the pc by one. -/
theorem wideStep_lpc (w : WideOp) (s s' : LstateM) (h : wideStep w s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold wideStep at h
  cases w with
  | mov d b =>
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        simp [LstateM.lpc, LstateM.nextPc, LstateM.setReg]
      · simp at h
  | mulx lo hi b =>
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        simp [LstateM.lpc, LstateM.nextPc, LstateM.setReg]
      · simp at h

/-- A flag-quiet lift step keeps the carry and overflow flags. -/
theorem wideStep_flags (w : WideOp) (s s' : LstateM) (h : wideStep w s = some s') :
    s'.cf = s.cf ∧ s'.of = s.of := by
  unfold wideStep at h
  cases w with
  | mov d b =>
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl⟩
      · simp at h
  | mulx lo hi b =>
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨rfl, rfl⟩
      · simp at h

/-- Every successful `stepMemF` step advances the pc by one. -/
theorem stepMemF_lpc_succ (i : LinstrRM) (s s' : LstateM) (h : stepMemF i s = some s') :
    s'.lpc = s.lpc + 1 := by
  unfold stepMemF at h
  cases hs : lsemStepMem i s with
  | some b =>
      rw [hs] at h
      obtain rfl := Option.some.inj h
      rw [withALUFlags_lpc]
      exact lsemStepMem_lpc_succ i s b hs
  | none =>
      rw [hs] at h
      simp only [] at h
      split at h
      · exact carryStep_lpc _ _ _ _ s s' h
      · split at h
        · exact wideStep_lpc _ s s' h
        · simp at h

/-- Where `lsemStepMem` steps, `stepMemF` is that step with the flags of
    `withALUFlags`. -/
theorem stepMemF_of_lsemStepMem {i : LinstrRM} {s b : LstateM}
    (h : lsemStepMem i s = some b) : stepMemF i s = some (withALUFlags i s b) := by
  unfold stepMemF; rw [h]

/-- On an instruction that is neither a recognised arithmetic or logical operation, a
    carry-family operation nor a flag-quiet lift instruction, `stepMemF` is
    `lsemStepMem`. -/
theorem stepMemF_of_quiet {i : LinstrRM} (ha : aluFlagOp? i = none)
    (hk : carryArgs? i = none) (hw : wideArgs? i = none) (s : LstateM) :
    stepMemF i s = lsemStepMem i s := by
  unfold stepMemF
  cases hs : lsemStepMem i s with
  | some b => show some (withALUFlags i s b) = some b; rw [withALUFlags_of_none ha]
  | none => simp only [hk, hw]

/-- The `SET<cc>` wire is no recognised arithmetic or logical operation. -/
theorem aluFlagOp?_cmp (c : JasminDialect.JasminCmp) (wOp : Nat) (dst : String)
    (a b : LOperand) (tag : MemTag) :
    aluFlagOp? (.Lopn [.reg dst] (withWidthTag wOp (cmpName c)) [a, b], tag) = none := by
  have hs := JasminLsem.stripWidthTag_withWidthTag_cmpName wOp c
  have hne : ∀ m : String, stripWidthTag (withWidthTag 64 m) = m → cmpName c ≠ m →
      withWidthTag wOp (cmpName c) ≠ withWidthTag 64 m :=
    fun m h1 h2 he => h2 (hs.symm.trans (he ▸ h1))
  simp only [aluFlagOp?,
    if_neg (hne "ADD" (by decide +kernel) (by cases c <;> decide)),
    if_neg (hne "SUB" (by decide +kernel) (by cases c <;> decide)),
    if_neg (hne "AND" (by decide +kernel) (by cases c <;> decide)),
    if_neg (hne "OR" (by decide +kernel) (by cases c <;> decide)),
    if_neg (hne "XOR" (by decide +kernel) (by cases c <;> decide))]

/-- **The comparison step of the flag machine.** The `SET<cc>` wire writes the comparison
    bit `cmpBit c va vb : BitVec 1` to `dst` and advances the pc, as `lsemStepMem_cmp`; the
    carry and overflow flags are unchanged. -/
theorem stepMemF_cmp (c : JasminDialect.JasminCmp) (wOp : Nat) (dst a : String) (b : LOperand)
    (cd : Option Nat) (s : LstateM) {w : Nat} {va vb : BitVec w}
    (ha : s.reg.getW a w = some va) (hb : evalOperandN s.reg w b = some vb) :
    stepMemF (.Lopn [.reg dst] (withWidthTag wOp (cmpName c)) [.reg a, b], .reg cd) s
      = some ((s.setReg dst (JasminDialect.cmpBit c va vb)).nextPc) := by
  rw [stepMemF_of_lsemStepMem (lsemStepMem_cmp c wOp dst a b cd s ha hb),
    withALUFlags_of_none (aluFlagOp?_cmp c wOp dst (.reg a) b _)]

/-! ## 2. The flag-extended program state and step -/

/-- The flag-extended memref program state: the loop program state `LstatePM`
    (bundled base + function name) plus the zero-flag `zf` the emitted
    `CMP`/`Jcc` idiom communicates through.  The flag lives outside the register
    file: a flag-machine step never writes a flag *register*, so the base state
    tracks the unextended machine exactly. -/
structure LstateMF where
  /-- The wrapped loop program state (bundled memref base + function name). -/
  prog : LstatePM
  /-- `ZF`: set by the flag-`CMP`, read by the `Lcond NZ`/`Z` conditional. -/
  zf : Bool := false

/-- **The flag-extended eval arm.**  Three additive arms in front of the
    counter-register delegate:

    * the emitted flag-`CMP` (`cmpArgs?`) evaluates both operands at width 64,
      sets `zf := (va = vb)` (a compare is a subtract that only writes flags),
      and advances the pc — the store is untouched;
    * the emitted register-copy `MOV` and the array-ABI moves `MOVQ`, `LOAD:64`,
      `STORE:64` (`movRegArgs?`) write `dst := src` at `src`'s stored width and
      advance the pc, threading `zf`;
    * the flag-reading conditional (`flagCondCC?`) jumps (via
      `evalJumpMem`) iff `zf` matches the condition-code polarity, else falls
      through — the `jne`/`je` semantics;
    * a carry-family instruction (`carryArgs?`) that `lsemStepMem` does not step is the
      carry step `carryStep` on the base, and a flag-quiet lift instruction (`wideArgs?`)
      the step `wideStep`;
    * **everything else is `evalInstrPMemL` on the wrapped state**, `zf`
      threaded unchanged, with the carry and overflow flags of `withALUFlags` on the
      base. -/
def evalInstrPMemF (P : LprogM) (i : LinstrRM) (s : LstateMF) : Option LstateMF :=
  match cmpArgs? i with
  | some (a, b) =>
      match evalOperandN s.prog.base.reg 64 a, evalOperandN s.prog.base.reg 64 b with
      | some va, some vb =>
          some { prog := { s.prog with base := s.prog.base.nextPc }, zf := va == vb }
      | _, _ => none
  | none =>
  match movRegArgs? i with
  | some (dst, src) =>
      match readReg s.prog.base.reg (.reg src) with
      | some ⟨_, v⟩ =>
          some { s with prog := { s.prog with base := (s.prog.base.setReg dst v).nextPc } }
      | none => none
  | none =>
  match flagCondCC? i with
  | some (pol, lbl) =>
      if s.zf = pol then (evalJumpMem P lbl s.prog).map (fun p => { s with prog := p })
      else some { s with prog := { s.prog with base := s.prog.base.nextPc } }
  | none =>
  match evalInstrPMemL P i s.prog with
  | some p => some { s with prog := { p with base := withALUFlags i s.prog.base p.base } }
  | none =>
      match carryArgs? i with
      | some (op, d, a, b) =>
          (carryStep op d a b s.prog.base).map
            (fun b' => { s with prog := { s.prog with base := b' } })
      | none =>
          match wideArgs? i with
          | some w =>
              (wideStep w s.prog.base).map
                (fun b' => { s with prog := { s.prog with base := b' } })
          | none => none

/-- `step`: fetch (`findInstrMem` on the wrapped state) and flag-eval. -/
def lsemStepPMemF (P : LprogM) (s : LstateMF) : Option LstateMF :=
  match findInstrMem P s.prog with
  | some i => evalInstrPMemF P i s
  | none => none

/-- The flag-extended fuel-stepped interpreter: iterate `evalInstrPMemF`,
    halting (returning the state) when `findInstrMem` is `none` — the same
    recursion as `lsemFuelMemL`. -/
def lsemFuelMemF (P : LprogM) : Nat → LstateMF → Option LstateMF
  | 0, s => match findInstrMem P s.prog with
            | none => some s
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some s
      | some i =>
          match evalInstrPMemF P i s with
          | some s' => lsemFuelMemF P fuel s'
          | none => none

/-- A halted state (`findInstrMem = none`) takes no step. -/
theorem lsemFuelMemF_halt (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : lsemFuelMemF P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuelMemF, h]
  | succ n => simp [lsemFuelMemF, h]

/-- One fetched-and-evaluated step under the fuel iterator. -/
theorem lsemFuelMemF_step (P : LprogM) (fuel : Nat) (i : LinstrRM) (s s' : LstateMF)
    (hfetch : findInstrMem P s.prog = some i)
    (heval : evalInstrPMemF P i s = some s') :
    lsemFuelMemF P (fuel + 1) s = lsemFuelMemF P fuel s' := by
  rw [lsemFuelMemF, hfetch]
  simp only [heval]

/-- Fetch in a singleton program: the body at the pc, when the function names
    agree. -/
theorem findInstrMem_singleton (fn : String) (body : List LinstrRM) (s : LstatePM)
    (hfn : s.lfn = fn) :
    findInstrMem (singletonProgM fn body) s = body[s.base.lpc]? := by
  unfold findInstrMem
  rw [if_pos (show s.lfn = (singletonProgM fn body).lfn from hfn)]
  rfl

/-! ## 3. Conservativity: without the three emitted forms, this IS the counter-register machine -/

/-- On an instruction recognised by none of the flag arms (no flag-`CMP`, register copy,
    condition-code `Lcond`, carry-family, flag-quiet lift or flag-writing arithmetic),
    `evalInstrPMemF` is exactly the counter-register step on the wrapped state, `zf`
    threaded unchanged. -/
theorem evalInstrPMemF_delegate (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none) (hf : flagCondCC? i = none)
    (hk : carryArgs? i = none) (ha : aluFlagOp? i = none) (hw : wideArgs? i = none) :
    evalInstrPMemF P i s = (evalInstrPMemL P i s.prog).map (fun p => { s with prog := p }) := by
  unfold evalInstrPMemF
  rw [hc, hm, hf]
  cases evalInstrPMemL P i s.prog with
  | none => simp only [hk, hw, Option.map_none]
  | some p => simp only [withALUFlags_of_none ha, Option.map_some]

/-- A program with no emitted flag idiom: no flag-`CMP`, no register-copy `MOV`,
    no condition-code `Lcond`, no carry-family instruction, no flag-quiet lift
    instruction and no flag-writing arithmetic.  A memref loop program with a
    counter-register back-edge satisfies this whenever its counter register is not itself
    named `"Z"`/`"NZ"` (the two condition-code names) and its body has no 64-bit `ADD`,
    `SUB`, `AND`, `OR`, `XOR`, two-source `MOV` or `MULX`. -/
def NoFlagIdiom (P : LprogM) : Prop :=
  ∀ i ∈ P.body, cmpArgs? i = none ∧ movRegArgs? i = none ∧ flagCondCC? i = none
    ∧ carryArgs? i = none ∧ aluFlagOp? i = none ∧ wideArgs? i = none

/-- A fetched instruction is in the program body. -/
theorem findInstrMem_mem (P : LprogM) (s : LstatePM) (i : LinstrRM)
    (h : findInstrMem P s = some i) : i ∈ P.body := by
  unfold findInstrMem at h
  split at h
  · exact List.mem_of_getElem? h
  · exact absurd h (by simp)

/-- **The conservativity square.**  On a `NoFlagIdiom` program the flag machine
    is the counter-register machine: `lsemFuelMemF` is `lsemFuelMemL` on the
    wrapped state with the flag carried through untouched.  Every closed memref
    loop theorem
    (`loopMem_runBounded`, the chain-bridge exports, the nest folds) therefore
    describes the flag machine verbatim on its own programs. -/
theorem lsemFuelMemF_conservative (P : LprogM) (h : NoFlagIdiom P) :
    ∀ (fuel : Nat) (s : LstatePM) (zf : Bool),
      lsemFuelMemF P fuel { prog := s, zf := zf }
        = (lsemFuelMemL P fuel s).map (fun t => { prog := t, zf := zf }) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s zf
      rw [lsemFuelMemF, lsemFuelMemL]
      cases hf : findInstrMem P s with
      | none => simp only [Option.map_some]
      | some i => simp only [Option.map_none]
  | succ n ih =>
      intro s zf
      rw [lsemFuelMemF, lsemFuelMemL]
      cases hf : findInstrMem P s with
      | none => simp only [Option.map_some]
      | some i =>
          simp only []
          obtain ⟨hc, hm, hcc, hk, ha, hw⟩ := h i (findInstrMem_mem P s i hf)
          rw [evalInstrPMemF_delegate P i { prog := s, zf := zf } hc hm hcc hk ha hw]
          cases he : evalInstrPMemL P i s with
          | none => simp
          | some s' => simpa using ih s' zf

/-! ## 4. The emitted idiom, pinned to the lowering

`flagBackedge`/`flagLoopLinstrRM`/`guardedFlagLoopLinstrRM` restate — over the
typed instruction list — exactly the shapes `forLoopLcmdNRt` emits; the
`forLoopLcmdNRt_backedge`/`forLoopLcmdNRt_guard` pins prove the correspondence
against the lowering itself (the `Lopn` strings are the same `withWidthTag 64
"CMP"` terms, not re-typed mnemonics). -/

/-- The emitted back-edge segment: `CMP nReg,#0 ; Lcond NZ top` (renders
    `cmpq $0,%nReg ; jne .L<top>`). -/
def flagBackedge (nReg : String) (top : LLabel) : List LinstrRM :=
  [ (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none)
  , (.Lcond (.reg "NZ") top, MemTag.reg none) ]

/-- The flag-guarded counter loop — the EMITTED guard idiom over a general typed
    body: `Llabel top :: body ++ [CMP nReg,#0 ; Lcond NZ top]`.  The `LstateMF`
    analogue of the counter-guarded `loopLinstrRM` (which reads `nReg` directly
    at the `Lcond`); here the back-edge reads the `zf` the `CMP` materialised. -/
def flagLoopLinstrRM (top : LLabel) (nReg : String) (body : List LinstrRM) :
    List LinstrRM :=
  (LinstrR.Llabel .internal top, MemTag.reg none) :: (body ++ flagBackedge nReg top)

/-- The zero-trip-guarded runtime-count loop — the whole `forLoopLcmdNRt` loop
    skeleton (everything after the three seed `MOV`s): top guard `CMP nReg,#0 ;
    Lcond Z endL` (skip when the runtime count is `0`), the flag-guarded loop,
    and the skip target `Llabel endL`. -/
def guardedFlagLoopLinstrRM (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) : List LinstrRM :=
  (LinstrR.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], MemTag.reg none)
    :: (LinstrR.Lcond (.reg "Z") endL, MemTag.reg none)
    :: flagLoopLinstrRM top nReg body
    ++ [(LinstrR.Llabel .internal endL, MemTag.reg none)]

/-- **Pin (back-edge).**  `forLoopLcmdNRt` ends with exactly the modeled
    back-edge and skip target: `… ++ [CMP Lctr<d>,#0 ; Lcond NZ <d> ; Llabel
    <d+0x40000000>]` — the wire forms `flagBackedge (loopCtr d) d` models. -/
theorem forLoopLcmdNRt_backedge (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminDialect.JasminTy} {invTys : Ctxt JasminDialect.jasminDialect}
    (update : Com JasminDialect.jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    ∃ pre, forLoopLcmdNRt d accReg initOp countOp update invOps immSlotMap
      = pre ++ [ ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP")
                     [.reg (loopCtr d), .imm 0]⟩
               , ⟨0, .Lcond (.reg "NZ") d⟩
               , ⟨0, .Llabel .internal (d + 0x40000000)⟩ ] :=
  ⟨_, rfl⟩

/-- **Pin (zero-trip guard).**  `forLoopLcmdNRt` opens with the three seeds and
    exactly the modeled top guard: `MOV acc,initOp ; MOV Lidx,#0 ; MOV
    Lctr,countOp ; CMP Lctr,#0 ; Lcond Z <endL> ; Llabel <top>`. -/
theorem forLoopLcmdNRt_guard (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminDialect.JasminTy} {invTys : Ctxt JasminDialect.jasminDialect}
    (update : Com JasminDialect.jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    (forLoopLcmdNRt d accReg initOp countOp update invOps immSlotMap).take 6
      = [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
        , ⟨0, .Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0]⟩
        , ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [countOp]⟩
        , ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .imm 0]⟩
        , ⟨0, .Lcond (.reg "Z") (d + 0x40000000)⟩
        , ⟨0, .Llabel .internal d⟩ ] := by
  rw [forLoopLcmdNRt]
  rfl

/-! ## 5. Recognizer and step facts for the emitted instructions -/

/-- `cmpArgs?` recognises the emitted flag-`CMP nReg,#0`. -/
theorem cmpArgs?_cmp (dst : LOperand) (nReg : String) (tag : MemTag) :
    cmpArgs? (.Lopn [dst] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], tag)
      = some (.reg nReg, .imm 0) := by
  simp [cmpArgs?]

/-- The flag-`CMP nReg,#0` step: with the counter readable at width 64, set
    `zf := (v = 0)` and advance the pc — the store untouched. -/
theorem evalInstrPMemF_cmp (P : LprogM) (dst : LOperand) (nReg : String) (tag : MemTag)
    (s : LstateMF) (v : BitVec 64) (hread : s.prog.base.reg.getW nReg 64 = some v) :
    evalInstrPMemF P (.Lopn [dst] (withWidthTag 64 "CMP") [.reg nReg, .imm 0], tag) s
      = some { prog := { s.prog with base := s.prog.base.nextPc }, zf := v == 0#64 } := by
  unfold evalInstrPMemF
  rw [cmpArgs?_cmp]
  simp only []
  rw [show evalOperandN s.prog.base.reg 64 (.reg nReg) = some v from hread]
  rfl

/-- The `jne` step (`Lcond (.reg "NZ") lbl`): jump iff `zf = false`. -/
theorem evalInstrPMemF_jne (P : LprogM) (lbl : LLabel) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lcond (.reg "NZ") lbl, tag) s
      = if s.zf = false then (evalJumpMem P lbl s.prog).map (fun p => { s with prog := p })
        else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := rfl

/-- The `je` step (`Lcond (.reg "Z") lbl`): jump iff `zf = true`. -/
theorem evalInstrPMemF_je (P : LprogM) (lbl : LLabel) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lcond (.reg "Z") lbl, tag) s
      = if s.zf = true then (evalJumpMem P lbl s.prog).map (fun p => { s with prog := p })
        else some { s with prog := { s.prog with base := s.prog.base.nextPc } } := rfl

/-! ## 6. Guard equivalence: `CMP nReg,#0` materialises the counter test -/

/-- Extract the counter read from a positive `condNZ`: the register is readable
    at width 64 and non-zero. -/
theorem condNZ_true_getW {b : LstateM} {nReg : String}
    (h : condNZ b (.reg nReg) = true) :
    ∃ v, b.reg.getW nReg 64 = some v ∧ (v == 0#64) = false := by
  unfold condNZ at h
  cases hv : evalOperandN b.reg 64 (.reg nReg) with
  | none => rw [hv] at h; exact absurd h (by simp)
  | some v =>
      rw [hv] at h
      exact ⟨v, hv, by simpa using of_decide_eq_true h⟩

/-- **Guard equivalence.**  The `zf` the emitted `CMP nReg,#0` writes is the
    negation of the counter-register guard of `loopLinstrRM` reads: `zf = (v = 0)`
    where `condNZ = (v ≠ 0)`.  So `Lcond NZ` (jump iff `¬ zf`) takes the
    back-edge exactly when `Lcond (.reg nReg)` does. -/
theorem zf_after_cmp_eq_not_condNZ (b : LstateM) (nReg : String) (v : BitVec 64)
    (hread : b.reg.getW nReg 64 = some v) :
    (v == 0#64) = !(condNZ b (.reg nReg)) := by
  unfold condNZ
  rw [show evalOperandN b.reg 64 (.reg nReg) = some v from hread]
  by_cases hz : v = 0#64 <;> simp [hz]

/-! ## 7. Program-shape facts for the flag-guarded loop -/

/-- `findLabelMem` finds the loop's top label at position 0. -/
theorem findLabelMem_flagLoop (top : LLabel) (nReg : String) (body : List LinstrRM) :
    findLabelMem top (flagLoopLinstrRM top nReg body) = some 0 := by
  unfold findLabelMem flagLoopLinstrRM JasminLsemLabeled.findLabel
  rw [List.map_cons, List.findIdx?_cons]
  simp [JasminLsemLabeled.isLabel]

/-- Body position: index `1+k` is `body[k]` (index 0 is the label). -/
theorem flagLoop_body_pos (top : LLabel) (nReg : String) (body : List LinstrRM)
    (k : Nat) (hk : k < body.length) :
    (flagLoopLinstrRM top nReg body)[1 + k]? = body[k]? := by
  unfold flagLoopLinstrRM
  rw [show 1 + k = k + 1 from by omega, List.getElem?_cons_succ,
    List.getElem?_append_left (by simpa using hk)]

/-- The flag-`CMP` position: index `1 + body.length`. -/
theorem flagLoop_cmp_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (flagLoopLinstrRM top nReg body)[1 + body.length]? =
      some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
        MemTag.reg none) := by
  unfold flagLoopLinstrRM flagBackedge
  rw [show 1 + body.length = body.length + 1 from by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The back-edge `Lcond NZ` position: index `2 + body.length`. -/
theorem flagLoop_cond_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (flagLoopLinstrRM top nReg body)[2 + body.length]? =
      some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
  unfold flagLoopLinstrRM flagBackedge
  rw [show 2 + body.length = (body.length + 1) + 1 from by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega)]
  simp [show body.length + 1 - body.length = 1 from by omega]

/-- Past the loop end (pc `3 + body.length`) there is no instruction. -/
theorem flagLoop_end_pos (top : LLabel) (nReg : String) (body : List LinstrRM) :
    (flagLoopLinstrRM top nReg body)[3 + body.length]? = none := by
  apply List.getElem?_eq_none
  unfold flagLoopLinstrRM flagBackedge
  simp only [List.length_cons, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## 8. The straight-line segment over the flag machine

A body of plain `Lopn`s (no flag-`CMP`, no register-copy `MOV`) steps by `stepMemF`,
so a segment run is the flag body-fold `lsemStraightMemF` with `zf` threaded
unchanged — the flag analogue of `lsemFuelMemL_seg`. Where the straight-line
body-fold `lsemStraightMem` runs, `lsemStraightMemF` runs to the same state up to
the carry and overflow flags (`lsemStraightMemF_of_lsemStraightMem`). -/

/-- On a plain `Lopn` (not a flag-`CMP`, not a register-copy `MOV`),
    `evalInstrPMemF` is the flag machine's straight-line step `stepMemF` on the
    wrapped base, `zf` unchanged. -/
theorem evalInstrPMemF_lopn (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (hi : IsLopn i) (hc : cmpArgs? i = none) (hm : movRegArgs? i = none) :
    evalInstrPMemF P i s
      = (stepMemF i s.prog.base).map
          (fun b => { s with prog := { s.prog with base := b } }) := by
  have hf : flagCondCC? i = none := by
    obtain ⟨d, o, src, hd⟩ := hi
    unfold flagCondCC?
    rw [hd]
  unfold evalInstrPMemF stepMemF
  rw [hc, hm, hf]
  simp only []
  rw [evalInstrPMemL_lopn P i s.prog hi]
  cases lsemStepMem i s.prog.base with
  | some b => rfl
  | none =>
      simp only [Option.map_none]
      cases carryArgs? i with
      | none =>
          cases wideArgs? i with
          | none => rfl
          | some w => rfl
      | some q =>
          obtain ⟨op, d, a, b⟩ := q
          rfl

/-- The flag body-fold: `stepMemF` over a segment. -/
def lsemStraightMemF : List LinstrRM → LstateM → Option LstateM
  | [], s => some s
  | i :: is, s => (stepMemF i s).bind (lsemStraightMemF is)

@[simp] theorem lsemStraightMemF_nil (s : LstateM) : lsemStraightMemF [] s = some s := rfl

theorem lsemStraightMemF_cons (i : LinstrRM) (is : List LinstrRM) (s : LstateM) :
    lsemStraightMemF (i :: is) s = (stepMemF i s).bind (lsemStraightMemF is) := rfl

/-- The flag body-fold advances the pc by the body length. -/
theorem lsemStraightMemF_lpc :
    ∀ (body : List LinstrRM) (s b : LstateM),
      lsemStraightMemF body s = some b → b.lpc = s.lpc + body.length := by
  intro body
  induction body with
  | nil => intro s b h; simp only [lsemStraightMemF_nil, Option.some.injEq] at h; subst h; simp
  | cons i is ih =>
      intro s b h
      rw [lsemStraightMemF_cons] at h
      cases hstep : stepMemF i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s' =>
          rw [hstep, Option.bind_some] at h
          have h1 : s'.lpc = s.lpc + 1 := stepMemF_lpc_succ i s s' hstep
          have h2 : b.lpc = s'.lpc + is.length := ih s' b h
          rw [h2, h1, List.length_cons]; omega

/-- `lsemStepMem` neither reads nor writes the carry and overflow flags. -/
theorem lsemStepMem_setFlags (i : LinstrRM) (s : LstateM) (c o : Bool) :
    lsemStepMem i { s with cf := c, of := o }
      = (lsemStepMem i s).map (fun b => { b with cf := c, of := o }) := by
  have hg : ∀ x w n, ({ s with cf := c, of := o } : LstateM).getArr x w n = s.getArr x w n :=
    fun _ _ _ => rfl
  obtain ⟨li, tag⟩ := i
  cases tag <;> simp only [lsemStepMem, Option.map_map, Function.comp_def, hg] <;>
    (repeat' split) <;>
    simp_all [LstateM.setReg, LstateM.setArr, LstateM.nextPc, LstateM.storeMemC,
      Function.comp_def]

/-- **The bridge to the straight-line body-fold.**  Where `lsemStraightMem` runs a
    segment, `lsemStraightMemF` runs it from the same state with any flags to the
    same result up to the carry and overflow flags. -/
theorem lsemStraightMemF_of_lsemStraightMem :
    ∀ (seg : List LinstrRM) (s b : LstateM) (c o : Bool),
      lsemStraightMem seg s = some b →
      ∃ c' o', lsemStraightMemF seg { s with cf := c, of := o }
        = some { b with cf := c', of := o' } := by
  intro seg
  induction seg with
  | nil =>
      intro s b c o h
      simp only [lsemStraightMem_nil, Option.some.injEq] at h
      subst h
      exact ⟨c, o, rfl⟩
  | cons i is ih =>
      intro s b c o h
      rw [lsemStraightMem_cons] at h
      cases hstep : lsemStepMem i s with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hstep] at h
          simp only [] at h
          have h1 : lsemStepMem i { s with cf := c, of := o }
              = some { s1 with cf := c, of := o } := by
            rw [lsemStepMem_setFlags, hstep]; rfl
          obtain ⟨c1, o1, hw⟩ := withALUFlags_eq i { s with cf := c, of := o }
            { s1 with cf := c, of := o }
          obtain ⟨c', o', hr⟩ := ih s1 b c1 o1 h
          refine ⟨c', o', ?_⟩
          rw [lsemStraightMemF_cons, stepMemF_of_lsemStepMem h1, Option.bind_some, hw]
          exact hr

/-- A plain-`Lopn` body: every instruction is an `Lopn` and neither a flag-`CMP`
    nor a register-copy `MOV` — the fragment of the flag body-fold `lsemStraightMemF`. -/
def PlainLopnBody (body : List LinstrRM) : Prop :=
  ∀ i ∈ body, IsLopn i ∧ cmpArgs? i = none ∧ movRegArgs? i = none

/-- **Straight-line segment run with continuation fuel** (flag machine).  The
    flag analogue of `lsemFuelMemL_seg`: a plain-`Lopn` segment at
    positions `lpc .. lpc+|seg|-1` executes the flag body-fold `lsemStraightMemF`
    on the base and continues with `f` fuel, `zf` threaded unchanged. -/
theorem lsemFuelMemF_seg (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 : LstateM) (zf : Bool) (f : Nat),
      PlainLopnBody seg →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      lsemFuelMemF P (seg.length + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = (lsemStraightMemF seg b0).bind
            (fun b => lsemFuelMemF P f { prog := { base := b, lfn := fn }, zf := zf }) := by
  intro seg
  induction seg with
  | nil =>
      intro b0 zf f _ _
      simp only [List.length_nil, Nat.zero_add, lsemStraightMemF_nil, Option.bind_some]
  | cons i is ih =>
      intro b0 zf f hlopn hpos
      obtain ⟨hi, hc, hm⟩ := hlopn i (by simp)
      have his : PlainLopnBody is := fun j hj => hlopn j (by simp [hj])
      have hfetch : findInstrMem P
          ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
        show findInstrMem P { base := b0, lfn := fn } = some i
        unfold findInstrMem
        rw [if_pos (show ({ base := b0, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
        have := hpos 0 (by simp)
        simpa using this
      rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
        lsemFuelMemF, hfetch]
      simp only []
      rw [evalInstrPMemF_lopn P i _ hi hc hm]
      cases hstep : stepMemF i b0 with
      | none =>
          simp only [Option.map_none]
          rw [lsemStraightMemF_cons, hstep]; rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraightMemF_cons, hstep, Option.bind_some]
          have hb_lpc : b.lpc = b0.lpc + 1 := stepMemF_lpc_succ i b0 b hstep
          have hpos' : ∀ k, k < is.length → P.body[b.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            rw [hb_lpc, show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega]
            rw [hp]; simp
          exact ih b zf f his hpos'

/-- The bounded loop fold of the flag body-fold: `k` passes of `lsemStraightMemF body`,
    each followed by the back-edge's `setLpc 1`. The flag analogue of
    `runBoundedLoopMem`. -/
def runBoundedLoopMemF (body : List LinstrRM) : Nat → LstateM → Option LstateM
  | 0, s => some s
  | k + 1, s =>
      (lsemStraightMemF body s).bind (fun b => runBoundedLoopMemF body k (b.setLpc 1))

@[simp] theorem runBoundedLoopMemF_zero (body : List LinstrRM) (s : LstateM) :
    runBoundedLoopMemF body 0 s = some s := rfl

theorem runBoundedLoopMemF_succ (body : List LinstrRM) (k : Nat) (s : LstateM) :
    runBoundedLoopMemF body (k + 1) s =
      (lsemStraightMemF body s).bind (fun b => runBoundedLoopMemF body k (b.setLpc 1)) :=
  rfl

/-- After at least one pass the fold's state sits at the loop top (`lpc = 1`). -/
theorem runBoundedLoopMemF_succ_lpc :
    ∀ (k : Nat) (body : List LinstrRM) (s bj : LstateM),
      runBoundedLoopMemF body (k + 1) s = some bj → bj.lpc = 1 := by
  intro k
  induction k with
  | zero =>
      intro body s bj h
      rw [runBoundedLoopMemF_succ] at h
      cases hb : lsemStraightMemF body s with
      | none => rw [hb] at h; simp at h
      | some b =>
          rw [hb, Option.bind_some, runBoundedLoopMemF_zero] at h
          obtain rfl := Option.some.inj h
          simp
  | succ n ih =>
      intro body s bj h
      rw [runBoundedLoopMemF_succ] at h
      cases hb : lsemStraightMemF body s with
      | none => rw [hb] at h; simp at h
      | some b => rw [hb, Option.bind_some] at h; exact ih body (b.setLpc 1) bj h

/-- Peel the last pass of the flag loop fold. -/
theorem runBoundedLoopMemF_succ_right :
    ∀ (j : Nat) (body : List LinstrRM) (s : LstateM),
      runBoundedLoopMemF body (j + 1) s =
        (runBoundedLoopMemF body j s).bind
          (fun bj => (lsemStraightMemF body bj).map (fun b => b.setLpc 1)) := by
  intro j
  induction j with
  | zero =>
      intro body s
      simp only [runBoundedLoopMemF_succ, runBoundedLoopMemF_zero, Option.bind_some]
      cases lsemStraightMemF body s <;> simp
  | succ n ih =>
      intro body s
      rw [runBoundedLoopMemF_succ]
      conv_rhs => rw [runBoundedLoopMemF_succ]
      cases hb : lsemStraightMemF body s with
      | none => simp
      | some b => rw [Option.bind_some, Option.bind_some]; exact ih body (b.setLpc 1)

/-! ## 9. The single-pass core: body, flag-`CMP`, back-edge -/

/-- **Single loop pass — back-edge TAKEN** (flag machine).  From the top of the
    body (`lpc = 1`), if the flag body-fold runs to `b` and the counter is
    non-zero at `b` (`condNZ` — the SAME schedule hypothesis as `loopMem_runBounded`), then one
    pass (body + flag-`CMP` + taken `Lcond NZ`) consumes `body.length + 2` fuel
    and lands back at the top with base `b.setLpc 1` and `zf = false` (the `CMP`
    saw a non-zero counter). -/
theorem flagLoop_pass_taken (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hbody : PlainLopnBody body)
    (b0 b : LstateM) (zf : Bool) (f : Nat)
    (hpc : b0.lpc = 1)
    (hrun : lsemStraightMemF body b0 = some b)
    (htaken : condNZ b (.reg nReg) = true) :
    lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body))
        ((body.length + 2) + f) { prog := { base := b0, lfn := fn }, zf := zf }
      = lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body)) f
          { prog := { base := b.setLpc 1, lfn := fn }, zf := false } := by
  set P := singletonProgM fn (flagLoopLinstrRM top nReg body) with hP
  have hPbody : P.body = flagLoopLinstrRM top nReg body := rfl
  -- (1) the body block.
  have hseg := lsemFuelMemF_seg P fn rfl body b0 zf (2 + f) hbody
    (by intro k hk
        show P.body[b0.lpc + k]? = body[k]?
        rw [hPbody, hpc]; exact flagLoop_body_pos top nReg body k hk)
  rw [show (body.length + 2) + f = body.length + (2 + f) from by omega, hseg, hrun,
    Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMemF_lpc body b0 b hrun; rw [hpc] at this; omega
  obtain ⟨v, hread, hvne⟩ := condNZ_true_getW htaken
  -- (2) the flag-`CMP`: fetch at `1+|body|`, set `zf := (v == 0) = false`, pc+1.
  have hfetchCmp : findInstrMem P
      ({ prog := { base := b, lfn := fn }, zf := zf } : LstateMF).prog
        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
            MemTag.reg none) := by
    show findInstrMem P { base := b, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (flagLoopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact flagLoop_cmp_pos top nReg body
  have hevalCmp := evalInstrPMemF_cmp P (.reg nReg) nReg (MemTag.reg none)
    { prog := { base := b, lfn := fn }, zf := zf } v hread
  rw [show 2 + f = (1 + f) + 1 from by omega,
    lsemFuelMemF_step P (1 + f) _ _ _ hfetchCmp hevalCmp]
  -- (3) the back-edge `Lcond NZ`, taken (`zf = (v == 0) = false`).
  have hfetchCond : findInstrMem P
      ({ prog := { base := b.nextPc, lfn := fn }, zf := v == 0#64 } : LstateMF).prog
        = some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
    show findInstrMem P { base := b.nextPc, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (flagLoopLinstrRM top nReg body)[(b.nextPc).lpc]? = _
    rw [show (b.nextPc).lpc = 2 + body.length from by rw [LstateM.lpc_nextPc, hb_lpc]; omega]
    exact flagLoop_cond_pos top nReg body
  have hevalCond : evalInstrPMemF P (.Lcond (.reg "NZ") top, MemTag.reg none)
      { prog := { base := b.nextPc, lfn := fn }, zf := v == 0#64 }
        = some { prog := { base := b.setLpc 1, lfn := fn }, zf := false } := by
    rw [evalInstrPMemF_jne]
    rw [if_pos (show ({ prog := { base := b.nextPc, lfn := fn }, zf := v == 0#64 }
      : LstateMF).zf = false from hvne)]
    unfold evalJumpMem
    rw [show P.body = flagLoopLinstrRM top nReg body from rfl, findLabelMem_flagLoop]
    rw [show ({ prog := { base := b.nextPc, lfn := fn }, zf := v == 0#64 }
      : LstateMF).zf = false from hvne]
    rfl
  rw [show 1 + f = f + 1 from by omega,
    lsemFuelMemF_step P f _ _ _ hfetchCond hevalCond]

/-- **Single loop pass — HALT** (flag machine).  From the top of the body, if
    the body-fold runs to `b` and the counter reads **zero** at `b`, one pass
    consumes `body.length + 2` fuel: the flag-`CMP` sets `zf = true`, the
    `Lcond NZ` falls through past the program end, and the machine halts at the
    body-fold data with `zf = true`. -/
theorem flagLoop_pass_halt (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hbody : PlainLopnBody body)
    (b0 b : LstateM) (zf : Bool)
    (hpc : b0.lpc = 1)
    (hrun : lsemStraightMemF body b0 = some b)
    (hzero : b.reg.getW nReg 64 = some 0#64) :
    lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body))
        (body.length + 2) { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := b.nextPc.nextPc, lfn := fn }, zf := true } := by
  set P := singletonProgM fn (flagLoopLinstrRM top nReg body) with hP
  have hPbody : P.body = flagLoopLinstrRM top nReg body := rfl
  have hseg := lsemFuelMemF_seg P fn rfl body b0 zf 2 hbody
    (by intro k hk
        show P.body[b0.lpc + k]? = body[k]?
        rw [hPbody, hpc]; exact flagLoop_body_pos top nReg body k hk)
  rw [hseg, hrun, Option.bind_some]
  have hb_lpc : b.lpc = 1 + body.length := by
    have := lsemStraightMemF_lpc body b0 b hrun; rw [hpc] at this; omega
  -- the flag-`CMP` (fuel 2 → 1): zf := (0 == 0) = true.
  have hfetchCmp : findInstrMem P
      ({ prog := { base := b, lfn := fn }, zf := zf } : LstateMF).prog
        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
            MemTag.reg none) := by
    show findInstrMem P { base := b, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (flagLoopLinstrRM top nReg body)[b.lpc]? = _
    rw [hb_lpc]; exact flagLoop_cmp_pos top nReg body
  have hevalCmp := evalInstrPMemF_cmp P (.reg nReg) nReg (MemTag.reg none)
    { prog := { base := b, lfn := fn }, zf := zf } (0#64) hzero
  rw [show (2 : Nat) = 1 + 1 from rfl,
    lsemFuelMemF_step P 1 _ _ _ hfetchCmp hevalCmp]
  -- the `Lcond NZ` (fuel 1 → 0): zf = true ≠ false, fall through.
  have hfetchCond : findInstrMem P
      ({ prog := { base := b.nextPc, lfn := fn }, zf := (0#64 == 0#64) } : LstateMF).prog
        = some (.Lcond (.reg "NZ") top, MemTag.reg none) := by
    show findInstrMem P { base := b.nextPc, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (flagLoopLinstrRM top nReg body)[(b.nextPc).lpc]? = _
    rw [show (b.nextPc).lpc = 2 + body.length from by rw [LstateM.lpc_nextPc, hb_lpc]; omega]
    exact flagLoop_cond_pos top nReg body
  have hevalCond : evalInstrPMemF P (.Lcond (.reg "NZ") top, MemTag.reg none)
      { prog := { base := b.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
        = some { prog := { base := b.nextPc.nextPc, lfn := fn }, zf := true } := by
    rw [evalInstrPMemF_jne]
    rw [if_neg (show ¬ ({ prog := { base := b.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
      : LstateMF).zf = false from by simp)]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl,
    lsemFuelMemF_step P 0 _ _ _ hfetchCond hevalCond]
  -- halted: pc `3 + |body|` is past the program end.
  apply lsemFuelMemF_halt
  show findInstrMem P { base := b.nextPc.nextPc, lfn := fn } = none
  rw [hP, findInstrMem_singleton fn _ _ rfl]
  show (flagLoopLinstrRM top nReg body)[(b.nextPc.nextPc).lpc]? = none
  rw [show (b.nextPc.nextPc).lpc = 3 + body.length from by
    rw [LstateM.lpc_nextPc, LstateM.lpc_nextPc, hb_lpc]; omega]
  exact flagLoop_end_pos top nReg body

/-! ## 10. The `n`-fold re-tie: the counter-loop fold, realised by the EMITTED guard idiom -/

/-- **Taken chain** (flag machine): the first `j` passes (back-edge taken after
    each — the same `condNZ` schedule as `loopMem_taken_chain`) factor
    through the fold `runBoundedLoopMemF`; each pass costs `|body| + 2` fuel
    (body + flag-`CMP` + `Lcond`), and every reentry after the first pass
    carries `zf = false` (the just-run `CMP` saw a non-zero counter). -/
theorem flagLoop_taken_chain (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hbody : PlainLopnBody body)
    (b0 : LstateM) (hpc : b0.lpc = 1) :
    ∀ (j f : Nat) (zf : Bool),
      (∀ i, 0 < i → i ≤ j → ∀ bi, runBoundedLoopMemF body i b0 = some bi →
        condNZ bi (.reg nReg) = true) →
      lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body))
          (j * (body.length + 2) + f) { prog := { base := b0, lfn := fn }, zf := zf }
        = (runBoundedLoopMemF body j b0).bind
            (fun bj => lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body)) f
              { prog := { base := bj, lfn := fn },
                zf := if j = 0 then zf else false }) := by
  set P := singletonProgM fn (flagLoopLinstrRM top nReg body) with hP
  intro j
  induction j with
  | zero =>
      intro f zf _
      simp only [Nat.zero_mul, Nat.zero_add, runBoundedLoopMemF_zero, Option.bind_some,
        reduceIte]
  | succ n ih =>
      intro f zf htk
      have htk' : ∀ i, 0 < i → i ≤ n → ∀ bi, runBoundedLoopMemF body i b0 = some bi →
          condNZ bi (.reg nReg) = true := fun i hi hin bi hbi => htk i hi (by omega) bi hbi
      have hfuel : (n + 1) * (body.length + 2) + f
          = n * (body.length + 2) + ((body.length + 2) + f) := by ring
      rw [hfuel, ih ((body.length + 2) + f) zf htk']
      rw [runBoundedLoopMemF_succ_right]
      cases hj : runBoundedLoopMemF body n b0 with
      | none => simp
      | some bj =>
          simp only [Option.bind_some]
          have hbj_lpc : bj.lpc = 1 := by
            cases n with
            | zero =>
                rw [runBoundedLoopMemF_zero] at hj
                obtain rfl := Option.some.inj hj; exact hpc
            | succ k => exact runBoundedLoopMemF_succ_lpc k body b0 bj hj
          cases hb : lsemStraightMemF body bj with
          | none =>
              have hseg := lsemFuelMemF_seg P fn rfl body bj
                (if n = 0 then zf else false) (2 + f) hbody
                (by intro k hk
                    show P.body[bj.lpc + k]? = body[k]?
                    rw [show P.body = flagLoopLinstrRM top nReg body from rfl, hbj_lpc]
                    exact flagLoop_body_pos top nReg body k hk)
              rw [show (body.length + 2) + f = body.length + (2 + f) from by omega, hseg,
                hb]
              simp
          | some blast =>
              simp only [Option.map_some, Option.bind_some]
              have htaken : condNZ blast (.reg nReg) = true := by
                have hfold : runBoundedLoopMemF body (n + 1) b0
                    = some (blast.setLpc 1) := by
                  rw [runBoundedLoopMemF_succ_right, hj, Option.bind_some, hb,
                    Option.map_some]
                have := htk (n + 1) (by omega) (by omega) (blast.setLpc 1) hfold
                rwa [condNZ_setLpc] at this
              have hpass := flagLoop_pass_taken fn top nReg body hbody bj blast
                (if n = 0 then zf else false) f hbj_lpc hb htaken
              rw [← hP] at hpass
              rw [hpass]
              simp

/-- **The bounded-loop re-tie over the EMITTED guard idiom.**
    `loopMem_runBounded`, lifted to the flag-guarded loop `flagLoopLinstrRM` —
    the literal `CMP nReg,#0 ; Lcond NZ top` back-edge `forLoopLcmdNRt` emits
    (pin: `forLoopLcmdNRt_backedge`) — run under the flag machine
    `lsemFuelMemF`:

    given the SAME counter schedule as `loopMem_runBounded` (back-edge taken after iterations
    `1..m-1`; the counter *reads zero* after the `m`-th body-fold — the emitted
    `CMP` evaluates the counter, so the exit needs a zero read, not only
    a read miss), the machine runs `m·(|body|+2)` steps and halts in a state
    whose base agrees with the flag loop fold `runBoundedLoopMemF body m` on the
    register store and the array carrier, with `zf = true` (the exit compare). -/
theorem flagLoop_runBounded (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hbody : PlainLopnBody body)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMemF body (m - 1) b0 = some bprev)
    (hlast : lsemStraightMemF body bprev = some blast)
    (hbfin : runBoundedLoopMemF body m b0 = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMemF body i b0 = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : blast.reg.getW nReg 64 = some 0#64) :
    ∃ t : LstateMF,
      lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body))
          (m * (body.length + 2)) { prog := { base := b0, lfn := fn }, zf := zf }
            = some t
        ∧ t.prog.base.reg.lvm = bfin.reg.lvm ∧ t.prog.base.larr = bfin.larr
        ∧ t.zf = true := by
  set P := singletonProgM fn (flagLoopLinstrRM top nReg body) with hP
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprev
  have htk : ∀ i, 0 < i → i ≤ k → ∀ bi, runBoundedLoopMemF body i b0 = some bi →
      condNZ bi (.reg nReg) = true := fun i hi hik bi hbi => htaken i hi (by omega) bi hbi
  have hchain := flagLoop_taken_chain fn top nReg body hbody b0 hpc k
    (body.length + 2) zf htk
  rw [show (k + 1) * (body.length + 2) = k * (body.length + 2) + (body.length + 2)
    from by ring, hchain, hprev, Option.bind_some]
  have hprev_lpc : bprev.lpc = 1 := by
    cases k with
    | zero =>
        rw [runBoundedLoopMemF_zero] at hprev
        obtain rfl := Option.some.inj hprev; exact hpc
    | succ j => exact runBoundedLoopMemF_succ_lpc j body b0 bprev hprev
  have hhaltpass := flagLoop_pass_halt fn top nReg body hbody bprev blast
    (if k = 0 then zf else false) hprev_lpc hlast hzero
  rw [← hP] at hhaltpass
  rw [hhaltpass]
  have hbfin' : bfin = blast.setLpc 1 := by
    have : runBoundedLoopMemF body (k + 1) b0 = some (blast.setLpc 1) := by
      rw [runBoundedLoopMemF_succ_right, hprev, Option.bind_some, hlast, Option.map_some]
    rw [this] at hbfin; exact (Option.some.inj hbfin).symm
  exact ⟨_, rfl, by rw [hbfin']; rfl, by rw [hbfin']; rfl, rfl⟩

/-! ## 11. The zero-trip top-guard skip -/

/-- The skip label of the guarded shape resolves past the loop: with a label-free
    (all-`Lopn`) body and `top ≠ endL`, the first `Llabel _ endL` is the skip
    target at index `body.length + 5`. -/
theorem findLabelMem_guarded_endL (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i) (htop : top ≠ endL) :
    findLabelMem endL (guardedFlagLoopLinstrRM top endL nReg body)
      = some (body.length + 5) := by
  unfold findLabelMem guardedFlagLoopLinstrRM flagLoopLinstrRM flagBackedge
    JasminLsemLabeled.findLabel
  simp only [List.map_cons, List.map_append, List.cons_append, List.findIdx?_cons]
  rw [show JasminLsemLabeled.isLabel endL (.Lopn [.reg nReg] (withWidthTag 64 "CMP")
      [.reg nReg, .imm 0]) = false from rfl]
  rw [show JasminLsemLabeled.isLabel endL (.Lcond (.reg "Z") endL) = false from rfl]
  rw [show JasminLsemLabeled.isLabel endL (.Llabel .internal top) = false from by
    simp only [JasminLsemLabeled.isLabel, beq_eq_false_iff_ne]
    exact fun h => htop h.symm]
  simp only [Bool.false_eq_true, if_false, List.map_nil]
  rw [List.findIdx?_append, List.findIdx?_append]
  have hbodyNone : (body.map Prod.fst).findIdx? (JasminLsemLabeled.isLabel endL)
      = none := by
    rw [List.findIdx?_eq_none_iff]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain ⟨d, o, src, hd⟩ := hlopn i hi
    show JasminLsemLabeled.isLabel endL i.fst = false
    rw [hd]
    rfl
  rw [hbodyNone]
  rw [show List.findIdx? (JasminLsemLabeled.isLabel endL)
      [LinstrR.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
       LinstrR.Lcond (.reg "NZ") top] = none from rfl]
  rw [show List.findIdx? (JasminLsemLabeled.isLabel endL)
      [LinstrR.Llabel .internal endL] = some 0 from by
    rw [List.findIdx?_cons, show JasminLsemLabeled.isLabel endL (.Llabel .internal endL)
      = true from by simp [JasminLsemLabeled.isLabel]]
    rfl]
  simp only [Option.map_none, Option.none_or, Option.map_some, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  congr 1
  omega

/-- **Zero-trip top-guard skip** (the `Lcond Z` forward skip).  The guarded
    runtime-count shape `guardedFlagLoopLinstrRM` — the whole `forLoopLcmdNRt`
    loop skeleton (pin: `forLoopLcmdNRt_guard`) — run from its head with a
    **zero** counter: the guard `CMP nReg,#0` sets `zf = true`, the `Lcond Z
    endL` (`je`) jumps to the skip label, and the machine halts having executed
    **no body instruction** — the register store and the array carrier are
    exactly the entry's (`runBoundedLoopMemF body 0` = the identity), so a
    `count = 0` loop denotes correctly. -/
theorem guardedFlagLoop_zeroTrip (fn : String) (top endL : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i) (htop : top ≠ endL)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hzero : b0.reg.getW nReg 64 = some 0#64) (fuel : Nat) :
    lsemFuelMemF (singletonProgM fn (guardedFlagLoopLinstrRM top endL nReg body))
        (fuel + 2) { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := b0.nextPc.setLpc (body.length + 6), lfn := fn },
               zf := true } := by
  set P := singletonProgM fn (guardedFlagLoopLinstrRM top endL nReg body) with hP
  -- step 1: the guard `CMP nReg,#0` at pc 0.
  have hfetch0 : findInstrMem P
      ({ prog := { base := b0, lfn := fn }, zf := zf } : LstateMF).prog
        = some (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .imm 0],
            MemTag.reg none) := by
    show findInstrMem P { base := b0, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (guardedFlagLoopLinstrRM top endL nReg body)[b0.lpc]? = _
    rw [hpc]
    rfl
  have heval0 := evalInstrPMemF_cmp P (.reg nReg) nReg (MemTag.reg none)
    { prog := { base := b0, lfn := fn }, zf := zf } (0#64) hzero
  rw [show fuel + 2 = (fuel + 1) + 1 from by omega,
    lsemFuelMemF_step P (fuel + 1) _ _ _ hfetch0 heval0]
  -- step 2: the `Lcond Z endL` at pc 1, taken (`zf = (0 == 0) = true`).
  have hfetch1 : findInstrMem P
      ({ prog := { base := b0.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
        : LstateMF).prog
        = some (.Lcond (.reg "Z") endL, MemTag.reg none) := by
    show findInstrMem P { base := b0.nextPc, lfn := fn } = _
    rw [hP, findInstrMem_singleton fn _ _ rfl]
    show (guardedFlagLoopLinstrRM top endL nReg body)[(b0.nextPc).lpc]? = _
    rw [show (b0.nextPc).lpc = 1 from by rw [LstateM.lpc_nextPc, hpc]]
    rfl
  have heval1 : evalInstrPMemF P (.Lcond (.reg "Z") endL, MemTag.reg none)
      { prog := { base := b0.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
        = some { prog := { base := b0.nextPc.setLpc (body.length + 6), lfn := fn },
                 zf := true } := by
    rw [evalInstrPMemF_je]
    rw [if_pos (show ({ prog := { base := b0.nextPc, lfn := fn }, zf := (0#64 == 0#64) }
      : LstateMF).zf = true from by simp)]
    unfold evalJumpMem
    rw [show P.body = guardedFlagLoopLinstrRM top endL nReg body from rfl,
      findLabelMem_guarded_endL top endL nReg body hlopn htop]
    show some _ = some _
    congr 2
  rw [lsemFuelMemF_step P fuel _ _ _ hfetch1 heval1]
  -- the jump target `|body| + 6` is past the program end: halt.
  apply lsemFuelMemF_halt
  show findInstrMem P
    { base := b0.nextPc.setLpc (body.length + 6), lfn := fn } = none
  rw [hP, findInstrMem_singleton fn _ _ rfl]
  show (guardedFlagLoopLinstrRM top endL nReg body)[(b0.nextPc.setLpc
    (body.length + 6)).lpc]? = none
  rw [LstateM.lpc_setLpc]
  apply List.getElem?_eq_none
  unfold guardedFlagLoopLinstrRM flagLoopLinstrRM flagBackedge
  simp only [List.length_cons, List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## 12. Validate: the REAL rendered `forLoopNRt` lowering under the flag machine

`loopSmokeRtBody` (`JasminLprogExport`) is the actual `comLToBody` rendering of
`ComL.forLoopNRt` (runtime-count squaring, `invOps = []`):

    MOV:64 r2, a1 ; MOV:64 Lidx2, #0 ; MOV:64 Lctr2, a0 ;
    CMP:64 Lctr2, #0 ; Lcond Z <endL> ; Llabel <top> ;
    MUL:64 L2_r2, r2, r2 ; MOV:64 r2, L2_r2 ;
    ADD:64 Lidx2, #1 ; SUB:64 Lctr2, #1 ;
    CMP:64 Lctr2, #0 ; Lcond NZ <top> ; Llabel <endL> ; Lret

— reg-copy `MOV` seeds/feedback, the zero-trip guard, and the flag-`CMP`/`jne`
back-edge, none of which step under the counter-register machine.  The flag
machine runs the stream end to end (the trailing `Lret` — function return, outside the loop
idiom — is dropped; program-end is the halt). -/

/-- The real rendered runtime-count loop, lifted to the typed instruction list
    (register bindings only in this kernel), `Lret` dropped. -/
def rtLoopRM (_ : Unit) : List LinstrRM :=
  ((loopSmokeRtBody ()).map (fun i => (i.li_i, MemTag.reg none))).dropLast

/-- The rendered loop as a singleton program. -/
def rtLoopProg (_ : Unit) : LprogM := singletonProgM "f" (rtLoopRM ())

/-- Entry state: the resolved arguments `a0 = count`, `a1 = seed`
    (`loopSmokeRtProg`'s resolution), pc 0, flag clear. -/
def rtStart (seed count : BitVec 64) : LstateMF :=
  { prog := { base := (({} : LstateM).setReg "a0" count).setReg "a1" seed, lfn := "f" }
    zf := false }

/-- **Validate (functional, runtime count 2).**  The flag machine runs the real
    rendered lowering and the accumulator `r2` decodes to the source denotation
    `ComL.denote loopSmokeRtProg [3, 2] = 3^(2²) = 81` — the emitted
    `CMP`/`jne` back-edge was followed twice and the guard fell through. -/
example :
    (lsemFuelMemF (rtLoopProg ()) 40 (rtStart 3 2)).map
        (fun t => decodeM t.prog.base "r2" 64)
      = some (some (ComL.denote loopSmokeRtProg
          (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil)))) := by
  native_decide

/-- **Validate (zero-trip skip, runtime count 0).**  With runtime count `0` the
    top guard's `Lcond Z` jumps over the loop: the accumulator is the untouched
    seed (`= ComL.denote` at count `0` — the empty fold), and the body never
    ran. -/
example :
    (lsemFuelMemF (rtLoopProg ()) 40 (rtStart 3 0)).map
        (fun t => decodeM t.prog.base "r2" 64)
      = some (some (ComL.denote loopSmokeRtProg
          (.cons (3 : BitVec 64) (.cons (0 : BitVec 64) .nil)))) := by
  native_decide

/-- **Validate (halt, not stuck).**  Both runs halt (`some`), i.e.
    every rendered instruction — the reg-copy `MOV`s, the two `CMP`s, the
    `je`/`jne` conditionals — has a step. -/
example : (lsemFuelMemF (rtLoopProg ()) 40 (rtStart 3 2)).isSome
    ∧ (lsemFuelMemF (rtLoopProg ()) 40 (rtStart 3 0)).isSome := by
  native_decide

/-! ### Carry chains

The instruction shapes of `Fe25519LfundefBridge.jinstrToLinstrR` (`.add d s` is
`Lopn [d] ADD:64 [d, s]`, and likewise `ADC`, `SUB`, `SBB`, `XOR`, `ADCX`, `ADOX`) run
under the flag machine with the carries of the decoder machine. -/

/-- A register-typed instruction `Lopn [.reg d] (withWidthTag 64 m) [.reg d, .reg s]`. -/
def twoAddrRM (m d s : String) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 m) [.reg d, .reg s], MemTag.reg none)

/-- A flag-machine start state with the given 64-bit registers, pc `0`, flags clear. -/
def regStart (vs : List (String × BitVec 64)) : LstateMF :=
  { prog := { base := vs.foldl (fun b p => b.setReg p.1 p.2) ({} : LstateM), lfn := "f" } }

/-- The registers `rs` at width `64` and the two flags after running `body`. -/
def runRegs (body : List LinstrRM) (vs : List (String × BitVec 64)) (rs : List String) :
    Option (List (Option (BitVec 64)) × Bool × Bool) :=
  (lsemFuelMemF (singletonProgM "f" body) (body.length + 1) (regStart vs)).map fun t =>
    (rs.map (fun r => t.prog.base.reg.getW r 64), t.prog.base.cf, t.prog.base.of)

/-- The all-ones word `2^64 - 1`. -/
def wMax : BitVec 64 := BitVec.allOnes 64

/- `ADD` then `ADC`: `2^64 - 1 + 1` carries into `5 + 7`. -/
#kat runRegs [twoAddrRM "ADD" "R8" "R9", twoAddrRM "ADC" "R10" "R11"]
    [("R8", wMax), ("R9", 1), ("R10", 5), ("R11", 7)] ["R8", "R10"]
  == some ([some 0, some 13], false, false)

/- `XOR` clears both flags; `ADCX` and `ADOX` run two independent chains. -/
#kat runRegs [twoAddrRM "XOR" "R12" "R12", twoAddrRM "ADCX" "R8" "R9",
      twoAddrRM "ADOX" "R10" "R11", twoAddrRM "ADCX" "R13" "R12",
      twoAddrRM "ADOX" "R14" "R12"]
    [("R8", wMax), ("R9", 1), ("R10", wMax), ("R11", 1), ("R12", 3), ("R13", 5),
      ("R14", 7)] ["R8", "R10", "R13", "R14"]
  == some ([some 0, some 0, some 6, some 8], false, false)

/- `SUB` then `SBB`: `0 - 1` borrows from `5 - 2`. -/
#kat runRegs [twoAddrRM "SUB" "R8" "R9", twoAddrRM "SBB" "R10" "R11"]
    [("R8", 0), ("R9", 1), ("R10", 5), ("R11", 2)] ["R8", "R10"]
  == some ([some wMax, some 2], false, false)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
