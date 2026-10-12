/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
public import Transfer.Base.Related

/-!
# Faithful `lsem` for the widening-multiply / carry-chain fragment

The modules `JasminLsemSimulation`, `JasminLsemRobust`, `JasminLsemWidthN` and
`JasminLsemShift` bring `regArith`, `regConst`, the width-mixing `select`, and the
immediate shifts (`shrImm`/`shlImm`/`sarImm`) into the unconditional functional ∧
constant-time `lsem` simulation. This module adds the widening-multiply /
carry-chain trio:

* **`mulhi w`** — `[reg w, reg w] → reg w`: uniform width, expressible in the
  single-width store;
* **`addCarryLo w` / `addCarryHi w`** — carry-coupled: the carry-in is `.reg 1`
  and `addCarryHi` *returns* `.reg 1`; the width-tagged `LstateN` carries both
  (read two `.reg w` and one `.reg 1`, write `addCarryWord`/`carryOutBit`).

The `JasminLsemWidthN` `LstateN` (width-tagged store), `StoreAgreesN` invariant,
`encodeN`/`decodeN`, and the induction skeleton of `JasminLsemSimulation` /
`JasminLsemWidthN` are reused verbatim; only the step function gains three arms.

## The three roles, faithful to the wire form `opToLinstrR` already emits

`opToLinstrR` (`JasminLprogExport.lean`) lowers the trio to single-output `Lopn`s
whose mnemonic names the *role* the binding plays (the byte reader reassembles
each into the matching `MULX`/`ADCX`/`ADOX` `sopn`). **No wire change is made
here**; the model reads exactly what the emit path already produces:

* **`mulhi w`** ↦ `Lopn [.reg dst] (withWidthTag w "MULXHI") [a, b]` — two
  `.reg w` sources, one `.reg w` result. The step reads `a, b` at the data width
  `w` (recovered from the store tag) and writes `mulHiW a b = (mulhi w).denote …`
  (the high word of the `w × w` product — a `BitVec w`, *uniform* out).
* **`addCarryLo w`** ↦ `Lopn [.reg dst] (withWidthTag w "ADCX") [a, b, cin]` —
  two `.reg w` sources and a `.reg 1` carry-in, one `.reg w` result. The step
  reads `a, b` at width `w` and `cin` at width 1, writing `addCarryWord a b cin =
  (addCarryLo w).denote …` (the low data word `a + b + cin`).
* **`addCarryHi w`** ↦ `Lopn [.reg dst] (withWidthTag w "ADCXHI") [a, b, cin]` —
  same three sources but a **`.reg 1` result** (the propagated carry-out). The
  step writes `carryOutBit a b cin = (addCarryHi w).denote …`, a `BitVec 1`. This
  is the second **width-mixing** op (after `select`): two `BitVec w`
  data words and a `BitVec 1` carry in *and* out, all in one instruction — the
  width-tagged store carries the `BitVec 1` destination alongside the `BitVec w`
  data without strain.

A multi-limb Montgomery / pairing-field multiply is then a data-flow thread:
`mulhi`/`regArith mul` for the partial products, `addCarryLo`/`addCarryHi`
chaining the `reg 1` carry through the limbs — no hidden flag state, exactly the
two independent CF/OF accumulators an `ADCX`-only / `ADOX`-only sequence realises.

## Trocq (`Related`) where it helps, and where it does not

Like the structured shifts of `JasminLsemShift`, the per-op denotation equality is a
*representation* fact: the value the structured linear step computes (read sources
at their store widths, run the pure `BitVec` function) *realizes* the abstract
dialect denotation. Here the realization is **definitional** — the step writes
exactly `mulHiW`/`addCarryWord`/`carryOutBit`, which *are* the `.denote` arms — so
each square is `rfl`, registered as a `Trocq.Related` identity-encoding witness
(`relatedMulHi`/`relatedAddCarryWord`/`relatedCarryOut`) for symmetry with
`relatedStructShr` and `CompilerRegistry`'s op-leaf realizers. Where Trocq does
**not** fit (as in `JasminLsemShift`): the `Option`-partiality descent of the step
over the `LinstrR` syntax and the de-Bruijn `StoreAgreesN` bookkeeping reuse
the `JasminLsemWidthN` machinery directly.

## Op set covered

`regArith ∪ regConst ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
addCarryHi` — the `ScalarMulCarryN` predicate, which subsumes
`ScalarShiftN` (`ScalarMulCarryN.of_scalarShiftN`). The `regConst` arm carries the
immediate-`MOV` image `Lopn [.reg dst] (withWidthTag w "MOV") [.imm n]`; its output
width `w` is recovered from the width tag (`widthFromTag`), which pins it on the two
wire-distinguished widths `w ∈ {64, 32}` (the `const` constructor's `hwn`
hypothesis). Outside this op set, for the same frozen-wire reasons as in
`JasminLsemWidthN`/`JasminLsemShift`: `castW` (output width not recoverable from
the wire), `stackLoad`/`stackStore`
(the memory/array carrier, an orthogonal state axis), `vpackZMM`/`extCall`/`callN`
(SIMD / opaque-leaf axes).

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open Transfer (Related)

/-! ## 1. The realizers and their `Trocq.Related` squares

Each structured instruction's linear step computes a pure `BitVec` function of the
sources read out of the width-tagged store. For the trio that function is exactly
the dialect denotation (`mulHiW` / `addCarryWord` / `carryOutBit`), so each
representation square is `rfl`; it is registered as a `Related` identity-
encoding witness for symmetry with `relatedStructShr`. -/

/-- **Representation square (MULXHI).** The structured high-word realizer
    `mulHiW a b` equals the dialect's `mulhi` denotation (definitionally — the
    step writes exactly `mulHiW`). Registered as a `Related` identity-encoding
    witness, this module's analogue of `relatedStructShr`. -/
instance relatedMulHi {w : Nat} (a b : BitVec w) :
    Related (id : BitVec w → BitVec w) (mulHiW a b) (mulHiW a b) where
  rel := rfl

/-- **Representation square (ADCX data word).** -/
instance relatedAddCarryWord {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    Related (id : BitVec w → BitVec w) (addCarryWord a b cin) (addCarryWord a b cin) where
  rel := rfl

/-- **Representation square (ADCXHI carry-out bit).** Note the carrier is
    `BitVec 1` — the width-mixing output the store carries alongside the data. -/
instance relatedCarryOut {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    Related (id : BitVec 1 → BitVec 1) (carryOutBit a b cin) (carryOutBit a b cin) where
  rel := rfl

/-! ## 2. The mnemonics round-trip through the width tag

The three role mnemonics carry the same `withWidthTag w` as every other op, so
they round-trip through `stripWidthTag ∘ withWidthTag` (kernel evaluation per
width branch, as for `MOV`/`CMOV`/`SHR`). -/

theorem stripWidthTag_withWidthTag_MULXHI (w : Nat) :
    stripWidthTag (withWidthTag w "MULXHI") = "MULXHI" := by
  unfold withWidthTag; split <;> decide +kernel

theorem stripWidthTag_withWidthTag_ADCX (w : Nat) :
    stripWidthTag (withWidthTag w "ADCX") = "ADCX" := by
  unfold withWidthTag; split <;> decide +kernel

theorem stripWidthTag_withWidthTag_ADCXHI (w : Nat) :
    stripWidthTag (withWidthTag w "ADCXHI") = "ADCXHI" := by
  unfold withWidthTag; split <;> decide +kernel

theorem stripWidthTag_withWidthTag_SBB (w : Nat) :
    stripWidthTag (withWidthTag w "SBB") = "SBB" := by
  unfold withWidthTag; split <;> decide +kernel

theorem stripWidthTag_withWidthTag_SBBHI (w : Nat) :
    stripWidthTag (withWidthTag w "SBBHI") = "SBBHI" := by
  unfold withWidthTag; split <;> decide +kernel

/-! ## 3. The mul/carry-aware step `lsemStepMC`

`lsemStepMC` adds exactly three arms — the structured `MULXHI`, `ADCX`, `ADCXHI`
instructions — and delegates **everything else** (control flow, `regArith`,
`select`, the structured shift forms, `regConst`) verbatim to
`lsemStepSh` (which itself adds the `SAR` arm and delegates the rest to
`JasminLsemWidthN`'s `lsemStepN`). (None of the trio is reachable through `lsemStepSh`:
`MULXHI` has the `[a,b]` shape but is not `SAR` / in `applyOpnN`; `ADCX`/`ADCXHI`
have the `[a,b,cin]` shape but are not `SAR`/`CMOV` — so `lsemStepSh` returns
`none` on all three, and the three arms are the faithful semantics.) Each arm
reads its sources at their op-determined widths
(`a, b` at the data width `w` recovered from `a`'s store tag, `cin` at width 1),
applies the pure denotation, writes the op-determined-width destination, and
advances the pc — faithful to `eval_instr`'s `Lopn` (evaluate sources, run the
`exec_sopn` data effect, write the destination, advance pc). -/

/-- Recognise a structured `MULXHI` instruction `Lopn [.reg dst] (…"MULXHI"…)
    [.reg a, .reg b]` and return `(dst, a, b)`; `none` otherwise. -/
def mulhiStruct? : LinstrR → Option (String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b] =>
      if stripWidthTag opn = "MULXHI" then some (dst, a, b) else none
  | _ => none

/-- Recognise a structured `ADCX` (carry data) instruction `Lopn [.reg dst]
    (…"ADCX"…) [.reg a, .reg b, .reg c]` and return `(dst, a, b, c)`. -/
def adcxStruct? : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b, .reg c] =>
      if stripWidthTag opn = "ADCX" then some (dst, a, b, c) else none
  | _ => none

/-- Recognise a structured `ADCXHI` (carry-out) instruction. -/
def adcxhiStruct? : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b, .reg c] =>
      if stripWidthTag opn = "ADCXHI" then some (dst, a, b, c) else none
  | _ => none

/-- Recognise a structured `SBB` (borrow data) instruction `Lopn [.reg dst]
    (…"SBB"…) [.reg a, .reg b, .reg c]` and return `(dst, a, b, c)` — the dual of
    `adcxStruct?`. Reads minuend `a`, subtrahend `b`, borrow-in `c` (width 1). -/
def sbbStruct? : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b, .reg c] =>
      if stripWidthTag opn = "SBB" then some (dst, a, b, c) else none
  | _ => none

/-- Recognise a structured `SBBHI` (borrow-out) instruction — the dual of
    `adcxhiStruct?`. -/
def sbbhiStruct? : LinstrR → Option (String × String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b, .reg c] =>
      if stripWidthTag opn = "SBBHI" then some (dst, a, b, c) else none
  | _ => none

/-- The mul/carry-aware single-step semantics:

    * a structured `MULXHI` reads `a, b` at the data width `wₐ` (from `a`'s store
      tag), writes `mulHiW a b` at `wₐ`;
    * a structured `ADCX` reads `a, b` at `wₐ` and `cin` at width 1, writes
      `addCarryWord a b cin` at `wₐ`;
    * a structured `ADCXHI` reads the same, writes `carryOutBit a b cin` at width
      **1** (the width-mixing carry-out);
    * everything else delegates to `JasminLsemWidthN`'s `lsemStepN`.

    The recognizers are checked in the order `MULXHI`, `ADCX`, `ADCXHI`; they are
    pairwise disjoint (distinct stripped mnemonics) and disjoint from every
    `lsemStepN` arm. Faithful to `eval_instr`'s `Lopn`. -/
def lsemStepMC (i : LinstrR) (s : LstateN) : Option LstateN :=
  match mulhiStruct? i with
  | some (dst, a, b) =>
      match readReg s (.reg a) with
      | some ⟨wₐ, va⟩ =>
          match s.getW b wₐ with
          | some vb => some ((s.setReg dst (mulHiW va vb)).nextPc)
          | none => none
      | none => none
  | none =>
  match adcxStruct? i with
  | some (dst, a, b, c) =>
      match readReg s (.reg a) with
      | some ⟨wₐ, va⟩ =>
          match s.getW b wₐ, s.getW c 1 with
          | some vb, some vc => some ((s.setReg dst (addCarryWord va vb vc)).nextPc)
          | _, _ => none
      | none => none
  | none =>
  match adcxhiStruct? i with
  | some (dst, a, b, c) =>
      match readReg s (.reg a) with
      | some ⟨wₐ, va⟩ =>
          match s.getW b wₐ, s.getW c 1 with
          | some vb, some vc => some ((s.setReg dst (carryOutBit va vb vc)).nextPc)
          | _, _ => none
      | none => none
  | none =>
  match sbbStruct? i with
  | some (dst, a, b, c) =>
      match readReg s (.reg a) with
      | some ⟨wₐ, va⟩ =>
          match s.getW b wₐ, s.getW c 1 with
          | some vb, some vc => some ((s.setReg dst (subBorrowWord va vb vc)).nextPc)
          | _, _ => none
      | none => none
  | none =>
  match sbbhiStruct? i with
  | some (dst, a, b, c) =>
      match readReg s (.reg a) with
      | some ⟨wₐ, va⟩ =>
          match s.getW b wₐ, s.getW c 1 with
          | some vb, some vc => some ((s.setReg dst (borrowOutBit va vb vc)).nextPc)
          | _, _ => none
      | none => none
  | none => lsemStepSh i s

/-- On any instruction recognised by none of the three structured recognizers,
    `lsemStepMC` is exactly `JasminLsemShift`'s `lsemStepSh`. (So the
    `regArith`/`select`/shift steps transfer unchanged.) -/
theorem lsemStepMC_of_delegate (i : LinstrR) (s : LstateN)
    (hm : mulhiStruct? i = none) (ha : adcxStruct? i = none) (hh : adcxhiStruct? i = none)
    (hs : sbbStruct? i = none) (hsh : sbbhiStruct? i = none) :
    lsemStepMC i s = lsemStepSh i s := by
  simp only [lsemStepMC, hm, ha, hh, hs, hsh]

/-- **The comparison step.** The `SET<cc>` wire `Lopn [.reg dst] (withWidthTag wOp (cmpName c))
    [.reg a, b]` is recognised by none of the multiply, carry and `SAR` heads, so
    `lsemStepMC` writes the comparison bit `cmpBit c va vb : BitVec 1` to `dst`, as
    `lsemStepN_cmp`. -/
theorem lsemStepMC_cmp (c : JasminCmp) (wOp : Nat) (dst a : String) (b : LOperand)
    (s : LstateN) {w : Nat} {va vb : BitVec w} (ha : s.getW a w = some va)
    (hb : evalOperandN s w b = some vb) :
    lsemStepMC (.Lopn [.reg dst] (withWidthTag wOp (cmpName c)) [.reg a, b]) s
      = some ((s.setReg dst (cmpBit c va vb)).nextPc) := by
  have hs := JasminLsem.stripWidthTag_withWidthTag_cmpName wOp c
  rw [lsemStepMC_of_delegate _ _
      (by cases b <;> simp only [mulhiStruct?, hs]; cases c <;> rfl)
      (by cases b <;> rfl) (by cases b <;> rfl) (by cases b <;> rfl) (by cases b <;> rfl),
    lsemStepSh_of_not_sar _ _ (by cases b <;> simp only [sarStruct?, hs]; cases c <;> rfl)]
  exact lsemStepN_cmp c wOp dst a b s ha hb

/-! ### `lsemStraightMC` / leakage / composition over the mul/carry-aware step -/

/-- Mul/carry-aware straight-line execution: the sequential fold of `lsemStepMC`. -/
def lsemStraightMC : List LinstrR → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepMC i s with
      | some s' => lsemStraightMC is s'
      | none => none

@[simp] theorem lsemStraightMC_nil (s : LstateN) : lsemStraightMC [] s = some s := rfl

@[simp] theorem lsemStraightMC_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemStraightMC (i :: is) s =
      (match lsemStepMC i s with
        | some s' => lsemStraightMC is s'
        | none => none) := rfl

/-- Mul/carry-aware leakage trace: `linstrLeak` (`JasminLsemRobust`) is reused verbatim —
    it reads only the `LinstrR` syntax (the source register *names*, never a
    register value: the carry-in's *name* leaks, never its 1-bit secret). -/
def lsemLeakMC : List LinstrR → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepMC i s with
          | some s' => lsemLeakMC is s'
          | none => [])

@[simp] theorem lsemLeakMC_nil (s : LstateN) : lsemLeakMC [] s = [] := rfl

@[simp] theorem lsemLeakMC_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemLeakMC (i :: is) s =
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepMC i s with
          | some s' => lsemLeakMC is s'
          | none => []) := rfl

/-! ## 4. Recognizer disjointness lemmas

The structured recognizers are pairwise disjoint and the trio is disjoint from
every other emitted instruction (`regArith`/`select`/shifts/`regConst`). These
make `lsemStepMC` reduce to the right arm on each binding head. -/

/-- `mulhiStruct?` recognises the structured `MULXHI` (two `.reg` sources). -/
theorem mulhiStruct?_mulhi {w : Nat} (dst a b : String) :
    mulhiStruct? (.Lopn [.reg dst] (withWidthTag w "MULXHI") [.reg a, .reg b])
      = some (dst, a, b) := by
  simp only [mulhiStruct?, stripWidthTag_withWidthTag_MULXHI, if_pos]

/-- `mulhiStruct?` of an `Lopn` whose stripped mnemonic is not `"MULXHI"` is
    `none` (regardless of operand shape). -/
theorem mulhiStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "MULXHI") :
    mulhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp only [mulhiStruct?, if_neg h]
  · cases a <;> cases b <;> rfl

/-- `adcxStruct?` recognises the structured `ADCX` (three `.reg` sources). -/
theorem adcxStruct?_adcx {w : Nat} (dst a b c : String) :
    adcxStruct? (.Lopn [.reg dst] (withWidthTag w "ADCX") [.reg a, .reg b, .reg c])
      = some (dst, a, b, c) := by
  simp only [adcxStruct?, stripWidthTag_withWidthTag_ADCX, if_pos]

/-- `adcxStruct?` of an `Lopn` whose stripped mnemonic is not `"ADCX"` is `none`. -/
theorem adcxStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "ADCX") :
    adcxStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> cases c <;> simp only [adcxStruct?, if_neg h]
  · cases a <;> cases b <;> cases c <;> rfl

/-- `adcxhiStruct?` recognises the structured `ADCXHI`. -/
theorem adcxhiStruct?_adcxhi {w : Nat} (dst a b c : String) :
    adcxhiStruct? (.Lopn [.reg dst] (withWidthTag w "ADCXHI") [.reg a, .reg b, .reg c])
      = some (dst, a, b, c) := by
  simp only [adcxhiStruct?, stripWidthTag_withWidthTag_ADCXHI, if_pos]

/-- `adcxhiStruct?` of an `Lopn` whose stripped mnemonic is not `"ADCXHI"` is
    `none`. -/
theorem adcxhiStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "ADCXHI") :
    adcxhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> cases c <;> simp only [adcxhiStruct?, if_neg h]
  · cases a <;> cases b <;> cases c <;> rfl

/-- The two distinct stripped mnemonics `"MULXHI"` and `"ADCX"` etc. give the
    cross-disjointness facts the step arms need. -/
theorem mulhiStruct?_adcx {w : Nat} (dst a b c : String) :
    mulhiStruct? (.Lopn [.reg dst] (withWidthTag w "ADCX") [.reg a, .reg b, .reg c]) = none :=
  mulhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_ADCX]; decide)

theorem mulhiStruct?_adcxhi {w : Nat} (dst a b c : String) :
    mulhiStruct? (.Lopn [.reg dst] (withWidthTag w "ADCXHI") [.reg a, .reg b, .reg c]) = none :=
  mulhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_ADCXHI]; decide)

theorem adcxStruct?_mulhi {w : Nat} (dst a b : String) :
    adcxStruct? (.Lopn [.reg dst] (withWidthTag w "MULXHI") [.reg a, .reg b]) = none :=
  adcxStruct?_of_ne (by rw [stripWidthTag_withWidthTag_MULXHI]; decide)

theorem adcxStruct?_adcxhi {w : Nat} (dst a b c : String) :
    adcxStruct? (.Lopn [.reg dst] (withWidthTag w "ADCXHI") [.reg a, .reg b, .reg c]) = none :=
  adcxStruct?_of_ne (by rw [stripWidthTag_withWidthTag_ADCXHI]; decide)

theorem adcxhiStruct?_adcx {w : Nat} (dst a b c : String) :
    adcxhiStruct? (.Lopn [.reg dst] (withWidthTag w "ADCX") [.reg a, .reg b, .reg c]) = none :=
  adcxhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_ADCX]; decide)

/-! ### `SBB` / `SBBHI` recognizer + cross-disjointness (dual of the `ADCX` block) -/

/-- `sbbStruct?` recognises the structured `SBB` (three `.reg` sources). -/
theorem sbbStruct?_sbb {w : Nat} (dst a b c : String) :
    sbbStruct? (.Lopn [.reg dst] (withWidthTag w "SBB") [.reg a, .reg b, .reg c])
      = some (dst, a, b, c) := by
  simp only [sbbStruct?, stripWidthTag_withWidthTag_SBB, if_pos]

/-- `sbbStruct?` of an `Lopn` whose stripped mnemonic is not `"SBB"` is `none`. -/
theorem sbbStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "SBB") :
    sbbStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> cases c <;> simp only [sbbStruct?, if_neg h]
  · cases a <;> cases b <;> cases c <;> rfl

/-- `sbbhiStruct?` recognises the structured `SBBHI`. -/
theorem sbbhiStruct?_sbbhi {w : Nat} (dst a b c : String) :
    sbbhiStruct? (.Lopn [.reg dst] (withWidthTag w "SBBHI") [.reg a, .reg b, .reg c])
      = some (dst, a, b, c) := by
  simp only [sbbhiStruct?, stripWidthTag_withWidthTag_SBBHI, if_pos]

/-- `sbbhiStruct?` of an `Lopn` whose stripped mnemonic is not `"SBBHI"` is `none`. -/
theorem sbbhiStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "SBBHI") :
    sbbhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> cases c <;> simp only [sbbhiStruct?, if_neg h]
  · cases a <;> cases b <;> cases c <;> rfl

/-- The prior recognizers are `none` on an `SBB` instruction (distinct mnemonics),
    so `lsemStepMC` reaches the `SBB` arm. -/
theorem mulhiStruct?_sbb {w : Nat} (dst a b c : String) :
    mulhiStruct? (.Lopn [.reg dst] (withWidthTag w "SBB") [.reg a, .reg b, .reg c]) = none :=
  mulhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBB]; decide)

theorem adcxStruct?_sbb {w : Nat} (dst a b c : String) :
    adcxStruct? (.Lopn [.reg dst] (withWidthTag w "SBB") [.reg a, .reg b, .reg c]) = none :=
  adcxStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBB]; decide)

theorem adcxhiStruct?_sbb {w : Nat} (dst a b c : String) :
    adcxhiStruct? (.Lopn [.reg dst] (withWidthTag w "SBB") [.reg a, .reg b, .reg c]) = none :=
  adcxhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBB]; decide)

/-- The prior recognizers (including `sbbStruct?`) are `none` on an `SBBHI`
    instruction, so `lsemStepMC` reaches the `SBBHI` arm. -/
theorem mulhiStruct?_sbbhi {w : Nat} (dst a b c : String) :
    mulhiStruct? (.Lopn [.reg dst] (withWidthTag w "SBBHI") [.reg a, .reg b, .reg c]) = none :=
  mulhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBBHI]; decide)

theorem adcxStruct?_sbbhi {w : Nat} (dst a b c : String) :
    adcxStruct? (.Lopn [.reg dst] (withWidthTag w "SBBHI") [.reg a, .reg b, .reg c]) = none :=
  adcxStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBBHI]; decide)

theorem adcxhiStruct?_sbbhi {w : Nat} (dst a b c : String) :
    adcxhiStruct? (.Lopn [.reg dst] (withWidthTag w "SBBHI") [.reg a, .reg b, .reg c]) = none :=
  adcxhiStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBBHI]; decide)

theorem sbbStruct?_sbbhi {w : Nat} (dst a b c : String) :
    sbbStruct? (.Lopn [.reg dst] (withWidthTag w "SBBHI") [.reg a, .reg b, .reg c]) = none :=
  sbbStruct?_of_ne (by rw [stripWidthTag_withWidthTag_SBBHI]; decide)

/-! ### The trio is disjoint from the width-mixed and shift instruction images

`regArith` emits a `binOpName` mnemonic, `select` emits `CMOV`, the shifts emit
`SHR`/`SHL`/`SAR` — none is `MULXHI`/`ADCX`/`ADCXHI`, so all three recognizers are
`none` on those images and `lsemStepMC` delegates to `lsemStepN`. -/

theorem binOpName_ne_MULXHI (bop : JasminBinOp) : binOpName bop ≠ "MULXHI" := by
  cases bop <;> decide

theorem binOpName_ne_ADCX (bop : JasminBinOp) : binOpName bop ≠ "ADCX" := by
  cases bop <;> decide

theorem binOpName_ne_ADCXHI (bop : JasminBinOp) : binOpName bop ≠ "ADCXHI" := by
  cases bop <;> decide

theorem binOpName_ne_SBB (bop : JasminBinOp) : binOpName bop ≠ "SBB" := by
  cases bop <;> decide

theorem binOpName_ne_SBBHI (bop : JasminBinOp) : binOpName bop ≠ "SBBHI" := by
  cases bop <;> decide

/-- All three recognizers are `none` on the `regArith` `opToLinstrR` image. -/
theorem struct?_regArith {w : Nat} (bop : JasminBinOp) (dst : String)
    (srcs : List LOperand) :
    mulhiStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none ∧
    adcxStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none ∧
    adcxhiStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none ∧
    sbbStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none ∧
    sbbhiStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none := by
  rw [opToLinstrR]
  refine ⟨mulhiStruct?_of_ne ?_, adcxStruct?_of_ne ?_, adcxhiStruct?_of_ne ?_,
      sbbStruct?_of_ne ?_, sbbhiStruct?_of_ne ?_⟩ <;>
    · rw [stripWidthTag_withWidthTag_binOpName]
      first
      | exact binOpName_ne_MULXHI bop
      | exact binOpName_ne_ADCX bop
      | exact binOpName_ne_ADCXHI bop
      | exact binOpName_ne_SBB bop
      | exact binOpName_ne_SBBHI bop

/-- All three recognizers are `none` on the `select` `opToLinstrR` image. -/
theorem struct?_select {w : Nat} (dst : String) (srcs : List LOperand) :
    mulhiStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none ∧
    adcxStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none ∧
    adcxhiStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none ∧
    sbbStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none ∧
    sbbhiStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none := by
  rw [opToLinstrR]
  refine ⟨mulhiStruct?_of_ne ?_, adcxStruct?_of_ne ?_, adcxhiStruct?_of_ne ?_,
      sbbStruct?_of_ne ?_, sbbhiStruct?_of_ne ?_⟩ <;>
    · rw [stripWidthTag_withWidthTag_CMOV]; decide

/-- All three recognizers are `none` on a structured shift instruction
    (`shiftLinstr`): it has only two sources `[src, .imm n]`, so the three-source
    `ADCX`/`ADCXHI` recognizers are `none` by shape, and the two-source
    `mulhiStruct?` is `none` because the second source is `.imm`, not `.reg`. -/
theorem struct?_shiftLinstr {w : Nat} (mnem : String) (dst : String)
    (src : LOperand) (n : Nat) :
    mulhiStruct? (shiftLinstr mnem w dst src n) = none ∧
    adcxStruct? (shiftLinstr mnem w dst src n) = none ∧
    adcxhiStruct? (shiftLinstr mnem w dst src n) = none ∧
    sbbStruct? (shiftLinstr mnem w dst src n) = none ∧
    sbbhiStruct? (shiftLinstr mnem w dst src n) = none := by
  simp only [shiftLinstr, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?]
  cases src <;> exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- All three recognizers are `none` on the `regConst` `opToLinstrR` image (the
    immediate-`MOV` form): the trio mnemonics are `MULXHI`/`ADCX`/`ADCXHI`, never
    `MOV`. -/
theorem struct?_regConst {w n : Nat} (dst : String) (srcs : List LOperand) :
    mulhiStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none ∧
    adcxStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none ∧
    adcxhiStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none ∧
    sbbStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none ∧
    sbbhiStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none := by
  rw [opToLinstrR]
  refine ⟨mulhiStruct?_of_ne ?_, adcxStruct?_of_ne ?_, adcxhiStruct?_of_ne ?_,
      sbbStruct?_of_ne ?_, sbbhiStruct?_of_ne ?_⟩ <;>
    (rw [CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV];
     decide)

/-! ## 5. Per-binding agreement for the trio

Each binding `lsemStepMC`s, from a store agreeing with `V`, to the state that
writes the binding's `Com`-denotation to `regName curDepth` and advances the pc.
The denotation equality is the (definitional) `Related` square. The data width is
recovered from the first source's store tag (`readReg_resolveVar`); `cin` is read
at width 1 (the `StoreAgreesN` agreement reads it at its own width — which is 1,
since `cin : Var Γ (.reg 1)`). -/

/-- The `exprArgs` of a `mulhi` binding is the two resolved data sources. -/
theorem exprArgs_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (a b : Ctxt.Var Γ (.reg w)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.mulhi w, heq, .cons a (.cons b .nil)⟩ : Expr jasminDialect Γ (.reg w))
      = [resolveVar curDepth nArgs argName (fun _ => none) a,
         resolveVar curDepth nArgs argName (fun _ => none) b] := rfl

/-- **`mulhi` per-binding step.** From a store agreeing with `V`, the structured
    `MULXHI` instruction `lsemStepMC`s to the state writing the binding's
    denotation `(mulhi w).denote V = mulHiW (a.lookup V) (b.lookup V)` to
    `regName curDepth`, reading both data sources at the recovered width `w`.
    Faithful to `eval_instr`'s `Lopn`; the denotation equality is the (`rfl`)
    `Related` square `relatedMulHi`. -/
theorem lsemStepMC_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons a (.cons b .nil) =>
    -- the read of `a` recovers width `w`; the read of `b` at `w` succeeds by agreement
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    have hb : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) b)) w
        = some (b.lookup V) := by
      have := hagree b; rwa [evalOperandN_resolveVar] at this
    rw [opToLinstrR, exprArgs_mulhi heq a b, resolveVar_isReg a, resolveVar_isReg b]
    simp only [lsemStepMC, mulhiStruct?_mulhi, ha, hb]
    rfl

/-- The `exprArgs` of an `addCarryLo` binding is its three resolved sources. -/
theorem exprArgs_addCarryLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (a b : Ctxt.Var Γ (.reg w)) (c : Ctxt.Var Γ (.reg 1)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.addCarryLo w, heq, .cons a (.cons b (.cons c .nil))⟩ :
        Expr jasminDialect Γ (.reg w))
      = [resolveVar curDepth nArgs argName (fun _ => none) a,
         resolveVar curDepth nArgs argName (fun _ => none) b,
         resolveVar curDepth nArgs argName (fun _ => none) c] := rfl

/-- The `exprArgs` of an `addCarryHi` binding is its three resolved sources. -/
theorem exprArgs_addCarryHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (a b : Ctxt.Var Γ (.reg w)) (c : Ctxt.Var Γ (.reg 1)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.addCarryHi w, heq, .cons a (.cons b (.cons c .nil))⟩ :
        Expr jasminDialect Γ (.reg 1))
      = [resolveVar curDepth nArgs argName (fun _ => none) a,
         resolveVar curDepth nArgs argName (fun _ => none) b,
         resolveVar curDepth nArgs argName (fun _ => none) c] := rfl

/-- **`addCarryLo` per-binding step.** From a store agreeing with `V`, the
    structured `ADCX` instruction `lsemStepMC`s to the state writing the binding's
    denotation `(addCarryLo w).denote V = addCarryWord (a.lookup V) (b.lookup V)
    (c.lookup V)` to `regName curDepth`. The data words `a, b` are read at the
    recovered width `w`; the carry-in `c` is read at width 1 (the `.reg 1`
    agreement reads it at its own width). Faithful to `eval_instr`'s `Lopn`; the
    denotation equality is the (`rfl`) `Related` square `relatedAddCarryWord`. -/
theorem lsemStepMC_addCarryLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons a (.cons b (.cons c .nil)) =>
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    have hb : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) b)) w
        = some (b.lookup V) := by
      have := hagree b; rwa [evalOperandN_resolveVar] at this
    have hc : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) c)) 1
        = some (c.lookup V) := by
      have := hagree c; rwa [evalOperandN_resolveVar] at this
    rw [opToLinstrR, exprArgs_addCarryLo heq a b c, resolveVar_isReg a, resolveVar_isReg b,
      resolveVar_isReg c]
    simp only [lsemStepMC, mulhiStruct?_adcx, adcxStruct?_adcx, ha, hb, hc]
    rfl

/-- **`addCarryHi` per-binding step (width-mixing carry-out).** From a store
    agreeing with `V`, the structured `ADCXHI` instruction `lsemStepMC`s to the
    state writing the binding's denotation `(addCarryHi w).denote V = carryOutBit
    (a.lookup V) (b.lookup V) (c.lookup V)` — a **`BitVec 1`** — to `regName
    curDepth`. The data words `a, b` are read at width `w`, the carry-in `c` at
    width 1; the result is the width-mixing 1-bit carry-out. Faithful to
    `eval_instr`'s `Lopn`; the denotation equality is the (`rfl`) `Related` square
    `relatedCarryOut`. -/
theorem lsemStepMC_addCarryHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) := by
  match args with
  | .cons a (.cons b (.cons c .nil)) =>
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    have hb : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) b)) w
        = some (b.lookup V) := by
      have := hagree b; rwa [evalOperandN_resolveVar] at this
    have hc : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) c)) 1
        = some (c.lookup V) := by
      have := hagree c; rwa [evalOperandN_resolveVar] at this
    rw [opToLinstrR, exprArgs_addCarryHi heq a b c, resolveVar_isReg a, resolveVar_isReg b,
      resolveVar_isReg c]
    simp only [lsemStepMC, mulhiStruct?_adcxhi, adcxStruct?_adcxhi, adcxhiStruct?_adcxhi,
      ha, hb, hc]
    rfl

/-! ## 6. The `regArith`/`select`/shift bindings step via `lsemStepMC = lsemStepSh`

`opToLinstrR (regArith …)` / `opToLinstrR (select …)` and the structured shifts
are recognised by none of the three trio recognizers, so `lsemStepMC` delegates
them to `JasminLsemShift`'s `lsemStepSh` and its per-binding steps
transfer. -/

/-- The `regArith` binding steps via `lsemStepMC` to its denotation (`JasminLsemShift`'s
    `lsemStepSh_var`, transferred through `lsemStepMC = lsemStepSh`). -/
theorem lsemStepMC_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_regArith bop (regName curDepth) _
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_var bop heq args hagree

/-- The `select` binding steps via `lsemStepMC` to its denotation. -/
theorem lsemStepMC_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_select (regName curDepth) _
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_sel heq args hagree

/-- The `regConst` binding steps via `lsemStepMC` to its denotation (`JasminLsemShift`'s
    `lsemStepSh_const`, transferred through `lsemStepMC = lsemStepSh`). The `hwn`
    hypothesis pins the constant's width on the two wire-distinguished widths
    `{64, 32}` — the only width information the nullary const carries on the wire. -/
theorem lsemStepMC_const {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (_hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_regConst (regName curDepth) _
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_const (V := V) n hwn heq args

/-- The structured shift bindings step via `lsemStepMC` to their denotations. -/
theorem lsemStepMC_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_shiftLinstr "SHR" (regName curDepth) _ n
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_shr hn heq args hagree

theorem lsemStepMC_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_shiftLinstr "SHL" (regName curDepth) _ n
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_shl hn heq args hagree

theorem lsemStepMC_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepMC
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  obtain ⟨hm, ha, hh, hs, hsh⟩ := struct?_shiftLinstr "SAR" (regName curDepth) _ n
  rw [lsemStepMC_of_delegate _ _ hm ha hh hs hsh]
  exact lsemStepSh_sar hn heq args hagree

/-! ## 7. The mul/carry emission `straightOpsMC` and source predicate `ScalarMulCarryN`

`straightOpsMC` extends `JasminLsemShift`'s `straightOpsShift` with the three trio
bindings, each emitting the structured `opToLinstrR` instruction (the trio carries
no string-baked count, so — unlike the shifts — it routes through the *default*
`opToLinstrR` arm; `straightOpsMC` makes the dispatch explicit for the unfold
lemmas). `regArith`/`select`/shift bindings reuse `straightOpsShift`'s emission
verbatim. -/

/-- The straight-line `LinstrR` chain a `Com` emits in the mul/carry fragment:
    like `JasminLsemShift`'s `straightOpsShift`, but the `mulhi`/`addCarryLo`/
    `addCarryHi` bindings emit their structured `opToLinstrR` instruction (the
    `MULXHI`/`ADCX`/`ADCXHI` role form). All other bindings reuse the shift
    fragment's emission. -/
def straightOpsMC (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrR
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let instr : LinstrR :=
        match e.op, src with
        | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
        | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
        | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
        | _, _ => opToLinstrR e.op (regName curDepth) src
      instr :: straightOpsMC nArgs body (curDepth + 1)

/-- The straight-line **mul/carry-fragment** scalar source: every binding is a
    `regArith`, a width-mixing `select`, an in-range immediate shift, or one of
    the widening-multiply / carry-chain trio `mulhi`/`addCarryLo`/`addCarryHi`.
    This subsumes `JasminLsemShift`'s `ScalarShiftN`. Note the `addCarryHi` arm binds a
    **`.reg 1`** into the body context (width-mixing carry-out). -/
inductive ScalarMulCarryN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarMulCarryN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarMulCarryN body) :
      ScalarMulCarryN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)

/-- `ScalarMulCarryN` subsumes `ScalarShiftN`: every shift-fragment
    program is in the mul/carry fragment. So the `JasminLsemShift` results are special
    cases. -/
theorem ScalarMulCarryN.of_scalarShiftN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarShiftN com) : ScalarMulCarryN com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih
  | sel heq args _ ih => exact .sel heq args ih
  | shr hn heq args _ ih => exact .shr hn heq args ih
  | shl hn heq args _ ih => exact .shl hn heq args ih
  | sar hn heq args _ ih => exact .sar hn heq args ih

/-- A `ScalarMulCarryN` program returns a register. -/
theorem ScalarMulCarryN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) : ∃ w, t = .reg w := by
  induction hcom with
  | ret v => exact ⟨_, rfl⟩
  | var _ _ _ _ ih => exact ih
  | const _ _ _ _ _ ih => exact ih
  | sel _ _ _ ih => exact ih
  | shr _ _ _ _ ih => exact ih
  | shl _ _ _ _ ih => exact ih
  | sar _ _ _ _ ih => exact ih
  | mulhi _ _ _ ih => exact ih
  | addLo _ _ _ ih => exact ih
  | addHi _ _ _ ih => exact ih

/-! ## 8. `straightOpsMC` unfolding on each binding head -/

theorem straightOpsMC_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMC_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMC_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsMC_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsMC_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsMC_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsMC_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsMC_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-- `straightOpsMC` on a `regConst` binding: routes through the *default*
    `opToLinstrR` arm (the immediate-`MOV` image), as the trio bindings do. -/
theorem straightOpsMC_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsMC nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsMC nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

/-! ## 9. The core mul/carry straight-line simulation

Same induction skeleton as `JasminLsemShift`'s `lsemStraightShift_straightOps`, with the
three new trio arms closed by `lsemStepMC_mulhi`/`addCarryLo`/`addCarryHi` +
`StoreAgreesN.step`, and the `regArith`/`select`/shift arms by the delegating
`lsemStepMC_*`. The `addCarryHi` arm steps a `.reg 1` binding, so the
binding-extended valuation is over `.reg 1 :: Γ` — `StoreAgreesN.step` is generic
over the written width, so it absorbs the width-mixing carry-out without change. -/

/-- **Core simulation (parametrized by an agreeing start state), mul/carry
    fragment.** From any width-tagged store `st` agreeing with `V` at depth
    `curDepth`, running the mul/carry-fragment `.var`-chain `straightOpsMC`
    succeeds, lands in a store agreeing with the binding-extended valuation, and
    reads `Com.denote com V` (transported to its return width) at the return
    register. -/
theorem lsemStraightMC_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightMC (straightOpsMC nArgs com curDepth) st = some st' ∧
        evalOperandN st' w (.reg (comRetReg nArgs argName com curDepth)) =
          some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V w hw hlen harg hagree
      cases hw
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]
      exact hagree v
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_var, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_const (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        n hwn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_const, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_sel, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_shr (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_shr, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_shl (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_shl, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_sar (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_sar, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_mulhi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_mulhi, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_addCarryLo (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_addLo, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepMC_addCarryHi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsMC_addHi, lsemStraightMC_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 10. Faithfulness, leak state-independence, and the capstone

`encodeN`/`decodeN`/`encodeN_StoreAgreesN` are reused verbatim from `JasminLsemWidthN`
(the start-state encoding is op-agnostic). -/

/-- **Straight-line linearizer simulation, mul/carry fragment.** Running the
    mul/carry-fragment `.var`-chain `straightOpsMC` from the encoded argument
    valuation and decoding the result register at width `w` equals the source
    program's `Com.denote`. -/
theorem comToLprog_lsemMC {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightMC (straightOpsMC Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightMC_straightOps hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), mul/carry fragment.** -/
theorem comToLprog_faithful_mulcarry {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightMC (straightOpsMC Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemMC hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, mul/carry fragment (unconditional).** The leakage
    trace of the mul/carry-fragment `.var`-chain is the **same from any two initial
    states agreeing with the same valuation**: every head (`regArith`, `select`, a
    shift, or one of the trio) has a `linstrLeak` reading only syntax — for the
    trio, the source register *names* (including the carry-in's *name*), never a
    register value — and `lsemStepMC`s successfully, so both states take the `some`
    branch and the tails (still agreeing with the extended valuation) close by the
    IH. -/
theorem lsemLeakMC_straightOps_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakMC (straightOpsMC nArgs com curDepth) s₁ =
        lsemLeakMC (straightOpsMC nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_var (V := V₁) bop heq args hag1
      have hstep2 := lsemStepMC_var (V := V₂) bop heq args hag2
      rw [straightOpsMC_var]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_const (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepMC_const (V := V₂) n hwn heq args hag2
      rw [straightOpsMC_const]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_sel (V := V₁) heq args hag1
      have hstep2 := lsemStepMC_sel (V := V₂) heq args hag2
      rw [straightOpsMC_sel]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_shr (V := V₁) hn heq args hag1
      have hstep2 := lsemStepMC_shr (V := V₂) hn heq args hag2
      rw [straightOpsMC_shr]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_shl (V := V₁) hn heq args hag1
      have hstep2 := lsemStepMC_shl (V := V₂) hn heq args hag2
      rw [straightOpsMC_shl]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_sar (V := V₁) hn heq args hag1
      have hstep2 := lsemStepMC_sar (V := V₂) hn heq args hag2
      rw [straightOpsMC_sar]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_mulhi (V := V₁) heq args hag1
      have hstep2 := lsemStepMC_mulhi (V := V₂) heq args hag2
      rw [straightOpsMC_mulhi]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_addCarryLo (V := V₁) heq args hag1
      have hstep2 := lsemStepMC_addCarryLo (V := V₂) heq args hag2
      rw [straightOpsMC_addLo]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepMC_addCarryHi (V := V₁) heq args hag1
      have hstep2 := lsemStepMC_addCarryHi (V := V₂) heq args hag2
      rw [straightOpsMC_addHi]
      simp only [lsemLeakMC_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 11. The unconditional mul/carry capstone: `correct ∧ robust` -/

/-- **Unconditional `correct ∧ robust` for the widening-multiply / carry-chain
    fragment (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
    addCarryHi`).** For a mul/carry-fragment scalar straight-line `Com` with return
    type `.reg w`:

    1. *(correct, §10)* running the linearizer-emitted `.var`-chain `straightOpsMC`
       on the encoded argument valuation and decoding the result register at width
       `w` yields exactly `com.denote V`; and
    2. *(robust, syntactic leak model, §10)* the leakage trace `lsemLeakMC
       (straightOpsMC …)` is the **same from the encodings of any two input
       valuations** — the attacker's view (including, for the carry chain, the
       carry register *name* threaded between limbs) is a function of the emitted
       instruction list alone, never of a register value.

    This is **unconditional**: no IR→x86 faithfulness hypothesis, no
    `jasminc_preserves_ct`. Both conjuncts concern one and the same object — the
    mul/carry linearizer-emitted straight-line body run by `lsemStraightMC`
    (functional) and observed by `lsemLeakMC` (CT). The widening multiply and carry
    adds are read **structurally** from the role mnemonics `MULXHI`/`ADCX`/`ADCXHI`
    and their `.reg` operands the byte renderer consumes (no wire change),
    so the emitted **bytes are unchanged**. The first capstone covering the
    widening-multiply / carry-chain trio — `addCarryHi` being the second
    **width-mixing** op (after `select`): `BitVec w` data words and a `BitVec 1`
    carry-out in one instruction. The `lsem→bytes` encoder and Sail tables remain
    the declared trusted base.

    The leak function reads no register value (an indexed access leaks the index
    register's name, not its value), so conjunct 2 holds for every program of the
    fragment and is not constant-time evidence. Constant-time evidence for emitted
    code is `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` (straight-line
    gathered blocks) and the per-kernel `blockLeak` theorems. -/
theorem owned_lsem_correct_and_robust_mulcarry {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§10)
    ((lsemStraightMC (straightOpsMC Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§10)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakMC (straightOpsMC Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakMC (straightOpsMC Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_mulcarry hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakMC_straightOps_state_independent hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 12. Tie-back: the shift fragment is subsumed

`ScalarMulCarryN.of_scalarShiftN` shows every `ScalarShiftN` program is a
`ScalarMulCarryN` program. The mul/carry capstone therefore specialises to the
shift fragment (and, transitively via `ScalarShiftN.of_scalarArithN`, to the
`JasminLsemWidthN` width-mixed and `JasminLsemSimulation` `regArith` fragments). -/

/-- Every shift-fragment program satisfies the mul/carry capstone:
    the `JasminLsemShift` results are special cases of the ones proved here. -/
theorem owned_lsem_correct_and_robust_mulcarry_of_scalarShiftN {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightMC (straightOpsMC Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakMC (straightOpsMC Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakMC (straightOpsMC Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_mulcarry (ScalarMulCarryN.of_scalarShiftN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
