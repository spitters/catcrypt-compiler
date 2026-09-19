/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardSatisfiable
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord

/-!
# A `runBlock` correspondence over the single-word field-add front, not a hand block

`FieldToJasminWord.lean` is a verified front: for a `SingleWordField p`, the
lowering `lowerBlockW` maps the abstract field op `fAdd p` to
`FieldWord.addBlk p a b`, a `Com jasminDialect Γ (.reg 64)` term, and
`fieldToJasminWord_denote` proves the lowering denotation-preserving. Every
concrete instruction-list block this repository states an ascent
correspondence about (`feAddBlock`, `feMulBlock`, `combSelectBlock`, …) is
instead a `List (JInstr 64)` authored directly, with no mechanised map from a
`Com jasminDialect` term to a `List (JInstr n)` — `JasminDialect.lean`'s own
docstring names that map "intentionally not attempted". `#408`'s `feAddBlock`
and `feMulBlock` (`X86Backend/Fe25519OpsKernel.lean`,
`X86Backend/Fe25519MulKernel.lean`) are 4-limb (256-bit) kernels; the only
front reaching a concrete jasmin-level block at all, `FieldToJasminWord`, is a
**single-word** (one 64-bit limb) representation, so it cannot express either
kernel's 4-limb schoolbook and carry chain, and no other listed front
(`fieldToJasminLimbs`, `cryptoDialectToJasminCom`, the rolled-loop family)
lands in `List (JInstr n)` either — they all stop at the same `Com
jasminDialect` level. See the accompanying report for the file:line evidence.

This module states the smaller correspondence the existing front DOES support:
`addJBlock`, a `List (JInstr 64)` computing the same branch-free
conditional-subtract addition `FieldWord.addBlk`/`FieldWord.csubBlk` compute
(`csubW P (a + b)`), one x86 two-address instruction per `regArith`/`regConst`
binding of `csubBlk`'s eight-binding term (`u := a+b`; `d := u−P`; `e := d≫63`;
`f := 0−e`; `g := P&f`; `r := d+g`). `addJBlock` is **not** the output of an
automated `Com jasminDialect → List (JInstr n)` compiler — none exists — it is
a direct, one-block-family instruction-level transcription of `csubBlk`'s
already-verified recipe, justified by `addJBlock_value` reproducing `csubW`
exactly and, through `FieldWord.addBlk_denote`, the `SingleWordField` addition
law. Building the missing general serializer (`UniformScalarArith 64 c → List
(JInstr 64)`, denotation-preserving) is the natural next step; this module is
the value-level bridge that step would produce automatically.

## Main definitions

* `addJBlock`: the six-step `List (JInstr 64)` computing `csubW P (a + b)`.
* `AAdd`, `SRAdd`, `addPStep`: the `CorresJ` state relation and abstract step.

## Main results

* `addJBlock_value`: `runBlock` of `addJBlock` at register `"r"` equals
  `csubW P (a + b)`, matching `FieldWord.addBlk_value` exactly.
* `addJBlock_corresJ`: the `CorresJ` statement over `SRAdd`.
* `addJBlock_corresJ_guardSat`: its guard is satisfiable.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.FieldWordAddCorres

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-! ## 1. The generated-recipe block -/

/-- The branch-free conditional-subtract addition `csubW P (a + b)`, one x86
    two-address instruction per `regArith`/`regConst` binding of
    `FieldWord.addBlk P a b = spliceCom (binBlk .add a b) (csubBlk P .here)`:
    `u := a + b`; `d := u − P`; `e := d ≫ 63`; `f := 0 − e`; `g := P & f`;
    `r := d + g`. The final value lives in register `"r"`. -/
def addJBlock (P : Nat) : List (JInstr 64) :=
  [ .mov "u" (.reg "a"), .add "u" (.reg "b")
  , .mov "d" (.reg "u"), .sub "d" (.imm P)
  , .mov "e" (.reg "d"), .shr "e" (.imm 63)
  , .mov "f" (.imm 0),   .sub "f" (.reg "e")
  , .mov "g" (.imm P),   .and_ "g" (.reg "f")
  , .mov "r" (.reg "d"), .add "r" (.reg "g") ]

/-- **Value correctness.** Running `addJBlock P` from a state whose `"a"`/`"b"`
    registers hold `a`/`b` leaves `"r"` holding `csubW P (a + b)` — the same
    word function `FieldWord.addBlk_value` proves of `FieldWord.addBlk P a b`. -/
theorem addJBlock_value (P : Nat) (s : JState 64) :
    (runBlock s (addJBlock P)).get "r" = csubW P (s.get "a" + s.get "b") := by
  simp only [addJBlock, runBlock_cons, runBlock_nil, evalInstr, JState.get,
    JState.setReg, JState.writeB5W, JOperand.eval, x86_MOV, x86_ADD, x86_SUB,
    x86_AND, csubW]
  rfl

/-! ## 2. The `CorresJ` statement -/

/-- The abstract state: the two addends and the result register, matching the
    three registers `SRAdd` tracks. -/
structure AAdd where
  /-- First addend. -/
  a : BitVec 64
  /-- Second addend. -/
  b : BitVec 64
  /-- Result register (arbitrary before running the block). -/
  r : BitVec 64

/-- The registers `"a"`, `"b"`, `"r"` agree with the abstract state. `addJBlock`
    touches no other register the block's caller could depend on. -/
def SRAdd (st : JState 64) (s : AAdd) : Prop :=
  st.regs "a" = s.a ∧ st.regs "b" = s.b ∧ st.regs "r" = s.r

/-- The abstract transition: the addends are unchanged, the result becomes
    `csubW P (a + b)`. -/
def addPStep (P : Nat) (s : AAdd) : AAdd :=
  { a := s.a, b := s.b, r := csubW P (s.a + s.b) }

/-- **The `CorresJ` correspondence.** `addJBlock P` refines `addPStep P` through
    `SRAdd`: the addends persist and the result register becomes `csubW P (a+b)`. -/
theorem addJBlock_corresJ (P : Nat) :
    CorresJ SRAdd (fun _ => True) (addPStep P) (addJBlock P) := by
  intro st s hSR _
  obtain ⟨ha, hb, _⟩ := hSR
  refine ⟨?_, ?_, ?_⟩
  · show (runBlock st (addJBlock P)).regs "a" = s.a
    rw [← ha]; rfl
  · show (runBlock st (addJBlock P)).regs "b" = s.b
    rw [← hb]; rfl
  · show (runBlock st (addJBlock P)).regs "r" = csubW P (s.a + s.b)
    have h := addJBlock_value P st
    simp only [JState.get] at h
    rw [h, ha, hb]

/-! ## 3. Satisfiability -/

/-- **`addJBlock_corresJ`'s guard is satisfiable.** The all-zero machine state
    matches the all-zero abstract state under `SRAdd`, and the guard is `True`. -/
theorem addJBlock_corresJ_guardSat (P : Nat) :
    ∃ st a, SRAdd st a ∧ (fun (_ : AAdd) => True) a :=
  corresJ_guardSat (addJBlock_corresJ P)
    ⟨{ regs := fun _ => 0 }, { a := 0, b := 0, r := 0 }, ⟨rfl, rfl, rfl⟩, trivial⟩

/-! ## 4. The field-addition law through `SingleWordField.ofCanonical` -/

/-- **The generated block realises `SingleWordField` addition.** For a prime
    `p` with `2 p ≤ 2 ^ 63` and encoded operands, `addJBlock`'s result register
    holds the encoding of the field sum — the same law
    `FieldWord.SingleWordField.ofCanonical`'s `addBlk_denote` proves of the
    front-lowered `Com jasminDialect` term. -/
theorem addJBlock_field_add {p : Nat} [NeZero p] (hp : 2 * p ≤ 2 ^ 63)
    (s : JState 64) (x y : ZMod p) (ha : s.get "a" = canonEnc p x)
    (hb : s.get "b" = canonEnc p y) :
    (runBlock s (addJBlock p)).get "r" = canonEnc p (x + y) := by
  rw [addJBlock_value, ha, hb]
  exact csubW_add_canonEnc hp x y

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.FieldWordAddCorres
