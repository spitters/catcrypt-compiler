/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ReadingTac

/-!
# Regression of `emit_reading`

The functions of hax-lean's `HaxLean/EmitterRegressions.lean` (namespace `MonadicOut`) that
`--emit-monadic` prints and that are in the fragment of `emit_reading`, written as the printer
writes them, with the `ImpExpr` literal each is printed from and the theorem `f_reading` as
`--emit-reading` prints it. The counted loop `sumLoop` is read by the loop square
`foldRangeM_go_of_loopBS` with its invariant written out.

## Main results

* `mulChecked_reading`, `K_reading`, `guardedIf_reading`, `rebind_reading`: the reading of a
  checked multiplication, a constant, a guarded `if` and a rebinding refines the printed
  function, by `emit_reading`.
* `sumLoop_reading`: the same for a counted loop, by the loop square.
-/

@[expose] public section

set_option autoImplicit false

namespace HaxAscent.RustSemantics.ReadingTacTest

open Hax
open HaxAscent.RustSemantics CatCrypt.Hax.RustSemantics
open Aeneas.Std (RustM bind_assoc_eq bind_tc_ok)

/-! ## Checked arithmetic -/

/-- `fn f(a: u64, b: u64) -> u64 { a * b }`. -/
def mulChecked (a : Int) (b : Int) :=
  do
    Hax.mulM_w 64 a b

/-- The literal of `mulChecked`. -/
def mulChecked_impExpr : ImpExpr :=
  .letBind "a" (.var "a") (.letBind "b" (.var "b") (.app "Mul#64" [.var "a", .var "b"]))

/-- The printed `mulChecked` reads as the `toRustMSB` reading of `mulChecked_impExpr`. -/
theorem mulChecked_reading (a : Int) (b : Int) (v_a : AVal) (v_b : AVal) (ρ : AEnv)
    (h_a : v_a.toValue = Hax.Ascent.HaxEnc.enc a)
    (h_b : v_b.toValue = Hax.Ascent.HaxEnc.enc b) :
    ReadsAs (mulChecked a b)
      (toRustMSB appRt mulChecked_impExpr ((ρ.upd "a" v_a).upd "b" v_b)) := by
  emit_reading [mulChecked, mulChecked_impExpr]

/-- A constant of the effect closure, a checked `usize` addition of literals. -/
def K :=
  do
    Hax.addM_w Hax.usizeBits (3 : Int) (16 : Int)

/-- The literal of `K`. -/
def K_impExpr : ImpExpr := .app "Add#size" [.lit (.int 3), .lit (.int 16)]

/-- The printed `K` reads as the `toRustMSB` reading of `K_impExpr`. -/
theorem K_reading (ρ : AEnv) :
    ReadsAs (K) (toRustMSB appRt K_impExpr ρ) := by
  emit_reading [K, K_impExpr]

/-! ## Indexing in a branch -/

/-- A partial operation in a branch. -/
def guardedIf (a : Array Int) (i : Int) :=
  do
    if Hax.lt i (Hax.array_len a) then
      Hax.indexM a i
    else
      pure (0 : Int)

/-- The literal of `guardedIf`. -/
def guardedIf_impExpr : ImpExpr :=
  .letBind "a" (.var "a") (.letBind "i" (.var "i")
    (.ifThenElse (.app "Lt" [.var "i", .app "len" [.var "a"]])
      (.app "index" [.var "a", .var "i"]) (.lit (.int 0))))

/-- The printed `guardedIf` reads as the `toRustMSB` reading of `guardedIf_impExpr`. -/
theorem guardedIf_reading (a : Array Int) (i : Int) (v_a : AVal) (v_i : AVal) (ρ : AEnv)
    (h_a : v_a.toValue = Hax.Ascent.HaxEnc.enc a)
    (h_i : v_i.toValue = Hax.Ascent.HaxEnc.enc i) :
    ReadsAs (guardedIf a i)
      (toRustMSB appRt guardedIf_impExpr ((ρ.upd "a" v_a).upd "i" v_i)) := by
  emit_reading [guardedIf, guardedIf_impExpr]

/-- A variable rebound in a monadic branch. -/
def rebind (a : Array Int) (i : Int) :=
  do
    let y := (0 : Int)
    let y ← do
      if Hax.lt i (3 : Int) then
        let y ← Hax.indexM a i
        pure y
      else
        pure y
    pure y

/-- The literal of `rebind`. -/
def rebind_impExpr : ImpExpr :=
  .letBind "a" (.var "a") (.letBind "i" (.var "i") (.letBind "y" (.lit (.int 0))
    (.seq (.ifThenElse (.app "Lt" [.var "i", .lit (.int 3)])
      (.letBind "y" (.app "index" [.var "a", .var "i"]) (.var "y")) .unitVal) (.var "y"))))

/-- The printed `rebind` reads as the `toRustMSB` reading of `rebind_impExpr`. -/
theorem rebind_reading (a : Array Int) (i : Int) (v_a : AVal) (v_i : AVal) (ρ : AEnv)
    (h_a : v_a.toValue = Hax.Ascent.HaxEnc.enc a)
    (h_i : v_i.toValue = Hax.Ascent.HaxEnc.enc i) :
    ReadsAs (rebind a i)
      (toRustMSB appRt rebind_impExpr ((ρ.upd "a" v_a).upd "i" v_i)) := by
  emit_reading [rebind, rebind_impExpr]

/-! ## A counted loop -/

/-- A counted loop. -/
def sumLoop (a : Array Int) (n : Int) :=
  do
    let acc := (0 : Int)
    Hax.foldRangeM (0 : Int) n acc fun j acc => do
      let _m0 ← Hax.indexM a j
      Hax.addM_w 32 acc _m0

/-- The literal of `sumLoop`. -/
def sumLoop_impExpr : ImpExpr :=
  .letBind "a" (.var "a") (.letBind "n" (.var "n") (.letBind "acc" (.lit (.int 0))
    (.seq (.forFold "j" (.lit (.int 0)) (.var "n") (.letBind "acc"
      (.app "Add#32" [.var "acc", .app "index" [.var "a", .var "j"]]) (.var "acc")))
      (.var "acc"))))

/-- The printed `sumLoop` reads as the `toRustMSB` reading of `sumLoop_impExpr`, by the loop
    square with the invariant: `a` is bound to `v_a`, and `acc` to a value encoding the printed
    accumulator. -/
theorem sumLoop_reading (a : Array Int) (n : Int) (v_a : AVal) (v_n : AVal) (ρ : AEnv)
    (h_a : v_a.toValue = Hax.Ascent.HaxEnc.enc a)
    (h_n : v_n.toValue = Hax.Ascent.HaxEnc.enc n) :
    ReadsAs (sumLoop a n)
      (toRustMSB appRt sumLoop_impExpr ((ρ.upd "a" v_a).upd "n" v_n)) := by
  intro o ρ' h
  simp only [sumLoop, sumLoop_impExpr, toRustMSB, toRustMSB.argsSB, AEnv.upd] at h ⊢
  simp [AEnv.upd, AVal.toInt?_int, AVal.toInt?_of_toValue h_n] at h
  by_cases hb : n ≤ 2 ^ System.Platform.numBits
  · simp only [hb, ↓reduceIte, bind_assoc_eq, bind_tc_ok] at h
    obtain ⟨⟨o1, ρ1⟩, hl, h⟩ := rustM_bind_ok h
    have hloop := foldRangeM_go_of_loopBS n.toNat
      (fun _ s ρ => ρ "a" = some v_a ∧
        ∃ v, ρ "acc" = some v ∧ v.toValue = Hax.Ascent.HaxEnc.enc s)
      (body := fun j acc => do
        let _m0 ← Hax.indexM a j
        Hax.addM_w 32 acc _m0)
      (by
        intro i s ρ o ρ' hi ⟨hρa, v, hρv, hv⟩ hst
        have hc : (ctr i).toValue = Hax.Ascent.HaxEnc.enc (i : Int) := ctr_toValue (by
          simp only [Aeneas.Std.UScalarTy.numBits]
          exact_mod_cast (show (i : Int) < 2 ^ System.Platform.numBits by omega))
        simp [AEnv.upd, hρa, hρv] at hst
        obtain ⟨r1, h1, hst⟩ := rustM_bind_ok hst
        obtain ⟨z1, hz1, hr1⟩ := rd_index h1 h_a hc
        obtain ⟨r2, h2, hst⟩ := rustM_bind_ok hst
        obtain ⟨z2, hz2, hr2⟩ := rd_checked (by rfl) (by rfl) h2 hv hr1
        simp only [AOp.emitM, Aeneas.Std.UScalarTy.numBits] at hz2
        cases hst
        exact ⟨rfl, z2, by simp only [hz1, hz2, Aeneas.Std.bind_tc_ok], by simp [AEnv.upd, hρa],
          r2, by simp [AEnv.upd], hr2⟩)
      n.toNat 0 0 _ o1 ρ1 (by omega) (by simp [AEnv.upd]; rfl) hl
    obtain ⟨rfl, s', hgo, -, v', hv', hvs⟩ := hloop
    simp only [hv'] at h
    cases h
    refine ⟨s', ?_, hvs⟩
    simpa [Hax.foldRangeM] using hgo
  · simp [hb] at h

end HaxAscent.RustSemantics.ReadingTacTest
