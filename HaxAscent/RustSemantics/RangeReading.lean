/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.RangeBridge
public import HaxAscent.RustSemantics.ReadingTac
public import CatCryptCore.Crypto.UCMonad.RustMBridge

/-!
# Range-checked printed functions return their surface value

The range checker's acceptance of an extracted function (the statement `f_noPanicOn` of
`--emit-monadic`) makes the `toRustMSB` reading of its body return the encoding of the total
surface function on the checked range (`toRustMSB_spec_of_noPanicOn`,
`HaxAscent/RustSemantics/RangeBridge.lean`). The reading theorem `f_reading` of
`--emit-reading` (`ReadsAs`, `HaxAscent/RustSemantics/ReadingTac.lean`) transfers a value of
the reading to the function printed by `--emit-monadic`. Composed, the printed function returns
the surface value on the checked range, so it is `PanicFreeOn` that range with no proof per
function.

## Main definitions

* `CheckedRange`: the arguments on which the range checker's acceptance applies.

## Main results

* `toRustMSB_panicFreeOn_of_noPanicOn`: the reading of a range-checked body is `PanicFreeOn`
  the checked range.
* `ok_of_reading`: on the checked range, the printed function returns `.ok (f_pure a)`.
* `panicFreeOn_of_reading`: the printed function is `PanicFreeOn` the checked range.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RangeRustM

open CatCrypt CatCrypt.Hax CatCrypt.Hax.RustSemantics HaxAscent.RustSemantics Aeneas.Std

variable {g : String → List _root_.Hax.Value → Bool} {bi : _root_.Hax.Builtins}
  {app : String → List AVal → _root_.RustM AVal} {entry : _root_.Hax.Range.AEnv}
  {e : _root_.Hax.ImpExpr} {A β : Type} [Hax.Ascent.HaxEnc β] {G : A → Prop}
  {f_pure : A → β} {entryOf : A → AEnv}

/-- The arguments on which the range checker's acceptance applies: those satisfying the
    guard `G` of the function correspondence, whose environment is small, lies in the
    checked abstract environment `entry` and holds no control-flow value. -/
def CheckedRange (G : A → Prop) (entry : _root_.Hax.Range.AEnv) (entryOf : A → AEnv) (a : A) :
    Prop :=
  G a ∧ EnvSmall (entryOf a) ∧ _root_.Hax.Range.Sat entry (encEnv (entryOf a)) ∧
    _root_.Hax.Env.NoControlFlow (encEnv (entryOf a))

/-- The `toRustMSB` reading of a range-checked body is panic-free on the checked range. -/
theorem toRustMSB_panicFreeOn_of_noPanicOn
    (hF : Hax.Ascent.FnCorres bi e (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppComplete (_root_.Hax.Range.guardBi g bi) app) {k : Bool} (hf : RevFrag k e) :
    UCMonad.RustMBridge.PanicFreeOn (CheckedRange G entry entryOf)
      (fun a => toRustMSB app e (entryOf a)) := by
  rintro a ⟨hG, hρ, hΓ, hN⟩
  obtain ⟨r, ρ', h, -⟩ := toRustMSB_spec_of_noPanicOn hF hnp hc hf a hG hρ hΓ hN
  exact ⟨(r, ρ'), h⟩

/-- **A range-checked printed function returns its surface value.** Let `fM` be the function
    printed by `--emit-monadic`, read by its literal `e` (`hread`, the theorem `f_reading`),
    accepted by the range checker (`hnp`, the theorem `f_noPanicOn`), with total surface
    `f_pure` (`hF`). On the checked range, `fM a` returns `.ok (f_pure a)`. -/
theorem ok_of_reading [Hax.Ascent.HaxEnc.Inj β] {fM : A → _root_.RustM β}
    (hF : Hax.Ascent.FnCorres bi e (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppComplete (_root_.Hax.Range.guardBi g bi) app) {k : Bool} (hf : RevFrag k e)
    (hread : ∀ a, ReadsAs (fM a) (toRustMSB app e (entryOf a)))
    {a : A} (ha : CheckedRange G entry entryOf a) :
    fM a = .ok (f_pure a) := by
  obtain ⟨hG, hρ, hΓ, hN⟩ := ha
  obtain ⟨r, ρ', h, hv⟩ := toRustMSB_spec_of_noPanicOn hF hnp hc hf a hG hρ hΓ hN
  obtain ⟨v, hm, hr⟩ := hread a r ρ' h
  rw [hm, Hax.Ascent.HaxEnc.Inj.inj (hr.symm.trans hv)]

/-- A range-checked printed function is panic-free on the checked range. -/
theorem panicFreeOn_of_reading [Hax.Ascent.HaxEnc.Inj β] {fM : A → _root_.RustM β}
    (hF : Hax.Ascent.FnCorres bi e (fun a => encEnv (entryOf a)) G f_pure)
    (hnp : ∀ (fuel : Nat) (env : _root_.Hax.Env), _root_.Hax.Range.Sat entry env →
      _root_.Hax.Env.NoControlFlow env →
      _root_.Hax.denote' (_root_.Hax.Range.guardBi g bi) fuel e env =
        _root_.Hax.denote' bi fuel e env)
    (hc : AppComplete (_root_.Hax.Range.guardBi g bi) app) {k : Bool} (hf : RevFrag k e)
    (hread : ∀ a, ReadsAs (fM a) (toRustMSB app e (entryOf a))) :
    UCMonad.RustMBridge.PanicFreeOn (CheckedRange G entry entryOf) fM :=
  fun _ ha => ⟨_, ok_of_reading hF hnp hc hf hread ha⟩

end CatCrypt.Hax.RangeRustM
