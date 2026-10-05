/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Guards
public import CatCrypt.Crypto.SecureCompilation.Ascent.Exit

/-!
# Type strengthening: the weakest fitting result monad

The pass of this module picks, for a program the ascent abstracts, the lowest of the
three result monads of `Ascent/Phases.lean` (`MonadLevel`: pure, `Option`,
exception) in which the abstract program is stated, and produces the abstract
program at that level (`AbsProg`) with its refinement theorem. AutoCorres's
TypeStrengthen is the model: try pure, then option, then exception. The lifting
lemmas of `Phases.lean` (`AbsProg.refines_lift_iff`, `AbsProg.refines_iff_toExcept`)
turn a program stated at a lower level into the same correspondence one level up.

## A `LowCT` command

`tsLowCTL L fuel c` reads the guards of the total abstraction `ascendGL L fuel c` over
the array layout `L`, and `tsLowCT` is its instance at the empty layout:

* a guard with an `unsupported` node anywhere: no abstract program (`none`);
* every guard statically true (`Guard.trivialB`): the pure transformer;
* otherwise: the `Option` program `optGuard (guardsHold gs) f`, failing exactly when a
  guard fails on the store.

A guard is statically true when it is an `assert`, a `range` guard whose expression
cannot leave `u64` range on a word store (`rangeTrivialB`: variables, literals below
`2 ^ 64`, the bitwise and signed/widening nodes, and a right shift by a literal below
`64`), or a pull-back of a statically true guard. `tsLowCTL_sound` states the
correspondence at the unified waist `semU fuel c` over `SRwordL L`, and
`tsLowCTL_sound_scalar` at `semScalar` on a loop-free command; `tsLowCT_sound` and
`tsLowCT_sound_scalar` are the same over `SRwordNT`. `arrSelK_tsLowCTL` abstracts the
array kernel `arrSelK` of `Guards.lean` at the pure level. A `LowCT` command has
no exit construct, so the pass never picks the exception level for it; the
exception-level body relation of the loop rule of `Ascent/Exit.lean` is
`corresUE_iff_refinesO`.

## A hax source program

The pass on a hax source is in hax-lean's `HaxAscent/Ascent/Exit.lean` (namespace
`Hax.Ascent`) and is re-exported here. `tsHax bi fuel e` abstracts a raw hax-lean program whose pipeline output
`Hax.pipeline e` encodes early exits as control-flow tags. The exception program is
the exception reading of the reference run, `haxExceptAbs`; its refinement of the
pipeline's encoded outcome is `haxExceptAbs_refines` (`pipeline_exceptProg`). The
pass picks the `Option` level when `Hax.checkNoEarlyExit e` holds and the exception
level otherwise. `denote_ne_earlyRet` proves that a program passing the check never
returns early, so on those programs the `Option` program is the exception program
(`tsHax_toExcept`). A fuel-bounded reference run fails on fuel exhaustion and on
ill-typed values, so the pass never picks the pure level for a hax source.

## Main definitions and results

* `rangeTrivialB`, `Guard.trivialB`, `Guard.unsupportedB` — the static guard analysis
* `tsLevelLowCTL`, `tsLowCTL`, `tsLowCTL_sound`, `tsLowCTL_sound_scalar`,
  `tsLowCTL_isSome_iff`, and their empty-layout instances `tsLevelLowCT`, `tsLowCT`,
  `tsLowCT_sound`, `tsLowCT_sound_scalar`, `tsLowCT_isSome_iff`
* `denote_ne_earlyRet` — a program without `return` or `?` never returns early
* `haxExceptAbs`, `haxPipelineSem`, `tsHaxLevel`, `tsHax`, `tsHax_sound`, `tsHax_toExcept`
* `Kernel`, `Kernel.tsLevel` — the choice over both program kinds

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The pass on a hax source, and the generic facts on the three levels

`liftOk` and `refinesO_exceptOk` are re-exported by `Phases.lean`; the hax-source pass
from `NotEarlyRet` to `tsHax_toExcept` is in hax-lean's `HaxAscent/Ascent/Exit.lean`
(namespace `Hax.Ascent`), re-exported here. -/

export _root_.Hax.Ascent (NotEarlyRet denote_notEarlyRet_mutual denote_ne_earlyRet
  haxExceptAbs haxPipelineSem haxEntry haxExceptAbs_refines haxExceptAbs_noThrow tsHaxLevel
  tsHax tsHax_level tsHax_sound tsHax_toExcept)

/-! ## The unified-waist relations as instances -/

/-- `CorresU` is `RefinesP` at the concrete semantics `semU fuel c`. -/
theorem corresU_iff_refinesP {AState : Type} (fuel : Nat) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) :
    CorresU fuel SR P fa c ↔ RefinesP (fun env => semU fuel c env) SR SR P fa := Iff.rfl

/-- The exception-level body relation `CorresUE` of the loop rule is the `Option`
    refinement, at `semU fuel c`, of the body step guarded by `P a ∧ C a`. -/
theorem corresUE_iff_refinesO {ε A : Type} (fuel : Nat) (SR : SEnvScalar → Except ε A → Prop)
    (P : A → Prop) [DecidablePred P] (C : A → Bool) (fb : A → ExceptT ε Id A) (c : LowCT) :
    CorresUE fuel SR P C fb c ↔
      RefinesO (fun env => semU fuel c env) (fun env a => SR env (.ok a)) SR
        (optGuard (fun a => P a ∧ C a = true) (fun a => (fb a).run)) := by
  rw [← refinesP_iff_refinesO_guard]
  constructor
  · intro h env a hSR hPC
    exact h env a hSR hPC.1 hPC.2
  · intro h env a hSR hP hC
    exact h env a hSR ⟨hP, hC⟩

/-! ## Static guard analysis -/

/-- The expression cannot leave `u64` range on a store of `u64` values: variables,
    literals below `2 ^ 64`, the nodes whose range condition is only the range of
    their operands, and a right shift by a literal below `64`. -/
def rangeTrivialB : SExpr → Bool
  | .SVar _ => true
  | .SLit n => litOkB n
  | .SAnd a b | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b
  | .SMulHiS a b => rangeTrivialB a && rangeTrivialB b
  | .SShr a (.SLit k) => rangeTrivialB a && decide (k < 64)
  | .SLimb _ _ => true
  | _ => false

theorem rangeTrivialB_sound {σ : String → Nat} (hσ : ∀ x, σ x < 2 ^ 64) :
    ∀ e : SExpr, rangeTrivialB e = true → e.inRange σ
  | .SVar x, _ => hσ x
  | .SLit n, h => by simpa [rangeTrivialB, litOkB, SExpr.inRange] using h
  | .SAnd a b, h | .SXor a b, h | .SLt a b, h | .SAsr a b, h | .SMulS a b, h
  | .SMulHiU a b, h | .SMulHiS a b, h => by
      simp only [rangeTrivialB, Bool.and_eq_true] at h
      exact ⟨rangeTrivialB_sound hσ a h.1, rangeTrivialB_sound hσ b h.2⟩
  | .SShr a b, h => by
      cases b with
      | SLit k =>
          simp only [rangeTrivialB, Bool.and_eq_true, decide_eq_true_eq] at h
          refine ⟨rangeTrivialB_sound hσ a h.1, ?_, ?_⟩
          · show k < 2 ^ 64
            omega
          · exact h.2
      | _ => simp [rangeTrivialB] at h
  | .SLimb _ _, _ => trivial
  | .SAdd _ _, h | .SSub _ _, h | .SMul _ _, h | .SShl _ _, h => by simp [rangeTrivialB] at h

/-- Every value of the Nat view of a word store is below `2 ^ 64`. -/
theorem natStore_lt (a : AField) (x : String) : natStore a x < 2 ^ 64 := ZMod.val_lt (a x)

/-- The guard holds on every store: an `assert`, a `range` guard passing
    `rangeTrivialB`, or a pull-back of such a guard. -/
def Guard.trivialB : Guard → Bool
  | .range _ e => rangeTrivialB e
  | .loopHalts _ _ _ => false
  | .unsupported _ => false
  | .assert _ => true
  | .after _ g => g.trivialB
  | .whenNz _ g => g.trivialB
  | .everyTrip _ _ _ g => g.trivialB
  | .loopBody _ _ _ g => g.trivialB

/-- The guard contains an `unsupported` node. -/
def Guard.unsupportedB : Guard → Bool
  | .unsupported _ => true
  | .after _ g => g.unsupportedB
  | .whenNz _ g => g.unsupportedB
  | .everyTrip _ _ _ g => g.unsupportedB
  | .loopBody _ _ _ g => g.unsupportedB
  | _ => false

/-- A predicate true on every state holds at the entry of every trip. -/
theorem atrips_of_forall {A : Type} {Q : A → Prop} (hQ : ∀ a, Q a) (g : A → Bool)
    (fb : A → A) : ∀ (k : Nat) (a : A), atrips Q g fb k a
  | 0, _ => trivial
  | k + 1, a => ⟨hQ a, fun _ => atrips_of_forall hQ g fb k (fb a)⟩

theorem Guard.trivialB_sound : ∀ (g : Guard), g.trivialB = true → ∀ a, g.holds a
  | .range _ e, h, a => rangeTrivialB_sound (natStore_lt a) e h
  | .loopHalts _ _ _, h, _ => by simp [Guard.trivialB] at h
  | .unsupported _, h, _ => by simp [Guard.trivialB] at h
  | .assert _, _, _ => trivial
  | .after _ g, h, _ => Guard.trivialB_sound g h _
  | .whenNz _ g, h, a => fun _ => Guard.trivialB_sound g h a
  | .everyTrip _ _ _ g, h, _ => fun _ _ => Guard.trivialB_sound g h _
  | .loopBody _ _ _ g, h, _ => atrips_of_forall (Guard.trivialB_sound g h) _ _ _ _

/-! ## The pass on a `LowCT` command -/

/-- The level `tsLowCTL` picks over the layout `L`: none for an unsupported node, pure
    when every guard is statically true, `Option` otherwise. -/
def tsLevelLowCTL (L : ArrLayout) (fuel : Nat) (c : LowCT) : Option MonadLevel :=
  if (ascendGL L fuel c).1.any Guard.unsupportedB then none
  else if (ascendGL L fuel c).1.all Guard.trivialB then some .pure
  else some .option

/-- The level `tsLowCT` picks: `tsLevelLowCTL` at the empty layout. -/
abbrev tsLevelLowCT (fuel : Nat) (c : LowCT) : Option MonadLevel := tsLevelLowCTL [] fuel c

/-- The abstract program of a `LowCT` command over the layout `L` at the weakest fitting
    level: the transformer of `ascendGL L` as a pure function when its guards are
    statically true, as the `Option` program failing where a guard fails otherwise, and
    none when a guard contains an `unsupported` node. -/
def tsLowCTL {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    Option (AbsProg ε AField AField) :=
  if (ascendGL L fuel c).1.any Guard.unsupportedB then none
  else if (ascendGL L fuel c).1.all Guard.trivialB then some (.pure (ascendGL L fuel c).2)
  else some (.option (optGuard (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2))

/-- The abstract program of a `LowCT` command over `SRwordNT`: `tsLowCTL` at the empty
    layout. -/
abbrev tsLowCT {ε : Type} (fuel : Nat) (c : LowCT) : Option (AbsProg ε AField AField) :=
  tsLowCTL [] fuel c

theorem tsLowCTL_level {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    (tsLowCTL (ε := ε) L fuel c).map AbsProg.level = tsLevelLowCTL L fuel c := by
  unfold tsLowCTL tsLevelLowCTL
  split
  · rfl
  · split <;> rfl

theorem tsLowCT_level {ε : Type} (fuel : Nat) (c : LowCT) :
    (tsLowCT (ε := ε) fuel c).map AbsProg.level = tsLevelLowCT fuel c :=
  tsLowCTL_level [] fuel c

/-- **Soundness of the pass at the unified waist over a layout.** The abstract program
    `tsLowCTL L` returns refines `c` under `semU fuel` over `SRwordL L`, at its own
    level. -/
theorem tsLowCTL_sound {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT)
    {p : AbsProg ε AField AField} (h : tsLowCTL L fuel c = some p) :
    p.Refines (fun env => semU fuel c env) (SRwordL L) (liftOk (SRwordL L)) := by
  have hs := ascendGL_sound L fuel c
  unfold tsLowCTL at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i htriv
      obtain rfl := Option.some.inj h
      intro env a hSR _
      exact hs env a hSR (fun g hg => Guard.trivialB_sound g (List.all_eq_true.mp htriv g hg) a)
    · obtain rfl := Option.some.inj h
      exact (refinesP_iff_refinesO_guard (fun env => semU fuel c env) (SRwordL L) (SRwordL L)
        (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2).mp hs

/-- **Soundness of the pass at the unified waist.** The abstract program `tsLowCT`
    returns refines `c` under `semU fuel` over `SRwordNT`, at its own level. -/
theorem tsLowCT_sound {ε : Type} (fuel : Nat) (c : LowCT) {p : AbsProg ε AField AField}
    (h : tsLowCT fuel c = some p) :
    p.Refines (fun env => semU fuel c env) SRwordNT (liftOk SRwordNT) := by
  have hs := ascendG_sound fuel c
  unfold tsLowCT tsLowCTL at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i htriv
      obtain rfl := Option.some.inj h
      intro env a hSR _
      exact hs env a hSR (fun g hg => Guard.trivialB_sound g (List.all_eq_true.mp htriv g hg) a)
    · obtain rfl := Option.some.inj h
      exact (refinesP_iff_refinesO_guard (fun env => semU fuel c env) SRwordNT SRwordNT
        (guardsHold (ascendG fuel c).1) (ascendG fuel c).2).mp hs

/-- **Soundness of the pass at `semScalar` over a layout** on a loop-free command. -/
theorem tsLowCTL_sound_scalar {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT)
    (hlf : loopFree c = true) {p : AbsProg ε AField AField} (h : tsLowCTL L fuel c = some p) :
    p.Refines (fun env => semScalar c env) (SRwordL L) (liftOk (SRwordL L)) := by
  have hsem : (fun env => semU fuel c env) = (fun env => semScalar c env) :=
    funext (semU_eq_semScalar_of_loopFree fuel c hlf)
  have hs := tsLowCTL_sound L fuel c h
  rwa [hsem] at hs

/-- **Soundness of the pass at `semScalar`** on a loop-free command. -/
theorem tsLowCT_sound_scalar {ε : Type} (fuel : Nat) (c : LowCT) (hlf : loopFree c = true)
    {p : AbsProg ε AField AField} (h : tsLowCT fuel c = some p) :
    p.Refines (fun env => semScalar c env) SRwordNT (liftOk SRwordNT) := by
  have hsem : (fun env => semU fuel c env) = (fun env => semScalar c env) :=
    funext (semU_eq_semScalar_of_loopFree fuel c hlf)
  have hs := tsLowCT_sound fuel c h
  rwa [hsem] at hs

/-- The pass over a layout returns a program exactly when no guard contains an
    `unsupported` node. -/
theorem tsLowCTL_isSome_iff {ε : Type} (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    (tsLowCTL (ε := ε) L fuel c).isSome = true ↔
      (ascendGL L fuel c).1.any Guard.unsupportedB = false := by
  unfold tsLowCTL
  split
  · rename_i hu; simp [hu]
  · rename_i hu
    simp only [Bool.not_eq_true] at hu
    simp only [hu, iff_true]
    split <;> rfl

/-- The pass returns a program exactly when no guard contains an `unsupported`
    node. -/
theorem tsLowCT_isSome_iff {ε : Type} (fuel : Nat) (c : LowCT) :
    (tsLowCT (ε := ε) fuel c).isSome = true ↔
      (ascendG fuel c).1.any Guard.unsupportedB = false :=
  tsLowCTL_isSome_iff [] fuel c

/-- The array kernel `arrSelK` is abstracted at the pure level over its layout: its one
    guard, the range condition of the mask select, is statically true. -/
theorem arrSelK_tsLowCTL {ε : Type} (fuel : Nat) :
    tsLowCTL (ε := ε) arrSelLayout fuel arrSelK = some (.pure arrSelKAbs) := rfl

/-- The pure program of `arrSelK` refines its `semScalar` run over `SRwordL arrSelLayout`. -/
theorem arrSelK_ts_refines {ε : Type} :
    (AbsProg.pure (ε := ε) arrSelKAbs).Refines (fun env => semScalar arrSelK env)
      (SRwordL arrSelLayout) (liftOk (SRwordL arrSelLayout)) :=
  tsLowCTL_sound_scalar arrSelLayout 0 arrSelK rfl (arrSelK_tsLowCTL 0)

/-! ## The choice over both program kinds -/

/-- A program the ascent abstracts: a `LowCT` command at a fuel, or a raw hax source
    under a builtin table and a fuel. -/
inductive Kernel where
  | lowct (fuel : Nat) (c : LowCT)
  | hax (bi : Hax.Builtins) (fuel : Nat) (e : Hax.ImpExpr)

/-- The level the pass picks for a kernel; `none` when the `LowCT` abstraction has an
    unsupported node. -/
def Kernel.tsLevel : Kernel → Option MonadLevel
  | .lowct fuel c => tsLevelLowCT fuel c
  | .hax _ _ e => some (tsHaxLevel e)

end CatCrypt.Crypto.SecureCompilation.Ascent
