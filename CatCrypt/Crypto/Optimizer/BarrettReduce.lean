/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.RenameCalls

/-!
# Pass 1.1 — Barrett leaf renaming

A pass of CatCrypt's optimizer on `LowCT`. It renames the leaf calls
`"mod_q"` and ML-KEM's `"reduce"` to the Barrett leaf `s!"barrett_{q}"` for a
statically known modulus `q`; it is the call renaming
`RenameCalls.renameCalls (barrettSubst q)`.

The pass changes leaf names only. Its semantic statement is a congruence: when
the leaf specification gives `barrett_{q}` the same result as `"mod_q"` and
`"reduce"` on every input (`barrettAgreesModQ`), the renamed command has the
same executions. The Barrett arithmetic of the leaf is proved in
`Rewrite/BarrettReduceGeneric`.

## Main results

* `barrettReduce q` — the renaming pass, `renameCalls (barrettSubst q)`.
* `barrettAgreesModQ leafSpec q` — the leaf-agreement hypothesis.
* `renamedCallsAgree_barrettSubst` — `barrettAgreesModQ` gives `RenamedCallsAgree` for the
  renaming.
* `rustExec_barrettReduce_iff` — under `barrettAgreesModQ`, `barrettReduce q c`
  and `c` have the same executions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.BarrettReduce

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.RenameCalls

/-! ## §1  Pattern recognition

A leaf call is a mod-q reduction site if its name is `"mod_q"` (the name used
in the abstract spec) or `"reduce"` (ML-KEM's kernel name, see
`CatCrypt/Crypto/MLKEM/MlkemLowCT.lean` §2.1). -/

/-- The call name `f` is one of the recognised mod-q reduction-site names. -/
def isModQName (f : String) : Bool :=
  f == "mod_q" || f == "reduce"

@[simp] theorem isModQName_mod_q : isModQName "mod_q" = true := by
  decide

@[simp] theorem isModQName_reduce : isModQName "reduce" = true := by
  decide

/-! ## §2  Rewrite pass -/

/-- The name of the Barrett-q leaf for a given modulus `q`. -/
@[inline] def barrettName (q : Nat) : String := s!"barrett_{q}"

/-- The renaming of the Barrett pass: a recognised mod-q name goes to
    `barrettName q`, every other name is kept. -/
def barrettSubst (q : Nat) (f : String) : String :=
  if isModQName f then barrettName q else f

/-- The Barrett pass for the modulus `q`: the leaf-call renaming
    `renameCalls (barrettSubst q)`, which replaces `RCall "mod_q"` and
    `RCall "reduce"` (and the same names in `RCallSwap`, `RCloneCall` and
    `RCallDstThreaded`) by `barrettName q`. -/
def barrettReduce (q : Nat) : LowCT → LowCT :=
  renameCalls (barrettSubst q)

/-! ## §3  Leaf agreement -/

/-- The leaf specification's Barrett-`q` leaf agrees with the `"mod_q"` and
    `"reduce"` leaves on all inputs. -/
def barrettAgreesModQ (leafSpec : LeafSpec) (q : Nat) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    isModQName f = true →
    leafSpec.call (barrettName q) dt argTs oldV args =
      leafSpec.call f dt argTs oldV args

/-- `barrettAgreesModQ` is the `RenamedCallsAgree` hypothesis of the renaming
    `barrettSubst q`. -/
theorem renamedCallsAgree_barrettSubst {leafSpec : LeafSpec} {q : Nat}
    (hAgree : barrettAgreesModQ leafSpec q) :
    RenamedCallsAgree leafSpec (barrettSubst q) := by
  intro f dt argTs oldV args
  unfold barrettSubst
  split
  · exact hAgree f dt argTs oldV args ‹_›
  · rfl

/-! ## §4  Semantic congruence -/

/-- Under `barrettAgreesModQ leafSpec q`, the Barrett leaf renaming preserves
    the big-step semantics: `barrettReduce q c` and `c` have the same
    executions. The statement is about the renaming; it does not concern the
    arithmetic of the Barrett leaf. -/
theorem rustExec_barrettReduce_iff
    (q : Nat) (N : Nat) (leafSpec : LeafSpec)
    (hAgree : barrettAgreesModQ leafSpec q)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (barrettReduce q c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  rustExec_renameCalls_iff (renamedCallsAgree_barrettSubst hAgree) c rs rs'

end CatCrypt.Crypto.Optimizer.BarrettReduce
