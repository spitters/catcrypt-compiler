/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.RenameCalls

/-!
# Pass 1.2 — Montgomery leaf renaming

A pass of CatCrypt's optimizer on `LowCT`, sibling to `BarrettReduce.lean`. It
renames the leaf calls `"mul_mod_q"` and ML-KEM's `"mul_reduce"` to the
Montgomery multiplication leaf `s!"mont_mul_{q}_{R}"` for a statically known
modulus `q` and radix `R = 2^k`; it is the call renaming
`RenameCalls.renameCalls (montSubst q R)`. Any conversion into and out of
Montgomery form belongs to the leaf, and the backend dispatches on the leaf
name.

The pass changes leaf names only. Its semantic statement is a congruence: when
the leaf specification gives `mont_mul_{q}_{R}` the same result as
`"mul_mod_q"` and `"mul_reduce"` on every input (`montAgreesMulModQ`), the
renamed command has the same executions. The Montgomery arithmetic of the leaf
is proved in `Rewrite/MontgomeryRedcGeneric`.

In `Optimizer/Pipeline.lean` this pass is `montgomeryPass`.

## Main results

* `montgomeryReduce q R` — the renaming pass, `renameCalls (montSubst q R)`.
* `montAgreesMulModQ leafSpec q R` — the leaf-agreement hypothesis.
* `callsAgree_montSubst` — `montAgreesMulModQ` gives `CallsAgree` for the
  renaming.
* `rustExec_montgomeryReduce_iff` — under `montAgreesMulModQ`,
  `montgomeryReduce q R c` and `c` have the same executions; its ML-KEM
  instance is `rustExec_montgomeryReduceMlkem_iff`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.MontgomeryReduce

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Optimizer.RenameCalls

/-! ## §1  Pattern recognition

A leaf call is a mul-mod-q multiplication site if its name is `"mul_mod_q"`
or `"mul_reduce"` (ML-KEM's fused multiply-reduce kernel). -/

/-- The call name `f` is one of the recognised mul-mod-q multiplication-site
    names. -/
def isMulModQName (f : String) : Bool :=
  f == "mul_mod_q" || f == "mul_reduce"

@[simp] theorem isMulModQName_mul_mod_q : isMulModQName "mul_mod_q" = true := by
  decide

@[simp] theorem isMulModQName_mul_reduce : isMulModQName "mul_reduce" = true := by
  decide

/-! ## §2  Rewrite pass -/

/-- The name of the Montgomery multiplication leaf for given modulus
    `q` and radix `R`. -/
@[inline] def montMulName (q R : Nat) : String := s!"mont_mul_{q}_{R}"

/-- The renaming of the Montgomery pass: a recognised mul-mod-q name goes to
    `montMulName q R`, every other name is kept. -/
def montSubst (q R : Nat) (f : String) : String :=
  if isMulModQName f then montMulName q R else f

/-- The Montgomery pass for the modulus `q` and radix `R`: the leaf-call
    renaming `renameCalls (montSubst q R)`, which replaces `RCall "mul_mod_q"`
    and `RCall "mul_reduce"` (and the same names in `RCallSwap`, `RCloneCall`
    and `RCallDstThreaded`) by `montMulName q R`. -/
def montgomeryReduce (q R : Nat) : LowCT → LowCT :=
  renameCalls (montSubst q R)

/-! ## §3  Leaf agreement -/

/-- The leaf specification's Montgomery multiplication leaf agrees with the
    `"mul_mod_q"` and `"mul_reduce"` leaves on all inputs. -/
def montAgreesMulModQ (leafSpec : LeafSpec) (q R : Nat) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldV : RustVal dt) (args : List (Σ t : TowerType, RustVal t)),
    isMulModQName f = true →
    leafSpec.call (montMulName q R) dt argTs oldV args =
      leafSpec.call f dt argTs oldV args

/-- `montAgreesMulModQ` is the `CallsAgree` hypothesis of the renaming
    `montSubst q R`. -/
theorem callsAgree_montSubst {leafSpec : LeafSpec} {q R : Nat}
    (hAgree : montAgreesMulModQ leafSpec q R) :
    CallsAgree leafSpec (montSubst q R) := by
  intro f dt argTs oldV args
  unfold montSubst
  split
  · exact hAgree f dt argTs oldV args ‹_›
  · rfl

/-! ## §4  Semantic congruence -/

/-- Under `montAgreesMulModQ leafSpec q R`, the Montgomery leaf renaming
    preserves the big-step semantics: `montgomeryReduce q R c` and `c` have
    the same executions. The statement is about the renaming; it does not
    concern the arithmetic of the Montgomery leaf. -/
theorem rustExec_montgomeryReduce_iff
    (q R : Nat) (N : Nat) (leafSpec : LeafSpec)
    (hAgree : montAgreesMulModQ leafSpec q R)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (montgomeryReduce q R c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  rustExec_renameCalls_iff (callsAgree_montSubst hAgree) c rs rs'

/-! ## §5  ML-KEM specialisation

ML-KEM works over `Z_q[X] / (X^256 + 1)` with `q = 3329` and Montgomery radix
`R = 2^16 = 65536`, matching the `i16` limbs of the reference and formosa
implementations. -/

/-- ML-KEM modulus. -/
abbrev mlkem_q : Nat := 3329

/-- ML-KEM Montgomery radix: `2^16`, matching the `i16` representation
    used by both the reference C implementation and the formosa-MLKEM
    Jasmin port. -/
abbrev mlkem_R : Nat := 65536

/-- Montgomery renaming pre-specialised for ML-KEM. -/
abbrev montgomeryReduceMlkem : LowCT → LowCT :=
  montgomeryReduce mlkem_q mlkem_R

/-- ML-KEM instance of `rustExec_montgomeryReduce_iff`. -/
theorem rustExec_montgomeryReduceMlkem_iff
    (N : Nat) (leafSpec : LeafSpec)
    (hAgree : montAgreesMulModQ leafSpec mlkem_q mlkem_R)
    (c : LowCT) (rs rs' : RustState) :
    RustExec N leafSpec (montgomeryReduceMlkem c) rs rs' ↔
      RustExec N leafSpec c rs rs' :=
  rustExec_montgomeryReduce_iff mlkem_q mlkem_R N leafSpec hAgree c rs rs'

end CatCrypt.Crypto.Optimizer.MontgomeryReduce
