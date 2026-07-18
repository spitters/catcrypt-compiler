/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.LowCTCT
import CatCrypt.Crypto.SecureCompilation.LowCTCTBridge

/-!
# Labeled-LowCT: Trail-of-Bits-style `Secret<T>` framing (Track C5)

Companion to `LowCTCT.lean` (the structural CT predicate
`isCT_LowCT'`). This file restates the same discipline in Trail of
Bits' labeled `Secret<T>` framing: every variable name carries a
`Label` (Public/Secret), and the `wellLabeled` predicate enforces the
ToB rules — no branching on secret-labeled scalars, no
secret-labeled-indexed memory access, etc.

The labeled predicate is **equivalent** to `isCT_LowCT'` modulo the
naming convention (a `Labeling` and a `SecretSet` carry the same
information). The motivation is cosmetic and audience-facing:

* Security writeups quote Trail of Bits' "Secret<T>" terminology.
* Information-flow proofs typically state CT as
  "noninterference under a public/secret partition", not as
  "structurally CT-by-construction".
* When/if LowCT grows to admit secret-indexed memory, the labeled
  framing extends uniformly without growing `isCT_LowCT'`.

## What this file establishes

* `Label` (Public/Secret), `Labeling := String → Label`.
* `Labeling.toSecretSet` and `SecretSet.toLabeling` — the bijection.
* `wellLabeled` predicate — ToB's discipline as a Bool check.
* `wellLabeled_iff_isCT_LowCT'` — the discipline coincides with the
  existing structural check.
* `wellLabeled_implies_isCT_LowCT'` — the useful direction Qed.

**0 sorries.** Standard axioms.

## References

* Trail of Bits — *Achieving Constant-Time Rust* (blog post, 2024).
-/

namespace CatCrypt.Crypto.SecureCompilation.LowCTLabeled

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.LowCTCT

set_option autoImplicit false

/-! ## §1. Labels -/

/-- A flow-sensitivity label, in Trail of Bits' `Secret<T>` framing.

* `Public` — the value can flow into branch conditions, indices,
  variable-time intrinsics. Plumbed through to the public observable.
* `Secret` — the value is cryptographically sensitive. Cannot be
  branched on, indexed by, or fed to variable-time operations. -/
inductive Label where
  | Public : Label
  | Secret : Label
  deriving DecidableEq, Repr, Inhabited

/-- A labeling assigns a `Label` to every variable name. -/
abbrev Labeling := String → Label

/-! ## §2. Bijection with `SecretSet`

`isCT_LowCT'` (in `LowCTCT.lean`) takes a `SecretSet := String →
Bool`, where `secrets x = true` means "x holds a secret value". The
labeled framing carries the same information as a `Labeling`, and the
two are equi-expressive. -/

/-- View a labeling as a secret set: a name is in the set iff it's
labeled `Secret`. -/
def Labeling.toSecretSet (l : Labeling) : SecretSet :=
  fun x => match l x with
    | .Secret => true
    | .Public => false

/-- View a secret set as a labeling: names in the set are `Secret`,
the rest `Public`. -/
def SecretSet.toLabeling (s : SecretSet) : Labeling :=
  fun x => if s x then .Secret else .Public

/-- Round-trip: `Labeling → SecretSet → Labeling` is the identity. -/
theorem Labeling.toSecretSet_toLabeling (l : Labeling) :
    SecretSet.toLabeling (Labeling.toSecretSet l) = l := by
  funext x
  unfold SecretSet.toLabeling Labeling.toSecretSet
  cases h : l x with
  | Public => simp [h]
  | Secret => simp [h]

/-- Round-trip: `SecretSet → Labeling → SecretSet` is the identity. -/
theorem SecretSet.toLabeling_toSecretSet (s : SecretSet) :
    Labeling.toSecretSet (SecretSet.toLabeling s) = s := by
  funext x
  unfold Labeling.toSecretSet SecretSet.toLabeling
  by_cases h : s x = true
  · simp [h]
  · simp [h]

/-! ## §3. The labeled CT discipline

`wellLabeled label c` is the labeled-LowCT analogue of `isCT_LowCT'
leaves secrets c`. It enforces Trail of Bits' rules at the AST level:

* `RIfNz x _ _` accepted only when `label x = Public`.
* `RWhileNz x _` accepted only when `label x = Public`.
* `RScalarSet`, `RLetU64Zero`, `RLetZero` are accepted unconditionally
  — the *value* may be secret; what matters is whether subsequent
  branches consume it as a guard.
* `RCall f` accepted when `f` is in the leaf whitelist (verified-CT
  leaves; same role as `leaves` in `isCT_LowCT'`).
* `RCloneCall _ _ _ innerF _ _` accepted when `innerF` is in the
  whitelist (the clone primitive itself is structural).
* Structural cases (`RSkip`, `RSeq`, `RLimbStore`) accept by
  recursion or unconditionally.

The connection to `isCT_LowCT'`: `wellLabeled label c` holds iff
`isCT_LowCT' leaves (label.toSecretSet) c` does, for the same leaf
whitelist. Proven below. -/

/-- Decidable Bool labeled-CT predicate. -/
def wellLabeled (leaves : CTLeaves) (label : Labeling) : LowCT → Bool
  | .RSkip                           => true
  | .RSeq c1 c2                      => wellLabeled leaves label c1
                                          && wellLabeled leaves label c2
  | .RLetZero _ _ body               => wellLabeled leaves label body
  | .RLetU64Zero _ body              => wellLabeled leaves label body
  | .RScalarSet _ _                  => true
  | .RCall f _ _                     => leaves f
  | .RCloneCall _ _ _ innerF _ _     => leaves innerF
  | .RIfNz x t f                     =>
      decide (label x = .Public)
        && wellLabeled leaves label t
        && wellLabeled leaves label f
  | .RWhileNz x body                 =>
      decide (label x = .Public)
        && wellLabeled leaves label body
  | .RFor _ _ body                   => wellLabeled leaves label body
  | .RForRuntime _ _ body            => wellLabeled leaves label body
  | .RLimbStore _ _ _                => true
  | .RLimbStoreExpr _ _ _            => true
  -- Phase F/G/H/L/M (2026-05-03): mirror the strict CT predicate.
  | .RCallSwap f _ _ _               => leaves f
  -- #235: mirror `isCT_LowCT'`'s tightened `RAsmOp` gate — CT iff the
  -- opcode is on the vendor DOIT∩DIT whitelist `ct_intrinsic`.
  | .RAsmOp name _ _                 => CatCrypt.Crypto.Jasmin.ct_intrinsic name
  | .RCallN f _ _                    => leaves f
  | .RSelect _ _ _ _                 => true
  | .RAssert _                       => true
  | .RBlock body                     => wellLabeled leaves label body
  | .RFnDef _ _ _ body cont          =>
      wellLabeled leaves label body && wellLabeled leaves label cont
  | .RFnCall f _ _                   => leaves f
  -- Phase I (2026-05-03): tuple component store/load is structural.
  | .RTupleStore _ _ _               => true
  | .RTupleLoad _ _ _                => true
  -- Phase J (added later): byte slice / array load/store / scalar-set-from-expr
  -- are structural (no data-dependent control flow).
  | .RBytesSlice _ _ _ _             => true
  | .RScalarSetExpr _ _              => true
  | .RArrLoad _ _ _                  => true
  | .RArrStore _ _ _                 => true
  -- Phase Ext3 / E2 (2026-05-29): literal-indexed array store/load are
  -- structural (no data-dependent control flow); the dst-threaded leaf call
  -- is accepted exactly when its leaf is whitelisted — mirroring
  -- `isCT_LowCT'`.
  | .RArrStoreLit _ _ _              => true
  | .RArrLoadLit _ _ _               => true
  | .RCallDstThreaded f _ _          => leaves f

/-! ## §4. Equivalence with the existing structural predicate -/

/-- The labeled discipline coincides with `isCT_LowCT'` under the
canonical `Labeling ↔ SecretSet` bijection. Forward direction. -/
theorem wellLabeled_iff_isCT_LowCT' (leaves : CTLeaves) (label : Labeling)
    (c : LowCT) :
    wellLabeled leaves label c = true ↔
    isCT_LowCT' leaves (Labeling.toSecretSet label) c = true := by
  induction c with
  | RSkip => simp [wellLabeled, isCT_LowCT']
  | RSeq c1 c2 ih1 ih2 =>
      simp [wellLabeled, isCT_LowCT', ih1, ih2]
  | RLetZero _ _ body ih => simp [wellLabeled, isCT_LowCT', ih]
  | RLetU64Zero _ body ih => simp [wellLabeled, isCT_LowCT', ih]
  | RScalarSet _ _ => simp [wellLabeled, isCT_LowCT']
  | RCall _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RCloneCall _ _ _ _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RIfNz x t f ih1 ih2 =>
      simp only [wellLabeled, isCT_LowCT', Labeling.toSecretSet,
                 Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_eq_eq_not,
                 Bool.not_true]
      constructor
      · rintro ⟨⟨hlabel, ht⟩, hf⟩
        refine ⟨⟨?_, ih1.mp ht⟩, ih2.mp hf⟩
        rw [hlabel]
      · rintro ⟨⟨hlabel, ht⟩, hf⟩
        refine ⟨⟨?_, ih1.mpr ht⟩, ih2.mpr hf⟩
        cases hL : label x
        case Public => rfl
        case Secret => rw [hL] at hlabel; cases hlabel
  | RWhileNz x body ih =>
      simp only [wellLabeled, isCT_LowCT', Labeling.toSecretSet,
                 Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_eq_eq_not,
                 Bool.not_true]
      constructor
      · rintro ⟨hlabel, hbody⟩
        refine ⟨?_, ih.mp hbody⟩
        rw [hlabel]
      · rintro ⟨hlabel, hbody⟩
        refine ⟨?_, ih.mpr hbody⟩
        cases hL : label x
        case Public => rfl
        case Secret => rw [hL] at hlabel; cases hlabel
  | RFor _ _ body ih => simp [wellLabeled, isCT_LowCT', ih]
  | RForRuntime _ _ body ih => simp [wellLabeled, isCT_LowCT', ih]
  | RLimbStore _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RLimbStoreExpr _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RCallSwap _ _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RAsmOp _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RCallN _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RSelect _ _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RAssert _ => simp [wellLabeled, isCT_LowCT']
  | RBlock body ih => simp [wellLabeled, isCT_LowCT', ih]
  | RFnDef _ _ _ _ _ ih_body ih_cont =>
      simp [wellLabeled, isCT_LowCT', ih_body, ih_cont]
  | RFnCall _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RTupleStore _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RTupleLoad _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RBytesSlice _ _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RScalarSetExpr _ _ => simp [wellLabeled, isCT_LowCT']
  | RArrLoad _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RArrStore _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RArrStoreLit _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RArrLoadLit _ _ _ => simp [wellLabeled, isCT_LowCT']
  | RCallDstThreaded _ _ _ => simp [wellLabeled, isCT_LowCT']

/-- Useful direction: `wellLabeled` implies `isCT_LowCT'`. -/
theorem wellLabeled_implies_isCT_LowCT'
    (leaves : CTLeaves) (label : Labeling) (c : LowCT)
    (h : wellLabeled leaves label c = true) :
    isCT_LowCT' leaves (Labeling.toSecretSet label) c = true :=
  (wellLabeled_iff_isCT_LowCT' leaves label c).mp h

/-! ## §5. Lift to x86-64 CT (composition with the C3 chain)

`wellLabeled_implies_isCT_LowCT'` composes with the existing
`rustcmd_ct_implies_x86_ct` (in `LowCTCTBridge.lean`) to yield the
literature-idiomatic statement:

    wellLabeled leaves label c   →   x86-64 program is CT.

This is the cosmetic upgrade the C5 track aimed at: a callsite
expressing CT in Trail of Bits' `Secret<T>` framing rather than the
structural shape predicate, with the verified-middle and back-end
preservation theorems inherited verbatim from C3. -/

open CatCrypt.Crypto.SecureCompilation.LowCTCTBridge
open CatCrypt.Crypto.SecureCompilation.JasminCompilerBridge

/-- **Labeled-LowCT CT preservation** (C5 corollary). For any
labeling and `wellLabeled` source program, the compiled x86-64
program is constant-time. Composes
`wellLabeled_implies_isCT_LowCT'` with
`rustcmd_ct_implies_x86_ct`. -/
theorem wellLabeled_implies_x86_ct
    (leaves : CTLeaves) (label : Labeling)
    (c : LowCT)
    (h_lab : wellLabeled leaves label c = true)
    (h_safe : jasminCTSafe c = true)
    (params results : List Located) (fname : String)
    (x86 : X86Prog)
    (h_compile : Jasminc.compilesTo
                   (toJasminProg fname params results c) x86) :
    x86.isCT :=
  rustcmd_ct_implies_x86_ct (secrets := Labeling.toSecretSet label)
    c (wellLabeled_implies_isCT_LowCT' leaves label c h_lab)
    h_safe params results fname x86 h_compile

/-! ## §6. Smoke

A trivial example: `let x = 0; let y = 0; if x then y := 1` with
`x : Public`, `y : Secret`. The `RIfNz` guard `x` is public, so the
program is `wellLabeled`. -/

namespace Smoke

/-- Sample labeling. -/
def labelXYpub : Labeling := fun n =>
  if n = "x" then .Public
  else if n = "y" then .Secret
  else .Public

/-- Sample CT-leaves whitelist (empty — no calls in the smoke). -/
def leavesNone : CTLeaves := fun _ => false

/-- The sample program: `RScalarSet x 0; RScalarSet y 0; RIfNz x skip skip`. -/
def smokeProg : LowCT :=
  .RSeq (.RScalarSet "x" 0)
    (.RSeq (.RScalarSet "y" 0)
      (.RIfNz "x" .RSkip .RSkip))

/-- Smoke: the sample is `wellLabeled` under `labelXYpub`. -/
example : wellLabeled leavesNone labelXYpub smokeProg = true := by decide

/-- Smoke: a flipped labeling (`x : Secret`) rejects the same program. -/
def labelXSecret : Labeling := fun _ => .Secret

example : wellLabeled leavesNone labelXSecret smokeProg = false := by decide

end Smoke

end CatCrypt.Crypto.SecureCompilation.LowCTLabeled
