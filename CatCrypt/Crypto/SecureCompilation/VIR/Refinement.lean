/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-!
# A canonical refinement relation for Com-lowering correctness

This module gives a single named relation for the lowering-correctness facts
the THIR front already proves: a target program/denotation **refines** a source
when the two agree on every input. For our semantics-preserving lowerings the
agreement is an equality (extensional denotation-equality), so `Refines` is an
equivalence on the denotation carrier, with reflexivity, transitivity, and a
function-composition congruence that chains front → Com → backend stages.

## Carrier

The shared carrier is a denotation **function** `α → β`: every lowering lemma in
the THIR front equates two such functions (a `Com.denote`, a `JForProg.denote`,
or an `n`-fold accumulator map). `Refines src tgt` reads "`tgt` denotes exactly
as `src` on all inputs".

## Relation to upstream Veir (PR #703 / #704)

This anticipates opencompl/veir's `Interpreter/Refinement/Basic.lean`
(the relation) and `Interpreter/Refinement/Lemmas.lean` (its reflexivity and
transitivity), where module/function refinement is the interface our
Com-lowering pipeline reports against. The relation here is intended to be
swapped for the upstream one on sync: the existing proved lowering lemmas are
restated below as `Refines` corollaries, so adopting the upstream relation is a
mechanical rename of `Refines`/`ComRefines` and their refl/trans lemmas rather
than a re-derivation of the lowering soundness.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Refinement

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)

/-! ## 1. The refinement relation (upstream `Refinement/Basic` shape) -/

/-- `Refines src tgt` holds when the target denotation function agrees with the
    source on every input. For a semantics-preserving lowering the target
    program's denotation `tgt` equals the source denotation `src` pointwise, so
    refinement here is denotation-equality. The argument order mirrors the
    lowering direction (`src` is the higher-level program, `tgt` the lowered
    one). -/
def Refines {α β : Type _} (src tgt : α → β) : Prop :=
  ∀ x, tgt x = src x

/-! ## 2. Reflexivity / transitivity / congruence (upstream `Refinement/Lemmas`) -/

/-- Reflexivity: every denotation refines itself. -/
@[refl] theorem Refines.refl {α β : Type _} (x : α → β) : Refines x x :=
  fun _ => rfl

/-- Transitivity: refinement composes through an intermediate denotation. -/
theorem Refines.trans {α β : Type _} {a b c : α → β}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c :=
  fun x => (hbc x).trans (hab x)

/-- Congruence under post-composition: a refinement is preserved by applying the
    same continuation `k` to both denotations. The chaining lemma for a
    front → Com → backend pipeline whose stages share an output transform. -/
theorem Refines.congr_postcomp {α β γ : Type _} {src tgt : α → β}
    (k : β → γ) (h : Refines src tgt) : Refines (fun x => k (src x)) (fun x => k (tgt x)) :=
  fun x => congrArg k (h x)

/-- Congruence under pre-composition: a refinement is preserved by feeding both
    denotations the same input transform `j`. -/
theorem Refines.congr_precomp {α α' β : Type _} {src tgt : α → β}
    (j : α' → α) (h : Refines src tgt) : Refines (fun x => src (j x)) (fun x => tgt (j x)) :=
  fun x => h (j x)

/-! ## 3. The existing proved lowering lemmas, restated as `Refines`

Each corollary below is the matching already-proved denotation-equality, viewed
through `Refines`. No lowering soundness is re-derived: every proof is the
existing lemma under `Refines`/`ComRefines` unfolded. -/

open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-- The generic THIR → jasmin `Com` lowering refines (in fact equals) the source
    on every valuation. `Refines` form of `lowerThir_denote`. -/
theorem lowerThir_refines {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com thirDialect Γ t) :
    Refines c.denote (lowerThir c).denote :=
  fun V => ThirDialect.lowerThir_denote c V

/-- The bounded-FOR lowering refines the THIR loop's `n`-fold denotation, on
    every initial accumulator. `Refines` form of `ThirDialect.toJForProg_denote`. -/
theorem toJForProg_refines {accTy : JasminTy} (p : ThirDialect.ThirForProg accTy) :
    Refines p.denote p.toJForProg.denote :=
  fun init => ThirDialect.toJForProg_denote p init

/-- The treehash CALL-in-LOOP front spine refines the `N`-fold of the `Th` leaf
    spec, on every initial node. `Refines` form of `treehashChain_via_thirDialect`. -/
theorem treehashChain_refines (n : Nat) :
    Refines (fun init => (List.range n).foldl (fun node _ => treehashLeafSpec node) init)
      (treehashChain n).toJForProg.denote :=
  fun init => treehashChain_via_thirDialect n init

/-- The ARX round schedule front spine refines the `n`-fold of the ARX round
    step, on every initial accumulator. `Refines` form of
    `foldRound_via_thirDialect`. -/
theorem foldRound_refines (n : Nat) :
    Refines (fun init => (List.range n).foldl (fun acc _ => foldRoundStep acc) init)
      (foldRoundLoop n).toJForProg.denote :=
  fun init => foldRound_via_thirDialect n init

end CatCrypt.Crypto.SecureCompilation.VIR.Refinement
