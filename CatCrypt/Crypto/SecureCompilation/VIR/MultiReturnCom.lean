/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# Multi-return VIR (D2 skeleton)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`Com d Γ t` in `Core.lean` is single-return: a program denotes to one value of
type `⟦t⟧`. That single-return shape forces shared work across multiple
"final" outputs to land in *separate* `func.func` boundaries downstream, which
is the CSE trap documented in writeup §5.5: LLVM cannot DCE shared work across
function boundaries, so a `CProg` that wants to emit two correlated values
ends up doing the work twice.

This file introduces the structural skeleton of a multi-return VIR
(`MultiReturnCom d Γ ts`) which returns a heterogeneous vector of variables
indexed by a `List d.Ty`. The single-return `Com d Γ t` is recovered as the
`ts = [t]` special case, and the equivalence is proved here.

Strategy: **(A) side-by-side**. We do not modify `Core.lean`; the existing
single-return `Com` keeps working. New code can opt into `MultiReturnCom` when
it needs to emit multiple correlated outputs from a single SSA region.

Follow-ups (D2.1 – D2.4) are listed at the bottom of this file.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var)

/-! ## 1. Denotation of a list of dialect types -/

/-- A list of dialect types denotes to an `HVector` of Lean types — one entry
    per element. This is what a multi-return program produces. -/
abbrev ListDenote {τ : Type _} [TyDenote τ] (ts : List τ) : Type :=
  HVector (fun t => ⟦t⟧) ts

/-! ## 2. The multi-return Com -/

/-- A program in A-normal form returning a tuple of variables.

    Mirrors `Com d Γ t` from `Core.lean` but the `ret` case carries an
    `HVector (Var Γ) ts` instead of a single variable. Setting `ts = [t]`
    recovers the existing single-return shape; setting `ts = []` gives a
    "void" program that runs side-effects (none in our pure setting) and
    returns `()`; setting `ts = [t₁, t₂, …]` is the new shared-work case. -/
inductive MultiReturnCom (d : Dialect) [DialectSignature d] :
    Ctxt d → List d.Ty → Type _ where
  /-- Return a heterogeneous vector of variables. -/
  | ret {Γ : Ctxt d} {ts : List d.Ty} (vs : HVector (fun ty => Var Γ ty) ts) :
      MultiReturnCom d Γ ts
  /-- Let-bind an expression and continue with its result in scope. The body
      may itself return any number of outputs. -/
  | var {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty}
      (e : Expr d Γ t) (body : MultiReturnCom d (t :: Γ) ts) :
      MultiReturnCom d Γ ts

namespace MultiReturnCom

/-! ## 3. Denotation -/

/-- Resolve an `HVector` of variables against a valuation, producing a
    matching `HVector` of values. (Same shape as `Expr.lookupArgs` from
    `Core.lean`; we duplicate rather than re-export to keep this file
    structurally independent.) -/
def lookupVars {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d} :
    {ts : List d.Ty} → HVector (fun ty => Var Γ ty) ts →
    Ctxt.Valuation Γ → ListDenote ts
  | [], .nil, _ => .nil
  | _ :: _, .cons v rest, V => .cons (v.lookup V) (lookupVars rest V)

/-- Denotation of a multi-return program. -/
def denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d] :
    {Γ : Ctxt d} → {ts : List d.Ty} →
    MultiReturnCom d Γ ts → Ctxt.Valuation Γ → ListDenote ts
  | _, _, .ret vs, V => lookupVars vs V
  | _, _, .var e body, V => body.denote (V.extend (e.denote V))

end MultiReturnCom

/-! ## 4. Single-return is `ts = [t]` -/

/-- Embed a single-return `Com d Γ t` into the multi-return view. -/
def Com.toMulti {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → MultiReturnCom d Γ [t]
  | _, _, .ret v        => .ret (.cons v .nil)
  | _, _, .var e body   => .var e body.toMulti

/-- Project a multi-return `MultiReturnCom d Γ [t]` back to a single-return
    `Com d Γ t`. -/
def MultiReturnCom.toSingle {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → MultiReturnCom d Γ [t] → Com d Γ t
  | _, _, .ret (.cons v .nil) => .ret v
  | _, _, .var e body         => .var e body.toSingle

/-! ## 5. Equivalence: `Com d Γ t ≃ MultiReturnCom d Γ [t]` -/

/-- Round-trip: `toSingle ∘ toMulti = id`. -/
theorem Com.toMulti_toSingle {d : Dialect} [DialectSignature d]
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    c.toMulti.toSingle = c := by
  induction c with
  | ret _      => simp [Com.toMulti, MultiReturnCom.toSingle]
  | var _ _ ih => simp [Com.toMulti, MultiReturnCom.toSingle, ih]

/-- Round-trip: `toMulti ∘ toSingle = id`. We pattern-match `m` directly and
    recurse on the body in the `var` case (`body : MultiReturnCom d (t :: Γ)
    [t']` still has return list `[t']`, so the recursive call type-checks). -/
def MultiReturnCom.toSingle_toMulti {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → (m : MultiReturnCom d Γ [t]) →
      m.toSingle.toMulti = m
  | _, _, .ret (.cons _ .nil) => by
      simp [MultiReturnCom.toSingle, Com.toMulti]
  | _, _, .var _ body         => by
      simp [MultiReturnCom.toSingle, Com.toMulti,
            MultiReturnCom.toSingle_toMulti body]

/-- Denotation is preserved by the embedding (single-return semantics agrees
    with the head-of-tuple of the multi-return semantics). -/
theorem Com.denote_toMulti {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    c.toMulti.denote V = .cons (c.denote V) .nil := by
  induction c with
  | ret v          =>
      simp [Com.toMulti, MultiReturnCom.denote, MultiReturnCom.lookupVars,
            Com.denote]
  | var e body ih  =>
      simp [Com.toMulti, MultiReturnCom.denote, Com.denote, ih]

/-! ## 6. Smoke-test: a concrete two-output program denotes correctly -/

namespace SmokeTest

/-- A trivial dialect with no operations and a one-element type alphabet. -/
inductive Op : Type where
inductive Ty : Type where
  | bit : Ty

def D : Dialect := { Op := Op, Ty := Ty }

instance : TyDenote D.Ty where
  denote
  | .bit => Bool

instance : DialectSignature D where
  sig op := nomatch op
  ret op := nomatch op

instance : DialectDenote D where
  denote op := nomatch op

/-- A two-input context. -/
def Γ : Ctxt D := [Ty.bit, Ty.bit]

/-- A program that returns the pair `(x₀, x₁)` — i.e. both inputs, in order
    of de Bruijn index. With single-return `Com`, this would require two
    separate functions; with `MultiReturnCom`, one program suffices. -/
def pair : MultiReturnCom D Γ [Ty.bit, Ty.bit] :=
  .ret (.cons Ctxt.Var.here (.cons (Ctxt.Var.there Ctxt.Var.here) .nil))

/-- The smoke test: `pair` denotes to its inputs, in order. -/
theorem pair_denote (a b : Bool) :
    pair.denote (.cons a (.cons b .nil)) = .cons a (.cons b .nil) := by
  rfl

end SmokeTest

end CatCrypt.Crypto.SecureCompilation.VIR

/-!
## Follow-ups (D2.1 – D2.4)

This file is the structural skeleton. The remaining work is:

* **D2.1 — `CryptoToVIR.lean`**: extend with a `toMultiReturnCom` translation
  for `CProg`s that should produce multiple outputs. Currently impossible
  because `CProg` itself is also single-return; that may need a parallel
  `MultiReturnCProg` (or a `List CProg` glue layer) before this file's
  multi-return target becomes reachable from the source language.

* **D2.2 ✅ AUDITED**: `CatCryptDialect.lean`'s 24 ops
  (`constBit`/`xor`/`and`/`or`/`not`/`mkPair`/`fst`/`snd`/`inl`/`inr`/
  `bvConst`/`bvXor`/`bvAnd`/`bvOr`/`bvNot`/`bvAdd`/`bvSub`/`bvMul`/
  `bvEq`/`bvShiftL`/`bvShiftR`/`ite`/`memrefZero`/`memrefSet`/
  `memrefGet`/`extCall`) are all **single-return** at the op level.
  No `bvAdd64`/`bvAdc` (multi-output ALU ops are bundled at the
  CryptoSSA-source level via `pair` types and projected after the
  call, not exposed as multi-return Expr ops). The CSE trap is at
  the *program*-level `func.func` boundary, not the *op* level —
  `MultiReturnCom` (this file) addresses the program-level concern,
  and no `DialectSignature.ret : d.Op → List d.Ty` change is needed.

* **D2.3 ✅ LANDED** (commit `6fcea0c6`, 2026-04-30):
  `Print.lean` extended with `MultiReturnCom.printModule` emitting
  `func.func @f() -> (T1, T2)` signatures with multi-value return
  statements. Three new defs: `lookupNames`, `printBody`, `printModule`.

* **D2.4 — `X25519EmitMLIR.lean`**: retrofit to use `MultiReturnCom` where
  the CSE trap currently kicks in (the writeup §5.5 motivating example).
  Concretely: identify which emitted programs share work across separate
  current `func.func`s and merge them into a single multi-return program.
-/
