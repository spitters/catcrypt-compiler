/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# Borrow Checker and Frame Theorems for LowCT

Port of `AUCurves/src/Bedrock/SafeRustBorrowCheck.v`.

## Contents

* §1  `borrowOk`: static alias checker (one `decide` per program)
* §2  `destsOf`: write-set of a program
* §3  `seqFrame`: if `loc ∉ destsOf c`, then `c` preserves `locatedLookup rs loc`
* §4  `callFrame`: convenience wrappers

## Design note

`seqFrame` is proved by induction on the `RustExec` derivation, matching
every constructor.  The `cloneCall` case is closed cleanly by including
`cloneVar` in `destsOf`: the precondition `loc.locVar ∉ destsOf c` then
directly yields both `loc.locVar ≠ cloneVar` and `loc.locVar ≠ dest.locVar`,
making the three-step chain `RemoveTower → inner ih → SetTower` trivial.

**0 admits, all goals closed.**
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

open List

/-! ## §1  Borrow checker -/

-- RCloneCall : cloneVar cloneTy oldDest innerF dest args
/-- `borrowOk c` holds iff every `RCall` (and the inner call of every
    `RCloneCall`) has its destination variable distinct from all arguments.

    For `RCallSwap f dest1 dest2 args`, the borrow check additionally
    requires `dest1.locVar ≠ dest2.locVar` (the two destinations don't
    alias each other) and that neither destination appears in `args`. -/
def borrowOk : LowCT → Bool :=
  LowCT.fold (seqLike := (· && ·)) (wrap1 := id)
    (leaf := borrowOkLeaf)
where
  /-- Per-leaf borrow-check condition for the *non-recursive*
      constructors; the eight
      recursive constructors are handled structurally by `LowCT.fold`
      (`seqLike = (· && ·)` for `RSeq`/`RIfNz`/`RFnDef`, `wrap1 = id` for the
      single-child wrappers `RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/
      `RBlock`, since each merely lifts to its body).  A new *leaf*
      constructor only needs an arm here. -/
  borrowOkLeaf : LowCT → Bool
  | .RSkip                      => true
  | .RScalarSet _ _             => true
  | .RCall _ dest args          => !callAliases dest args
  | .RCallSwap _ dest1 dest2 args =>
      (dest1.locVar != dest2.locVar)
        && !callAliases dest1 args
        && !callAliases dest2 args
  | .RCloneCall _ _ _ _ dest args => !callAliases dest args
  | .RLimbStore _ _ _           => true
  -- Runtime-valued limb store.  Same as `RLimbStore` — writes
  -- one limb of `loc`, reads scalar slots in `e`; no aliasing concern.
  | .RLimbStoreExpr _ _ _       => true
  -- `RCallN`: dests must be mutually distinct and disjoint from args.  The
  -- distinctness is over VARIABLE NAMES, as in `RCallSwap` above: a tower slot
  -- is keyed by `locVar` alone, so `[⟨"x", TU64⟩, ⟨"x", TFp⟩]` is `Nodup` as a
  -- list of `Located` while both writes land on `x` and the second shadows the
  -- first.
  | .RCallN _ dests args        =>
      (dests.map (·.locVar)).Nodup && dests.all (fun d => !callAliases d args)
  -- `RSelect`: dst, src0, src1 base vars distinct (for the simple
  -- discipline; cmov-with-aliased-src is a future refinement).
  | .RSelect dst _ src0 src1    =>
      (dst.locVar != src0.locVar) && (dst.locVar != src1.locVar)
  -- Assertion has no destination, no args.
  | .RAssert _                  => true
  -- Function-call same shape as RCallN, distinctness over names.
  | .RFnCall _ dests args       =>
      (dests.map (·.locVar)).Nodup && dests.all (fun d => !callAliases d args)
  -- Tuple component load — single destination, no aliasing concern.
  | .RTupleLoad dst src _       => dst.locVar != src.locVar
  -- Runtime array load/store + scalar expression assign.
  -- Conservative defaults: array load/store require dst.locVar ≠ src.locVar
  -- (the scalar `idxVar` is read-only, no aliasing concern with tower locs).
  -- RScalarSetExpr is always borrowOk (writes only a scalar; reads scalars).
  | .RArrStore arr _ src        => arr.locVar != src.locVar
  | .RArrLoad dst src _         => dst.locVar != src.locVar
  -- Literal-index variants — same constraint as their
  -- dynamic-index siblings (dst/arr distinct from src).  No idxVar to consider.
  | .RArrStoreLit arr _ src     => arr.locVar != src.locVar
  | .RArrLoadLit dst src _      => dst.locVar != src.locVar
  | .RScalarSetExpr _ _         => true
  -- Dst-threaded leaf call.  Same alias
  -- discipline as `RCall`: dst must not appear in args (the kernel
  -- reads its own threaded dst from the first arg slot then writes;
  -- the borrow checker treats dst as a write-only output for the
  -- purposes of the no-alias check).
  | .RCallDstThreaded _ dst args => !callAliases dst args
  -- Recursive constructors are dispatched by `LowCT.fold` (seqLike/wrap1)
  -- and never reach `borrowOkLeaf`; these arms keep the leaf total.
  | .RSeq _ _                   => true
  | .RLetZero _ _ _             => true
  | .RLetU64Zero _ _            => true
  | .RIfNz _ _ _                => true
  | .RWhileNz _ _               => true
  | .RFor _ _ _                 => true
  | .RForRuntime _ _ _          => true
  | .RBlock _                   => true
  | .RFnDef _ _ _ _ _           => true

/-! ## §2  Write-set -/

/-- `destsOf c` is the list of base variable names that `c` may write. -/
def destsOf : LowCT → List String
  | .RSkip                       => []
  | .RSeq c1 c2                  => destsOf c1 ++ destsOf c2
  | .RLetZero x _ body           => x :: destsOf body
  | .RLetU64Zero _ body          => destsOf body
  | .RScalarSet _ _              => []
  | .RCall _ dest _              => [dest.locVar]
  | .RCallSwap _ dest1 dest2 _   => [dest1.locVar, dest2.locVar]
  | .RCloneCall cloneVar _ _ _ dest _   => [cloneVar, dest.locVar]
  | .RIfNz _ ct cf               => destsOf ct ++ destsOf cf
  | .RWhileNz _ body             => destsOf body
  | .RFor _ _ body               => destsOf body
  | .RForRuntime _ _ body        => destsOf body
  | .RLimbStore loc _ _          => [loc.locVar]
  | .RLimbStoreExpr loc _ _      => [loc.locVar]
  | .RCallN _ dests _            => dests.map (·.locVar)
  | .RSelect dst _ _ _           => [dst.locVar]
  | .RAssert _                   => []
  | .RBlock body                 => destsOf body
  -- Function-def's writes are body ∪ cont (under static analysis).
  | .RFnDef _ _ _ body cont      => destsOf body ++ destsOf cont
  | .RFnCall _ dests _           => dests.map (·.locVar)
  -- Tuple component load — single destination.
  | .RTupleLoad dst _ _          => [dst.locVar]
  -- Runtime array load/store + scalar expression assign.
  | .RArrStore arr _ _           => [arr.locVar]  -- mutates the array variable
  | .RArrLoad dst _ _            => [dst.locVar]
  -- Literal-index variants — same dst as their siblings.
  | .RArrStoreLit arr _ _        => [arr.locVar]
  | .RArrLoadLit dst _ _         => [dst.locVar]
  | .RScalarSetExpr _ _          => []           -- writes a scalar, not in destsOf
  -- Dst-threaded leaf call writes its threaded dst.
  | .RCallDstThreaded _ dst _    => [dst.locVar]

/-! ## §3  callAliases ↔ ∉ lemma -/

/-- If `callAliases dest args = false`, then every arg has a different
    base variable from `dest`. -/
lemma callAliases_false_ne (dest : Located) (args : List Located)
    (h : callAliases dest args = false) (arg : Located) (hmem : arg ∈ args) :
    dest.locVar ≠ arg.locVar := by
  intro heq
  have htrue : callAliases dest args = true := by
    simp only [callAliases, List.any_eq_true]
    exact ⟨arg, hmem, by simp [heq]⟩
  simp [htrue] at h

/-! ## §4  seqFrame -/

/-- **seqFrame**: if `loc.locVar ∉ destsOf c`, then any execution of `c`
    preserves `locatedLookup rs loc`.

    A single structural induction, proved once here, in place of
    per-function separation-logic frame proofs. -/
theorem seqFrame (N : Nat) (leafSpec : LeafSpec)
    (c : LowCT) (rs rs' : RustState) (loc : Located)
    (hExec : RustExec N leafSpec c rs rs')
    (hNotIn : loc.locVar ∉ destsOf c) :
    locatedLookup rs' loc = locatedLookup rs loc := by
  induction hExec with

  | skip _ => rfl

  | seq _ _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    rw [ih2 hNotIn.2, ih1 hNotIn.1]

  | letZero x _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_cons, not_or] at hNotIn
    rw [ih hNotIn.2]
    exact locatedLookup_rsSetTower_other _ _ _ _ (Ne.symm hNotIn.1)

  | letU64Zero _ _ _ _ _ ih =>
    simp only [destsOf] at hNotIn
    rw [ih hNotIn]
    exact locatedLookup_rsSetScalar _ _ _ _

  | scalarSet _ _ _ =>
    exact locatedLookup_rsSetScalar _ _ _ _

  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    exact ih hNotIn.1

  | ifFalse _ _ _ _ _ _ _ ih =>
    simp only [destsOf, List.mem_append, not_or] at hNotIn
    exact ih hNotIn.2

  | whileFalse _ _ _ _ => rfl

  -- whileTrue: 10 constructor args (e body rs r1 rs' v h1 h2 hBody hWhile) + 2 IHs
  | whileTrue _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf] at hNotIn
    rw [ih2 hNotIn, ih1 hNotIn]

  | forZero _ _ _ => rfl

  -- forSucc: x n body rs r1 rs' + 2 IHs (one for the inner RFor, one for the body run).
  -- Setting the scalar counter doesn't touch the tower heap, so the body run preserves
  -- locatedLookup; the inner RFor preservation follows by IH.
  | forSucc _ n _ _ _ _ _ _ ih1 ih2 =>
    simp only [destsOf] at hNotIn
    -- After ih2, the body run preserves loc; before that, scalarSet preserves loc;
    -- before that, ih1 (the inner RFor) preserves loc.
    rw [ih2 hNotIn]
    rw [locatedLookup_rsSetScalar]
    rw [ih1 hNotIn]

  -- forRuntime: delegates to the inner `RFor (bound.evalState rs)` derivation;
  -- write-set is the same (destsOf mirrors RFor), so the inner IH closes it.
  | forRuntime _ _ _ _ _ _ ih =>
    simp only [destsOf] at hNotIn ⊢
    exact ih hNotIn

  | call _ dest _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  | callDstThreaded _ dst _ _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  | cloneCall cloneVar cloneTy oldDest innerF dest args rs0 rsClone rsInner hClone _ ih =>
    simp only [destsOf, List.mem_cons, List.mem_singleton, not_or] at hNotIn
    obtain ⟨hne_clone, hne_dest⟩ := hNotIn
    have hne : cloneVar ≠ loc.locVar := Ne.symm hne_clone
    have hDestsRCall : destsOf (.RCall innerF dest args) = [dest.locVar] := rfl
    have hInner : loc.locVar ∉ destsOf (.RCall innerF dest args) := by
      rw [hDestsRCall]; simp [hne_dest]
    -- two-step chain: inner call → initial SetTower (no Remove)
    exact (ih hInner).trans (hClone ▸ locatedLookup_rsSetTower_other _ _ _ _ hne)

  | callSwap f dest1 dest2 args rs0 rs1 rs2 _h1 _h2 ih1 ih2 =>
    simp only [destsOf, List.mem_cons, List.mem_singleton, not_or] at hNotIn
    obtain ⟨hne_dest1, hne_dest2⟩ := hNotIn
    have hDests1 : destsOf (.RCall f dest1 args) = [dest1.locVar] := rfl
    have hDests2 : destsOf (.RCall f dest2 args) = [dest2.locVar] := rfl
    have hIn1 : loc.locVar ∉ destsOf (.RCall f dest1 args) := by
      rw [hDests1]; simp [hne_dest1]
    have hIn2 : loc.locVar ∉ destsOf (.RCall f dest2 args) := by
      rw [hDests2]; simp [hne_dest2]
    exact (ih2 hIn2).trans (ih1 hIn1)

  | limbStore _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Runtime-valued limb store — same frame as `limbStore`.
  | limbStoreExpr _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- The N-output call writes exactly `dests`; `destsOf` is that list
  -- of names, so the fold's frame lemma applies directly.
  | callN f dests args rs argList _ _ _ =>
    simp only [destsOf] at hNotIn
    exact locatedLookup_callNUpdate_other leafSpec f (args.map (·.locDst)) argList
      dests 0 rs loc hNotIn

  -- selectFalse: dst gets updated, others untouched.
  | selectFalse dst _ _ _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- selectTrue: same as selectFalse.
  | selectTrue dst _ _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf] at hNotIn
    rw [List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Assertion is a state no-op.
  | assert _ _ => rfl

  -- Scope wraps body identity-fully; lift via the body IH.
  | block _ _ _ _ ih =>
    simp only [destsOf] at hNotIn
    exact ih hNotIn

  -- Tuple load writes to dst → use
  -- locatedUpdate_other to preserve other locations' lookups.
  | tupleLoad dst _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)

  -- Array store/load update a single dst → use locatedUpdate_other.
  | arrStore arr _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  | arrLoad dst _ _ _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  -- Literal-index array store/load — same frame proof.
  | arrStoreLit arr _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  | arrLoadLit dst _ _ _ _ _ _ _ =>
    simp only [destsOf, List.mem_singleton] at hNotIn
    exact locatedUpdate_other _ _ _ _ (Ne.symm hNotIn)
  | scalarSetExpr _ _ _ =>
    -- RScalarSetExpr writes to rsScalar only (not rsTower); leaves tower lookups intact.
    exact locatedLookup_rsSetScalar _ _ _ _

/-! ## §5  Call frame theorems -/

/-- **borrowOkCallFrame**: for a borrow-checked `RCall`, every argument
    variable is preserved by the call. -/
theorem borrowOkCallFrame (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState)
    (hBok : borrowOk (.RCall f dest args) = true)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (arg : Located) (hArg : arg ∈ args) :
    locatedLookup rs' arg = locatedLookup rs arg := by
  have hca : callAliases dest args = false := by
    simpa [borrowOk, LowCT.fold, borrowOk.borrowOkLeaf] using hBok
  apply seqFrame N leafSpec _ _ _ _ hExec
  simp only [destsOf]
  rw [List.mem_singleton]
  exact Ne.symm (callAliases_false_ne dest args hca arg hArg)

/-- **callFrameNonDest**: any variable whose base name differs from `dest`
    is preserved by an `RCall`, regardless of `borrowOk`. -/
theorem callFrameNonDest (N : Nat) (leafSpec : LeafSpec)
    (f : String) (dest : Located) (args : List Located)
    (rs rs' : RustState) (loc : Located)
    (hExec : RustExec N leafSpec (.RCall f dest args) rs rs')
    (hne : dest.locVar ≠ loc.locVar) :
    locatedLookup rs' loc = locatedLookup rs loc := by
  apply seqFrame N leafSpec _ _ _ _ hExec
  simp only [destsOf]
  rw [List.mem_singleton]
  exact Ne.symm hne

/-! ## §6  seqFrame corollaries -/

lemma borrowOk_seq_l {c1 c2 : LowCT} (h : borrowOk (.RSeq c1 c2) = true) :
    borrowOk c1 = true := by simp [borrowOk] at h; exact h.1

lemma borrowOk_seq_r {c1 c2 : LowCT} (h : borrowOk (.RSeq c1 c2) = true) :
    borrowOk c2 = true := by simp [borrowOk] at h; exact h.2

/-! ## §7  RCallSwap smoke tests

Sanity-check `borrowOk` and `destsOf` on the new 2-destination call. -/

/-- Two distinct destinations, neither in args: borrow-checks. -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        [{ locVar := "swap", locSrc := .TU64 }]) = true := by
  decide

/-- Same destination twice: borrow-check fails (`dest1 = dest2`). -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x2", locSrc := .TFp25519 }
        [{ locVar := "swap", locSrc := .TU64 }]) = false := by
  decide

/-- Destination aliases an arg: borrow-check fails. -/
example :
    borrowOk
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        [{ locVar := "x2", locSrc := .TFp25519 }]) = false := by
  decide

/-- `destsOf` on `RCallSwap` lists both destination variables. -/
example :
    destsOf
      (.RCallSwap "cswap"
        { locVar := "x2", locSrc := .TFp25519 }
        { locVar := "x3", locSrc := .TFp25519 }
        []) = ["x2", "x3"] := by
  decide

end CatCrypt.Crypto.Jasmin.LowCT
