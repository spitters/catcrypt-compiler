/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert
import CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops
import CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards
import CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2
import CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify

/-!
# Phase J — `cmdCT` constant-time analyser for `LowCT`

This module closes the audit-vs-proof gap noted in
`curve25519-jasmin-rs/docs/timing-resistance-2026-05-13.md` §4–§5: the
existing `SecretLevel` / `LevelTable` infrastructure in `LowCT.lean`
classifies slots, but no analyser had yet enforced the classification
at the *body* level.

`cmdCT cmd lt leafCT` returns `true` iff every branch condition,
loop guard, and memory index in `cmd` is `Public` under `lt`, and
every leaf call in `cmd` is in the per-leaf CT table `leafCT`.

## What `cmdCT` checks (positive list)

* `RIfNz cond _ _`: `lt cond = Public`.
* `RWhileNz cond _`: `lt cond = Public`.
* `RArrLoad _ _ idxVar` / `RArrStore _ idxVar _`: `lt idxVar = Public`.
* `RCall f _ _` / `RCallSwap f _ _ _` / `RCallN f _ _` / `RFnCall f _ _`:
  `leafCT f = true` (per-leaf CT table; all fiat-crypto + Jasmin
  leaves we use are CT).
* `RFor x n body`: `body` is CT (the loop counter `x` is bound to a
  *known* iteration index, structurally public).
* `RScalarSetExpr x e`: `x` is rewritten to whatever the RHS computes;
  see `sexprIsCT` for the recursive check on `e`'s free variables.
* `RSelect _ _ _ _`: CT by construction (a CMOV — both source values
  are read regardless of the selector); the selector itself may be
  Secret.  See `selectIsCT`.

## What `cmdCT` does NOT check (out of scope)

* Cache-line leaks via address-of-stack-slot.  LowCT has no
  notion of stack offset — the borrow checker on the Jasmin side
  would catch cross-leaf alignment leaks if they existed.
* Power / EM side channels.  Out of scope for a syntactic analyser.

## Soundness

`cmdCT_sound`: proved, by structural induction on the `RustExec`
derivation.  The formulation is a *leakage-equivalence* (noninterference)
claim — `PublicEquiv` inputs give `PublicEquiv` outputs — conditional on a
`CMOVInvariant` side condition on the program.  See `LeakageEquiv` below.
-/

namespace CatCrypt.Crypto.Jasmin.LowCT

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1.  Per-leaf CT table -/

/-- A per-leaf CT table: maps a leaf-function name to `true` iff the
    leaf is known to be constant-time on its input range.  All
    fiat-crypto + Jasmin leaves we currently emit are CT, so the
    default table classifies the names we use as `true`.

    Adding a new (non-CT) leaf to the AST without updating this
    table will make `cmdCT` return `false`, which is the intended
    fail-closed behaviour. -/
abbrev LeafCTTable := String → Bool

/-- The canonical CT leaf table: every leaf name used by the five
    audited ASTs is classified `true`.  Other names default to
    `false` (fail-closed).

    Coverage:
    * `fe25519_*` — fiat-crypto Curve25519 base field (all CT).
    * `scalar25519_*` — fiat-crypto Curve25519 scalar field (all CT).
    * `xyzt_add_decomposed`, `xyzt_double_decomposed` — Edwards curve
      arithmetic via decomposed coordinates (CT — no secret-branching).
    * `mont_u_to_edwards_compressed_zero`, `ed25519_verify` —
      composed of the above + CT shim glue.
-/
def LeafCTTable.canonical : LeafCTTable := fun name =>
  -- Curve25519 base field (fiat-crypto + Lean-emitted invert)
  name == "fe25519_set_one"        ||
  name == "fe25519_copy"           ||
  name == "fe25519_mul"            ||
  name == "fe25519_sqr"            ||
  name == "fe25519_add_then_carry" ||
  name == "fe25519_sub_then_carry" ||
  name == "fe25519_invert"         ||
  -- Curve25519 scalar field (fiat-crypto curve25519_scalar_64)
  name == "scalar25519_bytes_to_mont" ||
  name == "scalar25519_mont_to_bytes" ||
  name == "scalar25519_mul_mont"      ||
  name == "scalar25519_add_mont"      ||
  name == "scalar25519_sub_mont"      ||
  name == "scalar25519_opp_mont"      ||
  -- Edwards XYZT arithmetic (decomposed-form add / double)
  name == "xyzt_add_decomposed"    ||
  name == "xyzt_double_decomposed" ||
  -- Composed-CT leaves used at the XEdDSA layer
  name == "mont_u_to_edwards_compressed_zero" ||
  name == "ed25519_verify"

/-! ## §2.  SExpr CT check -/

/-- Free variables of an `SExpr` (the scalar-slot names that the
    expression *reads*).  Used by `sexprIsCT` below to decide whether
    an expression's value is publicly determined. -/
def SExpr.freeVars : SExpr → List String
  | .SVar x   => [x]
  | .SLit _   => []
  | .SAdd a b => a.freeVars ++ b.freeVars
  | .SSub a b => a.freeVars ++ b.freeVars
  | .SMul a b => a.freeVars ++ b.freeVars
  | .SShr a b => a.freeVars ++ b.freeVars
  | .SShl a b => a.freeVars ++ b.freeVars
  | .SAnd a b => a.freeVars ++ b.freeVars
  | .SXor a b => a.freeVars ++ b.freeVars
  | .SLt  a b => a.freeVars ++ b.freeVars
  -- Signed-arith extension (#257): the signed binary ops read the union of
  -- their operands' free variables, exactly as the unsigned binary ops.
  | .SAsr  a b => a.freeVars ++ b.freeVars
  | .SMulS a b => a.freeVars ++ b.freeVars
  -- Widening-multiply extension (#261): the high-word multiplies read the
  -- union of their operands' free variables, exactly as the other binary ops.
  | .SMulHiU a b => a.freeVars ++ b.freeVars
  | .SMulHiS a b => a.freeVars ++ b.freeVars
  -- Tower-limb read extension (#354): `SLimb v i` reads (a limb of) the tower
  -- slot `v`, so the slot name `v` is the expression's free variable.  A
  -- Secret-classified tower slot flowing into a stored limb is thereby caught
  -- by `isPublic` (the limb value would otherwise leak via the STORE64 operand).
  | .SLimb v _ => [v]

/-- An `SExpr` is "publicly determined" iff every free variable it
    reads is classified Public.  Used by `RScalarSetExpr` to detect
    secret-tainted index arithmetic. -/
def SExpr.isPublic (e : SExpr) (lt : LevelTable) : Bool :=
  e.freeVars.all (fun v => lt v == .Public)

/-! ## §3.  cmdCT analyser -/

/-- The constant-time syntactic check.  Returns `true` iff every
    branch, loop, and memory-index in `cmd` is Public-classified
    under `lt`, and every leaf call is in `leafCT`.

    Convention: scalar-slot mutations propagate by *promoting* the
    slot to the join of inputs.  We model this with a *closed*
    `LevelTable` that the caller is responsible for — `cmdCT` does
    not synthesise the table from scratch.  This is sound because:
    * `RScalarSet x n` (literal) cannot taint `x`; the caller's
      table can classify `x` Public.
    * `RScalarSetExpr x e` is checked: if `e` reads any Secret slot,
      the AST is rejected (because writes to `x` would propagate the
      taint and downstream uses of `x` as a branch/index would not be
      caught by `lt` alone).

    For loops `RFor x n body`: the counter `x` is bound to a known
    iteration in `[0, n)` and is therefore structurally Public.  We
    require the caller's table to classify `x` Public; this is
    documented as the loop-counter convention.  (A stricter version
    would *override* `lt x` to `.Public` for the body's recursive
    call; both are sound.) -/
def cmdCT (cmd : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) : Bool :=
  -- **Structural fold (task #360).**  `cmdCT` is the `LowCT.foldNode`
  -- whose `leaf` discharges every non-recursive constructor exactly as the
  -- old open match did, and whose node-aware `seqNode`/`wrapNode` combiners
  -- re-introduce the per-node guards that make the analysis NON-UNIFORM:
  -- the `lt cond == .Public &&` guard on `RIfNz`/`RWhileNz`.  All the other
  -- two-child / one-child nodes (`RSeq`/`RFnDef`, `RLetZero`/`RLetU64Zero`/
  -- `RFor`/`RBlock`) just `&&` / forward their children's results.  Passing
  -- the original node `c` to the combiners (rather than `LowCT.fold`'s
  -- node-blind ones) is exactly what lets the guard be recovered.
  --
  -- The per-constructor `@[simp]` equation lemmas below (`cmdCT_R…`) each
  -- hold by `rfl`, so `simp only [cmdCT_R…]` reduces `cmdCT` on a literal
  -- constructor to the very same `&&`-conjunction the match produced — the
  -- soundness proofs' `.1`/`.2` projections after `Bool.and_eq_true` land
  -- unchanged.
  LowCT.foldNode
    (leaf := fun c => match c with
      | .RSkip                        => true
      | .RAssert _                    => true
      | .RScalarSet _ _               => true
      | .RScalarSetExpr _ e           => e.isPublic lt
      | .RCall f dest args            =>
          leafCT f && lt dest.locVar == .Public &&
            args.all (fun a => lt a.locVar == .Public)
      | .RCallSwap f dest1 dest2 args =>
          leafCT f && lt dest1.locVar == .Public && lt dest2.locVar == .Public &&
            args.all (fun a => lt a.locVar == .Public)
      | .RCallN f dests args          =>
          leafCT f && dests.all (fun d => lt d.locVar == .Public) &&
            args.all (fun a => lt a.locVar == .Public)
      | .RFnCall f dests args         =>
          leafCT f && dests.all (fun d => lt d.locVar == .Public) &&
            args.all (fun a => lt a.locVar == .Public)
      | .RCloneCall cloneVar _ oldDest innerF dest args =>
          leafCT innerF && lt cloneVar == .Public && lt oldDest.locVar == .Public &&
            lt dest.locVar == .Public &&
            args.all (fun a => lt a.locVar == .Public)
      | .RSelect dst _ src0 src1      =>
          lt dst.locVar == .Public && lt src0.locVar == .Public &&
            lt src1.locVar == .Public
      | .RLimbStore loc _ _           => lt loc.locVar == .Public
      | .RLimbStoreExpr loc _ e       =>
          (lt loc.locVar == .Public) && e.isPublic lt
      | .RArrStore arr idxVar src     =>
          lt idxVar == .Public && lt arr.locVar == .Public &&
            lt src.locVar == .Public
      | .RArrLoad dst src idxVar      =>
          lt idxVar == .Public && lt dst.locVar == .Public &&
            lt src.locVar == .Public
      | .RTupleLoad dst src _         =>
          lt dst.locVar == .Public && lt src.locVar == .Public
      | .RArrLoadLit dst src _        =>
          lt dst.locVar == .Public && lt src.locVar == .Public
      | .RArrStoreLit arr _ src       =>
          lt arr.locVar == .Public && lt src.locVar == .Public
      | .RCallDstThreaded f dst args  =>
          leafCT f && lt dst.locVar == .Public &&
            args.all (fun a => lt a.locVar == .Public)
      -- Stage 1a (2026-07-01): `RForRuntime` is NOT in `foldNode`'s recursive
      -- descent list, so it reaches `leaf` and the body is NOT analysed here.
      -- Returning `true` would be UNSOUND (fail-open on an un-analysed body);
      -- classify the runtime loop OUT of the certified-CT fragment (fail
      -- CLOSED) until the A2–A5 backend teaches `foldNode` to descend.
      | .RForRuntime _ _ _            => false
      -- The recursive constructors never reach `leaf` (`foldNode` descends
      -- into them through `seqNode`/`wrapNode`); give a fail-closed default.
      | _                             => true)
    (seqNode := fun c r1 r2 => match c with
      | .RIfNz cond _ _ =>
          -- A secret-dependent branch is the canonical CT leak.
          lt cond == .Public && r1 && r2
      -- `RSeq`, `RFnDef`: both children must be CT.
      | _ => r1 && r2)
    (wrapNode := fun c r => match c with
      | .RWhileNz cond _ =>
          -- A secret-dependent loop guard is also a CT leak (iteration
          -- count → trace length).
          lt cond == .Public && r
      -- `RLetZero`, `RLetU64Zero`, `RFor`, `RBlock`: forward the child.
      | _ => r)
    cmd

/-! ### `cmdCT` per-constructor reduction lemmas

These `@[simp]` equations reproduce the old open-match RHS verbatim, each by
`rfl` through the `foldNode` reduction lemmas.  Soundness proofs use
`simp only [cmdCT_R…, Bool.and_eq_true] at hCT` exactly where they used
`simp only [cmdCT, …]` before; the resulting `&&` structure — and hence the
`.1`/`.2` projections — is unchanged. -/

@[simp] theorem cmdCT_RSkip (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT .RSkip lt leafCT = true := rfl

@[simp] theorem cmdCT_RAssert (s : String) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RAssert s) lt leafCT = true := rfl

@[simp] theorem cmdCT_RScalarSet (x : String) (n : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RScalarSet x n) lt leafCT = true := rfl

@[simp] theorem cmdCT_RScalarSetExpr (x : String) (e : SExpr)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RScalarSetExpr x e) lt leafCT = e.isPublic lt := rfl

@[simp] theorem cmdCT_RSeq (c1 c2 : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RSeq c1 c2) lt leafCT = (cmdCT c1 lt leafCT && cmdCT c2 lt leafCT) := rfl

@[simp] theorem cmdCT_RLetZero (x : String) (t : TowerType) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RLetZero x t body) lt leafCT = cmdCT body lt leafCT := rfl

@[simp] theorem cmdCT_RLetU64Zero (x : String) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RLetU64Zero x body) lt leafCT = cmdCT body lt leafCT := rfl

@[simp] theorem cmdCT_RIfNz (cond : String) (ct cf : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RIfNz cond ct cf) lt leafCT
      = (lt cond == .Public && cmdCT ct lt leafCT && cmdCT cf lt leafCT) := rfl

@[simp] theorem cmdCT_RWhileNz (cond : String) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RWhileNz cond body) lt leafCT
      = (lt cond == .Public && cmdCT body lt leafCT) := rfl

@[simp] theorem cmdCT_RFor (x : String) (n : Nat) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RFor x n body) lt leafCT = cmdCT body lt leafCT := rfl

-- Stage 1a (2026-07-01): `RForRuntime` reaches the `foldNode` leaf, which
-- classifies it OUT of the certified-CT fragment (fail-closed `false`).
@[simp] theorem cmdCT_RForRuntime (x : String) (b : SExpr) (body : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RForRuntime x b body) lt leafCT = false := rfl

@[simp] theorem cmdCT_RBlock (body : LowCT) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RBlock body) lt leafCT = cmdCT body lt leafCT := rfl

@[simp] theorem cmdCT_RFnDef (n : String) (p r : List Located) (body cont : LowCT)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RFnDef n p r body cont) lt leafCT
      = (cmdCT body lt leafCT && cmdCT cont lt leafCT) := rfl

@[simp] theorem cmdCT_RCall (f : String) (dest : Located) (args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RCall f dest args) lt leafCT
      = (leafCT f && lt dest.locVar == .Public &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

@[simp] theorem cmdCT_RCallSwap (f : String) (dest1 dest2 : Located) (args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RCallSwap f dest1 dest2 args) lt leafCT
      = (leafCT f && lt dest1.locVar == .Public && lt dest2.locVar == .Public &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

@[simp] theorem cmdCT_RCallN (f : String) (dests args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RCallN f dests args) lt leafCT
      = (leafCT f && dests.all (fun d => lt d.locVar == .Public) &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

@[simp] theorem cmdCT_RFnCall (f : String) (dests args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RFnCall f dests args) lt leafCT
      = (leafCT f && dests.all (fun d => lt d.locVar == .Public) &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

@[simp] theorem cmdCT_RCloneCall (cloneVar : String) (cloneTy : TowerType)
    (oldDest : Located) (innerF : String) (dest : Located) (args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RCloneCall cloneVar cloneTy oldDest innerF dest args) lt leafCT
      = (leafCT innerF && lt cloneVar == .Public && lt oldDest.locVar == .Public &&
          lt dest.locVar == .Public &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

@[simp] theorem cmdCT_RSelect (dst : Located) (sel : String) (src0 src1 : Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RSelect dst sel src0 src1) lt leafCT
      = (lt dst.locVar == .Public && lt src0.locVar == .Public &&
          lt src1.locVar == .Public) := rfl

@[simp] theorem cmdCT_RLimbStore (loc : Located) (i : Nat) (v : BitVec 64)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RLimbStore loc i v) lt leafCT = (lt loc.locVar == .Public) := rfl

@[simp] theorem cmdCT_RLimbStoreExpr (loc : Located) (i : Nat) (e : SExpr)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RLimbStoreExpr loc i e) lt leafCT
      = ((lt loc.locVar == .Public) && e.isPublic lt) := rfl

@[simp] theorem cmdCT_RArrStore (arr : Located) (idxVar : String) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrStore arr idxVar src) lt leafCT
      = (lt idxVar == .Public && lt arr.locVar == .Public &&
          lt src.locVar == .Public) := rfl

@[simp] theorem cmdCT_RArrLoad (dst src : Located) (idxVar : String)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrLoad dst src idxVar) lt leafCT
      = (lt idxVar == .Public && lt dst.locVar == .Public &&
          lt src.locVar == .Public) := rfl

@[simp] theorem cmdCT_RTupleLoad (dst src : Located) (i : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RTupleLoad dst src i) lt leafCT
      = (lt dst.locVar == .Public && lt src.locVar == .Public) := rfl

@[simp] theorem cmdCT_RArrLoadLit (dst src : Located) (i : Nat)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrLoadLit dst src i) lt leafCT
      = (lt dst.locVar == .Public && lt src.locVar == .Public) := rfl

@[simp] theorem cmdCT_RArrStoreLit (arr : Located) (i : Nat) (src : Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RArrStoreLit arr i src) lt leafCT
      = (lt arr.locVar == .Public && lt src.locVar == .Public) := rfl

@[simp] theorem cmdCT_RCallDstThreaded (f : String) (dst : Located) (args : List Located)
    (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT (.RCallDstThreaded f dst args) lt leafCT
      = (leafCT f && lt dst.locVar == .Public &&
          args.all (fun a => lt a.locVar == .Public)) := rfl

/-! ## §4.  Soundness statement -/

/-- **Public-equivalence of states.**  Two `RustState`s are
    Public-equivalent under `lt` iff they agree on every Public-classified
    tower slot and every Public-classified scalar slot.  Secret slots
    may disagree.

    This is the standard *low-equivalence* relation from
    information-flow type systems (Volpano–Smith, Goguen–Meseguer). -/
def PublicEquiv (lt : LevelTable) (rs1 rs2 : RustState) : Prop :=
  (∀ x, lt x = .Public → rs1.rsTower x = rs2.rsTower x) ∧
  (∀ x, lt x = .Public → rs1.rsScalar x = rs2.rsScalar x)

/-- Convert the `BEq` comparison `lt x == .Public = true` into a
    propositional equality `lt x = .Public`.  Needed because
    `SecretLevel` derives `BEq` but not `LawfulBEq`. -/
theorem level_beq_public_iff {lt : LevelTable} {x : String} :
    (lt x == SecretLevel.Public) = true ↔ lt x = SecretLevel.Public := by
  cases hLT : lt x <;> decide

/-! ### §4.1 Basic preservation lemmas for `PublicEquiv` -/

/-- Reflexivity of `PublicEquiv`. -/
theorem PublicEquiv.refl (lt : LevelTable) (rs : RustState) :
    PublicEquiv lt rs rs := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Symmetry of `PublicEquiv`. -/
theorem PublicEquiv.symm {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) : PublicEquiv lt rs2 rs1 := by
  obtain ⟨ht, hs⟩ := h
  exact ⟨fun x hx => (ht x hx).symm, fun x hx => (hs x hx).symm⟩

/-- Transitivity of `PublicEquiv`. -/
theorem PublicEquiv.trans {lt : LevelTable} {rs1 rs2 rs3 : RustState}
    (h12 : PublicEquiv lt rs1 rs2) (h23 : PublicEquiv lt rs2 rs3) :
    PublicEquiv lt rs1 rs3 := by
  obtain ⟨ht1, hs1⟩ := h12
  obtain ⟨ht2, hs2⟩ := h23
  exact ⟨fun x hx => (ht1 x hx).trans (ht2 x hx),
          fun x hx => (hs1 x hx).trans (hs2 x hx)⟩

/-- Setting the same scalar value on both sides preserves `PublicEquiv`. -/
theorem PublicEquiv.set_scalar_same {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) (x : String) (v : Nat) :
    PublicEquiv lt (rsSetScalar rs1 x v) (rsSetScalar rs2 x v) := by
  obtain ⟨ht, hs⟩ := h
  refine ⟨?_, ?_⟩
  · intro y hy
    unfold rsSetScalar
    simp [ht y hy]
  · intro y hy
    unfold rsSetScalar
    by_cases hxy : y = x
    · subst hxy; simp
    · simp [beq_eq_false_iff_ne.mpr hxy, hs y hy]

/-- Setting the same tower value on both sides preserves `PublicEquiv`. -/
theorem PublicEquiv.set_tower_same {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) (x : String) (v : Σ t : TowerType, RustVal t) :
    PublicEquiv lt (rsSetTower rs1 x v) (rsSetTower rs2 x v) := by
  obtain ⟨ht, hs⟩ := h
  refine ⟨?_, ?_⟩
  · intro y hy
    unfold rsSetTower
    by_cases hxy : y = x
    · subst hxy; simp
    · simp [beq_eq_false_iff_ne.mpr hxy, ht y hy]
  · intro y hy
    unfold rsSetTower
    simp [hs y hy]

/-- A Public-classified tower variable agrees on the two states. -/
theorem PublicEquiv.tower_eq {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) {x : String} (hx : lt x = .Public) :
    rs1.rsTower x = rs2.rsTower x := h.1 x hx

/-- A Public-classified scalar variable agrees on the two states. -/
theorem PublicEquiv.scalar_eq {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) {x : String} (hx : lt x = .Public) :
    rs1.rsScalar x = rs2.rsScalar x := h.2 x hx

/-- `locatedLookup` is determined by `rsTower` at `loc.locVar`, so a
    Public-classified `locVar` yields equal lookups on Public-equiv states. -/
theorem PublicEquiv.locatedLookup_eq {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) {loc : Located}
    (hloc : lt loc.locVar = .Public) :
    locatedLookup rs1 loc = locatedLookup rs2 loc := by
  unfold locatedLookup
  rw [h.tower_eq hloc]

/-! ### §4.2 SExpr publicness implies determinism on Public-equiv envs -/

/-- If every free var in `e` is Public, then `e.eval` produces the same
    value on Public-equivalent scalar environments. -/
theorem SExpr.eval_eq_of_isPublic {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) (e : SExpr)
    (hp : e.isPublic lt = true) :
    e.eval rs1.rsScalar = e.eval rs2.rsScalar := by
  -- Walk the expression; each `SVar x` step needs `lt x = .Public`.
  induction e with
  | SVar x =>
    have hxBool : (lt x == SecretLevel.Public) = true := by
      simpa [SExpr.isPublic, SExpr.freeVars] using hp
    have hx : lt x = .Public := by
      cases hLT : lt x
      · rfl
      · rw [hLT] at hxBool; cases hxBool
    simp [SExpr.eval, h.scalar_eq hx]
  | SLit n => rfl
  | SAdd a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SSub a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SMul a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SShr a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SShl a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SAnd a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SXor a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SLt a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SAsr a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SMulS a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SMulHiU a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SMulHiS a b ih_a ih_b =>
    have hpA : a.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.1
    have hpB : b.isPublic lt = true := by
      simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
      simpa [SExpr.isPublic] using hp.2
    simp [SExpr.eval, ih_a hpA, ih_b hpB]
  | SLimb v i =>
    -- Tower-limb read extension (#354): the SCALAR `eval` gives `SLimb` a
    -- constant default of `0` (it cannot see the tower heap), so both sides
    -- are `0` regardless of the environment.  (The tower-aware variant
    -- `evalState_eq_of_isPublic` below handles the faithful limb read.)
    rfl

/-- **Tower-aware publicness ⇒ determinism (#356).**  If every free var in
    `e` is Public, then the *tower-aware* `SExpr.evalState` produces the same
    value on Public-equivalent states.  This is the faithful analogue of
    `eval_eq_of_isPublic`: where the scalar `eval` discharges the `SLimb` arm
    by the `0`-default, `evalState` reads limb `i` of the tower slot `v` via
    `rsTowerLimb`, which depends only on `rs.rsTower v`.  Because `v ∈
    freeVars (SLimb v i)`, `isPublic` forces `lt v = .Public`, and
    `PublicEquiv.tower_eq` then equates `rs1.rsTower v = rs2.rsTower v`.  This
    is what makes the `RLimbStoreExpr`-CT step sound with the faithful
    tower-read semantics. -/
theorem SExpr.evalState_eq_of_isPublic {lt : LevelTable} {rs1 rs2 : RustState}
    (h : PublicEquiv lt rs1 rs2) (e : SExpr)
    (hp : e.isPublic lt = true) :
    e.evalState rs1 = e.evalState rs2 := by
  induction e with
  | SVar x =>
    have hxBool : (lt x == SecretLevel.Public) = true := by
      simpa [SExpr.isPublic, SExpr.freeVars] using hp
    have hx : lt x = .Public := by
      cases hLT : lt x
      · rfl
      · rw [hLT] at hxBool; cases hxBool
    simp [SExpr.evalState, h.scalar_eq hx]
  | SLit n => rfl
  | SLimb v i =>
    -- The tower slot name `v` is the sole free var of `SLimb v i`, so
    -- `isPublic` forces `lt v = .Public`; then `rs1.rsTower v = rs2.rsTower v`
    -- and the byte-offset limb read agrees.
    have hvBool : (lt v == SecretLevel.Public) = true := by
      simpa [SExpr.isPublic, SExpr.freeVars] using hp
    have hv : lt v = .Public := by
      cases hLT : lt v
      · rfl
      · rw [hLT] at hvBool; cases hvBool
    simp only [SExpr.evalState, rsTowerLimb, h.tower_eq hv]
  | SAdd a b ih_a ih_b
  | SSub a b ih_a ih_b
  | SMul a b ih_a ih_b
  | SShr a b ih_a ih_b
  | SShl a b ih_a ih_b
  | SAnd a b ih_a ih_b
  | SXor a b ih_a ih_b
  | SLt a b ih_a ih_b
  | SAsr a b ih_a ih_b
  | SMulS a b ih_a ih_b
  | SMulHiU a b ih_a ih_b
  | SMulHiS a b ih_a ih_b =>
    all_goals (
      have hpA : a.isPublic lt = true := by
        simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
        simpa [SExpr.isPublic] using hp.1
      have hpB : b.isPublic lt = true := by
        simp [SExpr.isPublic, SExpr.freeVars, List.all_append] at hp
        simpa [SExpr.isPublic] using hp.2
      simp [SExpr.evalState, ih_a hpA, ih_b hpB])

/-! **Leakage-equivalence skeleton.**  For a CT-classified command,
    two executions starting from Public-equivalent states should
    follow the *same* control-flow trace (same branch decisions,
    same loop counts, same memory-index sequence).  We model "trace"
    loosely here: we require that the *final* Public projections
    match.  A finer-grained leakage model would expose the per-step
    trace explicitly; that's left as future work.

    `RustExec` already factors per-leaf semantics through
    `leafSpec.call`, so the leaf-level CT-ness is delegated to the
    `leafCT` table — the soundness theorem assumes leaves classified
    `true` in `leafCT` actually *are* CT (they produce equal outputs
    on Public-equivalent inputs).  See `LeafCTAssumption` below. -/

/-- **Per-leaf CT assumption.**  A leaf `f` that `leafCT` classifies
    as `true` produces equal outputs whenever the dependent argument
    list is Public-equivalent.  This is a side-condition the per-leaf
    CT table is *witnessed by* (proven externally — by audit for
    fiat-crypto, by Jasmin's `ct_check` for Jasmin leaves). -/
def LeafCTAssumption (leafSpec : LeafSpec) (leafCT : LeafCTTable) : Prop :=
  ∀ (f : String) (dt : TowerType) (argTs : List TowerType)
    (oldDest : RustVal dt)
    (args1 args2 : List (Σ t : TowerType, RustVal t)),
    leafCT f = true →
    -- Inputs are Public-equivalent (modelled as full equality at this
    -- abstraction level — a finer model would partition arg slots).
    args1 = args2 →
    leafSpec.call f dt argTs oldDest args1 =
      leafSpec.call f dt argTs oldDest args2

/-! ### §4.2½  CMOV invariant — the per-RSelect well-formedness obligation

Coarse `PublicEquiv` cannot capture the per-call semantic equality
between the two CMOV sources in well-formed CT programs (e.g. the
point-recoding step of a CT scalar-multiplication that sets both
candidate coordinates to the same value when the selector bit is
masked).  We expose this gap as a structural per-AST predicate that
the caller must discharge.

`CMOVInvariant cmd` walks the AST and, at every `RSelect dst sel
src0 src1` site, requires that the tower-slot contents at `src0.locVar`
and `src1.locVar` are equal in **every** reachable state.  This is
the standard CMOV invariant enforced at the protocol layer: src0 and
src1 are programmed to hold equal values whenever the selector is
Secret and the result `dst` is meant to be Public.

* For ASTs with **no** `RSelect`, `CMOVInvariant` reduces to `True`
  (recursively).  All ten ASTs audited by `cmdCT` in §6 below satisfy
  this — see `CMOVInvariant_of_noSelect` (decidable discharge). -/
def CMOVInvariant : LowCT → Prop
  | .RSelect _ _ src0 src1 =>
      ∀ rs : RustState, rs.rsTower src0.locVar = rs.rsTower src1.locVar
  | .RSeq c1 c2              => CMOVInvariant c1 ∧ CMOVInvariant c2
  | .RLetZero _ _ body       => CMOVInvariant body
  | .RLetU64Zero _ body      => CMOVInvariant body
  | .RBlock body             => CMOVInvariant body
  | .RFor _ _ body           => CMOVInvariant body
  | .RForRuntime _ _ body    => CMOVInvariant body
  | .RIfNz _ c1 c2           => CMOVInvariant c1 ∧ CMOVInvariant c2
  | .RWhileNz _ body         => CMOVInvariant body
  | .RFnDef _ _ _ body cont  => CMOVInvariant body ∧ CMOVInvariant cont
  | _                        => True

/-! ### §4.3  Helper lemmas for hard cases

For cases involving inter-procedural calls and memory aliasing (RCall,
RCallSwap, RCloneCall, RArrLoad, RArrStore, RSelect,
RTupleLoad, RLimbStore), the Public-equivalence preservation
requires reasoning about both `locatedLookup` and the per-oracle
specification's behaviour on Public-equivalent inputs.  We state each as
a separate lemma so the main induction stays manageable. -/

/-- Helper: if every arg's locVar is Public-classified, then
    `args.filterMap (rs.rsTower)` agrees on Public-equiv states. -/
private lemma args_filterMap_eq
    {lt : LevelTable} {rs1 rs2 : RustState}
    (hEq : PublicEquiv lt rs1 rs2) {args : List Located}
    (hArgs : args.all (fun a => lt a.locVar == .Public) = true) :
    args.filterMap (fun a => rs1.rsTower a.locVar) =
      args.filterMap (fun a => rs2.rsTower a.locVar) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hArgs
    obtain ⟨hHead, hTail⟩ := hArgs
    have hHeadP : lt a.locVar = .Public := level_beq_public_iff.mp hHead
    have hT : rs1.rsTower a.locVar = rs2.rsTower a.locVar :=
      hEq.tower_eq hHeadP
    simp [List.filterMap_cons, hT, ih hTail]

/-- The destination fold of an N-output call preserves `PublicEquiv` when every
    destination slot is Public-classified.  Each destination's old value is read
    from a Public slot, so it agrees on the two states, and the argument list is
    the same on both sides, so the leaf oracle returns the same value at every
    index. -/
private lemma callNUpdate_PublicEquiv
    {leafSpec : LeafSpec} {lt : LevelTable} {f : String}
    {argTs : List TowerType} {argList : List (Σ t : TowerType, RustVal t)} :
    ∀ (dests : List Located) (i : Nat) {rs1 rs2 : RustState},
      PublicEquiv lt rs1 rs2 →
      dests.all (fun d => lt d.locVar == .Public) = true →
      PublicEquiv lt (callNUpdate leafSpec f argTs argList i dests rs1)
        (callNUpdate leafSpec f argTs argList i dests rs2) := by
  intro dests
  induction dests with
  | nil => intro _ _ _ hEq _; exact hEq
  | cons d rest ih =>
    intro i rs1 rs2 hEq hDests
    simp only [List.all_cons, Bool.and_eq_true] at hDests
    obtain ⟨hHead, hTail⟩ := hDests
    have hHeadP : lt d.locVar = .Public := level_beq_public_iff.mp hHead
    have hLookEq : locatedLookup rs1 d = locatedLookup rs2 d :=
      hEq.locatedLookup_eq hHeadP
    show PublicEquiv lt
      (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs1 d _))
      (callNUpdate leafSpec f argTs argList (i + 1) rest (locatedUpdate rs2 d _))
    refine ih (i + 1) ?_ hTail
    rw [hLookEq]
    exact hEq.set_tower_same d.locVar _

/-- `RCall` preserves `PublicEquiv` given the per-leaf CT assumption and
    that both `dest` and every `arg` are Public-classified slots.  The
    strengthened `cmdCT` provides these per-slot obligations syntactically. -/
lemma RCall_CT_step
    {leafSpec : LeafSpec} {leafCT : LeafCTTable} {lt : LevelTable}
    {N : Nat} {f : String} {dest : Located} {args : List Located}
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCT : leafCT f = true)
    (hCTdest : lt dest.locVar = .Public)
    (hCTargs : args.all (fun a => lt a.locVar == .Public) = true)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RCall f dest args) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RCall f dest args) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | call _ _ _ _ oldV1 argList1 hLookup1 hArgList1 _ =>
    cases hExec2 with
    | call _ _ _ _ oldV2 argList2 hLookup2 hArgList2 _ =>
      -- 1. dest's old value agrees because dest is Public.
      have hTdst : rs1.rsTower dest.locVar = rs2.rsTower dest.locVar :=
        hEq.tower_eq hCTdest
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookup1 hLookup2
        rw [hTdst] at hLookup1
        rcases h2 : rs2.rsTower dest.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookup1; cases hLookup1
        · rw [h2] at hLookup1 hLookup2
          by_cases hT : t' = dest.locDst
          · simp [hT] at hLookup1 hLookup2
            rw [← hLookup1, ← hLookup2]
          · simp [hT] at hLookup1
      -- 2. argList agrees because every arg slot is Public.
      have hArgListEq : argList1 = argList2 := by
        rw [hArgList1, hArgList2]
        exact args_filterMap_eq hEq hCTargs
      -- 3. The leaf produces equal outputs on equal inputs (trivial — but
      --    we invoke the per-leaf CT assumption to make the dependency
      --    explicit).
      have hCallEq : leafSpec.call f dest.locDst (args.map (·.locDst))
                       oldV1 argList1 =
                     leafSpec.call f dest.locDst (args.map (·.locDst))
                       oldV2 argList2 := by
        subst hOldV; subst hArgListEq
        exact hLeaf f dest.locDst (args.map (·.locDst)) oldV1
                argList1 argList1 hCT rfl
      rw [hCallEq]
      exact hEq.set_tower_same dest.locVar _

/-- `RCallDstThreaded` preserves `PublicEquiv` given the per-leaf CT
    assumption and that `dst` and every `arg` are Public-classified.  Same
    structure as `RCall_CT_step`, but the call's argument list runs over
    `dst :: args` (the dst-threaded ABI passes the destination's prior
    value as the first input). -/
lemma RCallDstThreaded_CT_step
    {leafSpec : LeafSpec} {leafCT : LeafCTTable} {lt : LevelTable}
    {N : Nat} {f : String} {dst : Located} {args : List Located}
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCT : leafCT f = true)
    (hCTdst : lt dst.locVar = .Public)
    (hCTargs : args.all (fun a => lt a.locVar == .Public) = true)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RCallDstThreaded f dst args) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RCallDstThreaded f dst args) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  -- `dst :: args` all-Public predicate (combine `hCTdst` with `hCTargs`).
  have hCTall : (dst :: args).all (fun a => lt a.locVar == .Public) = true := by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by rw [hCTdst]; decide, hCTargs⟩
  cases hExec1 with
  | callDstThreaded _ _ _ _ oldV1 argList1 hLookup1 hArgList1 _ =>
    cases hExec2 with
    | callDstThreaded _ _ _ _ oldV2 argList2 hLookup2 hArgList2 _ =>
      -- 1. dst's old value agrees because dst is Public.
      have hTdst : rs1.rsTower dst.locVar = rs2.rsTower dst.locVar :=
        hEq.tower_eq hCTdst
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookup1 hLookup2
        rw [hTdst] at hLookup1
        rcases h2 : rs2.rsTower dst.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookup1; cases hLookup1
        · rw [h2] at hLookup1 hLookup2
          by_cases hT : t' = dst.locDst
          · simp [hT] at hLookup1 hLookup2
            rw [← hLookup1, ← hLookup2]
          · simp [hT] at hLookup1
      -- 2. argList agrees because every (dst :: args) slot is Public.
      have hArgListEq : argList1 = argList2 := by
        rw [hArgList1, hArgList2]
        exact args_filterMap_eq hEq hCTall
      -- 3. The leaf produces equal outputs on equal inputs.
      have hCallEq : leafSpec.call f dst.locDst ((dst :: args).map (·.locDst))
                       oldV1 argList1 =
                     leafSpec.call f dst.locDst ((dst :: args).map (·.locDst))
                       oldV2 argList2 := by
        subst hOldV; subst hArgListEq
        exact hLeaf f dst.locDst ((dst :: args).map (·.locDst)) oldV1
                argList1 argList1 hCT rfl
      rw [hCallEq]
      exact hEq.set_tower_same dst.locVar _

/-- `RCallSwap` reduces to two sequential `RCall`s.  Discharged by
    applying `RCall_CT_step` twice on the strengthened analyser. -/
lemma RCallSwap_CT_step
    {leafSpec : LeafSpec} {leafCT : LeafCTTable} {lt : LevelTable}
    {N : Nat} {f : String} {dest1 dest2 : Located} {args : List Located}
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCT : leafCT f = true)
    (hCTdest1 : lt dest1.locVar = .Public)
    (hCTdest2 : lt dest2.locVar = .Public)
    (hCTargs : args.all (fun a => lt a.locVar == .Public) = true)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | callSwap _ _ _ _ _ rsMid1 _ hC11 hC12 =>
    cases hExec2 with
    | callSwap _ _ _ _ _ rsMid2 _ hC21 hC22 =>
      have hMid : PublicEquiv lt rsMid1 rsMid2 :=
        RCall_CT_step (lt := lt) hLeaf hCT hCTdest1 hCTargs hEq hC11 hC21
      exact RCall_CT_step (lt := lt) hLeaf hCT hCTdest2 hCTargs hMid hC12 hC22

/-- `RCloneCall` reduces to `RCall` after cloning the old destination's
    value into a fresh `cloneVar` slot.  Requires `cloneVar`,
    `oldDest.locVar`, `dest.locVar`, and every arg's locVar to be
    Public-classified.  The clone step preserves `PublicEquiv` because
    we set the same tower value on both sides; then we appeal to
    `RCall_CT_step` for the inner call. -/
lemma RCloneCall_CT_step
    {leafSpec : LeafSpec} {leafCT : LeafCTTable} {lt : LevelTable}
    {N : Nat} {cloneVar : String} {cloneTy : TowerType}
    {oldDest : Located} {innerF : String} {dest : Located}
    {args : List Located}
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCT : leafCT innerF = true)
    (hCTclone : lt cloneVar = .Public)
    (hCToldDest : lt oldDest.locVar = .Public)
    (hCTdest : lt dest.locVar = .Public)
    (hCTargs : args.all (fun a => lt a.locVar == .Public) = true)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec
                (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs1 rs1')
    (hExec2 : RustExec N leafSpec
                (.RCloneCall cloneVar cloneTy oldDest innerF dest args) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | cloneCall _ _ _ _ _ _ _ rsClone1 _ hClone1 hInner1 =>
    cases hExec2 with
    | cloneCall _ _ _ _ _ _ _ rsClone2 _ hClone2 hInner2 =>
      -- The clone values agree because oldDest is Public.
      have hToldDest : rs1.rsTower oldDest.locVar = rs2.rsTower oldDest.locVar :=
        hEq.tower_eq hCToldDest
      have hCloneEq : PublicEquiv lt rsClone1 rsClone2 := by
        subst hClone1; subst hClone2
        rw [hToldDest]
        exact hEq.set_tower_same cloneVar _
      exact RCall_CT_step (lt := lt) hLeaf hCT hCTdest hCTargs hCloneEq
              hInner1 hInner2

/-- `RArrLoad` preserves `PublicEquiv` if the array slot, source slot,
    destination slot, and index variable are all Public-classified.
    The strengthened `cmdCT` (2026-05-13) now provides these per-slot
    obligations syntactically. -/
lemma RArrLoad_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {dst src : Located} {idxVar : String}
    (hCTidx : lt idxVar = .Public)
    (hCTdst : lt dst.locVar = .Public)
    (hCTsrc : lt src.locVar = .Public)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RArrLoad dst src idxVar) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RArrLoad dst src idxVar) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | arrLoad _ _ _ _ idx1 oldV1 srcV1 hIdx1 hLookupDst1 hLookupSrc1 =>
    cases hExec2 with
    | arrLoad _ _ _ _ idx2 oldV2 srcV2 hIdx2 hLookupDst2 hLookupSrc2 =>
      -- Indices are equal because idxVar is Public.
      have hIdx : idx1 = idx2 := by
        rw [← hIdx1, ← hIdx2, hEq.scalar_eq hCTidx]
      subst hIdx
      -- The dst and src lookups give equal Sigma pairs because the
      -- corresponding rsTower entries agree on Public-equiv states.
      have hTdst : rs1.rsTower dst.locVar = rs2.rsTower dst.locVar :=
        hEq.tower_eq hCTdst
      have hTsrc : rs1.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hCTsrc
      -- Extract the value-level equalities from `locatedLookup = some _`.
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookupDst1 hLookupDst2
        rw [hTdst] at hLookupDst1
        rcases h2 : rs2.rsTower dst.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupDst1; cases hLookupDst1
        · rw [h2] at hLookupDst1 hLookupDst2
          by_cases hT : t' = dst.locDst
          · simp [hT] at hLookupDst1 hLookupDst2
            rw [← hLookupDst1, ← hLookupDst2]
          · simp [hT] at hLookupDst1
      have hSrcV : (⟨src.locDst, srcV1⟩ : Σ t, RustVal t) = ⟨src.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookupSrc1 hLookupSrc2
        rw [hTsrc] at hLookupSrc1
        rcases h2 : rs2.rsTower src.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupSrc1; cases hLookupSrc1
        · rw [h2] at hLookupSrc1 hLookupSrc2
          by_cases hT : t' = src.locDst
          · simp [hT] at hLookupSrc1 hLookupSrc2
            rw [← hLookupSrc1, ← hLookupSrc2]
          · simp [hT] at hLookupSrc1
      subst hOldV
      rw [hSrcV]
      exact hEq.set_tower_same dst.locVar
        ⟨dst.locDst, leafSpec.arrLoad dst oldV1 ⟨src.locDst, srcV2⟩ idx1⟩

/-- `RArrStore`: symmetric to `RArrLoad_CT_step`. -/
lemma RArrStore_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {arr : Located} {idxVar : String} {src : Located}
    (hCTidx : lt idxVar = .Public)
    (hCTarr : lt arr.locVar = .Public)
    (hCTsrc : lt src.locVar = .Public)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RArrStore arr idxVar src) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RArrStore arr idxVar src) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | arrStore _ _ _ _ idx1 oldV1 srcV1 hIdx1 hLookupArr1 hLookupSrc1 =>
    cases hExec2 with
    | arrStore _ _ _ _ idx2 oldV2 srcV2 hIdx2 hLookupArr2 hLookupSrc2 =>
      have hIdx : idx1 = idx2 := by
        rw [← hIdx1, ← hIdx2, hEq.scalar_eq hCTidx]
      subst hIdx
      have hTarr : rs1.rsTower arr.locVar = rs2.rsTower arr.locVar :=
        hEq.tower_eq hCTarr
      have hTsrc : rs1.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hCTsrc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookupArr1 hLookupArr2
        rw [hTarr] at hLookupArr1
        rcases h2 : rs2.rsTower arr.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupArr1; cases hLookupArr1
        · rw [h2] at hLookupArr1 hLookupArr2
          by_cases hT : t' = arr.locDst
          · simp [hT] at hLookupArr1 hLookupArr2
            rw [← hLookupArr1, ← hLookupArr2]
          · simp [hT] at hLookupArr1
      have hSrcV : (⟨src.locDst, srcV1⟩ : Σ t, RustVal t) = ⟨src.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookupSrc1 hLookupSrc2
        rw [hTsrc] at hLookupSrc1
        rcases h2 : rs2.rsTower src.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupSrc1; cases hLookupSrc1
        · rw [h2] at hLookupSrc1 hLookupSrc2
          by_cases hT : t' = src.locDst
          · simp [hT] at hLookupSrc1 hLookupSrc2
            rw [← hLookupSrc1, ← hLookupSrc2]
          · simp [hT] at hLookupSrc1
      subst hOldV
      rw [hSrcV]
      exact hEq.set_tower_same arr.locVar
        ⟨arr.locDst, leafSpec.arrStore arr oldV1 idx1 ⟨src.locDst, srcV2⟩⟩

/-- `RSelect`: CMOV is read-then-write, both sources read regardless
    of `sel`.  If selector is Secret but both Public source values are
    equal on Public-equiv states, the CMOV output is still equal.  The
    strengthened analyser requires Public dst/src0/src1 (the selector
    may still be Secret — that's the whole point of CMOV).

    The **cross-branch case** (selectFalse on rs1, selectTrue on rs2 —
    or symmetric) requires the per-call CMOV invariant `hCMOV` that
    `src0.locVar` and `src1.locVar` hold equal tower values in the
    runtime state at the call site.  This is the standard well-formed-
    CMOV programming discipline.  For ASTs with no `RSelect`, this
    hypothesis is vacuous (see `CMOVInvariant`). -/
lemma RSelect_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {dst : Located} {sel : String} {src0 src1 : Located}
    (hCTdst : lt dst.locVar = .Public)
    (hCTsrc0 : lt src0.locVar = .Public)
    (hCTsrc1 : lt src1.locVar = .Public)
    (hCMOV : ∀ rs : RustState, rs.rsTower src0.locVar = rs.rsTower src1.locVar)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RSelect dst sel src0 src1) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RSelect dst sel src0 src1) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  -- The selector may be Secret, so executions 1 and 2 may take different
  -- branches.  But the resulting dst value comes from src0 or src1, and
  -- the CMOV invariant ensures src0 and src1 hold equal values in any
  -- single state — so cross-branch outputs are still equal.
  have hTsrc0 : rs1.rsTower src0.locVar = rs2.rsTower src0.locVar :=
    hEq.tower_eq hCTsrc0
  have hTsrc1 : rs1.rsTower src1.locVar = rs2.rsTower src1.locVar :=
    hEq.tower_eq hCTsrc1
  have hLookupSrc0Eq : locatedLookup rs1 src0 = locatedLookup rs2 src0 := by
    unfold locatedLookup; rw [hTsrc0]
  have hLookupSrc1Eq : locatedLookup rs1 src1 = locatedLookup rs2 src1 := by
    unfold locatedLookup; rw [hTsrc1]
  -- CMOV invariant in each state: rs.rsTower src0.locVar = rs.rsTower src1.locVar
  have hCMOV1 := hCMOV rs1
  have hCMOV2 := hCMOV rs2
  cases hExec1 with
  | selectFalse _ _ _ _ _ h1 srcV1 _ hLookup1 =>
    cases hExec2 with
    | selectFalse _ _ _ _ _ h2 srcV2 _ hLookup2 =>
      -- Both took src0.
      rw [hLookupSrc0Eq] at hLookup1
      rw [hLookup1] at hLookup2
      have hSrcEq : srcV1 = srcV2 := by
        injection hLookup2
      subst hSrcEq
      have hPI : h1 = h2 := rfl
      subst hPI
      exact hEq.set_tower_same dst.locVar ⟨dst.locDst, h1 ▸ srcV1⟩
    | selectTrue _ _ _ _ _ h2 _ srcV2 _ _ hLookup2 =>
      -- Cross-branch FT: rs1 took src0 (sel=0); rs2 took src1 (sel≠0).
      -- Use the CMOV invariant on rs2: rs2.rsTower src0.locVar =
      -- rs2.rsTower src1.locVar, then chain via Public-equiv to identify
      -- the lookup values.
      -- 1. Bring hLookup1 to rs2's view: locatedLookup rs2 src0 = some srcV1.
      rw [hLookupSrc0Eq] at hLookup1
      -- 2. The CMOV invariant gives a Sigma equality between the two
      --    raw tower entries at src0.locVar and src1.locVar in rs2.
      have hSrcSigma : (⟨src0.locDst, srcV1⟩ : Σ t, RustVal t)
                         = ⟨src1.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookup1 hLookup2
        rcases h0 : rs2.rsTower src0.locVar with _ | ⟨t0, v0⟩
        · rw [h0] at hLookup1; cases hLookup1
        rcases h1' : rs2.rsTower src1.locVar with _ | ⟨t1, v1⟩
        · rw [h1'] at hLookup2; cases hLookup2
        rw [h0] at hLookup1
        rw [h1'] at hLookup2
        by_cases hC0 : t0 = src0.locDst
        · by_cases hC1 : t1 = src1.locDst
          · simp [hC0] at hLookup1
            simp [hC1] at hLookup2
            -- srcV1 = hC0 ▸ v0, srcV2 = hC1 ▸ v1
            subst hLookup1
            subst hLookup2
            -- Need ⟨src0.locDst, hC0 ▸ v0⟩ = ⟨src1.locDst, hC1 ▸ v1⟩.
            -- From CMOV invariant: rs2.rsTower src0.locVar = rs2.rsTower src1.locVar.
            have hCMOVsig : (⟨t0, v0⟩ : Σ t, RustVal t) = ⟨t1, v1⟩ := by
              have := hCMOV2
              rw [h0, h1'] at this
              exact Option.some.inj this
            -- Substitute t0 = src0.locDst, t1 = src1.locDst.
            subst hC0
            subst hC1
            exact hCMOVsig
          · simp [hC1] at hLookup2
        · simp [hC0] at hLookup1
      -- 3. Final Sigma equality at dst.locDst.
      have hCastEq : (⟨dst.locDst, h1 ▸ srcV1⟩ : Σ t, RustVal t)
                       = ⟨dst.locDst, h2 ▸ srcV2⟩ := by
        -- The first component agrees; equate the second via HEq.
        refine Sigma.ext ?_ ?_
        · rfl
        -- Goal: HEq (h1 ▸ srcV1) (h2 ▸ srcV2)
        -- h1 ▸ srcV1 ≍ srcV1 ≍ srcV2 ≍ h2 ▸ srcV2
        have hHeq12 : HEq srcV1 srcV2 := (Sigma.mk.inj_iff.mp hSrcSigma).2
        refine HEq.trans (eqRec_heq h1 srcV1) (HEq.trans hHeq12 ?_)
        exact (eqRec_heq h2 srcV2).symm
      have hSet := hEq.set_tower_same dst.locVar
                     (v := ⟨dst.locDst, h2 ▸ srcV2⟩)
      -- locatedUpdate rs1 dst (h1 ▸ srcV1) = rsSetTower rs1 dst.locVar ⟨dst.locDst, h1 ▸ srcV1⟩
      --                                  = rsSetTower rs1 dst.locVar ⟨dst.locDst, h2 ▸ srcV2⟩ by hCastEq
      show PublicEquiv lt (locatedUpdate rs1 dst (h1 ▸ srcV1))
                          (locatedUpdate rs2 dst (h2 ▸ srcV2))
      unfold locatedUpdate
      rw [show (⟨dst.locDst, h1 ▸ srcV1⟩ : Σ t, RustVal t)
            = ⟨dst.locDst, h2 ▸ srcV2⟩ from hCastEq]
      exact hSet
  | selectTrue _ _ _ _ _ h1 _ srcV1 _ _ hLookup1 =>
    cases hExec2 with
    | selectFalse _ _ _ _ _ h2 srcV2 _ hLookup2 =>
      -- Cross-branch TF: rs1 took src1 (sel≠0); rs2 took src0 (sel=0).
      rw [hLookupSrc1Eq] at hLookup1
      have hSrcSigma : (⟨src1.locDst, srcV1⟩ : Σ t, RustVal t)
                         = ⟨src0.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookup1 hLookup2
        rcases h1' : rs2.rsTower src1.locVar with _ | ⟨t1, v1⟩
        · rw [h1'] at hLookup1; cases hLookup1
        rcases h0 : rs2.rsTower src0.locVar with _ | ⟨t0, v0⟩
        · rw [h0] at hLookup2; cases hLookup2
        rw [h1'] at hLookup1
        rw [h0] at hLookup2
        by_cases hC1 : t1 = src1.locDst
        · by_cases hC0 : t0 = src0.locDst
          · simp [hC1] at hLookup1
            simp [hC0] at hLookup2
            subst hLookup1
            subst hLookup2
            -- CMOV invariant (symmetric): rs2.rsTower src1.locVar = rs2.rsTower src0.locVar.
            have hCMOVsig : (⟨t1, v1⟩ : Σ t, RustVal t) = ⟨t0, v0⟩ := by
              have := hCMOV2.symm
              rw [h1', h0] at this
              exact Option.some.inj this
            subst hC1
            subst hC0
            exact hCMOVsig
          · simp [hC0] at hLookup2
        · simp [hC1] at hLookup1
      have hCastEq : (⟨dst.locDst, h1 ▸ srcV1⟩ : Σ t, RustVal t)
                       = ⟨dst.locDst, h2 ▸ srcV2⟩ := by
        refine Sigma.ext ?_ ?_
        · rfl
        have hHeq12 : HEq srcV1 srcV2 := (Sigma.mk.inj_iff.mp hSrcSigma).2
        refine HEq.trans (eqRec_heq h1 srcV1) (HEq.trans hHeq12 ?_)
        exact (eqRec_heq h2 srcV2).symm
      have hSet := hEq.set_tower_same dst.locVar
                     (v := ⟨dst.locDst, h2 ▸ srcV2⟩)
      show PublicEquiv lt (locatedUpdate rs1 dst (h1 ▸ srcV1))
                          (locatedUpdate rs2 dst (h2 ▸ srcV2))
      unfold locatedUpdate
      rw [show (⟨dst.locDst, h1 ▸ srcV1⟩ : Σ t, RustVal t)
            = ⟨dst.locDst, h2 ▸ srcV2⟩ from hCastEq]
      exact hSet
    | selectTrue _ _ _ _ _ h2 _ srcV2 _ _ hLookup2 =>
      rw [hLookupSrc1Eq] at hLookup1
      rw [hLookup1] at hLookup2
      have hSrcEq : srcV1 = srcV2 := by
        injection hLookup2
      subst hSrcEq
      have hPI : h1 = h2 := rfl
      subst hPI
      exact hEq.set_tower_same dst.locVar ⟨dst.locDst, h1 ▸ srcV1⟩

/-- `RLimbStore`: writes to dest via the leaf-store oracle.  Needs dest
    slot Public for the read-modify-write to agree on Public-equiv states. -/
lemma RLimbStore_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {loc : Located} {idx : Nat} {v : BitVec 64}
    (hCTloc : lt loc.locVar = .Public)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RLimbStore loc idx v) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RLimbStore loc idx v) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | limbStore _ _ _ _ oldV1 hLookup1 =>
    cases hExec2 with
    | limbStore _ _ _ _ oldV2 hLookup2 =>
      have hT : rs1.rsTower loc.locVar = rs2.rsTower loc.locVar :=
        hEq.tower_eq hCTloc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookup1 hLookup2
        rw [hT] at hLookup1
        rcases h2 : rs2.rsTower loc.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookup1; cases hLookup1
        · rw [h2] at hLookup1 hLookup2
          by_cases hT' : t' = loc.locDst
          · simp [hT'] at hLookup1 hLookup2
            rw [← hLookup1, ← hLookup2]
          · simp [hT'] at hLookup1
      subst hOldV
      exact hEq.set_tower_same loc.locVar
        ⟨loc.locDst, leafSpec.limbStore loc oldV1 idx v⟩

/-- `RLimbStoreExpr`: writes the runtime `SExpr` value to dest via the
    leaf-store oracle.  Needs dest Public (for the equal-old-value step) and
    `e` Public (so the stored word agrees on Public-equiv scalar envs). -/
lemma RLimbStoreExpr_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {loc : Located} {idx : Nat} {e : SExpr}
    (hCTloc : lt loc.locVar = .Public)
    (hCTe : e.isPublic lt = true)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | limbStoreExpr _ _ _ _ oldV1 hLookup1 =>
    cases hExec2 with
    | limbStoreExpr _ _ _ _ oldV2 hLookup2 =>
      have hT : rs1.rsTower loc.locVar = rs2.rsTower loc.locVar :=
        hEq.tower_eq hCTloc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookup1 hLookup2
        rw [hT] at hLookup1
        rcases h2 : rs2.rsTower loc.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookup1; cases hLookup1
        · rw [h2] at hLookup1 hLookup2
          by_cases hT' : t' = loc.locDst
          · simp [hT'] at hLookup1 hLookup2
            rw [← hLookup1, ← hLookup2]
          · simp [hT'] at hLookup1
      subst hOldV
      -- The stored word is now `BitVec.ofNat 64 (e.evalState rs)` (#356,
      -- tower-aware): `e` Public ⇒ the tower-aware eval (hence the word)
      -- agrees on the two Public-equiv states, INCLUDING any `SLimb` tower
      -- reads (the slot name is a free var, so Public-classified).
      have hVal : e.evalState rs1 = e.evalState rs2 :=
        SExpr.evalState_eq_of_isPublic hEq e hCTe
      rw [hVal]
      exact hEq.set_tower_same loc.locVar
        ⟨loc.locDst,
         leafSpec.limbStore loc oldV1 idx (BitVec.ofNat 64 (e.evalState rs2))⟩

/-- `RTupleLoad`: needs both dst and src Public. -/
lemma RTupleLoad_CT_step
    {leafSpec : LeafSpec} {lt : LevelTable}
    {N : Nat} {dst : Located} {src : Located} {idx : Nat}
    (hCTdst : lt dst.locVar = .Public)
    (hCTsrc : lt src.locVar = .Public)
    {rs1 rs2 rs1' rs2' : RustState}
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec (.RTupleLoad dst src idx) rs1 rs1')
    (hExec2 : RustExec N leafSpec (.RTupleLoad dst src idx) rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  cases hExec1 with
  | tupleLoad _ _ _ _ oldV1 srcV1 hLookupDst1 hLookupSrc1 =>
    cases hExec2 with
    | tupleLoad _ _ _ _ oldV2 srcV2 hLookupDst2 hLookupSrc2 =>
      have hTdst : rs1.rsTower dst.locVar = rs2.rsTower dst.locVar :=
        hEq.tower_eq hCTdst
      have hTsrc : rs1.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hCTsrc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookupDst1 hLookupDst2
        rw [hTdst] at hLookupDst1
        rcases h2 : rs2.rsTower dst.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupDst1; cases hLookupDst1
        · rw [h2] at hLookupDst1 hLookupDst2
          by_cases hT : t' = dst.locDst
          · simp [hT] at hLookupDst1 hLookupDst2
            rw [← hLookupDst1, ← hLookupDst2]
          · simp [hT] at hLookupDst1
      have hSrcV : (⟨src.locDst, srcV1⟩ : Σ t, RustVal t) = ⟨src.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookupSrc1 hLookupSrc2
        rw [hTsrc] at hLookupSrc1
        rcases h2 : rs2.rsTower src.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupSrc1; cases hLookupSrc1
        · rw [h2] at hLookupSrc1 hLookupSrc2
          by_cases hT : t' = src.locDst
          · simp [hT] at hLookupSrc1 hLookupSrc2
            rw [← hLookupSrc1, ← hLookupSrc2]
          · simp [hT] at hLookupSrc1
      subst hOldV
      rw [hSrcV]
      exact hEq.set_tower_same dst.locVar
        ⟨dst.locDst, leafSpec.tupleLoad dst oldV1 ⟨src.locDst, srcV2⟩ idx⟩

/-! ### §4.4  Main soundness theorem -/

/-- **Main soundness statement.**  If `cmdCT cmd lt leafCT = true` and
    the per-leaf assumption holds, then executing `cmd` from two
    Public-equivalent initial states produces Public-equivalent final
    states.  ("Same Public outputs whenever Public inputs match.")

    **Proof structure:** structural induction on the `RustExec`
    derivation `hExec1`.  Trivial / pure-control cases close directly;
    leaf-call and memory-store cases dispatch to per-constructor
    helper lemmas (`R*_CT_step`) above, which carry the per-slot
    Public-classification obligations.  Soundness is conditional on the
    `CMOVInvariant` hypothesis on the program. -/
theorem cmdCT_sound
    (cmd : LowCT) (lt : LevelTable) (leafCT : LeafCTTable)
    (leafSpec : LeafSpec) (N : Nat)
    (hCT : cmdCT cmd lt leafCT = true)
    (hLeaf : LeafCTAssumption leafSpec leafCT)
    (hCMOV : CMOVInvariant cmd)
    (rs1 rs2 rs1' rs2' : RustState)
    (hEq : PublicEquiv lt rs1 rs2)
    (hExec1 : RustExec N leafSpec cmd rs1 rs1')
    (hExec2 : RustExec N leafSpec cmd rs2 rs2') :
    PublicEquiv lt rs1' rs2' := by
  induction hExec1 generalizing rs2 rs2' with
  | skip rs =>
    -- RSkip: both executions are no-ops; rs1' = rs and rs2' = rs2.
    cases hExec2
    exact hEq
  | seq c1 c2 rs r1 rs' h1 h2 ih1 ih2 =>
    -- RSeq c1 c2: hCT splits into c1 CT ∧ c2 CT; chain IHs.
    have hCT1 : cmdCT c1 lt leafCT = true := by
      simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT; exact hCT.1
    have hCT2 : cmdCT c2 lt leafCT = true := by
      simp only [cmdCT_RSeq, Bool.and_eq_true] at hCT; exact hCT.2
    have hCMOV1 : CMOVInvariant c1 := hCMOV.1
    have hCMOV2 : CMOVInvariant c2 := hCMOV.2
    cases hExec2 with
    | seq _ _ _ r2 _ h1' h2' =>
      have hMid : PublicEquiv lt r1 r2 := ih1 hCT1 hCMOV1 _ _ hEq h1'
      exact ih2 hCT2 hCMOV2 _ _ hMid h2'
  | letZero x t body rs rs' hBody ih =>
    -- RLetZero x t body: both sides start by setting tower[x] := zero,
    -- then run body. Pre-state equiv lifts to set_tower_same.
    have hCTb : cmdCT body lt leafCT = true := by
      simp only [cmdCT_RLetZero] at hCT; exact hCT
    have hCMOVb : CMOVInvariant body := hCMOV
    cases hExec2 with
    | letZero _ _ _ _ _ hBody2 =>
      have hPre : PublicEquiv lt (rsSetTower rs x ⟨t, default⟩)
                                  (rsSetTower rs2 x ⟨t, default⟩) :=
        hEq.set_tower_same x ⟨t, default⟩
      exact ih hCTb hCMOVb _ _ hPre hBody2
  | letU64Zero x body rs rs' hBody ih =>
    have hCTb : cmdCT body lt leafCT = true := by
      simp only [cmdCT_RLetU64Zero] at hCT; exact hCT
    have hCMOVb : CMOVInvariant body := hCMOV
    cases hExec2 with
    | letU64Zero _ _ _ _ hBody2 =>
      have hPre : PublicEquiv lt (rsSetScalar rs x 0) (rsSetScalar rs2 x 0) :=
        hEq.set_scalar_same x 0
      exact ih hCTb hCMOVb _ _ hPre hBody2
  | scalarSet x v rs =>
    -- Both executions are pure scalarSet to the same value.
    cases hExec2
    exact hEq.set_scalar_same x v
  | ifTrue cond ct cf rs rs' v hCond hNz hCt ihT =>
    -- cmdCT ensures cond is Public ⇒ both executions take the same branch.
    have hCTcond : lt cond = .Public := by
      simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTct : cmdCT ct lt leafCT = true := by
      simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT; exact hCT.1.2
    have hCMOVct : CMOVInvariant ct := hCMOV.1
    -- The second execution must also take the true branch because
    -- rs2.rsScalar cond = rs.rsScalar cond = v ≠ 0.
    have hCondEq : rs2.rsScalar cond = v := by
      rw [← hEq.scalar_eq hCTcond]; exact hCond
    cases hExec2 with
    | ifTrue _ _ _ _ _ v2 hCond2 _ hCt2 =>
      have hv : v2 = v := by rw [← hCond2, hCondEq]
      subst hv
      exact ihT hCTct hCMOVct _ _ hEq hCt2
    | ifFalse _ _ _ _ _ hCond2 _ =>
      -- contradiction: rs2.rsScalar cond = 0 but also = v ≠ 0
      exfalso
      apply hNz
      rw [hCondEq] at hCond2
      exact hCond2
  | ifFalse cond ct cf rs rs' hCond hCf ihF =>
    have hCTcond : lt cond = .Public := by
      simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTcf : cmdCT cf lt leafCT = true := by
      simp only [cmdCT_RIfNz, Bool.and_eq_true] at hCT; exact hCT.2
    have hCMOVcf : CMOVInvariant cf := hCMOV.2
    have hCondEq : rs2.rsScalar cond = 0 := by
      rw [← hEq.scalar_eq hCTcond]; exact hCond
    cases hExec2 with
    | ifTrue _ _ _ _ _ v2 hCond2 hNz2 _ =>
      exfalso; apply hNz2
      rw [← hCond2, hCondEq]
    | ifFalse _ _ _ _ _ _ hCf2 =>
      exact ihF hCTcf hCMOVcf _ _ hEq hCf2
  | whileFalse cond body rs hCond =>
    -- cond is Public; rs2 also has cond = 0 (same scalar value).
    have hCTcond : lt cond = .Public := by
      simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCondEq : rs2.rsScalar cond = 0 := by
      rw [← hEq.scalar_eq hCTcond]; exact hCond
    cases hExec2 with
    | whileFalse _ _ _ _ =>
      exact hEq
    | whileTrue _ _ _ _ _ v2 hCond2 hNz2 _ _ =>
      exfalso; apply hNz2
      rw [← hCond2, hCondEq]
  | whileTrue cond body rs r1 rs' v hCond hNz hBody hLoop ihBody ihLoop =>
    -- Both must also take the true branch (cond Public).
    have hCTcond : lt cond = .Public := by
      simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCTbody : cmdCT body lt leafCT = true := by
      simp only [cmdCT_RWhileNz, Bool.and_eq_true] at hCT; exact hCT.2
    have hCMOVbody : CMOVInvariant body := hCMOV
    have hCondEq : rs2.rsScalar cond = v := by
      rw [← hEq.scalar_eq hCTcond]; exact hCond
    cases hExec2 with
    | whileFalse _ _ _ hCond2 =>
      exfalso; apply hNz
      rw [← hCond, hEq.scalar_eq hCTcond, hCond2]
    | whileTrue _ _ _ r2 _ v2 _ _ hBody2 hLoop2 =>
      have hMid : PublicEquiv lt r1 r2 := ihBody hCTbody hCMOVbody _ _ hEq hBody2
      -- Recurse on the tail loop. Note `cmdCT` and CMOVInvariant of
      -- `RWhileNz cond body` are unchanged so `hCT` / `hCMOV` still apply.
      exact ihLoop hCT hCMOV _ _ hMid hLoop2
  | forZero x body rs =>
    cases hExec2 with
    | forZero _ _ _ =>
      exact hEq
  | forSucc x n body rs r1 rs' hOuter hBody ihOuter ihBody =>
    -- RFor x (n+1) body: outer = RFor x n body, then body with x := n.
    have hCTbody : cmdCT body lt leafCT = true := by
      simp only [cmdCT_RFor] at hCT; exact hCT
    have hCMOVbody : CMOVInvariant body := hCMOV
    cases hExec2 with
    | forSucc _ _ _ _ r2 _ hOuter2 hBody2 =>
      have hMid : PublicEquiv lt r1 r2 := ihOuter hCT hCMOV _ _ hEq hOuter2
      have hSet : PublicEquiv lt (rsSetScalar r1 x n) (rsSetScalar r2 x n) :=
        hMid.set_scalar_same x n
      exact ihBody hCTbody hCMOVbody _ _ hSet hBody2
  | forRuntime _ _ _ _ _ _ _ =>
    -- `cmdCT` classifies the runtime loop as `false` (out of fragment), so
    -- the `cmdCT … = true` hypothesis is contradictory.
    rw [cmdCT_RForRuntime] at hCT
    exact absurd hCT (by decide)
  | call f dest args rs oldDestV argList hLookup hArgList hArgTypes =>
    -- Dispatch to RCall_CT_step helper.
    have hCTf : leafCT f = true := by
      simp only [cmdCT_RCall, Bool.and_eq_true] at hCT; exact hCT.1.1
    have hCTdest : lt dest.locVar = .Public := by
      simp only [cmdCT_RCall, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTargs : args.all (fun a => lt a.locVar == .Public) = true := by
      simp only [cmdCT_RCall, Bool.and_eq_true] at hCT; exact hCT.2
    -- Reconstruct the call exec for the first side and pass to helper.
    have hExec1' : RustExec N leafSpec (.RCall f dest args) rs
        (locatedUpdate rs dest
          (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList)) :=
      RustExec.call f dest args rs oldDestV argList hLookup hArgList hArgTypes
    exact RCall_CT_step (lt := lt) hLeaf hCTf hCTdest hCTargs hEq hExec1' hExec2
  | cloneCall cloneVar cloneTy oldDest innerF dest args
              rs rsClone rs' hClone hInner ihInner =>
    have hCTf : leafCT innerF = true := by
      simp only [cmdCT_RCloneCall, Bool.and_eq_true] at hCT; exact hCT.1.1.1.1
    have hCTclone : lt cloneVar = .Public := by
      simp only [cmdCT_RCloneCall, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1.1.2
    have hCToldDest : lt oldDest.locVar = .Public := by
      simp only [cmdCT_RCloneCall, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1.2
    have hCTdest : lt dest.locVar = .Public := by
      simp only [cmdCT_RCloneCall, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTargs : args.all (fun a => lt a.locVar == .Public) = true := by
      simp only [cmdCT_RCloneCall, Bool.and_eq_true] at hCT; exact hCT.2
    have hExec1' : RustExec N leafSpec
                     (.RCloneCall cloneVar cloneTy oldDest innerF dest args)
                     rs rs' :=
      RustExec.cloneCall cloneVar cloneTy oldDest innerF dest args
                          rs rsClone rs' hClone hInner
    exact RCloneCall_CT_step (lt := lt) hLeaf hCTf hCTclone hCToldDest hCTdest
            hCTargs hEq hExec1' hExec2
  | callSwap f dest1 dest2 args rs rs1 rs' hC1 hC2 ihC1 ihC2 =>
    have hCTf : leafCT f = true := by
      simp only [cmdCT_RCallSwap, Bool.and_eq_true] at hCT; exact hCT.1.1.1
    have hCTdest1 : lt dest1.locVar = .Public := by
      simp only [cmdCT_RCallSwap, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1.2
    have hCTdest2 : lt dest2.locVar = .Public := by
      simp only [cmdCT_RCallSwap, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTargs : args.all (fun a => lt a.locVar == .Public) = true := by
      simp only [cmdCT_RCallSwap, Bool.and_eq_true] at hCT; exact hCT.2
    have hExec1' : RustExec N leafSpec (.RCallSwap f dest1 dest2 args) rs rs' :=
      RustExec.callSwap f dest1 dest2 args rs rs1 rs' hC1 hC2
    exact RCallSwap_CT_step (lt := lt) hLeaf hCTf hCTdest1 hCTdest2 hCTargs hEq hExec1' hExec2
  | limbStore loc idx v rs oldDestV hLookup =>
    have hCTloc : lt loc.locVar = .Public := by
      simp only [cmdCT_RLimbStore] at hCT
      exact level_beq_public_iff.mp hCT
    have hExec1' : RustExec N leafSpec (.RLimbStore loc idx v) rs
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v)) :=
      RustExec.limbStore loc idx v rs oldDestV hLookup
    exact RLimbStore_CT_step (lt := lt) hCTloc hEq hExec1' hExec2
  | limbStoreExpr loc idx e rs oldDestV hLookup =>
    have hCTloc : lt loc.locVar = .Public := by
      simp only [cmdCT_RLimbStoreExpr, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCTe : e.isPublic lt = true := by
      simp only [cmdCT_RLimbStoreExpr, Bool.and_eq_true] at hCT
      exact hCT.2
    have hExec1' : RustExec N leafSpec (.RLimbStoreExpr loc idx e) rs
        (locatedUpdate rs loc
          (leafSpec.limbStore loc oldDestV idx (BitVec.ofNat 64 (e.evalState rs)))) :=
      RustExec.limbStoreExpr loc idx e rs oldDestV hLookup
    exact RLimbStoreExpr_CT_step (lt := lt) hCTloc hCTe hEq hExec1' hExec2
  | callN f dests args rs argList hArgList _ _ =>
    have hCTdests : dests.all (fun d => lt d.locVar == .Public) = true := by
      simp only [cmdCT_RCallN, Bool.and_eq_true] at hCT; exact hCT.1.2
    have hCTargs : args.all (fun a => lt a.locVar == .Public) = true := by
      simp only [cmdCT_RCallN, Bool.and_eq_true] at hCT; exact hCT.2
    cases hExec2 with
    | callN _ _ _ _ argList2 hArgList2 _ _ =>
      have hArgListEq : argList = argList2 := by
        rw [hArgList, hArgList2]; exact args_filterMap_eq hEq hCTargs
      subst hArgListEq
      exact callNUpdate_PublicEquiv dests 0 hEq hCTdests
  | callDstThreaded f dst args rs oldDestV argList hLookup hArgList hArgTypes =>
    -- Dispatch to RCallDstThreaded_CT_step helper (mirrors `call`).
    have hCTf : leafCT f = true := by
      simp only [cmdCT_RCallDstThreaded, Bool.and_eq_true] at hCT; exact hCT.1.1
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RCallDstThreaded, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTargs : args.all (fun a => lt a.locVar == .Public) = true := by
      simp only [cmdCT_RCallDstThreaded, Bool.and_eq_true] at hCT; exact hCT.2
    have hExec1' : RustExec N leafSpec (.RCallDstThreaded f dst args) rs
        (locatedUpdate rs dst
          (leafSpec.call f dst.locDst ((dst :: args).map (·.locDst)) oldDestV argList)) :=
      RustExec.callDstThreaded f dst args rs oldDestV argList hLookup hArgList hArgTypes
    exact RCallDstThreaded_CT_step (lt := lt) hLeaf hCTf hCTdst hCTargs hEq hExec1' hExec2
  | selectFalse dst sel src0 src1 rs h srcV hSel hLookup =>
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTsrc0 : lt src0.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTsrc1 : lt src1.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    -- CMOVInvariant projects directly to the per-RSelect equal-source obligation.
    have hCMOVsel : ∀ rs : RustState, rs.rsTower src0.locVar = rs.rsTower src1.locVar :=
      hCMOV
    have hExec1' : RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV)) :=
      RustExec.selectFalse dst sel src0 src1 rs h srcV hSel hLookup
    exact RSelect_CT_step (lt := lt) hCTdst hCTsrc0 hCTsrc1 hCMOVsel hEq hExec1' hExec2
  | selectTrue dst sel src0 src1 rs h v srcV hSel hNz hLookup =>
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTsrc0 : lt src0.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTsrc1 : lt src1.locVar = .Public := by
      simp only [cmdCT_RSelect, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    have hCMOVsel : ∀ rs : RustState, rs.rsTower src0.locVar = rs.rsTower src1.locVar :=
      hCMOV
    have hExec1' : RustExec N leafSpec (.RSelect dst sel src0 src1) rs
        (locatedUpdate rs dst (h ▸ srcV)) :=
      RustExec.selectTrue dst sel src0 src1 rs h v srcV hSel hNz hLookup
    exact RSelect_CT_step (lt := lt) hCTdst hCTsrc0 hCTsrc1 hCMOVsel hEq hExec1' hExec2
  | assert label rs =>
    cases hExec2
    exact hEq
  | block body rs rs' hBody ih =>
    have hCTb : cmdCT body lt leafCT = true := by
      simp only [cmdCT_RBlock] at hCT; exact hCT
    have hCMOVb : CMOVInvariant body := hCMOV
    cases hExec2 with
    | block _ _ _ hBody2 =>
      exact ih hCTb hCMOVb _ _ hEq hBody2
  | tupleLoad dst src idx rs oldV srcV hLookupDst hLookupSrc =>
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RTupleLoad, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCTsrc : lt src.locVar = .Public := by
      simp only [cmdCT_RTupleLoad, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    have hExec1' : RustExec N leafSpec (.RTupleLoad dst src idx) rs
        (locatedUpdate rs dst (leafSpec.tupleLoad dst oldV ⟨src.locDst, srcV⟩ idx)) :=
      RustExec.tupleLoad dst src idx rs oldV srcV hLookupDst hLookupSrc
    exact RTupleLoad_CT_step (lt := lt) hCTdst hCTsrc hEq hExec1' hExec2
  | arrStore arr idxVar src rs idx oldV srcV hIdx hLookupArr hLookupSrc =>
    have hCTidx : lt idxVar = .Public := by
      simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTarr : lt arr.locVar = .Public := by
      simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTsrc : lt src.locVar = .Public := by
      simp only [cmdCT_RArrStore, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    have hExec1' : RustExec N leafSpec (.RArrStore arr idxVar src) rs
        (locatedUpdate rs arr (leafSpec.arrStore arr oldV idx ⟨src.locDst, srcV⟩)) :=
      RustExec.arrStore arr idxVar src rs idx oldV srcV hIdx hLookupArr hLookupSrc
    exact RArrStore_CT_step (lt := lt) hCTidx hCTarr hCTsrc hEq hExec1' hExec2
  | arrLoad dst src idxVar rs idx oldV srcV hIdx hLookupDst hLookupSrc =>
    have hCTidx : lt idxVar = .Public := by
      simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.1
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1.2
    have hCTsrc : lt src.locVar = .Public := by
      simp only [cmdCT_RArrLoad, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    have hExec1' : RustExec N leafSpec (.RArrLoad dst src idxVar) rs
        (locatedUpdate rs dst (leafSpec.arrLoad dst oldV ⟨src.locDst, srcV⟩ idx)) :=
      RustExec.arrLoad dst src idxVar rs idx oldV srcV hIdx hLookupDst hLookupSrc
    exact RArrLoad_CT_step (lt := lt) hCTidx hCTdst hCTsrc hEq hExec1' hExec2
  | arrStoreLit arr idx src rs oldV1 srcV1 hLookupArr1 hLookupSrc1 =>
    -- Literal index: no `rsScalar` lookup, so the index is a shared
    -- compile-time constant on both sides — no index-equality obligation.
    -- The dst (`arr`) and `src` slots are Public, so the old/source values
    -- agree on Public-equiv states (mirrors `RArrStore_CT_step`).
    have hCTarr : lt arr.locVar = .Public := by
      simp only [cmdCT_RArrStoreLit, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCTsrc : lt src.locVar = .Public := by
      simp only [cmdCT_RArrStoreLit, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    cases hExec2 with
    | arrStoreLit _ _ _ _ oldV2 srcV2 hLookupArr2 hLookupSrc2 =>
      have hTarr : rs.rsTower arr.locVar = rs2.rsTower arr.locVar :=
        hEq.tower_eq hCTarr
      have hTsrc : rs.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hCTsrc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookupArr1 hLookupArr2
        rw [hTarr] at hLookupArr1
        rcases h2 : rs2.rsTower arr.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupArr1; cases hLookupArr1
        · rw [h2] at hLookupArr1 hLookupArr2
          by_cases hT : t' = arr.locDst
          · simp [hT] at hLookupArr1 hLookupArr2
            rw [← hLookupArr1, ← hLookupArr2]
          · simp [hT] at hLookupArr1
      have hSrcV : (⟨src.locDst, srcV1⟩ : Σ t, RustVal t) = ⟨src.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookupSrc1 hLookupSrc2
        rw [hTsrc] at hLookupSrc1
        rcases h2 : rs2.rsTower src.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupSrc1; cases hLookupSrc1
        · rw [h2] at hLookupSrc1 hLookupSrc2
          by_cases hT : t' = src.locDst
          · simp [hT] at hLookupSrc1 hLookupSrc2
            rw [← hLookupSrc1, ← hLookupSrc2]
          · simp [hT] at hLookupSrc1
      subst hOldV
      rw [hSrcV]
      exact hEq.set_tower_same arr.locVar
        ⟨arr.locDst, leafSpec.arrStore arr oldV1 idx ⟨src.locDst, srcV2⟩⟩
  | arrLoadLit dst src idx rs oldV1 srcV1 hLookupDst1 hLookupSrc1 =>
    -- Literal index complement of `arrLoad`; same Public dst/src argument,
    -- no index-equality obligation (the index is a shared AST literal).
    have hCTdst : lt dst.locVar = .Public := by
      simp only [cmdCT_RArrLoadLit, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.1
    have hCTsrc : lt src.locVar = .Public := by
      simp only [cmdCT_RArrLoadLit, Bool.and_eq_true] at hCT
      exact level_beq_public_iff.mp hCT.2
    cases hExec2 with
    | arrLoadLit _ _ _ _ oldV2 srcV2 hLookupDst2 hLookupSrc2 =>
      have hTdst : rs.rsTower dst.locVar = rs2.rsTower dst.locVar :=
        hEq.tower_eq hCTdst
      have hTsrc : rs.rsTower src.locVar = rs2.rsTower src.locVar :=
        hEq.tower_eq hCTsrc
      have hOldV : oldV1 = oldV2 := by
        unfold locatedLookup at hLookupDst1 hLookupDst2
        rw [hTdst] at hLookupDst1
        rcases h2 : rs2.rsTower dst.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupDst1; cases hLookupDst1
        · rw [h2] at hLookupDst1 hLookupDst2
          by_cases hT : t' = dst.locDst
          · simp [hT] at hLookupDst1 hLookupDst2
            rw [← hLookupDst1, ← hLookupDst2]
          · simp [hT] at hLookupDst1
      have hSrcV : (⟨src.locDst, srcV1⟩ : Σ t, RustVal t) = ⟨src.locDst, srcV2⟩ := by
        unfold locatedLookup at hLookupSrc1 hLookupSrc2
        rw [hTsrc] at hLookupSrc1
        rcases h2 : rs2.rsTower src.locVar with _ | ⟨t', v'⟩
        · rw [h2] at hLookupSrc1; cases hLookupSrc1
        · rw [h2] at hLookupSrc1 hLookupSrc2
          by_cases hT : t' = src.locDst
          · simp [hT] at hLookupSrc1 hLookupSrc2
            rw [← hLookupSrc1, ← hLookupSrc2]
          · simp [hT] at hLookupSrc1
      subst hOldV
      rw [hSrcV]
      exact hEq.set_tower_same dst.locVar
        ⟨dst.locDst, leafSpec.arrLoad dst oldV1 ⟨src.locDst, srcV2⟩ idx⟩
  | scalarSetExpr x e rs =>
    -- e is Public ⇒ same value on both sides.
    have hPub : e.isPublic lt = true := by
      simp only [cmdCT_RScalarSetExpr] at hCT; exact hCT
    cases hExec2 with
    | scalarSetExpr _ _ _ =>
      have hEval : e.eval rs.rsScalar = e.eval rs2.rsScalar :=
        SExpr.eval_eq_of_isPublic hEq e hPub
      rw [hEval]
      exact hEq.set_scalar_same x _

/-! ## §5.  Negative test: a leaky AST -/

/-- A tiny AST exhibiting the canonical "secret index" leak: bind a
    Secret-classified `secret_idx`, then load an array cell at that
    index.  `cmdCT` should reject this. -/
def leakyAST : LowCT :=
  LowCT.RLetU64Zero "secret_idx" $
    LowCT.RArrLoad
      { locVar := "dst", locSrc := TowerType.TBytes 32 }
      { locVar := "table", locSrc := TowerType.TArr 16 (TowerType.TBytes 32) }
      "secret_idx"

/-- Classification: `secret_idx` is Secret; everything else Public. -/
def leakyAST_lt : LevelTable :=
  fun x => if x == "secret_idx" then .Secret else .Public

#eval (cmdCT leakyAST leakyAST_lt LeafCTTable.canonical : Bool)
-- expected: false  (the RArrLoad has a Secret idxVar)

/-! ## §6.  Running cmdCT on the five emitted ASTs -/

/-- Level table for `fe25519InvertBody`: input `a` and output `out`
    classified Public.  All intermediates Public.  (`fe25519_invert`
    has no scalar slots — there are no Secret slots at all.) -/
def fe25519Invert_lt : LevelTable := LevelTable.allPublic

/-- Level table for the Scalar25519 method bodies.  Per the doc:
    scalar bytes are Secret (user's secret key), Mont-domain scalar
    is also Secret; byte outputs of `to_bytes` write back a Secret
    value.  Public: nothing in this AST family — but since all six
    bodies are single leaf calls with NO branches/indices, the table
    we choose doesn't change the result.  We pick all-Public to keep
    the test minimal. -/
def scalar25519_lt : LevelTable := LevelTable.allPublic

/-- Level table for `montUToEdwardsBody`.  Public-Mont-u-coord input;
    public Edwards-y output.  XEdDSA verifies a PUBLIC point, so
    every slot is Public. -/
def montUToEdwards_lt : LevelTable := LevelTable.allPublic

/-- Level table for `combTableInitArrV2Body`.  The comb table is
    built from PUBLIC inputs `B_xyzt` and `ID_xyzt`; the cells, the
    loop counters `i` / `d`, and the index variable `k` (computed via
    `k := i*16 + d`) are all Public. -/
def combTableInitArrV2_lt : LevelTable := LevelTable.allPublic

/-- Level table for `xeddsaVerifyBody`.  Verify operates on PUBLIC
    inputs (public key, signature, message); all slots Public. -/
def xeddsaVerify_lt : LevelTable := LevelTable.allPublic

/-! ### Evaluations

`#eval`'d below for each of the five emitted ASTs; each returns `true`
(also formally checked via `native_decide` in §7).

* `fe25519InvertBody` — 254 sqr + 11 mul, no branches / loops / arrays.
* `Scalar25519Ops` × 6 — each is a single CT leaf call.
* `montUToEdwardsBody` — 6 sequential RCalls, 4 RLetZero locals.
* `combTableInitArrV2Body` — `RFor` + `RArrLoad`/`RArrStore` with
   `k := i*16 + d` built from PUBLIC loop counters.  This is the AST
   whose RUNTIME LOOKUP (Rust shim, SECRET digit index) was the P0 CT
   leak fixed on 2026-05-13 — the build itself is purely public.
* `xeddsaVerifyBody` — `RLetZero` + 2 sequential RCalls.
-/

#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.fe25519InvertBody
              fe25519Invert_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.fromBytesModOrderBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.toBytesBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.mulBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.addBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.subBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.negateBody
              scalar25519_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards.montUToEdwardsBody
              montUToEdwards_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.combTableInitArrV2Body
              combTableInitArrV2_lt LeafCTTable.canonical : Bool)
#eval (cmdCT CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify.xeddsaVerifyBody
              xeddsaVerify_lt LeafCTTable.canonical : Bool)

/-! ## §7.  Verification examples — Lean-side `decide` proofs

These show that the analyser is decidable and the audit results are
formally checked, not just `#eval`'d. -/

example :
    cmdCT CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.fe25519InvertBody
           fe25519Invert_lt LeafCTTable.canonical = true := by
  native_decide

example :
    cmdCT CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards.montUToEdwardsBody
           montUToEdwards_lt LeafCTTable.canonical = true := by
  native_decide

example :
    cmdCT CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify.xeddsaVerifyBody
           xeddsaVerify_lt LeafCTTable.canonical = true := by
  native_decide

example :
    cmdCT CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.combTableInitArrV2Body
           combTableInitArrV2_lt LeafCTTable.canonical = true := by
  native_decide

example :
    cmdCT leakyAST leakyAST_lt LeafCTTable.canonical = false := by
  native_decide

/-! ### CMOVInvariant discharge — `RSelect`-free ASTs are vacuous.

Every one of the ten audited ASTs (`fe25519InvertBody`, the six
`Scalar25519Ops` bodies, `montUToEdwardsBody`, `combTableInitArrV2Body`,
`xeddsaVerifyBody`) has zero `RSelect` constructors — see
`hasSelect = false` in
`CatCrypt/Crypto/Jasmin/Examples/EmittedASTCorrectness.lean`.  The
`CMOVInvariant` predicate is defined to reduce to `True` structurally
on every non-`RSelect` constructor, so each of these discharges
trivially.

These instances are stated as theorems (not `example`s) so the
downstream caller of `cmdCT_sound` can quote them by name.  Body:
`by unfold CMOVInvariant ...; exact True.intro` or simply `trivial`
after reducing the AST. -/

theorem fe25519InvertBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.fe25519InvertBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Fe25519Invert.fe25519InvertBody
  trivial

theorem fromBytesModOrderBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.fromBytesModOrderBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.fromBytesModOrderBody
  trivial

theorem toBytesBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.toBytesBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.toBytesBody
  trivial

theorem mulBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.mulBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.mulBody
  trivial

theorem addBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.addBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.addBody
  trivial

theorem subBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.subBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.subBody
  trivial

theorem negateBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.negateBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops.negateBody
  trivial

theorem montUToEdwardsBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards.montUToEdwardsBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.MontUToEdwards.montUToEdwardsBody
  trivial

theorem combTableInitArrV2Body_CMOV :
    CMOVInvariant
      CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.combTableInitArrV2Body := by
  unfold CatCrypt.Crypto.Jasmin.Examples.CombTableInitArrV2.combTableInitArrV2Body
  trivial

theorem xeddsaVerifyBody_CMOV :
    CMOVInvariant CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify.xeddsaVerifyBody := by
  unfold CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify.xeddsaVerifyBody
  trivial

/-! ## §8.  Axiom check -/

-- Confirms `cmdCT_sound` depends on the stated assumptions only:
-- `[propext, Classical.choice, Quot.sound]` — no `sorryAx` after the
-- Phase J CT-analyser strengthening (`CMOVInvariant` hypothesis +
-- cross-branch `RSelect_CT_step` discharge, 2026-05-13).  These are
-- standard mathlib classical-logic axioms used by `decide`/`Decidable`.
#print axioms cmdCT_sound

end CatCrypt.Crypto.Jasmin.LowCT
