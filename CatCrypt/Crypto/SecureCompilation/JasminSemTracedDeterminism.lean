/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.JasminSemTraced

set_option autoImplicit false

/-!
# JasminSemTracedDeterminism — A1.18 closure

Determinism proofs for `jasminSemTracedSingle`, `jasminSemTraced'`,
`jasminSemTraced`, `jasminSem`. Split out from `JasminSemTraced.lean`
to keep the core inductive + bridge definitions separate from the
substantive proof content. See the section headers below for the
sub-track of A1.18 each part addresses.
-/

namespace CatCrypt.Crypto.SecureCompilation.JasminSemTraced

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.SemBridge
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ### Determinism (A1.18 main result)

The width-keyed `jasminSemTraced` constructors carry, besides the
`.sarr` storage width, the ghost `VarInfo.towerTag` — the
`TowerType.byteSize` of the tower type each `.sarr` variable was
lowered from.  `byteSize` is injective (`byteSize_inj` below), so the
instruction pins the tower type, and two derivations over the same
`InstrR` recover the same type.  This is what makes the per-pair
`det_*_pair` lemmas and the mutual
`jasminSemTracedSingle.deterministic` / `jasminSemTraced'.deterministic`
unconditional.

Two residual dependent-elimination wrinkles remain, handled per proof:
* `Located`-projection and `List.map locToPExpr` subterms in an
  `InstrR` index are generalized to fresh variables before `cases`
  (the eliminator only assigns *variable* index positions).
* The `(limb_store_oracle, clone_tower)` cross-pair shares the outer
  `Copn` shape and differs in the `AsmOp.name` literal; generalizing
  the literal moves the mismatch into an equation dischargeable by
  `decide`/`simp` (demonstrated in `toy_no_cross_store_clone` below). -/

/-- `TowerType.byteSize` is injective.

    **Closure (2026-05-04):** Phase D/E/I/K's `byteSize` definition
    in `LowCT.lean` uses `Nat.pair tag inner` with a unique
    constructor-tag in the first slot:
    * Legacy 7 constructors: `Nat.pair 0 i` for `i ∈ [0..8]`.
    * `TFp25519_4Bounded b`: `Nat.pair 1 b`.
    * `TFpGen name n`: `Nat.pair 2 (Nat.pair (encodeStringNat name) n)`.
    * `TFp2Gen name n`: `Nat.pair 3 (Nat.pair (encodeStringNat name) n)`.
    * `TTuple a b`: `Nat.pair 4 (Nat.pair a.byteSize b.byteSize)`.
    * `TBytes n`: `Nat.pair 5 n`.

    Top-level tag injectivity (via `Nat.pair_eq_pair`) discriminates
    all cross-constructor cases.  Inner injectivity:
    * Legacy: each `Nat.pair 0 i` is unique by `i`.
    * `TFpGen`/`TFp2Gen`: inner is `Nat.pair (encodeStringNat name) n`;
      `encodeStringNat_inj` recovers `name`.
    * `TTuple`: structural recursion on inner byteSize. -/
theorem TowerType.byteSize_inj : Function.Injective TowerType.byteSize := by
  intro a b h
  induction a generalizing b with
  | TFp => cases b <;> simp_all [TowerType.byteSize]
  | TFp2 => cases b <;> simp_all [TowerType.byteSize]
  | TFp6 => cases b <;> simp_all [TowerType.byteSize]
  | TFp12 => cases b <;> simp_all [TowerType.byteSize]
  | TU64 => cases b <;> simp_all [TowerType.byteSize]
  | TFp25519 => cases b <;> simp_all [TowerType.byteSize]
  | TFp25519_64 => cases b <;> simp_all [TowerType.byteSize]
  | TFpL25519 => cases b <;> simp_all [TowerType.byteSize]
  | TFpP256 => cases b <;> simp_all [TowerType.byteSize]
  | TU8 => cases b <;> simp_all [TowerType.byteSize]
  | TU32 => cases b <;> simp_all [TowerType.byteSize]
  | TFp25519_4Bounded i => cases b <;> simp_all [TowerType.byteSize]
  | TFpGen name n =>
      cases b with
      | TFpGen name' n' =>
          have hp : Nat.pair (encodeStringNat name) n
                  = Nat.pair (encodeStringNat name') n' := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          rw [encodeStringNat_inj hp.1, hp.2]
      | _ => simp_all [TowerType.byteSize]
  | TFp2Gen name n =>
      cases b with
      | TFp2Gen name' n' =>
          have hp : Nat.pair (encodeStringNat name) n
                  = Nat.pair (encodeStringNat name') n' := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          rw [encodeStringNat_inj hp.1, hp.2]
      | _ => simp_all [TowerType.byteSize]
  | TTuple a₁ a₂ ih1 ih2 =>
      cases b with
      | TTuple b₁ b₂ =>
          have hp : Nat.pair a₁.byteSize a₂.byteSize
                  = Nat.pair b₁.byteSize b₂.byteSize := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          rw [ih1 hp.1, ih2 hp.2]
      | _ => simp_all [TowerType.byteSize]
  | TBytes n => cases b <;> simp_all [TowerType.byteSize]
  | TArr n t ih =>
      cases b with
      | TArr n' t' =>
          have hp : Nat.pair n t.byteSize
                  = Nat.pair n' t'.byteSize := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          rw [hp.1, ih hp.2]
      | _ => simp_all [TowerType.byteSize]
  -- Phase L (2026-05-22): polynomial-mod-q constructors.  Each ctor's
  -- byteSize uses a distinct top-level Nat.pair tag (7/8/9), so
  -- cross-ctor cases are discharged by `simp_all`.  Same-ctor cases
  -- recover the parameters via `Nat.pair_eq_pair`.
  | TPolyMod q n =>
      cases b with
      | TPolyMod q' n' =>
          have hp : Nat.pair q n = Nat.pair q' n' := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          rw [hp.1, hp.2]
      | _ => simp_all [TowerType.byteSize]
  | TPolyVec q n k =>
      cases b with
      | TPolyVec q' n' k' =>
          have hp : Nat.pair q (Nat.pair n k) = Nat.pair q' (Nat.pair n' k') := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          obtain ⟨hq, hnk⟩ := hp
          rw [Nat.pair_eq_pair] at hnk
          rw [hq, hnk.1, hnk.2]
      | _ => simp_all [TowerType.byteSize]
  | TPolyMat q n k m =>
      cases b with
      | TPolyMat q' n' k' m' =>
          have hp : Nat.pair q (Nat.pair n (Nat.pair k m))
                  = Nat.pair q' (Nat.pair n' (Nat.pair k' m')) := by
            simpa [TowerType.byteSize, Nat.pair_eq_pair] using h
          rw [Nat.pair_eq_pair] at hp
          obtain ⟨hq, hnkm⟩ := hp
          rw [Nat.pair_eq_pair] at hnkm
          obtain ⟨hn, hkm⟩ := hnkm
          rw [Nat.pair_eq_pair] at hkm
          rw [hq, hn, hkm.1, hkm.2]
      | _ => simp_all [TowerType.byteSize]

/-- `TowerType.storageBytes` is not injective — the 32-byte constructors
    `TFp25519_64` / `TFpL25519` / `TFpP256` / `TFp25519_4Bounded _` share
    a width, and `TBytes n` shares width `n` with every type of storage
    width `n`.  The trace model therefore pins the tower type through the
    ghost `VarInfo.towerTag` (a `byteSize` value, injective by
    `byteSize_inj`), never through the `.sarr` width alone. -/
example : (TowerType.TFp25519_64).storageBytes = (TowerType.TFpP256).storageBytes := rfl

/-! ### `decide` + `generalize` demonstration

Self-contained example showing that the option-(a) workaround
(generalize the string literal behind a fresh variable, run `cases`,
discharge the resulting absurd string equation by `decide`) closes
the dependent-elim failure for string literals.

Toy inductive parameterised by an `AsmOp` (the same shape as the
problematic `Copn` cases of `jasminSemTracedSingle`, minus the
`Located` complication). `cases h1; cases h2` directly fails on the
cross-pair "STORE64"/"CLONE_TOWER"; `generalize` + `decide` closes it. -/

private inductive ToyOpDeriv : AsmOp → Prop where
  | store64 : ToyOpDeriv { name := "STORE64" }
  | clone_tower : ToyOpDeriv { name := "CLONE_TOWER" }

private theorem toy_no_cross_store_clone
    (h1 : ToyOpDeriv { name := "STORE64" })
    (h2 : ToyOpDeriv { name := "STORE64" }) :
    True := by
  -- Without `generalize`, `cases h2` would fail on the clone_tower branch
  -- with "Failed to solve equation 'STORE64' = 'CLONE_TOWER'". With
  -- generalize, the literal becomes a free var that the eliminator
  -- handles cleanly.
  generalize hname : "STORE64" = nm at h2
  cases h2
  case store64 => trivial
  case clone_tower =>
    -- After generalize, h2's index uses `nm`. The clone_tower case
    -- forces `nm = "CLONE_TOWER"`, so combined with `hname : "STORE64" = nm`,
    -- we have `"STORE64" = "CLONE_TOWER"` — closeable by `decide`.
    exact absurd (hname.trans rfl : ("STORE64" : String) = "CLONE_TOWER")
      (by decide)

/-! ### Concrete determinism for the `assgn_parr_init` pair

The `towerTag` in the shared `InstrR` index pins the tower type on both
derivations via `byteSize_inj`. -/

theorem jasminSemTracedSingle.det_assgn_parr_init_pair {leafSpec : LeafSpec}
    {x : String} {n tag : Nat} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr n },
                              info := { towerTag := tag } })
                     .AT_none (.sarr n) (.Parr_init n))
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr n },
                              info := { towerTag := tag } })
                     .AT_none (.sarr n) (.Parr_init n))
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Both derivations invert to `assgn_parr_init`, recovering tower types
  -- `t`, `t'` with `t.byteSize = tag = t'.byteSize`; `byteSize_inj`
  -- gives `t = t'`.
  cases h1 <;> cases h2 <;>
    simp_all only [TowerType.byteSize_inj.eq_iff] <;>
    subst_vars <;> exact ⟨trivial, rfl⟩

/-! ### Concrete determinism for the `assgn_u64_zero` pair

Trivial: no TowerType in the index, no Located, no AsmOp. -/

theorem jasminSemTracedSingle.det_assgn_u64_zero_pair {leafSpec : LeafSpec}
    {x : String} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                              info := {} })
                     .AT_none (.sword .U64) (.Pconst 0))
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                              info := {} })
                     .AT_none (.sword .U64) (.Pconst 0))
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  cases h1 with
  | assgn_u64_zero _ _ =>
    cases h2 with
    | assgn_u64_zero _ _ => exact ⟨rfl, rfl⟩

theorem jasminSemTracedSingle.det_assgn_u64_val_pair {leafSpec : LeafSpec}
    {x : String} {v : Nat} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                              info := {} })
                     .AT_none (.sword .U64)
                     (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))))
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                              info := {} })
                     .AT_none (.sword .U64)
                     (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))))
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  cases h1 with
  | assgn_u64_val _ _ _ =>
    cases h2 with
    | assgn_u64_val _ _ _ => exact ⟨rfl, rfl⟩

/-! ### Helper: `locatedLookup` recovers `locDst` uniquely

Two `Located`s with the same `locVar`, both successfully looked up in the
same state, must agree on `locDst`. This is the missing piece for
`limb_store_oracle` determinism: after Option-1 lifting, we have
`loc1.locVar = loc2.locVar`; this lemma plus the lookup equations gives
`loc1.locDst = loc2.locDst`, closing the structural gap. -/

theorem locatedLookup_locDst_eq
    {rs : RustState} {loc1 loc2 : Located}
    (hVar : loc1.locVar = loc2.locVar)
    {v1 : RustVal loc1.locDst} {v2 : RustVal loc2.locDst}
    (hLk1 : locatedLookup rs loc1 = some v1)
    (hLk2 : locatedLookup rs loc2 = some v2) :
    loc1.locDst = loc2.locDst := by
  unfold locatedLookup at hLk1 hLk2
  rw [← hVar] at hLk2
  cases hT : rs.rsTower loc1.locVar with
  | none => rw [hT] at hLk1; cases hLk1
  | some s =>
    obtain ⟨t, val⟩ := s
    rw [hT] at hLk1 hLk2
    by_cases h1 : t = loc1.locDst
    · by_cases h2 : t = loc2.locDst
      · exact h1.symm.trans h2
      · simp [h2] at hLk2
    · simp [h1] at hLk1

/-! ### Determinism for `limb_store_oracle` pair

Same-constructor determinism for two `limb_store_oracle` derivations:
`loc1 = loc2` from the shared `locVar` plus the shared `towerTag`
(`byteSize_inj`), and the shared lookup forces `oldDestV1 = oldDestV2`. -/

theorem jasminSemTracedSingle.det_limb_store_oracle_pair {leafSpec : LeafSpec}
    {locVar' : String} {m mTag idx : Nat} {v : BitVec 64} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := locVar', vtype := .sarr m },
                            info := { towerTag := mTag } }]
                   .AT_none (.Oasm { name := "STORE64" })
                   [.Pvar { gv := { var := { vname := locVar', vtype := .sarr m },
                                     info := { towerTag := mTag } }, gs := false },
                    .Pconst idx, .Pconst v.toNat])
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := locVar', vtype := .sarr m },
                            info := { towerTag := mTag } }]
                   .AT_none (.Oasm { name := "STORE64" })
                   [.Pvar { gv := { var := { vname := locVar', vtype := .sarr m },
                                     info := { towerTag := mTag } }, gs := false },
                    .Pconst idx, .Pconst v.toNat])
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Generalizing the `AsmOp.name` literal and the `.Pconst v.toNat` index to
  -- fresh variables per hypothesis defeats the dependent-elimination failure, so
  -- `cases` discriminates to the single `limb_store_oracle` case; `loc1 = loc2`
  -- follows from the shared `locVar` and `towerTag` (`byteSize_inj.eq_iff`), and
  -- the shared lookup forces `oldDestV1 = oldDestV2`.
  generalize hop1 : (SOpn.Oasm { name := "STORE64" }) = op1 at h1
  generalize hop2 : (SOpn.Oasm { name := "STORE64" }) = op2 at h2
  generalize hv1 : v.toNat = vn1 at h1
  generalize hv2 : v.toNat = vn2 at h2
  cases h1 <;> cases h2 <;>
    simp_all only [BitVec.toNat_inj, reduceCtorEq, TowerType.byteSize_inj.eq_iff,
      Located.mk.injEq, and_true, true_and, and_self] <;>
    casesm* Located <;> subst_vars <;> simp_all [locatedUpdate, locatedLookup]

/-! ### Determinism for `clone_tower` pair

Two `clone_tower` derivations on the same InstrR. The InstrR fixes
`cloneVar`, `n`, `cloneTag`, `oldVar'`, `oldM`, `oldTag`; `cloneTy` is
recovered from `cloneTag = cloneTy.byteSize` via `byteSize_inj`. The
output state depends only on `cloneTy` and `oldVar'`, so determinism
follows. -/

theorem jasminSemTracedSingle.det_clone_tower_pair {leafSpec : LeafSpec}
    {cloneVar oldVar' : String} {oldM oldTag n cloneTag : Nat} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr n },
                            info := { towerTag := cloneTag } }] .AT_none
                   (.Oasm { name := "CLONE_TOWER" })
                   [.Pvar { gv := { var := { vname := oldVar', vtype := .sarr oldM },
                                     info := { towerTag := oldTag } }, gs := false }])
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr n },
                            info := { towerTag := cloneTag } }] .AT_none
                   (.Oasm { name := "CLONE_TOWER" })
                   [.Pvar { gv := { var := { vname := oldVar', vtype := .sarr oldM },
                                     info := { towerTag := oldTag } }, gs := false }])
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- `clone_tower` and `limb_store_oracle` share the outer `Copn` shape
  -- and differ only in the `AsmOp.name` literal (`"CLONE_TOWER"` vs
  -- `"STORE64"`), which Lean's eliminator cannot discriminate.
  -- Generalizing the `AsmOp.name` literal per hypothesis defeats that;
  -- `cases` discriminates to the single `clone_tower` case, where
  -- `cloneTy` is recovered from the shared `towerTag` via
  -- `byteSize_inj.eq_iff` and the output depends only on the shared
  -- `oldDest.locVar`.
  generalize hop1 : (SOpn.Oasm { name := "CLONE_TOWER" }) = op1 at h1
  generalize hop2 : (SOpn.Oasm { name := "CLONE_TOWER" }) = op2 at h2
  cases h1 <;> cases h2 <;>
    simp_all only [reduceCtorEq, TowerType.byteSize_inj.eq_iff, Located.mk.injEq,
      and_true, true_and, and_self] <;>
    casesm* Located <;> subst_vars <;> simp_all [rsSetTower, locatedLookup]

/-! ### Helpers for `call_oracle` determinism

`locToPExpr` is injective: it carries `locVar` in the variable name and
`locSrc.byteSize` in the `VarInfo.towerTag`, and `byteSize` is
injective. For two `args` lists producing the same
`args.map locToPExpr`, we get per-arg equality of `locVar` and
`locSrc`. -/

theorem locToPExpr_inj {a1 a2 : Located}
    (h : locToPExpr a1 = locToPExpr a2) :
    a1.locVar = a2.locVar ∧ a1.locSrc = a2.locSrc := by
  -- `locToPExpr loc = .Pvar { gv := { var := { vname := loc.locVar,
  --   vtype := towerToSType loc.locSrc },
  --   info := { towerTag := loc.locSrc.byteSize } }, gs := false }`.
  -- Unfolding gives `locVar` equality outright and towerTag equality;
  -- `byteSize_inj` recovers `a1.locSrc = a2.locSrc`.
  unfold locToPExpr locToGVar locToVar towerToSType at h
  injection h with hgv
  injection hgv with hv _
  injection hv with hvar hinfo
  injection hvar with hname _htype
  injection hinfo with htag
  exact ⟨hname, TowerType.byteSize_inj htag⟩

/-- `args.map locToPExpr` is injective on argument lists: two lists with
    the same `locToPExpr` images are equal.  `Located` has only the two
    fields `locVar`/`locSrc`, so per-index `locVar`+`locSrc` equality
    (from `locToPExpr_inj`) already pins the whole list down. -/
theorem map_locToPExpr_listInj :
    ∀ (l1 l2 : List Located), l1.map locToPExpr = l2.map locToPExpr →
      l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a1 :: as1, a2 :: as2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hHead, hTail⟩ := h
    obtain ⟨hVar, hSrc⟩ := locToPExpr_inj hHead
    have hLoc : a1 = a2 := by cases a1; cases a2; simp_all
    rw [hLoc, map_locToPExpr_listInj as1 as2 hTail]

/-- List-level: same `args.map locToPExpr` ⟹ same length + per-index
    `locVar` / `locSrc` equality. -/
theorem map_locToPExpr_inj :
    ∀ (l1 l2 : List Located), l1.map locToPExpr = l2.map locToPExpr →
      l1.length = l2.length ∧
      ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length),
        (l1.get ⟨i, h1⟩).locVar = (l2.get ⟨i, h2⟩).locVar ∧
        (l1.get ⟨i, h1⟩).locSrc = (l2.get ⟨i, h2⟩).locSrc
  | [], [], _ => ⟨rfl, fun i h1 _ => absurd h1 (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a1 :: as1, a2 :: as2, h => by
    simp [List.map] at h
    obtain ⟨hHead, hTail⟩ := h
    have ihTail := map_locToPExpr_inj as1 as2 hTail
    refine ⟨by simp [List.length, ihTail.1], ?_⟩
    intro i hi1 hi2
    cases i with
    | zero =>
      have := locToPExpr_inj hHead
      exact ⟨this.1, this.2⟩
    | succ k =>
      have hk1 : k < as1.length := by
        simp [List.length] at hi1; omega
      have hk2 : k < as2.length := by
        simp [List.length] at hi2; omega
      exact ihTail.2 k hk1 hk2

/-- If two derivations have the same per-arg `locVar` and the type-
    recovery hypothesis holds for both, then their per-arg `locDst`s
    agree (recovered from the shared `rs.rsTower a.locVar`). -/
theorem args_locDst_eq_at
    (rs : RustState) (a1 a2 : Located)
    (hVar : a1.locVar = a2.locVar)
    (h1 : ∃ v, rs.rsTower a1.locVar = some ⟨a1.locDst, v⟩)
    (h2 : ∃ v, rs.rsTower a2.locVar = some ⟨a2.locDst, v⟩) :
    a1.locDst = a2.locDst := by
  obtain ⟨v1, hv1⟩ := h1
  obtain ⟨v2, hv2⟩ := h2
  rw [← hVar] at hv2
  rw [hv1] at hv2
  exact ((Sigma.mk.injEq _ _ _ _).mp ((Option.some.injEq _ _).mp hv2)).1

/-! ### Determinism for `call_oracle` pair (Option-A closure)

Same-constructor determinism for two `call_oracle` derivations.
The `args.map (·.locDst)` is recovered via the new `hArgsTyped`
hypothesis (per-arg type-recovery) plus same-state lookup. -/

theorem jasminSemTracedSingle.det_call_oracle_pair {leafSpec : LeafSpec}
    {f destVar' : String} {destM destTag : Nat} {argEs : List PExpr}
    {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Ccall .DoNotInline
                    [.Lvar { var := { vname := destVar', vtype := .sarr destM },
                             info := { towerTag := destTag } }]
                    { name := f } argEs)
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Ccall .DoNotInline
                    [.Lvar { var := { vname := destVar', vtype := .sarr destM },
                             info := { towerTag := destTag } }]
                    { name := f } argEs)
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- `cases h1` unifies the shared `Ccall` argument-list index with
  -- `args1.map locToPExpr` (substituting the index away), so a direct
  -- second `cases h2` would have to solve
  -- `args1.map locToPExpr = args2.map locToPExpr` *as an index
  -- equation* — which Lean's dependent eliminator cannot decompose
  -- through the `List.map`/`locToPExpr` layer.
  -- Generalizing the `Ccall` argument-list index to a fresh variable per
  -- hypothesis defeats the dependent-elimination failure; `map_locToPExpr_listInj`
  -- then recovers `args1 = args2` from the shared `argEs`, and the rest closes as
  -- for the other constructors.
  generalize hg1 : argEs = ae1 at h1
  generalize hg2 : argEs = ae2 at h2
  cases h1 <;> cases h2 <;>
    first
    | (simp_all only [reduceCtorEq]; done)
    | (obtain rfl := map_locToPExpr_listInj _ _ (hg1.symm.trans hg2)
       simp_all only [reduceCtorEq, TowerType.byteSize_inj.eq_iff,
         Located.mk.injEq, and_true, true_and, and_self]
       casesm* Located <;> subst_vars <;> simp_all [rsSetTower, locatedLookup])

/-! ### Full mutual determinism

The mutual closure: `jasminSemTracedSingle.deterministic` and
`jasminSemTraced'.deterministic` proved together. Each `if_true` /
`if_false` case in the Single recurses into `Prime.deterministic` on
the inner branch; the `cons` case in Prime recurses into
`Single.deterministic` on the head. -/

mutual

/-- Single-step determinism: two `jasminSemTracedSingle` derivations on
    the same `InstrR` and input state agree on trace and output state.
    Each non-`Cif` constructor dispatches to its `det_*_pair` lemma; the
    `Cif` cases recurse into `jasminSemTraced'.deterministic` on the
    taken branch, and the `(if_true, if_false)` cross-pairs contradict
    on the shared scalar value. -/
theorem jasminSemTracedSingle.deterministic {leafSpec : LeafSpec}
    {i : InstrR} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec i rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec i rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 :=
  match h1, h2 with
  | .assgn_parr_init x t n tag rs hn htag, h2 =>
      jasminSemTracedSingle.det_assgn_parr_init_pair
        (.assgn_parr_init x t n tag rs hn htag) h2
  | .assgn_u64_zero x rs, h2 =>
      jasminSemTracedSingle.det_assgn_u64_zero_pair
        (.assgn_u64_zero x rs) h2
  | .assgn_u64_val x v rs, h2 =>
      jasminSemTracedSingle.det_assgn_u64_val_pair
        (.assgn_u64_val x v rs) h2
  | .if_true e ct cf rs rs1' v tInner hv hne hct, h2 => by
      cases h2 with
      | if_true _ _ _ _ _ v' tInner' hv' hne' hct' =>
          obtain ⟨hT, hS⟩ := jasminSemTraced'.deterministic hct hct'
          exact ⟨by rw [hT], hS⟩
      | if_false _ _ _ _ _ tInner' h0' hcf' =>
          exact absurd (hv.symm.trans h0') hne
  | .if_false e ct cf rs rs1' tInner h0 hcf, h2 => by
      cases h2 with
      | if_true _ _ _ _ _ v' tInner' hv' hne' hct' =>
          exact absurd (hv'.symm.trans h0) hne'
      | if_false _ _ _ _ _ tInner' h0' hcf' =>
          obtain ⟨hT, hS⟩ := jasminSemTraced'.deterministic hcf hcf'
          exact ⟨by rw [hT], hS⟩
  | .call_oracle f dest destVar' destM destTag args rs oldDestV argList
      hVar hM hTag hLk hArgs hArgsTyped, h2 =>
      jasminSemTracedSingle.det_call_oracle_pair
        (.call_oracle f dest destVar' destM destTag args rs oldDestV argList
          hVar hM hTag hLk hArgs hArgsTyped) h2
  | .limb_store_oracle loc locVar' m mTag idx v rs oldDestV
      hVar hM hTag hLk, h2 =>
      jasminSemTracedSingle.det_limb_store_oracle_pair
        (.limb_store_oracle loc locVar' m mTag idx v rs oldDestV
          hVar hM hTag hLk) h2
  | .clone_tower cv cloneTy oldDest oldVar' oldM oldTag n cloneTag rs
      hVar hM hOldTag hn hCloneTag, h2 =>
      jasminSemTracedSingle.det_clone_tower_pair
        (.clone_tower cv cloneTy oldDest oldVar' oldM oldTag n cloneTag rs
          hVar hM hOldTag hn hCloneTag) h2
termination_by sizeOf i
decreasing_by all_goals (simp_wf <;> omega)

/-- Cmd-level determinism: two `jasminSemTraced'` derivations on the
    same `Cmd` and input state agree on trace and output state. `nil`
    is immediate; `cons` uses single-step determinism on the head to
    align the intermediate states, then recurses on the tail. -/
theorem jasminSemTraced'.deterministic {leafSpec : LeafSpec}
    {body : Cmd} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTraced' leafSpec body rs t1 rs1)
    (h2 : jasminSemTraced' leafSpec body rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 :=
  match h1, h2 with
  | .nil rs, h2 => by cases h2; exact ⟨rfl, rfl⟩
  | .cons i is rs ta rsa tb rsb hS hR, h2 => by
      cases h2 with
      | cons _ _ _ ta' rsa' tb' _ hS' hR' =>
          obtain ⟨hta, hrsa⟩ := jasminSemTracedSingle.deterministic hS hS'
          subst hta
          subst hrsa
          obtain ⟨htb, hrsb⟩ := jasminSemTraced'.deterministic hR hR'
          subst htb
          exact ⟨rfl, hrsb⟩
termination_by sizeOf body
decreasing_by all_goals (simp_wf <;> omega)

end

/-! ### Lifting determinism to the original `jasminSemTraced`

Via the forward bridge `jasminSemTraced.toPrime`, determinism transfers
from `jasminSemTraced'` to `jasminSemTraced`. -/

theorem jasminSemTraced.deterministic {leafSpec : LeafSpec}
    {body : Cmd} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTraced leafSpec body rs t1 rs1)
    (h2 : jasminSemTraced leafSpec body rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 :=
  jasminSemTraced'.deterministic (jasminSemTraced.toPrime h1)
                                 (jasminSemTraced.toPrime h2)

/-- Non-traced determinism for `jasminSem`: derived via promotion to
    the traced form (`jasminSem.toTraced`) plus
    `jasminSemTraced.deterministic`. The trace component is forgotten
    in the conclusion since `jasminSem` doesn't carry it. -/
theorem jasminSem.deterministic {leafSpec : LeafSpec}
    {body : Cmd} {rs rs1 rs2 : RustState}
    (h1 : jasminSem leafSpec body rs rs1)
    (h2 : jasminSem leafSpec body rs rs2) :
    rs1 = rs2 := by
  obtain ⟨_, h1'⟩ := jasminSem.toTraced leafSpec h1
  obtain ⟨_, h2'⟩ := jasminSem.toTraced leafSpec h2
  exact (jasminSemTraced.deterministic h1' h2').2

/-! ### A1.18 — Determinism status

Determinism of the trace model is unconditional: every width-keyed
`InstrR` index also carries the ghost `VarInfo.towerTag`, so two
derivations on the same instruction recover the same tower type via
`byteSize_inj`. The per-pair lemmas
(`det_assgn_parr_init_pair`, `det_assgn_u64_zero_pair`,
`det_assgn_u64_val_pair`, `det_limb_store_oracle_pair`,
`det_clone_tower_pair`, `det_call_oracle_pair`) are hypothesis-free,
as are the mutual wrappers `jasminSemTracedSingle.deterministic` /
`jasminSemTraced'.deterministic` and the lifted
`jasminSemTraced.deterministic` / `jasminSem.deterministic`.

`call_oracle` determinism additionally relies on the per-arg
type-recovery side hypothesis
`(∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩)` carried
by the constructor itself (propagated through `RustExec.call`,
`RustExecTraced.call`, `jasminSem.call_oracle`, and
`jasminSemTraced.call_oracle`), which ties each argument's `locDst` to
the stored Sigma type; `locatedLookup_locDst_eq` and
`args_locDst_eq_at` recover the remaining `locDst` data from the
shared state. The `(if_true, if_false)` cross-pair contradicts on the
shared scalar value (`rs.rsScalar e = v ≠ 0` vs `rs.rsScalar e = 0`). -/

end CatCrypt.Crypto.SecureCompilation.JasminSemTraced
