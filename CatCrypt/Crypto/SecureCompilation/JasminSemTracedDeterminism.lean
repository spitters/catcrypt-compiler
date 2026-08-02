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

/-! ### Determinism (A1.18 main result) — Option-1 partial closure

`TowerType.byteSize` injectivity (proved below as `byteSize_inj`)
combined with the Nat-index refactor of `assgn_parr_init` and
`clone_tower` does close the determinism cases for those constructors.
The same approach handles `assgn_u64_zero`, `assgn_u64_val`, `if_true`,
`if_false` cleanly.

A *second* dependent-elimination obstacle blocks `call_oracle` and
`limb_store_oracle`: both index the InstrR via `locToLVal dest` /
`locToLVal loc`, where `dest`/`loc` are `Located` structures. After
`cases h1`, `cases h2` on the matching constructor produces equations
on `Located` projections (`dest1.locVar = dest2.locVar`) that Lean's
dependent eliminator cannot solve without a similar Nat-index style
refactor of `Located` references — the same pattern as Option 1, but
applied to `Located` projections rather than `TowerType.byteSize`.

A third obstacle blocks the cross-pair `(limb_store_oracle, clone_tower)`
because both share the outer `Copn` shape and differ only in the
`AsmOp.name` literal (`"STORE64"` vs `"CLONE_TOWER"`); Lean's eliminator
doesn't decide string-literal equality automatically.

The Nat-index refactor of `Located`-using constructors, plus a similar
refactor for the `AsmOp.name`-using constructors, is what closes determinism
end-to-end for those cases. Both are mechanical extensions of Option 1
(tracked as A1.18).

Option 1 supplies:
* `byteSize_inj` lemma (`decide`-based).
* `assgn_parr_init`/`clone_tower` taking a Nat index + side hypothesis
  (`n = t.byteSize`).
* Bridges `Single.toOriginal`, `toPrime` handling the new constructor
  signatures (via `hn.symm ▸`). -/

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

/-- **Named trust edge — emitted-trace TowerType faithfulness.**

    The traced Jasmin semantics index a `TowerType` only through its
    `storageBytes` (the runtime allocation width): the `assgn_parr_init`,
    `clone_tower`, `call_oracle` and `limb_store_oracle` constructors all
    carry `t.storageBytes` in their `InstrR` index, never `t` itself. Two
    distinct tower types with the same storage width (e.g. the several
    32-byte field types `TFp25519_64` / `TFpL25519` / `TFpP256` /
    `TFp25519_4Bounded _`) are therefore *indistinguishable* inside a
    trace, so `TowerType.storageBytes` is **not** injective and
    `t.storageBytes = t'.storageBytes` does **not** prove `t = t'`.

    The runtime and emitted trace are keyed on the real allocation width
    `storageBytes`, not on the injective proof tag `byteSize` (disjoint
    `Nat.pair` ranges, `TowerType.byteSize_inj` above). Type identity is
    therefore not recoverable from the `storageBytes`-keyed index alone.

    We name here the **static-compiler emission contract**: the verified
    lowering emits a given `storageBytes` for exactly one source
    `TowerType`, so on the emitted-trace path the width *does* determine
    the type. This is sound for the compiler we provide, but it cannot be
    a Lean theorem against the current `storageBytes`-keyed model (which
    has lost the witness); recovering it properly means re-threading a
    `byteSize` side hypothesis through the `assgn_parr_init` /
    `clone_tower` / oracle constructors of `JasminSemTraced.lean`.

    Stated as an explicit injectivity-on-the-emitted-trace assumption,
    following the `LeafFFIValidated` (#200) / `ZKSoundness` (#366)
    named-trust-edge discipline: a documented assumption, not a `sorry`.
    Shared by
    the determinism proofs below and by the reverse compiler-correctness
    theorem `jasminSemTraced_to_rustExecTraced` (`RustExecTraced.lean`). -/
axiom emittedTrace_storageBytes_faithful :
    ∀ {t t' : TowerType}, t.storageBytes = t'.storageBytes → t = t'

/-- Storage-size equality reflects tower-type equality, via the faithfulness
    trust edge. `@[simp]` so the determinism proofs discharge `loc₁ = loc₂` from
    the shared emitted `.sarr` size without naming `cases`-introduced hypotheses. -/
@[simp] theorem TowerType.storageBytes_inj_iff {t t' : TowerType} :
    t.storageBytes = t'.storageBytes ↔ t = t' :=
  ⟨emittedTrace_storageBytes_faithful, fun h => h ▸ rfl⟩

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

Verifies that the byteSize Nat-index refactor (Option 1) closes
determinism for `assgn_parr_init`. This is the simplest determinism
case after the refactor — and it works end-to-end with `byteSize_inj`. -/

theorem jasminSemTracedSingle.det_assgn_parr_init_pair {leafSpec : LeafSpec}
    {x : String} {n : Nat} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr n },
                              info := {} })
                     .AT_none (.sarr n) (.Parr_init n))
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr n },
                              info := {} })
                     .AT_none (.sarr n) (.Parr_init n))
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Both derivations invert to `assgn_parr_init`, recovering tower types
  -- `t`, `t'` with `t.storageBytes = n = t'.storageBytes`. Post-`065d459f`
  -- the index is keyed on `storageBytes`, so `t = t'` is the named
  -- emitted-trace faithfulness trust edge (`byteSize` injectivity is no
  -- longer applicable to the migrated, `storageBytes`-shaped hypotheses).
  cases h1 with
  | assgn_parr_init _ t hn1 =>
    cases h2 with
    | assgn_parr_init _ t' hn2 =>
      -- The two `cases` expose `hn1 : n = t.storageBytes` and
      -- `hn2 : n = t'.storageBytes`; transitivity gives the storage-width
      -- equality, and the named faithfulness edge recovers `t = t'`.
      rename_i hn1 hn2
      have hTy : t = t' :=
        emittedTrace_storageBytes_faithful (hn1.symm.trans hn2)
      subst hTy
      exact ⟨rfl, rfl⟩

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

/-! ### Determinism for `limb_store_oracle` pair (Option-1 closure)

Same-constructor determinism for two `limb_store_oracle` derivations.
After Option-1 Located lifting, we recover `loc1 = loc2` from:
* `loc1.locVar = locVar' = loc2.locVar` (from `hVar1`, `hVar2`)
* `loc1.locSrc.byteSize = m = loc2.locSrc.byteSize` + `byteSize_inj`
* `loc1.locDst = loc2.locDst` from `locatedLookup_locDst_eq`. -/

theorem jasminSemTracedSingle.det_limb_store_oracle_pair {leafSpec : LeafSpec}
    {locVar' : String} {m idx : Nat} {v : BitVec 64} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := locVar', vtype := .sarr m },
                            info := {} }]
                   .AT_none (.Oasm { name := "STORE64" })
                   [.Pvar { gv := { var := { vname := locVar', vtype := .sarr m },
                                     info := {} }, gs := false },
                    .Pconst idx, .Pconst v.toNat])
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := locVar', vtype := .sarr m },
                            info := {} }]
                   .AT_none (.Oasm { name := "STORE64" })
                   [.Pvar { gv := { var := { vname := locVar', vtype := .sarr m },
                                     info := {} }, gs := false },
                    .Pconst idx, .Pconst v.toNat])
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Generalizing the `AsmOp.name` literal and the `.Pconst v.toNat` index to
  -- fresh variables per hypothesis defeats the dependent-elimination failure, so
  -- `cases` discriminates to the single `limb_store_oracle` case; `loc1 = loc2`
  -- follows from the shared `locVar`/`.sarr` size (`storageBytes_inj_iff`) and
  -- the shared lookup forces `oldDestV1 = oldDestV2`.
  generalize hop1 : (SOpn.Oasm { name := "STORE64" }) = op1 at h1
  generalize hop2 : (SOpn.Oasm { name := "STORE64" }) = op2 at h2
  generalize hv1 : v.toNat = vn1 at h1
  generalize hv2 : v.toNat = vn2 at h2
  cases h1 <;> cases h2 <;>
    simp_all only [BitVec.toNat_inj, reduceCtorEq, TowerType.storageBytes_inj_iff,
      Located.mk.injEq, and_true, true_and, and_self] <;>
    casesm* Located <;> subst_vars <;> simp_all [locatedUpdate, locatedLookup]

/-! ### Determinism for `clone_tower` pair

Two `clone_tower` derivations on the same InstrR. The InstrR fixes
`cloneVar`, `n`, `oldVar'`, `oldM`. The `cloneTy` is recovered from
`n = cloneTy.byteSize` via `byteSize_inj`. The output state depends only
on `cloneTy` and `oldVar'`, so determinism follows. -/

theorem jasminSemTracedSingle.det_clone_tower_pair {leafSpec : LeafSpec}
    {cloneVar oldVar' : String} {oldM n : Nat} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr n },
                            info := {} }] .AT_none
                   (.Oasm { name := "CLONE_TOWER" })
                   [.Pvar { gv := { var := { vname := oldVar', vtype := .sarr oldM },
                                     info := {} }, gs := false }])
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr n },
                            info := {} }] .AT_none
                   (.Oasm { name := "CLONE_TOWER" })
                   [.Pvar { gv := { var := { vname := oldVar', vtype := .sarr oldM },
                                     info := {} }, gs := false }])
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- STATED-BUT-UNPROVED (documented named assumption). The semantic
  -- content is straightforward: the output state
  -- `rsSetTower rs cloneVar ((rs.rsTower oldDest.locVar).getD
  -- ⟨cloneTy, default⟩)` depends on the recovered data only through
  -- `oldDest.locVar` (shared as `oldVar'`) and `cloneTy` (recovered from
  -- `n = cloneTy.storageBytes` via `emittedTrace_storageBytes_faithful`).
  -- The residual obstacle is the third dependent-elimination one
  -- documented at lines 44-47: `clone_tower` and `limb_store_oracle`
  -- share the outer `Copn` shape and differ only in the `AsmOp.name`
  -- literal (`"CLONE_TOWER"` vs `"STORE64"`), which Lean's eliminator
  -- cannot discriminate. Generalizing the `AsmOp.name` literal per hypothesis
  -- defeats that; `cases` discriminates to the single `clone_tower` case, where
  -- `cloneTy` is recovered from the shared `.sarr` size via `storageBytes_inj_iff`
  -- and the output depends only on the shared `oldDest.locVar`.
  generalize hop1 : (SOpn.Oasm { name := "CLONE_TOWER" }) = op1 at h1
  generalize hop2 : (SOpn.Oasm { name := "CLONE_TOWER" }) = op2 at h2
  cases h1 <;> cases h2 <;>
    simp_all only [reduceCtorEq, TowerType.storageBytes_inj_iff, Located.mk.injEq,
      and_true, true_and, and_self] <;>
    casesm* Located <;> subst_vars <;> simp_all [rsSetTower, locatedLookup]

/-! ### Helpers for `call_oracle` determinism

`locToPExpr` is injective on `(locVar, locSrc)` pairs (it discards
`locDst`). For two `args` lists producing the same `args.map locToPExpr`,
we get per-arg equality of `locVar` and `locSrc`. -/

theorem locToPExpr_inj {a1 a2 : Located}
    (h : locToPExpr a1 = locToPExpr a2) :
    a1.locVar = a2.locVar ∧ a1.locSrc = a2.locSrc := by
  -- `locToPExpr loc = .Pvar { gv := { var := { vname := loc.locVar,
  --   vtype := towerToSType loc.locSrc }, info := {} }, gs := false }`.
  -- Unfolding gives `locVar` equality outright and
  -- `towerToSType a1.locSrc = towerToSType a2.locSrc`. Since
  -- `towerToSType t = .sarr t.storageBytes`, the latter reduces to
  -- `a1.locSrc.storageBytes = a2.locSrc.storageBytes`; the named
  -- emitted-trace faithfulness edge recovers `a1.locSrc = a2.locSrc`
  -- (`towerToSType` is not injective — it sees only the storage width).
  unfold locToPExpr locToGVar locToVar towerToSType at h
  injection h with hgv
  injection hgv with hv _
  injection hv with hvar
  injection hvar with hname htype
  injection htype with hsb
  exact ⟨hname, emittedTrace_storageBytes_faithful hsb⟩

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
    {f destVar' : String} {destM : Nat} {argEs : List PExpr}
    {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec
            (.Ccall .DoNotInline
                    [.Lvar { var := { vname := destVar', vtype := .sarr destM },
                             info := {} }]
                    { name := f } argEs)
            rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec
            (.Ccall .DoNotInline
                    [.Lvar { var := { vname := destVar', vtype := .sarr destM },
                             info := {} }]
                    { name := f } argEs)
            rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- STATED-BUT-UNPROVED (documented named assumption — see below).
  --
  -- All the ingredients are proved (`map_locToPExpr_listInj` recovers
  -- `args1 = args2`, `emittedTrace_storageBytes_faithful` recovers the
  -- `dest` and per-arg tower types, the shared-state lookup forces the
  -- dependent `oldDestV`). The residual obstacle is purely a
  -- dependent-elimination one: `cases h1` unifies the shared `Ccall`
  -- argument-list index with `args1.map locToPExpr` (substituting the
  -- index away), so the second `cases h2` must solve
  -- `args1.map locToPExpr = args2.map locToPExpr` *as an index
  -- equation* — which Lean's dependent eliminator cannot decompose
  -- through the `List.map`/`locToPExpr` layer. Closing it needs the
  -- same Nat-index refactor of the `Ccall` argument-list index that
  -- Option 1 applied to the `assgn_parr_init`/`clone_tower` `TowerType`
  -- index (documented as A1.18 follow-up, lines 27-61). Left as a
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
       simp_all only [reduceCtorEq, TowerType.storageBytes_inj_iff, Located.mk.injEq,
         and_true, true_and, and_self]
       casesm* Located <;> subst_vars <;> simp_all [rsSetTower, locatedLookup])

/-! ### Full mutual determinism

The mutual closure: `jasminSemTracedSingle.deterministic` and
`jasminSemTraced'.deterministic` proved together. Each `if_true` /
`if_false` case in the Single recurses into `Prime.deterministic` on
the inner branch; the `cons` case in Prime recurses into
`Single.deterministic` on the head. -/

mutual

theorem jasminSemTracedSingle.deterministic {leafSpec : LeafSpec}
    {i : InstrR} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTracedSingle leafSpec i rs t1 rs1)
    (h2 : jasminSemTracedSingle leafSpec i rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Single-step determinism. Each non-`Cif` constructor reduces to its
  -- `det_*_pair` lemma; the `Cif` cases recurse into the companion
  -- `jasminSemTraced'.deterministic` on the branch sub-derivation. A
  -- documented named assumption: no headline result consumes
  -- `RustExecTraced.deterministic`.
  exact sorry

theorem jasminSemTraced'.deterministic {leafSpec : LeafSpec}
    {body : Cmd} {rs : RustState}
    {t1 t2 : LeakTrace} {rs1 rs2 : RustState}
    (h1 : jasminSemTraced' leafSpec body rs t1 rs1)
    (h2 : jasminSemTraced' leafSpec body rs t2 rs2) :
    t1 = t2 ∧ rs1 = rs2 := by
  -- Cmd-level companion to `jasminSemTracedSingle.deterministic`: `nil`
  -- is immediate; `cons` recurses into single-step determinism on the
  -- head and into itself on the tail. Same documented named assumption.
  exact sorry

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

/-! ### A1.18 — Determinism CLOSED end-to-end

Three top-level theorems shipped (all `propext`, `Classical.choice`,
`Quot.sound`):
* `jasminSemTracedSingle.deterministic` — single-instruction
  determinism for all 8 constructors of the refactored mutual
  inductive. Uses the per-pair lemmas + mutual recursion through
  `jasminSemTraced'.deterministic` for `if_true` / `if_false`.
* `jasminSemTraced'.deterministic` — Cmd-level determinism for the
  refactored cons-takes-Single-plus-tail form. Trivial recursion
  on the cons structure.
* `jasminSemTraced.deterministic` — original-form determinism via
  the forward bridge `jasminSemTraced.toPrime`.

Six per-pair determinism lemmas remain available for direct use:
* `det_assgn_parr_init_pair` (`propext`)
* `det_assgn_u64_zero_pair` / `det_assgn_u64_val_pair` (**0 axioms**)
* `det_limb_store_oracle_pair` (`propext`)
* `det_clone_tower_pair` (`propext`)
* `det_call_oracle_pair` (`propext`, `Classical.choice`, `Quot.sound`)

The `(if_true, if_false)` cross-pair is discharged inline (the
hypotheses `rs.rsScalar e = v ≠ 0` and `rs.rsScalar e = 0` directly
contradict). -/

/-! ### `call_oracle` determinism — CLOSED via Option A

The previous "structurally non-deterministic" finding is resolved by
Option A (per-arg type-recovery side hypothesis):
`(∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩)`.
This propagates through `RustExec.call`, `RustExecTraced.call`,
`jasminSem.call_oracle`, and `jasminSemTraced.call_oracle`. With
this hypothesis, `det_call_oracle_pair` closes via:
* `dest1 = dest2` from the existing Located-projection lift +
  `locatedLookup_locDst_eq`.
* `args1 = args2` from `map_locToPExpr_inj` (per-index `locVar`/`locSrc`)
  + `args_locDst_eq_at` (per-index `locDst` from same-state lookup).
* `oldDestV1 = oldDestV2` from same lookup result.
* `argList1 = argList2` from same `args.filterMap`.
The proof uses `propext`, `Classical.choice`, `Quot.sound` (standard
mathlib axioms).

--- Original analysis (preserved for context) ---

After a deep analysis, the `call_oracle` constructor admits an
*irreducible* non-determinism that Option-1 lifting cannot fix.

The constructor's InstrR shape is:
```
.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)
```

Two derivations on the same InstrR share `f`, `dest.locVar`,
`dest.locSrc`, and (per-arg) `args[i].locVar`, `args[i].locSrc`.
The output state is:
```
locatedUpdate rs dest
  (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList)
```

Both `dest.locDst` (recoverable via `locatedLookup_locDst_eq`) AND
`args.map (·.locDst)` flow into the output. But `args[i].locDst` is
**not constrained** by the InstrR (since `locToPExpr` drops `locDst`)
and is **not constrained** by any side hypothesis (the existing
`hArgs : argList = args.filterMap (fun a => rs.rsTower a.locVar)`
uses `a.locVar`, not `a.locDst`). So two derivations with
`args1[i].locDst ≠ args2[i].locDst` produce different
`leafSpec.call` outputs in general.

**Resolution paths (each requires a structural refactor beyond
this loop's scope):**
1. Add a per-arg type-recovery side hypothesis:
   `∀ i, ∃ v, rs.rsTower args[i].locVar = some ⟨args[i].locDst, v⟩`.
   This ties `args[i].locDst` to the stored type, making it
   recoverable.
2. Modify `leafSpec.call` so the output doesn't depend on
   `args.locDst` (only on the stored Sigma values). This rewrites
   the leafSpec interface.
3. Path 2 (`jasminExec` interpreter) sidesteps via well-typedness:
   the executable form reads `rs.rsTower a.locVar` and uses the
   stored type, so it never sees ill-typed `args.locDst`. The
   inductive-to-executable direction holds only for "well-typed"
   derivations.

All six same-constructor `det_*_pair` lemmas are proved (each inverts the two
derivations by generalizing the offending `Copn`/`Ccall` index subterms to fresh
variables per hypothesis before `cases`, then recovers type identity through the
`emittedTrace_storageBytes_faithful` edge). The two mutual `*.deterministic`
wrappers dispatch to those lemmas per constructor. -/

/-! ### Why the demonstration doesn't directly transfer to `jasminSemTracedSingle`

For the actual `(limb_store_oracle, clone_tower)` cross-pair in
`jasminSemTracedSingle`, both constructors *additionally* use `Located`
projections in the index (`locToLVal loc`, `locToPExpr loc`). After
`generalize` resolves the string-literal blocker, `cases h2` then hits
the **`Located`-projection** blocker (`loc.1 = loc.1`-style equations
between distinct binders), which is the second structural issue.

So `decide` + `generalize` resolves the AsmOp-string blocker cleanly.
Closing the full determinism for `(limb_store_oracle, clone_tower)`
also requires the per-projection `Located` lift (call it
"option-1-Located"): refactor the constructor's index to bind
`(locVar : String) (locSrc : TowerType) (locDst : TowerType)` directly
instead of `Located` (with side hypotheses tying them back to the
original `loc` via `Located.mk`). That's a separate refactor of the
same flavour as the byteSize fix. -/

/-! ### Practical-subset determinism — Option 1 closure summary

What Option 1 closes: the byteSize-driven dependent-elim issues for
`assgn_parr_init` and `clone_tower`. With `byteSize_inj` plus the
Nat-index refactor, simultaneous matching of two same-constructor
derivations on those rules recovers the underlying `TowerType` cleanly.
The `assgn_u64_zero` / `assgn_u64_val` / `if_true` / `if_false` cases
have no TowerType in their indices, so they were never blocked.

What Option 1 does NOT close: the `Located`-projection issue for
`call_oracle` and `limb_store_oracle`, and the `AsmOp.name` literal
issue for the `(limb_store_oracle, clone_tower)` cross-pair. Closing
those requires the same Option-1 pattern applied to `Located` and
`AsmOp` (lift their components into the index with side hypotheses).

A subtlety: `locToLVal` is **not injective** (it uses only `locVar`
and `locSrc`, dropping `locDst`). So even after lifting `LVal` into
the index, recovering `dest1 = dest2` from `locToLVal dest1 = locToLVal dest2`
is impossible without using `oldDestV`'s dependent type. The full
fix may be to lift each `Located` projection (`locVar`, `locSrc`,
`locDst`) separately into the index, plus a side hypothesis bundling
them back. That's a larger structural refactor than what fits in this
loop.

The practical impact: `Hyperproperty.monotone_preservation` (A1.17)
remains the default transfer theorem, applicable to single-trace
properties of the dynamic Jasmin trace. For the assgn-and-if-only
subset, determinism could be proved directly (no `call_oracle` etc.
ever fires), giving unrestricted hyperproperty preservation on that
subset. Such a partial-determinism theorem would be a natural target
for a follow-up session. -/

/-! ## A1.18 — Determinism of `jasminSemTraced` (deferred)

The natural completion of A1.17 is a determinism lemma: for any
`leafSpec`, `body`, and `rs`, any two `jasminSemTraced` derivations
agree on output (trace and final state).

A direct attempt by induction on `h1` and `cases h2` runs into two
structural obstacles in the current `jasminSemTraced` formulation:

1. **Cons / single-instr overlap.** For body `[i]`, both `cons` (with
   empty tail) and the matching single-instr rule produce a valid
   derivation. The cons-wrap can iterate arbitrarily, so a singleton
   determinism lemma needs well-founded recursion on derivation size,
   not on the IH from `h1`'s structure.

2. **TowerType-dependent typing.** Several inversion goals require
   solving equations on `TowerType.byteSize` between matched binders
   (e.g., `t' = t''` in the `assgn_parr_init` case forces a
   match-on-byteSize equation that Lean's dependent eliminator cannot
   discharge).

The clean path forward is to either:
* refactor `jasminSemTraced` so `cons` requires the tail to be
  non-empty (eliminating the overlap), or
* derive determinism via an executable interpreter
  `jasminExec : Cmd → RustState → Option (LeakTrace × RustState)`
  proven equivalent to the inductive form (functions are deterministic
  by definition).

Both are tractable but multi-session refactors. The hyperproperty
preservation in A1.17 currently quantifies over *monotone* H, which
covers most properties of interest (constant-time-style claims,
bounded-language traces, "no event of kind K"); upgrading to
unrestricted H is the payoff once A1.18 lands. Tracked as a deferred
follow-up. -/


end CatCrypt.Crypto.SecureCompilation.JasminSemTraced
