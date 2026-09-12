/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta_Discharge

/-!
# H3 Blocker 1: match tuple-destructure simulation

Discharges the 2-output tuple-destructure simulation case
(`Hyp_match_full`) for the H3.quarta layer.

The source-side pattern is

```
match f(args) with | (n1, n2) => body
```

which `haxToLowCT` lowers to

```
RLetZero n1 dt (RLetZero n2 dt (RSeq (RCallSwap f d1 d2 args') bodyC))
```

This file lands:

* `LeafCallAgreesTowerSwap` — 2-output analogue of `LeafCallAgreesTower`.
* `evalImp_match_tuple_app_inv` — source-side inverse for the
  `.match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)]`
  arm.
* `haxToLowCT_match_tuple_app_some` — syntactic unpacker.
* `haxToLowCT_simulates_match_tuple_app_full` — main simulation
  theorem under the `HaxToLowCTSimulatesFull` predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType Value Env Outcome Builtins denote)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  `LeafCallAgreesTowerSwap`

The 2-output analogue of `LeafCallAgreesTower`.  Given a leaf `f` whose
Builtins-side call returns a 2-tuple value `.tuple [v1, v2]`, the
`RCallSwap`-lowered version produces a state in which each of the two
destination slots is bridge-aligned with the corresponding component
of the source-side tuple.

Per `RustExec.callSwap`'s definition, `RCallSwap f d1 d2 args` runs
two sequential `RCall` steps (one per destination), reusing the same
args list.  The bridge therefore relates `v1` (resp. `v2`) to the
RustVal stored at `d1` (resp. `d2`) after both calls complete.

This is a consumer-supplied per-leaf assumption: a concrete `LeafSpec`
implementing a 2-output primitive (e.g. `cswap`) populates it. -/

/-- Per-leaf tower-swap agreement predicate.  Given a leaf `f` returning
    a two-component value, either `.tuple [v1, v2]` or `.array [v1, v2]`
    (the two values a `tuplePat` of length 2 matches), the two `RCallSwap`
    outputs at `dest1` and `dest2` are bridge-aligned with `v1` and `v2`. -/
def LeafCallAgreesTowerSwap
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (bridge : ValueTowerBridge) : Prop :=
  ∀ (rs : RustState) (dest1 dest2 : String) (args : List Located)
    (vals : List Value) (vRes : Value) (v1 v2 : Value),
    bi f vals = some vRes →
    (vRes = .tuple [v1, v2] ∨ vRes = .array [v1, v2]) →
    (∀ a ∈ args, ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩) →
    ∀ rs', RustExec 0 leafSpec
             (.RCallSwap f { locVar := dest1, locSrc := dt }
                         { locVar := dest2, locSrc := dt } args) rs rs' →
    (∃ val1, rs'.rsTower dest1 = some ⟨dt, val1⟩ ∧ bridge dt v1 val1)
    ∧ (∃ val2, rs'.rsTower dest2 = some ⟨dt, val2⟩ ∧ bridge dt v2 val2)

/-! ## §2  Syntactic unpacker for `match_ (app f args) [(tuplePat .., body)]`

Companion to `haxToLowCT_letBind_app_some` for the tuple-destructure
arm. -/

/-- Unpack the syntactic translation for the
    `.match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)]`
    arm.  Yields the translated body, the translated argument list, and
    the assembled `RLetZero + RLetZero + RSeq (RCallSwap ..) bodyC` shape. -/
theorem haxToLowCT_match_tuple_app_some
    (f : String) (args : List ImpExpr) (n1 n2 : String)
    (body : ImpExpr) (c : LowCT)
    (h : haxToLowCT
            (.match_ (.app f args)
              [(.tuplePat [.varPat n1, .varPat n2], body)]) = some c) :
    ∃ (args' : List Located) (bodyC : LowCT),
      haxArgsToLocated (towerOfCallName f) args = some args' ∧
      haxToLowCT body = some bodyC ∧
      c = .RLetZero n1 (towerOfCallName f)
            (.RLetZero n2 (towerOfCallName f)
              (.RSeq (.RCallSwap f
                       { locVar := n1, locSrc := towerOfCallName f }
                       { locVar := n2, locSrc := towerOfCallName f }
                       args')
                     bodyC)) := by
  simp only [haxToLowCT] at h
  cases hArgs : haxArgsToLocated (towerOfCallName f) args with
  | none => simp [hArgs] at h
  | some args' =>
    cases hBody : haxToLowCT body with
    | none => simp [hArgs, hBody] at h
    | some bodyC =>
      simp [hArgs, hBody] at h
      exact ⟨args', bodyC, rfl, rfl, h.symm⟩

/-! ## §3  Source-side inverse for `match_ (.app f args) [(tuplePat ..)]`

When all `args` are plain `.var` lookups, the source-side evaluation
of `match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)]`
decomposes into:

* `bi f vals = some vRes` where `vRes = .tuple [v1, v2]` or
  `vRes = .array [v1, v2]` (`matchPat` matches a `tuplePat` against both);
* `body` runs in the env extended at `n1 ↦ v1` and `n2 ↦ v2`.
-/

theorem evalImp_match_tuple_app_inv
    (bi : Builtins) (fuel : Nat)
    (f : String) (args : List ImpExpr) (n1 n2 : String) (body : ImpExpr)
    (env : Env) (v : Value) (env' : Env)
    (hVars : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (h : evalImp bi fuel
           (.match_ (.app f args)
             [(.tuplePat [.varPat n1, .varPat n2], body)]) env
         = some (v, env')) :
    ∃ vals vRes v1 v2,
      AllVars env args vals ∧
      bi f vals = some vRes ∧
      (vRes = .tuple [v1, v2] ∨ vRes = .array [v1, v2]) ∧
      evalImp bi fuel body
        (Env.extend (Env.extend env n1 v1) n2 v2) = some (v, env') := by
  -- Build the AllVars witness for the args.
  obtain ⟨vals, hAV⟩ := allVars_of_forall env args hVars
  have hda := denoteArgs_vars bi fuel env hAV
  -- Unfold evalImp at h; reduce through the .match_ -> .app cascade.
  unfold evalImp at h
  simp only [denote, bind, Bind.bind, StateT.bind, StateT.run,
             pure, Pure.pure] at h
  -- Normalise denoteArgs on hAV to match the shape in h.
  simp only [StateT.run] at hda
  rw [hda] at h
  dsimp only at h
  -- Case on bi f vals.
  cases hbi : bi f vals with
  | none =>
    rw [hbi] at h
    simp [pure, Pure.pure, StateT.pure] at h
  | some vRes =>
    rw [hbi] at h
    -- Unfold denoteMatchArms once for the single-arm list.
    simp only [Hax.denoteMatchArms, bind, Bind.bind, StateT.bind,
               get, getThe, MonadStateOf.get, StateT.get,
               pure, Pure.pure, StateT.pure,
               set, MonadStateOf.set] at h
    -- Case on vRes: `.tuple [v1, v2]` and `.array [v1, v2]` match.  Other
    -- constructors collapse matchPat to none, leaving the err arm of
    -- denoteMatchArms.
    cases vRes with
    | tuple vs =>
      cases vs with
      | nil =>
        simp only [Hax.matchPat, List.length_cons, List.length_nil,
                   bne_iff_ne, ne_eq] at h
        rw [if_pos (by decide : ¬ (0 + 1 + 1 = 0))] at h
        simp [StateT.pure] at h
      | cons v1 vs1 =>
        cases vs1 with
        | nil =>
          simp only [Hax.matchPat, List.length_cons, List.length_nil,
                     bne_iff_ne, ne_eq] at h
          rw [if_pos (by decide : ¬ (0 + 1 + 1 = 0 + 1))] at h
          simp [StateT.pure] at h
        | cons v2 vs2 =>
          cases vs2 with
          | nil =>
            -- matchPat succeeds.
            simp only [Hax.matchPat, Hax.matchPat.matchPatList,
                       List.length_cons, List.length_nil, bne_iff_ne, ne_eq] at h
            refine ⟨vals, _, v1, v2, hAV, hbi, Or.inl rfl, ?_⟩
            unfold evalImp
            exact h
          | cons w ws =>
            simp only [Hax.matchPat, List.length_cons, List.length_nil,
                       bne_iff_ne, ne_eq] at h
            rw [if_pos (by omega : ¬ (0 + 1 + 1 = ws.length + 1 + 1 + 1))] at h
            simp [StateT.pure] at h
    | array vs =>
      cases vs with
      | nil =>
        simp only [Hax.matchPat, List.length_cons, List.length_nil,
                   bne_iff_ne, ne_eq] at h
        rw [if_pos (by decide : ¬ (0 + 1 + 1 = 0))] at h
        simp [StateT.pure] at h
      | cons v1 vs1 =>
        cases vs1 with
        | nil =>
          simp only [Hax.matchPat, List.length_cons, List.length_nil,
                     bne_iff_ne, ne_eq] at h
          rw [if_pos (by decide : ¬ (0 + 1 + 1 = 0 + 1))] at h
          simp [StateT.pure] at h
        | cons v2 vs2 =>
          cases vs2 with
          | nil =>
            -- matchPat succeeds.
            simp only [Hax.matchPat, Hax.matchPat.matchPatList,
                       List.length_cons, List.length_nil, bne_iff_ne, ne_eq] at h
            refine ⟨vals, _, v1, v2, hAV, hbi, Or.inr rfl, ?_⟩
            unfold evalImp
            exact h
          | cons w ws =>
            simp only [Hax.matchPat, List.length_cons, List.length_nil,
                       bne_iff_ne, ne_eq] at h
            rw [if_pos (by omega : ¬ (0 + 1 + 1 = ws.length + 1 + 1 + 1))] at h
            simp [StateT.pure] at h
    | int _ => simp [Hax.matchPat, StateT.pure] at h
    | uint _ _ => simp [Hax.matchPat, StateT.pure] at h
    | sint _ _ => simp [Hax.matchPat, StateT.pure] at h
    | bool _ => simp [Hax.matchPat, StateT.pure] at h
    | unit => simp [Hax.matchPat, StateT.pure] at h
    | option _ => simp [Hax.matchPat, StateT.pure] at h
    | result _ _ => simp [Hax.matchPat, StateT.pure] at h
    | controlFlow _ _ => simp [Hax.matchPat, StateT.pure] at h

/-! ## §4  Goal 3 (main): match-tuple-app simulation under Full predicate

The proof structure:

1. Unpack the syntactic translation via `haxToLowCT_match_tuple_app_some`.
2. Use `evalImp_match_tuple_app_inv` to decompose the source-side
   evaluation into `bi f vals = some vRes` with `vRes` either
   `.tuple [v1, v2]` or `.array [v1, v2]`, plus the body evaluation.
3. Build the `RLetZero + RLetZero + RSeq (RCallSwap ..) bodyC` execution.
4. Apply `LeafCallAgreesTowerSwap` to get tower agreement for `n1`, `n2`.
5. Apply `envAgreesRustFull_extend_tower` twice to lift agreement
   across both bindings.
6. Apply the body IH to close the rest.
-/

theorem haxToLowCT_simulates_match_tuple_app_full
    (bridge : ValueTowerBridge)
    (bi : Builtins) (fuel : Nat) (leafSpec : LeafSpec)
    (f : String) (args : List ImpExpr) (n1 n2 : String) (body : ImpExpr)
    (c : LowCT) (env env' : Env) (rs : RustState) (v : Value)
    (hLeaf : LeafCallAgreesTowerSwap bi leafSpec f (towerOfCallName f) bridge)
    (hArgsEnv : ∀ a ∈ args, ∃ n, a = .var n ∧ ∃ w, env n = some w)
    (hArgsBound :
       ∀ args', haxArgsToLocated (towerOfCallName f) args = some args' →
       ArgsTowerBound rs args')
    (hArgsFresh :
       ∀ args', haxArgsToLocated (towerOfCallName f) args = some args' →
       ∀ a ∈ args', a.locVar ≠ n1 ∧ a.locVar ≠ n2)
    (hDistinct : n1 ≠ n2)
    (hCompScalar :
       ∀ vals vRes v1 v2,
         bi f vals = some vRes →
         (vRes = .tuple [v1, v2] ∨ vRes = .array [v1, v2]) →
         valueToScalar v1 = none ∧ valueToScalar v2 = none)
    (ihBody : ∀ c' env_a env_b rs_a v_a,
                HaxToLowCTSimulatesFull bridge bi fuel 0 leafSpec
                  body c' env_a env_b rs_a v_a) :
    HaxToLowCTSimulatesFull bridge bi fuel 0 leafSpec
      (.match_ (.app f args)
        [(.tuplePat [.varPat n1, .varPat n2], body)])
      c env env' rs v := by
  intro hHax hEval hAgreeFull
  -- §1: Unpack syntactic translation.
  obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
    haxToLowCT_match_tuple_app_some f args n1 n2 body c hHax
  subst hC
  -- §2: Source-side decomposition.
  obtain ⟨vals, vRes, v1, v2, _hAV, hBi, hvRes, hBodyEval⟩ :=
    evalImp_match_tuple_app_inv bi fuel f args n1 n2 body env v env'
      hArgsEnv hEval
  -- §3: Specialise args/fresh/scalar hypotheses.
  have hAB : ArgsTowerBound rs args' := hArgsBound args' hArgsT
  have hAF : ∀ a ∈ args', a.locVar ≠ n1 ∧ a.locVar ≠ n2 := hArgsFresh args' hArgsT
  have hAF1 : ∀ a ∈ args', a.locVar ≠ n1 := fun a ha => (hAF a ha).1
  have hAF2 : ∀ a ∈ args', a.locVar ≠ n2 := fun a ha => (hAF a ha).2
  obtain ⟨hScalar1, hScalar2⟩ := hCompScalar vals vRes v1 v2 hBi hvRes
  -- §4: Set up.
  set dt := towerOfCallName f with hdt_def
  set dest1 : Located := { locVar := n1, locSrc := dt } with hdest1_def
  set dest2 : Located := { locVar := n2, locSrc := dt } with hdest2_def
  -- After RLetZero n1 dt, rs becomes rs1 := rsSetTower rs n1 ⟨dt, default⟩.
  -- After RLetZero n2 dt, rs1 becomes rs2 := rsSetTower rs1 n2 ⟨dt, default⟩.
  set rs1 := rsSetTower rs n1 ⟨dt, default⟩ with hrs1_def
  set rs2 := rsSetTower rs1 n2 ⟨dt, default⟩ with hrs2_def
  -- §5: Args remain tower-bound after both letZeros (via freshness).
  have hAB1 : ArgsTowerBound rs1 args' :=
    ArgsTowerBound_preserved_extend rs args' n1 ⟨dt, default⟩ hAF1 hAB
  have hAB2 : ArgsTowerBound rs2 args' :=
    ArgsTowerBound_preserved_extend rs1 args' n2 ⟨dt, default⟩ hAF2 hAB1
  -- §6: Both dest slots are looked up to `some default` on rs2.
  -- For rs2.rsTower n1 we need to dive past the n2 set (since n1 ≠ n2).
  have hRs2N1 : rs2.rsTower n1 = some ⟨dt, default⟩ := by
    show (rsSetTower rs1 n2 ⟨dt, default⟩).rsTower n1 = some ⟨dt, default⟩
    unfold rsSetTower
    have hne : (n1 == n2) = false := beq_eq_false_iff_ne.mpr hDistinct
    simp [hne]
    show rs1.rsTower n1 = some ⟨dt, default⟩
    unfold rs1 rsSetTower
    simp
  have hRs2N2 : rs2.rsTower n2 = some ⟨dt, default⟩ := by
    show (rsSetTower rs1 n2 ⟨dt, default⟩).rsTower n2 = some ⟨dt, default⟩
    unfold rsSetTower
    simp
  have hLookup1Rs2 : locatedLookup rs2 dest1 = some default := by
    unfold locatedLookup
    show (match rs2.rsTower n1 with
          | some ⟨t, v⟩ => if h : t = dt then some (h ▸ v) else none
          | none => none) = some default
    rw [hRs2N1]
    simp
  have hLookup2Rs2 : locatedLookup rs2 dest2 = some default := by
    unfold locatedLookup
    show (match rs2.rsTower n2 with
          | some ⟨t, v⟩ => if h : t = dt then some (h ▸ v) else none
          | none => none) = some default
    rw [hRs2N2]
    simp
  -- §7: Build the call argList and rs after the swap.
  -- The RCallSwap step runs RCall(dest1) ; RCall(dest2).
  set argList1 := args'.filterMap (fun a => rs2.rsTower a.locVar) with hargList1_def
  set newVal1 := leafSpec.call f dt (args'.map (·.locDst)) (default : RustVal dt)
                   argList1 with hnewVal1_def
  set rs3 := locatedUpdate rs2 dest1 newVal1 with hrs3_def
  -- Args are still tower-bound on rs3 (we only updated n1's slot).
  have hAB3 : ArgsTowerBound rs3 args' :=
    ArgsTowerBound_preserved_extend rs2 args' n1 ⟨dt, newVal1⟩ hAF1 hAB2
  -- §8: The dest2 lookup on rs3 is still `some default` (we updated dest1's slot).
  have hRs3N2 : rs3.rsTower n2 = some ⟨dt, default⟩ := by
    show (locatedUpdate rs2 dest1 newVal1).rsTower n2 = some ⟨dt, default⟩
    unfold locatedUpdate rsSetTower
    simp [hdest1_def, Ne.symm hDistinct]
    exact hRs2N2
  have hLookup2Rs3 : locatedLookup rs3 dest2 = some (default : RustVal dt) := by
    unfold locatedLookup
    show (match rs3.rsTower n2 with
          | some ⟨t, v⟩ => if h : t = dt then some (h ▸ v) else none
          | none => none) = some default
    rw [hRs3N2]
    simp
  -- §9: Build the second RCall step.  argList2 uses rs3.
  set argList2 := args'.filterMap (fun a => rs3.rsTower a.locVar) with hargList2_def
  set newVal2 := leafSpec.call f dt (args'.map (·.locDst)) (default : RustVal dt)
                   argList2 with hnewVal2_def
  set rs4 := locatedUpdate rs3 dest2 newVal2 with hrs4_def
  -- §10: Construct the RustExec.callSwap step.
  have hCallArgs1 : ∀ a ∈ args', ∃ vv, rs2.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
    hAB2
  have hCallArgs2 : ∀ a ∈ args', ∃ vv, rs3.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
    hAB3
  have hCall1 : RustExec 0 leafSpec (.RCall f dest1 args') rs2 rs3 :=
    RustExec.call (N := 0) (leafSpec := leafSpec)
      f dest1 args' rs2 default argList1 hLookup1Rs2 rfl hCallArgs1
  have hCall2 : RustExec 0 leafSpec (.RCall f dest2 args') rs3 rs4 :=
    RustExec.call (N := 0) (leafSpec := leafSpec)
      f dest2 args' rs3 default argList2 hLookup2Rs3 rfl hCallArgs2
  have hCallSwap : RustExec 0 leafSpec
      (.RCallSwap f dest1 dest2 args') rs2 rs4 :=
    RustExec.callSwap f dest1 dest2 args' rs2 rs3 rs4 hCall1 hCall2
  -- §11: Apply the leaf-swap-agreement to extract bridge facts on rs4.
  have hLeafAgr := hLeaf rs2 n1 n2 args' vals vRes v1 v2 hBi hvRes hCallArgs1
                    rs4 hCallSwap
  obtain ⟨⟨val1, hVal1, hBridge1⟩, ⟨val2, hVal2, hBridge2⟩⟩ := hLeafAgr
  -- §12: Lift agreement to rs4, in two stages, against (env.extend n1 v1).extend n2 v2.
  -- First lift env -> env.extend n1 v1.
  -- We need an intermediate rs that matches the env.extend n1 v1 step.
  -- Strategy: rs4 has n1 |-> ⟨dt, val1⟩ and n2 |-> ⟨dt, val2⟩.
  -- We'll show envAgreesRustFull bridge ((env.extend n1 v1).extend n2 v2) rs4
  -- by reducing rs4 to (rsSetTower (rsSetTower rs n1 ⟨dt, val1⟩) n2 ⟨dt, val2⟩).
  have hRs4Eq : rs4 = rsSetTower (rsSetTower rs n1 ⟨dt, val1⟩) n2 ⟨dt, val2⟩ := by
    -- val1 is rs4's tower at n1, val2 is rs4's tower at n2.
    -- Reconstruct rs4 via collapse:
    -- rs4 = locatedUpdate rs3 dest2 newVal2 = rsSetTower rs3 n2 ⟨dt, newVal2⟩
    -- rs3 = rsSetTower rs2 n1 ⟨dt, newVal1⟩
    -- rs2 = rsSetTower rs1 n2 ⟨dt, default⟩
    -- rs1 = rsSetTower rs n1 ⟨dt, default⟩
    -- We need to extract val1 = newVal1 and val2 = newVal2 from hVal1 and hVal2.
    -- hVal1 : rs4.rsTower n1 = some ⟨dt, val1⟩.
    -- Compute rs4.rsTower n1 by unfolding.
    have hLookupRs4N1 : rs4.rsTower n1 = some ⟨dt, newVal1⟩ := by
      show (locatedUpdate rs3 dest2 newVal2).rsTower n1 = some ⟨dt, newVal1⟩
      unfold locatedUpdate rsSetTower
      simp [hdest2_def, hDistinct]
      show (locatedUpdate rs2 dest1 newVal1).rsTower n1 = some ⟨dt, newVal1⟩
      unfold locatedUpdate rsSetTower
      simp [hdest1_def]
    have hLookupRs4N2 : rs4.rsTower n2 = some ⟨dt, newVal2⟩ := by
      show (locatedUpdate rs3 dest2 newVal2).rsTower n2 = some ⟨dt, newVal2⟩
      unfold locatedUpdate rsSetTower
      simp [hdest2_def]
    rw [hLookupRs4N1] at hVal1
    rw [hLookupRs4N2] at hVal2
    -- hVal1 : some ⟨dt, newVal1⟩ = some ⟨dt, val1⟩.
    have h1 : val1 = newVal1 := by rcases hVal1 with ⟨_⟩; rfl
    have h2 : val2 = newVal2 := by rcases hVal2 with ⟨_⟩; rfl
    rw [h1, h2]
    -- Now show rs4 = rsSetTower (rsSetTower rs n1 ⟨dt, newVal1⟩) n2 ⟨dt, newVal2⟩.
    -- Use the rsSetTower_collapse lemma twice.
    -- rs4 = rsSetTower rs3 n2 ⟨dt, newVal2⟩
    -- rs3 = rsSetTower rs2 n1 ⟨dt, newVal1⟩
    -- rs2 = rsSetTower rs1 n2 ⟨dt, default⟩
    -- rs1 = rsSetTower rs n1 ⟨dt, default⟩
    have hExpand : rs4 = rsSetTower (rsSetTower (rsSetTower (rsSetTower rs
                          n1 ⟨dt, default⟩) n2 ⟨dt, default⟩) n1 ⟨dt, newVal1⟩)
                          n2 ⟨dt, newVal2⟩ := by
      show rs4 = rsSetTower (rsSetTower (rsSetTower rs1 n2 ⟨dt, default⟩)
                              n1 ⟨dt, newVal1⟩) n2 ⟨dt, newVal2⟩
      show rs4 = rsSetTower (rsSetTower rs2 n1 ⟨dt, newVal1⟩) n2 ⟨dt, newVal2⟩
      show rs4 = rsSetTower rs3 n2 ⟨dt, newVal2⟩
      show locatedUpdate rs3 dest2 newVal2
           = rsSetTower rs3 n2 ⟨dt, newVal2⟩
      rfl
    rw [hExpand]
    -- Want: rsSetTower (rsSetTower (rsSetTower (rsSetTower rs
    --        n1 ⟨dt, default⟩) n2 ⟨dt, default⟩) n1 ⟨dt, newVal1⟩) n2 ⟨dt, newVal2⟩
    --      = rsSetTower (rsSetTower rs n1 ⟨dt, newVal1⟩) n2 ⟨dt, newVal2⟩
    -- By commutativity over distinct names (n1 ≠ n2) + collapse.
    rcases rs with ⟨t, s⟩
    simp only [rsSetTower]
    congr 1
    funext y
    by_cases hy1 : y = n1
    · subst hy1
      have hne : ¬ y = n2 := fun h => hDistinct (h.symm ▸ rfl)
      simp [hne]
    · by_cases hy2 : y = n2
      · subst hy2
        simp
      · simp [hy1, hy2]
  -- §13: Now lift agreement across the two bindings.
  -- env_mid := env.extend n1 v1.
  -- rs_mid := rsSetTower rs n1 ⟨dt, val1⟩.
  have hAgreeMid : envAgreesRustFull bridge (Env.extend env n1 v1)
                    (rsSetTower rs n1 ⟨dt, val1⟩) :=
    envAgreesRustFull_extend_tower bridge env rs n1 v1 dt val1
      hAgreeFull hBridge1 hScalar1
  -- Then lift to env_mid.extend n2 v2 and rs_mid' = rsSetTower rs_mid n2 ⟨dt, val2⟩.
  have hAgreeFinal : envAgreesRustFull bridge
        (Env.extend (Env.extend env n1 v1) n2 v2)
        (rsSetTower (rsSetTower rs n1 ⟨dt, val1⟩) n2 ⟨dt, val2⟩) :=
    envAgreesRustFull_extend_tower bridge (Env.extend env n1 v1)
      (rsSetTower rs n1 ⟨dt, val1⟩) n2 v2 dt val2 hAgreeMid hBridge2 hScalar2
  -- Rewrite using hRs4Eq.
  have hAgreeRs4 : envAgreesRustFull bridge
      (Env.extend (Env.extend env n1 v1) n2 v2) rs4 := by
    rw [hRs4Eq]; exact hAgreeFinal
  -- §14: Apply the body IH.
  obtain ⟨rs', hBodyExec, hAgree'⟩ :=
    ihBody bodyC (Env.extend (Env.extend env n1 v1) n2 v2) env' rs4 v
           hBodyT hBodyEval hAgreeRs4
  -- §15: Chain the executions: letZero n1 + letZero n2 + (callSwap ; bodyC).
  refine ⟨rs', ?_, hAgree'⟩
  refine RustExec.letZero n1 dt _ rs rs' ?_
  -- After RLetZero n1, state is rs1.  Need: RustExec 0 leafSpec
  -- (RLetZero n2 dt (RSeq (RCallSwap ..) bodyC)) rs1 rs'.
  refine RustExec.letZero n2 dt _ rs1 rs' ?_
  -- After RLetZero n2, state is rs2.  Need: RustExec 0 leafSpec
  -- (RSeq (RCallSwap ..) bodyC) rs2 rs'.
  exact RustExec.seq _ _ _ _ _ hCallSwap hBodyExec

end CatCrypt.Crypto.Hax
