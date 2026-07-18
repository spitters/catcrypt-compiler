/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile

set_option autoImplicit false

/-!
# Arbitrary-depth nesting and per-outer-recomputed inner trips (capabilities 1a + 1b)

A3 (`JasminLsemMemLoopNestWhile`) closed **depth-2** nested region calls
(`callee_run2`: a callee whose body itself calls a leaf) and validated a **depth-2**
inline nested loop (`nestedLoop_validate`).  Its stated residual was *arbitrary-depth*
nesting (the closed cost/denote accounting was depth-2-bounded) and an inline nested
loop whose inner trip is **recomputed from the outer index each pass**.  This module
closes both, additively on A1–A3 (imported directly, dodging the cone).

## 1a — ARBITRARY-DEPTH NESTED CALLS (`callee_run_n`, depth-indexed)

`NestBodyOK env P d` is the depth-indexed body predicate: a depth-0 body is
straight-line (`IsLopn`); a depth-`(d+1)` body may call a callee whose own body is
depth-`d`.  `lsemStraightMemDN d` is the matching depth-`d` spec fold — its call arm
recurses at depth `d-1` (so it resolves nested calls all the way down, unlike A2's
`lsemStraightMemC`, which resolves exactly one call level).  `fuelCostDN d` is the
call-aware, depth-indexed fuel.  `nestSegDN` (the depth-indexed generalisation of A3's
`segCallG`) and `calleeRunDN` (the depth-indexed generalisation of A3's `callee_run` /
`callee_run2`) are proved together by induction on `d`: entering a depth-`(d+1)` callee
runs the depth-`d` body-fold then `Lret`-pops, in `fuelCostDN d body + 1 + f` steps.
`calleeRun_depth3` is the concrete depth-3 instance (a callee calling a callee calling a
leaf) with `denote = spec` closed.

## 1b — PER-OUTER-RECOMPUTED INNER TRIP (varying-bound fold)

`runNestedVarLoopMem innerTrip D body` is the two-level fold whose **inner** trip count
is `innerTrip jd` — a function of the *outer* index `jd`, re-evaluated each outer pass.
This is the GGM Phase-3 shape (`innerTrip jd = num >> (jd+1)`, halved per outer pass).
The emitted nest recomputes that bound in the outer body (a real `SHR` on the outer
index register `jd`, seeding the middle counter each pass), so the middle trip is *read*
from the recomputed value, not baked in.

## Validate (native_decide)

A **depth-3** inline nested loop matching the GGM Phase-3 shape (outer `jd ∈ 0..D`,
middle `idx ∈ 0..(num>>(jd+1))` — per-outer-halved, inner `t ∈ 0..outlen`) front-forms
to genuine nested `loopLinstrRM` loops (real back-edges at each of three distinct
labels) and denotes to the triple fold `ggmNestedFold` with the middle bound varying per
`jd`:

* `ggm_depth3_validate` — interpreter `acc = ggmNestedFold D num outlen` (D=3, num=8,
  outlen=2 ⇒ middle trips 4,2,1 ⇒ acc = 14).
* `ggm_recompute_reads_num` — with `num = 16` the interpreter gives `28`
  (= `(8+4+2)*2`), NOT `14`: the middle trip is genuinely recomputed as `num>>(jd+1)`
  from the register per outer pass, not a baked-in `4,2,1`.

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validates).**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile

/-! ## Part 1a — arbitrary-depth nested calls (depth-indexed spec + fuel)

`lsemStraightMemDN env d` is the depth-`d` straight-line-with-calls fold: at depth `0`
it is A1's straight-line `lsemStraightMem` (no calls); at depth `d+1` each call resolves
the callee's body-fold **at depth `d`** — so it resolves nested calls all the way down,
unlike A2's `lsemStraightMemC`, which resolves exactly one call level. -/

/-- Depth-indexed straight-line-with-calls fold. -/
def lsemStraightMemDN (env : LeafEnvM) : Nat → List LinstrRM → LstateM → Option LstateM
  | 0, body, s => lsemStraightMem body s
  | (_ + 1), [], s => some s
  | (d + 1), i :: is, s =>
      match (match i.fst with
             | .Lcall _ (sym, _) =>
                 match env sym with
                 | some body =>
                     (lsemStraightMemDN env d body.dropLast (s.setLpc 0)).map
                       (fun b => b.setLpc (s.lpc + 1))
                 | none => none
             | _ => lsemStepMem i s) with
      | some s' => lsemStraightMemDN env (d + 1) is s'
      | none => none
  termination_by n body _ => (n, body.length)

@[simp] theorem lsemStraightMemDN_zero (env : LeafEnvM) (body : List LinstrRM) (s : LstateM) :
    lsemStraightMemDN env 0 body s = lsemStraightMem body s := by
  simp only [lsemStraightMemDN]

@[simp] theorem lsemStraightMemDN_nil (env : LeafEnvM) (d : Nat) (s : LstateM) :
    lsemStraightMemDN env (d + 1) [] s = some s := by
  simp only [lsemStraightMemDN]

theorem lsemStraightMemDN_succ_cons (env : LeafEnvM) (d : Nat) (i : LinstrRM)
    (is : List LinstrRM) (s : LstateM) :
    lsemStraightMemDN env (d + 1) (i :: is) s =
      (match (match i.fst with
             | .Lcall _ (sym, _) =>
                 match env sym with
                 | some body =>
                     (lsemStraightMemDN env d body.dropLast (s.setLpc 0)).map
                       (fun b => b.setLpc (s.lpc + 1))
                 | none => none
             | _ => lsemStepMem i s) with
      | some s' => lsemStraightMemDN env (d + 1) is s'
      | none => none) := by
  simp only [lsemStraightMemDN]

/-- Depth-indexed fuel cost of a straight-line-with-calls segment: at depth `0`, one step
    per instruction; at depth `d+1`, a call to `sym` costs the depth-`d` callee-body-fold
    cost plus `2` (enter + the callee's `Lret`). -/
def fuelCostDN (env : LeafEnvM) : Nat → List LinstrRM → Nat
  | 0, body => body.length
  | (d + 1), body =>
      (body.map (fun i =>
        match i.fst with
        | .Lcall _ (sym, _) => fuelCostDN env d ((env sym).getD []).dropLast + 2
        | _ => 1)).sum

@[simp] theorem fuelCostDN_zero (env : LeafEnvM) (body : List LinstrRM) :
    fuelCostDN env 0 body = body.length := rfl

@[simp] theorem fuelCostDN_succ_nil (env : LeafEnvM) (d : Nat) :
    fuelCostDN env (d + 1) [] = 0 := rfl

theorem fuelCostDN_succ_cons (env : LeafEnvM) (d : Nat) (i : LinstrRM) (is : List LinstrRM) :
    fuelCostDN env (d + 1) (i :: is) =
      (match i.fst with
        | .Lcall _ (sym, _) => fuelCostDN env d ((env sym).getD []).dropLast + 2
        | _ => 1) + fuelCostDN env (d + 1) is := by
  simp only [fuelCostDN, List.map_cons, List.sum_cons]

/-- The depth-indexed body predicate: a depth-`0` body is straight-line; a depth-`(d+1)`
    body may call a callee whose own body is depth-`d`. -/
def NestBodyOK (env : LeafEnvM) (P : LprogM) : Nat → LinstrRM → Prop
  | 0, i => IsLopn i
  | (d + 1), i =>
      IsLopn i ∨ ∃ (ra : Option String) (sym : String) (lbl : LLabel) (calleeBody : List LinstrRM),
        i.fst = LinstrR.Lcall ra (sym, lbl) ∧ sym ≠ P.lfn ∧
        env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]) ∧
        (∀ j ∈ calleeBody, NestBodyOK env P d j)

/-- The depth-indexed **head step**: a call to `sym` runs the depth-`d` callee-body-fold
    (over `(env sym).dropLast`, the owned body minus its trailing `Lret`) and sets the pc
    to `s.lpc + 1`; every other instruction is the straight-line/memory step. -/
def stepDN (env : LeafEnvM) (d : Nat) (i : LinstrRM) (s : LstateM) : Option LstateM :=
  match i.fst with
  | .Lcall _ (sym, _) =>
      match env sym with
      | some body =>
          (lsemStraightMemDN env d body.dropLast (s.setLpc 0)).map (fun b => b.setLpc (s.lpc + 1))
      | none => none
  | _ => lsemStepMem i s

/-- `lsemStraightMemDN` at depth `d+1` is the `stepDN`-fold. -/
theorem lsemStraightMemDN_succ_cons' (env : LeafEnvM) (d : Nat) (i : LinstrRM)
    (is : List LinstrRM) (s : LstateM) :
    lsemStraightMemDN env (d + 1) (i :: is) s =
      (stepDN env d i s).bind (fun s' => lsemStraightMemDN env (d + 1) is s') := by
  rw [lsemStraightMemDN_succ_cons]
  cases h : stepDN env d i s <;> simp only [stepDN] at h <;>
    simp only [h, Option.bind_none, Option.bind_some]

/-- A successful head step advances the pc by exactly one (a call's `.map (setLpc (s.lpc+1))`;
    a straight-line step's `lsemStepMem_lpc_succ`). -/
theorem stepDN_lpc (env : LeafEnvM) (d : Nat) (i : LinstrRM) (s s' : LstateM)
    (h : stepDN env d i s = some s') : s'.lpc = s.lpc + 1 := by
  unfold stepDN at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨c, _, hc⟩ := h; rw [← hc]; rfl
    · simp at h
  · exact lsemStepMem_lpc_succ i s s' h

/-- Every successful depth-indexed body-fold advances the pc by the body length (each
    step — `Lopn` or nested call — advances the pc by exactly one). -/
theorem lsemStraightMemDN_lpc (env : LeafEnvM) :
    ∀ (d : Nat) (body : List LinstrRM) (s b : LstateM),
      lsemStraightMemDN env d body s = some b → b.lpc = s.lpc + body.length := by
  intro d
  induction d with
  | zero =>
      intro body s b h
      rw [lsemStraightMemDN_zero] at h
      exact lsemStraightMem_lpc body s b h
  | succ d _ =>
      intro body
      induction body with
      | nil => intro s b h; simp only [lsemStraightMemDN_nil, Option.some.injEq] at h; subst h; simp
      | cons i is ih =>
          intro s b h
          rw [lsemStraightMemDN_succ_cons'] at h
          cases hstep : stepDN env d i s with
          | none => rw [hstep] at h; simp at h
          | some s' =>
              rw [hstep, Option.bind_some] at h
              have h1 := stepDN_lpc env d i s s' hstep
              have h2 := ih s' b h
              rw [h2, h1, List.length_cons]; omega

/-! ### All-`Lopn` reconciliation (depth-0 ↔ A2's one-level fold)

At depth `0` the call-aware fold and cost collapse to A1's straight-line fold and the
segment length, so the depth-`0` case of the segment lemma is A3's `segCallG` restricted
to an all-`Lopn` segment. -/

/-- On an all-`Lopn` segment, the one-level call fold `lsemStraightMemC` is A1's
    straight-line fold `lsemStraightMem` (no calls to resolve). -/
theorem lsemStraightMemC_allLopn (env : LeafEnvM) :
    ∀ (seg : List LinstrRM), (∀ i ∈ seg, IsLopn i) → ∀ (s : LstateM),
      lsemStraightMemC env seg s = lsemStraightMem seg s := by
  intro seg
  induction seg with
  | nil => intro _ s; rfl
  | cons i is ih =>
      intro h s
      rw [lsemStraightMemC_cons, lsemStraightMem_cons, lsemStepMemC_lopn env i s (h i (by simp))]
      cases lsemStepMem i s with
      | none => rfl
      | some s' => exact ih (fun j hj => h j (by simp [hj])) s'

/-- On an all-`Lopn` segment, the one-level call cost `fuelCostC` is the segment length. -/
theorem fuelCostC_allLopn (env : LeafEnvM) :
    ∀ (seg : List LinstrRM), (∀ i ∈ seg, IsLopn i) → fuelCostC env seg = seg.length := by
  intro seg
  induction seg with
  | nil => intro _; rfl
  | cons i is ih =>
      intro h
      rw [fuelCostC_cons, List.length_cons]
      have h1 : stepCostC env i = 1 := by
        obtain ⟨d, o, src, hd⟩ := h i (by simp); unfold stepCostC; rw [hd]
      rw [h1, ih (fun j hj => h j (by simp [hj]))]; omega

/-- A call's head step over the shared state: `stepDN` on an `Lopn` is `lsemStepMem`. -/
theorem stepDN_lopn (env : LeafEnvM) (d : Nat) (i : LinstrRM) (s : LstateM) (hi : IsLopn i) :
    stepDN env d i s = lsemStepMem i s := by
  obtain ⟨dd, o, src, hd⟩ := hi; unfold stepDN; rw [hd]

/-! ### `calleeEnterDN` — a depth-`d` callee run (parameterised by the depth-`d` segment lemma)

`calleeEnterDN` is the depth-indexed generalisation of A2's `callee_run` / A3's
`callee_run2`: entering a callee whose body is depth-`d` runs the depth-`d` body-fold then
`Lret`-pops.  It takes the depth-`d` segment lemma `hsegd` as a hypothesis — inside
`nestSegDN`'s `succ` case that hypothesis is the induction hypothesis at depth `d`. -/

/-- The type of the depth-`d` segment lemma (the induction carrier of `nestSegDN`). -/
def SegLemmaDN (env : LeafEnvM) (P : LprogM) (d : Nat) : Prop :=
  ∀ (cf : String) (seg : List LinstrRM) (s : LstatePMC) (f : Nat),
    s.lfn = cf →
    (∀ i ∈ seg, NestBodyOK env P d i) →
    (∀ k, k < seg.length → (curBodyC env P cf)[s.base.lpc + k]? = seg[k]?) →
    lsemFuelMemLC env P (fuelCostDN env d seg + f) s
      = (lsemStraightMemDN env d seg s.base).bind
          (fun b => lsemFuelMemLC env P f { s with base := b })

/-- **Depth-`d` callee run (success).**  Given the depth-`d` segment lemma, entering a
    callee `sym` whose body is depth-`d` runs the depth-`d` body-fold to `b` then
    `Lret`-pops back to the caller at `retPc`, in `fuelCostDN env d calleeBody + 1 + f`
    steps. -/
theorem calleeEnterDN (env : LeafEnvM) (P : LprogM) (d : Nat) (hsegd : SegLemmaDN env P d)
    (sym callerFn : String) (retPc : Nat) (calleeBody : List LinstrRM)
    (hbok : ∀ i ∈ calleeBody, NestBodyOK env P d i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base b : LstateM) (rest : List (String × Nat)) (f : Nat)
    (hrun : lsemStraightMemDN env d calleeBody (base.setLpc 0) = some b) :
    lsemFuelMemLC env P (fuelCostDN env d calleeBody + 1 + f)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest }
      = lsemFuelMemLC env P f
          { base := b.setLpc retPc, lfn := callerFn, rstack := rest } := by
  have hcur : curBodyC env P sym = calleeBody ++ [(LinstrR.Lret, MemTag.reg none)] := by
    unfold curBodyC; rw [if_neg hne, hsym]; rfl
  have hseg := hsegd sym calleeBody
      { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest } (1 + f)
      rfl hbok
      (by intro k hk
          show (curBodyC env P sym)[(base.setLpc 0).lpc + k]? = calleeBody[k]?
          rw [hcur]
          simp only [LstateM.lpc_setLpc, Nat.zero_add]
          rw [List.getElem?_append_left (by simpa using hk)])
  rw [show fuelCostDN env d calleeBody + 1 + f = fuelCostDN env d calleeBody + (1 + f) from by omega,
    hseg, hrun, Option.bind_some]
  have hb_lpc : b.lpc = calleeBody.length := by
    have := lsemStraightMemDN_lpc env d calleeBody (base.setLpc 0) b hrun
    simpa using this
  have hfetchRet : findInstrMemC env P
      { base := b, lfn := sym, rstack := (callerFn, retPc) :: rest }
        = some (LinstrR.Lret, MemTag.reg none) := by
    unfold findInstrMemC
    show (curBodyC env P sym)[b.lpc]? = _
    rw [hcur, hb_lpc, List.getElem?_append_right (by simp)]
    simp
  rw [show 1 + f = f + 1 from by omega, lsemFuelMemLC, hfetchRet]
  simp only []
  unfold evalInstrPMemLC
  simp only []

/-- **Depth-`d` callee run (failure).**  If the depth-`d` body-fold fails, the whole
    callee run is `none`. -/
theorem calleeEnterDN_none (env : LeafEnvM) (P : LprogM) (d : Nat) (hsegd : SegLemmaDN env P d)
    (sym callerFn : String) (retPc : Nat) (calleeBody : List LinstrRM)
    (hbok : ∀ i ∈ calleeBody, NestBodyOK env P d i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base : LstateM) (rest : List (String × Nat)) (g : Nat)
    (hrun : lsemStraightMemDN env d calleeBody (base.setLpc 0) = none) :
    lsemFuelMemLC env P (fuelCostDN env d calleeBody + 1 + g)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest } = none := by
  have hcur : curBodyC env P sym = calleeBody ++ [(LinstrR.Lret, MemTag.reg none)] := by
    unfold curBodyC; rw [if_neg hne, hsym]; rfl
  have hseg := hsegd sym calleeBody
      { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest } (1 + g)
      rfl hbok
      (by intro k hk
          show (curBodyC env P sym)[(base.setLpc 0).lpc + k]? = calleeBody[k]?
          rw [hcur]
          simp only [LstateM.lpc_setLpc, Nat.zero_add]
          rw [List.getElem?_append_left (by simpa using hk)])
  rw [show fuelCostDN env d calleeBody + 1 + g = fuelCostDN env d calleeBody + (1 + g) from by omega,
    hseg, hrun, Option.bind_none]

/-! ### `nestSegDN` — the depth-indexed segment lemma (1a, closed)

By induction on `d`: at depth `0` it is `segCallG` on an all-`Lopn` segment; at depth
`d+1` each call is discharged by `calleeEnterDN` at depth `d` (the induction hypothesis).
This is the closed, arbitrary-depth generalisation of A3's `segCallG` + `callee_run2`. -/
theorem nestSegDN (env : LeafEnvM) (P : LprogM) : ∀ (d : Nat), SegLemmaDN env P d := by
  intro d
  induction d with
  | zero =>
      intro cf seg s f hfn hok hpos
      have hlopn : ∀ i ∈ seg, IsLopn i := fun i hi => hok i hi
      have hbody : ∀ i ∈ seg, BodyStepOK env P i := fun i hi => Or.inl (hlopn i hi)
      have hseg := segCallG env P cf seg s f hfn hbody hpos
      rw [fuelCostDN_zero, lsemStraightMemDN_zero, ← fuelCostC_allLopn env seg hlopn, hseg,
        lsemStraightMemC_allLopn env seg hlopn]
  | succ d' ihd =>
      intro cf seg
      induction seg with
      | nil =>
          intro s f _ _ _
          simp only [fuelCostDN_succ_nil, Nat.zero_add, lsemStraightMemDN_nil, Option.bind_some]
      | cons i is ihseg =>
          intro s f hfn hok hpos
          have hcur : curBodyC env P s.lfn = curBodyC env P cf := by rw [hfn]
          have hii : NestBodyOK env P (d' + 1) i := hok i (by simp)
          have his : ∀ j ∈ is, NestBodyOK env P (d' + 1) j := fun j hj => hok j (by simp [hj])
          have hfetch : findInstrMemC env P s = some i := by
            unfold findInstrMemC; rw [hcur]
            have := hpos 0 (by simp); simpa using this
          have hpostail : ∀ (b : LstateM), b.lpc = s.base.lpc + 1 →
              ∀ k, k < is.length →
                (curBodyC env P cf)[({ s with base := b } : LstatePMC).base.lpc + k]? = is[k]? := by
            intro b hb k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            show (curBodyC env P cf)[b.lpc + k]? = is[k]?
            rw [hb, show s.base.lpc + 1 + k = s.base.lpc + (k + 1) from by omega, hp]; simp
          rw [fuelCostDN_succ_cons]
          rcases hii with hlopn | ⟨ra, sym, lbl, calleeBody, hcall, hne, hsym, hcbOK⟩
          · -- `Lopn`: cost 1, straight-line step.
            have hcost1 : (match i.fst with
                | .Lcall _ (sym, _) => fuelCostDN env d' ((env sym).getD []).dropLast + 2
                | _ => 1) = 1 := by obtain ⟨dd, o, src, hd⟩ := hlopn; rw [hd]
            rw [hcost1,
              show 1 + fuelCostDN env (d' + 1) is + f = (fuelCostDN env (d' + 1) is + f) + 1 from by omega,
              lsemFuelMemLC, hfetch]
            simp only []
            rw [evalInstrPMemLC_lopn env P i s hlopn, lsemStraightMemDN_succ_cons',
              stepDN_lopn env d' i s.base hlopn]
            cases hstep : lsemStepMem i s.base with
            | none => simp
            | some b =>
                simp only [Option.map_some, Option.bind_some]
                have hb_lpc : b.lpc = s.base.lpc + 1 := lsemStepMem_lpc_succ i s.base b hstep
                have hfn' : ({ s with base := b } : LstatePMC).lfn = cf := hfn
                have := ihseg { s with base := b } f hfn' his (hpostail b hb_lpc)
                simpa using this
          · -- region call to a depth-`d'` callee: discharged by `calleeEnterDN` (IH `ihd`).
            have hcostcall : (match i.fst with
                | .Lcall _ (sym, _) => fuelCostDN env d' ((env sym).getD []).dropLast + 2
                | _ => 1) = fuelCostDN env d' calleeBody + 2 := by
              rw [hcall]; simp only []; rw [hsym]
              simp only [Option.getD_some, List.dropLast_concat]
            rw [hcostcall,
              show fuelCostDN env d' calleeBody + 2 + fuelCostDN env (d' + 1) is + f
                = (fuelCostDN env d' calleeBody + 1 + (fuelCostDN env (d' + 1) is + f)) + 1 from by omega,
              lsemFuelMemLC, hfetch]
            simp only []
            have henter : evalInstrPMemLC env P i s
                = some { base := s.base.setLpc 0, lfn := sym,
                         rstack := (s.lfn, s.base.lpc + 1) :: s.rstack } := by
              unfold evalInstrPMemLC; rw [hcall]; simp only []; rw [hsym]
            rw [henter]
            simp only []
            rw [lsemStraightMemDN_succ_cons']
            have hstepcall : stepDN env d' i s.base
                = (lsemStraightMemDN env d' calleeBody (s.base.setLpc 0)).map
                    (fun b => b.setLpc (s.base.lpc + 1)) := by
              unfold stepDN; rw [hcall]; simp only []; rw [hsym]
              simp only [List.dropLast_concat]
            rw [hstepcall]
            cases hleaf : lsemStraightMemDN env d' calleeBody (s.base.setLpc 0) with
            | none =>
                simp only [Option.map_none, Option.bind_none]
                exact calleeEnterDN_none env P d' ihd sym s.lfn (s.base.lpc + 1) calleeBody
                  hcbOK hne hsym s.base s.rstack (fuelCostDN env (d' + 1) is + f) hleaf
            | some b =>
                simp only [Option.map_some, Option.bind_some]
                have hcallee := calleeEnterDN env P d' ihd sym s.lfn (s.base.lpc + 1) calleeBody
                  hcbOK hne hsym s.base b s.rstack (fuelCostDN env (d' + 1) is + f) hleaf
                rw [hcallee]
                have hbset_lpc : (b.setLpc (s.base.lpc + 1)).lpc = s.base.lpc + 1 := rfl
                have := ihseg (⟨b.setLpc (s.base.lpc + 1), s.lfn, s.rstack⟩ : LstatePMC) f hfn
                  his (hpostail _ hbset_lpc)
                have hstateEq :
                    ((⟨b.setLpc (s.base.lpc + 1), s.lfn, s.rstack⟩ : LstatePMC))
                      = { s with base := b.setLpc (s.base.lpc + 1) } := by
                  cases s; rfl
                rw [hstateEq] at *
                exact this

/-- **`calleeRunDN` — the closed depth-`d` nested-call denote.**  Entering a callee whose
    body is depth-`d` (may call depth-`(d-1)` callees, recursively) runs the depth-`d`
    body-fold `lsemStraightMemDN env d calleeBody` then `Lret`-pops — the arbitrary-depth
    generalisation of A3's `callee_run2` (depth-2), with the depth-indexed cost
    `fuelCostDN env d calleeBody + 1`. -/
theorem calleeRunDN (env : LeafEnvM) (P : LprogM) (d : Nat)
    (sym callerFn : String) (retPc : Nat) (calleeBody : List LinstrRM)
    (hbok : ∀ i ∈ calleeBody, NestBodyOK env P d i)
    (hne : sym ≠ P.lfn)
    (hsym : env sym = some (calleeBody ++ [(LinstrR.Lret, MemTag.reg none)]))
    (base b : LstateM) (rest : List (String × Nat)) (f : Nat)
    (hrun : lsemStraightMemDN env d calleeBody (base.setLpc 0) = some b) :
    lsemFuelMemLC env P (fuelCostDN env d calleeBody + 1 + f)
        { base := base.setLpc 0, lfn := sym, rstack := (callerFn, retPc) :: rest }
      = lsemFuelMemLC env P f
          { base := b.setLpc retPc, lfn := callerFn, rstack := rest } :=
  calleeEnterDN env P d (nestSegDN env P d) sym callerFn retPc calleeBody hbok hne hsym
    base b rest f hrun

/-! ### Concrete depth-3 nested calls (`calleeRun_depth3`)

A three-level call tower over the shared `LstateM`: `l3` (body all-`Lopn`) is a
depth-0 leaf; `l2` calls `l3` (depth-1 body); `l1` calls `l2` (depth-2 body).  Entering
`l1` is a genuine depth-3 nested call, discharged by `calleeRunDN` at depth `2`. -/

/-- The three-level environment: `l1 → l2 → l3`, `l3` adds `t` to `acc`. -/
def depth3Env : LeafEnvM := fun name =>
  if name = "l3" then
    some [ (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else if name = "l2" then
    some [ (LinstrR.Lcall none ("l3", (0 : LLabel)), MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else if name = "l1" then
    some [ (LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)
         , (LinstrR.Lret, MemTag.reg none) ]
  else none

/-- The (depth-3-carrying) loop program whose function name is `g` (so `l1`/`l2`/`l3`
    are all callees, `≠ P.lfn`). -/
def depth3Prog : LprogM := singletonProgM "g" []

/-- `l1`'s body — a single call to `l2` — is a depth-2 body. -/
theorem depth3_l1_body_ok :
    ∀ i ∈ [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)],
      NestBodyOK depth3Env depth3Prog 2 i := by
  intro i hi
  simp only [List.mem_singleton] at hi; subst hi
  refine Or.inr ⟨none, "l2", 0, [(LinstrR.Lcall none ("l3", (0 : LLabel)), MemTag.reg none)], rfl,
    by decide, rfl, ?_⟩
  intro j hj
  simp only [List.mem_singleton] at hj; subst hj
  refine Or.inr ⟨none, "l3", 0,
    [(LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "t"], MemTag.reg none)], rfl,
    by decide, rfl, ?_⟩
  intro k hk
  simp only [List.mem_singleton] at hk; subst hk
  exact ⟨_, _, _, rfl⟩

/-- **Closed depth-3 nested call.**  Entering `l1` (which calls `l2`, which calls `l3`)
    from a state with `acc = 5`, `t = 7` runs the three-level tower and pops back with
    `acc = 12`, in `fuelCostDN depth3Env 2 l1Body + 1 = 6` steps — the interpreter
    followed a genuine depth-3 region-call chain, `denote = spec` closed via
    `calleeRunDN` (no `native_decide`). -/
theorem calleeRun_depth3 :
    let l1Body := [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)]
    let base := (({} : LstateM).setReg "acc" (5#64)).setReg "t" (7#64)
    ∀ (b : LstateM),
      lsemStraightMemDN depth3Env 2 l1Body (base.setLpc 0) = some b →
      lsemFuelMemLC depth3Env depth3Prog (fuelCostDN depth3Env 2 l1Body + 1 + 0)
          { base := base.setLpc 0, lfn := "l1", rstack := ("g", 3) :: [] }
        = lsemFuelMemLC depth3Env depth3Prog 0
            { base := b.setLpc 3, lfn := "g", rstack := [] } := by
  intro l1Body base b hrun
  exact calleeRunDN depth3Env depth3Prog 2 "l1" "g" 3 l1Body depth3_l1_body_ok
    (by decide) rfl base b [] 0 hrun

/-- The depth-3 tower computes `acc = 5 + 7 = 12` (the innermost `l3` adds `t` to `acc`),
    read off the depth-indexed fold `lsemStraightMemDN`. -/
theorem calleeRun_depth3_value :
    (lsemStraightMemDN depth3Env 2
        [(LinstrR.Lcall none ("l2", (0 : LLabel)), MemTag.reg none)]
        (((({} : LstateM).setReg "acc" (5#64)).setReg "t" (7#64)).setLpc 0)).map
      (fun b => decodeM b "acc" 64) = some (some (12#64)) := by native_decide

/-! ## Part 1b/validate — the GGM Phase-3 depth-3 inline nested loop

We build the depth-3 nest directly from `loopLinstrRM` (three distinct top labels
`0`/`1`/`2`), and validate `denote = spec` by `native_decide`. -/

/-- The **pure triple-fold spec** with the middle bound varying per outer index: for
    each `jd < D`, run the inner (constant `outlen`) fold `num >>> (jd+1)` times,
    accumulating `+1` per innermost step.  The middle range `num >>> (jd+1)` is an
    explicit function of the outer index `jd` — the per-outer-recomputed inner trip. -/
def ggmNestedFold (D num outlen : Nat) : Nat :=
  (List.range D).foldl (fun acc jd =>
    (List.range (num >>> (jd + 1))).foldl (fun acc2 _ =>
      (List.range outlen).foldl (fun acc3 _ => acc3 + 1) acc2) acc) 0

/-- The **per-outer-recomputed inner-trip fold** (1b): a two-level fold whose inner
    (middle) trip count is `innerTrip jd`, a function of the *outer* index `jd`,
    re-evaluated on each outer pass.  Each innermost step accumulates `+1` over an inner
    constant `outlen` loop.  The GGM Phase-3 shape is this with
    `innerTrip jd = num >> (jd+1)` (halved per outer pass). -/
def runNestedVarLoopMem (innerTrip : Nat → Nat) (D outlen : Nat) : Nat :=
  (List.range D).foldl (fun acc jd =>
    (List.range (innerTrip jd)).foldl (fun acc2 _ =>
      (List.range outlen).foldl (fun acc3 _ => acc3 + 1) acc2) acc) 0

/-- The GGM triple fold IS the varying-bound fold whose middle trip is the outer-index
    function `jd ↦ num >> (jd+1)` — the inner bound is *read* from that per-outer-index
    function, not a fixed schedule. -/
theorem ggmNestedFold_eq_var (D num outlen : Nat) :
    ggmNestedFold D num outlen = runNestedVarLoopMem (fun jd => num >>> (jd + 1)) D outlen := rfl

/-- The **innermost** loop body (label `2`, counter `mc`): `acc += 1`, `mc -= 1`. -/
def ggmInnerBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "mc"] "SUB:64" [.reg "mc", .imm 1], MemTag.reg none) ]

/-- The **middle** loop body (label `1`, counter `mid`): reseed the inner counter
    `mc := outlen` (constant `2`), run the inner loop, then `mid -= 1`. -/
def ggmMiddleBody : List LinstrRM :=
  (LinstrR.Lopn [.reg "mc"] "MOV:64" [.imm 2], MemTag.reg none)
    :: (loopLinstrRM 2 "mc" ggmInnerBody
        ++ [(LinstrR.Lopn [.reg "mid"] "SUB:64" [.reg "mid", .imm 1], MemTag.reg none)])

/-- The **outer** loop body (label `0`, counter `oc`): compute `sa := jd + 1`, then
    **recompute the middle trip** `mid := num >> sa` (a real `SHR` on the outer index
    register — the per-outer-recomputed inner bound), run the middle loop, then advance
    the outer index `jd += 1` and decrement the outer counter `oc -= 1`. -/
def ggmOuterBody : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "sa"] "ADD:64" [.reg "jd", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "mid"] "SHR:64" [.reg "num", .reg "sa"], MemTag.reg none) ]
    ++ loopLinstrRM 1 "mid" ggmMiddleBody
    ++ [ (LinstrR.Lopn [.reg "jd"] "ADD:64" [.reg "jd", .imm 1], MemTag.reg none)
       , (LinstrR.Lopn [.reg "oc"] "SUB:64" [.reg "oc", .imm 1], MemTag.reg none) ]

/-- The depth-3 GGM program: the outer loop (top label `0`, counter `oc`) over
    `ggmOuterBody`, which contains the middle loop (label `1`), which contains the inner
    loop (label `2`) — three genuine back-edges over the shared `LstateM`. -/
def ggmProg : LprogM := singletonProgM "g" (loopLinstrRM 0 "oc" ggmOuterBody)

/-- The start state for `D = 3`, `num` supplied, `outlen = 2` (as the immediate `2` in
    `ggmMiddleBody`): `acc = 0`, `jd = 0`, outer counter `oc = 3`, `num` register. -/
def ggmStart (num : Nat) : LstatePMC :=
  { base :=
      (((({} : LstateM).setReg "acc" (0#64)).setReg "jd" (0#64)).setReg "oc"
        (3#64)).setReg "num" (BitVec.ofNat 64 num)
    lfn := "g"
    rstack := [] }

/-- **Validate 1a (depth-3) + 1b (varying bound), `denote = spec`.**  The depth-3 inline
    nested loop (outer `jd ∈ 0..3`, middle `idx ∈ 0..(num>>(jd+1))` per-outer-halved,
    inner `t ∈ 0..2`) run by `lsemFuelMemLC` decodes `acc` to the pure triple fold
    `ggmNestedFold 3 8 2 = 14` (middle trips `4, 2, 1`).  The interpreter followed three
    genuine nested back-edges (labels `0`/`1`/`2`) over the shared `LstateM`. -/
theorem ggm_depth3_validate :
    (lsemFuelMemLC (fun _ => none) ggmProg 4000 (ggmStart 8)).map
        (fun t => decodeM t.base "acc" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 8 2))) := by native_decide

/-- **Validate 1b — the middle trip is READ from the recomputed bound, not baked in.**
    With `num = 16` the same program gives `acc = ggmNestedFold 3 16 2 = (8+4+2)*2 = 28`,
    NOT `14`.  Had the middle trips `4, 2, 1` been baked in, changing `num` would leave
    the result at `14`; instead the middle counter is recomputed as `num >> (jd+1)` from
    the `num` register on every outer pass. -/
theorem ggm_recompute_reads_num :
    (lsemFuelMemLC (fun _ => none) ggmProg 8000 (ggmStart 16)).map
        (fun t => decodeM t.base "acc" 64)
      = some (some (BitVec.ofNat 64 (ggmNestedFold 3 16 2))) := by native_decide

/-- The two `num`s give different results — the per-outer-recomputed middle trip is not a
    baked-in constant schedule. -/
theorem ggm_depth3_num_sensitive :
    ggmNestedFold 3 8 2 = 14 ∧ ggmNestedFold 3 16 2 = 28 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
