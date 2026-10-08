/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
public import CatCrypt.Crypto.SecureCompilation.VIR.LinMapSchedule

/-!
# Schedules of linear maps as straight-line programs

A schedule of `LinMapSchedule` names its values by natural numbers. A straight-line
program `SLP` of `TowerDialect` names them by positions of a register file of known
size. `schedSLP k m s` is the straight-line program of the schedule `s` over `k` inputs
with `m` outputs, defined when every index of `s` is in range and `s` has `m` outputs.
Its instructions are the sum, the difference, the multiplication by an integer constant
and the copy; a doubling is the sum of a register with itself. The emitted program binds
`fAdd`, `fSub`, `fConst` and `fMul` only, and a copy binds nothing.

## Main results

* `LinI`, `LinI.eval`: the instructions and their value over a carrier with the
  operations of `LinOps`.
* `stepIns`, `stepsSLP`, `schedSLP`: the conversion of a step, of a list of steps with
  the output indices, and of a schedule.
* `schedSLP_eval`: the results of the converted schedule are the outputs of the schedule.
* `LinI.emit`, `LinI.emit_sound`: the emission of an instruction over coordinate
  variables and its soundness over `ZMod p`.
* `schedEmit`, `schedEmit_denote`: the emitted program of a converted schedule hands its
  continuation variables holding the outputs of the schedule.
* `schedEmit_linMap`: for a schedule accepted by `schedOk` for the matrix `M`, the
  variables hold `M` applied to the inputs.
* `schedEmit_cov`: the emitted program is `ArithAt p`-covered when its continuation is.
* `quadSched_slp`, `externalSched_slp`: the two schedules of Poseidon2 convert.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LinMapSLP

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.TowerDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.LinMapSchedule

/-! ## 1. Instructions -/

/-- The instructions of a linear map over `k` registers. -/
inductive LinI (k : Nat) where
  /-- Sum of two registers. -/
  | add (i j : Fin k)
  /-- Difference of two registers. -/
  | sub (i j : Fin k)
  /-- The integer `c` times a register. -/
  | scale (c : Int) (i : Fin k)
  /-- A register. -/
  | copy (i : Fin k)

variable {α : Type}

/-- The value of an instruction over the operations `o`. -/
def LinI.eval (o : LinOps α) {k : Nat} : LinI k → (Fin k → α) → α
  | .add i j, xs => o.add (xs i) (xs j)
  | .sub i j, xs => o.sub (xs i) (xs j)
  | .scale c i, xs => o.smul c (xs i)
  | .copy i, xs => xs i

/-- The semantics of the instructions over the operations `o`. -/
abbrev linEv (o : LinOps α) : ∀ {k : Nat}, LinI k → (Fin k → α) → α :=
  fun ins xs => ins.eval o xs

/-! ## 2. The conversion -/

/-- The instruction of a step over `k` registers; `none` when an index is out of range. -/
def stepIns (k : Nat) : Step → Option (LinI k)
  | .add i j => if h : i < k ∧ j < k then some (.add ⟨i, h.1⟩ ⟨j, h.2⟩) else none
  | .sub i j => if h : i < k ∧ j < k then some (.sub ⟨i, h.1⟩ ⟨j, h.2⟩) else none
  | .double i => if h : i < k then some (.add ⟨i, h⟩ ⟨i, h⟩) else none
  | .scale c i => if h : i < k then some (.scale c ⟨i, h⟩) else none
  | .copy i => if h : i < k then some (.copy ⟨i, h⟩) else none

/-- The output registers: `none` unless there are `m` indices, all below `k`. -/
def retOf (k m : Nat) (outs : List Nat) : Option (Fin m → Fin k) :=
  if h : outs.length = m ∧ ∀ i ∈ outs, i < k then
    some fun j => ⟨outs[j.val]'(h.1 ▸ j.isLt), h.2 _ (List.getElem_mem _)⟩
  else none

/-- The straight-line program of the steps over `k` registers with the outputs `outs`. -/
def stepsSLP : (k m : Nat) → List Step → List Nat → Option (SLP LinI k m)
  | k, m, [], outs => (retOf k m outs).map SLP.ret
  | k, m, st :: r, outs =>
    match stepIns k st, stepsSLP (k + 1) m r outs with
    | some ins, some rest => some (.step ins rest)
    | _, _ => none

/-- The straight-line program of a schedule over `k` inputs with `m` outputs. -/
def schedSLP (k m : Nat) (s : Sched) : Option (SLP LinI k m) :=
  stepsSLP k m s.steps s.outs

theorem getElem?_ofFn_lt {k : Nat} (xs : Fin k → α) (i : Nat) (h : i < k) :
    (List.ofFn xs)[i]? = some (xs ⟨i, h⟩) := by
  simp [h]

/-- The value of a converted step is the value of the step. -/
theorem stepIns_val (o : LinOps α) (k : Nat) (st : Step) (ins : LinI k)
    (h : stepIns k st = some ins) (xs : Fin k → α) :
    st.val o (List.ofFn xs) = some (ins.eval o xs) := by
  cases st with
  | add i j =>
    simp only [stepIns] at h
    split at h
    · next hc =>
      cases h
      simp only [Step.val, getElem?_ofFn_lt xs i hc.1, getElem?_ofFn_lt xs j hc.2, LinI.eval]
    · cases h
  | sub i j =>
    simp only [stepIns] at h
    split at h
    · next hc =>
      cases h
      simp only [Step.val, getElem?_ofFn_lt xs i hc.1, getElem?_ofFn_lt xs j hc.2, LinI.eval]
    · cases h
  | double i =>
    simp only [stepIns] at h
    split at h
    · next hc =>
      cases h
      simp only [Step.val, getElem?_ofFn_lt xs i hc, LinI.eval]
    · cases h
  | scale c i =>
    simp only [stepIns] at h
    split at h
    · next hc =>
      cases h
      simp only [Step.val, getElem?_ofFn_lt xs i hc, LinI.eval]
    · cases h
  | copy i =>
    simp only [stepIns] at h
    split at h
    · next hc =>
      cases h
      simp only [Step.val, getElem?_ofFn_lt xs i hc, LinI.eval]
    · cases h

theorem pick_map_some (vs : List α) (outs : List Nat) (h : ∀ i ∈ outs, i < vs.length) :
    (pick vs outs).map some = outs.map fun i => vs[i]? := by
  induction outs with
  | nil => rfl
  | cons i r ih =>
    have hi : i < vs.length := h i (List.mem_cons_self ..)
    have hr := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [pick, List.filterMap_cons, List.getElem?_eq_getElem hi, List.map_cons] at hr ⊢
    rw [hr]

/-- The values at the output registers are the picked values. -/
theorem retOf_pick (k m : Nat) (outs : List Nat) (f : Fin m → Fin k)
    (h : retOf k m outs = some f) (xs : Fin k → α) :
    List.ofFn (fun j => xs (f j)) = pick (List.ofFn xs) outs := by
  unfold retOf at h
  split at h
  · next hc =>
    cases h
    obtain ⟨hl, hall⟩ := hc
    subst hl
    apply List.map_injective_iff.mpr (Option.some_injective α)
    rw [pick_map_some _ _ (fun i hi => by rw [List.length_ofFn]; exact hall i hi)]
    refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
    have hj : j < outs.length := by simpa using h₂
    simp only [List.getElem_map, List.getElem_ofFn]
    exact (getElem?_ofFn_lt xs _ (hall _ (List.getElem_mem hj))).symm
  · cases h

theorem ofFn_snoc {k : Nat} (xs : Fin k → α) (v : α) :
    List.ofFn (Fin.snoc (α := fun _ => α) xs v) = List.ofFn xs ++ [v] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]

/-- The results of the converted steps are the picked values after the steps. -/
theorem stepsSLP_eval (o : LinOps α) :
    ∀ (steps : List Step) (k m : Nat) (outs : List Nat) (P : SLP LinI k m),
      stepsSLP k m steps outs = some P → ∀ xs : Fin k → α,
      List.ofFn (P.eval (linEv o) xs) = pick (runSteps o (List.ofFn xs) steps) outs
  | [], k, m, outs, P, h, xs => by
    simp only [stepsSLP, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    exact retOf_pick k m outs f hf xs
  | st :: r, k, m, outs, P, h, xs => by
    simp only [stepsSLP] at h
    split at h
    · next ins rest hi hr =>
      cases h
      show List.ofFn (rest.eval (linEv o) (Fin.snoc (α := fun _ => α) xs (ins.eval o xs))) = _
      rw [stepsSLP_eval o r (k + 1) m outs rest hr, runSteps, stepIns_val o k st ins hi xs,
        ofFn_snoc]
      rfl
    · cases h

/-- **The results of the converted schedule are the outputs of the schedule.** -/
theorem schedSLP_eval (o : LinOps α) {k m : Nat} {s : Sched} {P : SLP LinI k m}
    (h : schedSLP k m s = some P) (xs : Fin k → α) :
    List.ofFn (P.eval (linEv o) xs) = s.run o (List.ofFn xs) :=
  stepsSLP_eval o s.steps k m s.outs P h xs

/-! ## 3. Emission -/

section Emit

variable {p : Nat}

/-- The emission of an instruction over the coordinate variables `env`: one `fAdd` or
    `fSub` binding for a sum or a difference, an `fConst` and an `fMul` binding for a
    multiplication by a constant, no binding for a copy. -/
def LinI.emit (p : Nat) {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} :
    LinI k → (Fin k → Ctxt.Var Γ (.fp p)) →
    ({Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → MRC Γ' ts) → MRC Γ ts
  | .add i j, env, kk => emitT (.add (.inp 0) (.inp 1)) ![env i, env j] kk
  | .sub i j, env, kk => emitT (.sub (.inp 0) (.inp 1)) ![env i, env j] kk
  | .scale c i, env, kk => emitT (.mul (.const (c : ZMod p)) (.inp 0)) ![env i] kk
  | .copy i, env, kk => kk (fun v => v) (env i)

/-- **The instructions are sound** over `ZMod p`: the emitted code of each instruction
    computes its value. -/
theorem LinI.emit_sound :
    EmitSound (B := fun Γ => Ctxt.Var Γ (.fp p)) (fun v V => v.lookup V)
      (linEv (ringOps (ZMod p)))
      (fun {k Γ ts} ins env kk => LinI.emit p (k := k) (Γ := Γ) (ts := ts) ins env kk) := by
  intro k Γ ts ins env kk V R hk
  cases ins with
  | add i j =>
    exact emitT_denote (fun t => (![env i, env j] t).lookup V) _ _ kk V R (fun _ => rfl)
      fun r V' w hr hw => hk r V' w hr hw
  | sub i j =>
    exact emitT_denote (fun t => (![env i, env j] t).lookup V) _ _ kk V R (fun _ => rfl)
      fun r V' w hr hw => hk r V' w hr hw
  | scale c i =>
    exact emitT_denote (fun t => (![env i] t).lookup V) _ _ kk V R (fun _ => rfl)
      fun r V' w hr hw => hk r V' w hr hw
  | copy i => exact hk _ V (env i) (fun _ => rfl) rfl

/-- The emitted program of a straight-line program of linear instructions. -/
def schedEmit (p : Nat) {ts : List FieldTy} {k m : Nat} (P : SLP LinI k m)
    {Γ : Ctxt fieldDialect} (env : Fin k → Ctxt.Var Γ (.fp p))
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts) :
    MRC Γ ts :=
  P.emit (B := fun Γ => Ctxt.Var Γ (.fp p)) (fun r v => r v)
    (fun ins env kk => LinI.emit p ins env kk) env kk

/-- **Denotation of the emitted program of a converted schedule.** If the continuation
    denotes `R` whenever its renaming preserves values and its variables hold the outputs
    of the schedule on the values of `env`, then the emitted program denotes `R`. -/
theorem schedEmit_denote {ts : List FieldTy} {k m : Nat} {s : Sched} {P : SLP LinI k m}
    (h : schedSLP k m s = some P) {Γ : Ctxt fieldDialect} (env : Fin k → Ctxt.Var Γ (.fp p))
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
      (zs : Fin m → Ctxt.Var Γ' (.fp p)), Preserves r V V' →
      List.ofFn (fun j => (zs j).lookup V')
        = s.run (ringOps (ZMod p)) (List.ofFn fun i => (env i).lookup V) →
      (kk r zs).denote V' = R) :
    (schedEmit p P env kk).denote V = R :=
  SLP.emit_denote (B := fun Γ => Ctxt.Var Γ (.fp p)) (fun v V => v.lookup V) (fun r v => r v)
    (linEv (ringOps (ZMod p))) (fun ins env kk => LinI.emit p ins env kk)
    (fun _ _ _ b hr => hr b) LinI.emit_sound P env kk V R fun r V' zs hr hzs =>
      hk r V' zs hr ((congrArg List.ofFn (funext hzs)).trans
        (schedSLP_eval (ringOps (ZMod p)) h _))

/-- **The emitted program of an accepted schedule computes the matrix.** If `env` holds
    `x` and the continuation denotes `R` whenever its renaming preserves values and its
    variables hold `M` applied to `x`, then the emitted program denotes `R`. -/
theorem schedEmit_linMap {ts : List FieldTy} {m n : Nat} {M : Matrix (Fin m) (Fin n) Int}
    {s : Sched} (hok : schedOk n (rowsOf M) s = true) {P : SLP LinI n m}
    (h : schedSLP n m s = some P) {Γ : Ctxt fieldDialect} (env : Fin n → Ctxt.Var Γ (.fp p))
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
    (V : Ctxt.Valuation Γ) (R : ListDenote ts) (x : Fin n → ZMod p)
    (hx : ∀ i, (env i).lookup V = x i)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (V' : Ctxt.Valuation Γ')
      (zs : Fin m → Ctxt.Var Γ' (.fp p)), Preserves r V V' →
      (∀ j, (zs j).lookup V' = (M.map (Int.cast : Int → ZMod p)).mulVec x j) →
      (kk r zs).denote V' = R) :
    (schedEmit p P env kk).denote V = R := by
  refine schedEmit_denote h env kk V R fun r V' zs hr hzs => hk r V' zs hr fun j => ?_
  rw [funext hx, schedOk_sound hok] at hzs
  exact congrFun (List.ofFn_injective hzs) j

/-- The emission of an instruction is `ArithAt p`-covered when its continuation is. -/
theorem LinI.emit_cov {k : Nat} {Γ : Ctxt fieldDialect} {ts : List FieldTy} (ins : LinI k)
    (env : Fin k → Ctxt.Var Γ (.fp p))
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → Ctxt.Var Γ' (.fp p) → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (z : Ctxt.Var Γ' (.fp p)),
      CoveredM (ArithAt p) (kk r z)) :
    CoveredM (ArithAt p) (LinI.emit p ins env kk) := by
  cases ins with
  | add i j => exact emitT_cov _ _ kk hk
  | sub i j => exact emitT_cov _ _ kk hk
  | scale c i => exact emitT_cov _ _ kk hk
  | copy i => exact hk _ _

/-- The emitted program is `ArithAt p`-covered when its continuation is. -/
theorem schedEmit_cov {ts : List FieldTy} {k m : Nat} (P : SLP LinI k m)
    {Γ : Ctxt fieldDialect} (env : Fin k → Ctxt.Var Γ (.fp p))
    (kk : {Γ' : Ctxt fieldDialect} → Ren Γ Γ' → (Fin m → Ctxt.Var Γ' (.fp p)) → MRC Γ' ts)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (r : Ren Γ Γ') (zs : Fin m → Ctxt.Var Γ' (.fp p)),
      CoveredM (ArithAt p) (kk r zs)) :
    CoveredM (ArithAt p) (schedEmit p P env kk) :=
  SLP.emit_cov (B := fun Γ => Ctxt.Var Γ (.fp p)) (ArithAt p) (fun r v => r v)
    (fun ins env kk => LinI.emit p ins env kk)
    (fun ins env kk hk => LinI.emit_cov ins env kk hk) P env kk hk

end Emit

/-! ## 4. The schedules of Poseidon2 -/

/-- The 4 × 4 schedule converts, over 4 inputs with 4 outputs. -/
theorem quadSched_slp : (schedSLP 4 4 quadSched).isSome = true := by decide

/-- The external schedule converts, over 16 inputs with 16 outputs. -/
theorem externalSched_slp : (schedSLP 16 16 externalSched).isSome = true := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.LinMapSLP
