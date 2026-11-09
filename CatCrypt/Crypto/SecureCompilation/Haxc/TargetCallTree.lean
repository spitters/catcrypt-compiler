/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-!
# The call tree of the target semantics of `compileA`

The linked-call step of `haxc_correct_auto` is stated on the decoded program: the bytes of
`compileA` decode to a calling body `pc` followed by the region of the kernel blocks, and `pc`
halts on the address machine `aMachine` with each `call` answered by an oracle on machine states
(`HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'`). The flag machine of `Lprog`
(`lsemFuelMemF`) is not the level of that step: there a linked call is a shadow with no step,
and the theorem reaches the call through the decoded `call` instruction. This module reads the
run of a decoded calling body as a finite call tree over the events of `NFCallTree`: a `call t`
is an event carrying the linked call `LinkCall` (the name of the kernel at the target `t` and the
argument values its layout reads in the entry state) and the machine state at the entry of the
callee; its answer is the state at the return of the callee, or `none` when the callee does not
return. The events project to the events of `NFCallTree.linkSig` (`KCall.call`), the signature
of the source call tree `nfTree`; the answer is a machine state rather than a value, since the
caller continues from the state the kernel leaves, which a value does not determine.

## Main definitions

* `KCall`, `kSig`: a linked call at a machine state, answered by an optional return state.
* `runO`: the fuelled run of a decoded program on a machine, each `call` answered by a partial
  function on states.
* `targetTree`: the call tree of the fuelled run of a decoded program.
* `kernelHandler`: the handler answering a call by the fuelled run of the decoded block of the
  kernel it names.
* `linkRead`: the argument values a call of a linked function of a module reads in a state.
* `Rutt`: the relation between two finite call trees up to relations on events, answers and
  leaves, with the leaves of a failed source run related to every target tree.
* `contractRE`, `contractRA`, `resRel`, `R3Statement`: the event and answer relations of the
  contracts of the linked functions, the relation of the results, and the statement that the
  source and the target call trees of `compileA` are related by them.

## Main results

* `interp_targetTree`: **adequacy**: interpreting the target tree under a handler is the
  fuelled run `runO` at the oracle the handler induces, at every fuel, without side condition.
* `interp_targetTree_kernel`: at `kernelHandler`, the run with each call answered by the
  fuelled run of the kernel block.
* `haltsO_of_runO`, `runO_of_haltsO`: a fuelled run is a run `HaltsO` under the graph of the
  oracle, and every such run is a fuelled run at every large enough fuel.
* `haltsO_of_interp_kernel`, `interp_kernel_of_haltsO`: the interpreted target tree at the
  kernel handler and the runs `HaltsO aMachine (oracleOf ...)` of `haxc_correct_auto`, under
  properties of the compiled code only (the symbol of each call target, call-free blocks).
* `interp_rutt`: two trees related by `Rutt` interpret, under handlers related on related
  events, to related or failed leaves.
* `r3_consequence`: from the relation of `R3Statement` and a target handler meeting the
  contracts, a source run to a value gives a target run reading it back.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO oracleOf runOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open _root_.Hax
open _root_.Hax.InlineLocalClosures

/-! ## Linked calls at machine states -/

/-- A linked call at a machine state: the linked call (the name of the kernel and the argument
    values) and the state at the entry of the callee, after the stack operations of the call. -/
structure KCall (σ : Type) where
  /-- The linked call, an event of `linkSig`. -/
  call : LinkCall
  /-- The state at the entry of the callee. -/
  entry : σ

/-- The event signature of linked calls at machine states: a call is answered by the state at
    the return of the callee, or by `none` when the callee does not return. -/
abbrev kSig (σ : Type) : EventSig where
  Event := KCall σ
  Resp := fun _ => Option σ

/-! ## The fuelled run with an oracle and its call tree -/

section Run

variable {σ : Type}

/-- The fuelled run of `prog` on `M` from `pc`, each `call t` answered by the oracle `o t` on
    the state after the stack operations of the call, the run continuing at the next index on
    the state after the stack operation of the return. Every other instruction is a `step`. -/
def runO (M : Machine σ) (prog : List RInstr) (o : Nat → σ → Option σ) :
    Nat → Nat → σ → Option σ
  | 0, _, _ => none
  | fuel + 1, pc, s =>
    match prog[pc]? with
    | some (.call t) =>
      (o t ((callOps (pc + 1)).foldl M.exec s)).bind fun sc =>
        runO M prog o fuel (pc + 1) (retOps.foldl M.exec sc)
    | _ =>
      match step M prog pc s with
      | none => none
      | some (.halt s') => some s'
      | some (.go pc' s') => runO M prog o fuel pc' s'

/-- **The target call tree** of the decoded program `prog` on `M` at the fuel `fuel`, from `pc`
    and `s`: a `call t` is the event of the linked call of the symbol `sym t` with the argument
    values `rd (sym t)` reads in the entry state of the callee, continued at the next index
    from the return state of the answer; every other instruction is a `step`. -/
def targetTree (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
    (rd : String → σ → List Value) : Nat → Nat → σ → CallTree (kSig σ) (Option σ)
  | 0, _, _ => .ret none
  | fuel + 1, pc, s =>
    match prog[pc]? with
    | some (.call t) =>
      .vis (⟨⟨sym t, rd (sym t) ((callOps (pc + 1)).foldl M.exec s)⟩,
          (callOps (pc + 1)).foldl M.exec s⟩ : KCall σ) fun (r : Option σ) =>
        match r with
        | some sc => targetTree M prog sym rd fuel (pc + 1) (retOps.foldl M.exec sc)
        | none => .ret none
    | _ =>
      match step M prog pc s with
      | none => .ret none
      | some (.halt s') => .ret (some s')
      | some (.go pc' s') => targetTree M prog sym rd fuel pc' s'

/-- The oracle a handler induces: a call to the target `t` from the state `s` is answered by
    the handler at the linked call of `sym t`. -/
def oracleOfHandler (sym : Nat → String) (rd : String → σ → List Value)
    (h : ∀ e : (kSig σ).Event, (kSig σ).Resp e) : Nat → σ → Option σ :=
  fun t s => h (⟨⟨sym t, rd (sym t) s⟩, s⟩ : KCall σ)

/-- **Adequacy of the target call tree**: interpreting the target tree under `h` is the
    fuelled run `runO` at the oracle `h` induces, at every fuel. -/
theorem interp_targetTree (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
    (rd : String → σ → List Value) (h : ∀ e : (kSig σ).Event, (kSig σ).Resp e) :
    ∀ (fuel pc : Nat) (s : σ),
      interp h (targetTree M prog sym rd fuel pc s) =
        runO M prog (oracleOfHandler sym rd h) fuel pc s := by
  intro fuel
  induction fuel with
  | zero => intro pc s; rfl
  | succ fuel ih =>
    intro pc s
    simp only [targetTree, runO]
    split
    · change interp h (match oracleOfHandler sym rd h _ ((callOps (pc + 1)).foldl M.exec s) with
        | some sc => _ | none => _) = _
      cases oracleOfHandler sym rd h _ ((callOps (pc + 1)).foldl M.exec s) with
      | none => rfl
      | some sc => exact ih _ _
    · split
      · rfl
      · rfl
      · exact ih _ _

/-- The handler answering a linked call by the fuelled run on `M` of the block `blk f` of the
    kernel `f` it names, from the entry state, at the fuel `fuelK`. -/
def kernelHandler (M : Machine σ) (blk : String → List RInstr) (fuelK : Nat) :
    ∀ e : (kSig σ).Event, (kSig σ).Resp e :=
  fun e => run M (blk (KCall.call e).name) fuelK 0 (KCall.entry e)

/-- **Adequacy at the kernel handler**: interpreting the target tree under `kernelHandler` is
    the fuelled run in which a call to `t` runs the block of the kernel `sym t`. -/
theorem interp_targetTree_kernel (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
    (rd : String → σ → List Value) (blk : String → List RInstr) (fuelK fuel pc : Nat) (s : σ) :
    interp (kernelHandler M blk fuelK) (targetTree M prog sym rd fuel pc s) =
      runO M prog (fun t s₀ => run M (blk (sym t)) fuelK 0 s₀) fuel pc s :=
  interp_targetTree M prog sym rd _ fuel pc s

/-! ### Fuelled runs and halting runs -/

/-- A step that halts is at a `ret` and keeps the state. -/
theorem step_halt {M : Machine σ} {prog : List RInstr} {pc : Nat} {s s' : σ}
    (h : step M prog pc s = some (.halt s')) : prog[pc]? = some .ret ∧ s = s' := by
  unfold step at h
  split at h <;> simp_all
  obtain ⟨c, -, hc⟩ := h
  split at hc <;> simp at hc

/-- **A fuelled run is a halting run under the graph of its oracle.** -/
theorem haltsO_of_runO {M : Machine σ} {prog : List RInstr} {o : Nat → σ → Option σ} :
    ∀ {fuel pc : Nat} {s s' : σ}, runO M prog o fuel pc s = some s' →
      HaltsO M (fun t x y => o t x = some y) prog pc s s' := by
  intro fuel
  induction fuel with
  | zero => intro pc s s' h; simp [runO] at h
  | succ fuel ih =>
    intro pc s s' h
    simp only [runO] at h
    split at h
    · rename_i t hpc
      obtain ⟨sc, hsc, hr⟩ := Option.bind_eq_some_iff.mp h
      exact .call hpc hsc (ih hr)
    · rename_i hnc
      split at h
      · simp at h
      · rename_i s₁ hs
        cases h
        obtain ⟨hret, rfl⟩ := step_halt hs
        exact .ret hret
      · rename_i pc' s₁ hs
        exact .go hs (ih h)

/-- A fuelled run is a fuelled run at every larger fuel. -/
theorem runO_mono {M : Machine σ} {prog : List RInstr} {o : Nat → σ → Option σ} :
    ∀ {fuel fuel' pc : Nat} {s s' : σ}, fuel ≤ fuel' → runO M prog o fuel pc s = some s' →
      runO M prog o fuel' pc s = some s' := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pc s s' _ h; simp [runO] at h
  | succ fuel ih =>
    intro fuel' pc s s' hle h
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [runO] at h ⊢
    split at h
    · obtain ⟨sc, hsc, hr⟩ := Option.bind_eq_some_iff.mp h
      rw [hsc, Option.bind_some]
      exact ih (by omega) hr
    · split at h
      · simp at h
      · exact h
      · exact ih (by omega) h

/-- A fuelled run under an oracle is a fuelled run under every oracle with more answers. -/
theorem runO_mono_oracle {M : Machine σ} {prog : List RInstr} {o o' : Nat → σ → Option σ}
    (ho : ∀ t x y, o t x = some y → o' t x = some y) :
    ∀ {fuel pc : Nat} {s s' : σ}, runO M prog o fuel pc s = some s' →
      runO M prog o' fuel pc s = some s' := by
  intro fuel
  induction fuel with
  | zero => intro pc s s' h; simp [runO] at h
  | succ fuel ih =>
    intro pc s s' h
    simp only [runO] at h ⊢
    split at h
    · obtain ⟨sc, hsc, hr⟩ := Option.bind_eq_some_iff.mp h
      rw [ho _ _ _ hsc, Option.bind_some]
      exact ih hr
    · split at h
      · simp at h
      · exact h
      · exact ih h

/-- **A halting run under an oracle is a fuelled run**: for a family of partial oracles
    increasing in their index `j`, a run `HaltsO` under the union of their graphs is a fuelled
    run at every large enough index and fuel. -/
theorem runO_of_haltsO {M : Machine σ} {prog : List RInstr} {o : Nat → Nat → σ → Option σ}
    (hmono : ∀ j j' t x y, j ≤ j' → o j t x = some y → o j' t x = some y)
    {pc : Nat} {s s' : σ}
    (h : HaltsO M (fun t x y => ∃ j, o j t x = some y) prog pc s s') :
    ∃ j fuel, ∀ j' fuel', j ≤ j' → fuel ≤ fuel' → runO M prog (o j') fuel' pc s = some s' := by
  induction h with
  | @ret pc s hret =>
    refine ⟨0, 1, fun j' fuel' _ hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp [runO, hret, step]
  | @go pc s pc' s₁ s₂ hs _ ih =>
    obtain ⟨j, fuel, H⟩ := ih
    refine ⟨j, fuel + 1, fun j' fuel' hj hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    have hnc : ∀ t, prog[pc]? ≠ some (.call t) := by
      intro t hp
      simp [step, hp] at hs
    simp only [runO]
    cases hp : prog[pc]? with
    | none => simp [step, hp] at hs
    | some i =>
      cases i with
      | call t => exact absurd hp (hnc t)
      | _ => simp only [hs]; exact H j' f hj (by omega)
  | @call pc t s sc s₂ hp hc _ ih =>
    obtain ⟨j₁, hj₁⟩ := hc
    obtain ⟨j, fuel, H⟩ := ih
    refine ⟨max j j₁, fuel + 1, fun j' fuel' hj hf => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [runO, hp]
    rw [hmono j₁ j' _ _ _ (by omega) hj₁, Option.bind_some]
    exact H j' f (by omega) (by omega)

end Run

/-! ## The target tree of a decoded calling body on the address machine -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL RunL.halts haltsC_runL)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime)

/-- A fuelled run of a block on a machine is a halting run without call. -/
theorem haltsNoCall_of_run {σ : Type} {M : Machine σ} {q : List RInstr} :
    ∀ {fuel pc : Nat} {s s' : σ}, run M q fuel pc s = some s' → HaltsNoCall M q pc s s' := by
  intro fuel
  induction fuel with
  | zero => intro pc s s' h; simp [run] at h
  | succ fuel ih =>
    intro pc s s' h
    simp only [run] at h
    split at h
    · simp at h
    · rename_i s₁ hs
      cases h
      obtain ⟨hret, rfl⟩ := step_halt hs
      exact ⟨pc, .refl _ _, hret⟩
    · rename_i pc' s₁ hs
      obtain ⟨pc'', hr, hret⟩ := ih h
      exact ⟨pc'', .next hs hr, hret⟩

/-- A fuelled run is a fuelled run at every larger fuel. -/
theorem run_mono {σ : Type} {M : Machine σ} {q : List RInstr} :
    ∀ {fuel fuel' pc : Nat} {s s' : σ}, fuel ≤ fuel' → run M q fuel pc s = some s' →
      run M q fuel' pc s = some s' := by
  intro fuel
  induction fuel with
  | zero => intro fuel' pc s s' _ h; simp [run] at h
  | succ fuel ih =>
    intro fuel' pc s s' hle h
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    simp only [run] at h ⊢
    split at h
    · simp at h
    · exact h
    · exact ih (by omega) h

/-- **A fuelled run of a block on the address machine is a leaky run** under every regime. -/
theorem runOf_of_run (r : DoitRegime) {q : List RInstr} {fuel : Nat} {s s' : AState}
    (h : run aMachine q fuel 0 s = some s') : ∃ tr, runOf r q s tr s' :=
  haltsC_runL r (halts_of_haltsNoCall (haltsNoCall_of_run h))

/-- **A leaky run of a block without `call` is a fuelled run** on the address machine. -/
theorem run_of_runOf {r : DoitRegime} {q : List RInstr}
    (hq : ∀ (i t : Nat), q[i]? ≠ some (RInstr.call t)) {s s' : AState} {tr : List CT.CTLeak}
    (h : runOf r q s tr s') : ∃ fuel, run aMachine q fuel 0 s = some s' := by
  have hc : HaltsC aMachine q 0 s s' := RunL.halts h
  suffices H : ∀ {pc : Nat} {s s' : AState}, HaltsC aMachine q pc s s' →
      HaltsNoCall aMachine q pc s s' from run_of_haltsNoCall (H hc)
  intro pc s s' h
  induction h with
  | ret hret => exact ⟨_, .refl _ _, hret⟩
  | go hs _ ih =>
    obtain ⟨pc'', hr, hret⟩ := ih
    exact ⟨pc'', .next hs hr, hret⟩
  | call hp _ _ _ _ => exact absurd hp (hq _ _)

/-- **The interpreted target tree is a run of `haxc_correct_auto`'s shape.** Let every `call t`
    of the calling body `pc` name, by `sym`, a kernel `sym t` of `fs` whose target is `t`. A
    leaf `some s'` of the target tree interpreted under the kernel handler of the blocks `q` is
    a halting run of `pc` on `aMachine` with each call answered by the leaky runs of the block
    of its kernel (`oracleOf`), the oracle of `tabOracle` without the guard of the
    preconditions. -/
theorem haltsO_of_interp_kernel (pc : List RInstr) (fs : List String)
    (tgtOf : String → Nat) (sym : Nat → String) (rd : String → AState → List Value)
    (q : String → List RInstr) (r : DoitRegime)
    (hsym : ∀ (i t : Nat), pc[i]? = some (RInstr.call t) → sym t ∈ fs ∧ tgtOf (sym t) = t)
    (fuelK fuel : Nat) {s s' : AState}
    (h : interp (kernelHandler aMachine q fuelK) (targetTree aMachine pc sym rd fuel 0 s)
      = some s') :
    HaltsO aMachine (oracleOf fs tgtOf fun f => runOf r (q f)) pc 0 s s' := by
  rw [interp_targetTree_kernel] at h
  -- Only the call targets of `pc` are queried.
  suffices H : ∀ {fuel i : Nat} {s s' : AState},
      runO aMachine pc (fun t s₀ => run aMachine (q (sym t)) fuelK 0 s₀) fuel i s = some s' →
      HaltsO aMachine (oracleOf fs tgtOf fun f => runOf r (q f)) pc i s s' from H h
  intro fuel
  induction fuel with
  | zero => intro i s s' h; simp [runO] at h
  | succ fuel ih =>
    intro i s s' h
    simp only [runO] at h
    split at h
    · rename_i t hpc
      obtain ⟨sc, hsc, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨hmem, htgt⟩ := hsym i t hpc
      obtain ⟨tr, htr⟩ := runOf_of_run r hsc
      exact .call hpc ⟨sym t, hmem, htgt, tr, htr⟩ (ih hr)
    · split at h
      · simp at h
      · rename_i s₁ hs
        cases h
        obtain ⟨hret, rfl⟩ := step_halt hs
        exact .ret hret
      · rename_i pc' s₁ hs
        exact .go hs (ih h)

/-- **Every run of `haxc_correct_auto`'s shape is an interpreted target tree.** Let every
    kernel `f` of `fs` have a block `q f` without `call`, and let `sym` recover each kernel of
    `fs` from its target. A halting run of the calling body `pc` on `aMachine` with each call
    answered by the leaky runs of the block of its kernel is a leaf of the target tree
    interpreted under the kernel handler, at every large enough kernel fuel and fuel. -/
theorem interp_kernel_of_haltsO (pc : List RInstr) (fs : List String) (tgtOf : String → Nat)
    (sym : Nat → String) (rd : String → AState → List Value) (q : String → List RInstr)
    (r : DoitRegime) (hsym : ∀ f ∈ fs, sym (tgtOf f) = f)
    (hq : ∀ f ∈ fs, ∀ (i t : Nat), (q f)[i]? ≠ some (RInstr.call t)) {s s' : AState}
    (h : HaltsO aMachine (oracleOf fs tgtOf fun f => runOf r (q f)) pc 0 s s') :
    ∃ fuelK fuel, ∀ fuelK' fuel', fuelK ≤ fuelK' → fuel ≤ fuel' →
      interp (kernelHandler aMachine q fuelK') (targetTree aMachine pc sym rd fuel' 0 s)
        = some s' := by
  have h' : HaltsO aMachine
      (fun t x y => ∃ j, (fun j t s₀ => run aMachine (q (sym t)) j 0 s₀) j t x = some y)
      pc 0 s s' := by
    refine h.mono fun t x y ho => ?_
    obtain ⟨f, hf, ht, tr, hx⟩ := ho
    obtain ⟨j, hj⟩ := run_of_runOf (hq f hf) hx
    refine ⟨j, ?_⟩
    simp only
    rw [← ht, hsym f hf]
    exact hj
  obtain ⟨j, fuel, H⟩ := runO_of_haltsO (o := fun j t s₀ => run aMachine (q (sym t)) j 0 s₀)
    (fun j j' t x y hle hr => run_mono hle hr) h'
  exact ⟨j, fuel, fun fuelK' fuel' hj hf => by
    rw [interp_targetTree_kernel]; exact H fuelK' fuel' hj hf⟩

/-! ## The target tree of a module -/

open CatCrypt.Crypto.Hax (HaxModule LinkedFn)

/-- The argument values a call of the linked function `f` of the module `m` reads in the state
    `s`: the read of the arguments of its layout; no value for another name. -/
def linkRead (m : HaxModule) (f : String) (s : AState) : List Value :=
  match m.linked.find? (·.name == f) with
  | some l => l.layout.args.map (·.read s)
  | none => []

/-! ## Relating call trees up to the contracts (the statement of R3) -/

/-- **Two finite call trees related up to relations** on events `RE`, on answers `RA` and on
    leaves `RR`: leaves related by `RR`; or a source leaf that fails (`Fail`), related to every
    target tree; or two events related by `RE` whose continuations are related at every pair
    of answers related by `RA`. The finite counterpart of the relation `rutt` of interaction
    trees, with a failed source run as the partial-correctness escape. -/
inductive Rutt {E₁ E₂ : EventSig} {R₁ R₂ : Type} (RE : E₁.Event → E₂.Event → Prop)
    (RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop)
    (RR : R₁ → R₂ → Prop) (Fail : R₁ → Prop) : CallTree E₁ R₁ → CallTree E₂ R₂ → Prop
  | ret {r₁ : R₁} {r₂ : R₂} (h : RR r₁ r₂) : Rutt RE RA RR Fail (.ret r₁) (.ret r₂)
  | fail {r₁ : R₁} {t₂ : CallTree E₂ R₂} (h : Fail r₁) : Rutt RE RA RR Fail (.ret r₁) t₂
  | vis {e₁ : E₁.Event} {e₂ : E₂.Event} {k₁ : E₁.Resp e₁ → CallTree E₁ R₁}
      {k₂ : E₂.Resp e₂ → CallTree E₂ R₂} (he : RE e₁ e₂)
      (hk : ∀ a₁ a₂, RA e₁ e₂ a₁ a₂ → Rutt RE RA RR Fail (k₁ a₁) (k₂ a₂)) :
      Rutt RE RA RR Fail (.vis e₁ k₁) (.vis e₂ k₂)

/-- **Interpretation of related trees**: under handlers whose answers at related events are
    related, two related trees interpret to a failed source leaf or to related leaves. -/
theorem interp_rutt {E₁ E₂ : EventSig} {R₁ R₂ : Type} {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (h₁ : ∀ e : E₁.Event, E₁.Resp e) (h₂ : ∀ e : E₂.Event, E₂.Resp e)
    (hh : ∀ e₁ e₂, RE e₁ e₂ → RA e₁ e₂ (h₁ e₁) (h₂ e₂))
    {t₁ : CallTree E₁ R₁} {t₂ : CallTree E₂ R₂} (h : Rutt RE RA RR Fail t₁ t₂) :
    Fail (interp h₁ t₁) ∨ RR (interp h₁ t₁) (interp h₂ t₂) := by
  induction h with
  | ret h => exact .inr h
  | fail h => exact .inl h
  | vis he _ ih => exact ih _ _ (hh _ _ he)

/-- **The event relation of the contracts**: a source call of the linked function `l` of `m`
    on the values `args` and a target call at the entry state `s`, with the same linked call,
    the values of the arguments the layout of `l` reads in `s`, and `s` satisfying the
    precondition of `l`. -/
def contractRE (m : HaxModule) (e₁ : linkSig.Event) (e₂ : (kSig AState).Event) : Prop :=
  KCall.call e₂ = e₁ ∧ ∃ l, m.linked.find? (·.name == LinkCall.name e₁) = some l ∧
    l.pre (KCall.entry e₂) ∧ LinkCall.args e₁ = l.layout.args.map (·.read (KCall.entry e₂))

/-- **The answer relation of the contracts**: the source answer is the meaning of `l` on the
    arguments, and a value of the meaning is answered by the target with a return state that
    the postcondition of `l` relates to the entry state and from which the layout of `l` reads
    the value back. -/
def contractRA (m : HaxModule) (e₁ : linkSig.Event) (e₂ : (kSig AState).Event)
    (a₁ : linkSig.Resp e₁) (a₂ : (kSig AState).Resp e₂) : Prop :=
  ∃ l, m.linked.find? (·.name == LinkCall.name e₁) = some l ∧
    (a₁ : Option Value) = l.sem (LinkCall.args e₁) ∧
    ∀ v, (a₁ : Option Value) = some v → ∃ s', (a₂ : Option AState) = some s' ∧
      l.post (KCall.entry e₂) s' ∧ l.layout.ResultOf (KCall.entry e₂) s' v

/-- **The relation of the results**: a source value that is not a control-flow value is read
    back by `σ` from the target return state, from the entry state `sa`. -/
def resRel (σ : AbiLayout) (sa : AState) (r₁ : Outcome × Env) (r₂ : Option AState) : Prop :=
  ∀ v, r₁.1 = .val v → v.isControlFlow = false → ∃ s', r₂ = some s' ∧ σ.ResultOf sa s' v

/-- A source leaf that is not a value that is not a control-flow value. -/
def srcFail (r₁ : Outcome × Env) : Prop :=
  ∀ v, r₁.1 = .val v → v.isControlFlow = true

/-- A target handler meets the contracts of the linked functions of `m`: at related events, the
    source handler of the meanings and the target handler give related answers. -/
def HandlerMeets (m : HaxModule) (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) :
    Prop :=
  ∀ e₁ e₂, contractRE m e₁ e₂ → contractRA m e₁ e₂ (linkHandler m e₁) (h₂ e₂)

/-- **The statement of R3**: on a module whose linked functions are linked kernels with
    distinct names, the bytes of `compileA` decode to a calling body `pc` followed by the
    region `Q` of the kernel blocks, with a symbol map `sym` of its call targets, such that from
    every entry state satisfying `σ.Regions` and every source environment `σ` reads off it, the
    source call tree `nfTree` of the entry at the tree table of `m` and every source fuel is
    related, at some target fuel, to the target call tree of `pc` by the relations of the
    contracts (`contractRE`, `contractRA`), the read-back of the result (`resRel`) and the
    escape of a failed source run (`srcFail`). -/
def R3Statement : Prop :=
  ∀ (m : HaxModule) (σ : AbiLayout) (fname : String) (P : VIR.JasminLprogExport.Lprog)
    (bytes : List (BitVec 8)), compileA m σ fname = some (P, bytes) →
    (m.linked.map (·.name)).Nodup → (∀ l ∈ m.linked, RegionLinkCall.LinkedKernel l) →
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      X86Backend.LprogBytesDecode.decodeLprog bytes =
          some (pc ++ X86Backend.LprogBytesLink.shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel, ∃ fuelT,
          Rutt (contractRE m) (contractRA m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (targetTree aMachine pc sym (linkRead m) fuelT 0 sa)

/-- **The consequence of R3**: from related source and target trees, under every target handler
    meeting the contracts, a source run of the call tree under the meanings of the linked
    functions to a value that is not a control-flow value is read back by `σ` from the leaf of
    the target tree under the handler. -/
theorem r3_consequence (m : HaxModule) (σ : AbiLayout) (sa : AState)
    (h₂ : ∀ e : (kSig AState).Event, (kSig AState).Resp e) (hh : HandlerMeets m h₂)
    {t₁ : CallTree linkSig (Outcome × Env)} {t₂ : CallTree (kSig AState) (Option AState)}
    (hr : Rutt (contractRE m) (contractRA m) (resRel σ sa) srcFail t₁ t₂)
    {v : Value} {env' : Env} (hv : interp (linkHandler m) t₁ = (.val v, env'))
    (hcf : v.isControlFlow = false) :
    ∃ s', interp h₂ t₂ = some s' ∧ σ.ResultOf sa s' v := by
  rcases interp_rutt (linkHandler m) h₂ hh hr with hf | hR
  · rw [hv] at hf
    have := hf v rfl
    rw [hcf] at this
    exact absurd this (by simp)
  · exact hR v (by rw [hv]) hcf

end CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
