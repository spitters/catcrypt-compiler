/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of a coalesced body with labels and jumps

`ImageCoalesceCfg.lsemFuelMemF_coalesce` matches a halting run of a body accepted by
`coCfgB σ body L obs` by a run of the coalesced body `body.map (renArr σ)`. This module
states the same simulation for the traced flag machine `lsemFuelMemFLeak`, whose events are
the address events `addr base (scale * index value)` of the array operands and the branch
events of the conditionals.

The two runs take the same steps from states with equal registers and zero flags, so the
index values and the branch decisions are equal. The renaming `renArr σ` moves the base of
a load-tagged `LOADIDX` and of a store-tagged `STOREIDX`, so the event of such an
instruction has its base renamed by `σ`. The map on events is `renEv σ`:
`addr b k ↦ addr (σ b) k`, every other event unchanged. Every other instruction is kept by
`renArr σ`, so its events are kept; they are their own image under `renEv σ` when `σ` fixes
the base of every array operand of the instruction, which `leakFixB σ` checks.

## Main definitions

* `arrBasesOf`: the array base an operand names.
* `leakFixB`, `leakFixCfgB`: an instruction with no array position emits events that
  `renEv σ` fixes; the check of a body.
* `CoStart`: the entry states `lsemFuelMemF_coalesce` relates.
* `CoPub`: the public-equality relation of the coalesced body.

## Main results

* `instrLeakF_coalesce`: the events of the renamed instruction, from a state with the same
  registers and zero flag, are the events of the instruction mapped by `renEv σ`.
* `lsemFuelMemFLeak_coalesce`: a halting traced run of an accepted body with trace `ℓ` is
  matched, with the same fuel, by a halting traced run of the coalesced body with trace
  `ℓ.map (renEv σ)`.
* `fRun_coalesce`: the same statement for `FRun`.
* `memFCT_coalesce`: constant time of the body at `pubEq` gives constant time of the
  coalesced body at `CoPub σ fn body L pubEq`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeakLoop (renEv)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (CoRel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)

variable {σ : String → String}

/-! ## 1. The events of an instruction -/

/-- The array base an operand names. -/
def arrBasesOf : LOperand → List String
  | .arr b _ => [b]
  | .arrIdx b _ _ => [b]
  | _ => []

/-- The address event of an operand whose base `σ` fixes is its own image. -/
theorem opLeakF_fix (r : LstateN) (o : LOperand) (h : ∀ b ∈ arrBasesOf o, σ b = b) :
    (opLeakF r o).map (renEv σ) = opLeakF r o := by
  cases o <;> simp_all [opLeakF, arrBasesOf, renEv]

/-- **The check of the events of one instruction.** An instruction with an array position
    (`arrShapeB`) passes. An `Lopn` without one passes when it is a load-effective-address
    `LEA`, which emits nothing, or when `σ` fixes the base of each of its array operands.
    Every other instruction passes. -/
def leakFixB (σ : String → String) (i : LinstrRM) : Bool :=
  arrShapeB i ||
    match i.1 with
    | .Lopn ds o ss =>
        stripWidthTag o == "LEA" || (ds ++ ss).all fun op => (arrBasesOf op).all fun b => σ b == b
    | _ => true

/-- The check `leakFixB` at every instruction of a body. -/
def leakFixCfgB (σ : String → String) (body : List LinstrRM) : Bool := body.all (leakFixB σ)

theorem leakFixCfgB_instr {body : List LinstrRM} (h : leakFixCfgB σ body = true) {k : Nat}
    {i : LinstrRM} (hi : body[k]? = some i) : leakFixB σ i = true :=
  List.all_eq_true.mp h i (List.mem_of_getElem? hi)

/-- The events of an accepted instruction with no array position are their own image. -/
theorem instrLeakB_fix {i : LinstrRM} (hsh : arrShapeB i = false) (h : leakFixB σ i = true)
    (r : LstateN) : (instrLeakB r i).map (renEv σ) = instrLeakB r i := by
  obtain ⟨w, tag⟩ := i
  simp only [leakFixB, hsh, Bool.false_or] at h
  cases w with
  | Lopn ds o ss =>
      simp only [Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
      simp only [instrLeakB]
      split
      · rfl
      · next hne =>
        rcases h with h | h
        · exact absurd h hne
        · rw [List.map_flatMap]
          exact List.flatMap_congr fun op hop => opLeakF_fix r op (h op hop)
  | Lcond c l => simp [instrLeakB, renEv]
  | _ => simp [instrLeakB]

/-- The events of an instruction with an array position after the renaming of its array
    positions: the base of each address event is renamed by `σ`. -/
theorem instrLeakB_renArr {i : LinstrRM} (hsh : arrShapeB i = true) (r : LstateN) :
    instrLeakB r (renArr σ i) = (instrLeakB r i).map (renEv σ) := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | load a n =>
      simp only [arrShapeB] at hsh
      unfold loadStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          simp [instrLeakB, renArr, renLoad, opLeakF, renEv]
        · simp at hsh
      · simp at hsh
  | store a n =>
      simp only [arrShapeB] at hsh
      unfold storeStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          simp [instrLeakB, renArr, renStore, opLeakF, renEv]
        · simp at hsh
      · simp at hsh
  | zero a n =>
      have hop : ∀ o, opLeakF r (renOpA σ o) = (opLeakF r o).map (renEv σ) := by
        intro o; cases o <;> rfl
      simp only [arrShapeB] at hsh
      unfold zeroStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          have hne : stripWidthTag "ZEROARR" ≠ "LEA" := by decide +kernel
          have hreg : ∀ x, opLeakF r (.reg x) = [] := fun _ => rfl
          simp [instrLeakB, renArr, renZero, hne, hreg, List.flatMap_map, hop, List.map_flatMap]
        · simp at hsh
      · simp at hsh
  | _ => simp [arrShapeB] at hsh

/-- An instruction with an array position is an `Lopn`, and so is its renaming. -/
theorem flagCondCC?_of_arrShape {i : LinstrRM} (hsh : arrShapeB i = true) :
    flagCondCC? i = none ∧ flagCondCC? (renArr σ i) = none := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | load a n =>
      simp only [arrShapeB] at hsh
      unfold loadStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          simp [flagCondCC?, renArr, renLoad]
        · simp at hsh
      · simp at hsh
  | store a n =>
      simp only [arrShapeB] at hsh
      unfold storeStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          simp [flagCondCC?, renArr, renStore]
        · simp at hsh
      · simp at hsh
  | zero a n =>
      simp only [arrShapeB] at hsh
      unfold zeroStruct? at hsh
      split at hsh
      · split at hsh
        · next ho =>
          subst ho
          simp [flagCondCC?, renArr, renZero]
        · simp at hsh
      · simp at hsh
  | _ => simp [arrShapeB] at hsh

/-- **The events of a coalesced instruction on the flag machine.** For an instruction
    accepted by `leakFixB σ` that is no shadow instruction of a call, the renamed instruction
    `renArr σ i` emits, from a state with the registers and the zero flag of `s`, the events
    of `i` from `s` mapped by `renEv σ`. -/
theorem instrLeakF_coalesce {i : LinstrRM} (hfix : leakFixB σ i = true)
    (hn : shadowCall? i.1 = none) {s s' : LstateMF}
    (hreg : s'.prog.base.reg = s.prog.base.reg) (hz : s'.zf = s.zf) :
    instrLeakF (renArr σ i) s' = (instrLeakF i s).map (renEv σ) := by
  by_cases hsh : arrShapeB i = true
  · obtain ⟨e1, e2⟩ := flagCondCC?_of_arrShape (σ := σ) hsh
    simp only [instrLeakF, e1, e2, hreg]
    exact instrLeakB_renArr hsh _
  · have hsh' : arrShapeB i = false := by simpa using hsh
    rw [renArr_of_not_shape hsh' hn]
    unfold instrLeakF
    cases hf : flagCondCC? i with
    | some p => simp [hz, renEv]
    | none =>
        simp only [hreg]
        exact (instrLeakB_fix hsh' hfix _).symm

/-! ## 2. The traced run -/

/-- **The traced run of the coalesced body.** For a body accepted by `coCfgB σ body L obs`
    and by `leakFixCfgB σ`, a halting traced run of the flag machine on `body` with trace
    `ℓ`, from a state `s` of the function `fn` at a position at most `body.length`, is
    matched with the same fuel by a halting traced run on the coalesced body
    `body.map (renArr σ)` from every state `s'` that has the registers, word memory, flags
    and function name of `s` and whose arrays agree with those of `s` through `σ` on the
    names `L` gives the position of `s`. The trace of the coalesced run is `ℓ.map (renEv σ)`:
    each address event has its base renamed by `σ`, with the same offset, and each branch
    event is kept. The final states have equal registers, word memory and flags, and their
    arrays agree through `σ` on `obs`. -/
theorem lsemFuelMemFLeak_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hc : coCfgB σ body L obs = true) (hx : leakFixCfgB σ body = true) :
    ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak}, s.prog.lfn = fn →
      s.prog.base.lpc ≤ body.length →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      s'.zf = s.zf → lsemFuelMemFLeak (singletonProgM fn body) fuel s = some (t, ℓ) →
      ∃ t', lsemFuelMemFLeak (singletonProgM fn (body.map (renArr σ))) fuel s'
          = some (t', ℓ.map (renEv σ))
        ∧ CoRel σ obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
  have hfetch : ∀ {s s' : LstateMF}, s.prog.lfn = fn →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      findInstrMem (singletonProgM fn body) s.prog = body[s.prog.base.lpc]?
        ∧ findInstrMem (singletonProgM fn (body.map (renArr σ))) s'.prog
            = (body[s.prog.base.lpc]?).map (renArr σ) := by
    intro s s' hf hR hfn
    exact ⟨findInstrMem_singleton fn body s.prog hf, by
      rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR, List.getElem?_map]⟩
  have hhalt : ∀ (fuel : Nat) {s s' t : LstateMF} {ℓ : List CTLeak}, s.prog.lfn = fn →
      s.prog.base.lpc ≤ body.length →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      s'.zf = s.zf → body[s.prog.base.lpc]? = none →
      lsemFuelMemFLeak (singletonProgM fn body) fuel s = some (t, ℓ) →
      ∃ t', lsemFuelMemFLeak (singletonProgM fn (body.map (renArr σ))) fuel s'
          = some (t', ℓ.map (renEv σ))
        ∧ CoRel σ obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
    intro fuel s s' t ℓ hf hle hR hfn hz hb h
    obtain ⟨e1, e2⟩ := hfetch hf hR hfn
    rw [lsemFuelMemFLeak_halt _ _ s (e1.trans hb)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hlen : s.prog.base.lpc = body.length := by
      have := List.getElem?_eq_none_iff.mp hb
      omega
    rw [hlen] at hR
    exact ⟨s', lsemFuelMemFLeak_halt _ _ s' (by rw [e2, hb]; rfl), hR.mono (coCfgB_obs hc), hz⟩
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t ℓ hf hle hR hfn hz h
      cases hb : body[s.prog.base.lpc]? with
      | none => exact hhalt 0 hf hle hR hfn hz hb h
      | some i =>
          obtain ⟨e1, -⟩ := hfetch hf hR hfn
          simp [lsemFuelMemFLeak, e1, hb] at h
  | succ n ih =>
      intro s s' t ℓ hf hle hR hfn hz h
      cases hb : body[s.prog.base.lpc]? with
      | none => exact hhalt (n + 1) hf hle hR hfn hz hb h
      | some i =>
          obtain ⟨e1, e2⟩ := hfetch hf hR hfn
          cases he : evalInstrPMemF (singletonProgM fn body) i s with
          | none => simp [lsemFuelMemFLeak, e1, hb, he] at h
          | some u =>
              rw [lsemFuelMemFLeak_step _ _ i s u (e1.trans hb) he] at h
              obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hqe
              obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := evalInstrPMemF_coalesce
                (coCfgB_instr hc hb) (List.getElem?_eq_some_iff.mp hb).1 hR hfn hz he
              obtain ⟨t', ht', hRt, hzt⟩ := ih (hfs.trans hf) hleu hRu hfu hzu hq
              refine ⟨t', ?_, hRt, hzt⟩
              rw [lsemFuelMemFLeak_step _ _ (renArr σ i) s' u' (by rw [e2, hb]; rfl) hu', ht',
                Option.map_some, List.map_append,
                instrLeakF_coalesce (leakFixCfgB_instr hx hb)
                  (by
                    by_contra hne
                    rw [evalInstrPMemF_shadowCall _ i s hne] at he
                    cases he)
                  hR.reg hz]

/-! ## 3. Constant time -/

/-- **The entry states of the coalescing.** `s` is a state of the function `fn` at a
    position at most `body.length`, and `s'` has the registers, word memory, flags, function
    name and zero flag of `s`, with arrays that agree with those of `s` through `σ` on the
    names `L` gives the position of `s`. -/
def CoStart (σ : String → String) (fn : String) (body : List LinstrRM) (L : Nat → List String)
    (s s' : LstateMF) : Prop :=
  s.prog.lfn = fn ∧ s.prog.base.lpc ≤ body.length
    ∧ CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base ∧ s'.prog.lfn = s.prog.lfn
    ∧ s'.zf = s.zf

/-- A state of the function `fn` at a position at most `body.length` is an entry state of
    the coalescing with itself when `σ` fixes the names `L` gives its position. -/
theorem coStart_refl {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {s : LstateMF} (hf : s.prog.lfn = fn) (hle : s.prog.base.lpc ≤ body.length)
    (hfix : ∀ r ∈ L s.prog.base.lpc, σ r = r) : CoStart σ fn body L s s :=
  ⟨hf, hle, ⟨rfl, rfl, rfl, rfl, fun r hr => by rw [hfix r hr]⟩, rfl, rfl⟩

/-- **A terminating run of the coalesced body.** For a body accepted by `coCfgB` and
    `leakFixCfgB`, a terminating run of `body` from `s` with trace `ℓ` gives a terminating
    run of the coalesced body from every `s'` with `CoStart σ fn body L s s'`, with trace
    `ℓ.map (renEv σ)`. -/
theorem fRun_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hc : coCfgB σ body L obs = true) (hx : leakFixCfgB σ body = true)
    {s s' : LstateMF} {ℓ : List CTLeak} (hs : CoStart σ fn body L s s')
    (h : FRun (singletonProgM fn body) s ℓ) :
    FRun (singletonProgM fn (body.map (renArr σ))) s' (ℓ.map (renEv σ)) := by
  obtain ⟨fuel, t, h⟩ := h
  obtain ⟨hf, hle, hR, hfn, hz⟩ := hs
  obtain ⟨t', ht', -, -⟩ := lsemFuelMemFLeak_coalesce hc hx fuel hf hle hR hfn hz h
  exact ⟨fuel, t', ht'⟩

/-- **The public-equality relation of the coalesced body.** Two states are related when
    they are the images, by `CoStart σ fn body L`, of two states related by `pubEq` from
    each of which `body` has a terminating run. -/
def CoPub (σ : String → String) (fn : String) (body : List LinstrRM) (L : Nat → List String)
    (pubEq : LstateMF → LstateMF → Prop) (s₁' s₂' : LstateMF) : Prop :=
  ∃ s₁ s₂, pubEq s₁ s₂ ∧ CoStart σ fn body L s₁ s₁' ∧ CoStart σ fn body L s₂ s₂'
    ∧ (∃ ℓ, FRun (singletonProgM fn body) s₁ ℓ) ∧ (∃ ℓ, FRun (singletonProgM fn body) s₂ ℓ)

/-- **Constant time of the coalesced body.** For a body accepted by `coCfgB σ body L obs`
    and `leakFixCfgB σ`, constant time of `body` on the flag machine at `pubEq` gives
    constant time of the coalesced body `body.map (renArr σ)` at `CoPub σ fn body L pubEq`:
    two terminating runs of the coalesced body, from the images of two `pubEq`-related
    states from which `body` terminates, have equal traces. -/
theorem memFCT_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hc : coCfgB σ body L obs = true) (hx : leakFixCfgB σ body = true)
    {pubEq : LstateMF → LstateMF → Prop} (hct : MemFCT (singletonProgM fn body) pubEq) :
    MemFCT (singletonProgM fn (body.map (renArr σ))) (CoPub σ fn body L pubEq) := by
  rintro s₁' s₂' ℓ₁' ℓ₂' ⟨s₁, s₂, hp, h₁, h₂, ⟨ℓ₁, r₁⟩, ⟨ℓ₂, r₂⟩⟩ hr₁ hr₂
  rw [fRun_unique hr₁ (fRun_coalesce hc hx h₁ r₁), fRun_unique hr₂ (fRun_coalesce hc hx h₂ r₂),
    hct s₁ s₂ ℓ₁ ℓ₂ hp r₁ r₂]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak
