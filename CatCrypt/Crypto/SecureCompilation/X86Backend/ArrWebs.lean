/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FreshenArr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGMemF

@[expose] public section

set_option autoImplicit false

/-!
# Array names split into webs

An array name of a typed virtual body may carry unrelated arrays at different positions,
for example a buffer written afresh in each of two phases. The pass `arrWebs` gives each
web of an array name its own name: a web is a class of the live occurrences of the name,
joined across the control-flow edges along which the name stays live and is not written,
and split at each write that does not read the written name. A loop-carried array, live
around the back edge and written in the loop, stays one web.

The renaming is a position map `w : Nat → String → String`: the array positions of the
instruction at `k` are renamed by `w k`, except the array it writes, renamed by `w (k + 1)`
(`stepRen`, `webRen`). The step renaming `stepRen w ao k i` is a renaming of the array
positions of one instruction in the sense of `ImageCoalesceCfg.renArr`, so every step is
checked by the coalescing check `coInstrB` of that renaming, and the simulation of one
step is `ImageCoalesceCfg.evalInstrPMemF_coalesce` or `ImageCoalesceCfg.callStep_coalesce`.

The position map computed by `webMap` is not trusted. The check `webB` accepts it when
every instruction passes `coInstrB` under its step renaming, the step renaming agrees with
`w k` on the names live before the instruction and with `w k'` on the names live at each
successor `k'`, `w 0` fixes the names live at entry and `w body.length` fixes the names
read after the body.

## Main definitions

* `stepRen`, `webRen`: the renaming of one instruction and of a body by a position map.
* `webSuccs`: the successor positions of an instruction.
* `webInstrB`, `webB`: the check of one instruction and of a body.
* `WebSt`, `webMap`, `arrWebs`: the webs of a body by union-find over the live occurrences,
  their names, and the pass.

## Main results

* `findLabelMem_webRen`, `evalInstrPMemF_congr_labels`: the renamed body has the labels of
  the body, and a flag-machine step reads a singleton program only through its labels.
* `mem_webSuccs_of_nextPc`: a step of the flag machine reaches a position of `webSuccs`.
* `step_webs`: one step of an accepted instruction is matched by a step of the renamed
  instruction in the renamed body.
* `lsemFuelMemF_webs`: a halting run of an accepted body is matched, with the same fuel,
  by a halting run of the renamed body from a related state, into a related state.
* `lsemFuelMemF_webs_entry`: the same run from position `0`, with the arrays of the names
  live at entry and of the names read after the body at their own names.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (CoRel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes
  shadowCall? shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc
  evalInstrPMemF_next)

/-! ## 1. The renaming by a position map -/

/-- **The renaming of the instruction `i` at position `k`** by the position map `w`, for the
    result lengths `ao` of the called symbols: the array `i` writes (`wrArr ao i`) is renamed
    by `w (k + 1)`, every other name by `w k`. -/
def stepRen (w : Nat → String → String) (ao : String → Option Nat) (k : Nat) (i : LinstrRM) :
    String → String :=
  fun r => if wrArr ao i = some r then w (k + 1) r else w k r

/-- **The renamed body**: the instruction at each position `k` with its array positions
    renamed by `stepRen w ao k`. -/
def webRen (w : Nat → String → String) (ao : String → Option Nat) (body : List LinstrRM) :
    List LinstrRM :=
  body.mapIdx fun k i => renArr (stepRen w ao k i) i

/-- **The successor positions** of the instruction `i` at position `k` of `body`: the
    position after the target label of an unconditional jump; the next position and the
    position after the target label of a conditional jump; the next position otherwise. -/
def webSuccs (body : List LinstrRM) (k : Nat) (i : LinstrRM) : List Nat :=
  match i.1 with
  | .Lgoto (_, l) => (findLabelMem l body).toList.map (· + 1)
  | .Lcond _ l => (k + 1) :: (findLabelMem l body).toList.map (· + 1)
  | _ => [k + 1]

/-- **The check of the instruction `i` at position `k`** for the position map `w` and the
    liveness certificate `L`: `i` passes the coalescing check `coInstrB` under its step
    renaming, which agrees with `w k` on the names live before `i` and with `w k'` on the
    names live at each successor `k'`. -/
def webInstrB (w : Nat → String → String) (body : List LinstrRM) (L : Nat → List String)
    (k : Nat) (i : LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    Bool :=
  coInstrB (stepRen w ao k i) body L k i aa ao
    && (L k).all (fun r => stepRen w ao k i r == w k r)
    && (webSuccs body k i).all fun k' => (L k').all fun r => stepRen w ao k i r == w k' r

/-- **The check of a position map** `w` for `body`, against the liveness certificate `L`,
    the names `obs` read after the body, the array positions `aa` and the result lengths
    `ao` of the called symbols: `obs` is in `L body.length`, every instruction passes
    `webInstrB`, `w 0` fixes the names of `L 0`, and `w body.length` fixes the names of
    `obs`. -/
def webB (w : Nat → String → String) (body : List LinstrRM) (L : Nat → List String)
    (obs : List String) (aa : String → Nat → Option Nat) (ao : String → Option Nat) : Bool :=
  subB obs (L body.length)
    && ((List.range body.length).all fun k =>
      match body[k]? with
      | some i => webInstrB w body L k i aa ao
      | none => true)
    && (L 0).all (fun r => w 0 r == r)
    && obs.all (fun r => w body.length r == r)

theorem webB_obs {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : webB w body L obs aa ao = true) : ∀ r ∈ obs, r ∈ L body.length := by
  unfold webB at h
  simp only [Bool.and_eq_true] at h
  exact subB_spec h.1.1.1

theorem webB_instr {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : webB w body L obs aa ao = true) {k : Nat} {i : LinstrRM} (hi : body[k]? = some i) :
    webInstrB w body L k i aa ao = true := by
  unfold webB at h
  simp only [Bool.and_eq_true] at h
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have := (List.all_eq_true.mp h.1.1.2) k (List.mem_range.mpr hk)
  rw [hi] at this
  exact this

theorem webB_entry {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : webB w body L obs aa ao = true) : ∀ r ∈ L 0, w 0 r = r := by
  unfold webB at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem webB_exit {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : webB w body L obs aa ao = true) : ∀ r ∈ obs, w body.length r = r := by
  unfold webB at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.2

/-! ## 2. Labels and successors -/

/-- The relation of two states through `σ` on `A` is one through every renaming that agrees
    with `σ` on `A`. -/
theorem coRel_congr {σ τ : String → String} {A : List String} {s s' : LstateM}
    (h : CoRel σ A s s') (hστ : ∀ r ∈ A, σ r = τ r) : CoRel τ A s s' :=
  ⟨h.reg, h.mem, h.cf, h.of, fun r hr => by rw [← hστ r hr]; exact h.arr r hr⟩

/-- The renamed body has the label positions of the body. -/
theorem findLabelMem_webRen (w : Nat → String → String) (ao : String → Option Nat)
    (l : LLabel) (body : List LinstrRM) :
    findLabelMem l (webRen w ao body) = findLabelMem l body := by
  have key : ∀ A : List LinstrRM, JasminLsemLabeled.findLabel l (A.map Prod.fst)
      = (A.map fun i => JasminLsemLabeled.isLabel l i.1).findIdx? id := by
    intro A
    unfold JasminLsemLabeled.findLabel
    rw [List.findIdx?_map, List.findIdx?_map]
    rfl
  unfold findLabelMem
  rw [key, key]
  congr 1
  apply List.ext_getElem (by simp [webRen])
  intro n h1 h2
  simp only [webRen, List.getElem_map, List.getElem_mapIdx, isLabel_renArr]

/-- **A flag-machine step reads a singleton program only through its labels.** -/
theorem evalInstrPMemF_congr_labels {fn : String} {b1 b2 : List LinstrRM}
    (h : ∀ l, findLabelMem l b1 = findLabelMem l b2) (j : LinstrRM) (s : LstateMF) :
    evalInstrPMemF (singletonProgM fn b1) j s = evalInstrPMemF (singletonProgM fn b2) j s := by
  have hj : evalJumpMem (singletonProgM fn b1) = evalJumpMem (singletonProgM fn b2) := by
    funext l p
    simp only [evalJumpMem, singletonProgM, h]
  unfold evalInstrPMemF evalInstrPMemL
  rw [hj]
  rfl

/-- **A step reaches a successor.** A position reached from `k` by the instruction `i`
    under `NextPc` is in `webSuccs body k i`. -/
theorem mem_webSuccs_of_nextPc {body : List LinstrRM} {k k' : Nat} {i : LinstrRM}
    (h : NextPc (body.map Prod.fst) i.1 k k') : k' ∈ webSuccs body k i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lgoto x =>
      obtain ⟨f, l⟩ := x
      obtain ⟨q, hq, rfl⟩ := h
      simp only [webSuccs]
      have : findLabelMem l body = some q := hq
      simp [this]
  | Lcond c l =>
      simp only [webSuccs]
      rcases h with rfl | ⟨q, hq, rfl⟩
      · simp
      · have : findLabelMem l body = some q := hq
        simp [this]
  | Lret => exact absurd h id
  | _ => simp only [NextPc] at h; subst h; simp [webSuccs]

/-! ## 3. The step -/

/-- **One step of a renamed instruction.** For an instruction `i` accepted by `webInstrB`
    at the position `k < body.length` of a state `s`, at an instruction set `I` whose steps
    contain those of `x86Isa` and whose further steps are local calls at the array positions
    `aa` and the result lengths `ao`, a step from `s` is matched by a step of the renamed
    instruction in the renamed body from a state related to `s` through `w k` on `L k`, with
    the same function name and zero flag. The successor states are related through `w` at
    the successor position, which is at most `body.length`. -/
theorem step_webs {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {w : Nat → String → String}
    {i : LinstrRM} {s s' t : LstateMF}
    (hc : webInstrB w body L s.prog.base.lpc i aa ao = true)
    (hlt : s.prog.base.lpc < body.length)
    (hR : CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base)
    (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (h : I.step (singletonProgM fn body) i s = some t) :
    ∃ t', I.step (singletonProgM fn (webRen w ao body))
        (renArr (stepRen w ao s.prog.base.lpc i) i) s' = some t'
      ∧ CoRel (w t.prog.base.lpc) (L t.prog.base.lpc) t.prog.base t'.prog.base
      ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc ≤ body.length := by
  unfold webInstrB at hc
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hco, hpre⟩, hsucc⟩ := hc
  have hRσ := coRel_congr hR (fun r hr => (hpre r hr).symm)
  have hpost : ∀ k', NextPc (body.map Prod.fst) i.1 s.prog.base.lpc k' →
      ∀ r ∈ L k', stepRen w ao s.prog.base.lpc i r = w k' r :=
    fun k' hn => hsucc k' (mem_webSuccs_of_nextPc hn)
  rcases hcl _ i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, hlen⟩
  · obtain ⟨t', ht', hRt, hfn', hfs, hz', hle'⟩ := evalInstrPMemF_coalesce hco hlt hRσ hfn hz hx
    have hnext := (evalInstrPMemF_next _ i s t hx).2
    refine ⟨t', hle _ _ _ _ ?_, coRel_congr hRt (hpost _ hnext), hfn', hfs, hz', hle'⟩
    show evalInstrPMemF _ _ s' = some t'
    rw [evalInstrPMemF_congr_labels (b2 := body.map (renArr (stepRen w ao s.prog.base.lpc i)))
      (fun l => by rw [findLabelMem_webRen, findLabelMem_map_renArr])]
    exact ht'
  · obtain ⟨wi, tag⟩ := i
    simp only at hi
    subst hi
    have hcB : callB (stepRen w ao s.prog.base.lpc (callShadow dst f srcs, tag)) L
        s.prog.base.lpc aa ao tag dst f srcs = true := by
      unfold coInstrB at hco
      simpa only [shadowCall?_callShadow] using hco
    obtain ⟨hst, hRt⟩ := callStep_coalesce (singletonProgM fn (webRen w ao body)) hcB hRσ
      hfwd hlen
    refine ⟨_, hst, ?_, ?_, LprogIsa.lfn_retRes dst x s, ?_, ?_⟩
    · rw [LprogIsa.lpc_retRes]
      exact coRel_congr hRt (hpost _ (by simp [callShadow, NextPc]))
    · rw [LprogIsa.lfn_retRes, LprogIsa.lfn_retRes]
      exact hfn
    · cases x <;> exact hz
    · rw [LprogIsa.lpc_retRes]
      exact hlt

/-! ## 4. The run -/

/-- **The renamed body at an instruction set with local calls.** For a body accepted by
    `webB w body L obs aa ao` and an instruction set `I` whose steps contain those of
    `x86Isa` and whose further steps are local calls at the array positions `aa` and the
    result lengths `ao`, a halting run of `I` on `body`, from a state `s` of the function
    `fn` at a position `k` at most `body.length`, is matched with the same fuel by a halting
    run of `I` on the renamed body `webRen w ao body` from every state `s'` that has the
    registers, word memory, flags and function name of `s` and whose arrays agree with those
    of `s` through `w k` on `L k`. The final states have equal registers, word memory and
    flags, and their arrays agree through `w body.length` on `obs`. -/
theorem lsemFuelMemF_webs {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
    {w : Nat → String → String} (hc : webB w body L obs aa ao = true) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, s.prog.lfn = fn → s.prog.base.lpc ≤ body.length →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn → s'.zf = s.zf →
      I.lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ t', I.lsemFuelMemF (singletonProgM fn (webRen w ao body)) fuel s' = some t'
        ∧ CoRel (w body.length) obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
  have hfetch : ∀ {s s' : LstateMF}, s.prog.lfn = fn →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn →
      findInstrMem (singletonProgM fn body) s.prog = body[s.prog.base.lpc]?
        ∧ findInstrMem (singletonProgM fn (webRen w ao body)) s'.prog
            = (body[s.prog.base.lpc]?).map
                (fun i => renArr (stepRen w ao s.prog.base.lpc i) i) := by
    intro s s' hf hR hfn
    refine ⟨findInstrMem_singleton fn body s.prog hf, ?_⟩
    rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR]
    simp only [webRen, List.getElem?_mapIdx]
  have hhalt : ∀ {s s' : LstateMF}, s.prog.base.lpc ≤ body.length →
      CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base →
      body[s.prog.base.lpc]? = none → CoRel (w body.length) obs s.prog.base s'.prog.base := by
    intro s s' hle hR hn
    have hlen : s.prog.base.lpc = body.length := by
      have := List.getElem?_eq_none_iff.mp hn
      omega
    rw [hlen] at hR
    exact hR.mono (webB_obs hc)
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hf hpc hR hfn hz h
      obtain ⟨e1, e2⟩ := hfetch hf hR hfn
      unfold Isa.lsemFuelMemF at h ⊢
      rw [e1] at h
      rw [e2]
      cases hb : body[s.prog.base.lpc]? with
      | none =>
          simp only [hb, Option.map_none, Option.some.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, hhalt hpc hR hb, hz⟩
      | some i => simp [hb] at h
  | succ n ih =>
      intro s s' t hf hpc hR hfn hz h
      obtain ⟨e1, e2⟩ := hfetch hf hR hfn
      unfold Isa.lsemFuelMemF at h ⊢
      rw [e1] at h
      rw [e2]
      cases hb : body[s.prog.base.lpc]? with
      | none =>
          simp only [hb, Option.map_none, Option.some.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, hhalt hpc hR hb, hz⟩
      | some i =>
          simp only [hb, Option.map_some] at h ⊢
          cases he : I.step (singletonProgM fn body) i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := step_webs hle hcl
                (webB_instr hc hb) (List.getElem?_eq_some_iff.mp hb).1 hR hfn hz he
              simp only [hu']
              exact ih (hfs.trans hf) hleu hRu hfu hzu h

/-- **The renamed body from its entry.** For a body accepted by `webB w body L obs aa ao`, a
    halting run of `I` on `body` from a state `s` of the function `fn` at position `0` is
    matched with the same fuel by a halting run of `I` on `webRen w ao body` from every state
    `s'` that has the registers, word memory, flags and function name of `s` and the arrays
    of `s` at the names of `L 0`. The final states have equal registers, word memory and
    flags, and equal arrays at the names of `obs`. -/
theorem lsemFuelMemF_webs_entry {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
    {w : Nat → String → String} (hc : webB w body L obs aa ao = true) (fuel : Nat)
    {s s' t : LstateMF} (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (hR : CoRel id (L 0) s.prog.base s'.prog.base) (hfn : s'.prog.lfn = s.prog.lfn)
    (hz : s'.zf = s.zf) (h : I.lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ t', I.lsemFuelMemF (singletonProgM fn (webRen w ao body)) fuel s' = some t'
      ∧ CoRel id obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
  have hR0 : CoRel (w s.prog.base.lpc) (L s.prog.base.lpc) s.prog.base s'.prog.base := by
    rw [hpc]
    exact coRel_congr hR (fun r hr => (webB_entry hc r hr).symm)
  obtain ⟨t', ht', hRt, hzt⟩ :=
    lsemFuelMemF_webs hle hcl hc fuel hf (by omega) hR0 hfn hz h
  exact ⟨t', ht', coRel_congr hRt (webB_exit hc), hzt⟩

/-! ## 5. The webs -/

/-- The state of the union-find over the occurrences of array names: the slot of each
    occurrence `(k, r)`, the parent and the rank of each slot. -/
structure WebSt where
  /-- The slot of each occurrence. -/
  slots : Std.HashMap (Nat × String) Nat := {}
  /-- The parent of each slot. -/
  parent : Array Nat := #[]
  /-- The rank of each slot. -/
  rank : Array Nat := #[]

/-- The slot of the occurrence `key`, added when absent. -/
def WebSt.slot (st : WebSt) (key : Nat × String) : WebSt × Nat :=
  match st.slots[key]? with
  | some n => (st, n)
  | none =>
      let n := st.parent.size
      ({ slots := st.slots.insert key n, parent := st.parent.push n,
         rank := st.rank.push 0 }, n)

/-- The root of the class of the slot `x`. -/
def WebSt.find (st : WebSt) (x : Nat) : Nat :=
  go st.parent.size x
where
  /-- The root reached from `x` in at most `n` parent steps. -/
  go : Nat → Nat → Nat
    | 0, x => x
    | n + 1, x =>
        let p := st.parent[x]?.getD x
        if p == x then x else go n p

/-- The union of the classes of the occurrences `a` and `b`, by rank. -/
def WebSt.union (st : WebSt) (a b : Nat × String) : WebSt :=
  let (st, x) := st.slot a
  let (st, y) := st.slot b
  let rx := st.find x
  let ry := st.find y
  if rx == ry then st
  else
    let kx := st.rank[rx]?.getD 0
    let ky := st.rank[ry]?.getD 0
    if kx < ky then { st with parent := st.parent.set! rx ry }
    else if ky < kx then { st with parent := st.parent.set! ry rx }
    else { st with parent := st.parent.set! ry rx, rank := st.rank.set! rx (kx + 1) }

/-- The unions of the instruction `i` at position `k`: the occurrence of each name live at a
    successor and not written by `i` is joined with its occurrence at `k`, and the occurrence
    after `k` of the name `i` writes is joined with its occurrence at `k` when the name is
    live at `k`. -/
def webStep (body : List LinstrRM) (L : Nat → List String) (ao : String → Option Nat)
    (st : WebSt) (k : Nat) (i : LinstrRM) : WebSt :=
  let st := (webSuccs body k i).foldl (fun st k' =>
    (L k').foldl (fun st r =>
      if wrArr ao i = some r then st else st.union (k, r) (k', r)) st) st
  match wrArr ao i with
  | some d => if (L k).contains d then st.union (k, d) (k + 1, d) else (st.slot (k + 1, d)).1
  | none => st

/-- **The position map of the webs** of `body`, for the result lengths `ao`, the liveness
    certificate `L` and the names `obs` read after the body. The occurrences of the names
    of `L` are joined by `webStep`. A class that contains the occurrence after a write and
    no occurrence of a name live at entry or read after the body is named
    `"a#" ++ toString root ++ "#" ++ r`, with `root` its root slot and `r` its array name;
    every other occurrence keeps its name. -/
def webMap (ao : String → Option Nat) (L : Nat → List String) (obs : List String)
    (body : List LinstrRM) : Nat → String → String :=
  let st0 : WebSt := (L 0).foldl (fun st r => (st.slot (0, r)).1) {}
  let st0 := obs.foldl (fun st r => (st.slot (body.length, r)).1) st0
  let st := body.zipIdx.foldl (fun st (i, k) => webStep body L ao st k i) st0
  let fixed : Std.HashSet Nat :=
    ((L 0).filterMap fun r => (st.slots[(0, r)]?).map st.find).foldl (·.insert ·)
      (((obs.filterMap fun r => (st.slots[(body.length, r)]?).map st.find)).foldl
        (·.insert ·) {})
  let defs : Std.HashSet Nat :=
    body.zipIdx.foldl (fun acc (i, k) =>
      match wrArr ao i with
      | some d => match st.slots[(k + 1, d)]? with
        | some n => acc.insert (st.find n)
        | none => acc
      | none => acc) {}
  fun k r =>
    match st.slots[(k, r)]? with
    | some n =>
        let root := st.find n
        if defs.contains root && !fixed.contains root then "a#" ++ toString root ++ "#" ++ r
        else r
    | none => r

/-- **The webs pass**: the body with its array positions renamed by the position map of its
    webs. -/
def arrWebs (ao : String → Option Nat) (L : Nat → List String) (obs : List String)
    (body : List LinstrRM) : List LinstrRM :=
  webRen (webMap ao L obs body) ao body

end CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs
