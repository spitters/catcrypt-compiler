/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute

@[expose] public section

set_option autoImplicit false

/-!
# Array versions coalesced in a body with labels and jumps

`ImageStraightRoute.coalesceB` decides when a renaming `σ` of array names may merge the
array versions of a straight chain. This module decides the same question for a typed
virtual body with labels and jumps, run by the flag machine `lsemFuelMemF`.

A name of the body names two cells, a register and an array. The renaming `renArr σ`
applies `σ` at the array positions of an instruction only: the base of a `LOADIDX`, the
destination and the base of a `STOREIDX`. A name that is an array at one instruction and a
register at another is renamed at the first and kept at the second.

The check is relative to a certificate `L : Nat → List String` giving, for each position
of the body, a list of array names containing those live before that position. The
certificate is not trusted: `coCfgB σ body L obs` checks that `L` is closed under the
backward liveness equations of the control-flow graph of `body`, that the names `obs` read
after the body are in `L body.length`, and that every instruction passes the coalescing
check of its kind against the names live after it.

## Main definitions

* `subB`: list inclusion as a Boolean.
* `jumpB`: the liveness condition of a jump to a label.
* `renArr`: the renaming of the array positions of an instruction.
* `coArrStepB`: the check of one operation against the names read after it.
* `coInstrB`: the check of the instruction at one position.
* `coCfgB`: the check of a body.

## Main results

* `lsemStepMem_coArr`: one step of an accepted operation is matched by a step of the
  operation with its array positions renamed.
* `evalInstrPMemF_coalesce`: one flag-machine step of an accepted instruction is matched by
  a step of the renamed instruction from a related state.
* `lsemFuelMemF_coalesce`: a halting run of an accepted body is matched, with the same
  fuel, by a halting run of the coalesced body `body.map (renArr σ)` from a related state,
  into a state related on `obs`.
* `renArr_callShadow`, `coInstrB_callShadow`, `step_coalesce_calls`,
  `lsemFuelMemF_coalesce_calls`: the same matching at an instruction set `I` with
  `x86Isa.StepLe I` whose further steps are local calls on words (`Isa.CallLocal`); the
  renaming keeps a shadow instruction of a call, and `lsemFuelMemF_coalesce` is the
  instance at `x86Isa`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (lsemStepCast)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagPrefix (CtlOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (lsemStepMem_of_carryArgs
  lsemStepMem_of_wideArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite CoRel)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retWord argsRead_none
  loadStruct?_callShadow storeStruct?_callShadow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-! ## 1. The check -/

/-- Every name of `A` is in `B`. -/
def subB (A B : List String) : Bool := A.all fun r => B.contains r

theorem subB_spec {A B : List String} (h : subB A B = true) : ∀ r ∈ A, r ∈ B := by
  intro r hr
  simpa using (List.all_eq_true.mp h) r hr

/-- The liveness condition of a jump from position `k` to the label `lbl`: when the label
    is at position `p` of `body`, the position `p + 1` after it is at most the length of
    the body, and the names live there are live at `k`. -/
def jumpB (body : List LinstrRM) (L : Nat → List String) (k : Nat) (lbl : LLabel) : Bool :=
  match findLabelMem lbl body with
  | some p => decide (p + 1 ≤ body.length) && subB (L (p + 1)) (L k)
  | none => true

/-- The wire of a `LOADIDX` with its base renamed by `σ`; every other wire unchanged. -/
def renLoad (σ : String → String) : LinstrR → LinstrR
  | .Lopn [.reg d] opn [.arrIdx b x sc] =>
      if opn = "LOADIDX" then .Lopn [.reg d] opn [.arrIdx (σ b) x sc]
      else .Lopn [.reg d] opn [.arrIdx b x sc]
  | i => i

/-- The wire of a `STOREIDX` with its destination and its base renamed by `σ`; every other
    wire unchanged. -/
def renStore (σ : String → String) : LinstrR → LinstrR
  | .Lopn [.reg d] opn [.arrIdx b x sc, .reg v] =>
      if opn = "STOREIDX" then .Lopn [.reg (σ d)] opn [.arrIdx (σ b) x sc, .reg v]
      else .Lopn [.reg d] opn [.arrIdx b x sc, .reg v]
  | i => i

/-- **The renaming of the array positions** of a typed instruction by `σ`: the base of a
    load-tagged `LOADIDX`, the destination and the base of a store-tagged `STOREIDX`. The
    index, the value, the destination of a load and every name of every other instruction
    are register positions and are kept. -/
def renArr (σ : String → String) (i : LinstrRM) : LinstrRM :=
  match i.2 with
  | .load _ _ => (renLoad σ i.1, i.2)
  | .store _ _ => (renStore σ i.1, i.2)
  | _ => i

/-- An instruction with an array position: a load-tagged `LOADIDX` or a store-tagged
    `STOREIDX`. -/
def arrShapeB (i : LinstrRM) : Bool :=
  match i.2 with
  | .load _ _ => (loadStruct? i.1).isSome
  | .store _ _ => (storeStruct? i.1).isSome
  | _ => false

/-- An operation that none of the recognisers of the flag machine reads: no compare, no
    register move, no carry-family operation, no flag-quiet lift instruction and no
    flag-writing arithmetic or logical operation. -/
def plainArrB (i : LinstrRM) : Bool :=
  isLopnB i && (cmpArgs? i).isNone && (movRegArgs? i).isNone && (carryArgs? i).isNone
    && (wideArgs? i).isNone && (aluFlagOp? i).isNone

/-- **The check of one operation** followed by reads of the array names `after`, for a
    renaming of array positions: the destination `d` of a store has an image under `σ` that
    no later-read name `r ≠ d` shares; never a compile-time-offset memory access. -/
def coArrStepB (σ : String → String) (i : LinstrRM) (after : List String) : Bool :=
  match i.2 with
  | .store _ _ => match storeStruct? i.1 with
    | some (d, _, _, _) => after.all fun r => r == d || σ r != σ d
    | none => true
  | .loadC | .storeC => false
  | _ => true

/-- **The check of the instruction `i` at position `k`**, by the arm of `evalInstrPMemF`
    that runs it. An instruction with an array position is read by no recogniser of the
    flag machine, before and after the renaming, passes `coArrStepB` against the names live
    after it, and the names it reads and the later-live names it does not write are live
    before it. For a compare, a register move, a carry-family operation and a flag-quiet
    lift instruction, the names live after them are live before them. A label and a
    conditional jump pass the names live at each successor. An unconditional jump passes
    the names live at its target. Every other operation passes `coArrStepB` against the
    names live after it, and the names it reads and the later-live names it does not write
    are live before it. Every other instruction is refused. -/
def coInstrB (σ : String → String) (body : List LinstrRM) (L : Nat → List String) (k : Nat)
    (i : LinstrRM) : Bool :=
  if arrShapeB i then
    plainArrB i && plainArrB (renArr σ i) && coArrStepB σ i (L (k + 1))
      && subB (arrReads i ++ (L (k + 1)).filter fun r => some r != arrWrite i) (L k)
  else if (cmpArgs? i).isSome || (movRegArgs? i).isSome then subB (L (k + 1)) (L k)
  else match flagCondCC? i with
  | some (_, lbl) => subB (L (k + 1)) (L k) && jumpB body L k lbl
  | none =>
    match i.1 with
    | .Llabel _ _ => subB (L (k + 1)) (L k)
    | .Lcond _ lbl => subB (L (k + 1)) (L k) && jumpB body L k lbl
    | .Lgoto (_, lbl) => jumpB body L k lbl
    | .Lopn _ _ _ =>
        if (carryArgs? i).isSome || (wideArgs? i).isSome then subB (L (k + 1)) (L k)
        else
          coArrStepB σ i (L (k + 1))
            && subB (arrReads i ++ (L (k + 1)).filter fun r => some r != arrWrite i) (L k)
    | _ => false

/-- **The coalescing check of a body** against the liveness certificate `L` and the names
    `obs` read after the body: `obs` is in `L body.length`, and the instruction at every
    position passes `coInstrB`. -/
def coCfgB (σ : String → String) (body : List LinstrRM) (L : Nat → List String)
    (obs : List String) : Bool :=
  subB obs (L body.length)
    && (List.range body.length).all fun k =>
      match body[k]? with
      | some i => coInstrB σ body L k i
      | none => true

theorem coCfgB_obs {σ : String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (h : coCfgB σ body L obs = true) : ∀ r ∈ obs, r ∈ L body.length := by
  unfold coCfgB at h
  exact subB_spec (Bool.and_eq_true_iff.mp h).1

theorem coCfgB_instr {σ : String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (h : coCfgB σ body L obs = true) {k : Nat} {i : LinstrRM}
    (hi : body[k]? = some i) : coInstrB σ body L k i = true := by
  unfold coCfgB at h
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hi).1
  have := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) k (List.mem_range.mpr hk)
  rw [hi] at this
  exact this

/-! ## 2. The relation under the register and flag updates -/

variable {σ : String → String} {A : List String}

-- The lemmas of this section about `CoRel` belong beside it in `ImageStraightRoute`.

theorem coRel_lpc {s s' : LstateM} (h : CoRel σ A s s') : s'.lpc = s.lpc := by
  simp [LstateM.lpc, h.reg]

theorem coRel_nextPc {s s' : LstateM} (h : CoRel σ A s s') : CoRel σ A s.nextPc s'.nextPc :=
  ⟨by simp [LstateM.nextPc, h.reg], h.mem, h.cf, h.of, h.arr⟩

theorem coRel_setLpc {s s' : LstateM} (h : CoRel σ A s s') (pc : Nat) :
    CoRel σ A (s.setLpc pc) (s'.setLpc pc) :=
  ⟨by simp [LstateM.setLpc, h.reg], h.mem, h.cf, h.of, h.arr⟩

theorem coRel_setReg {s s' : LstateM} (h : CoRel σ A s s') (d : String) {w : Nat}
    (v : BitVec w) : CoRel σ A (s.setReg d v) (s'.setReg d v) :=
  ⟨by simp [LstateM.setReg, h.reg], h.mem, h.cf, h.of, h.arr⟩

theorem coRel_aluFlags {b b' s0 s0' : LstateM} (h : CoRel σ A b b') (h0 : s0'.reg = s0.reg)
    (i : LinstrRM) : CoRel σ A (withALUFlags i s0 b) (withALUFlags i s0' b') := by
  unfold withALUFlags
  rw [h0]
  split
  · split
    · exact ⟨h.reg, h.mem, rfl, rfl, h.arr⟩
    · exact h
  · exact h

/-- A carry-family step from related states. -/
theorem carryStep_coalesce {s s' u : LstateM} (h : CoRel σ A s s') {op : CarryOp} {d : String}
    {a b : LOperand} (hu : carryStep op d a b s = some u) :
    ∃ u', carryStep op d a b s' = some u' ∧ CoRel σ A u u' := by
  unfold carryStep at hu ⊢
  rw [h.reg, h.cf, h.of]
  cases ha : evalOperandN s.reg 64 a with
  | none => simp [ha] at hu
  | some va =>
    cases hb : evalOperandN s.reg 64 b with
    | none => simp [ha, hb] at hu
    | some vb =>
      simp only [ha, hb] at hu ⊢
      cases op <;> (obtain rfl := Option.some.inj hu; refine ⟨_, rfl, ?_⟩) <;>
        exact ⟨by simp [LstateM.nextPc, LstateM.setReg, h.reg], h.mem, by first | rfl | exact h.cf,
          by first | rfl | exact h.of, h.arr⟩

/-- A flag-quiet lift step from related states. -/
theorem wideStep_coalesce {s s' u : LstateM} (h : CoRel σ A s s') {w : WideOp}
    (hu : wideStep w s = some u) : ∃ u', wideStep w s' = some u' ∧ CoRel σ A u u' := by
  unfold wideStep at hu ⊢
  cases w with
  | mov d b =>
      simp only [h.reg] at hu ⊢
      cases hb : evalOperandN s.reg 64 b with
      | none => simp [hb] at hu
      | some v =>
        simp only [hb, Option.some.injEq] at hu ⊢
        subst hu
        exact ⟨_, rfl, coRel_nextPc (coRel_setReg h d v)⟩
  | mulx lo hi b =>
      simp only [h.reg] at hu ⊢
      cases hx : evalOperandN s.reg 64 (.reg mulxSrc) with
      | none => simp [hx] at hu
      | some x =>
        cases hb : evalOperandN s.reg 64 b with
        | none => simp [hx, hb] at hu
        | some y =>
          simp only [hx, hb, Option.some.injEq] at hu ⊢
          subst hu
          exact ⟨_, rfl, coRel_nextPc (coRel_setReg (coRel_setReg h lo _) hi _)⟩

/-! ## 3. The renaming of array positions -/

theorem renLoad_of_none {w : LinstrR} (h : loadStruct? w = none) : renLoad σ w = w := by
  unfold renLoad
  split
  · split
    · next ho => simp [loadStruct?, ho] at h
    · rfl
  · rfl

theorem renStore_of_none {w : LinstrR} (h : storeStruct? w = none) : renStore σ w = w := by
  unfold renStore
  split
  · split
    · next ho => simp [storeStruct?, ho] at h
    · rfl
  · rfl

/-- The renamed wire of a `LOADIDX` reads the renamed base. -/
theorem loadStruct?_renLoad (w : LinstrR) :
    loadStruct? (renLoad σ w) = (loadStruct? w).map fun p => (p.1, σ p.2.1, p.2.2) := by
  unfold renLoad
  split
  · split <;> simp [loadStruct?, *]
  · next hne =>
    have : loadStruct? w = none := by
      unfold loadStruct?
      split
      · next d o b x sc => exact absurd rfl (hne d o b x sc)
      · rfl
    rw [this]
    rfl

/-- The renamed wire of a `STOREIDX` writes the renamed destination through the renamed
    base. -/
theorem storeStruct?_renStore (w : LinstrR) :
    storeStruct? (renStore σ w)
      = (storeStruct? w).map fun p => (σ p.1, σ p.2.1, p.2.2.1, p.2.2.2) := by
  unfold renStore
  split
  · split <;> simp [storeStruct?, *]
  · next hne =>
    have : storeStruct? w = none := by
      unfold storeStruct?
      split
      · next d o b x sc v => exact absurd rfl (hne d o b x sc v)
      · rfl
    rw [this]
    rfl

/-- An instruction with no array position is its own renaming. -/
theorem renArr_of_not_shape {i : LinstrRM} (h : arrShapeB i = false) : renArr σ i = i := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | load a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renLoad_of_none h]
  | store a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renStore_of_none h]
  | _ => rfl

theorem isLabel_renArr (l : LLabel) (i : LinstrRM) :
    JasminLsemLabeled.isLabel l (renArr σ i).1 = JasminLsemLabeled.isLabel l i.1 := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | load a n =>
      show JasminLsemLabeled.isLabel l (renLoad σ w) = _
      unfold renLoad
      split
      · split <;> rfl
      · rfl
  | store a n =>
      show JasminLsemLabeled.isLabel l (renStore σ w) = _
      unfold renStore
      split
      · split <;> rfl
      · rfl
  | _ => rfl

/-- The renaming of array positions leaves every label position unchanged. -/
theorem findLabelMem_map_renArr (l : LLabel) (body : List LinstrRM) :
    findLabelMem l (body.map (renArr σ)) = findLabelMem l body := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.map_map, List.findIdx?_map, List.findIdx?_map]
  congr 1
  funext i
  exact isLabel_renArr l i

/-- The renaming of array positions keeps the instruction kinds of `CtlOK`. -/
theorem ctlOK_renArr (σ : String → String) {i : LinstrRM} (h : CtlOK i) :
    CtlOK (renArr σ i) := by
  obtain ⟨w, tag⟩ := i
  have hL : ∀ w : LinstrR, (∃ d o s, w = LinstrR.Lopn d o s) → ∃ d o s,
      renLoad σ w = LinstrR.Lopn d o s := by
    rintro w ⟨d, o, s, rfl⟩
    unfold renLoad
    split
    · split <;> exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
  have hS : ∀ w : LinstrR, (∃ d o s, w = LinstrR.Lopn d o s) → ∃ d o s,
      renStore σ w = LinstrR.Lopn d o s := by
    rintro w ⟨d, o, s, rfl⟩
    unfold renStore
    split
    · split <;> exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
  rcases h with ⟨d, o, s, hd⟩ | ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
  · simp only at hd
    cases tag with
    | load a n => exact Or.inl (hL w ⟨d, o, s, hd⟩)
    | store a n => exact Or.inl (hS w ⟨d, o, s, hd⟩)
    | _ => exact Or.inl ⟨d, o, s, hd⟩
  · simp only at hw
    subst hw
    cases tag <;> exact Or.inr (Or.inl ⟨kd, l, rfl⟩)
  · simp only at hw
    subst hw
    cases tag <;> exact Or.inr (Or.inr (Or.inl ⟨c, l, rfl, hcc⟩))
  · simp only at hw
    subst hw
    cases tag <;> exact Or.inr (Or.inr (Or.inr ⟨tgt, rfl⟩))

/-- **One step of an operation with its array positions renamed.** For an operation
    accepted by `coArrStepB` with the later reads `after`, a step from `s` is matched by a
    step of `renArr σ i` from a state related on the reads of the operation and the names
    of `after` it does not write, into a state related on `after`. -/
theorem lsemStepMem_coArr {i : LinstrRM} {after : List String}
    (hc : coArrStepB σ i after = true) {s s' t : LstateM}
    (hR : CoRel σ (arrReads i ++ after.filter fun r => some r != arrWrite i) s s')
    (h : lsemStepMem i s = some t) :
    ∃ t', lsemStepMem (renArr σ i) s' = some t' ∧ CoRel σ after t t' := by
  obtain ⟨wire, tag⟩ := i
  have hnone : arrWrite (wire, tag) = none → CoRel σ after s s' := fun hw =>
    hR.mono fun r hr => List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by rw [hw]; simp⟩)
  have hcast : arrWrite (wire, tag) = none → ∀ (cd : Option Nat),
      (lsemStepCast (wire, cd) s.reg).map (fun r => { s with reg := r }) = some t →
      ∃ t', (lsemStepCast (wire, cd) s'.reg).map
          (fun r => { s' with reg := r }) = some t' ∧ CoRel σ after t t' := by
    intro hw cd h
    have hA := hnone hw
    rw [hR.reg]
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨{ s' with reg := r }, by rw [hr]; rfl, ⟨rfl, hA.mem, hA.cf, hA.of, hA.arr⟩⟩
  cases tag with
  | reg cd => exact hcast rfl cd h
  | load w n =>
      unfold lsemStepMem at h ⊢
      simp only [renArr] at h ⊢
      rw [loadStruct?_renLoad]
      cases hl : loadStruct? wire with
      | none =>
          rw [hl] at h
          rw [renLoad_of_none hl]
          exact hcast rfl none h
      | some p =>
          obtain ⟨d, b, x⟩ := p
          rw [hl] at h
          have hA := hnone rfl
          have hb : b ∈ arrReads (wire, .load w n)
              ++ after.filter fun r => some r != arrWrite (wire, .load w n) := by
            simp [arrReads, hl]
          simp only [Option.map_some, hR.getArr hb, hR.reg] at h ⊢
          cases ha : s.getArr b w n with
          | none => simp [ha] at h
          | some arr =>
            cases hi : s.reg.getW x 64 with
            | none => simp [ha, hi] at h
            | some vi =>
              simp only [ha, hi, Option.some.injEq] at h
              subst h
              refine ⟨_, rfl, ⟨?_, hA.mem, hA.cf, hA.of, hA.arr⟩⟩
              simp only [LstateM.nextPc, LstateM.setReg, hR.reg]
  | store w n =>
      simp only [coArrStepB] at hc
      unfold lsemStepMem at h ⊢
      simp only [renArr] at h ⊢
      rw [storeStruct?_renStore]
      cases hl : storeStruct? wire with
      | none =>
          rw [hl] at h
          rw [renStore_of_none hl]
          exact hcast (by simp [arrWrite, hl]) none h
      | some p =>
          obtain ⟨d, b, x, v⟩ := p
          rw [hl] at hc h
          simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
          have hb : b ∈ arrReads (wire, .store w n)
              ++ after.filter fun r => some r != arrWrite (wire, .store w n) := by
            simp [arrReads, hl]
          simp only [Option.map_some, hR.getArr hb, hR.reg] at h ⊢
          cases ha : s.getArr b w n with
          | none => simp [ha] at h
          | some arr =>
            cases hi : s.reg.getW x 64 with
            | none => simp [ha, hi] at h
            | some vi =>
              cases hvv : s.reg.getW v w with
              | none => simp [ha, hi, hvv] at h
              | some vv =>
                simp only [ha, hi, hvv, Option.some.injEq] at h
                subst h
                refine ⟨_, rfl, ⟨?_, hR.mem, hR.cf, hR.of, fun r hr => ?_⟩⟩
                · simp only [LstateM.nextPc, LstateM.setArr, hR.reg]
                · simp only [LstateM.nextPc, LstateM.setArr]
                  by_cases hrd : r = d
                  · subst hrd
                    simp
                  · have hne : σ r ≠ σ d := by
                      rcases hc r hr with h' | h'
                      · exact absurd h' hrd
                      · exact h'
                    simp only [hne, hrd, if_false]
                    exact hR.arr r (List.mem_append_right _
                      (List.mem_filter.mpr ⟨hr, by simp [arrWrite, hl, hrd]⟩))
  | loadC => simp [coArrStepB] at hc
  | storeC => simp [coArrStepB] at hc

/-! ## 4. The step -/

/-- A jump from related states: the target position is in the body, and the states after
    the jump are related on the names live at the target. -/
theorem evalJumpMem_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {k : Nat} {lbl : LLabel} (hj : jumpB body L k lbl = true) {p p' q : LstatePM}
    (hR : CoRel σ (L k) p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem (singletonProgM fn body) lbl p = some q) :
    ∃ q', evalJumpMem (singletonProgM fn (body.map (renArr σ))) lbl p' = some q'
      ∧ CoRel σ (L q.base.lpc) q.base q'.base ∧ q'.lfn = q.lfn ∧ q.lfn = p.lfn
      ∧ q.base.lpc ≤ body.length := by
  unfold evalJumpMem at h ⊢
  simp only [singletonProgM] at h ⊢
  rw [findLabelMem_map_renArr]
  unfold jumpB at hj
  cases hl : findLabelMem lbl body with
  | none => simp [hl] at h
  | some pc =>
    simp only [hl, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at hj h ⊢
    subst h
    exact ⟨_, rfl, coRel_setLpc (hR.mono (subB_spec hj.2)) _, hfn, rfl, hj.1⟩

theorem flagCondCC?_of_isLopn {j : LinstrRM} (h : IsLopn j) : flagCondCC? j = none := by
  obtain ⟨w, tag⟩ := j
  obtain ⟨d, o, s, e⟩ := h
  simp only at e
  subst e
  rfl

/-- **One step of a coalesced instruction at the flag machine.** For an instruction `i`
    accepted by `coInstrB` at position `k < body.length`, a step from a state `s` at
    position `k` is matched by a step of `renArr σ i` in the coalesced body from a state
    related to `s` on `L k` with the same function name and zero flag. The two successor
    states are related on the names `L` gives the successor position, which is at most
    `body.length`; the function name is kept, and the zero flags are equal. -/
theorem evalInstrPMemF_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {i : LinstrRM} {s s' t : LstateMF}
    (hc : coInstrB σ body L s.prog.base.lpc i = true) (hlt : s.prog.base.lpc < body.length)
    (hR : CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base)
    (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (h : evalInstrPMemF (singletonProgM fn body) i s = some t) :
    ∃ t', evalInstrPMemF (singletonProgM fn (body.map (renArr σ))) (renArr σ i) s' = some t'
      ∧ CoRel σ (L t.prog.base.lpc) t.prog.base t'.prog.base
      ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc ≤ body.length := by
  obtain ⟨w, tag⟩ := i
  unfold coInstrB at hc
  by_cases hsh : arrShapeB (w, tag) = true
  · simp only [hsh, if_true, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hp, hp'⟩, hstep⟩, hsub⟩ := hc
    simp only [plainArrB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp hp'
    obtain ⟨⟨⟨⟨⟨hl, h1⟩, h2⟩, hk⟩, hw⟩, ha⟩ := hp
    obtain ⟨⟨⟨⟨⟨hl', h1'⟩, h2'⟩, hk'⟩, hw'⟩, ha'⟩ := hp'
    have hI := isLopnB_isLopn hl
    have hI' := isLopnB_isLopn hl'
    unfold evalInstrPMemF at h ⊢
    simp only [h1, h2, flagCondCC?_of_isLopn hI, h1', h2', flagCondCC?_of_isLopn hI'] at h ⊢
    rw [evalInstrPMemL_lopn _ _ _ hI] at h
    rw [evalInstrPMemL_lopn _ _ _ hI']
    cases hb : lsemStepMem (w, tag) s.prog.base with
    | none => simp [hb, hk, hw] at h
    | some b =>
      simp only [hb, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨b', hb', hRb⟩ := lsemStepMem_coArr hstep (hR.mono (subB_spec hsub)) hb
      have hl1 := JasminLsemMemLoop.lsemStepMem_lpc_succ _ _ _ hb
      simp only [hb', Option.map_some]
      refine ⟨_, rfl, ?_, hfn, trivial, hz, ?_⟩
      · show CoRel σ (L (withALUFlags (w, tag) s.prog.base b).lpc)
          (withALUFlags (w, tag) s.prog.base b)
          (withALUFlags (renArr σ (w, tag)) s'.prog.base b')
        rw [withALUFlags_lpc, withALUFlags_of_none ha, withALUFlags_of_none ha', hl1]
        exact hRb
      · show (withALUFlags (w, tag) s.prog.base b).lpc ≤ body.length
        rw [withALUFlags_lpc, hl1]
        omega
  have hsh' : arrShapeB (w, tag) = false := by simpa using hsh
  rw [renArr_of_not_shape hsh']
  simp only [hsh', Bool.false_eq_true, if_false] at hc
  cases h1 : cmpArgs? (w, tag) with
  | some p =>
      obtain ⟨a, b⟩ := p
      simp only [h1, Option.isSome_some, Bool.true_or, if_true] at hc
      unfold evalInstrPMemF at h ⊢
      simp only [h1, hR.reg] at h ⊢
      cases ha : evalOperandN s.prog.base.reg 64 a with
      | none => simp [ha] at h
      | some va =>
        cases hb : evalOperandN s.prog.base.reg 64 b with
        | none => simp [ha, hb] at h
        | some vb =>
          simp only [ha, hb, Option.some.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, coRel_nextPc (hR.mono (subB_spec hc)), hfn, rfl, rfl, hlt⟩
  | none =>
  cases h2 : movRegArgs? (w, tag) with
  | some p =>
      obtain ⟨d, r⟩ := p
      simp only [h2, Option.isSome_some, Bool.or_true, if_true] at hc
      unfold evalInstrPMemF at h ⊢
      simp only [h1, h2, hR.reg] at h ⊢
      cases hr : readReg s.prog.base.reg (.reg r) with
      | none => simp [hr] at h
      | some v =>
        obtain ⟨wv, v⟩ := v
        simp only [hr, Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, coRel_nextPc (coRel_setReg (hR.mono (subB_spec hc)) d v), hfn, rfl, hz,
          hlt⟩
  | none =>
  simp only [h1, h2, Option.isSome_none, Bool.or_false, Bool.false_eq_true, if_false] at hc
  cases h3 : flagCondCC? (w, tag) with
  | some p =>
      obtain ⟨pol, lbl⟩ := p
      simp only [h3, Bool.and_eq_true] at hc
      unfold evalInstrPMemF at h ⊢
      simp only [h1, h2, h3, hz] at h ⊢
      by_cases hp : s.zf = pol
      · rw [if_pos hp] at h ⊢
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨q', hq', hRq, hfq, hfs, hle⟩ := evalJumpMem_coalesce hc.2 hR hfn hq
        exact ⟨{ prog := q', zf := s.zf }, by rw [hq']; rfl, hRq, hfq, hfs, rfl, hle⟩
      · rw [if_neg hp] at h ⊢
        cases h
        exact ⟨_, rfl, coRel_nextPc (hR.mono (subB_spec hc.1)), hfn, rfl, rfl, hlt⟩
  | none =>
  simp only [h3] at hc
  have key : carryArgs? (w, tag) = none → wideArgs? (w, tag) = none →
      (∀ q, evalInstrPMemL (singletonProgM fn body) (w, tag) s.prog = some q →
        ∃ q', evalInstrPMemL (singletonProgM fn (body.map (renArr σ))) (w, tag)
            s'.prog = some q'
          ∧ CoRel σ (L q.base.lpc) q.base q'.base ∧ q'.lfn = q.lfn ∧ q.lfn = s.prog.lfn
          ∧ q.base.lpc ≤ body.length) →
      ∃ t', evalInstrPMemF (singletonProgM fn (body.map (renArr σ))) (w, tag) s'
          = some t'
        ∧ CoRel σ (L t.prog.base.lpc) t.prog.base t'.prog.base
        ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
        ∧ t.prog.base.lpc ≤ body.length := by
    intro hk hw hL
    unfold evalInstrPMemF at h ⊢
    simp only [h1, h2, h3] at h ⊢
    cases hq : evalInstrPMemL (singletonProgM fn body) (w, tag) s.prog with
    | none => simp [hq, hk, hw] at h
    | some q =>
      simp only [hq, Option.some.injEq] at h
      subst h
      obtain ⟨q', hq', hRq, hfq, hfs, hle⟩ := hL q hq
      simp only [hq']
      refine ⟨_, rfl, ?_, hfq, hfs, hz, ?_⟩
      · show CoRel σ (L (withALUFlags (w, tag) s.prog.base q.base).lpc)
          (withALUFlags (w, tag) s.prog.base q.base)
          (withALUFlags (w, tag) s'.prog.base q'.base)
        rw [withALUFlags_lpc]
        exact coRel_aluFlags hRq hR.reg _
      · show (withALUFlags (w, tag) s.prog.base q.base).lpc ≤ body.length
        rw [withALUFlags_lpc]
        exact hle
  cases w with
  | Llabel a l =>
      refine key rfl rfl fun q hq => ?_
      simp only [evalInstrPMemL, Option.some.injEq] at hq
      subst hq
      exact ⟨_, rfl, coRel_nextPc (hR.mono (subB_spec hc)), hfn, rfl, hlt⟩
  | Lcond c lbl =>
      simp only [Bool.and_eq_true] at hc
      refine key rfl rfl fun q hq => ?_
      have hcz : condNZ s'.prog.base c = condNZ s.prog.base c := by
        unfold condNZ
        rw [hR.reg]
      show ∃ q', evalInstrPMemL _ (LinstrR.Lcond c lbl, tag) s'.prog = some q' ∧ _
      simp only [evalInstrPMemL, hcz] at hq ⊢
      split at hq
      · rw [if_pos (by assumption)]
        exact evalJumpMem_coalesce hc.2 hR hfn hq
      · rw [if_neg (by assumption)]
        cases hq
        exact ⟨_, rfl, coRel_nextPc (hR.mono (subB_spec hc.1)), hfn, rfl, hlt⟩
  | Lgoto tgt =>
      obtain ⟨f, lbl⟩ := tgt
      refine key rfl rfl fun q hq => ?_
      show ∃ q', evalInstrPMemL _ (LinstrR.Lgoto (f, lbl), tag) s'.prog = some q' ∧ _
      by_cases hff : f = fn
      · subst hff
        simp only [evalInstrPMemL, singletonProgM, ↓reduceIte] at hq ⊢
        exact evalJumpMem_coalesce hc hR hfn hq
      · simp [evalInstrPMemL, singletonProgM, hff] at hq
  | Lopn d o src =>
      by_cases hcw : ((carryArgs? (LinstrR.Lopn d o src, tag)).isSome
          || (wideArgs? (LinstrR.Lopn d o src, tag)).isSome) = true
      · simp only [hcw, if_true] at hc
        have hRn := hR.mono (subB_spec hc)
        unfold evalInstrPMemF at h ⊢
        simp only [h1, h2, h3] at h ⊢
        have hI : IsLopn (LinstrR.Lopn d o src, tag) := ⟨_, _, _, rfl⟩
        rw [evalInstrPMemL_lopn _ _ _ hI] at h ⊢
        cases hk : carryArgs? (LinstrR.Lopn d o src, tag) with
        | some p =>
            obtain ⟨op, dd, a, b⟩ := p
            simp only [lsemStepMem_of_carryArgs hk, Option.map_none, hk] at h ⊢
            obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨u', hu', hRu⟩ := carryStep_coalesce hRn hu
            have hl := carryStep_lpc _ _ _ _ _ _ hu
            refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
              by rw [hu']; rfl, ?_, hfn, rfl, hz, ?_⟩
            · show CoRel σ (L u.lpc) u u'
              rw [hl]
              exact hRu
            · show u.lpc ≤ body.length
              omega
        | none =>
            cases hw : wideArgs? (LinstrR.Lopn d o src, tag) with
            | none => simp [hk, hw] at hcw
            | some wo =>
                simp only [lsemStepMem_of_wideArgs hw, Option.map_none, hk, hw] at h ⊢
                obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
                obtain ⟨u', hu', hRu⟩ := wideStep_coalesce hRn hu
                have hl := wideStep_lpc _ _ _ hu
                refine ⟨{ prog := { base := u', lfn := s'.prog.lfn }, zf := s'.zf },
                  by rw [hu']; rfl, ?_, hfn, rfl, hz, ?_⟩
                · show CoRel σ (L u.lpc) u u'
                  rw [hl]
                  exact hRu
                · show u.lpc ≤ body.length
                  omega
      · simp only [hcw, Bool.false_eq_true, if_false, Bool.and_eq_true] at hc
        obtain ⟨hstep, hsub⟩ := hc
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isSome_eq_false_iff,
          Option.isNone_iff_eq_none] at hcw
        refine key hcw.1 hcw.2 fun q hq => ?_
        rw [evalInstrPMemL_lopn _ _ _ ⟨d, o, src, rfl⟩]
        rw [evalInstrPMemL_lopn _ _ _ ⟨d, o, src, rfl⟩] at hq
        obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hq
        obtain ⟨b', hb', hRb⟩ := lsemStepMem_coArr hstep (hR.mono (subB_spec hsub)) hb
        rw [renArr_of_not_shape hsh'] at hb'
        have hl := JasminLsemMemLoop.lsemStepMem_lpc_succ _ _ _ hb
        refine ⟨⟨b', s'.prog.lfn⟩, by rw [hb']; rfl, ?_, hfn, rfl, ?_⟩
        · show CoRel σ (L b.lpc) b b'
          rw [hl]
          exact hRb
        · show b.lpc ≤ body.length
          omega
  | Lsyscall _ => simp at hc
  | Lcall _ _ => simp at hc
  | Lret => simp at hc
  | Lalign => simp at hc
  | Ligoto _ => simp at hc
  | LstoreLabel _ _ => simp at hc

/-! ## 5. The step of a call shadow -/

/-- The renaming of array positions keeps a shadow instruction of a call. -/
theorem renArr_callShadow (dst f : String) (srcs : List LOperand) (tag : MemTag) :
    renArr σ (callShadow dst f srcs, tag) = (callShadow dst f srcs, tag) := by
  unfold renArr
  cases tag <;> simp only [renLoad_of_none (loadStruct?_callShadow dst f srcs),
    renStore_of_none (storeStruct?_callShadow dst f srcs)]

/-- A shadow instruction of a call accepted by `coInstrB` at `k` keeps every array name live
    after it live before it. -/
theorem coInstrB_callShadow {body : List LinstrRM} {L : Nat → List String} {k : Nat}
    {dst f : String} {srcs : List LOperand} {tag : MemTag}
    (hc : coInstrB σ body L k (callShadow dst f srcs, tag) = true) :
    ∀ r ∈ L (k + 1), r ∈ L k := by
  have hw : arrWrite (callShadow dst f srcs, tag) = none := by
    cases tag <;> simp [arrWrite, storeStruct?_callShadow]
  unfold callShadow at hc hw
  have hfil : ∀ r ∈ L (k + 1), r ∈ arrReads (LinstrR.Lopn [.reg dst] ("CALL:" ++ f) srcs, tag)
      ++ (L (k + 1)).filter fun r =>
        some r != arrWrite (LinstrR.Lopn [.reg dst] ("CALL:" ++ f) srcs, tag) :=
    fun r hr => List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by rw [hw]; simp⟩)
  unfold coInstrB at hc
  split at hc
  · simp only [Bool.and_eq_true] at hc
    exact fun r hr => subB_spec hc.2 r (hfil r hr)
  split at hc
  · exact subB_spec hc
  split at hc
  · simp only [Bool.and_eq_true] at hc
    exact subB_spec hc.1
  dsimp only at hc
  split at hc
  · exact subB_spec hc
  · simp only [Bool.and_eq_true] at hc
    exact fun r hr => subB_spec hc.2 r (hfil r hr)

/-- **One step of a coalesced instruction at an instruction set with local calls.** The
    statement of `evalInstrPMemF_coalesce` for the step of an instruction set `I` whose steps
    contain those of `x86Isa` and whose further steps are local calls on words. -/
theorem step_coalesce_calls {I : Isa} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa (fun _ _ => none)) {fn : String} {body : List LinstrRM}
    {L : Nat → List String} {i : LinstrRM} {s s' t : LstateMF}
    (hc : coInstrB σ body L s.prog.base.lpc i = true) (hlt : s.prog.base.lpc < body.length)
    (hR : CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base)
    (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (h : I.step (singletonProgM fn body) i s = some t) :
    ∃ t', I.step (singletonProgM fn (body.map (renArr σ))) (renArr σ i) s' = some t'
      ∧ CoRel σ (L t.prog.base.lpc) t.prog.base t'.prog.base
      ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc ≤ body.length := by
  rcases hcl _ i s t h with hx | ⟨dst, f, srcs, r, hi, rfl, hfwd⟩
  · obtain ⟨t', ht', hrest⟩ := evalInstrPMemF_coalesce hc hlt hR hfn hz hx
    exact ⟨t', hle _ _ _ _ ht', hrest⟩
  · obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    rw [renArr_callShadow]
    have hpc : (retWord dst r s).prog.base.lpc = s.prog.base.lpc + 1 := by
      simp [retWord, LstateM.nextPc, LstateM.setReg, LstateM.lpc, LstateN.nextPc,
        LstateN.setReg]
    refine ⟨retWord dst r s', hfwd _ tag dst srcs s' rfl ?_, ?_, hfn, rfl, hz, ?_⟩
    · rw [argsRead_none, argsRead_none, hR.reg]
    · rw [hpc]
      exact coRel_nextPc (coRel_setReg (hR.mono (coInstrB_callShadow hc)) dst r)
    · rw [hpc]
      exact hlt

/-! ## 6. The run -/

/-- **The coalesced body at an instruction set with local calls.** For a body accepted by
    `coCfgB σ body L obs` and an instruction set `I` whose steps contain those of `x86Isa` and
    whose further steps are local calls on words, a halting run of `I` on `body`, from a state
    `s` of the function `fn` at a position at most `body.length`, is matched with the same
    fuel by a halting run of `I` on the coalesced body `body.map (renArr σ)` from every state
    `s'` that has the registers, word memory, flags and function name of `s` and whose arrays
    agree with those of `s` through `σ` on the names `L` gives the position of `s`. The final
    states have equal registers, word memory and flags, and their arrays agree through `σ` on
    `obs`. -/
theorem lsemFuelMemF_coalesce_calls {I : Isa} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa (fun _ _ => none)) {fn : String} {body : List LinstrRM}
    {L : Nat → List String} {obs : List String} (hc : coCfgB σ body L obs = true) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, s.prog.lfn = fn → s.prog.base.lpc ≤ body.length →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      s'.zf = s.zf → I.lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ t', I.lsemFuelMemF (singletonProgM fn (body.map (renArr σ))) fuel s' = some t'
        ∧ CoRel σ obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
  have hfetch : ∀ {s s' : LstateMF}, s.prog.lfn = fn →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      findInstrMem (singletonProgM fn body) s.prog = body[s.prog.base.lpc]?
        ∧ findInstrMem (singletonProgM fn (body.map (renArr σ))) s'.prog
            = (body[s.prog.base.lpc]?).map (renArr σ) := by
    intro s s' hf hR hfn
    exact ⟨findInstrMem_singleton fn body s.prog hf, by
      rw [findInstrMem_singleton fn _ s'.prog (hfn.trans hf), coRel_lpc hR, List.getElem?_map]⟩
  have hhalt : ∀ {s s' : LstateMF}, s.prog.base.lpc ≤ body.length →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → body[s.prog.base.lpc]? = none →
      CoRel σ obs s.prog.base s'.prog.base := by
    intro s s' hle hR hn
    have hlen : s.prog.base.lpc = body.length := by
      have := List.getElem?_eq_none_iff.mp hn
      omega
    rw [hlen] at hR
    exact hR.mono (coCfgB_obs hc)
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
              obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := step_coalesce_calls hle hcl
                (coCfgB_instr hc hb) (List.getElem?_eq_some_iff.mp hb).1 hR hfn hz he
              simp only [hu']
              exact ih (hfs.trans hf) hleu hRu hfu hzu h

/-- **The coalesced body.** For a body accepted by `coCfgB σ body L obs`, a halting run of
    the flag machine on `body`, from a state `s` of the function `fn` at a position at most
    `body.length`, is matched with the same fuel by a halting run on the coalesced body
    `body.map (renArr σ)` from every state `s'` that has the registers, word memory, flags
    and function name of `s` and whose arrays agree with those of `s` through `σ` on the
    names `L` gives the position of `s`. The final states have equal registers, word memory
    and flags, and their arrays agree through `σ` on `obs`. -/
theorem lsemFuelMemF_coalesce {fn : String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hc : coCfgB σ body L obs = true) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, s.prog.lfn = fn → s.prog.base.lpc ≤ body.length →
      CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      s'.zf = s.zf → lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ t', lsemFuelMemF (singletonProgM fn (body.map (renArr σ))) fuel s' = some t'
        ∧ CoRel σ obs t.prog.base t'.prog.base ∧ t'.zf = t.zf := by
  rw [← x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_coalesce_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) hc

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
