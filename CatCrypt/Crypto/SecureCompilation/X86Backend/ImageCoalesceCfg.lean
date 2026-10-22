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

At a shadow instruction of a call, `renArr σ` renames the destination and every register
operand; the check of the call requires `σ` to fix the word operands and a word
destination, so that the renaming moves the array operands and an array destination only.

The check is relative to a certificate `L : Nat → List String` giving, for each position
of the body, a list of array names containing those live before that position. The
certificate is not trusted: `coCfgB σ body L obs` checks that `L` is closed under the
backward liveness equations of the control-flow graph of `body`, that the names `obs` read
after the body are in `L body.length`, and that every instruction passes the coalescing
check of its kind against the names live after it.

## Main definitions

* `subB`: list inclusion as a Boolean.
* `jumpB`: the liveness condition of a jump to a label.
* `renOpR`, `renCallW`, `renArr`: the renaming of the array positions of an instruction,
  and of the destination and the register operands of a shadow instruction of a call.
* `coArrStepB`: the check of one operation against the names read after it.
* `callOpsB`, `callTagB`, `callB`: the check of a shadow instruction of a call, for the
  array positions and the result length of its symbol.
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
* `renArr_callShadow`, `argsRead_renOpR`, `callStep_coalesce`, `step_coalesce_calls`,
  `lsemFuelMemF_coalesce_calls`: the same matching at an instruction set `I` with
  `x86Isa.StepLe I` whose further steps are local calls (`Isa.CallLocal`) at the array
  positions `aa` and the result lengths `ao` the check is given; a call with a word result
  writes the same register, a call with an array result writes the renamed destination,
  and `lsemFuelMemF_coalesce` is the instance at `x86Isa`.
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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retWord retArr retRes
  CallRes argRead argsRead argsRead_none loadStruct?_callShadow storeStruct?_callShadow
  shadowCall? shadowCall?_callShadow eq_callShadow_of_shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
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

/-- The operand `o` with the base of an array element renamed by `σ`; the index register
    and every other operand unchanged. -/
def renOpA (σ : String → String) : LOperand → LOperand
  | .arr b k => .arr (σ b) k
  | .arrIdx b x sc => .arrIdx (σ b) x sc
  | o => o

/-- The wire of a `ZEROARR` with its destination and the array bases of its sources
    renamed by `σ`; every other wire unchanged. -/
def renZero (σ : String → String) : LinstrR → LinstrR
  | .Lopn [.reg d] opn ss =>
      if opn = "ZEROARR" then .Lopn [.reg (σ d)] opn (ss.map (renOpA σ))
      else .Lopn [.reg d] opn ss
  | i => i

/-- The wire of a `STOREIMM` with its destination and its array source renamed by `σ`; the
    value register, the index and every other wire unchanged. -/
def renStoreImm (σ : String → String) : LinstrR → LinstrR
  | .Lopn [.reg d] opn [.reg b, .reg v, .imm k] =>
      if opn = "STOREIMM" then .Lopn [.reg (σ d)] opn [.reg (σ b), .reg v, .imm k]
      else .Lopn [.reg d] opn [.reg b, .reg v, .imm k]
  | i => i

/-- The operand `o` with the name of a register operand renamed by `σ`. -/
def renOpR (σ : String → String) : LOperand → LOperand
  | .reg x => .reg (σ x)
  | o => o

/-- The wire of a shadow instruction of a call with its destination and the names of its
    register operands renamed by `σ`; every other wire unchanged. -/
def renCallW (σ : String → String) (w : LinstrR) : LinstrR :=
  match shadowCall? w with
  | some (dst, f, srcs) => callShadow (σ dst) f (srcs.map (renOpR σ))
  | none => w

/-- **The renaming of the array positions** of a typed instruction by `σ`: the base of a
    load-tagged `LOADIDX`, the destination and the base of a store-tagged `STOREIDX`, and
    the destination and the register operands of a shadow instruction of a call with any
    other tag. The index, the value, the destination of a load and every name of every
    other instruction are register positions and are kept. The check of a call (`callB`)
    admits it only when `σ` fixes its word operands and a word destination, so that the
    renaming of a call moves its array operands and an array destination only. -/
def renArr (σ : String → String) (i : LinstrRM) : LinstrRM :=
  match i.2 with
  | .load _ _ => (renLoad σ i.1, i.2)
  | .store _ _ => (renStore σ i.1, i.2)
  | .zero _ _ => (renZero σ i.1, i.2)
  | .storeImm _ _ => (renStoreImm σ i.1, i.2)
  | _ => (renCallW σ i.1, i.2)

/-- An instruction with an array position: a load-tagged `LOADIDX`, a store-tagged
    `STOREIDX`, a zero-tagged `ZEROARR` or a constant-index `STOREIMM`. -/
def arrShapeB (i : LinstrRM) : Bool :=
  match i.2 with
  | .load _ _ => (loadStruct? i.1).isSome
  | .store _ _ => (storeStruct? i.1).isSome
  | .zero _ _ => (zeroStruct? i.1).isSome
  | .storeImm _ _ => (storeImmStruct? i.1).isSome
  | _ => false

/-- An instruction without an array position writes no array. -/
theorem arrWrite_of_arrShapeB {i : LinstrRM} (h : arrShapeB i = false) :
    arrWrite i = none := by
  rcases i with ⟨w, t⟩
  cases t <;> simp_all [arrShapeB, arrWrite]

/-- An operation that none of the recognisers of the flag machine reads: no compare, no
    register move, no carry-family operation, no flag-quiet lift instruction and no
    flag-writing arithmetic or logical operation. -/
def plainArrB (i : LinstrRM) : Bool :=
  isLopnB i && (cmpArgs? i).isNone && (movRegArgs? i).isNone && (carryArgs? i).isNone
    && (wideArgs? i).isNone && (aluFlagOp? i).isNone

/-- An array zeroing is read by no recogniser of the flag machine. -/
theorem plainArrB_zero (d : String) (ss : List LOperand) (tag : MemTag) :
    plainArrB (.Lopn [.reg d] "ZEROARR" ss, tag) = true := by
  have hm : stripWidthTag "ZEROARR" ≠ "MOV" := by decide +kernel
  unfold plainArrB
  rcases ss with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> (try cases a) <;>
    simp [isLopnB, cmpArgs?, movRegArgs?, carryArgs?, wideArgs?, aluFlagOp?, withWidthTag, hm]

/-- **The check of one operation** followed by reads of the array names `after`, for a
    renaming of array positions: the destination `d` of a store or of an array zeroing has
    an image under `σ` that no later-read name `r ≠ d` shares; never a compile-time-offset
    memory access. A constant-index store is checked as a runtime-indexed one. -/
def coArrStepB (σ : String → String) (i : LinstrRM) (after : List String) : Bool :=
  match i.2 with
  | .store _ _ => match storeStruct? i.1 with
    | some (d, _, _, _) => after.all fun r => r == d || σ r != σ d
    | none => true
  | .zero _ _ => match zeroStruct? i.1 with
    | some d => after.all fun r => r == d || σ r != σ d
    | none => true
  | .storeImm _ _ => match storeImmStruct? i.1 with
    | some (d, _, _, _) => after.all fun r => r == d || σ r != σ d
    | none => true
  | .loadC | .storeC => false
  | _ => true

/-- The check of the operands of a call from the argument position `j`, for the array
    positions `a` and the array names `live` live before the call: an array operand that
    is a register names a live array, and `σ` fixes the name of a word operand that is a
    register. -/
def callOpsB (σ : String → String) (a : Nat → Option Nat) (live : List String) :
    Nat → List LOperand → Bool
  | _, [] => true
  | j, o :: os =>
      (match o with
        | .reg x => if (a j).isSome then live.contains x else σ x == x
        | _ => true)
      && callOpsB σ a live (j + 1) os

/-- A tag other than a load, a store, a zero or a constant-index store tag, at which
    `renArr` renames a call. -/
def callTagB : MemTag → Bool
  | .load _ _ | .store _ _ | .zero _ _ | .storeImm _ _ => false
  | _ => true

/-- **The check of a shadow instruction of a call** `callShadow dst f srcs` with the tag
    `tag` at position `k`, for the array positions `aa f` and the result length `ao f` of
    the symbol: the tag is no load or store tag, the operands pass `callOpsB` against the
    names live before the call, and at a word result `σ` fixes `dst` and the names live
    after the call are live before it; at an array result no name `r ≠ dst` live after the
    call shares the image of `dst` under `σ`, and the names other than `dst` live after the
    call are live before it. -/
def callB (σ : String → String) (L : Nat → List String) (k : Nat)
    (aa : String → Nat → Option Nat) (ao : String → Option Nat) (tag : MemTag)
    (dst f : String) (srcs : List LOperand) : Bool :=
  callTagB tag && callOpsB σ (aa f) (L k) 0 srcs &&
    match ao f with
    | none => σ dst == dst && subB (L (k + 1)) (L k)
    | some _ =>
        (L (k + 1)).all (fun r => r == dst || σ r != σ dst)
          && subB ((L (k + 1)).filter fun r => r != dst) (L k)

/-- **The check of the instruction `i` at position `k`**, by the arm of `evalInstrPMemF`
    that runs it, for the array positions `aa` and the result lengths `ao` of the called
    symbols. A shadow instruction of a call passes `callB`. An instruction with an array
    position is read by no recogniser of the
    flag machine, before and after the renaming, passes `coArrStepB` against the names live
    after it, and the names it reads and the later-live names it does not write are live
    before it. For a compare, a register move, a carry-family operation and a flag-quiet
    lift instruction, the names live after them are live before them. A label and a
    conditional jump pass the names live at each successor. An unconditional jump passes
    the names live at its target. Every other operation passes `coArrStepB` against the
    names live after it, and the names it reads and the later-live names it does not write
    are live before it. Every other instruction is refused. -/
def coInstrB (σ : String → String) (body : List LinstrRM) (L : Nat → List String) (k : Nat)
    (i : LinstrRM) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  match shadowCall? i.1 with
  | some (dst, f, srcs) => callB σ L k aa ao i.2 dst f srcs
  | none =>
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
    `obs` read after the body, for the array positions `aa` and the result lengths `ao` of
    the called symbols: `obs` is in `L body.length`, and the instruction at every position
    passes `coInstrB`. -/
def coCfgB (σ : String → String) (body : List LinstrRM) (L : Nat → List String)
    (obs : List String) (aa : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  subB obs (L body.length)
    && (List.range body.length).all fun k =>
      match body[k]? with
      | some i => coInstrB σ body L k i aa ao
      | none => true

theorem coCfgB_obs {σ : String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : coCfgB σ body L obs aa ao = true) : ∀ r ∈ obs, r ∈ L body.length := by
  unfold coCfgB at h
  exact subB_spec (Bool.and_eq_true_iff.mp h).1

theorem coCfgB_instr {σ : String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : coCfgB σ body L obs aa ao = true) {k : Nat} {i : LinstrRM}
    (hi : body[k]? = some i) : coInstrB σ body L k i aa ao = true := by
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

theorem renStoreImm_of_none {w : LinstrR} (h : storeImmStruct? w = none) :
    renStoreImm σ w = w := by
  unfold renStoreImm
  split
  · split
    · next ho => simp [storeImmStruct?, ho] at h
    · rfl
  · rfl

/-- The renamed wire of a `STOREIMM` writes the renamed destination from the renamed array
    source. -/
theorem storeImmStruct?_renStoreImm (w : LinstrR) :
    storeImmStruct? (renStoreImm σ w)
      = (storeImmStruct? w).map fun p => (σ p.1, σ p.2.1, p.2.2.1, p.2.2.2) := by
  unfold renStoreImm
  split
  · split <;> simp [storeImmStruct?, *]
  · next hne =>
    have : storeImmStruct? w = none := by
      unfold storeImmStruct?
      split
      · next d o b v k => exact absurd rfl (hne d o b v k)
      · rfl
    rw [this]
    rfl

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

theorem renZero_of_none {w : LinstrR} (h : zeroStruct? w = none) : renZero σ w = w := by
  unfold renZero
  split
  · split
    · next ho => simp [zeroStruct?, ho] at h
    · rfl
  · rfl

/-- The renamed wire of a `ZEROARR` zeroes the renamed destination. -/
theorem zeroStruct?_renZero (w : LinstrR) :
    zeroStruct? (renZero σ w) = (zeroStruct? w).map σ := by
  unfold renZero
  split
  · split <;> simp [zeroStruct?, *]
  · next hne =>
    have : zeroStruct? w = none := by
      unfold zeroStruct?
      split
      · next d o ss => exact absurd rfl (hne d o ss)
      · rfl
    rw [this]
    rfl

theorem renCallW_of_none {w : LinstrR} (h : shadowCall? w = none) : renCallW σ w = w := by
  unfold renCallW
  rw [h]

/-- The renaming of a shadow instruction of a call renames its destination and the names
    of its register operands. -/
theorem renCallW_callShadow (dst f : String) (srcs : List LOperand) :
    renCallW σ (callShadow dst f srcs) = callShadow (σ dst) f (srcs.map (renOpR σ)) := by
  unfold renCallW
  rw [shadowCall?_callShadow]

/-- An instruction with no array position that is no shadow instruction of a call is its
    own renaming. -/
theorem renArr_of_not_shape {i : LinstrRM} (h : arrShapeB i = false)
    (hn : shadowCall? i.1 = none) : renArr σ i = i := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | load a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renLoad_of_none h]
  | store a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renStore_of_none h]
  | zero a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renZero_of_none h]
  | storeImm a n =>
      simp only [arrShapeB, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [renArr, renStoreImm_of_none h]
  | _ => simp only [renArr, renCallW_of_none hn]

/-- The renaming of a shadow instruction of a call keeps its kind: a wire is a label
    exactly when its renaming is. -/
theorem isLabel_renCallW (l : LLabel) (w : LinstrR) :
    JasminLsemLabeled.isLabel l (renCallW σ w) = JasminLsemLabeled.isLabel l w := by
  unfold renCallW
  split
  · next h => rw [eq_callShadow_of_shadowCall? h]; rfl
  · rfl

/-- The renaming of a wire that is an operation is an operation. -/
theorem renCallW_lopn {w : LinstrR} (h : ∃ d o s, w = LinstrR.Lopn d o s) :
    ∃ d o s, renCallW σ w = LinstrR.Lopn d o s := by
  unfold renCallW
  split
  · exact ⟨_, _, _, rfl⟩
  · exact h

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
  | zero a n =>
      show JasminLsemLabeled.isLabel l (renZero σ w) = _
      unfold renZero
      split
      · split <;> rfl
      · rfl
  | storeImm a n =>
      show JasminLsemLabeled.isLabel l (renStoreImm σ w) = _
      unfold renStoreImm
      split
      · split <;> rfl
      · rfl
  | _ => exact isLabel_renCallW l w

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
    | zero a n =>
        refine Or.inl ?_
        show ∃ d o s, renZero σ w = LinstrR.Lopn d o s
        subst hd
        unfold renZero
        split
        · split <;> exact ⟨_, _, _, rfl⟩
        · exact ⟨_, _, _, rfl⟩
    | storeImm a n =>
        refine Or.inl ?_
        show ∃ d o s, renStoreImm σ w = LinstrR.Lopn d o s
        subst hd
        unfold renStoreImm
        split
        · split <;> exact ⟨_, _, _, rfl⟩
        · exact ⟨_, _, _, rfl⟩
    | _ => exact Or.inl (renCallW_lopn ⟨d, o, s, hd⟩)
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
    accepted by `coArrStepB` with the later reads `after` that is no shadow instruction of a
    call, a step from `s` is matched by a step of `renArr σ i` from a state related on the
    reads of the operation and the names of `after` it does not write, into a state related
    on `after`. -/
theorem lsemStepMem_coArr {i : LinstrRM} {after : List String}
    (hc : coArrStepB σ i after = true) (hn : shadowCall? i.1 = none) {s s' t : LstateM}
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
  | reg cd =>
      rw [show renArr σ (wire, .reg cd) = (wire, .reg cd) by
        simp only [renArr, renCallW_of_none hn]]
      exact hcast rfl cd h
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
  | storeImm w n =>
      simp only [coArrStepB] at hc
      unfold lsemStepMem at h ⊢
      simp only [renArr] at h ⊢
      rw [storeImmStruct?_renStoreImm]
      cases hl : storeImmStruct? wire with
      | none => rw [hl] at h; cases h
      | some p =>
          obtain ⟨d, b, v, k⟩ := p
          rw [hl] at hc h
          simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
          have hb : b ∈ arrReads (wire, .storeImm w n)
              ++ after.filter fun r => some r != arrWrite (wire, .storeImm w n) := by
            simp [arrReads, hl]
          simp only [Option.map_some, hR.getArr hb, hR.reg] at h ⊢
          cases ha : s.getArr b w n with
          | none => simp [ha] at h
          | some arr =>
            cases hvv : s.reg.getW v w with
            | none => simp [ha, hvv] at h
            | some vv =>
              simp only [ha, hvv, Option.some.injEq] at h
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
  | zero w n =>
      simp only [coArrStepB] at hc
      unfold lsemStepMem at h ⊢
      simp only [renArr] at h ⊢
      rw [zeroStruct?_renZero]
      cases hl : zeroStruct? wire with
      | none => rw [hl] at h; cases h
      | some d =>
          rw [hl] at hc h
          simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
          simp only [Option.map_some, Option.some.injEq] at h ⊢
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
    {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    {i : LinstrRM} {s s' t : LstateMF}
    (hc : coInstrB σ body L s.prog.base.lpc i aa ao = true)
    (hlt : s.prog.base.lpc < body.length)
    (hR : CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base)
    (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (h : evalInstrPMemF (singletonProgM fn body) i s = some t) :
    ∃ t', evalInstrPMemF (singletonProgM fn (body.map (renArr σ))) (renArr σ i) s' = some t'
      ∧ CoRel σ (L t.prog.base.lpc) t.prog.base t'.prog.base
      ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc ≤ body.length := by
  have hn : shadowCall? i.1 = none := by
    by_contra hne
    rw [evalInstrPMemF_shadowCall _ i s hne] at h
    cases h
  obtain ⟨w, tag⟩ := i
  simp only at hn
  unfold coInstrB at hc
  simp only [hn] at hc
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
      obtain ⟨b', hb', hRb⟩ := lsemStepMem_coArr hstep hn (hR.mono (subB_spec hsub)) hb
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
  rw [renArr_of_not_shape hsh' hn]
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
        obtain ⟨b', hb', hRb⟩ := lsemStepMem_coArr hstep hn (hR.mono (subB_spec hsub)) hb
        rw [renArr_of_not_shape hsh' hn] at hb'
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

/-- The renaming of array positions renames the destination and the register operands of a
    shadow instruction of a call with a tag that is no load or store tag. -/
theorem renArr_callShadow (dst f : String) (srcs : List LOperand) {tag : MemTag}
    (ht : callTagB tag = true) :
    renArr σ (callShadow dst f srcs, tag)
      = (callShadow (σ dst) f (srcs.map (renOpR σ)), tag) := by
  cases tag with
  | load a n => cases ht
  | store a n => cases ht
  | zero a n => cases ht
  | storeImm a n => cases ht
  | _ => simp only [renArr, renCallW_callShadow]

/-- **The argument words of the renamed operands.** For operands accepted by `callOpsB` at
    the array positions `a` against the names `live`, the argument words of the renamed
    operands in a state related on `live` are those of the operands. -/
theorem argsRead_renOpR {a : Nat → Option Nat} {live : List String} {b b' : LstateM}
    (hR : CoRel σ live b b') :
    ∀ (j : Nat) (srcs : List LOperand), callOpsB σ a live j srcs = true →
      argsRead a b' j (srcs.map (renOpR σ)) = argsRead a b j srcs
  | _, [], _ => rfl
  | j, o :: os, h => by
      simp only [callOpsB, Bool.and_eq_true] at h
      have ho : argRead a b' j (renOpR σ o) = argRead a b j o := by
        cases o with
        | reg x =>
            cases hj : a j with
            | none =>
                have hx : σ x = x := by simpa [hj] using h.1
                simp only [renOpR, argRead, hj, hx, hR.reg]
            | some n =>
                have hx : x ∈ live := by simpa [hj] using h.1
                simp only [renOpR, argRead, hj, hR.getArr hx]
        | _ => cases a j <;> simp only [renOpR, argRead, hR.reg]
      simp only [List.map_cons, argsRead, ho, argsRead_renOpR hR (j + 1) os h.2]

/-- **One step of a renamed shadow instruction of a call.** For a call `callShadow dst f
    srcs` accepted by `callB` at `k`, whose step from `s` writes the result `x` of the
    declared length `ao f` and is taken again, to the result `x`, from every state and on
    every list of as many operands with the same argument words, the renamed call steps
    from a state related to `s` on `L k` to the state with `x` at the renamed destination,
    related to the successor of `s` on `L (k + 1)`. -/
theorem callStep_coalesce {I : Isa} {L : Nat → List String} {k : Nat}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {tag : MemTag}
    {dst f : String} {srcs : List LOperand} {x : CallRes} {s s' : LstateMF} (P' : LprogM)
    (hc : callB σ L k aa ao tag dst f srcs = true)
    (hR : CoRel σ (L k) s.prog.base s'.prog.base)
    (hfwd : ∀ (P' : LprogM) (tag : MemTag) (dst' : String) (srcs' : List LOperand)
      (s' : LstateMF), srcs'.length = srcs.length →
      argsRead (aa f) s'.prog.base 0 srcs' = argsRead (aa f) s.prog.base 0 srcs →
      I.step P' (callShadow dst' f srcs', tag) s' = some (retRes dst' x s'))
    (hlen : x.len = ao f) :
    I.step P' (renArr σ (callShadow dst f srcs, tag)) s' = some (retRes (σ dst) x s')
      ∧ CoRel σ (L (k + 1)) (retRes dst x s).prog.base (retRes (σ dst) x s').prog.base := by
  simp only [callB, Bool.and_eq_true] at hc
  obtain ⟨⟨ht, hops⟩, hres⟩ := hc
  rw [renArr_callShadow dst f srcs ht]
  refine ⟨hfwd P' tag (σ dst) (srcs.map (renOpR σ)) s' (List.length_map _)
    (argsRead_renOpR hR 0 srcs hops), ?_⟩
  cases x with
  | word r =>
      rw [← hlen] at hres
      simp only [CallRes.len, Bool.and_eq_true, beq_iff_eq] at hres
      rw [LprogIsa.retRes_word, LprogIsa.retRes_word, hres.1]
      exact coRel_nextPc (coRel_setReg (hR.mono (subB_spec hres.2)) dst r)
  | arr a =>
      rw [← hlen] at hres
      simp only [CallRes.len, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
        bne_iff_ne, ne_eq] at hres
      obtain ⟨hcl, hsub⟩ := hres
      refine ⟨?_, hR.mem, hR.cf, hR.of, fun r hr => ?_⟩
      · simp only [LprogIsa.retRes_arr, retArr, LstateM.nextPc, LstateM.setArr, hR.reg]
      · simp only [LprogIsa.retRes_arr, retArr, LstateM.nextPc, LstateM.setArr]
        by_cases hrd : r = dst
        · subst hrd
          simp
        · have hne : σ r ≠ σ dst := by
            rcases hcl r hr with h' | h'
            · exact absurd h' hrd
            · exact h'
          simp only [hne, hrd, if_false]
          exact hR.arr r (subB_spec hsub r (List.mem_filter.mpr ⟨hr, by simpa using hrd⟩))

/-- **One step of a coalesced instruction at an instruction set with local calls.** The
    statement of `evalInstrPMemF_coalesce` for the step of an instruction set `I` whose steps
    contain those of `x86Isa` and whose further steps are local calls at the array positions
    `aa` and the result lengths `ao`, for an instruction accepted by `coInstrB` at `aa` and
    `ao`. -/
theorem step_coalesce_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {i : LinstrRM}
    {s s' t : LstateMF} (hc : coInstrB σ body L s.prog.base.lpc i aa ao = true)
    (hlt : s.prog.base.lpc < body.length)
    (hR : CoRel σ (L s.prog.base.lpc) s.prog.base s'.prog.base)
    (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (h : I.step (singletonProgM fn body) i s = some t) :
    ∃ t', I.step (singletonProgM fn (body.map (renArr σ))) (renArr σ i) s' = some t'
      ∧ CoRel σ (L t.prog.base.lpc) t.prog.base t'.prog.base
      ∧ t'.prog.lfn = t.prog.lfn ∧ t.prog.lfn = s.prog.lfn ∧ t'.zf = t.zf
      ∧ t.prog.base.lpc ≤ body.length := by
  rcases hcl _ i s t h with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, hlen⟩
  · obtain ⟨t', ht', hrest⟩ := evalInstrPMemF_coalesce hc hlt hR hfn hz hx
    exact ⟨t', hle _ _ _ _ ht', hrest⟩
  · obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    have hcB : callB σ L s.prog.base.lpc aa ao tag dst f srcs = true := by
      unfold coInstrB at hc
      simpa only [shadowCall?_callShadow] using hc
    obtain ⟨hst, hRt⟩ := callStep_coalesce (singletonProgM fn (body.map (renArr σ))) hcB hR
      hfwd hlen
    refine ⟨_, hst, ?_, ?_, LprogIsa.lfn_retRes dst x s, ?_, ?_⟩
    · rw [LprogIsa.lpc_retRes]
      exact hRt
    · rw [LprogIsa.lfn_retRes, LprogIsa.lfn_retRes]
      exact hfn
    · cases x <;> exact hz
    · rw [LprogIsa.lpc_retRes]
      exact hlt

/-! ## 6. The run -/

/-- **The coalesced body at an instruction set with local calls.** For a body accepted by
    `coCfgB σ body L obs aa ao` and an instruction set `I` whose steps contain those of
    `x86Isa` and whose further steps are local calls at the array positions `aa` and the
    result lengths `ao`, a halting run of `I` on `body`, from a state `s` of the function `fn`
    at a position at most `body.length`, is matched with the same fuel by a halting run of
    `I` on the coalesced body `body.map (renArr σ)` from every state `s'` that has the
    registers, word memory, flags and function name of `s` and whose arrays agree with those
    of `s` through `σ` on the names `L` gives the position of `s`. The final states have equal
    registers, word memory and flags, and their arrays agree through `σ` on `obs`. -/
theorem lsemFuelMemF_coalesce_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {L : Nat → List String} {obs : List String}
    (hc : coCfgB σ body L obs aa ao = true) :
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
