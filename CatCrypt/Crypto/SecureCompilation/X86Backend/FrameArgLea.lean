/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrLoad
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
public import CatCrypt.Crypto.SecureCompilation.SepLogic.AddrRun

/-!
# The argument moves of frame-array roots

The allocator gives a frame-array root, a name that the virtual body reads and does not
define, a register or a spill slot `x` (`physNameForBody`). The marshalling of a call
(`expandCallShadows`) passes the root to a linked function by the move `MOV:64 a, x` into an
argument register `a`, and `savedArgMoves` keeps that move, since no save slot holds the
value of `x`. The pass `faArgLeas` replaces the move by the address load `LEA:64 a, q` of the
frame-array name `q` of the root, at the reload pairs `(x, q)` of the frame arrays
(`faReloadPairs`).

The pass refuses a shared register (`faArgB`): the keys of the pairs are pairwise different
and different from the names `others` that hold other values from the entry, an argument
move from a key lies before the first instruction that writes the key, and no branch at or
after that instruction returns to a position up to it. An indexed store writes no register,
so the store into a frame array, whose destination operand is the key, is no write
(`writesB`). A refused body is unchanged.

## Main results

* `stepA_faArgLea`: the rewritten instruction writes the frame address to the argument
  register, at every state, and keeps the memory and the flags.
* `stepA_faArgLeas`: at a state where the keys hold the frame addresses (`RootsHeld`), the
  step of the pass is the step of the body.
* `rootsHeld_stepA`, `rootsHeld_callAC`, `rootsHeld_callAC_pool`: a step and the summary
  step of a call keep `RootsHeld`.
* `runA_faArgLeas`: the run of the pass is the run of the body. The run `runA` has no step
  at a call.
* `stepsC_faArgLeas`: the runs with calls (`StepC`) of the pass are those of the body.
* `instrLeakA_faArgLea`: the rewritten instruction has no event.
* `faArgB_iff`: the check is exactly the absence of sharing.
* `faArgB_image`: the check accepts the marshalled body of an allocated body that writes no
  key before its epilogue.
* `faArgLea_mem_image`: on an accepted marshalled body, the pass emits the address load for
  each argument of a call that is a frame root.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArgLea

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (gpNameB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct? movImmStruct?_spec)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (Loc stepWrites stepA_writesIn agreeOn_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (faB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall
  (operandNamesB entrySaveOf? savedArgMoveArm savedArgMoves clobN callAC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (CallOut read64_congr_range)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (instrLeakA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrLoad (faLoad? instrLeakA_leaFa)

/-! ## The pass -/

/-- An argument move: the 64-bit move `MOV:64 a, x` into an argument register `a`, as
    `(a, x)`. -/
def argMove? : LinstrR → Option (String × String)
  | .Lopn [.reg a] o [.reg x] =>
      if o = "MOV:64" ∧ a ∈ sysvArgRegs then some (a, x) else none
  | _ => none

/-- The instruction may change the name `x`: a destination operand names `x`, and the
    instruction is no indexed store (`storeIdxA?`), whose destination operand is the stored
    array and which writes no register on the address machine. -/
def writesB (x : String) : LinstrR → Bool
  | .Lopn ds o ss => ds.any (operandNamesB x) && (storeIdxA? (.Lopn ds o ss)).isNone
  | _ => false

/-- The instruction of an allocated body may change the name `x` in the marshalled body at
    the out symbols `outs`: a call shadow changes its destination unless it is an out call,
    whose expansion copies no result, and every other instruction as `writesB`. -/
def allocWritesB (outs : List String) (x : String) : LinstrR → Bool
  | .Lopn [.reg d] o ss =>
      if hasPrefix o "CALLN:" then d == x
      else if hasPrefix o "CALL:" then d == x && !outs.contains (strDrop o 5)
      else writesB x (.Lopn [.reg d] o ss)
  | i => writesB x i

/-- The position of the first instruction of `body` that writes `x`, and the length of
    `body` when none does. -/
def writeIdx (body : Lcmd) (x : String) : Nat :=
  body.findIdx fun i => writesB x i.li_i

/-- **The check that a name is held up to its first write**: every argument move from `x`
    lies before the first write of `x`, and every branch at or after that write goes to a
    position after it. -/
def heldB (body : Lcmd) (x : String) : Bool :=
  (List.range body.length).all fun k => (body[k]?).all fun i =>
    ((argMove? i.li_i).all fun m => m.2 != x || decide (k < writeIdx body x)) &&
      match i.li_i with
      | .Lcond _ l =>
          decide (k < writeIdx body x) ||
            (labelAt body l).all fun p => decide (writeIdx body x < p)
      | _ => true

/-- **The check of one pair `(x, q)`**: `q` is a frame-array name that no instruction writes,
    and `x` is no cell, is none of the names `others` that hold another value, and is held up
    to its first write (`heldB`). -/
def faRootB (others : List String) (body : Lcmd) (e : String × String) : Bool :=
  faB e.2 && (cellParts? e.1).isNone && !others.contains e.1
    && body.all (fun i => !writesB e.2 i.li_i) && heldB body e.1

/-- **The refusal of a shared register**: the keys of the reload pairs `fa` of the frame
    arrays are pairwise different and each pair passes `faRootB`. -/
def faArgB (fa : List (String × String)) (others : List String) (body : Lcmd) : Bool :=
  decide (fa.map Prod.fst).Nodup && fa.all (faRootB others body)

/-- The arm of `faArgLeas` on one instruction: an argument move `MOV:64 a, x` from a key of
    `fa` with the frame-array name `q` is the address load `LEA:64 a, q`. -/
def faArgArm (fa : List (String × String)) (i : Linstr) : Linstr :=
  match argMove? i.li_i with
  | some (a, x) =>
      match fa.lookup x with
      | some q => ⟨i.li_ii, .Lopn [.reg a] "LEA:64" [.reg q]⟩
      | none => i
  | none => i

/-- **The argument moves of frame-array roots are address loads.** At the reload pairs `fa`
    of the frame arrays (`faReloadPairs`) and the names `others` of the other values held
    from the entry, a body that passes `faArgB` has `faArgArm` applied to each instruction;
    every other body is unchanged. -/
def faArgLeas (fa : List (String × String)) (others : List String) (body : Lcmd) : Lcmd :=
  if faArgB fa others body then body.map (faArgArm fa) else body

section Basic

variable {fa : List (String × String)} {others : List String} {body : Lcmd}

/-- The instructions that `argMove?` reads. -/
theorem argMove?_eq_some {i : LinstrR} {a x : String} :
    argMove? i = some (a, x) ↔ i = .Lopn [.reg a] "MOV:64" [.reg x] ∧ a ∈ sysvArgRegs := by
  unfold argMove?
  grind

/-- An accepted body has the arm applied to each instruction. -/
theorem faArgLeas_of_accepted (h : faArgB fa others body = true) :
    faArgLeas fa others body = body.map (faArgArm fa) := by
  simp [faArgLeas, h]

/-- A refused body is unchanged. -/
theorem faArgLeas_of_refused (h : faArgB fa others body = false) :
    faArgLeas fa others body = body := by
  simp [faArgLeas, h]

/-- Without frame arrays the pass is the identity. -/
@[simp] theorem faArgLeas_nil (others : List String) (body : Lcmd) :
    faArgLeas [] others body = body := by
  have h : faArgArm [] = id := by
    funext i
    unfold faArgArm
    grind
  simp [faArgLeas, h]

/-- The pass keeps the length of a body, so the positions of the calls are kept. -/
@[simp] theorem faArgLeas_length : (faArgLeas fa others body).length = body.length := by
  unfold faArgLeas
  split <;> simp

/-- A value that a lookup returns is the second component of a member. -/
private theorem mem_of_lookup {x q : String} {l : List (String × String)}
    (h : l.lookup x = some q) : (x, q) ∈ l := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

/-- With pairwise different first components, the lookup returns each member. -/
private theorem lookup_of_mem {x q : String} :
    ∀ {l : List (String × String)}, (l.map Prod.fst).Nodup → (x, q) ∈ l →
      l.lookup x = some q
  | [], _, h => by simp at h
  | (y, r) :: l, hn, h => by
      have := @lookup_of_mem x q l
      grind

/-- The arm keeps an instruction, or replaces an argument move from a key by the address
    load of its frame-array name. -/
theorem faArgArm_cases (fa : List (String × String)) (i : Linstr) :
    faArgArm fa i = i ∨ ∃ a x q, i.li_i = .Lopn [.reg a] "MOV:64" [.reg x] ∧ a ∈ sysvArgRegs
      ∧ (x, q) ∈ fa ∧ faArgArm fa i = ⟨i.li_ii, .Lopn [.reg a] "LEA:64" [.reg q]⟩ := by
  unfold faArgArm
  grind [argMove?_eq_some, mem_of_lookup]

/-- A name is written before the first position that writes it at no instruction. -/
theorem writesB_of_lt {x : String} {k : Nat} (hk : k < writeIdx body x) {i : Linstr}
    (hb : body[k]? = some i) : writesB x i.li_i = false := by
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  simpa using List.not_of_lt_findIdx hk

/-- The first write of a name is at most every write of it. -/
theorem writeIdx_le {x : String} {k : Nat} {i : Linstr} (hb : body[k]? = some i)
    (hw : writesB x i.li_i = true) : writeIdx body x ≤ k := by
  grind [writesB_of_lt]

/-- A destination name of an instruction that is no indexed store is written by it. -/
theorem writesB_of_mem_dstNames {x : String} {i : LinstrR} (h : x ∈ dstNames i)
    (hs : storeIdxA? i = none) : writesB x i = true := by
  cases i with
  | Lopn ds o ss =>
    obtain ⟨d, hd, hx⟩ := List.mem_flatMap.mp h
    simp only [writesB, hs, Option.isNone_none, Bool.and_true]
    refine List.any_eq_true.mpr ⟨d, hd, ?_⟩
    cases d <;> grind [JasminLsemExportRewrites.opNames, operandNamesB]
  | _ => simp [dstNames] at h

/-- **The check is exactly the absence of sharing.** The keys are pairwise different; each
    frame-array name is a name `faB` that no instruction writes; each key is no cell and none
    of the names `others`; each argument move from a key lies before the first write of the
    key; and each branch at or after that write goes to a position after it. -/
theorem faArgB_iff :
    faArgB fa others body = true ↔ (fa.map Prod.fst).Nodup ∧ ∀ x q, (x, q) ∈ fa →
      faB q = true ∧ cellParts? x = none ∧ x ∉ others
        ∧ (∀ i ∈ body, writesB q i.li_i = false)
        ∧ (∀ k i a, body[k]? = some i → argMove? i.li_i = some (a, x) → k < writeIdx body x)
        ∧ (∀ k i cc l p, body[k]? = some i → i.li_i = .Lcond cc l → writeIdx body x ≤ k →
            labelAt body l = some p → writeIdx body x < p) := by
  simp only [faArgB, faRootB, heldB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Option.isNone_iff_eq_none, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, Prod.forall]
  refine and_congr_right fun _ => forall_congr' fun x => forall_congr' fun q =>
    imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, h3, h4, fun k i a hb hm => ?_, fun k i cc l p hb hi hk hl => ?_⟩
    · have := h5 k (List.getElem?_eq_some_iff.mp hb).1
      simp_all
    · have := h5 k (List.getElem?_eq_some_iff.mp hb).1
      simp_all
      omega
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, fun k hk => ?_⟩
    have hb := List.getElem?_eq_getElem hk
    simp only [hb, Option.all_some, Bool.and_eq_true, Option.all_eq_true]
    refine ⟨fun m hm => ?_, ?_⟩
    · obtain ⟨a, y⟩ := m
      by_cases e : y = x
      · subst e
        simp [h5 k _ a hb hm]
      · simp [e]
    · split
      · rename_i cc l hi
        by_cases hw : k < writeIdx body x
        · simp [hw]
        · cases hl : labelAt body l with
          | none => simp
          | some p => simp [h6 k _ cc l p hb hi (by omega) hl]
      · rfl

/-- A key that holds another value from the entry is refused. -/
theorem faArgB_of_shared {x q : String} (he : (x, q) ∈ fa) (hx : x ∈ others) :
    faArgB fa others body = false := by
  grind [faArgB_iff]

end Basic

/-! ## The rewritten instruction -/

/-- The argument registers are no cells. -/
theorem cellParts?_argReg {a : String} (h : a ∈ sysvArgRegs) : cellParts? a = none := by
  refine DecodePrintedAddr.cellParts?_gp ?_
  revert a
  decide

/-- The step of the body at an address load of a frame-array name writes the frame address. -/
theorem stepA_lea {frame : String → Option (BitVec 64)} {body : Lcmd} {s : LstateA}
    {ii : Nat} {d q : String}
    (hb : body[s.reg.lpc]? = some ⟨ii, .Lopn [.reg d] "LEA:64" [.reg q]⟩)
    (hq : faB q = true) {v : BitVec 64} (hv : frame q = some v) (zf : Bool) :
    stepA frame body s zf = some ({ s with reg := (s.reg.setReg d v).nextPc }, zf) := by
  rw [ImageAddrSim.stepA_lopn frame hb rfl, normA_of_caret_free (by decide),
    tagAt_of_ne (by simp [movImmStruct?]), tagA_lea]
  simpa using fstepA_leaFa frame hq hv s zf

/-- **The rewritten instruction passes the pointer.** At a position of an accepted body with
    an argument move `MOV:64 a, x` from a key `x` of the frame-array name `q` at the frame
    address `v`, the step of the pass writes `v` to `a` at every state, and keeps the memory
    and the flags. -/
theorem stepA_faArgLea {fa : List (String × String)} {others : List String} {body : Lcmd}
    (hok : faArgB fa others body = true) {frame : String → Option (BitVec 64)} {s : LstateA}
    {i : Linstr} (hb : body[s.reg.lpc]? = some i) {a x q : String}
    (hm : argMove? i.li_i = some (a, x)) (he : (x, q) ∈ fa) {v : BitVec 64}
    (hv : frame q = some v) (zf : Bool) :
    stepA frame (faArgLeas fa others body) s zf
      = some ({ s with reg := (s.reg.setReg a v).nextPc }, zf) := by
  obtain ⟨hn, hr⟩ := faArgB_iff.mp hok
  refine stepA_lea (ii := i.li_ii) ?_ (hr x q he).1 hv zf
  simp [faArgLeas_of_accepted hok, hb, faArgArm, hm, lookup_of_mem hn he]

/-- **The rewritten instruction accesses no memory**: it has no event. -/
theorem instrLeakA_faArgLea {fa : List (String × String)} {others : List String} {body : Lcmd}
    (hok : faArgB fa others body = true) {i : Linstr} {a x q : String}
    (hm : argMove? i.li_i = some (a, x)) (he : (x, q) ∈ fa)
    (frame : String → Option (BitVec 64)) (s : LstateA) :
    instrLeakA frame ((faArgArm fa i).li_i, .reg none) s = [] := by
  obtain ⟨hn, hr⟩ := faArgB_iff.mp hok
  simpa [faArgArm, hm, lookup_of_mem hn he] using instrLeakA_leaFa frame (hr x q he).1 s

/-- **The rewritten instruction is a pointer load of a frame array** (`faLoad?`) at every
    slot map with the frame-array name as a slot. -/
theorem faLoad?_faArgArm {fa : List (String × String)} {others : List String} {body : Lcmd}
    (hok : faArgB fa others body = true) {i : Linstr} {a x q : String}
    (hm : argMove? i.li_i = some (a, x)) (he : (x, q) ∈ fa)
    {slotArr : String → Option (String × Nat)} (hs : (slotArr q).isSome = true) :
    faLoad? slotArr (faArgArm fa i).li_i = some (a, q) := by
  obtain ⟨hn, hr⟩ := faArgB_iff.mp hok
  simp [faArgArm, hm, lookup_of_mem hn he, FrameArrLoad.faLoad?_eq_some, (hr x q he).1, hs]

/-! ## The simulation -/

/-- The name `x` holds the frame address of `q`: the register `x`, or the frame word of a
    spill slot `x`. -/
def HoldsAddr (frame : String → Option (BitVec 64)) (s : LstateA) (x q : String) : Prop :=
  ∃ v, frame q = some v ∧
    match frame x with
    | none => s.reg.lvm x = ⟨64, v⟩
    | some c => read64 s.mem c = v

/-- **The keys hold the frame addresses up to their first writes.** -/
def RootsHeld (frame : String → Option (BitVec 64)) (fa : List (String × String))
    (body : Lcmd) (s : LstateA) : Prop :=
  ∀ x q, (x, q) ∈ fa → s.reg.lpc ≤ writeIdx body x → HoldsAddr frame s x q

/-- The step at the program counter of `s` writes no byte of the frame word of a key before
    the first write of the key. -/
def SpillKept (frame : String → Option (BitVec 64)) (fa : List (String × String))
    (body : Lcmd) (s : LstateA) : Prop :=
  ∀ x q c, (x, q) ∈ fa → frame x = some c → s.reg.lpc < writeIdx body x →
    ∀ y, InRange8 c y → Loc.mem y ∉ stepWrites frame body s

/-- Keys that are registers have no frame word to keep. -/
theorem spillKept_of_regs {frame : String → Option (BitVec 64)} {fa : List (String × String)}
    (h : ∀ x q, (x, q) ∈ fa → frame x = none) (body : Lcmd) (s : LstateA) :
    SpillKept frame fa body s := by
  intro x q c he hc
  simp [h x q he] at hc

section Sim

variable {frame : String → Option (BitVec 64)} {fa : List (String × String)}
  {others : List String} {body : Lcmd}

/-- The move from a name that holds a frame address writes that address. -/
theorem fstepA_argMove {a x q : String} (ha : a ∈ sysvArgRegs) (hfa : frame a = none)
    (hx : cellParts? x = none) {s : LstateA} (hh : HoldsAddr frame s x q) (zf : Bool) :
    ∃ v, frame q = some v ∧
      fstepA frame (.Lopn [.reg a] "MOV:64" [.reg x], .reg none) s zf
        = some ({ s with reg := (s.reg.setReg a v).nextPc }, zf) := by
  obtain ⟨v, hv, hh⟩ := hh
  refine ⟨v, hv, ?_⟩
  have hm := slotMov?_mov64 (cellParts?_argReg ha) hx
  cases hc : frame x with
  | none =>
    simp only [hc] at hh
    have hs : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
    simp [fstepA, hm, hc, hfa, regStepA, JasminLsemMemFlagNestJoin.fstepF, readReg,
      JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?, hs, hh,
      LstateM.setReg, LstateM.nextPc]
  | some c =>
    rw [hc] at hh
    simp [fstepA, hm, hc, hh]

/-- The arm keeps whether the body has halted. -/
theorem haltedA_faArgLeas (s : LstateA) :
    haltedA (faArgLeas fa others body) s = haltedA body s := by
  unfold faArgLeas
  split
  · unfold haltedA
    rw [List.getElem?_map]
    cases hb : body[s.reg.lpc]? with
    | none => rfl
    | some i =>
      rcases faArgArm_cases fa i with e | ⟨a, x, q, hi, -, -, e⟩
      · simp [e]
      · obtain ⟨ii, li⟩ := i
        subst hi
        simp [e]
  · rfl

/-- The pass keeps the position of each label. -/
theorem labelAt_faArgLeas (l : LLabel) :
    labelAt (faArgLeas fa others body) l = labelAt body l := by
  unfold faArgLeas
  split
  · unfold labelAt
    rw [List.findIdx?_map]
    congr 1
    funext i
    rcases faArgArm_cases fa i with e | ⟨a, x, q, hi, -, -, e⟩
    · simp [e]
    · simp [e, hi, isLabelB]
  · rfl

/-- The pass keeps the tag of each instruction that it keeps: the key of an argument move
    after an immediate move is not the destination of that move. -/
theorem tagAt_faArgLeas (hok : faArgB fa others body = true) {k : Nat} {i : Linstr}
    (hb : body[k]? = some i) :
    tagAt (body.map (faArgArm fa)) k i.li_i = tagAt body k i.li_i := by
  cases hm : movImmStruct? i.li_i with
  | none => rw [tagAt_of_ne hm, tagAt_of_ne hm]
  | some p =>
    obtain ⟨d, n⟩ := p
    obtain ⟨o, hi⟩ := movImmStruct?_spec hm
    have hw : writesB d i.li_i = true := by simp [hi, writesB, operandNamesB, storeIdxA?]
    have key : bitInNext (body.map (faArgArm fa)) k d = bitInNext body k d := by
      unfold bitInNext
      rw [← List.map_drop]
      refine useFirst_congr _ _ _ _ (by simp) fun j hj hj' => ?_
      simp only [List.getElem_map, List.getElem_drop]
      have hb' : body[k + 1 + j]? = some (body[k + 1 + j]'(by simp at hj; omega)) :=
        List.getElem?_eq_getElem _
      generalize body[k + 1 + j]'(by simp at hj; omega) = z at hb'
      rcases faArgArm_cases fa z with e | ⟨a, x, q, hz, ha, he, e⟩
      · simp [e]
      · obtain ⟨-, -, -, hq, hlt, -⟩ := (faArgB_iff.mp hok).2 x q he
        have hk := hlt _ z a hb' (argMove?_eq_some.mpr ⟨hz, ha⟩)
        have hxd : (x == d) = false := beq_false_of_ne fun h => by
          have := writeIdx_le hb (h ▸ hw)
          omega
        have hqd : (q == d) = false := beq_false_of_ne (by grind)
        simp [e, hz, namesB, opNamesB, bitUseB, carryUseB, condUseB, hxd, hqd]
    simp [tagAt, bitMovB, hm, key]

/-- **The step of the pass is the step of the body** at a state where the keys hold the
    frame addresses. -/
theorem stepA_faArgLeas (hargs : ∀ a ∈ sysvArgRegs, frame a = none) {s : LstateA}
    (hh : RootsHeld frame fa body s) (zf : Bool) :
    stepA frame (faArgLeas fa others body) s zf = stepA frame body s zf := by
  cases hok : faArgB fa others body with
  | false => rw [faArgLeas_of_refused hok]
  | true =>
    cases hb : body[s.reg.lpc]? with
    | none => simp [stepA, faArgLeas_of_accepted hok, hb]
    | some i =>
      rcases faArgArm_cases fa i with e | ⟨a, x, q, hi, ha, he, e⟩
      · obtain ⟨ii, li⟩ := i
        have hl := labelAt_faArgLeas (fa := fa) (others := others) (body := body)
        have ht := tagAt_faArgLeas hok hb
        rw [faArgLeas_of_accepted hok] at hl ⊢
        cases li with
        | Lcond cc l => cases cc <;> simp_all [stepA]
        | _ => simp_all [stepA]
      · have hm := argMove?_eq_some.mpr ⟨hi, ha⟩
        obtain ⟨-, hx, -, -, hlt, -⟩ := (faArgB_iff.mp hok).2 x q he
        have hk := hlt _ i a hb hm
        obtain ⟨v, hv, hs⟩ := fstepA_argMove ha (hargs a ha) hx (hh x q he hk.le) zf
        have ht : tagA (.Lopn [.reg a] "MOV:64" [.reg x]) = .reg none := by
          simp [tagA, width_tag]
        rw [stepA_faArgLea hok hb hm he hv zf, ImageAddrSim.stepA_lopn frame hb hi, hi,
          normA_of_caret_free (by decide), tagAt_of_ne (by simp [movImmStruct?]), ht]
        simpa using hs.symm

/-- A step that ends at a position up to the first write of a key starts before that
    write. -/
theorem lt_writeIdx_of_stepA (hok : faArgB fa others body = true) {x q : String}
    (he : (x, q) ∈ fa) {s : LstateA} {zf : Bool} {p : LstateA × Bool}
    (hst : stepA frame body s zf = some p) (hp : p.1.reg.lpc ≤ writeIdx body x) :
    s.reg.lpc < writeIdx body x := by
  by_contra hlt
  obtain ⟨-, -, -, -, -, hj⟩ := (faArgB_iff.mp hok).2 x q he
  unfold stepA at hst
  split at hst
  · have := DecodePrintedAddr.fstepA_lpc frame _ s p.1 zf p.2 hst
    omega
  · simp only [Option.some.injEq] at hst
    subst hst
    simp [LstateA.setLpc] at hp
    omega
  · rename_i ii cc l hb
    split at hst
    · split at hst
      · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hst
        have := hj _ _ _ _ _ hb rfl (by omega) ht
        simp [LstateA.setLpc] at hp
        omega
      · simp only [Option.some.injEq] at hst
        subst hst
        simp [LstateA.setLpc] at hp
        omega
    · cases hst
  · cases hst

/-- A step keeps each register that its instruction does not write (`writesB`), the array
    operand of an indexed store among them. -/
theorem lvm_of_stepA {s : LstateA} {zf : Bool} {p : LstateA × Bool}
    (hst : stepA frame body s zf = some p) {x : String}
    (hn : ∀ i, body[s.reg.lpc]? = some i → writesB x i.li_i = false) :
    p.1.reg.lvm x = s.reg.lvm x := by
  have hw := agreeOn_iff.mp (stepA_writesIn frame body hst)
  by_cases hx : Loc.reg x ∈ stepWrites frame body s
  · unfold stepWrites at hx
    split at hx
    · rename_i ii ds o ss hb
      have hd : x ∈ dstNames (normA (.Lopn ds o ss)) := hx
      rw [ImageAddrSim.dstNames_normA] at hd
      cases hs : storeIdxA? (.Lopn ds o ss) with
      | none =>
        have := writesB_of_mem_dstNames hd hs
        simp [hn _ hb] at this
      | some r =>
        unfold storeIdxA? at hs
        split at hs
        · rename_i d o' b j sc v heq
          cases heq
          split at hs
          · rename_i hu
            rw [ImageAddrSim.stepA_lopn frame hb rfl, tagAt_of_ne (by simp [movImmStruct?])] at hst
            simp only [tagA, normA, hu, fstepA, storeIdxA?, String.reduceEq, ↓reduceIte] at hst
            split at hst
            · split at hst <;> first
                | (cases hst; rfl)
                | cases hst
            · cases hst
          · cases hs
        · cases hs
    · simp at hx
  · exact (hw (.reg x) hx).symm

/-- **A step keeps `RootsHeld`**, where it keeps the frame words of the keys that are spill
    slots. -/
theorem rootsHeld_stepA (hok : faArgB fa others body = true) {s : LstateA} {zf : Bool}
    (hh : RootsHeld frame fa body s) (hk : SpillKept frame fa body s) {p : LstateA × Bool}
    (hst : stepA frame body s zf = some p) : RootsHeld frame fa body p.1 := by
  intro x q he hp
  have hlt := lt_writeIdx_of_stepA hok he hst hp
  obtain ⟨v, hv, hval⟩ := hh x q he hlt.le
  refine ⟨v, hv, ?_⟩
  have hw := agreeOn_iff.mp (stepA_writesIn frame body hst)
  cases hc : frame x with
  | none =>
    rw [hc] at hval
    exact (lvm_of_stepA hst fun i hb => writesB_of_lt hlt hb).trans hval
  | some c =>
    rw [hc] at hval
    exact (read64_congr_range fun y hy => (hw (.mem y) (hk x q c he hc hlt y hy)).symm).trans hval

/-- **The summary step of a call keeps `RootsHeld`**: the callee keeps the registers among
    the keys and the frame words of the keys that are spill slots. -/
theorem rootsHeld_callAC (c : CalleeSig) (ω : CallOut) {m : AMem} {s : LstateA}
    (hh : RootsHeld frame fa body s)
    (hreg : ∀ x q, (x, q) ∈ fa → frame x = none → clobN c x = false)
    (hmem : ∀ x q a, (x, q) ∈ fa → frame x = some a → ∀ y, InRange8 a y → m y = s.mem y) :
    RootsHeld frame fa body (callAC c ω m s) := by
  intro x q he hp
  rw [ImageAddrCall.callAC_lpc] at hp
  obtain ⟨v, hv, hval⟩ := hh x q he (by omega)
  refine ⟨v, hv, ?_⟩
  cases hc : frame x with
  | none =>
    rw [hc] at hval
    simpa [callAC, ImageAddrCall.callRegsC, hreg x q he hc] using hval
  | some a =>
    rw [hc] at hval
    exact (read64_congr_range (hmem x q a he hc)).trans hval

/-- **The summary step of a call keeps `RootsHeld` at a checked allocation pool**: each key
    is a name of the pool or a spill slot whose frame word the callee keeps. -/
theorem rootsHeld_callAC_pool {c : CalleeSig} {pool : List String}
    (hpool : Callee.keepPoolB c pool = true) (ω : CallOut) {m : AMem} {s : LstateA}
    (hh : RootsHeld frame fa body s)
    (hreg : ∀ x q, (x, q) ∈ fa → frame x = none → x ∈ pool)
    (hmem : ∀ x q a, (x, q) ∈ fa → frame x = some a → ∀ y, InRange8 a y → m y = s.mem y) :
    RootsHeld frame fa body (callAC c ω m s) :=
  rootsHeld_callAC c ω hh
    (fun x q he hx => (ImageAddrCall.keepPoolB_clobN hpool (hreg x q he hx)).1) hmem

/-- **The run of the pass is the run of the body.** Let the argument registers have no frame
    words, let the keys hold the frame addresses at the start, and let every step that the
    body reaches keep the frame words of the keys that are spill slots. Then the pass and the
    body have the same runs. -/
theorem runA_faArgLeas (hargs : ∀ a ∈ sysvArgRegs, frame a = none) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool), RootsHeld frame fa body s →
      (∀ t, Relation.ReflTransGen
          (fun p p' : LstateA × Bool => stepA frame body p.1 p.2 = some p') (s, zf) t →
        SpillKept frame fa body t.1) →
      runA frame (faArgLeas fa others body) fuel s zf = runA frame body fuel s zf := by
  intro fuel
  induction fuel with
  | zero =>
    intro s zf _ _
    simp [runA, haltedA_faArgLeas]
  | succ f ih =>
    intro s zf hh hk
    cases hok : faArgB fa others body with
    | false => rw [faArgLeas_of_refused hok]
    | true =>
      simp only [runA, haltedA_faArgLeas, stepA_faArgLeas hargs hh]
      split
      · rfl
      · cases hst : stepA frame body s zf with
        | none => rfl
        | some p =>
          exact ih p.1 p.2 (rootsHeld_stepA hok hh (hk (s, zf) .refl) hst)
            fun t ht => hk t (Relation.ReflTransGen.head hst ht)

/-- **The run of the pass is the run of the body where the keys are registers.** -/
theorem runA_faArgLeas_regs (hargs : ∀ a ∈ sysvArgRegs, frame a = none)
    (hregs : ∀ x q, (x, q) ∈ fa → frame x = none) (fuel : Nat) {s : LstateA} (zf : Bool)
    (hh : RootsHeld frame fa body s) :
    runA frame (faArgLeas fa others body) fuel s zf = runA frame body fuel s zf :=
  runA_faArgLeas hargs fuel s zf hh fun t _ => spillKept_of_regs hregs body t.1

/-- A step of a body with calls: a step of the address machine (`stepA`, which has none at a
    call), or at a call the summary step `callAC` of a callee that keeps the registers among
    the keys and the frame words of the keys that are spill slots. -/
def StepC (frame : String → Option (BitVec 64)) (fa : List (String × String)) (body : Lcmd)
    (p p' : LstateA × Bool) : Prop :=
  stepA frame body p.1 p.2 = some p' ∨
    ∃ i ra t, ∃ (c : CalleeSig) (ω : CallOut) (m : AMem),
      body[p.1.reg.lpc]? = some i ∧ i.li_i = .Lcall ra t ∧ p' = (callAC c ω m p.1, ω.zf)
        ∧ (∀ x q, (x, q) ∈ fa → frame x = none → clobN c x = false)
        ∧ ∀ x q a, (x, q) ∈ fa → frame x = some a → ∀ y, InRange8 a y → m y = p.1.mem y

/-- The pass keeps the calls and their positions. -/
theorem getElem?_faArgLeas_call {k : Nat} {i : Linstr} {ra : Option String}
    {t : String × LLabel} (hi : i.li_i = .Lcall ra t) :
    (faArgLeas fa others body)[k]? = some i ↔ body[k]? = some i := by
  unfold faArgLeas
  split
  · rw [List.getElem?_map]
    cases hb : body[k]? with
    | none => simp
    | some j =>
      rcases faArgArm_cases fa j with e | ⟨a, x, q, hj, -, -, e⟩
      · simp [e]
      · grind
  · rfl

/-- At a state where the keys hold the frame addresses, the steps with calls of the pass are
    those of the body. -/
theorem stepC_faArgLeas (hargs : ∀ a ∈ sysvArgRegs, frame a = none) {p p' : LstateA × Bool}
    (hh : RootsHeld frame fa body p.1) :
    StepC frame fa (faArgLeas fa others body) p p' ↔ StepC frame fa body p p' := by
  simp only [StepC, stepA_faArgLeas hargs hh]
  grind [getElem?_faArgLeas_call]

/-- **The runs with calls of the pass are those of the body.** Let the argument registers
    have no frame words, let the keys hold the frame addresses at the start, and let every
    state that the body reaches keep the frame words of the keys that are spill slots. Then
    the pass reaches a state through steps and calls exactly when the body does. -/
theorem stepsC_faArgLeas (hargs : ∀ a ∈ sysvArgRegs, frame a = none) {p t : LstateA × Bool}
    (hh : RootsHeld frame fa body p.1)
    (hk : ∀ u, Relation.ReflTransGen (StepC frame fa body) p u →
      SpillKept frame fa body u.1) :
    Relation.ReflTransGen (StepC frame fa (faArgLeas fa others body)) p t ↔
      Relation.ReflTransGen (StepC frame fa body) p t := by
  cases hok : faArgB fa others body with
  | false => rw [faArgLeas_of_refused hok]
  | true =>
    have held : ∀ u, Relation.ReflTransGen (StepC frame fa body) p u →
        RootsHeld frame fa body u.1 := by
      intro u hu
      induction hu with
      | refl => exact hh
      | tail hb hs ih =>
        rcases hs with hs | ⟨i, ra, tg, c, ω, m, -, -, rfl, hreg, hmem⟩
        · exact rootsHeld_stepA hok ih (hk _ hb) hs
        · exact rootsHeld_callAC c ω ih hreg hmem
    constructor <;> intro h
    · induction h with
      | refl => exact .refl
      | tail _ hs ih => exact ih.tail ((stepC_faArgLeas hargs (held _ ih)).mp hs)
    · induction h with
      | refl => exact .refl
      | tail hb hs ih => exact ih.tail ((stepC_faArgLeas hargs (held _ hb)).mpr hs)

end Sim

/-! ## The completeness on the marshalled body -/

/-- The parallel move keeps a move whose source is no destination. -/
theorem mem_sequentialMovesAux {tmp a x : String} :
    ∀ (fuel : Nat) (ms out : List (String × LOperand)),
      sequentialMovesAux tmp fuel ms = some out → (ms.map Prod.fst).Nodup →
      (a, .reg x) ∈ ms → x ∉ ms.map Prod.fst → (a, .reg x) ∈ out
  | fuel, [], out, _, _, hm, _ => by simp at hm
  | 0, _ :: _, _, h, _, _, _ => by simp [sequentialMovesAux] at h
  | fuel + 1, m0 :: ms0, out, h, hn, hm, hx => by
      simp only [sequentialMovesAux] at h
      split at h
      · rename_i m hf
        obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
        by_cases e : m = (a, .reg x)
        · simp [e]
        · have hne : a ≠ m.1 := fun ha =>
            e (eq_of_mem_of_fst_eq hn (List.mem_of_find?_eq_some hf) hm ha.symm)
          have hs := (List.filter_sublist (p := fun m' => m'.1 != m.1)
            (l := m0 :: ms0)).map Prod.fst
          exact List.mem_cons_of_mem _ (mem_sequentialMovesAux fuel _ out' h' (hs.nodup hn)
            (List.mem_filter.mpr ⟨hm, by simpa using hne⟩) fun hx' => hx (hs.subset hx'))
      · split at h
        · cases h
        · obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have hf : ((m0 :: ms0).map fun m => (m.1, substReg m0.1 tmp m.2)).map Prod.fst
              = (m0 :: ms0).map Prod.fst := by simp
          have hx0 : x ≠ m0.1 := fun h => hx (by simp [h])
          refine List.mem_cons_of_mem _ (mem_sequentialMovesAux fuel _ out' h' (hf ▸ hn) ?_
            (hf ▸ hx))
          exact List.mem_map.mpr ⟨_, hm, by simp [substReg, hx0]⟩

/-- Every destination of the parallel move is the temporary or a destination of the pending
    moves. -/
theorem sequentialMovesAux_dst {tmp : String} :
    ∀ (fuel : Nat) (ms out : List (String × LOperand)),
      sequentialMovesAux tmp fuel ms = some out →
      ∀ m ∈ out, m.1 = tmp ∨ m.1 ∈ ms.map Prod.fst
  | fuel, [], out, h => by
      obtain rfl : out = [] := by
        cases fuel <;> simp only [sequentialMovesAux, Option.some.injEq] at h <;> exact h.symm
      simp
  | 0, _ :: _, _, h => by simp [sequentialMovesAux] at h
  | fuel + 1, m0 :: ms0, out, h => by
      simp only [sequentialMovesAux] at h
      split at h
      · rename_i m hf
        obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
        have ih := sequentialMovesAux_dst fuel _ out' h'
        have := List.mem_of_find?_eq_some hf
        grind
      · split at h
        · cases h
        · obtain ⟨out', h', rfl⟩ := Option.map_eq_some_iff.mp h
          have ih := sequentialMovesAux_dst fuel _ out' h'
          grind

/-- The destinations before the parallel move are the argument registers, in order. -/
theorem marshal_dsts_sublist : ∀ (ops : List LOperand) (rs : List String),
    (((ops.zip rs).map fun p => (p.2, p.1)).map Prod.fst).Sublist rs
  | [], rs => by simp
  | _ :: _, [] => by simp
  | _ :: ops, r :: rs => by simpa using (marshal_dsts_sublist ops rs).cons_cons r

/-- **The form of an argument move**: an operand `x` of a call that is no argument register
    has the marshalling move from `x` into its argument register. -/
theorem mem_marshalMoves {ops : List LOperand} {a x : String}
    (hm : (LOperand.reg x, a) ∈ ops.zip sysvArgRegs) (hx : x ∉ sysvArgRegs) :
    (a, LOperand.reg x) ∈ marshalMoves ops := by
  have hs := marshal_dsts_sublist ops sysvArgRegs
  have hm' : (a, LOperand.reg x) ∈ (ops.zip sysvArgRegs).map fun p => (p.2, p.1) :=
    List.mem_map.mpr ⟨_, hm, rfl⟩
  unfold marshalMoves sequentialMoves
  generalize hf : sequentialMovesAux sysvRetReg _ _ = r
  cases r with
  | none => exact hm'
  | some out =>
    exact mem_sequentialMovesAux _ _ out hf (hs.nodup (by decide)) hm' fun h => hx (hs.subset h)

/-- A marshalling move writes an argument register or the result register. -/
theorem marshalMoves_dst {ops : List LOperand} {m : String × LOperand}
    (h : m ∈ marshalMoves ops) : m.1 = sysvRetReg ∨ m.1 ∈ sysvArgRegs := by
  have hs := marshal_dsts_sublist ops sysvArgRegs
  unfold marshalMoves sequentialMoves at h
  generalize hf : sequentialMovesAux sysvRetReg _ _ = r at h
  cases r with
  | none => exact .inr (hs.subset (List.mem_map_of_mem h))
  | some out => exact (sequentialMovesAux_dst _ _ out hf m h).imp_right fun h' => hs.subset h'

/-- A write of a call sequence is a write of an argument register or of the result register,
    or the copy of the result into the destination of a call that is no out call. -/
theorem writesB_loopBodyCallLcmd {dst sym : String} {ops : List LOperand} {out : Bool}
    {z : Linstr} (hz : z ∈ loopBodyCallLcmd dst sym ops out) {x : String}
    (hw : writesB x z.li_i = true) :
    (x = dst ∧ out = false) ∨ x = sysvRetReg ∨ x ∈ sysvArgRegs := by
  unfold loopBodyCallLcmd at hz
  simp only [List.mem_append, List.mem_map, List.mem_cons] at hz
  rcases hz with ⟨⟨a, op⟩, hm, rfl⟩ | rfl | hz
  · have := marshalMoves_dst hm
    simp only [writesB, operandNamesB, List.any_cons, List.any_nil, Bool.or_false,
      Bool.and_eq_true, beq_iff_eq] at hw
    grind
  · simp [writesB] at hw
  · grind [writesB, operandNamesB]

/-- A write of a marshalled body is a write of the allocated body (`allocWritesB`) or a write
    of an argument register or of the result register, where no call is width-classed. -/
theorem writesB_expandCallShadows {B : Lcmd} {outs : List String}
    (hW : ∀ i ∈ B, ∀ ds o ss, i.li_i = .Lopn ds o ss → parseCallW o = none) {z : Linstr}
    (hz : z ∈ expandCallShadows B outs) {x : String} (hw : writesB x z.li_i = true) :
    (∃ i ∈ B, allocWritesB outs x i.li_i = true) ∨ x = sysvRetReg ∨ x ∈ sysvArgRegs := by
  obtain ⟨i, hi, hz⟩ := List.mem_flatMap.mp hz
  split at hz
  · rename_i dst o ops hio
    rw [hW i hi _ _ _ hio] at hz
    simp only at hz
    grind [writesB_loopBodyCallLcmd, allocWritesB]
  · grind [allocWritesB]

/-- The arm of `savedArgMoves` keeps the destinations of an instruction. -/
theorem writesB_savedArgMoveArm (body : Lcmd) (i : Linstr) (x : String) :
    writesB x (savedArgMoveArm body i).li_i = writesB x i.li_i := by
  unfold savedArgMoveArm
  split <;> first
    | rfl
    | (rename_i a y hi
       split <;> first
         | rfl
         | (split <;> first | rfl | simp [writesB, hi, storeIdxA?]))

/-- A name into which no instruction moves a register by `MOVQ` holds the value of no save
    slot. -/
theorem entrySaveOf?_of_noSave {body : Lcmd} {x : String}
    (h : ∀ i ∈ body, ∀ y, i.li_i ≠ .Lopn [.reg x] "MOVQ" [.reg y]) :
    entrySaveOf? body x = none := by
  cases he : entrySaveOf? body x with
  | none => rfl
  | some q =>
    unfold entrySaveOf? at he
    split at he
    · cases he
    split at he
    · split at he
      · split at he
        · rename_i d r' h5 h6
          split at he
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨⟨rfl, -⟩, -⟩, -⟩ := hc
            exact absurd rfl (h _ (List.mem_of_getElem? h6) r')
          · cases he
        · cases he
      · cases he
    · cases he

/-- **The check accepts the previous stage's image.** Let the allocated body be `P` followed
    by the epilogue `E`, and have no width-classed call. If the keys are pairwise different,
    none of them among `others`, the argument registers and the result register, none a
    cell, `P` changes no key and no frame-array name (`allocWritesB`: a key may be the array
    operand of an indexed store and the destination of an out call), `E` writes no
    frame-array name and has no call, no branch and no 64-bit move `MOV:64`, then the
    marshalled body
    `savedArgMoves (expandCallShadows (P ++ E) outs)` passes `faArgB`. -/
theorem faArgB_image {fa : List (String × String)} {others outs : List String} {P E : Lcmd}
    (hn : (fa.map Prod.fst).Nodup)
    (hW : ∀ i ∈ P, ∀ ds o ss, i.li_i = .Lopn ds o ss → parseCallW o = none)
    (hkey : ∀ x q, (x, q) ∈ fa → faB q = true ∧ cellParts? x = none ∧ x ∉ others
      ∧ x ≠ sysvRetReg ∧ x ∉ sysvArgRegs
      ∧ (∀ i ∈ P, allocWritesB outs x i.li_i = false)
      ∧ (∀ i ∈ P, allocWritesB outs q i.li_i = false)
      ∧ ∀ i ∈ E, writesB q i.li_i = false)
    (hE : expandCallShadows E outs = E)
    (hEc : ∀ i ∈ E, ∀ cc l, i.li_i ≠ .Lcond cc l)
    (hEm : ∀ i ∈ E, ∀ ds ss, i.li_i ≠ .Lopn ds "MOV:64" ss) :
    faArgB fa others (savedArgMoves (expandCallShadows (P ++ E) outs)) = true := by
  have happ : expandCallShadows (P ++ E) outs = expandCallShadows P outs ++ E := by
    conv_rhs => rw [← hE]
    simp [expandCallShadows]
  rw [happ]
  set B := expandCallShadows P outs ++ E with hB
  have harm : ∀ i ∈ E, savedArgMoveArm B i = i := by
    intro i hi
    unfold savedArgMoveArm
    grind
  have hS : savedArgMoves B = (expandCallShadows P outs).map (savedArgMoveArm B) ++ E := by
    rw [savedArgMoves]
    conv_lhs => arg 2; rw [hB]
    rw [List.map_append, List.map_congr_left harm, List.map_id']
  rw [hS]
  set P' := (expandCallShadows P outs).map (savedArgMoveArm B) with hP'
  refine faArgB_iff.mpr ⟨hn, fun x q he => ?_⟩
  obtain ⟨hq, hc, ho, hr, ha, hxP, hqP, hqE⟩ := hkey x q he
  have hwP : ∀ z ∈ P', writesB x z.li_i = false := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    rw [writesB_savedArgMoveArm, Bool.eq_false_iff]
    intro hw
    have := writesB_expandCallShadows hW hz' hw
    grind
  have hle : P'.length ≤ writeIdx (P' ++ E) x := by
    rw [writeIdx, List.findIdx_append]
    have : P'.findIdx (fun i => writesB x i.li_i) = P'.length :=
      List.findIdx_eq_length.mpr hwP
    grind
  refine ⟨hq, hc, ho, fun z hz => ?_, fun k i a' hb hm => ?_,
    fun k i cc l p hb hi hk hl => ?_⟩
  · rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      rw [writesB_savedArgMoveArm, Bool.eq_false_iff]
      intro hw
      have hq1 : q ≠ sysvRetReg ∧ q ∉ sysvArgRegs := by
        have hd : ∀ r ∈ sysvRetReg :: sysvArgRegs, faB r = false := by decide +kernel
        grind
      have := writesB_expandCallShadows hW hz' hw
      grind
    · grind
  · by_cases hk : k < P'.length
    · omega
    · rw [List.getElem?_append_right (by omega)] at hb
      exact absurd (argMove?_eq_some.mp hm).1 (hEm i (List.mem_of_getElem? hb) _ _)
  · rw [List.getElem?_append_right (by omega)] at hb
    exact absurd hi (hEc i (List.mem_of_getElem? hb) cc l)

/-- **The pass emits the address load for each argument that is a frame root.** Let the
    allocated body `B` have a call that expands to `loopBodyCallLcmd dst sym ops out`, with
    the key `x` of the frame-array name `q` as the operand of the argument register `a`,
    where `x` is no argument register, and is a general-purpose name or a name into which no
    instruction of the marshalled body moves a register by `MOVQ`. If that body passes
    `faArgB`, the pass on it has `LEA:64 a, q`. -/
theorem faArgLea_mem_image {fa : List (String × String)} {others outs : List String}
    {B : Lcmd} (hok : faArgB fa others (savedArgMoves (expandCallShadows B outs)) = true)
    {i : Linstr} (hi : i ∈ B) {dst sym : String} {ops : List LOperand} {out : Bool}
    (hexp : expandCallShadows [i] outs = loopBodyCallLcmd dst sym ops out) {a x q : String}
    (hop : (LOperand.reg x, a) ∈ ops.zip sysvArgRegs) (hx : x ∉ sysvArgRegs)
    (hkeep : gpNameB x = true ∨
      ∀ z ∈ expandCallShadows B outs, ∀ y, z.li_i ≠ .Lopn [.reg x] "MOVQ" [.reg y])
    (he : (x, q) ∈ fa) :
    (⟨0, .Lopn [.reg a] "LEA:64" [.reg q]⟩ : Linstr)
      ∈ faArgLeas fa others (savedArgMoves (expandCallShadows B outs)) := by
  let mv : Linstr := ⟨0, .Lopn [.reg a] "MOV:64" [.reg x]⟩
  have hw : withWidthTag 64 "MOV" = "MOV:64" := by decide +kernel
  have hmv : mv ∈ expandCallShadows B outs := by
    have h1 : mv ∈ expandCallShadows [i] outs := by
      rw [hexp]
      refine List.mem_append_left _ (List.mem_map.mpr ⟨_, mem_marshalMoves hop hx, ?_⟩)
      simp [mv, hw]
    simp only [expandCallShadows, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
    exact List.mem_flatMap.mpr ⟨i, hi, h1⟩
  have hsv : savedArgMoveArm (expandCallShadows B outs) mv = mv := by
    rcases hkeep with h | h
    · simp [savedArgMoveArm, mv, h]
    · simp [savedArgMoveArm, mv, entrySaveOf?_of_noSave h]
  have hmv' : mv ∈ savedArgMoves (expandCallShadows B outs) :=
    List.mem_map.mpr ⟨mv, hmv, hsv⟩
  rw [faArgLeas_of_accepted hok]
  refine List.mem_map.mpr ⟨mv, hmv', ?_⟩
  simp [faArgArm, argMove?, mv, (List.of_mem_zip hop).2, lookup_of_mem (faArgB_iff.mp hok).1 he]

/-! ## Instances -/

/-- The hypotheses of `runA_faArgLeas_regs` hold at the body `MOV:64 RDI, RBX; ret` of the
    root in `RBX`, for every frame address and memory, and the pass makes it
    `LEA:64 RDI, fa.0.1; ret`. -/
example (v : BitVec 64) (mem : AMem) (fuel : Nat) (zf : Bool) :
    let frame : String → Option (BitVec 64) := fun q => if q = "fa.0.1" then some v else none
    let body : Lcmd := [⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "RBX"]⟩, ⟨0, .Lret⟩]
    let s : LstateA := { reg := { lvm := fun _ => ⟨64, v⟩ }, mem := mem }
    let body' := faArgLeas [("RBX", "fa.0.1")] [] body
    body' = [⟨0, .Lopn [.reg "RDI"] "LEA:64" [.reg "fa.0.1"]⟩, ⟨0, .Lret⟩]
      ∧ runA frame body' fuel s zf = runA frame body fuel s zf := by
  intro frame body s body'
  have hok : faArgB [("RBX", "fa.0.1")] [] body = true := by decide +kernel
  refine ⟨?_, runA_faArgLeas_regs ?_ ?_ fuel zf ?_⟩
  · simp [body', faArgLeas_of_accepted hok, body, faArgArm, argMove?, sysvArgRegs]
  · simp [frame, sysvArgRegs]
  · simp [frame]
  · intro x q he _
    simp only [List.mem_singleton, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨v, by simp [frame], by simp [frame, s]⟩

/-- The hypotheses of `runA_faArgLeas` hold at the body `MOV:64 RDI, k.3; ret` of the root in
    the spill slot `k.3`, whose frame word at `c` holds the frame address. -/
example (c : BitVec 64) (mem : AMem) (fuel : Nat) (zf : Bool) :
    let frame : String → Option (BitVec 64) := fun q =>
      if q = "fa.0.1" then some (read64 mem c) else if q = "k.3" then some c else none
    let body : Lcmd := [⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "k.3"]⟩, ⟨0, .Lret⟩]
    let s : LstateA := { reg := { lvm := fun _ => ⟨64, 0⟩ }, mem := mem }
    faArgB [("k.3", "fa.0.1")] [] body = true
      ∧ runA frame (faArgLeas [("k.3", "fa.0.1")] [] body) fuel s zf
        = runA frame body fuel s zf := by
  intro frame body s
  refine ⟨by decide +kernel, runA_faArgLeas ?_ fuel s zf ?_ fun t _ => ?_⟩
  · simp [frame, sysvArgRegs]
  · intro x q he _
    simp only [List.mem_singleton, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨read64 mem c, by simp [frame], by simp [frame, s]⟩
  · intro x q a _ _ _ y _
    have hm : slotMov? (.Lopn [.reg "RDI"] "MOV:64" [.reg "k.3"]) = some ("RDI", "k.3") :=
      slotMov?_mov64 (by decide +kernel) (by decide +kernel)
    have htag : tagAt body 0 (.Lopn [.reg "RDI"] "MOV:64" [.reg "k.3"]) = .reg none := by
      decide +kernel
    simp only [body] at htag
    rcases ht : t.1.reg.lpc with _ | _ | n <;>
      simp [stepWrites, SepLogic.Addr.writesA, SepLogic.Addr.storeR?, SepLogic.Addr.storeA?,
        ht, body, hm, htag, frame, normA_of_caret_free]

/-- The hypotheses of `stepsC_faArgLeas` hold at a move from the root in `RBX` before a call,
    and the pass runs through the move and the call of a callee that clobbers no register. -/
example (c : CalleeSig) (ω : CallOut) (v : BitVec 64) (mem : AMem) (zf : Bool) :
    let c' : CalleeSig := { c with clob := fun _ => false }
    let frame : String → Option (BitVec 64) := fun q => if q = "fa.0.1" then some v else none
    let fa := [("RBX", "fa.0.1")]
    let body : Lcmd := [⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "RBX"]⟩,
      ⟨0, .Lcall none ("f", 0)⟩, ⟨0, .Lret⟩]
    let s : LstateA := { reg := { lvm := fun _ => ⟨64, v⟩ }, mem := mem }
    let s' : LstateA := { s with reg := (s.reg.setReg "RDI" v).nextPc }
    Relation.ReflTransGen (StepC frame fa (faArgLeas fa [] body)) (s, zf)
      (callAC c' ω mem s', ω.zf) := by
  intro c' frame fa body s s'
  have hok : faArgB fa [] body = true := by decide +kernel
  have hargs : ∀ a ∈ sysvArgRegs, frame a = none := by simp [frame, sysvArgRegs]
  have hh : RootsHeld frame fa body s := by
    intro x q he _
    simp only [fa, List.mem_singleton, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨v, by simp [frame], by simp [frame, s]⟩
  refine (stepsC_faArgLeas hargs hh fun u _ => spillKept_of_regs ?_ body u.1).mpr
    (.tail (b := (s', zf)) (.single (.inl ?_)) (.inr ?_))
  · simp [fa, frame]
  · exact (stepA_faArgLeas hargs hh zf).symm.trans
      (stepA_faArgLea hok (i := ⟨0, .Lopn [.reg "RDI"] "MOV:64" [.reg "RBX"]⟩)
        (x := "RBX") (q := "fa.0.1") rfl
        (by simp [argMove?, sysvArgRegs]) (by simp [fa]) (by simp [frame]) zf)
  · exact ⟨_, _, _, c', ω, mem, rfl, rfl, rfl, fun x _ _ _ => by simp [clobN, c'],
      fun _ _ _ _ _ _ _ => rfl⟩

/-- The hypotheses of `rootsHeld_callAC` hold at every callee that clobbers no register and
    keeps the memory. -/
example (c : CalleeSig) (ω : CallOut) {frame : String → Option (BitVec 64)}
    {fa : List (String × String)} {body : Lcmd} {s : LstateA}
    (hh : RootsHeld frame fa body s) :
    RootsHeld frame fa body (callAC { c with clob := fun _ => false } ω s.mem s) :=
  rootsHeld_callAC _ ω hh (fun x _ _ _ => by simp [clobN]) fun _ _ _ _ _ _ _ => rfl

/-- The hypotheses of `faArgB_image` and of `faArgLea_mem_image` hold at a store into the
    root in `RBX` followed by an out call of `f` on the root, before the restore of `RBX` and
    the return. The store and the call both name `RBX` as their destination operand. -/
example :
    let P : Lcmd := [⟨0, .Lopn [.reg "RBX"] "STOREIDX" [.arrIdx "R14" "R12" 8, .reg "R13"]⟩,
      ⟨0, .Lopn [.reg "RBX"] "CALL:f" [.reg "RBX"]⟩]
    let E : Lcmd := [⟨0, .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"]⟩, ⟨0, .Lret⟩]
    let B := savedArgMoves (expandCallShadows (P ++ E) ["f"])
    faArgB [("RBX", "fa.0.1")] ["RBP"] B = true
      ∧ (⟨0, .Lopn [.reg "RDI"] "LEA:64" [.reg "fa.0.1"]⟩ : Linstr)
          ∈ faArgLeas [("RBX", "fa.0.1")] ["RBP"] B := by
  intro P E B
  have hok : faArgB [("RBX", "fa.0.1")] ["RBP"] B = true := by
    refine faArgB_image (by simp) ?_ ?_ (by decide +kernel) (by simp [E]) (by simp [E])
    · have h1 : parseCallW "CALL:f" = none := by decide +kernel
      have h2 : parseCallW "STOREIDX" = none := by decide +kernel
      simp [P, h1, h2]
    · intro x q he
      simp only [List.mem_singleton, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      decide +kernel
  refine ⟨hok, faArgLea_mem_image hok (i := ⟨0, .Lopn [.reg "RBX"] "CALL:f" [.reg "RBX"]⟩)
    (dst := "RBX") (sym := "f") (ops := [.reg "RBX"]) (out := true) (x := "RBX")
    (by simp [P]) (by decide +kernel) (by simp [sysvArgRegs]) (by simp [sysvArgRegs])
    (.inl (by decide +kernel)) (by simp)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArgLea
