/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherMemOps
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

/-!
# Constant-index folding of register-indexed loads and stores

`Com.toLprogPhysAbi` exports a table read at an index bound in the body as the
register-indexed form `LOADIDX [.arrIdx B x 8]`, rendered
`movq (%B,%x,8), %d`, even when `x` holds a literal. This module gives an opt-in
`Lprog → Lprog` pass that rewrites such a load (and the matching `STOREIDX`) to
the compile-time-displacement form `LOAD [.arr B (8·k)]` (`STORE [.arr B (8·k), v]`)
whenever a forward analysis knows that `x` holds `k`.

## The machine model

The value semantics is `Jasmin.runBlock` over the `JInstr 64` gather, the model
`MachineConstantTime.blockLeak` is stated over. `gatherPrinted` is
`GatherImmForms.gatherJBlock6` with one arm changed: a register rebind
`SHL:0:64 [d] [s]` with `d ≠ s` lowers to `mov d, s`, which is what
`LprogAsmPrinter` prints for it. `gatherJBlock6` lowers the same instruction to
`shl d, $0`, which keeps the old value of `d`; the front emits one such rebind per
scalar binding, and the constant index reaches the load register through one.

## The analysis

`KEnv` maps register names to known 64-bit values. `stepK` updates it across one
gathered instruction: an immediate `mov` records its constant, a `mov` from one of
the sixteen general-purpose registers or from a spill or ABI-save slot (`k.N`,
`qsave.X`) copies a known value (a `mov` from a `mem.<base>.<off>` name forgets its
destination), a memory load forgets its destination, a memory store keeps every
register entry, and every other instruction forgets the registers it writes
(`MachineConstantTime.dstRegs`). A write to memory based at `RSP` (`writesFrame`)
also forgets every slot name, since a `MOVQ` to a slot gathers to such a store.
`foldCore` threads the environment through the body, reading the gathered block of
each instruction. Besides the indexed accesses, the fold rewrites a `MOV:64` copy of a
known slot value into a general-purpose register as the immediate move of that value,
which the dead-move elimination can then remove.

The fold is decided per array. `runtimeBases` collects the base names of the
register-indexed accesses the analysis cannot rewrite, and `constIndexFoldBody` leaves
every register-indexed access through one of those bases unchanged: an array the body
indexes at run time keeps the register-indexed form at its literal indices too, and an
array accessed at known indices only is accessed at constant displacements.

## Main results

* `evalInstr_loadMemIdx_const`, `evalInstr_storeMemIdx_const`: an indexed access
  whose index register holds `v` is the direct access at displacement
  `scale · v`.
* `gatherPrinted_constIndexFoldBody`: the folded body gathers whenever the input
  does, and its block runs to the same machine state from every initial state.
* `constIndexFoldBody_lcmdDirect`: if every register-indexed instruction of the
  body is foldable (`Covers`) and the frame guard holds, the folded body is
  `lcmdDirect`; `gatherPrinted_constIndexFoldBody_constant_time` then gives the
  machine constant-time property of its gathered block.
* `spellLprog`: the printable spelling of the folded forms as the `mem.<B>.<off>`
  `MOVQ` operands that `LprogAsmPrinter` and `LprogBytes` render and encode.
* `runBlock_movImm_loadMemIdx`, `runBlock_movImm_storeMemIdx`: after `mov x, $k`,
  the access `(%B,%x,8)` is the access at displacement `8·k` from `B`.
* `spellMemInstr`, `lowerMemOp_spellMemInstr_load`, `lowerMemOp_spellMemInstr_store`:
  the spelling as the array-ABI moves `LOAD:64`/`STORE:64`, which the memory arm of
  the gather lowers to the same `loadMem`/`storeMem` as the folded forms.
* `dropDeadImmBody`, `gatherPrinted_dropDeadImmBody`: removal of an immediate move
  to a register that is overwritten before it is read, with block agreement;
  `gatherPrinted_dropDeadImm_constIndexFold` composes it with the fold.
* `foldIndexedLprog`: fold, dead-move removal and array-ABI spelling of every
  function, the stage `LprogOptPipeline.renderOwned` applies before printing.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (lowerCov6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 qsaveBytesFor)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave isGpName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (linstrRDirect lcmdDirect lcmdDirect_iff lowerCov6_direct mapM_flatten_direct)

/-! ## 1. The gather with printed register rebinds -/

/-- Lower one instruction: a register rebind `SHL:0:64 [d] [s]` between two
    register names is `mov d, s` (nothing when `d = s`); every other instruction
    is lowered by `lowerCov6`. -/
def lowerPrinted (frame spillW qsaveB : Nat) : LinstrR → Option (List (JInstr 64))
  | .Lopn [.reg d] "SHL:0:64" [.reg s] =>
      if isSpillOrQsave d || isSpillOrQsave s then
        lowerCov6 frame spillW (.Lopn [.reg d] "SHL:0:64" [.reg s]) qsaveB
      else if d = s then some [] else some [.mov d (.reg s)]
  | i => lowerCov6 frame spillW i qsaveB

/-- The frame parameters `gatherJBlock6` reads off a body: frame size, spill
    width, qsave block size. -/
def bodyParams (body : Lcmd) : Nat × Nat × Nat :=
  (frameSize body, if bodyIsU64 body then 64 else 32, qsaveBytesFor body)

/-- `gatherJBlock6` with `lowerPrinted` in place of `lowerCov6`. -/
def gatherPrinted (body : Lcmd) : Option (List (JInstr 64)) :=
  let p := bodyParams body
  ((body.filter (fun i => !isLret i)).mapM
    (fun i => lowerPrinted p.1 p.2.1 p.2.2 i.li_i)).map List.flatten

theorem lowerPrinted_direct {frame spillW qsaveB : Nat} {i : LinstrR}
    {js : List (JInstr 64)} (hi : linstrRDirect i = true)
    (h : lowerPrinted frame spillW qsaveB i = some js) : allDirect js = true := by
  unfold lowerPrinted at h
  split at h
  · split at h
    · exact lowerCov6_direct hi h
    · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact AllocCTPreservation.allDirect_of_forall
          (by simp [MachineConstantTime.IsDirect])
  · exact lowerCov6_direct hi h

/-- The printed gather of an index-free body is `allDirect`. -/
theorem gatherPrinted_allDirect {body : Lcmd} {g : List (JInstr 64)}
    (hd : lcmdDirect body = true) (h : gatherPrinted body = some g) :
    allDirect g = true := by
  simp only [gatherPrinted, Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, rfl⟩ := h
  refine mapM_flatten_direct (f := fun i => lowerPrinted _ _ _ i.li_i) ?_ _ ?_ ls hls
  · intro i hi js hj
    exact lowerPrinted_direct hi hj
  · intro i hi
    exact (lcmdDirect_iff body).mp hd i (List.mem_of_mem_filter hi)

/-! ## 2. The lowered forms of the indexed and the direct accesses -/

theorem lowerPrinted_loadIdx (frame spillW qsaveB : Nat) (d B x : String) (sc : Nat) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "LOADIDX" [.arrIdx B x sc])
      = some [.loadMemIdx d B x sc] := rfl

theorem lowerPrinted_load (frame spillW qsaveB : Nat) (d B : String) (off : Nat) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "LOAD" [.arr B off])
      = some [.loadMem d B off] := rfl

theorem lowerPrinted_storeIdx (frame spillW qsaveB : Nat) (d B x : String) (sc : Nat)
    (v : LOperand) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, v])
      = some [.storeMemIdx B x sc (LoweringExtended.lowerJOperand v)] := rfl

theorem lowerPrinted_store (frame spillW qsaveB : Nat) (d B : String) (off : Nat)
    (v : LOperand) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "STORE" [.arr B off, v])
      = some [.storeMem B off (LoweringExtended.lowerJOperand v)] := rfl

theorem lowerPrinted_movReg (frame spillW qsaveB : Nat) (d x : String) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "MOV:64" [.reg x])
      = some [.mov d (.reg x)] := rfl

theorem lowerPrinted_movImm (frame spillW qsaveB : Nat) (d : String) (k : Nat) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "MOV:64" [.imm k])
      = some [.mov d (.imm k)] := rfl

/-! ## 3. One access at a known index -/

/-- A register move from a name holding `v` is the immediate move of `v`. -/
theorem evalInstr_movImm_const (s : JState 64) (d x : String) {v : BitVec 64}
    (h : s.get x = v) :
    evalInstr s (.mov d (.imm v.toNat)) = evalInstr s (.mov d (.reg x)) := by
  have h' : s.regs x = v := h
  simp [evalInstr, JOperand.eval, h']

/-- An indexed load whose index register holds `v` is the direct load at
    displacement `sc · v`. -/
theorem evalInstr_loadMemIdx_const (s : JState 64) (d B x : String) (sc : Nat)
    {v : BitVec 64} (h : s.get x = v) :
    evalInstr s (.loadMemIdx d B x sc) = evalInstr s (.loadMem d B ((sc * v.toNat : Nat) : Int)) := by
  simp only [evalInstr, JState.loadIdx, h, Nat.cast_mul]

/-- An indexed store whose index register holds `v` is the direct store at
    displacement `sc · v`. -/
theorem evalInstr_storeMemIdx_const (s : JState 64) (B x : String) (sc : Nat)
    (src : JOperand) {v : BitVec 64} (h : s.get x = v) :
    evalInstr s (.storeMemIdx B x sc src)
      = evalInstr s (.storeMem B ((sc * v.toNat : Nat) : Int) src) := by
  simp only [evalInstr, JState.storeIdx, h, Nat.cast_mul]

/-! ## 4. The known-register analysis -/

/-- Registers with a known 64-bit value; the first entry for a name wins. -/
abbrev KEnv : Type := List (String × BitVec 64)

/-- The known value of register `r`. -/
def KEnv.find : KEnv → String → Option (BitVec 64)
  | [], _ => none
  | (a, v) :: t, r => if a = r then some v else KEnv.find t r

/-- Forget register `r`. -/
def KEnv.kill (env : KEnv) (r : String) : KEnv := env.filter (fun p => !(p.1 == r))

/-- Every recorded value is the value of its register in `s`. -/
def KEnv.Holds (s : JState 64) (env : KEnv) : Prop :=
  ∀ r v, env.find r = some v → s.get r = v

theorem KEnv.find_kill (env : KEnv) (d r : String) :
    (env.kill d).find r = if d = r then none else env.find r := by
  induction env with
  | nil => simp [KEnv.kill, KEnv.find]
  | cons p t ih =>
      obtain ⟨a, v⟩ := p
      by_cases had : a = d
      · subst had
        have hk : KEnv.kill ((a, v) :: t) a = KEnv.kill t a := by
          simp [KEnv.kill]
        rw [hk, ih]
        by_cases har : a = r <;> simp [KEnv.find, har]
      · have hk : KEnv.kill ((a, v) :: t) d = (a, v) :: KEnv.kill t d := by
          simp [KEnv.kill, had]
        rw [hk]
        simp only [KEnv.find]
        rw [ih]
        by_cases hdr : d = r
        · subst hdr; simp [had]
        · simp [hdr]

theorem KEnv.Holds.nil (s : JState 64) : KEnv.Holds s [] := by
  intro r v h; simp [KEnv.find] at h

theorem JState.get_setReg' (s : JState 64) (d r : String) (w : BitVec 64) :
    (s.setReg d w).get r = if r = d then w else s.get r := by
  simp [JState.setReg]

theorem KEnv.Holds.setReg_kill {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (d : String) (w : BitVec 64) : KEnv.Holds (s.setReg d w) (env.kill d) := by
  intro r v hr
  rw [KEnv.find_kill] at hr
  rw [JState.get_setReg']
  by_cases hdr : d = r
  · simp [hdr] at hr
  · rw [ite_eq_right hdr] at hr
    rw [ite_eq_right (Ne.symm hdr)]
    exact h r v hr

theorem KEnv.Holds.setReg_cons {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (d : String) (w : BitVec 64) : KEnv.Holds (s.setReg d w) ((d, w) :: env.kill d) := by
  intro r v hr
  simp only [KEnv.find] at hr
  by_cases hdr : d = r
  · subst hdr
    simp only [ite_true, Option.some.injEq] at hr
    subst hr
    simp [JState.setReg]
  · rw [ite_eq_right hdr] at hr
    exact h.setReg_kill d w r v hr

/-- Forget every register of `ds`. -/
def KEnv.killAll (env : KEnv) (ds : List String) : KEnv := env.filter (fun p => !ds.contains p.1)

theorem KEnv.find_killAll {env : KEnv} {ds : List String} {r : String} {v : BitVec 64}
    (h : (env.killAll ds).find r = some v) : env.find r = some v ∧ r ∉ ds := by
  induction env with
  | nil => simp [KEnv.killAll, KEnv.find] at h
  | cons p t ih =>
      obtain ⟨a, w⟩ := p
      by_cases ha : a ∈ ds
      · have hk : KEnv.killAll ((a, w) :: t) ds = KEnv.killAll t ds := by
          simp [KEnv.killAll, ha]
        rw [hk] at h
        obtain ⟨h1, h2⟩ := ih h
        refine ⟨?_, h2⟩
        have har : a ≠ r := fun he => h2 (he ▸ ha)
        simp [KEnv.find, har, h1]
      · have hk : KEnv.killAll ((a, w) :: t) ds = (a, w) :: KEnv.killAll t ds := by
          simp [KEnv.killAll, ha]
        rw [hk] at h
        simp only [KEnv.find] at h ⊢
        by_cases har : a = r
        · subst har
          simp only [ite_true] at h ⊢
          exact ⟨h, ha⟩
        · simp only [har, ite_false] at h ⊢
          exact ih h

/-- Forgetting the registers an instruction writes keeps the environment true across
    the instruction. -/
theorem KEnv.Holds.evalInstr_killAll {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (i : JInstr 64) :
    KEnv.Holds (evalInstr s i) (env.killAll (MachineConstantTime.dstRegs i)) := by
  intro r v hr
  obtain ⟨h1, h2⟩ := KEnv.find_killAll hr
  rw [MachineConstantTime.evalInstr_get_of_not_dst _ _ _ h2]
  exact h r v h1

/-- Forget every spill (`k.N`) and ABI-save (`qsave.X`) name when `b` holds. -/
def KEnv.killFrame (b : Bool) (env : KEnv) : KEnv :=
  if b then env.filter (fun p => !isSpillOrQsave p.1) else env

theorem KEnv.find_filter_name (f : String → Bool) (env : KEnv) (r : String) :
    KEnv.find (env.filter (fun p => f p.1)) r = if f r then env.find r else none := by
  induction env with
  | nil => simp [KEnv.find]
  | cons p t ih =>
      obtain ⟨a, w⟩ := p
      by_cases har : a = r
      · subst har
        by_cases ha : f a = true <;> simp [KEnv.find, ha, ih]
      · by_cases ha : f a = true <;> simp [KEnv.find, ha, har, ih]

/-- Forgetting the frame slots keeps the environment true. -/
theorem KEnv.Holds.killFrame {s : JState 64} {env : KEnv} (h : KEnv.Holds s env) (b : Bool) :
    KEnv.Holds s (env.killFrame b) := by
  intro r v hr
  cases b with
  | false => exact h r v hr
  | true =>
      simp only [KEnv.killFrame, ite_true] at hr
      rw [KEnv.find_filter_name (fun n => !isSpillOrQsave n)] at hr
      split at hr
      · exact h r v hr
      · simp at hr

/-- The instruction writes memory addressed from `RSP`, the base of the spill and
    ABI-save slots: a store, an indexed store or a memory add at base `RSP`, or a
    symbol load that rebinds the `RSP` memory bank. -/
def writesFrame : JInstr 64 → Bool
  | .storeMem B _ _ => B == "RSP"
  | .storeMemIdx B _ _ _ => B == "RSP"
  | .addToMem B _ _ => B == "RSP"
  | .loadSym d _ => d == "RSP"
  | _ => false

/-- The analysis step across one gathered instruction. A spill or ABI-save name is
    a register name of the gather's state when an instruction names it directly and
    the memory word `off(%rsp)` when a `MOVQ` moves it; the step copies a known value
    from either kind of name and forgets every slot name at a write to memory based
    at `RSP`. -/
def stepK (env : KEnv) : JInstr 64 → KEnv
  | .mov d (.imm k) => (d, BitVec.ofNat 64 k) :: env.kill d
  | .mov d (.reg x) =>
      if isGpName x || isSpillOrQsave x then
        match env.find x with
        | some v => (d, v) :: env.kill d
        | none => env.kill d
      else env.kill d
  | .loadMem d _ _ => env.kill d
  | .loadMemIdx d _ _ _ => env.kill d
  | .storeMem B _ _ => env.killFrame (B == "RSP")
  | .storeMemIdx B _ _ _ => env.killFrame (B == "RSP")
  | i => (env.killAll (MachineConstantTime.dstRegs i)).killFrame (writesFrame i)

/-- The analysis step across a gathered block. -/
def stepKs (env : KEnv) (js : List (JInstr 64)) : KEnv := js.foldl stepK env

theorem KEnv.Holds.stepK {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (i : JInstr 64) : KEnv.Holds (evalInstr s i) (ConstIndexFold.stepK env i) := by
  cases i with
  | mov d src =>
      cases src with
      | imm k => exact h.setReg_cons d _
      | reg x =>
          simp only [ConstIndexFold.stepK, evalInstr]
          split
          · cases hx : env.find x with
            | none => exact h.setReg_kill d _
            | some v =>
                have hv : (JOperand.reg x).eval s = v := h x v hx
                rw [hv]
                exact h.setReg_cons d v
          · exact h.setReg_kill d _
  | loadMem d _ _ => exact h.setReg_kill d _
  | loadMemIdx d _ _ _ => exact h.setReg_kill d _
  | storeMem B off src =>
      have h' : KEnv.Holds (evalInstr s (.storeMem B off src)) env := fun r v hr => h r v hr
      exact h'.killFrame _
  | storeMemIdx B x sc src =>
      have h' : KEnv.Holds (evalInstr s (.storeMemIdx B x sc src)) env :=
        fun r v hr => h r v hr
      exact h'.killFrame _
  | _ => exact (h.evalInstr_killAll _).killFrame _

theorem runBlock_append' (s : JState 64) (l₁ l₂ : List (JInstr 64)) :
    runBlock s (l₁ ++ l₂) = runBlock (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

theorem KEnv.Holds.stepKs {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (js : List (JInstr 64)) : KEnv.Holds (runBlock s js) (ConstIndexFold.stepKs env js) := by
  induction js generalizing s env with
  | nil => exact h
  | cons i is ih => exact ih (h.stepK i)

/-! ## 5. The fold -/

/-- The fold applies to a 64-bit (`scale = 8`) access through a tabulated GP base
    whose displacement fits a signed 32-bit field. -/
def foldOK (B : String) (sc : Nat) (v : BitVec 64) : Bool :=
  sc == 8 && isGpName B && decide (sc * v.toNat < 2 ^ 31)

/-- The direct form of an indexed load or store whose index register is known
    in `env`, and the immediate move of a known value below `2 ^ 31` copied by
    `MOV:64` from a slot into a general-purpose register; `none` for every other
    instruction. -/
def foldTarget? (env : KEnv) : LinstrR → Option LinstrR
  | .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc] =>
      match env.find x with
      | some v =>
          if foldOK B sc v then some (.Lopn [.reg d] "LOAD" [.arr B (sc * v.toNat)])
          else none
      | none => none
  | .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn] =>
      match env.find x with
      | some v =>
          if foldOK B sc v then
            some (.Lopn [.reg d] "STORE" [.arr B (sc * v.toNat), .reg vn])
          else none
      | none => none
  | .Lopn [.reg d] "MOV:64" [.reg x] =>
      match env.find x with
      | some v =>
          if isGpName d && isSpillOrQsave x && decide (v.toNat < 2 ^ 31) then
            some (.Lopn [.reg d] "MOV:64" [.imm v.toNat])
          else none
      | none => none
  | _ => none

/-- The base names of the register-indexed operands of an `Lopn`; no name for any other
    instruction. -/
def idxBases : LinstrR → List String
  | .Lopn dsts _ srcs => (dsts ++ srcs).filterMap fun o =>
      match o with
      | .arrIdx b _ _ => some b
      | _ => none
  | _ => []

/-- The instruction has a register-indexed operand whose base is a name of `ex`. -/
def skipB (ex : List String) (i : LinstrR) : Bool := (idxBases i).any ex.contains

/-- Rewrite one instruction under `env`: the instruction itself when it accesses an array
    of `ex` at a register index (`skipB`), and its direct form `foldTarget?` otherwise. -/
def foldInstr (ex : List String) (env : KEnv) (i : LinstrR) : LinstrR :=
  if skipB ex i then i else (foldTarget? env i).getD i

/-- With no excluded base, `foldInstr` is the rewrite `foldTarget?`. -/
theorem foldInstr_nil (env : KEnv) (i : LinstrR) :
    foldInstr [] env i = (foldTarget? env i).getD i := by
  simp [foldInstr, skipB]

/-- The register names a destination operand names: a plain register, and the base
    and index of a SIB element. -/
def dstOpNames : LOperand → List String
  | .reg r => [r]
  | .arrIdx b x _ => [b, x]
  | _ => []

/-- The environment after instruction `i`: the analysis step across its gathered
    block; after an `Lopn` the gather does not lower, the environment without the
    names of its destination operands; the empty environment after a return or any
    other instruction the gather does not lower. -/
def nextEnv (p : Nat × Nat × Nat) (env : KEnv) (i : Linstr) : KEnv :=
  if isLret i then []
  else
    match lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
    | some js => stepKs env js
    | none =>
        match i.li_i with
        | .Lopn d _ _ => env.killAll (d.flatMap dstOpNames)
        | _ => []

/-- The fold over a body at frame parameters `p`, from environment `env`, leaving the
    register-indexed accesses of the arrays `ex` unchanged. -/
def foldCore (p : Nat × Nat × Nat) (ex : List String) : KEnv → Lcmd → Lcmd
  | _, [] => []
  | env, i :: is =>
      { i with li_i := foldInstr ex env i.li_i } :: foldCore p ex (nextEnv p env i) is

/-- The tail-recursive image of `foldCore`, accumulating in reverse. -/
def foldCoreTR (p : Nat × Nat × Nat) (ex : List String) (acc : Lcmd) : KEnv → Lcmd → Lcmd
  | _, [] => acc.reverse
  | env, i :: is =>
      foldCoreTR p ex ({ i with li_i := foldInstr ex env i.li_i } :: acc) (nextEnv p env i) is

theorem foldCoreTR_eq (p : Nat × Nat × Nat) (ex : List String) (acc : Lcmd) (env : KEnv)
    (body : Lcmd) : foldCoreTR p ex acc env body = acc.reverse ++ foldCore p ex env body := by
  induction body generalizing acc env with
  | nil => simp [foldCoreTR, foldCore]
  | cons i is ih => simp [foldCoreTR, foldCore, ih]

/-- `foldCore` from the empty accumulator, the form the compiler runs. -/
def foldCoreFast (p : Nat × Nat × Nat) (ex : List String) (env : KEnv) (body : Lcmd) : Lcmd :=
  foldCoreTR p ex [] env body

/-- Compiled code runs `foldCore` through its tail-recursive image, so a body of
    tens of thousands of instructions does not exhaust the stack. -/
@[csimp] theorem foldCore_eq_fast : @foldCore = @foldCoreFast := by
  funext p ex env body
  simp [foldCoreFast, foldCoreTR_eq]

/-- **The arrays a body indexes at run time**: from `acc`, the base names of the
    register-indexed operands of the instructions that `foldTarget?` does not rewrite
    under the environment reaching them, each name once. The walk is tail-recursive. -/
def runtimeBases (p : Nat × Nat × Nat) (acc : List String) : KEnv → Lcmd → List String
  | _, [] => acc
  | env, i :: is =>
      runtimeBases p
        (if (foldTarget? env i.li_i).isSome then acc
          else (idxBases i.li_i).foldl (fun a b => a.insert b) acc)
        (nextEnv p env i) is

/-- The fold of a body: `foldCore` at the body's own frame parameters, kept only
    when the folded body has the same frame parameters. The fold leaves every
    register-indexed access of an array that the body also indexes at run time
    (`runtimeBases`) unchanged, so an array is accessed either at constant displacements
    only or through register indices only. -/
def constIndexFoldBody (body : Lcmd) : Lcmd :=
  let b' := foldCore (bodyParams body) (runtimeBases (bodyParams body) [] [] body) [] body
  if bodyParams b' = bodyParams body then b' else body

/-- The fold applied to every function of a program. -/
def constIndexFold (lp : Lprog) : Lprog :=
  let fs := lp.lp_funcs.map
    (fun f => (f.1, { f.2 with lfd_body := constIndexFoldBody f.2.lfd_body }))
  { lp with lp_funcs := fs }

/-- Every register-indexed instruction of the body is folded: each instruction is
    index-free or has a direct form under the environment reaching it. -/
def covers (p : Nat × Nat × Nat) : KEnv → Lcmd → Bool
  | _, [] => true
  | env, i :: is =>
      (linstrRDirect i.li_i || (foldTarget? env i.li_i).isSome) && covers p (nextEnv p env i) is

/-- An index-free instruction has no register-indexed base. -/
theorem idxBases_of_direct {i : LinstrR} (h : linstrRDirect i = true) : idxBases i = [] := by
  cases i with
  | Lopn dsts _ srcs =>
      simp only [linstrRDirect, Bool.and_eq_true, List.all_eq_true] at h
      simp only [idxBases, List.filterMap_eq_nil_iff, List.mem_append]
      intro o ho
      have := ho.elim (h.1 o) (h.2 o)
      cases o <;> simp_all [AllocCTPreservation.isIndexed]
  | _ => rfl

/-- On a body every register-indexed instruction of which is folded, the walk
    `runtimeBases` adds no name. -/
theorem runtimeBases_of_covers (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (acc : List String) (env : KEnv), covers p env body = true →
      runtimeBases p acc env body = acc := by
  intro body
  induction body with
  | nil => intro _ _ _; rfl
  | cons i is ih =>
      intro acc env h
      simp only [covers, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hi, hrest⟩ := h
      have hacc : (if (foldTarget? env i.li_i).isSome then acc
          else (idxBases i.li_i).foldl (fun a b => a.insert b) acc) = acc := by
        split
        · rfl
        · rcases hi with hi | hi
          · rw [idxBases_of_direct hi]; rfl
          · simp_all
      simp only [runtimeBases, hacc]
      exact ih acc _ hrest

theorem foldTarget?_spec {env : KEnv} {i i' : LinstrR} (h : foldTarget? env i = some i') :
    (∃ d B x sc v, i = .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc]
        ∧ i' = .Lopn [.reg d] "LOAD" [.arr B (sc * v.toNat)] ∧ env.find x = some v)
    ∨ (∃ d B x sc vn v, i = .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn]
        ∧ i' = .Lopn [.reg d] "STORE" [.arr B (sc * v.toNat), .reg vn]
        ∧ env.find x = some v)
    ∨ (∃ d x v, i = .Lopn [.reg d] "MOV:64" [.reg x]
        ∧ i' = .Lopn [.reg d] "MOV:64" [.imm v.toNat] ∧ env.find x = some v) := by
  unfold foldTarget? at h
  split at h
  · left
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, _, _, _, _, rfl, h.symm, by assumption⟩
      · simp at h
    · simp at h
  · right; left
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, _, _, _, _, _, rfl, h.symm, by assumption⟩
      · simp at h
    · simp at h
  · right; right
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, _, _, rfl, h.symm, by assumption⟩
      · simp at h
    · simp at h
  · simp at h

theorem foldTarget?_direct {env : KEnv} {i i' : LinstrR} (h : foldTarget? env i = some i') :
    linstrRDirect i' = true := by
  rcases foldTarget?_spec h with ⟨_, _, _, _, _, -, rfl, -⟩ | ⟨_, _, _, _, _, _, -, rfl, -⟩ |
      ⟨_, _, _, -, rfl, -⟩ <;>
    simp [linstrRDirect, AllocCTPreservation.isIndexed]

theorem isLret_foldInstr (ex : List String) (env : KEnv) (i : Linstr) :
    isLret { i with li_i := foldInstr ex env i.li_i } = isLret i := by
  unfold foldInstr
  split
  · rfl
  cases h : foldTarget? env i.li_i with
  | none => rfl
  | some i' =>
      rcases foldTarget?_spec h with ⟨_, _, _, _, _, hi, rfl, -⟩ | ⟨_, _, _, _, _, _, hi, rfl, -⟩ |
          ⟨_, _, _, hi, rfl, -⟩ <;>
        simp [isLret, hi]

/-- A folded instruction lowers to a block that runs like the original block from
    every state the environment describes. -/
theorem foldInstr_lower (p : Nat × Nat × Nat) {ex : List String} {env : KEnv} {i : LinstrR}
    {js : List (JInstr 64)} (h : lowerPrinted p.1 p.2.1 p.2.2 i = some js) :
    ∃ js', lowerPrinted p.1 p.2.1 p.2.2 (foldInstr ex env i) = some js'
      ∧ ∀ s, KEnv.Holds s env → runBlock s js' = runBlock s js := by
  unfold foldInstr
  split
  · exact ⟨js, h, fun _ _ => rfl⟩
  cases hf : foldTarget? env i with
  | none => exact ⟨js, h, fun _ _ => rfl⟩
  | some i' =>
      rcases foldTarget?_spec hf with
        ⟨d, B, x, sc, v, rfl, rfl, hx⟩ | ⟨d, B, x, sc, vn, v, rfl, rfl, hx⟩ |
          ⟨d, x, v, rfl, rfl, hx⟩
      · rw [lowerPrinted_loadIdx] at h
        cases h
        refine ⟨_, lowerPrinted_load _ _ _ d B _, fun s hs => ?_⟩
        simp only [runBlock_cons, runBlock_nil]
        exact (evalInstr_loadMemIdx_const s d B x sc (hs x v hx)).symm
      · rw [lowerPrinted_storeIdx] at h
        cases h
        refine ⟨_, lowerPrinted_store _ _ _ d B _ _, fun s hs => ?_⟩
        simp only [runBlock_cons, runBlock_nil]
        exact (evalInstr_storeMemIdx_const s B x sc _ (hs x v hx)).symm
      · rw [lowerPrinted_movReg] at h
        cases h
        refine ⟨_, lowerPrinted_movImm _ _ _ d _, fun s hs => ?_⟩
        simp only [runBlock_cons, runBlock_nil]
        exact evalInstr_movImm_const s d x (hs x v hx)

/-- The lowering applied to the non-return instructions of a body. -/
abbrev gatherList (p : Nat × Nat × Nat) (body : Lcmd) : Option (List (List (JInstr 64))) :=
  (body.filter (fun i => !isLret i)).mapM (fun i => lowerPrinted p.1 p.2.1 p.2.2 i.li_i)

/-- **Block agreement at fixed frame parameters.** If the body gathers, the folded
    body gathers, and from every state the environment describes the two blocks
    run to the same machine state. -/
theorem foldCore_gather (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (body : Lcmd) (env : KEnv) (s : JState 64) (ls : List (List (JInstr 64))),
      KEnv.Holds s env → gatherList p body = some ls →
      ∃ ls', gatherList p (foldCore p ex env body) = some ls'
        ∧ runBlock s ls'.flatten = runBlock s ls.flatten := by
  intro body
  induction body with
  | nil =>
      intro env s ls _ h
      refine ⟨ls, h, rfl⟩
  | cons i is ih =>
      intro env s ls hs h
      by_cases hr : isLret i = true
      · have hr' : isLret { i with li_i := foldInstr ex env i.li_i } = true := by
          rw [isLret_foldInstr]; exact hr
        have h' : gatherList p is = some ls := by
          simpa [gatherList, List.filter_cons, hr] using h
        obtain ⟨ls', h1, h2⟩ := ih (nextEnv p env i) s ls (by
          simp only [nextEnv, hr, ite_true]; exact KEnv.Holds.nil s) h'
        refine ⟨ls', ?_, h2⟩
        simpa [gatherList, foldCore, List.filter_cons, hr'] using h1
      · have hr' : isLret { i with li_i := foldInstr ex env i.li_i } = false := by
          rw [isLret_foldInstr]; simpa using hr
        have hr0 : isLret i = false := by simpa using hr
        simp only [gatherList, List.filter_cons, hr0, Bool.not_false, ite_true,
          List.mapM_cons] at h
        cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
        | none => simp [hi] at h
        | some js =>
            cases hrest : gatherList p is with
            | none => simp [gatherList, hi] at h hrest; simp [hrest] at h
            | some rest =>
                simp only [gatherList] at hrest
                simp only [hi, hrest, Option.bind_eq_bind, Option.bind_some,
                  Option.pure_def, Option.some.injEq] at h
                subst h
                obtain ⟨js', hj', hrun⟩ := foldInstr_lower p (ex := ex) (env := env) hi
                have henv : nextEnv p env i = stepKs env js := by
                  simp [nextEnv, hr0, hi]
                obtain ⟨rest', h1, h2⟩ :=
                  ih (nextEnv p env i) (runBlock s js) rest
                    (by rw [henv]; exact hs.stepKs js) hrest
                refine ⟨js' :: rest', ?_, ?_⟩
                · simp only [gatherList] at h1
                  simp only [gatherList, foldCore, List.filter_cons, hr', Bool.not_false,
                    ite_true, List.mapM_cons, hj', h1, Option.bind_eq_bind,
                    Option.bind_some, Option.pure_def]
                · simp only [List.flatten_cons, runBlock_append', hrun s hs, h2]

theorem foldCore_lcmdDirect (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (env : KEnv), covers p env body = true →
      lcmdDirect (foldCore p [] env body) = true := by
  intro body
  induction body with
  | nil => intro _ _; rfl
  | cons i is ih =>
      intro env h
      simp only [covers, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hi, hrest⟩ := h
      have hd : linstrRDirect (foldInstr [] env i.li_i) = true := by
        rw [foldInstr_nil]
        cases hf : foldTarget? env i.li_i with
        | none =>
            rcases hi with hi | hi
            · exact hi
            · simp [hf] at hi
        | some i' => exact foldTarget?_direct hf
      have := ih _ hrest
      simp only [lcmdDirect, foldCore, List.all_cons, Bool.and_eq_true] at this ⊢
      exact ⟨hd, this⟩

/-! ## 6. The fold of a body -/

/-- **Semantic agreement.** If a body gathers under `gatherPrinted`, its fold
    gathers, and the two blocks run to the same machine state from every initial
    state. -/
theorem gatherPrinted_constIndexFoldBody {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) :
    ∃ g', gatherPrinted (constIndexFoldBody body) = some g'
      ∧ ∀ s, runBlock s g' = runBlock s g := by
  unfold constIndexFoldBody
  dsimp only
  split
  · rename_i hp
    simp only [gatherPrinted, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    have s0 : JState 64 := { regs := fun _ => 0 }
    obtain ⟨ls', h1, -⟩ :=
      foldCore_gather (bodyParams body) (runtimeBases (bodyParams body) [] [] body) body []
        s0 ls (KEnv.Holds.nil s0) hls
    refine ⟨ls'.flatten, ?_, fun s => ?_⟩
    · simp only [gatherPrinted, hp]
      simp only [gatherList] at h1
      simp [h1]
    · obtain ⟨ls'', h2, h3⟩ :=
        foldCore_gather (bodyParams body) (runtimeBases (bodyParams body) [] [] body) body []
          s ls (KEnv.Holds.nil s) hls
      rw [h1] at h2
      cases h2
      exact h3
  · exact ⟨g, h, fun _ => rfl⟩

/-- **Directness.** When every register-indexed instruction of the body is folded
    and the frame guard of `constIndexFoldBody` holds, the fold is index-free. -/
theorem constIndexFoldBody_lcmdDirect {body : Lcmd}
    (hc : covers (bodyParams body) [] body = true)
    (hg : bodyParams (foldCore (bodyParams body) [] [] body) = bodyParams body) :
    lcmdDirect (constIndexFoldBody body) = true := by
  simp only [constIndexFoldBody, runtimeBases_of_covers _ body [] [] hc, hg, ite_true]
  exact foldCore_lcmdDirect _ body [] hc

/-- **Constant time.** Under the hypotheses of `constIndexFoldBody_lcmdDirect`,
    the gathered block of the fold has the same machine leakage trace from any two
    initial states. -/
theorem gatherPrinted_constIndexFoldBody_constant_time {body : Lcmd}
    {g : List (JInstr 64)}
    (hc : covers (bodyParams body) [] body = true)
    (hg : bodyParams (foldCore (bodyParams body) [] [] body) = bodyParams body)
    (h : gatherPrinted (constIndexFoldBody body) = some g) (s₁ s₂ : JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  ConstantTimeCoverage.allDirect_constant_time g
    (gatherPrinted_allDirect (constIndexFoldBody_lcmdDirect hc hg) h) s₁ s₂

/-! ## 7. The printable spelling

`LprogAsmPrinter` and `LprogBytes` render a compile-time-displacement memory
operand as the register-shaped name `mem.<B>.<off>` under `MOVQ`, the form the
array-ABI orchestration emits; they do not render the `.arr` operand. `spellInstr`
maps the two folded forms to that spelling and leaves every other instruction
unchanged. -/

/-- `LOAD [d] [.arr B off]` is `MOVQ [d] [mem.B.off]`; `STORE [_] [.arr B off, v]`
    is `MOVQ [mem.B.off] [v]`. -/
def spellInstr : LinstrR → LinstrR
  | .Lopn [.reg d] "LOAD" [.arr B off] => .Lopn [.reg d] "MOVQ" [.reg (memName B off)]
  | .Lopn [.reg _] "STORE" [.arr B off, .reg vn] =>
      .Lopn [.reg (memName B off)] "MOVQ" [.reg vn]
  | i => i

/-- The spelling applied to every instruction of every function. -/
def spellLprog (lp : Lprog) : Lprog :=
  let spell : Lcmd → Lcmd := List.map (fun i => { i with li_i := spellInstr i.li_i })
  let fs := lp.lp_funcs.map (fun f => (f.1, { f.2 with lfd_body := spell f.2.lfd_body }))
  { lp with lp_funcs := fs }

/-- The spelling of the folded forms as array-ABI memory moves: `LOAD [d] [.arr B off]`
    is `LOAD:64 [d] [mem.B.off]` and `STORE [_] [.arr B off, v]` is
    `STORE:64 [mem.B.off] [v]` when the register operand is a general-purpose name,
    and the `spellInstr` form otherwise. `LprogAsmPrinter` prints the two forms as
    `movq off(%B), %d` and `movq %v, off(%B)`, `LprogBytes.encodeLopn` encodes them,
    and `GatherMemOps.lowerMemOp` lowers them to the `loadMem`/`storeMem` the
    unspelled forms lower to (`lowerMemOp_spellMemInstr_load`,
    `lowerMemOp_spellMemInstr_store`). -/
def spellMemInstr : LinstrR → LinstrR
  | .Lopn [.reg d] "LOAD" [.arr B off] =>
      if isGpName d then .Lopn [.reg d] "LOAD:64" [.reg (memName B off)]
      else .Lopn [.reg d] "MOVQ" [.reg (memName B off)]
  | .Lopn [.reg _] "STORE" [.arr B off, .reg vn] =>
      if isGpName vn then .Lopn [.reg (memName B off)] "STORE:64" [.reg vn]
      else .Lopn [.reg (memName B off)] "MOVQ" [.reg vn]
  | i => i

/-- `spellMemInstr` applied to every instruction of a body. -/
def spellMemBody (body : Lcmd) : Lcmd :=
  body.map (fun i => { i with li_i := spellMemInstr i.li_i })

/-- A `mem.<B>.<off>` name over a general-purpose base parses back to `(B, off)`. -/
theorem memNameParts_memName {B : String} (hB : isGpName B = true) (off : Nat) :
    GatherMemOps.memNameParts (memName B off) = some (B, (off : Int)) := by
  have hd : natOfDigits? (Nat.toDigits 10 off) = some off := by
    simpa using VIR.JasminImmShiftMnem.natOfDigits?_toString off
  unfold isGpName at hB
  split at hB <;>
    first
    | exact absurd hB (by decide)
    | simp [GatherMemOps.memNameParts, memName, hasPrefix, hd]

/-- The spelled load lowers, through the array-ABI memory arm, to the block the
    folded load lowers to. -/
theorem lowerMemOp_spellMemInstr_load (frame spillW qsaveB : Nat) {d B : String} (off : Nat)
    (hd : isGpName d = true) (hB : isGpName B = true) :
    GatherMemOps.lowerMemOp frame spillW (spellMemInstr (.Lopn [.reg d] "LOAD" [.arr B off]))
        qsaveB
      = lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "LOAD" [.arr B off]) := by
  rw [lowerPrinted_load]
  simp only [spellMemInstr, hd, ite_true]
  exact GatherMemOps.lowerMemOp_load _ _ _ _ _ _ _ (memNameParts_memName hB off) hB hd

/-- The spelled store lowers, through the array-ABI memory arm, to the block the
    folded store lowers to. -/
theorem lowerMemOp_spellMemInstr_store (frame spillW qsaveB : Nat) {d B vn : String}
    (off : Nat) (hv : isGpName vn = true) (hB : isGpName B = true) :
    GatherMemOps.lowerMemOp frame spillW
        (spellMemInstr (.Lopn [.reg d] "STORE" [.arr B off, .reg vn])) qsaveB
      = lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "STORE" [.arr B off, .reg vn]) := by
  rw [lowerPrinted_store]
  simp only [spellMemInstr, hv, ite_true]
  exact GatherMemOps.lowerMemOp_store _ _ _ _ _ _ _ (memNameParts_memName hB off) hB hv

/-! ## 8. Displacement addressing at a literal index -/

/-- After `mov x, $k`, the register-indexed load `(%B,%x,8)` is the load at
    displacement `8·k` from `B`. -/
theorem runBlock_movImm_loadMemIdx (s : JState 64) (d B x : String) {k : Nat}
    (hk : k < 2 ^ 64) :
    runBlock s [.mov x (.imm k), .loadMemIdx d B x 8]
      = runBlock s [.mov x (.imm k), .loadMem d B ((8 * k : Nat) : Int)] := by
  simp only [runBlock_cons, runBlock_nil]
  rw [evalInstr_loadMemIdx_const _ d B x 8 (v := BitVec.ofNat 64 k)
    (by simp [evalInstr, JState.setReg, x86_MOV])]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-- After `mov x, $k`, the register-indexed store `(%B,%x,8)` is the store at
    displacement `8·k` from `B`. -/
theorem runBlock_movImm_storeMemIdx (s : JState 64) (B x : String) (src : JOperand)
    {k : Nat} (hk : k < 2 ^ 64) :
    runBlock s [.mov x (.imm k), .storeMemIdx B x 8 src]
      = runBlock s [.mov x (.imm k), .storeMem B ((8 * k : Nat) : Int) src] := by
  simp only [runBlock_cons, runBlock_nil]
  rw [evalInstr_storeMemIdx_const _ B x 8 src (v := BitVec.ofNat 64 k)
    (by simp [evalInstr, JState.setReg, x86_MOV])]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

/-! ## 9. Dead immediate moves

A fold leaves the immediate move that set the index register in place. When the
register is overwritten before it is read, the move is dead. `transparentTo r`
holds for the instructions that neither read nor write `r` as a machine register
(a memory operand's base counts as a read), `overwrites r` for those that write `r`
without reading it; every register operand of both is one of the sixteen
general-purpose names, so a `mem.<base>.<off>` name, whose base the machine reads,
never passes. -/

/-- `i` neither reads nor writes the register `r`. -/
def transparentTo (r : String) : JInstr 64 → Bool
  | .mov d (.imm _) => isGpName d && d != r
  | .mov d (.reg x) => isGpName d && isGpName x && d != r && x != r
  | .loadMem d B _ => isGpName d && d != r && B != r
  | .storeMem B _ (.reg v) => isGpName v && B != r && v != r
  | .storeMem B _ (.imm _) => B != r
  | _ => false

/-- `i` writes the register `r` without reading it. -/
def overwrites (r : String) : JInstr 64 → Bool
  | .mov d (.imm _) => d == r
  | .mov d (.reg x) => d == r && isGpName x && x != r
  | .loadMem d B _ => d == r && B != r
  | _ => false

/-- Two machine states that agree everywhere except on register `r`. -/
def AgreeOff (r : String) (s t : JState 64) : Prop :=
  s.flags = t.flags ∧ s.mem = t.mem ∧ ∀ q, q ≠ r → s.regs q = t.regs q

theorem AgreeOff.setReg {r : String} {s t : JState 64} (h : AgreeOff r s t) (d : String)
    (v : BitVec 64) : AgreeOff r (s.setReg d v) (t.setReg d v) := by
  obtain ⟨hf, hm, hr⟩ := h
  refine ⟨hf, hm, fun q hq => ?_⟩
  simp only [JState.setReg]
  split
  · rfl
  · exact hr q hq

theorem AgreeOff.setReg_eq {r : String} {s t : JState 64} (h : AgreeOff r s t)
    (v : BitVec 64) : s.setReg r v = t.setReg r v := by
  obtain ⟨hf, hm, hr⟩ := h
  cases s
  cases t
  simp only at hf hm hr
  subst hf hm
  simp only [JState.setReg, JState.mk.injEq, and_true]
  funext q
  split
  · rfl
  · exact hr q (by assumption)

theorem AgreeOff.store {r : String} {s t : JState 64} (h : AgreeOff r s t) (B : String)
    (off : Int) (v : BitVec 64) : AgreeOff r (s.store B off v) (t.store B off v) := by
  obtain ⟨hf, hm, hr⟩ := h
  refine ⟨hf, ?_, hr⟩
  simp only [JState.store, hm]

theorem AgreeOff.setReg_left {r : String} (s : JState 64) (v : BitVec 64) :
    AgreeOff r (s.setReg r v) s := by
  refine ⟨rfl, rfl, fun q hq => ?_⟩
  simp [JState.setReg, hq]

/-- A transparent instruction keeps two states that agree off `r` agreeing off `r`. -/
theorem AgreeOff.evalInstr_transparent {r : String} {s t : JState 64} (h : AgreeOff r s t)
    {i : JInstr 64} (hi : transparentTo r i = true) :
    AgreeOff r (evalInstr s i) (evalInstr t i) := by
  cases i with
  | mov d src =>
      cases src with
      | imm k => exact h.setReg d _
      | reg x =>
          simp only [transparentTo, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
          have hx : s.regs x = t.regs x := h.2.2 x hi.2
          simp only [evalInstr, JOperand.eval, JState.get, hx]
          exact h.setReg d _
  | loadMem d B off =>
      simp only [evalInstr, JState.load, h.2.1]
      exact h.setReg d _
  | storeMem B off src =>
      cases src with
      | imm k => exact h.store B off _
      | reg v =>
          simp only [transparentTo, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
          have hv : s.regs v = t.regs v := h.2.2 v hi.2
          simp only [evalInstr, JOperand.eval, JState.get, hv]
          exact h.store B off _
  | _ => simp [transparentTo] at hi

/-- An instruction that overwrites `r` without reading it sends two states that agree
    off `r` to the same state. -/
theorem AgreeOff.evalInstr_overwrites {r : String} {s t : JState 64} (h : AgreeOff r s t)
    {i : JInstr 64} (hi : overwrites r i = true) : evalInstr s i = evalInstr t i := by
  cases i with
  | mov d src =>
      cases src with
      | imm k =>
          simp only [overwrites, beq_iff_eq] at hi
          subst hi
          exact h.setReg_eq _
      | reg x =>
          simp only [overwrites, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hi
          obtain ⟨⟨rfl, -⟩, hx⟩ := hi
          have hx' : s.regs x = t.regs x := h.2.2 x hx
          simp only [evalInstr, JOperand.eval, JState.get, hx']
          exact h.setReg_eq _
  | loadMem d B off =>
      simp only [overwrites, Bool.and_eq_true, beq_iff_eq] at hi
      obtain ⟨rfl, -⟩ := hi
      simp only [evalInstr, JState.load, h.2.1]
      exact h.setReg_eq _
  | _ => simp [overwrites] at hi

/-- The scan of a gathered block for register `r`: `some true` when an instruction
    overwrites `r` after a transparent prefix, `some false` when an instruction that
    is neither is reached first, `none` when the whole block is transparent. -/
def scanBlock (r : String) : List (JInstr 64) → Option Bool
  | [] => none
  | i :: is =>
      if overwrites r i then some true
      else if transparentTo r i then scanBlock r is
      else some false

theorem scanBlock_none {r : String} :
    ∀ {bs : List (JInstr 64)} {s t : JState 64}, scanBlock r bs = none →
      AgreeOff r s t → AgreeOff r (runBlock s bs) (runBlock t bs)
  | [], _, _, _, h => h
  | i :: is, s, t, hb, h => by
      simp only [scanBlock] at hb
      split at hb
      · simp at hb
      · split at hb
        · exact scanBlock_none (bs := is) hb (h.evalInstr_transparent (by assumption))
        · simp at hb

theorem scanBlock_true {r : String} :
    ∀ {bs : List (JInstr 64)} {s t : JState 64}, scanBlock r bs = some true →
      AgreeOff r s t → runBlock s bs = runBlock t bs
  | [], _, _, hb, _ => by simp [scanBlock] at hb
  | i :: is, s, t, hb, h => by
      simp only [scanBlock] at hb
      split at hb
      · simp only [runBlock_cons, h.evalInstr_overwrites (by assumption)]
      · split at hb
        · exact scanBlock_true (bs := is) hb (h.evalInstr_transparent (by assumption))
        · simp at hb

/-- The register `r` is overwritten before it is read along the straight-line body:
    the scan meets an overwrite before a return, an instruction the gather does not
    lower, or an instruction that is not transparent. -/
def deadAfter (p : Nat × Nat × Nat) (r : String) : Lcmd → Bool
  | [] => false
  | j :: js =>
      if isLret j then false
      else
        match lowerPrinted p.1 p.2.1 p.2.2 j.li_i with
        | none => false
        | some bs =>
            match scanBlock r bs with
            | some b => b
            | none => deadAfter p r js

theorem gatherList_cons (p : Nat × Nat × Nat) (i : Linstr) (is : Lcmd) :
    gatherList p (i :: is) =
      if isLret i = true then gatherList p is
      else (lowerPrinted p.1 p.2.1 p.2.2 i.li_i).bind
        (fun js => (gatherList p is).map (js :: ·)) := by
  by_cases hr : isLret i = true
  · simp [gatherList, hr]
  · have hr0 : isLret i = false := by simpa using hr
    cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i <;>
      cases hrest : gatherList p is <;>
      simp_all [gatherList, List.mapM_cons]

/-- Along a body in which `r` is dead, two states that agree off `r` run to the same
    state. -/
theorem deadAfter_run (p : Nat × Nat × Nat) (r : String) :
    ∀ (body : Lcmd) (ls : List (List (JInstr 64))) (s t : JState 64),
      deadAfter p r body = true → gatherList p body = some ls → AgreeOff r s t →
      runBlock s ls.flatten = runBlock t ls.flatten := by
  intro body
  induction body with
  | nil => intro _ _ _ hd; simp [deadAfter] at hd
  | cons j js ih =>
      intro ls s t hd hg h
      by_cases hr : isLret j = true
      · simp [deadAfter, hr] at hd
      · rw [gatherList_cons, ite_eq_right hr] at hg
        simp only [deadAfter, hr, Bool.false_eq_true, ite_false] at hd
        cases hj : lowerPrinted p.1 p.2.1 p.2.2 j.li_i with
        | none => simp [hj] at hd
        | some bs =>
            rw [hj] at hg
            simp only [hj] at hd
            cases hrest : gatherList p js with
            | none => simp [hrest] at hg
            | some rest =>
                simp only [hrest, Option.bind_some, Option.map_some,
                  Option.some.injEq] at hg
                subst hg
                simp only [List.flatten_cons, runBlock_append']
                cases hb : scanBlock r bs with
                | none =>
                    simp only [hb] at hd
                    exact ih rest _ _ hd hrest (scanBlock_none hb h)
                | some b =>
                    simp only [hb] at hd
                    subst hd
                    rw [scanBlock_true hb h]

/-- The register an instruction sets to an immediate, when it lowers to exactly
    that move. -/
def deadImmReg? (p : Nat × Nat × Nat) (i : Linstr) : Option String :=
  match lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
  | some [.mov r (.imm _)] => if isGpName r then some r else none
  | _ => none

theorem deadImmReg?_spec {p : Nat × Nat × Nat} {i : Linstr} {r : String}
    (h : deadImmReg? p i = some r) :
    ∃ k, lowerPrinted p.1 p.2.1 p.2.2 i.li_i = some [.mov r (.imm k)] := by
  unfold deadImmReg? at h
  split at h
  · rename_i k hl
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨k, hl⟩
    · simp at h
  · simp at h

/-- Drop every immediate move to a general-purpose register that is dead. -/
def dropDeadCore (p : Nat × Nat × Nat) : Lcmd → Lcmd
  | [] => []
  | i :: is =>
      match deadImmReg? p i with
      | some r => if deadAfter p r is then dropDeadCore p is else i :: dropDeadCore p is
      | none => i :: dropDeadCore p is

/-- The tail-recursive image of `dropDeadCore`, accumulating in reverse. -/
def dropDeadCoreTR (p : Nat × Nat × Nat) (acc : Lcmd) : Lcmd → Lcmd
  | [] => acc.reverse
  | i :: is =>
      match deadImmReg? p i with
      | some r =>
          if deadAfter p r is then dropDeadCoreTR p acc is else dropDeadCoreTR p (i :: acc) is
      | none => dropDeadCoreTR p (i :: acc) is

theorem dropDeadCoreTR_eq (p : Nat × Nat × Nat) (acc body : Lcmd) :
    dropDeadCoreTR p acc body = acc.reverse ++ dropDeadCore p body := by
  induction body generalizing acc with
  | nil => simp [dropDeadCoreTR, dropDeadCore]
  | cons i is ih =>
      simp only [dropDeadCoreTR, dropDeadCore]
      split
      · split <;> simp [ih]
      · simp [ih]

/-- `dropDeadCore` from the empty accumulator, the form the compiler runs. -/
def dropDeadCoreFast (p : Nat × Nat × Nat) (body : Lcmd) : Lcmd := dropDeadCoreTR p [] body

/-- Compiled code runs `dropDeadCore` through its tail-recursive image. -/
@[csimp] theorem dropDeadCore_eq_fast : @dropDeadCore = @dropDeadCoreFast := by
  funext p body
  simp [dropDeadCoreFast, dropDeadCoreTR_eq]

/-- **Block agreement at fixed frame parameters.** If the body gathers, the body
    without its dead immediate moves gathers, and the two blocks run to the same
    machine state from every state. -/
theorem dropDeadCore_gather (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (ls : List (List (JInstr 64))), gatherList p body = some ls →
      ∃ ls', gatherList p (dropDeadCore p body) = some ls'
        ∧ ∀ s, runBlock s ls'.flatten = runBlock s ls.flatten := by
  intro body
  induction body with
  | nil => intro ls h; exact ⟨ls, h, fun _ => rfl⟩
  | cons i is ih =>
      intro ls h
      -- keeping `i` in front of a body that agrees with the tail
      have keep : ∃ ls', gatherList p (i :: dropDeadCore p is) = some ls'
          ∧ ∀ s, runBlock s ls'.flatten = runBlock s ls.flatten := by
        rw [gatherList_cons] at h ⊢
        by_cases hr : isLret i = true
        · rw [ite_eq_left hr] at h ⊢
          exact ih ls h
        · rw [ite_eq_right hr] at h ⊢
          cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
          | none => simp [hi] at h
          | some js =>
              cases hrest : gatherList p is with
              | none => simp [hi, hrest] at h
              | some rest =>
                  simp only [hi, hrest, Option.bind_some, Option.map_some,
                    Option.some.injEq] at h
                  subst h
                  obtain ⟨rest', h1, h2⟩ := ih rest hrest
                  refine ⟨js :: rest', by simp [h1], fun s => ?_⟩
                  simp only [List.flatten_cons, runBlock_append', h2]
      cases hd : deadImmReg? p i with
      | none => simpa [dropDeadCore, hd] using keep
      | some r =>
          by_cases hdead : deadAfter p r is = true
          · simp only [dropDeadCore, hd, hdead, ite_true]
            obtain ⟨k, hk⟩ := deadImmReg?_spec hd
            rw [gatherList_cons] at h
            by_cases hr : isLret i = true
            · rw [ite_eq_left hr] at h
              exact ih ls h
            · rw [ite_eq_right hr, hk] at h
              cases hrest : gatherList p is with
              | none => simp [hrest] at h
              | some rest =>
                  simp only [hrest, Option.bind_some, Option.map_some,
                    Option.some.injEq] at h
                  subst h
                  obtain ⟨rest', h1, h2⟩ := ih rest hrest
                  refine ⟨rest', h1, fun s => ?_⟩
                  simp only [List.flatten_cons, List.singleton_append, runBlock_cons, h2]
                  exact (deadAfter_run p r is rest _ _ hdead hrest
                    (AgreeOff.setReg_left (r := r) s _)).symm
          · simpa [dropDeadCore, hd, hdead] using keep

/-- The dead-move elimination of a body: `dropDeadCore` at the body's own frame
    parameters, kept only when the result has the same frame parameters. -/
def dropDeadImmBody (body : Lcmd) : Lcmd :=
  let b' := dropDeadCore (bodyParams body) body
  if bodyParams b' = bodyParams body then b' else body

theorem gatherPrinted_eq (body : Lcmd) :
    gatherPrinted body = (gatherList (bodyParams body) body).map List.flatten := rfl

/-- **Semantic agreement.** If a body gathers, the body without its dead immediate
    moves gathers, and the two blocks run to the same machine state from every
    state. -/
theorem gatherPrinted_dropDeadImmBody {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) :
    ∃ g', gatherPrinted (dropDeadImmBody body) = some g'
      ∧ ∀ s, runBlock s g' = runBlock s g := by
  unfold dropDeadImmBody
  dsimp only
  split
  · rename_i hp
    rw [gatherPrinted_eq, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    obtain ⟨ls', h1, h2⟩ := dropDeadCore_gather (bodyParams body) body ls hls
    refine ⟨ls'.flatten, ?_, h2⟩
    rw [gatherPrinted_eq, hp, h1]
    rfl
  · exact ⟨g, h, fun _ => rfl⟩

/-! ## 10. The owned stage -/

/-- The fold, the dead-move elimination and the array-ABI spelling of one body. -/
def foldIndexedBody (body : Lcmd) : Lcmd :=
  spellMemBody (dropDeadImmBody (constIndexFoldBody body))

/-- `foldIndexedBody` applied to every function of a program: every 64-bit
    register-indexed access at an index the analysis knows becomes a
    compile-time-displacement access `off(%B)`, and the immediate moves that set
    those indices and are overwritten before a read are removed. -/
def foldIndexedLprog (lp : Lprog) : Lprog :=
  let fs := lp.lp_funcs.map
    (fun f => (f.1, { f.2 with lfd_body := foldIndexedBody f.2.lfd_body }))
  { lp with lp_funcs := fs }

/-- **Semantic agreement of the fold and the elimination.** If a body gathers, its
    folded body without dead immediate moves gathers, and the two blocks run to
    the same machine state from every state. -/
theorem gatherPrinted_dropDeadImm_constIndexFold {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) :
    ∃ g', gatherPrinted (dropDeadImmBody (constIndexFoldBody body)) = some g'
      ∧ ∀ s, runBlock s g' = runBlock s g := by
  obtain ⟨g1, h1, e1⟩ := gatherPrinted_constIndexFoldBody h
  obtain ⟨g2, h2, e2⟩ := gatherPrinted_dropDeadImmBody h1
  exact ⟨g2, h2, fun s => (e2 s).trans (e1 s)⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
