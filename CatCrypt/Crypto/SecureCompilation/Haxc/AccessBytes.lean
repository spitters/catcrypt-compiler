/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportSafety

/-!
# The memory accessed by the compiled bytes

`HaltsIn M prog pc sa sa'` says that the decoded program `prog` halts from index `pc` and state
`sa` in `sa'` and that every instruction of this run, in the state it runs in, reads and writes
memory in the set of bytes `M` only. The machine is deterministic, so the run is the one halting
run of the program from that state. The program is the argument of the predicate: in the
compiler theorems it is the program that the emitted bytes decode to.

The compiler meets the predicate at the memory of the layout. The image simulation bounds the
accesses of the address machine on the printed body, and the traced simulation of the decoded
bytes (`ImageStraightCellsCT.TracedSimW`) gives every memory event of the decoded run as an
event of a step of the address machine, a frame word of the body or the red-zone word.

## Main definitions

* `AccessBytes.OpAccessIn`: the accesses of one instruction lie in a set of bytes.
* `AccessBytes.HaltsIn`: a halting run of a decoded program whose accesses all lie in a set of
  bytes.

## Main results

* `AccessBytes.OpAccessIn.keep_mem`, `AccessBytes.OpAccessIn.agree`: an instruction with its
  accesses in `M` changes no byte outside `M`, and its effect depends on the bytes of `M` only.
* `AccessBytes.HaltsIn.of_halts`, `AccessBytes.HaltsIn.keep_mem`: the predicate holds of every
  halting run from the state, and a byte outside `M` keeps its value.
* `AccessBytes.compileRegion_haltsIn`, `AccessBytes.compileR_haltsIn`: the back half and the
  compiler at an entry emit bytes whose halting run accesses `layoutMem σ sa` only.
* `haxc_correct_auto_access`: the compiler theorem on a module, whose case without a call
  bounds the accesses of the emitted bytes.
* `haxc_safe_bytes`, `haxc_contract_safe_bytes`: on a module without linked functions the
  emitted bytes access only the memory that the precondition of the export owns.
* `AccessBytes.haltsIn_oneStore`: the predicate at a program of one store inside its layout.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (idxVal)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (MLeak instrLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL BlockOk blockLeakA opLeak
  resolveEv halts_runL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys slotOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (frameP redW classifyA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (RunSafe frameRsp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrWLeak (fEv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det redLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys (evA zeroEvs instrLeakA
  stepLeakA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCellsCT (runALeakG
  runALeakG_of_runA stepGW gW sLeakW iLeakW tracedSimW_of_armLeaks armLeaksW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightCells (cellIdx frameC slotArrC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCellFold (Slots)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRouteW (baseR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.SepLogic (Rng)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (AccessIn loadsA storeR? storeA? idxAddr?
  cellLdAddr? stepReads stepWrites readsA writesA)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime)

/-! ## 1. The predicate on decoded programs -/

/-- Every memory access of the instruction `i` in the state `sa` lies in `M`: the eight bytes
    at the effective address of each memory event of `MachineConstantTime.instrLeak`. -/
def OpAccessIn (M : Set (BitVec 64)) (sa : AState) (i : JInstr 64) : Prop :=
  ∀ b o, MLeak.mem b o ∈ instrLeak sa.view i →
    ∀ x ∈ (⟨sa.regs b + BitVec.ofInt 64 o, 8⟩ : Rng 64), x ∈ M

/-- The program `prog` halts from index `pc` and state `sa` in `sa'`, and every instruction of
    the run, those of callees, calls and returns included, accesses `M` only. -/
def HaltsIn (M : Set (BitVec 64)) (prog : List RInstr) (pc : Nat) (sa sa' : AState) : Prop :=
  ∃ t, RunL .doitm (OpAccessIn M) prog pc sa t sa'

/-- The eight bytes at the address of a memory event lie in `M`; every other event has no
    address. -/
def EventIn (M : Set (BitVec 64)) : CTLeak → Prop
  | .addr _ a => ∀ x ∈ (⟨BitVec.ofInt 64 a, 8⟩ : Rng 64), x ∈ M
  | _ => True

/-- The event of the address `a` lies in `M` when the eight bytes from `a` do. -/
theorem eventIn_evA {M : Set (BitVec 64)} {a : BitVec 64} :
    EventIn M (evA a) ↔ ∀ x ∈ (⟨a, 8⟩ : Rng 64), x ∈ M := by
  simp [EventIn, evA, BitVec.ofInt_natCast]

/-- An instruction whose events lie in `M` accesses `M` only. -/
theorem opAccessIn_of_events {M : Set (BitVec 64)} {r : DoitRegime} {sa : AState}
    {i : JInstr 64} (h : ∀ e ∈ opLeak r sa i, EventIn M e) : OpAccessIn M sa i := by
  intro b o hm
  exact eventIn_evA.1 (h _ (List.mem_append_left _ (List.mem_map.2 ⟨_, hm, rfl⟩)))

/-- A block whose events lie in `M` accesses `M` only. -/
theorem blockOk_of_events {M : Set (BitVec 64)} {r : DoitRegime} :
    ∀ (ops : List (JInstr 64)) (sa : AState), (∀ e ∈ blockLeakA r sa ops, EventIn M e) →
      BlockOk (OpAccessIn M) sa ops
  | [], _, _ => trivial
  | _ :: is, _, h =>
      ⟨opAccessIn_of_events fun e he => h e (List.mem_append_left _ he),
        blockOk_of_events is _ fun e he => h e (List.mem_append_right _ he)⟩

/-- A run whose events lie in `M` accesses `M` only at each of its steps. -/
theorem runL_of_events {M : Set (BitVec 64)} {r : DoitRegime}
    {ok : AState → JInstr 64 → Prop} {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    {t : List CTLeak} (h : RunL r ok prog pc sa t sa') :
    (∀ e ∈ t, EventIn M e) → RunL r (OpAccessIn M) prog pc sa t sa' := by
  induction h with
  | ret h => exact fun _ => .ret h
  | op h _ _ ih =>
      exact fun ht => .op h (opAccessIn_of_events fun e he => ht e (List.mem_append_left _ he))
        (ih fun e he => ht e (List.mem_append_right _ he))
  | jcc h hc _ ih => exact fun ht => .jcc h hc (ih fun e he => ht e (List.mem_cons_of_mem _ he))
  | stack h hops _ _ ih =>
      exact fun ht => .stack h hops
        (blockOk_of_events _ _ fun e he => ht e (List.mem_append_left _ he))
        (ih fun e he => ht e (List.mem_append_right _ he))
  | call h _ _ _ _ ihc ihr =>
      intro ht
      simp only [List.mem_append] at ht
      exact .call h (blockOk_of_events _ _ fun e he => ht e (.inl (.inl (.inl he))))
        (ihc fun e he => ht e (.inl (.inl (.inr he))))
        (blockOk_of_events _ _ fun e he => ht e (.inl (.inr he)))
        (ihr fun e he => ht e (.inr he))

/-- A run with its accesses in `M` is a halting run. -/
theorem HaltsIn.halts {M : Set (BitVec 64)} {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (h : HaltsIn M prog pc sa sa') : Halts aMachine prog pc sa sa' :=
  h.elim fun _ ht => ht.halts

/-- `HaltsIn` is monotone in the set of bytes. -/
theorem HaltsIn.mono {M N : Set (BitVec 64)} {prog : List RInstr} {pc : Nat} {sa sa' : AState}
    (hMN : M ⊆ N) (h : HaltsIn M prog pc sa sa') : HaltsIn N prog pc sa sa' :=
  h.imp fun _ ht => ht.mono fun _ _ hok b o hm x hx => hMN (hok b o hm x hx)

/-- **Every halting run from the state.** If one halting run of a program from a state accesses
    `M` only, so does every halting run of the program from that state. -/
theorem HaltsIn.of_halts {M : Set (BitVec 64)} {prog : List RInstr} {pc : Nat}
    {sa sa' sa'' : AState} (h : HaltsIn M prog pc sa sa')
    (hh : Halts aMachine prog pc sa sa'') : HaltsIn M prog pc sa sa'' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := halts_runL .doitm hh
  obtain ⟨-, rfl⟩ := runL_det ht ht'
  exact ⟨t, ht⟩

/-- An instruction that accesses `M` only changes no byte outside `M`. -/
theorem OpAccessIn.keep_mem {M : Set (BitVec 64)} {sa : AState} {i : JInstr 64}
    (h : OpAccessIn M sa i) {x : BitVec 64} (hx : x ∉ M) :
    (evalInstrA sa i).mem x = sa.mem x := by
  cases ha : writeAddr sa i with
  | none => simp [evalInstrA, ha]
  | some a =>
      simp only [evalInstrA, ha]
      refine write64_of_not_inRange _ _ _ _ fun hin => hx ?_
      cases i <;> simp only [writeAddr, Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
        exact h _ _ (by simp [instrLeak, AState.view, JState.get]) x hin

/-- **An instruction that accesses `M` only depends on the bytes of `M` only**: from two states
    with equal registers and flags and equal bytes on `M` it ends with equal registers and
    flags and equal bytes on `M`. -/
theorem OpAccessIn.agree {M : Set (BitVec 64)} {sa sb : AState} {i : JInstr 64}
    (h : OpAccessIn M sa i) (hr : sa.regs = sb.regs) (hf : sa.flags = sb.flags)
    (hm : ∀ x ∈ M, sa.mem x = sb.mem x) :
    (evalInstrA sa i).regs = (evalInstrA sb i).regs
      ∧ (evalInstrA sa i).flags = (evalInstrA sb i).flags
      ∧ ∀ x ∈ M, (evalInstrA sa i).mem x = (evalInstrA sb i).mem x := by
  have hread : ∀ b o, MLeak.mem b o ∈ instrLeak sa.view i →
      read64 sa.mem (sa.regs b + BitVec.ofInt 64 o)
        = read64 sb.mem (sa.regs b + BitVec.ofInt 64 o) := by
    intro b o he
    have hk : ∀ k, k < 8 → sa.mem (sa.regs b + BitVec.ofInt 64 o + BitVec.ofNat 64 k)
        = sb.mem (sa.regs b + BitVec.ofInt 64 o + BitVec.ofNat 64 k) := fun k hk =>
      hm _ (h b o he _ (SepLogic.Rng.mem_def.2 (by rwa [toNat_add_sub_self _ k hk])))
    have h0 := hk 0 (by decide)
    simp only [BitVec.add_zero] at h0
    simp only [read64, h0, hk 1 (by decide), hk 2 (by decide), hk 3 (by decide),
      hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]
  obtain ⟨R, F, m⟩ := sa
  obtain ⟨R', F', m'⟩ := sb
  subst hr hf
  let u := AState.view ⟨R, F, m⟩
  let u' := AState.view ⟨R, F, m'⟩
  have key : (evalInstr u i).regs = (evalInstr u' i).regs
      ∧ (evalInstr u i).flags = (evalInstr u' i).flags ∧ writeVal u i = writeVal u' i := by
    simp only [u, u']
    cases hform : addrFormB i with
    | true =>
        refine evalInstr_congr _ _ i hform rfl rfl fun k hk => hread k.1 k.2 ?_
        cases i <;> simp_all [readKey, instrLeak] <;> grind
    | false =>
        cases i <;> simp only [addrFormB, Bool.true_eq_false] at hform <;>
          simp_all [instrLeak, evalInstr, writeVal, AState.view, JState.loadIdx, JState.get,
            JState.setReg]
  refine ⟨key.1, key.2.1, fun x hx => ?_⟩
  have hw : writeAddr ⟨R, F, m⟩ i = writeAddr ⟨R, F, m'⟩ i := by cases i <;> rfl
  simp only [evalInstrA, ← hw]
  cases writeAddr ⟨R, F, m⟩ i <;> grind [write64]

/-- A block that accesses `M` only changes no byte outside `M`. -/
theorem blockOk_keep_mem {M : Set (BitVec 64)} {x : BitVec 64} (hx : x ∉ M) :
    ∀ (ops : List (JInstr 64)) (sa : AState), BlockOk (OpAccessIn M) sa ops →
      (runBlockA sa ops).mem x = sa.mem x
  | [], _, _ => rfl
  | _ :: is, _, h => (blockOk_keep_mem hx is _ h.2).trans (OpAccessIn.keep_mem h.1 hx)

/-- A byte outside `M` keeps its value through a run that accesses `M` only. -/
theorem HaltsIn.keep_mem {M : Set (BitVec 64)} {prog : List RInstr} {pc : Nat}
    {sa sa' : AState} (h : HaltsIn M prog pc sa sa') {x : BitVec 64} (hx : x ∉ M) :
    sa'.mem x = sa.mem x := by
  obtain ⟨t, ht⟩ := h
  induction ht with
  | ret => rfl
  | op _ hok _ ih => exact ih.trans (hok.keep_mem hx)
  | jcc _ _ _ ih => exact ih
  | stack _ _ hok _ ih => exact ih.trans (blockOk_keep_mem hx _ _ hok)
  | call _ hok _ hokr _ ihc ihr =>
      exact ihr.trans ((blockOk_keep_mem hx _ _ hokr).trans
        (ihc.trans (blockOk_keep_mem hx _ _ hok)))

/-! ## 2. The events of a step of the address machine -/

/-- **The events of a step lie in its footprints.** When a step of the address machine
    succeeds, its frame words and the bytes of its store and of its loads lie in `M`, so do
    its events `instrLeakA`. -/
theorem instrLeakA_eventIn {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {x : LinstrR} {tag : MemTag} {s : LstateA} {zf : Bool} {p : LstateA × Bool}
    (hF : ∀ q a, frame q = some a → ∀ y ∈ (⟨a, 8⟩ : Rng 64), y ∈ M)
    (hst : fstepA frame (x, tag) s zf = some p)
    (hS : ∀ R, storeR? frame (x, tag) s.reg = some R → ∀ y ∈ R, y ∈ M)
    (hL : ∀ a ∈ loadsA frame (x, tag) s.reg, ∀ y ∈ (⟨a, 8⟩ : Rng 64), y ∈ M) :
    ∀ e ∈ instrLeakA frame (x, tag) s, EventIn M e := by
  have hidx : ∀ i v, s.reg.getW i 64 = some v → idxVal s.reg i = v.toNat := by
    intro i v h
    unfold LstateN.getW at h
    unfold idxVal
    grind
  intro e he
  cases tag with
  | load w n =>
      simp only [instrLeakA] at he
      simp only [fstepA] at hst
      repeat' split at hst
      all_goals simp_all only [Option.some.injEq, List.mem_singleton, List.not_mem_nil,
        imp_false, reduceCtorEq]
      exact eventIn_evA.2 (hL _ (by simp_all [loadsA, idxAddr?]))
  | store w n =>
      simp only [instrLeakA] at he
      simp only [fstepA] at hst
      repeat' split at hst
      all_goals simp_all only [Option.some.injEq, List.mem_singleton, List.not_mem_nil,
        imp_false, reduceCtorEq]
      exact eventIn_evA.2 (hS _ (by simp_all [storeR?, storeA?]))
  | reg c =>
      simp only [instrLeakA] at he
      repeat' split at he
      all_goals simp only [List.mem_append, List.mem_map, List.mem_singleton, List.not_mem_nil,
        Option.mem_toList] at he
      all_goals
        first
        | grind [eventIn_evA, loadsA, storeR?, storeA?, cellLdAddr?]
        | (subst he; exact eventIn_evA.2 (hS _ (by simp_all [storeR?, storeA?])))
  | zero w n =>
      simp only [instrLeakA] at he
      simp only [fstepA] at hst
      repeat' split at hst
      all_goals simp_all only [zeroEvs, storeR?, ↓reduceIte, Option.map_some, Option.map_none,
        Option.some.injEq, forall_eq', List.mem_map, List.mem_range, List.not_mem_nil,
        reduceCtorEq]
      obtain ⟨i, hi, rfl⟩ := he
      refine eventIn_evA.2 fun y hy => hS y ?_
      simp only [SepLogic.Rng.mem_def, BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_ofNat] at hy ⊢
      omega
  | storeImm w n =>
      simp only [instrLeakA] at he
      simp only [fstepA] at hst
      repeat' split at hst
      all_goals simp_all only [Option.toList_some, Option.toList_none, List.map_cons,
        List.map_nil, List.mem_singleton, List.not_mem_nil, Option.some.injEq, imp_false,
        reduceCtorEq]
      exact eventIn_evA.2 (hS _ (by simp_all [storeR?, storeA?]))
  | _ => simp [instrLeakA] at he

/-- The frame events of a name lie in `M` when its frame word does. -/
theorem fEv_eventIn {M : Set (BitVec 64)} {P : Params} {rsp : BitVec 64} {q : String}
    (h : ∀ a, frameP P rsp q = some a → ∀ y ∈ (⟨a, 8⟩ : Rng 64), y ∈ M) :
    ∀ e ∈ fEv P rsp q, EventIn M e := by
  intro e he
  simp only [fEv, List.mem_map, Option.mem_toList] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact eventIn_evA.2 (h a ha)

/-- **The events of the decoded instructions of one instruction** lie in `M` when the
    red-zone word and the frame words of its names do, and the events of its step on the
    address machine, off the untagged immediate moves, do. -/
theorem gW_eventIn {M : Set (BitVec 64)} {body : Lcmd} {P : Params} {rsp : BitVec 64}
    {ds : List LOperand} {o : String} {ss : List LOperand} {ℓ : List CTLeak}
    (hok : instrOKWB body P (.Lopn ds o ss) = true)
    (hred : ∀ y ∈ (⟨redW rsp, 8⟩ : Rng 64), y ∈ M)
    (hF : ∀ q ∈ instrNames (.Lopn ds o ss), ∀ a, frameP P rsp q = some a →
      ∀ y ∈ (⟨a, 8⟩ : Rng 64), y ∈ M)
    (hl : movImmStruct? (.Lopn ds o ss) = none → ∀ e ∈ ℓ, EventIn M e) :
    ∀ e ∈ gW P rsp (.Lopn ds o ss) ℓ, EventIn M e := by
  have hr : EventIn M (evA (redW rsp)) := eventIn_evA.2 hred
  have hf := fun q hq => fEv_eventIn (hF q hq)
  intro e he
  simp only [instrOKWB] at hok
  unfold gW at he
  repeat' split at he
  all_goals try (exact absurd he List.not_mem_nil)
  · -- a carry arm with frame-slot operands
    rename_i c hc
    have hi := classifyS_instr hc
    rw [← hi] at hf
    cases c <;>
      simp only [SArm.instr, instrNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, opNames, List.mem_cons, List.not_mem_nil] at hf <;>
      simp only [sLeakW] at he <;> grind
  · -- a cell access
    grind
  · -- an immediate store into a frame slot
    rename_i q v hc
    have hq : iOk P q v = true := by simp_all
    simp only [iOk, Bool.and_eq_true] at hq
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hq.1.1.1.2
    have hs : EventIn M (evA (rsp + BitVec.ofInt 64 (slotOff P q))) :=
      eventIn_evA.2 (hF q (by rw [classifyI_instr hc]; simp [instrNames, opNames]) _
        (by simp [frameP, slotOff, ha]))
    simp only [iLeakW] at he
    grind
  · -- a select with frame-slot values
    rename_i d c a b hc
    rw [classifyV_instr hc] at hf
    simp only [instrNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, opNames, List.mem_cons, List.not_mem_nil] at hf
    grind
  · -- an arm with its red-zone accesses
    rename_i ar _
    cases ar <;> simp only [redLeak] at he <;> grind
  · grind

/-- **The events of the decoded instructions of one step.** On a body in `printedAddrWB`, at a
    frame map that is `frameP` on the names of the body, a succeeding step whose accesses, frame
    words and red-zone word lie in `M` has its decoded events in `M`. -/
theorem stepGW_eventIn {M : Set (BitVec 64)} {body : Lcmd} {rsp : BitVec 64}
    {frame : String → Option (BitVec 64)} (hpr : printedAddrWB body = true)
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (hF : ∀ q a, frame q = some a → ∀ y ∈ (⟨a, 8⟩ : Rng 64), y ∈ M)
    (hred : ∀ y ∈ (⟨redW rsp, 8⟩ : Rng 64), y ∈ M)
    {s : LstateA} {zf : Bool} {p : LstateA × Bool} (hacc : AccessIn M frame body s)
    (hst : stepA frame body s zf = some p) :
    ∀ e ∈ stepGW rsp body s.reg.lpc (stepLeakA frame body s zf), EventIn M e := by
  obtain ⟨shs, hB⟩ := bodyFactsW_of hpr
  intro e he
  obtain ⟨hS, hL⟩ := hacc
  unfold SepLogic.Addr.StoreIn stepWrites at hS
  unfold SepLogic.Addr.LoadIn stepReads at hL
  unfold stepA at hst
  unfold stepGW stepLeakA at he
  cases hb : body[s.reg.lpc]? with
  | none => simp [hb] at hst
  | some i =>
      obtain ⟨ii, li⟩ := i
      simp only [hb] at hS hL hst he
      cases li with
      | Lopn ds o ss =>
          obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
          have hkn : s.reg.lpc + 1 < body.length := by
            by_contra hc
            have hlast := hB.last
            have hpc : s.reg.lpc = body.length - 1 := by omega
            simp only [hpc] at hbk
            rw [hbk] at hlast
            cases hlast
          have hok := hB.instr _ hkn
          rw [hbk] at hok
          refine gW_eventIn hok hred (fun q hq a ha => hF q a ?_) (fun hm => ?_) e he
          · rw [hfr q (List.mem_flatMap.2 ⟨_, List.mem_of_getElem? hb, hq⟩)]
            exact ha
          · simp only [tagAt_of_ne hm] at hS hL hst
            exact instrLeakA_eventIn hF hst (fun R hR y hy => hS y ⟨R, hR, hy⟩)
              fun a ha y hy => hL y ⟨a, ha, hy⟩
      | Lcond c l => cases c <;> grind [EventIn]
      | _ => grind

/-- The mapped trace of a run lies in `M` when that of every step does. -/
theorem runALeakG_eventIn {M : Set (BitVec 64)} {G : Nat → List CTLeak → List CTLeak}
    {frame : String → Option (BitVec 64)} {c : Lcmd} {Q : LstateA → Prop}
    (hQ : ∀ s zf p, Q s → stepA frame c s zf = some p →
      ∀ e ∈ G s.reg.lpc (stepLeakA frame c s zf), EventIn M e) :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool) (t : LstateA × Bool) (ℓ : List CTLeak),
      runALeakG G frame c fuel s zf = some (t, ℓ) → RunSafe frame c Q fuel s zf →
      ∀ e ∈ ℓ, EventIn M e := by
  intro fuel
  induction fuel with
  | zero => intro s zf t ℓ h _; simp [runALeakG] at h; grind
  | succ n ih =>
      intro s zf t ℓ h hs
      unfold runALeakG at h
      split at h
      · grind
      · obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨t', ℓ'⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hQ s zf p hs.1 hp e he
        · exact ih _ _ _ _ hr (hs.2 _ _ hp) e he

/-! ## 3. The compiled bytes -/

/-- **A virtual body on the decoded bytes, with their accesses.** Under the hypotheses of
    `renImage_bytes`, the bytes of the printed body decode to a program whose halting run from
    `sa` accesses `layoutMem σ sa` only. -/
theorem renImage_haltsIn {σ : AbiLayout} {nm : String → String} {ps : List (String × String)}
    {R : Slots} {outs : List String} {body : Lcmd} {B : List LinstrRM}
    (hg : renImageB σ nm ps R outs body B = true)
    (hU : ∀ j, j < σ.args.length → unren ps (renOf ps (argName j)) = argName j) (sa : AState)
    (hreg : σ.Regions sa) (fn : String) (fuel : Nat) (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn B) fuel
      { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa' := by
  obtain ⟨hsep, hrel, hents⟩ := renImage_entry hg hU sa hreg fn
  simp only [renImageB, calleeImgT_none, calleeImgBT_none, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hck, hidx⟩, hphys⟩, hgate⟩, hfr⟩, hent⟩, hN⟩, hlen⟩ := hg
  have E := entryB_spec hent sa
  have N := X86Backend.ImageAddrRouteW.cellNamesRB_spec hN
  have hgpN : ∀ r, gpOk r = true → cellIdx R r = none := by
    intro r hr
    cases hc : cellIdx R r with
    | none => rfl
    | some _ => grind [N.gp r]
  have hred : ∀ A j, cellIdx R (memName A (8 * j)) = some (A, j) →
      Disjoint8 (redW (frameRsp body sa)) (cellAt (baseR σ sa ps A) j) := by
    intro A j hc
    obtain ⟨n, hn, hj, -⟩ := X86Backend.ImageStraightCells.cellIdx_spec hc
    have hk : X86Backend.DecodeGenMem.regK (rsOf σ) (unren ps A) j := by
      unfold X86Backend.DecodeGenMem.regK
      rw [(hlen _ hn).1]
      exact hj
    rw [redW_frameRsp]
    have h2 := X86Backend.ImageAddrFrame.frameOkB_red hfr
    exact X86Backend.DecodeGenNode.frameSep_of_regions E.rs hreg (unren ps A) j hk _ h2.1 h2.2
  -- the checked run of the image
  have hok := X86Backend.IdxInvCheck.runIdxOk_of_idxInvCheckB hidx fn
    { prog := { base := emptiedEntry σ ps R body sa, lfn := fn }, zf := false } t rfl rfl
    (hents _) fuel hrun
  have hck' := JasminLsemMemChecked.lsemFuelMemFk_of_runIdxOk true _ fuel _ t hrun hok
  obtain ⟨f', t', hr', -⟩ :=
    X86Backend.OwnedLprogTVChecked.ownedCheckMC_sound hck fn _ t rfl rfl fuel hck'
  -- the address machine on the printed body, with its accesses
  have hcore := regionImgCoreB_of_regionImgB hgate
  unfold regionImgCoreB at hcore
  simp only [Bool.and_eq_true] at hcore
  obtain ⟨⟨⟨⟨hprW, hca⟩, hns⟩, hg0⟩, -⟩ := hcore
  set frame := frameC (baseR σ sa ps) R (frameE body sa) with hframe
  have hfrP : ∀ q ∈ bodyNamesI body,
      frame q = frameP (Params.ofBody body) (frameRsp body sa) q := by
    intro q hq
    simp only [hframe, frameC, N.body q hq]
    change X86Backend.ImageAddrFrame.frameIn body _ q = _
    unfold X86Backend.ImageAddrFrame.frameIn
    rw [ite_eq_left hq]
  have hN' := X86Backend.ImageStraightCells.cellNoSlotB_spec hns
  have hF := X86Backend.ImageStraightCells.cellFrames_of (base := baseR σ sa ps)
    (rsp := frameRsp body sa) (fr := frameE body sa) hca N.gp
    (fun r hr => by
      have := hsep.gp r hr
      simp only [hframe, frameC, hgpN r hr] at this
      exact this) hred
  have hgC : X86Backend.ImageAddrCidx.imgGateCW frame
      (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)))
      (X86Backend.ImageAddrCells.cellBody (slotArrC R (slotRen (slotArrOf σ nm) (renOf ps)))
        body) = true := by
    rw [X86Backend.ImageAddrCidx.imgGateCW_congr
      (X86Backend.ImageStraightCells.frameC_isSome (baseR σ sa ps) R body sa)]
    exact hg0
  obtain ⟨n, sA, zA, hrA, -, -, hsafe, hacc⟩ :=
    X86Backend.ImageAddrStore.image_addr_simCW'_access (body := body) hsep hphys hgC hN' hF fn
      (X86Backend.ImageAddrCellsLoop.imgStepWCond_of_gateCW _ hphys hgC fn) f' _ t'
      (entryA σ sa) false rfl (X86Backend.ImageAddrSimW.imgRelW_of hrel)
      (X86Backend.ImageAddrCidx.CidxInv.of_lpc_zero (by rw [← hrel.pc]; rfl)) hr'
  rw [X86Backend.ImageAddrFrame.runA_congr hfrP] at hrA
  rw [X86Backend.ImageAddrFrame.runSafe_congr hfrP] at hsafe hacc
  have hentry : X86Backend.DecodePrintedAddrLeak.Entry sa (entryA σ sa) := by
    refine ⟨rfl, fun r hr => ?_, rfl⟩
    have hl : (entryA σ sa).reg.lvm r = ⟨64, sa.regs (phys r)⟩ := by
      simp only [entryA, hr, ite_true]
    unfold LstateN.getW
    rw [hl]
    simp
  -- the events of the decoded run
  obtain ⟨ℓ, hℓ⟩ := runALeakG_of_runA (stepGW (frameRsp body sa) body) hrA
  obtain ⟨prog, sa', hd, hL⟩ :=
    tracedSimW_of_armLeaks hprW (fun rsp => armLeaksW (Params.ofBody body) rsp)
      sa _ _ hentry n _ ℓ hℓ hsafe
  refine ⟨prog, sa', hd, ℓ, runL_of_events hL
    (runALeakG_eventIn (fun s zf p hQ hst => ?_) n _ _ _ ℓ hℓ hacc)⟩
  have hsub := imgStores_export (nm := nm) hfr E hlen hU
  rw [← X86Backend.ImageAddrFrame.stepA_congr hfrP] at hst
  rw [← X86Backend.DecodePrintedAddrLeak.stepLeakA_congr hfrP]
  exact stepGW_eventIn hprW hfrP (fun q a ha y hy => hsub ⟨a, Or.inl ⟨q, ha⟩, hy⟩)
    (fun y hy => Or.inl (mem_wordsLocs (redW_mem_frameWords hfr sa) hy))
    ⟨fun y hy => hsub (hQ.1 y hy), fun y hy => hsub (hQ.2 y hy)⟩ hst

/-- **The back half emits bytes that access the layout only.** For a result of `regionBack`
    without linked functions, from every entry state satisfying `σ.Regions` at a valuation at
    which the program denotes, the halting run of the decoded bytes accesses `layoutMem σ sa`
    only. -/
theorem regionBack_haltsIn {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa' := by
  obtain ⟨hB, r0, r, b, cert, hr, rfl, hb, hco, -⟩ := regionBack_spec h
  rw [← legalizeRegion_denote] at hv
  obtain ⟨-, -, -, -, -, -, -, -, ⟨k, u, hu, -⟩, -⟩ :=
    regionCo_bytes_of_regionExp_virt (regionExportableB_sound hB) (regionExp_webs _ hr) hco sa V
      hV hreg fuel hv
  obtain ⟨⟨outs, himg⟩, hU⟩ := regionCoB_renImage hco
  rw [X86Backend.LprogBytes.encodeLfundefBytesChecked_eq hb]
  exact renImage_haltsIn himg hU sa hreg _ k u hu

/-- **`compileRegion` emits bytes that access the layout only**: `regionBack_haltsIn` through
    the narrow-word stages. -/
theorem compileRegion_haltsIn {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa (VIR.NarrowWords.mapVal V))
    (hreg : σ.Regions sa) (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa' := by
  obtain ⟨-, q, hq, hb⟩ := compileRegion_eq_some.mp h
  have hw := VIR.NarrowWords.narrowPrep_denote hq hv
  cases v with
  | cons x xs =>
      cases xs
      exact regionBack_haltsIn hb sa (VIR.NarrowWords.mapVal V) hV hreg fuel hw

/-- **The compiler at an entry emits bytes that access the layout only.** For a result of
    `E.compileR` without linked functions, from every entry state satisfying `σ.Regions` with a
    source run, the halting run of the decoded bytes accesses `layoutMem σ sa` only. -/
theorem compileR_haltsIn (E : NFEntry) (s : E.Src) (σ : AbiLayout) (fname : String)
    (P : Lprog) (bytes : List (BitVec 8)) (hc : E.compileR s σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa' := by
  rw [NFEntry.compileR_eq_bind] at hc
  obtain ⟨q0, hq0, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨q, hp, hJ⟩ := Option.bind_eq_some_iff.mp hc
  have hf := NFEntry.frontR_of_compileRegion hq0 hp hJ
  obtain ⟨V, fuel, x, hV, hx, -⟩ := E.toFrontLegOfR.leg σ s _ hf sa v hsep hrun
  rw [RouteProgJ.envDenote_regions_of_callFree _ fuel q (callFree_of_compileRegion hJ)] at hx
  obtain ⟨w, hw, -⟩ := Option.map_eq_some_iff.mp hx
  exact compileRegion_haltsIn hJ sa V (abiValOf_widen hV) hsep fuel hw

/-! ## 4. A program of one store -/

/-- The store of `%rdi` in the stack word `%rsp - 8`, then `ret`, accesses the memory of a
    layout whose stack range is that word only. -/
theorem haltsIn_oneStore (sa : AState) :
    HaltsIn
      (layoutMem { args := [], consts := [], result := .reg "%rax", bounds := [],
                   frameLo := -8, frameHi := -8 } sa)
      [.op (.storeMem "%rsp" (-8) (.reg "%rdi")), .ret] 0 sa
      (evalInstrA sa (.storeMem "%rsp" (-8) (.reg "%rdi"))) := by
  refine ⟨_, .op rfl ?_ (.ret rfl)⟩
  intro b o hm x hx
  simp only [instrLeak, List.mem_singleton, MLeak.mem.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  exact Or.inl (mem_wordsLocs ⟨-8, le_refl _, le_refl _, rfl⟩ hx)

end CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiPre holds_abiPre regions_iff_abiPre
  wordsLocs frameWords regionWords)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes (HaltsIn compileR_haltsIn)

/-- **The compiler theorem on a module, with the accesses of the emitted bytes.** Let the
    linked functions of `m` have distinct names (`hnd`) and each be a linked kernel (`hk`). For
    the result of `compileA` on `m`, the bytes decode to a program `prog`, and from every entry
    state `sa` satisfying `σ.Regions`, every value `v` of a source run of `m` from `sa` is read
    back by `σ`, either from a state at which `prog` halts from `sa`, with the entry stack
    register, the entry bytes outside the stack words and the pointer regions of `σ`, and every
    memory access of this run of `prog` in `layoutMem σ sa` (`HaltsIn`), or, for a program
    `pc ++ shiftProg pc.length Q` calling the region `Q` of the decoded blocks of the data `cs`
    of linked functions of `m`, from a state at which the program halts through the calls and
    from a state at which `pc` halts with its calls answered by the oracle `tabOracle`. -/
theorem haxc_correct_auto_access (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v)
    (hnd : (m.linked.map (·.name)).Nodup := by exact List.nodup_nil)
    (hk : ∀ l ∈ m.linked, LinkedKernel l := by exact fun _ h => nomatch h) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData, cs.Sublist (m.linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) := by
  obtain ⟨x, hrun', hback⟩ := haxRuns_pairStage hrun
  have hl : haxEntry.linked (pairStage m σ).1 = m.linked := pairStage_linked m σ
  obtain ⟨hlo, hhi, hrg⟩ := pairStage_frame m σ
  have hsep' := (pairStage_regions m σ sa).2 hsep
  have hc0 := hc
  unfold compileA compileARegion at hc0
  replace hc0 := (haxEntry.compileR_eq_bind _ _ _ _).symm.trans hc0
  obtain ⟨q0, hq0, hc0⟩ := Option.bind_eq_some_iff.mp hc0
  obtain ⟨p, hp, hc0⟩ := Option.bind_eq_some_iff.mp hc0
  cases hcf : p.callFree with
  | true =>
      replace hc0 := (compileRegion_of_callFree _ _ hcf _).symm.trans hc0
      have hc' : haxEntry.compileR (pairStage m σ).1 (pairStage m σ).2 fname
          = some (P, bytes) :=
        (haxEntry.compileR_eq_bind _ _ _ _).trans (Option.bind_eq_some_iff.mpr
          ⟨q0, hq0, Option.bind_eq_some_iff.mpr ⟨p, hp, hc0⟩⟩)
      obtain ⟨prog, sa', hd, hh, hR, hsp, hkeep, -⟩ :=
        haxEntry.compileR_correct _ _ fname P bytes hc' sa hsep' x hrun'
      obtain ⟨prog', sa'', hd', hA⟩ :=
        compileR_haltsIn haxEntry _ _ fname P bytes hc' sa hsep' x hrun'
      obtain rfl := Option.some.inj (hd.symm.trans hd')
      rw [hlo, hhi, hrg] at hkeep
      rw [layoutMem_pairStage] at hA
      exact ⟨prog, hd, .inl ⟨sa', hh, hback _ hR, hsp, hkeep, hA.of_halts hh⟩⟩
  | false =>
      obtain ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, hdec, ⟨sa', hC, hR⟩, sa'', hO, hR'⟩ :=
        haxEntry.call_halts_multi (hl ▸ hnd) (hl ▸ hk) hq0 hp hcf hc0 sa hsep' x hrun'
      rw [hl] at hsub
      exact ⟨_, hdec, .inr ⟨cs, hsub, hne, hndc, pc, Q, k, q, hq, hQ, hB, rfl,
        ⟨sa', hC, hback _ hR⟩, sa'', hO, hback _ hR'⟩⟩

/-- **The emitted bytes access only the memory the precondition owns.** For the result of
    `compileA` on a module `m` with `m.linked = []` and the program `prog` its bytes decode to,
    from every entry state `sa` satisfying the precondition `abiPre σ rv` with a source run of
    `m` to a value, `prog` halts and every memory access of each step of its run lies in
    `abiMem σ rv`. -/
theorem haxc_safe_bytes (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (prog : List RInstr) (hd : decodeLprog bytes = some prog)
    (rv : String → BitVec 64) (sa : AState) (hpre : (abiPre σ rv).holds sa)
    (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v) :
    ∃ sa', HaltsIn (abiMem σ rv) prog 0 sa sa' := by
  have hregs := ((holds_abiPre σ rv sa).1 hpre).1
  obtain ⟨prog', hd', ⟨sa', -, -, -, -, hA⟩ | ⟨cs, hsub, hne, -⟩⟩ :=
    haxc_correct_auto_access m σ fname P bytes hc sa ((regions_iff_abiPre σ sa).2 ⟨rv, hpre⟩) v
      hrun (by simp [hlink]) (by simp [hlink])
  · obtain rfl := Option.some.inj (hd.symm.trans hd')
    exact ⟨sa', hA.mono (layoutMem_subset_abiMem hregs)⟩
  · exact absurd (by simpa [hlink] using hsub) hne

/-- **The compiler contract with the accesses of the emitted bytes.** For the result of
    `compileA` on a module `m` with `m.linked = []`, the program decoded from the bytes meets
    `exportSpec σ m`, and from every state satisfying the precondition at the entry register
    values `rv` it halts and accesses `abiMem σ rv` only (`haxc_safe_bytes`). -/
theorem haxc_contract_safe_bytes (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA m σ fname = some (P, bytes))
    (hlink : m.linked = []) (prog : List RInstr) (hd : decodeLprog bytes = some prog) :
    SContract (fun sa (_ : Unit) sa' => Halts aMachine prog 0 sa sa') (exportSpec σ m)
      ∧ ∀ (p : (String → BitVec 64) × _root_.Hax.Value) (sa : AState),
        ((exportSpec σ m).pre p).holds sa → ∃ sa', HaltsIn (abiMem σ p.1) prog 0 sa sa' := by
  refine ⟨haxc_contract m σ fname P bytes hc hlink prog hd, ?_⟩
  rintro ⟨rv, v⟩ sa ⟨⟨⟨hA, -, hrun⟩, -⟩, -⟩
  exact haxc_safe_bytes m σ fname P bytes hc hlink prog hd rv sa hA v hrun

end CatCrypt.Crypto.SecureCompilation.Haxc
