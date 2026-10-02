/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontBodyTie

/-!
# The bytes of `mpn_and_n_loop_owned` compute the limbwise `and`

@ascent-fixture theorems: and_n_bytes_value, and_n_front_bytes_value

`LprogBytesDecodeClosed.and_n_roundtrip_closed` decodes the function bytes the encoder
lays down for the `and` loop body to `binDecoded (andMidDecoded .and_)`, and
`RInstrAddrMem.binDecoded_and_halts` runs that program on the address machine `aMachine`
as the prologue `binPrologue`, the loop `AddrMemIdx.andLoop` and the epilogue
`binEpilogue`. This module gives the loop its value through `AddrMemIdx.runXLoopA_boundedLoop`
and composes the three segments into a theorem about the bytes.

The loop value comes in two steps. The named-ref loop `andBodyNamed` over name-keyed memory
is run `n` times by `runBoundedLoop` and computes word `j` of `rp` as the `and` of words `j`
of `ap` and `bp` (`andNamedPass_boundedLoop`). `runXLoopA_boundedLoop`, instantiated at
`andLoop` with the invariant `andInv n`, relates the shipped pointer loop over address
memory to it, and the relation `LoopRel` reads the values off at the cells of the four
regions of `andRegions n` (`andLoop_value`). The bytes outside the `n` words of `rp` are
unchanged by a separate frame induction over `runXLoopA` (`runXLoopA_frame`,
`andLoop_frame`), whose one-pass case is the single store of a trip (`andBody_mem`).

The prologue is computed as a store segment, whose memory is `prologueMem` (the ten stack
words from `frameBase sa - 16`), and a load segment; the epilogue reloads the callee-saved
registers and releases the frame. The layout hypothesis `AndNLayout` places the three
arrays and the ten stack words disjointly in the address space and gives
`RegionsDisjoint` for the entry pointers `entryP sa`.

The bytes are `encodeLfundefBytes` of the literal body `binLoopBody (andMid "AND:64"
"SHL:0:64") "SHL:0:64"`: the encoder's output, not the crate's assembled object.
`MpnLoopFrontBodyTie.and_n_front_roundtrip` ties that literal to the body the front
compiles into `MpnLoopFrontEmit.andLprog`.

## Main results

* `andNamedPass_boundedLoop`: `n` passes of the named-ref loop compute the `and` of the
  words `i ≤ j < i + n` and change no other cell.
* `andLoop_value`: `runXLoopA fuel sa andLoop` exits, for `1 ≤ n ≤ fuel`, `n < 2^64`, in a
  state whose `rp` words hold the `and`, whose other region words are unchanged and whose
  bytes outside `rp` are unchanged; the hypotheses on `sa` are its registers `%rax`, `%rdi`,
  `%rsp` and the three stack slots.
* `binDecoded_and_value`: `run aMachine (binDecoded (andMidDecoded .and_))` from an entry
  state with `%rcx = n` and `AndNLayout` halts, with some fuel, in a state satisfying
  `AndNPost`: `%rsp` and the callee-saved registers restored, the `and` in `rp`, every
  other byte outside the frame unchanged.
* `and_n_bytes_value`: every program `andNBytes` decodes to computes the `and` in that
  sense; `and_n_front_bytes_value` states it for the body the front compiles.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.AndNBytesValue

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll (runBoundedLoop
  runBoundedLoop_zero runBoundedLoop_succ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr binDecoded
  andMidDecoded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem

/-! ## 1. The named-ref loop over name-keyed memory -/

/-- The registers the trip `andBodyNamed` writes. -/
def andWritten : List String :=
  ["%rsi", "%r14", "%rbp", "%r8", "%r9", "%rbx", "%rax", "%rdi"]

/-- One trip of `andBodyNamed`: `%rax` steps up, `%rdi` steps down, the other registers
    outside `andWritten` keep their values, and the memory changes in one cell: word
    `%rax` of `rp` takes the `and` of words `%rax` of `ap` and `bp`. -/
theorem andBodyNamed_run (s : JState 64) :
    let s' := runBlock s andBodyNamed
    s'.regs "%rax" = s.regs "%rax" + 1 ∧ s'.regs "%rdi" = s.regs "%rdi" - 1 ∧
      (∀ r, r ∉ andWritten → s'.regs r = s.regs r) ∧
      (∀ b o, s'.mem b o =
        if b = "rp" ∧ o = 8 * ((s.regs "%rax").toNat : Int)
        then s.mem "ap" (8 * ((s.regs "%rax").toNat : Int))
          &&& s.mem "bp" (8 * ((s.regs "%rax").toNat : Int))
        else s.mem b o) := by
  intro s'
  simp +decide only [s', andBodyNamed, andWritten, runBlock_cons, runBlock_nil, evalInstr,
    JState.setReg, JState.writeB5W, JState.writeB5, JState.store, JState.storeIdx,
    JState.loadIdx, JState.load, JState.get, JOperand.eval, x86_MOV, x86_AND, x86_ADD, x86_SUB,
    x86_CMP, rflags_of_bwop, rflags_of_aluop, List.mem_cons, List.not_mem_nil, or_false,
    not_or, if_true, if_false, Nat.cast_ofNat]
  refine ⟨rfl, rfl, ?_, fun _ _ => trivial⟩
  intro r hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
  simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- The pass of the named-ref loop: the trip `andBodyNamed` and the counter compare. -/
def andNamedPass : List (JInstr 64) := andBodyNamed ++ [XLoop.cmpInstr andLoop]

theorem canonLoop_andLoop_pass :
    (canonLoop andBank andA andLoop).body ++ [(canonLoop andBank andA andLoop).cmpInstr]
      = andNamedPass := by
  have hc : canonLoop andBank andA andLoop = { andLoop with body := andBodyNamed } := by
    simp only [canonLoop, andLoop_canon]
  rw [hc]
  rfl

theorem canonLoop_andLoop_body : (canonLoop andBank andA andLoop).body = andBodyNamed := by
  have hc : canonLoop andBank andA andLoop = { andLoop with body := andBodyNamed } := by
    simp only [canonLoop, andLoop_canon]
  rw [hc]

/-- The registers and memory after a pass are those after the trip. -/
theorem andNamedPass_run (s : JState 64) :
    (runBlock s andNamedPass).regs = (runBlock s andBodyNamed).regs ∧
      (runBlock s andNamedPass).mem = (runBlock s andBodyNamed).mem := by
  simp only [andNamedPass, runBlock_append, runBlock_cons, runBlock_nil, XLoop.cmpInstr,
    evalInstr, JState.writeB5, and_self]

/-- **The named-ref loop computes the `and`.** `k` passes from a state whose index `%rax`
    is `i`, with `i + k < 2^64`: the index ends at `i + k`, the counter steps down by `k`,
    the registers outside `andWritten` keep their values, the words `i ≤ j < i + k` of `rp`
    hold the `and` of the words of `ap` and `bp`, and every other cell keeps its value. -/
theorem andNamedPass_boundedLoop (k : Nat) :
    ∀ (i : Nat) (s : JState 64), s.regs "%rax" = BitVec.ofNat 64 i → i + k < 2 ^ 64 →
      let s' := runBoundedLoop s k andNamedPass
      s'.regs "%rax" = BitVec.ofNat 64 (i + k) ∧
        s'.regs "%rdi" = s.regs "%rdi" - BitVec.ofNat 64 k ∧
        (∀ r, r ∉ andWritten → s'.regs r = s.regs r) ∧
        (∀ j : Nat, i ≤ j → j < i + k →
          s'.mem "rp" (8 * (j : Int)) = s.mem "ap" (8 * (j : Int)) &&& s.mem "bp" (8 * (j : Int))) ∧
        (∀ o : Int, (∀ j : Nat, i ≤ j → j < i + k → o ≠ 8 * (j : Int)) →
          s'.mem "rp" o = s.mem "rp" o) ∧
        (∀ b o, b ≠ "rp" → s'.mem b o = s.mem b o) := by
  induction k with
  | zero =>
    intro i s hi _ s'
    have hs' : s' = s := rfl
    rw [hs']
    refine ⟨by rw [Nat.add_zero]; exact hi, by simp, fun _ _ => rfl, fun j h1 h2 => by omega,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ k ih =>
    intro i s hi hik s'
    obtain ⟨hrax, hrdi, hreg, hmem⟩ := andBodyNamed_run s
    obtain ⟨preg, pmem⟩ := andNamedPass_run s
    have hi' : (runBlock s andNamedPass).regs "%rax" = BitVec.ofNat 64 (i + 1) := by
      rw [preg, hrax, hi, BitVec.ofNat_add]; rfl
    have htoNat : (s.regs "%rax").toNat = i := by
      rw [hi, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨irax, irdi, ireg, icell, iframe, ibank⟩ :=
      ih (i + 1) (runBlock s andNamedPass) hi' (by omega)
    have hs' : s' = runBoundedLoop (runBlock s andNamedPass) k andNamedPass := rfl
    rw [hs']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [irax]; congr 1; omega
    · rw [irdi, preg, hrdi, BitVec.ofNat_add, sub_sub, add_comm]; rfl
    · intro r hr
      rw [ireg r hr, preg, hreg r hr]
    · intro j h1 h2
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · rw [iframe _ (fun j' h1' _ => by omega), pmem, hmem, htoNat]
        simp
      · rw [icell j hlt (by omega), pmem, hmem "ap", hmem "bp"]
        simp +decide
    · intro o ho
      have hc : ¬ ("rp" = "rp" ∧ o = 8 * ((s.regs "%rax").toNat : Int)) :=
        fun h => ho i le_rfl (by omega) (htoNat ▸ h.2)
      rw [iframe o (fun j h1 h2 => ho j (by omega) (by omega)), pmem, hmem, if_neg hc]
    · intro b o hb
      have hc : ¬ (b = "rp" ∧ o = 8 * ((s.regs "%rax").toNat : Int)) := fun h => hb h.1
      rw [ibank b o hb, pmem, hmem, if_neg hc]

/-! ## 2. The shipped loop over address memory -/

/-- The footprint of the named-ref trip lies in the stack region. -/
theorem andLoop_footprint_cells (n : Nat) :
    ∀ k ∈ footprint (canonFromI andBank andA [] andLoop.body), regionCells (andRegions n) k := by
  rw [andLoop_canon, andLoop_footprint]
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 7, by decide, by decide⟩
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 0, by decide, by decide⟩
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 8, by decide, by decide⟩

/-- The tracked cells of `andA` lie in the stack region. -/
theorem andA_cellKeys_cells (n : Nat) :
    ∀ k ∈ andA.cellKeys, regionCells (andRegions n) k := by
  intro k hk
  simp only [DState.cellKeys, andA, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 8, by decide, by decide⟩
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 7, by decide, by decide⟩
  · exact ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, 0, by decide, by decide⟩

/-- `andA` holds at an address state whose `%rsp` is the stack base `P "%rsp"`. -/
theorem andA_regInv (P : String → BitVec 64) (R : String → BitVec 64)
    (hrsp : R "%rsp" = P "%rsp") : RegInvD andBank P andA R := by
  intro r v h
  simp only [DState.get, andA, lookupR] at h
  by_cases hr : r = "%rsp"
  · subst hr
    simp only [if_true, Option.some.injEq] at h
    subst h
    simp [AVal.denote, basePtr, andBank, hrsp]
  · simp [hr] at h

/-- `andA` holds at a memory whose stack slots `56`, `48` and `-8` hold the bases of `rp`,
    `ap` and `bp`. -/
theorem andA_cellInv (P : String → BitVec 64) (m : AMem)
    (h56 : read64 m (P "%rsp" + BitVec.ofInt 64 56) = P "%rdi")
    (h48 : read64 m (P "%rsp" + BitVec.ofInt 64 48) = P "%rsi")
    (hm8 : read64 m (P "%rsp" + BitVec.ofInt 64 (-8)) = P "%rdx") :
    CellInvD andBank P andA m := by
  intro c v h
  simp only [andA, lookupC] at h
  split at h
  · rename_i hc; cases h; subst hc; simpa [keyAddr, basePtr, andBank, AVal.denote] using h56
  · split at h
    · rename_i hc; cases h; subst hc; simpa [keyAddr, basePtr, andBank, AVal.denote] using h48
    · split at h
      · rename_i hc; cases h; subst hc
        simpa [keyAddr, basePtr, andBank, AVal.denote] using hm8
      · cases h

/-- Word `i < n` of the `rp` region. -/
theorem rp_cell (n i : Nat) (hi : i < n) : regionCells (andRegions n) ("rp", 8 * (i : Int)) :=
  ⟨⟨"rp", 0, n⟩, by simp [andRegions], rfl, i, hi, by simp⟩

/-- Stack word `o = -8 + 8 j`, `j < 9`, of the stack region. -/
theorem stack_cell (n : Nat) (o : Int) (j : Nat) (hj : j < 9) (ho : o = -8 + 8 * (j : Int)) :
    regionCells (andRegions n) ("%rsp", o) :=
  ⟨⟨"%rsp", -8, 9⟩, by simp [andRegions], rfl, j, hj, ho⟩

theorem ofNat64_ne_zero (n : Nat) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  simp at this
  omega

/-- `andInv n` at the loop entry: index `0`, counter `n ≥ 1`. -/
theorem andInv_entry (n : Nat) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64) (sa : AState)
    (hrax : sa.regs "%rax" = 0) (hrdi : sa.regs "%rdi" = BitVec.ofNat 64 n) : andInv n sa := by
  refine ⟨?_, ?_⟩
  · rw [hrax, hrdi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; simp
  · rw [hrdi]; exact ofNat64_ne_zero n hn1 hn

/-! ## 3. The prologue and the epilogue -/

/-- The stack pointer after the prologue's frame allocation. -/
def frameBase (sa : AState) : BitVec 64 := sa.regs "%rsp" + BitVec.ofInt 64 (-64)

/-- The memory after the prologue: the ten stack words from `frameBase sa - 16` hold, from
    the top, the entry values of `%rdi`, `%rsi`, `%rbx`, `%rbp`, `%r12`, `%r13`, `%r14`,
    `%r15`, `%rdx` and `%rcx`. -/
def prologueMem (sa : AState) : AMem :=
  write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64
    sa.mem (frameBase sa + BitVec.ofInt 64 56) (sa.regs "%rdi"))
    (frameBase sa + BitVec.ofInt 64 48) (sa.regs "%rsi"))
    (frameBase sa + BitVec.ofInt 64 40) (sa.regs "%rbx"))
    (frameBase sa + BitVec.ofInt 64 32) (sa.regs "%rbp"))
    (frameBase sa + BitVec.ofInt 64 24) (sa.regs "%r12"))
    (frameBase sa + BitVec.ofInt 64 16) (sa.regs "%r13"))
    (frameBase sa + BitVec.ofInt 64 8) (sa.regs "%r14"))
    (frameBase sa + BitVec.ofInt 64 0) (sa.regs "%r15"))
    (frameBase sa + BitVec.ofInt 64 (-8)) (sa.regs "%rdx"))
    (frameBase sa + BitVec.ofInt 64 (-16)) (sa.regs "%rcx")

/-- The registers the prologue writes. -/
def prologueWritten : List String := ["%rsp", "%r14", "%rbx", "%rcx", "%rsi", "%rax", "%rdi"]

/-- The store segment of the prologue: the frame allocation, the eight callee-saved and
    argument stores, the copy of `%rsi` and the two argument spills. -/
def prologueStores : List (JInstr 64) := binPrologue.take 12

/-- The load segment of the prologue: the reloads, the zero index and the count compare. -/
def prologueLoads : List (JInstr 64) := binPrologue.drop 12

theorem binPrologue_split : binPrologue = prologueStores ++ prologueLoads :=
  (List.take_append_drop 12 binPrologue).symm

theorem evalInstrA_storeMem_reg (sa : AState) (b : String) (o : Int) (r : String) :
    (evalInstrA sa (.storeMem b o (.reg r))).regs = sa.regs ∧
      (evalInstrA sa (.storeMem b o (.reg r))).flags = sa.flags ∧
      (evalInstrA sa (.storeMem b o (.reg r))).mem
        = write64 sa.mem (sa.regs b + BitVec.ofInt 64 o) (sa.regs r) :=
  ⟨rfl, rfl, rfl⟩

theorem evalInstrA_loadMem (sa : AState) (d b : String) (o : Int) :
    (evalInstrA sa (.loadMem d b o)).regs
        = (fun r => if r = d then read64 sa.mem (sa.regs b + BitVec.ofInt 64 o) else sa.regs r) ∧
      (evalInstrA sa (.loadMem d b o)).flags = sa.flags ∧
      (evalInstrA sa (.loadMem d b o)).mem = sa.mem :=
  ⟨rfl, rfl, rfl⟩

theorem evalInstrA_mov_reg (sa : AState) (d s : String) :
    (evalInstrA sa (.mov d (.reg s))).regs = (fun r => if r = d then sa.regs s else sa.regs r) ∧
      (evalInstrA sa (.mov d (.reg s))).flags = sa.flags ∧
      (evalInstrA sa (.mov d (.reg s))).mem = sa.mem :=
  ⟨rfl, rfl, rfl⟩

theorem evalInstrA_mov_imm (sa : AState) (d : String) (v : Nat) :
    (evalInstrA sa (.mov d (.imm v))).regs
        = (fun r => if r = d then BitVec.ofNat 64 v else sa.regs r) ∧
      (evalInstrA sa (.mov d (.imm v))).flags = sa.flags ∧
      (evalInstrA sa (.mov d (.imm v))).mem = sa.mem :=
  ⟨rfl, rfl, rfl⟩

theorem evalInstrA_lea_self (sa : AState) (d : String) (o : Int) :
    (evalInstrA sa (.lea d d d 0 o)).regs
        = (fun r => if r = d then sa.regs d + BitVec.ofInt 64 o else sa.regs r) ∧
      (evalInstrA sa (.lea d d d 0 o)).flags = sa.flags ∧
      (evalInstrA sa (.lea d d d 0 o)).mem = sa.mem := by
  refine ⟨?_, rfl, rfl⟩
  funext r
  simp only [evalInstrA, evalInstr, JState.setReg, x86_LEA, AState.view, JState.get,
    BitVec.mul_zero, BitVec.add_zero]

theorem evalInstrA_storeMemIdx_reg (sa : AState) (b x : String) (sc : Nat) (r : String) :
    (evalInstrA sa (.storeMemIdx b x sc (.reg r))).regs = sa.regs ∧
      (evalInstrA sa (.storeMemIdx b x sc (.reg r))).mem
        = write64 sa.mem (sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs x).toNat : Nat) : Int))
            (sa.regs r) :=
  ⟨rfl, rfl⟩

theorem evalInstrA_loadMemIdx (sa : AState) (d b x : String) (sc : Nat) :
    (evalInstrA sa (.loadMemIdx d b x sc)).regs
        = (fun r => if r = d
            then read64 sa.mem (sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs x).toNat : Nat) : Int))
            else sa.regs r) ∧
      (evalInstrA sa (.loadMemIdx d b x sc)).mem = sa.mem :=
  ⟨rfl, rfl⟩

theorem evalInstrA_and_reg (sa : AState) (d s : String) :
    (evalInstrA sa (.and_ d (.reg s))).regs
        = (fun r => if r = d then sa.regs d &&& sa.regs s else sa.regs r) ∧
      (evalInstrA sa (.and_ d (.reg s))).mem = sa.mem :=
  ⟨rfl, rfl⟩

theorem evalInstrA_add_imm (sa : AState) (d : String) (v : Nat) :
    (evalInstrA sa (.add d (.imm v))).regs
        = (fun r => if r = d then sa.regs d + BitVec.ofNat 64 v else sa.regs r) ∧
      (evalInstrA sa (.add d (.imm v))).mem = sa.mem :=
  ⟨rfl, rfl⟩

theorem evalInstrA_sub_imm (sa : AState) (d : String) (v : Nat) :
    (evalInstrA sa (.sub d (.imm v))).regs
        = (fun r => if r = d then sa.regs d - BitVec.ofNat 64 v else sa.regs r) ∧
      (evalInstrA sa (.sub d (.imm v))).mem = sa.mem :=
  ⟨rfl, rfl⟩

theorem evalInstrA_cmp_reg (sa : AState) (d s : String) :
    (evalInstrA sa (.cmp d (.reg s))).regs = sa.regs ∧
      (evalInstrA sa (.cmp d (.reg s))).mem = sa.mem :=
  ⟨rfl, rfl⟩

theorem evalInstrA_cmp_zero (sa : AState) (d : String) :
    (evalInstrA sa (.cmp d (.imm 0))).regs = sa.regs ∧
      (evalInstrA sa (.cmp d (.imm 0))).mem = sa.mem ∧
      (evalInstrA sa (.cmp d (.imm 0))).view.flagB (·.zf) = decide (sa.regs d = 0) := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [evalInstrA, AState.view, evalInstr, JState.writeB5, JState.flagB, x86_CMP,
    x86_SUB, ZF_of_word, JOperand.eval, JState.get, Option.getD_some]
  simp [BitVec.toNat_eq]

/-- The store segment: the frame is allocated, `%r14` takes the entry `%rsi`, the other
    registers keep their values, the flags are unchanged and the memory is `prologueMem`. -/
theorem prologueStores_run (sa : AState) :
    (runBlockA sa prologueStores).regs
        = (fun r => if r = "%r14" then sa.regs "%rsi"
            else if r = "%rsp" then frameBase sa else sa.regs r) ∧
      (runBlockA sa prologueStores).flags = sa.flags ∧
      (runBlockA sa prologueStores).mem = prologueMem sa := by
  have e : prologueStores =
      [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
      , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
      , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
      , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
      , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
      , .mov "%r14" (.reg "%rsi")
      , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx") ] := rfl
  rw [e]
  simp +decide only [runBlockA_cons, runBlockA_nil, evalInstrA_storeMem_reg,
    evalInstrA_mov_reg, evalInstrA_lea_self, if_false, ite_true, prologueMem, frameBase,
    and_self]

/-- A read at displacement `o'` from a base sees through a write at displacement `o` from
    the same base when the displacements are at least eight apart. -/
theorem read64_write64_ofInt (m : AMem) (p : BitVec 64) (o o' : Int) (v : BitVec 64)
    (h : 8 ≤ (o - o').natAbs) (h' : (o - o').natAbs ≤ 2 ^ 64 - 8) :
    read64 (write64 m (p + BitVec.ofInt 64 o) v) (p + BitVec.ofInt 64 o')
      = read64 m (p + BitVec.ofInt 64 o') :=
  read64_write64_of_disjoint _ _ _ _ (disjoint8_add_ofInt p o o' h h')

/-- The stack words of `prologueMem` read back the entry registers. -/
theorem prologueMem_reads (sa : AState) :
    read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 56) = sa.regs "%rdi" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 48) = sa.regs "%rsi" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 40) = sa.regs "%rbx" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 32) = sa.regs "%rbp" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 24) = sa.regs "%r12" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 16) = sa.regs "%r13" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 8) = sa.regs "%r14" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 0) = sa.regs "%r15" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 (-8)) = sa.regs "%rdx" ∧
      read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 (-16)) = sa.regs "%rcx" := by
  simp +decide only [prologueMem, read64_write64_ofInt, read64_write64_same, and_self]

/-- The load segment from a state whose memory is `prologueMem sa` and whose `%rsp` is the
    frame base. -/
theorem prologueLoads_run (sa s : AState) (hm : s.mem = prologueMem sa)
    (hsp : s.regs "%rsp" = frameBase sa) :
    let s1 := runBlockA s prologueLoads
    s1.mem = s.mem ∧ s1.regs "%rdi" = sa.regs "%rcx" ∧ s1.regs "%rax" = 0 ∧
      s1.regs "%rbx" = sa.regs "%rdi" ∧ s1.regs "%rsi" = sa.regs "%rcx" ∧
      s1.regs "%rcx" = sa.regs "%rsi" ∧
      (∀ r, r ∉ ["%rdi", "%rax", "%rbx", "%rsi", "%rcx"] → s1.regs r = s.regs r) ∧
      s1.view.flagB (·.zf) = decide (sa.regs "%rcx" = 0) := by
  intro s1
  have e : prologueLoads =
      [ .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48
      , .loadMem "%rsi" "%rsp" (-16)
      , .mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0)
      , .mov "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0) ] := rfl
  obtain ⟨r56, r48, -, -, -, -, -, -, -, rm16⟩ := prologueMem_reads sa
  simp +decide only [s1, e, runBlockA_cons, runBlockA_nil, evalInstrA_loadMem,
    evalInstrA_mov_reg, evalInstrA_mov_imm, evalInstrA_cmp_zero, if_false, ite_true, hm, hsp,
    r56, r48, rm16, List.mem_cons, List.not_mem_nil, or_false, not_or, true_and, and_true]
  intro r hr
  obtain ⟨h1, h2, h3, h4, h5⟩ := hr
  simp [h1, h2, h3, h4, h5]

/-- The displacements of the ten stack words the prologue writes, from the frame base. -/
def stackOffsets : List Int := [56, 48, 40, 32, 24, 16, 8, 0, -8, -16]

/-- A byte in none of the ten stack words keeps its value through the prologue. -/
theorem prologueMem_frame (sa : AState) (x : BitVec 64)
    (hx : ∀ o ∈ stackOffsets, ¬ InRange8 (frameBase sa + BitVec.ofInt 64 o) x) :
    prologueMem sa x = sa.mem x := by
  simp only [stackOffsets, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hx
  simp only [prologueMem, write64_of_not_inRange _ _ _ _ h1, write64_of_not_inRange _ _ _ _ h2,
    write64_of_not_inRange _ _ _ _ h3, write64_of_not_inRange _ _ _ _ h4,
    write64_of_not_inRange _ _ _ _ h5, write64_of_not_inRange _ _ _ _ h6,
    write64_of_not_inRange _ _ _ _ h7, write64_of_not_inRange _ _ _ _ h8,
    write64_of_not_inRange _ _ _ _ h9, write64_of_not_inRange _ _ _ _ h10]

/-- The epilogue: the memory is unchanged, the six callee-saved registers reload from the
    stack words `40` to `0`, `%rsp` moves up by the frame, and the other registers keep
    their values. -/
theorem binEpilogue_run (s : AState) :
    let s' := runBlockA s binEpilogue
    s'.mem = s.mem ∧ s'.regs "%rsp" = s.regs "%rsp" + BitVec.ofInt 64 64 ∧
      s'.regs "%rbx" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 40) ∧
      s'.regs "%rbp" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 32) ∧
      s'.regs "%r12" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 24) ∧
      s'.regs "%r13" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 16) ∧
      s'.regs "%r14" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 8) ∧
      s'.regs "%r15" = read64 s.mem (s.regs "%rsp" + BitVec.ofInt 64 0) ∧
      (∀ r, r ∉ ["%rsp", "%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15"] →
        s'.regs r = s.regs r) := by
  intro s'
  simp +decide only [s', binEpilogue, runBlockA_cons, runBlockA_nil, evalInstrA_loadMem,
    evalInstrA_lea_self, if_false, ite_true, List.mem_cons, List.not_mem_nil, or_false,
    not_or, true_and]
  intro r hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  simp [h1, h2, h3, h4, h5, h6, h7]

/-! ## 4. The frame of the loop -/

/-- The word `%rax` of the array whose base is in stack slot `o`, read from `sa`. -/
def slotWord (sa : AState) (o : Int) : BitVec 64 :=
  read64 sa.mem (read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 o)
    + BitVec.ofInt 64 (8 * ((sa.regs "%rax").toNat : Int)))

/-- The memory after a trip of the shipped loop: one word written, word `%rax` of the array
    based in stack slot `56`, holding the `and` of words `%rax` of the arrays based in slots
    `48` and `-8`. -/
theorem andBody_mem (sa : AState) :
    (runBlockA sa andLoop.body).mem
      = write64 sa.mem (read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 56)
          + BitVec.ofInt 64 (8 * ((sa.regs "%rax").toNat : Int)))
          (slotWord sa 48 &&& slotWord sa (-8)) := by
  simp +decide only [andLoop, slotWord, runBlockA_cons, runBlockA_nil, evalInstrA_loadMem,
    evalInstrA_loadMemIdx, evalInstrA_mov_reg, evalInstrA_storeMemIdx_reg, evalInstrA_and_reg,
    evalInstrA_add_imm, evalInstrA_sub_imm, evalInstrA_cmp_reg, if_false, ite_true,
    Nat.cast_mul, Nat.cast_ofNat]

/-- The memory after a pass is the memory after the trip. -/
theorem passA_andLoop_mem (sa : AState) :
    (passA andLoop sa).mem = (runBlockA sa andLoop.body).mem := by
  rw [passA, runBlockA_append]
  exact (evalInstrA_cmp_zero _ _).2.1

/-- **Frame of a counted loop.** Under a predicate `Q` preserved by every pass after which
    the loop continues, a byte satisfying `F` that no pass from a `Q`-state changes is
    unchanged by the loop. -/
theorem runXLoopA_frame (l : XLoop 64) (Q : AState → Prop) (F : BitVec 64 → Prop)
    (hQ : ∀ sa, Q sa → (passA l sa).view.flagB (·.zf) = false → Q (passA l sa))
    (hF : ∀ sa, Q sa → ∀ x, F x → (passA l sa).mem x = sa.mem x) :
    ∀ (fuel : Nat) (sa sa' : AState), Q sa → runXLoopA fuel sa l = some sa' →
      ∀ x, F x → sa'.mem x = sa.mem x := by
  intro fuel
  induction fuel with
  | zero => intro sa sa' _ h; cases h
  | succ f ih =>
    intro sa sa' hq h x hx
    simp only [runXLoopA] at h
    split at h
    · cases h; exact hF sa hq x hx
    · rename_i hz
      rw [ih (passA l sa) sa' (hQ sa hq (by simpa using hz)) h x hx, hF sa hq x hx]

/-- The bytes outside the `n` words of `rp`. -/
def OutsideRp (rp : BitVec 64) (n : Nat) (x : BitVec 64) : Prop :=
  ∀ i < n, ¬ InRange8 (rp + BitVec.ofInt 64 (8 * (i : Int))) x

/-- **Frame of the shipped loop.** From a state under `andInv n` related by `LoopRel` to a
    name-keyed state, the loop changes no byte outside the `n` words of `rp`. -/
theorem andLoop_frame (P : String → BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hR : RegionsDisjoint andBank P (andRegions n)) (fuel : Nat) (sa sa' : AState)
    (js : JState 64) (hI : andInv n sa)
    (hrel : LoopRel andBank P (regionCells (andRegions n)) andA sa js)
    (hrun : runXLoopA fuel sa andLoop = some sa') :
    ∀ x, OutsideRp (P "%rdi") n x → sa'.mem x = sa.mem x := by
  refine runXLoopA_frame andLoop
    (fun sa => andInv n sa ∧ ∃ js, LoopRel andBank P (regionCells (andRegions n)) andA sa js)
    (OutsideRp (P "%rdi") n) ?_ ?_ fuel sa sa' ⟨hI, js, hrel⟩ hrun
  · rintro sa ⟨hI, js, hrel⟩ hz
    exact ⟨andLoop_inv n hn sa hI hz, _, passA_sim andBank P _ (sepOn_regionCells _ _ _ hR)
      andA andLoop andLoop_disciplined (andLoop_footprint_cells n) andLoop_entails sa js
      (andLoop_idx n sa hI) hrel⟩
  · rintro sa ⟨⟨hs, hnz⟩, js, -, -, hreg, hcell, -, -⟩ x hx
    have hrsp : sa.regs "%rsp" = P "%rsp" := by
      have := hreg "%rsp" (.ptr "%rsp" 0) rfl
      simpa [AVal.denote, basePtr, andBank] using this
    have h56 : read64 sa.mem (P "%rsp" + BitVec.ofInt 64 56) = P "%rdi" := by
      have := hcell ("%rsp", 56) (.ptr "rp" 0) rfl
      simpa [keyAddr, basePtr, andBank, AVal.denote] using this
    have hlt : (sa.regs "%rax").toNat < n := by
      have hpos : 0 < (sa.regs "%rdi").toNat := by
        rcases Nat.eq_zero_or_pos (sa.regs "%rdi").toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hnz
        · exact h
      omega
    rw [passA_andLoop_mem, andBody_mem, hrsp, h56]
    exact write64_of_not_inRange _ _ _ _ (hx _ hlt)

/-- **The shipped `and` loop computes the `and`.** From an address state whose index `%rax`
    is `0`, whose counter `%rdi` is `n` with `1 ≤ n < 2^64`, whose `%rsp` is the stack base
    `P "%rsp"`, and whose stack slots `56`, `48` and `-8` hold the bases `P "%rdi"`,
    `P "%rsi"` and `P "%rdx"` of `rp`, `ap` and `bp`, with the three arrays of `n` words
    and the nine stack words from `-8` pairwise disjoint, `runXLoopA` with fuel at least
    `n` exits in a state where `%rax = n`, `%rdi = 0`, the registers outside `andWritten`
    are unchanged, word `i < n` of `rp` is the `and` of words `i` of `ap` and `bp`, every
    other word of the four regions is unchanged, and every byte outside the `n` words of
    `rp` is unchanged. -/
theorem andLoop_value (P : String → BitVec 64) (n : Nat) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hR : RegionsDisjoint andBank P (andRegions n)) (fuel : Nat) (hfuel : n ≤ fuel)
    (sa : AState) (hrax : sa.regs "%rax" = 0) (hrdi : sa.regs "%rdi" = BitVec.ofNat 64 n)
    (hrsp : sa.regs "%rsp" = P "%rsp")
    (h56 : read64 sa.mem (P "%rsp" + BitVec.ofInt 64 56) = P "%rdi")
    (h48 : read64 sa.mem (P "%rsp" + BitVec.ofInt 64 48) = P "%rsi")
    (hm8 : read64 sa.mem (P "%rsp" + BitVec.ofInt 64 (-8)) = P "%rdx") :
    ∃ sa', runXLoopA fuel sa andLoop = some sa' ∧
      sa'.regs "%rax" = BitVec.ofNat 64 n ∧ sa'.regs "%rdi" = 0 ∧
      (∀ r, r ∉ andWritten → sa'.regs r = sa.regs r) ∧
      (∀ i < n, read64 sa'.mem (P "%rdi" + BitVec.ofInt 64 (8 * (i : Int))) =
        read64 sa.mem (P "%rsi" + BitVec.ofInt 64 (8 * (i : Int)))
          &&& read64 sa.mem (P "%rdx" + BitVec.ofInt 64 (8 * (i : Int)))) ∧
      (∀ k, regionCells (andRegions n) k → k.1 ≠ "rp" →
        read64 sa'.mem (keyAddr andBank P k) = read64 sa.mem (keyAddr andBank P k)) ∧
      (∀ x, OutsideRp (P "%rdi") n x → sa'.mem x = sa.mem x) := by
  have hI : andInv n sa := andInv_entry n hn1 hn sa hrax hrdi
  have hrel := loopRel_jOfD andBank P (regionCells (andRegions n)) andA sa
    (andA_regInv P sa.regs hrsp) (andA_cellInv P sa.mem h56 h48 hm8) (andA_cellKeys_cells n)
  have hdec : ∀ s : JState 64,
      (runBlock s (canonLoop andBank andA andLoop).body).get andLoop.ctr
        = s.get andLoop.ctr - 1 := by
    intro s
    rw [canonLoop_andLoop_body]
    exact (andBodyNamed_run s).2.1
  obtain ⟨sa', hrun, hrel'⟩ := runXLoopA_boundedLoop andBank P (regionCells (andRegions n))
    (sepOn_regionCells _ _ _ hR) andA andLoop andLoop_disciplined (andLoop_footprint_cells n)
    andLoop_entails (andInv n) (andLoop_idx n) (andLoop_inv n hn) hdec n fuel sa
    (jOfD andBank P sa) hI hrel hn1 hn hrdi hfuel
  have hframe := andLoop_frame P n hn hR fuel sa sa' _ hI hrel hrun
  rw [canonLoop_andLoop_pass] at hrel'
  obtain ⟨hregs, -, -, -, -, hK⟩ := hrel'
  obtain ⟨jrax, jrdi, jreg, jcell, -, jbank⟩ :=
    andNamedPass_boundedLoop n 0 (jOfD andBank P sa) (by simpa [jOfD] using hrax) (by omega)
  refine ⟨sa', hrun, ?_, ?_, ?_, ?_, ?_, hframe⟩
  · rw [hregs, jrax, Nat.zero_add]
  · rw [hregs, jrdi]; simp [jOfD, hrdi]
  · intro r hr
    rw [hregs, jreg r hr]; rfl
  · intro i hi
    have := hK ("rp", 8 * (i : Int)) (rp_cell n i hi)
    simp only [absMem, keyAddr, basePtr, andBank, if_true] at this
    simp only [String.reduceEq, if_false] at this
    rw [this, jcell i (Nat.zero_le i) (by omega)]
    rfl
  · intro k hk hne
    have := hK k hk
    rw [jbank k.1 k.2 hne] at this
    exact this

/-! ## 5. The decoded function -/

/-- The layout of a call `mpn_and_n(rp, ap, bp, n)` with the stack pointer `rsp`: the
    three arrays of `n` words and the ten stack words from `rsp - 80` lie in the address
    space without wrapping and are pairwise disjoint. -/
structure AndNLayout (rp ap bp rsp : BitVec 64) (n : Nat) : Prop where
  rp_fits : rp.toNat + 8 * n ≤ 2 ^ 64
  ap_fits : ap.toNat + 8 * n ≤ 2 ^ 64
  bp_fits : bp.toNat + 8 * n ≤ 2 ^ 64
  stack_fits : 80 ≤ rsp.toNat
  rp_ap : rp.toNat + 8 * n ≤ ap.toNat ∨ ap.toNat + 8 * n ≤ rp.toNat
  rp_bp : rp.toNat + 8 * n ≤ bp.toNat ∨ bp.toNat + 8 * n ≤ rp.toNat
  ap_bp : ap.toNat + 8 * n ≤ bp.toNat ∨ bp.toNat + 8 * n ≤ ap.toNat
  rp_stack : rp.toNat + 8 * n ≤ rsp.toNat - 80 ∨ rsp.toNat ≤ rp.toNat
  ap_stack : ap.toNat + 8 * n ≤ rsp.toNat - 80 ∨ rsp.toNat ≤ ap.toNat
  bp_stack : bp.toNat + 8 * n ≤ rsp.toNat - 80 ∨ rsp.toNat ≤ bp.toNat

/-- The entry pointers of the loop: `%rsp` at the frame base, the other registers at their
    function-entry values. -/
def entryP (sa : AState) : String → BitVec 64 :=
  fun r => if r = "%rsp" then frameBase sa else sa.regs r

theorem ofInt_neg64 : BitVec.ofInt 64 (-64) = 18446744073709551552#64 := by decide

theorem ofInt_neg8 : BitVec.ofInt 64 (-8) = 18446744073709551608#64 := by decide

theorem ofInt_neg16 : BitVec.ofInt 64 (-16) = 18446744073709551600#64 := by decide

theorem frameBase_toNat (sa : AState) (h : 80 ≤ (sa.regs "%rsp").toNat) :
    (frameBase sa).toNat = (sa.regs "%rsp").toNat - 64 := by
  have := (sa.regs "%rsp").isLt
  rw [frameBase, ofInt_neg64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem entryP_rsp (sa : AState) : entryP sa "%rsp" = frameBase sa := by
  simp [entryP]

theorem entryP_other (sa : AState) (r : String) (hr : r ≠ "%rsp") : entryP sa r = sa.regs r := by
  simp [entryP, hr]

theorem regionLow_ap (sa : AState) (n : Nat) :
    regionLow andBank (entryP sa) ⟨"ap", 0, n⟩ = (sa.regs "%rsi").toNat := by
  simp +decide [regionLow, basePtr, andBank, entryP_other]

theorem regionLow_bp (sa : AState) (n : Nat) :
    regionLow andBank (entryP sa) ⟨"bp", 0, n⟩ = (sa.regs "%rdx").toNat := by
  simp +decide [regionLow, basePtr, andBank, entryP_other]

theorem regionLow_rp (sa : AState) (n : Nat) :
    regionLow andBank (entryP sa) ⟨"rp", 0, n⟩ = (sa.regs "%rdi").toNat := by
  simp +decide [regionLow, basePtr, andBank, entryP_other]

theorem regionLow_stack (sa : AState) (h : 80 ≤ (sa.regs "%rsp").toNat) :
    regionLow andBank (entryP sa) ⟨"%rsp", -8, 9⟩ = (sa.regs "%rsp").toNat - 72 := by
  have := (sa.regs "%rsp").isLt
  simp +decide only [regionLow, basePtr, andBank, entryP_rsp, ite_true, if_false]
  rw [ofInt_neg8, BitVec.toNat_add, BitVec.toNat_ofNat, frameBase_toNat sa h]
  omega

/-- The regions of the loop are disjoint under the layout. -/
theorem andRegions_disjoint (sa : AState) (n : Nat)
    (hL : AndNLayout (sa.regs "%rdi") (sa.regs "%rsi") (sa.regs "%rdx") (sa.regs "%rsp") n) :
    RegionsDisjoint andBank (entryP sa) (andRegions n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hL
  have := (sa.regs "%rsp").isLt
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [andRegions, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [regionLow_ap]; dsimp only; omega
    · rw [regionLow_bp]; dsimp only; omega
    · rw [regionLow_rp]; dsimp only; omega
    · rw [regionLow_stack sa h4]; dsimp only; omega
  · intro g hg h hh hne
    simp only [andRegions, List.mem_cons, List.not_mem_nil, or_false] at hg hh
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | (refine ⟨by dsimp only; decide, ?_⟩
         simp only [regionLow_ap, regionLow_bp, regionLow_rp, regionLow_stack sa h4]
         omega)

theorem keyAddr_stack (sa : AState) (o : Int) :
    keyAddr andBank (entryP sa) ("%rsp", o) = frameBase sa + BitVec.ofInt 64 o := by
  simp [keyAddr, basePtr, andBank, entryP_rsp]

/-- The address of word `i < n` of an array of `n` words that fits in the address space. -/
theorem word_toNat (a : BitVec 64) (i n : Nat) (hi : i < n) (hfit : a.toNat + 8 * n ≤ 2 ^ 64) :
    (a + BitVec.ofInt 64 (8 * (i : Int))).toNat = a.toNat + 8 * i := by
  have e : BitVec.ofInt 64 (8 * (i : Int)) = BitVec.ofNat 64 (8 * i) := by
    rw [← BitVec.ofInt_natCast]; simp
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- A word below the frame or at or above the entry `%rsp` reads through `prologueMem`. -/
theorem prologueMem_read_outside (sa : AState) (a : BitVec 64) (h80 : 80 ≤ (sa.regs "%rsp").toNat)
    (hout : a.toNat + 8 ≤ (sa.regs "%rsp").toNat - 80 ∨ (sa.regs "%rsp").toNat ≤ a.toNat)
    (hfit : a.toNat + 8 ≤ 2 ^ 64) :
    read64 (prologueMem sa) a = read64 sa.mem a := by
  have hb := frameBase_toNat sa h80
  have := (sa.regs "%rsp").isLt
  have key : ∀ o ∈ stackOffsets, Disjoint8 (frameBase sa + BitVec.ofInt 64 o) a := by
    intro o ho
    simp only [stackOffsets, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (apply disjoint8_of_toNat <;>
        first
        | (rw [ofInt_neg8, BitVec.toNat_add, BitVec.toNat_ofNat, hb]; omega)
        | (rw [ofInt_neg16, BitVec.toNat_add, BitVec.toNat_ofNat, hb]; omega)
        | (rw [BitVec.toNat_add, BitVec.toNat_ofInt, hb]; omega)
        | omega)
  simp only [prologueMem, read64_write64_of_disjoint _ _ _ _ (key 56 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 48 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 40 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 32 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 24 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 16 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 8 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key 0 (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key (-8) (by decide)),
    read64_write64_of_disjoint _ _ _ _ (key (-16) (by decide))]

/-- The postcondition of `mpn_and_n(rp, ap, bp, n)` on the address machine, from the entry
    state `sa` to the exit state `s'`: `%rsp` and the six callee-saved registers are
    restored, word `i < n` of `rp` is the `and` of words `i` of `ap` and `bp` at entry, and
    every byte outside the `n` words of `rp` and the ten stack words of the frame is
    unchanged. -/
def AndNPost (sa s' : AState) (n : Nat) : Prop :=
  s'.regs "%rsp" = sa.regs "%rsp" ∧
    (∀ r ∈ ["%rbx", "%rbp", "%r12", "%r13", "%r14", "%r15"], s'.regs r = sa.regs r) ∧
    (∀ i < n, read64 s'.mem (sa.regs "%rdi" + BitVec.ofInt 64 (8 * (i : Int)))
      = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 (8 * (i : Int)))
        &&& read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 (8 * (i : Int)))) ∧
    (∀ x, OutsideRp (sa.regs "%rdi") n x →
      (∀ o ∈ stackOffsets, ¬ InRange8 (frameBase sa + BitVec.ofInt 64 o) x) →
      s'.mem x = sa.mem x)

/-- **The decoded `mpn_and_n_loop_owned` computes the `and`.** From an entry state whose
    `%rcx` holds `n` with `1 ≤ n < 2^64` and whose `%rdi`, `%rsi`, `%rdx`, `%rsp` satisfy
    `AndNLayout`, the decoded program run on `aMachine` from index `0` halts, with some fuel,
    in a state satisfying `AndNPost`. -/
theorem binDecoded_and_value (sa : AState) (n : Nat) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hcx : sa.regs "%rcx" = BitVec.ofNat 64 n)
    (hL : AndNLayout (sa.regs "%rdi") (sa.regs "%rsi") (sa.regs "%rdx") (sa.regs "%rsp") n) :
    ∃ f s', run aMachine (binDecoded (andMidDecoded .and_)) f 0 sa = some s' ∧
      AndNPost sa s' n := by
  have hR := andRegions_disjoint sa n hL
  obtain ⟨h1, h2, h3, h4, -, -, -, h8, h9, h10⟩ := hL
  obtain ⟨Sregs, -, Smem⟩ := prologueStores_run sa
  obtain ⟨Lmem, Lrdi, Lrax, -, -, -, Lother, Lzf⟩ :=
    prologueLoads_run sa (runBlockA sa prologueStores) Smem (by rw [Sregs]; simp)
  have hsplit : runBlockA sa binPrologue = runBlockA (runBlockA sa prologueStores) prologueLoads := by
    rw [binPrologue_split, runBlockA_append]
  have s1mem : (runBlockA sa binPrologue).mem = prologueMem sa := by rw [hsplit, Lmem, Smem]
  have s1rsp : (runBlockA sa binPrologue).regs "%rsp" = frameBase sa := by
    rw [hsplit, Lother "%rsp" (by decide), Sregs]; simp
  have s1rax : (runBlockA sa binPrologue).regs "%rax" = 0 := by rw [hsplit, Lrax]
  have s1rdi : (runBlockA sa binPrologue).regs "%rdi" = BitVec.ofNat 64 n := by
    rw [hsplit, Lrdi, hcx]
  have hz : (runBlockA sa binPrologue).view.flagB (·.zf) = false := by
    rw [hsplit, Lzf, hcx, decide_eq_false_iff_not]
    exact ofNat64_ne_zero n hn1 hn
  obtain ⟨r56, r48, r40, r32, r24, r16, r8, r0, rm8, -⟩ := prologueMem_reads sa
  obtain ⟨sa', hrun, -, -, aregs, acell, aother, aframe⟩ := andLoop_value (entryP sa) n hn1 hn
    hR n le_rfl (runBlockA sa binPrologue) s1rax s1rdi (by rw [s1rsp, entryP_rsp])
    (by rw [entryP_rsp, s1mem, r56, entryP_other _ _ (by decide)])
    (by rw [entryP_rsp, s1mem, r48, entryP_other _ _ (by decide)])
    (by rw [entryP_rsp, s1mem, rm8, entryP_other _ _ (by decide)])
  obtain ⟨f, hf⟩ := run_of_halts (binDecoded_and_halts n sa sa' hz hrun)
  obtain ⟨Emem, Ersp, Erbx, Erbp, Er12, Er13, Er14, Er15, -⟩ := binEpilogue_run sa'
  have arsp : sa'.regs "%rsp" = frameBase sa := by rw [aregs "%rsp" (by decide), s1rsp]
  have slot : ∀ (o : Int) (j : Nat), j < 9 → o = -8 + 8 * (j : Int) →
      read64 sa'.mem (frameBase sa + BitVec.ofInt 64 o) = read64 (prologueMem sa) (frameBase sa + BitVec.ofInt 64 o) := by
    intro o j hj ho
    have := aother ("%rsp", o) (stack_cell n o j hj ho) (by dsimp only; decide)
    rwa [keyAddr_stack, s1mem] at this
  refine ⟨f, _, hf, ?_, ?_, ?_, ?_⟩
  · rw [Ersp, arsp, frameBase, BitVec.add_assoc, ← BitVec.ofInt_add]; simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Erbx, arsp, slot 40 6 (by decide) (by decide), r40]
    · rw [Erbp, arsp, slot 32 5 (by decide) (by decide), r32]
    · rw [Er12, arsp, slot 24 4 (by decide) (by decide), r24]
    · rw [Er13, arsp, slot 16 3 (by decide) (by decide), r16]
    · rw [Er14, arsp, slot 8 2 (by decide) (by decide), r8]
    · rw [Er15, arsp, slot 0 1 (by decide) (by decide), r0]
  · intro i hi
    have := acell i hi
    rw [entryP_other _ _ (by decide), entryP_other _ _ (by decide), entryP_other _ _ (by decide),
      s1mem] at this
    rw [Emem, this, prologueMem_read_outside sa _ h4 ?_ ?_, prologueMem_read_outside sa _ h4 ?_ ?_]
    · rw [word_toNat _ i n hi h3]; omega
    · rw [word_toNat _ i n hi h3]; omega
    · rw [word_toNat _ i n hi h2]; omega
    · rw [word_toNat _ i n hi h2]; omega
  · intro x hx hstack
    rw [Emem, aframe x (by rwa [entryP_other _ _ (by decide)]), s1mem,
      prologueMem_frame sa x hstack]

/-! ## 6. The bytes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog binLoopBody
  andMid)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecodeClosed
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontBodyTie
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit (andLprog andLprog_isSome)

/-- The function bytes of `mpn_and_n_loop_owned`: the encoder's output for the loop body
    `binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64"`. -/
def andNBytes : List (BitVec 8) :=
  encodeLfundefBytes (binLoopBody (andMid "AND:64" "SHL:0:64") "SHL:0:64")

/-- **The bytes of `mpn_and_n_loop_owned` compute the `and`.** Every program `andNBytes`
    decodes to, run on `aMachine` from an entry state whose `%rcx` holds `n` with
    `1 ≤ n < 2^64` and whose pointers satisfy `AndNLayout`, halts with some fuel in a
    state satisfying `AndNPost`. -/
theorem and_n_bytes_value (prog : List RInstr) (hdec : decodeLprog andNBytes = some prog)
    (sa : AState) (n : Nat) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hcx : sa.regs "%rcx" = BitVec.ofNat 64 n)
    (hL : AndNLayout (sa.regs "%rdi") (sa.regs "%rsi") (sa.regs "%rdx") (sa.regs "%rsp") n) :
    ∃ f s', run aMachine prog f 0 sa = some s' ∧ AndNPost sa s' n := by
  have h := and_n_roundtrip_closed
  rw [← andNBytes, hdec, Option.some.injEq] at h
  rw [h]
  exact binDecoded_and_value sa n hn1 hn hcx hL

/-- **The front-compiled `and` kernel's bytes compute the `and`.** The `Lprog` the front
    compiles for `mpn_and_n_loop_owned` has one function, and every program the encoder's
    bytes for its body decode to, run on `aMachine` as in `and_n_bytes_value`, halts in a
    state satisfying `AndNPost`. The statement inherits `Lean.ofReduceBool` from
    `MpnLoopFrontBodyTie.andLprog_body_eq`. -/
theorem and_n_front_bytes_value :
    ∃ fd, ((andLprog ()).get andLprog_isSome).lp_funcs = [("mpn_and_n_loop_owned", fd)] ∧
      ∀ (prog : List RInstr), decodeLprog (encodeLfundefBytes fd.lfd_body) = some prog →
        ∀ (sa : AState) (n : Nat), 1 ≤ n → n < 2 ^ 64 → sa.regs "%rcx" = BitVec.ofNat 64 n →
          AndNLayout (sa.regs "%rdi") (sa.regs "%rsi") (sa.regs "%rdx") (sa.regs "%rsp") n →
          ∃ f s', run aMachine prog f 0 sa = some s' ∧ AndNPost sa s' n := by
  obtain ⟨fd, hfd, hb⟩ := and_n_front_roundtrip
  refine ⟨fd, hfd, fun prog hdec sa n hn1 hn hcx hL => ?_⟩
  rw [hdec, Option.some.injEq] at hb
  rw [hb]
  exact binDecoded_and_value sa n hn1 hn hcx hL

end CatCrypt.Crypto.SecureCompilation.Ascent.AndNBytesValue
