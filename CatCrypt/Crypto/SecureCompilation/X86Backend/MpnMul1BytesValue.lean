/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode

@[expose] public section

set_option autoImplicit false

/-!
# The decoded `mpn_mul_1` node against the flag machine

`MpnMul1DecodedNode` gives the renamed `mpn_mul_1` node `mul1Seeds ρ ++
guardedFlagLoopLinstrRM 4 (4 + 0x40000000) (loopCtr 4) (mul1LoopBody ρ)` and the decoded
layout `nodeLayout mul1DecPre mul1DecLoop mul1DecPost` of its function bytes. This module
discharges the hypotheses of `DecodedLsemLoop.decNode_halts` for them, at the node
renaming `mul1Rho`.

## The register map and the layout

`mul1Pi` sends each name of the renamed node to the machine register the decoded body
keeps it in: `a0 ↦ %rbx`, `a1 ↦ %rcx`, `a2 ↦ %rsi`, `a3 ↦ %rdi`, `Lidx4 ↦ %rax`,
`Lctr4 ↦ %rbp`, and each body temporary `L4_rk` to the register of the allocated body.
At the entry, `mul1Pi0` holds the four arguments in the System V registers. The arrays
`a0` (`9` words at `rp`) and `a1` (`8` words at `up`) keep their pointers in the frame
slots at `56(%rsp)` and `48(%rsp)` (`mul1Lay`, `mul1Frame`).

## The trip

One trip of the loop is composed from segments: the two reloaded loads, the low product,
the high half bracketed through `%r15` (`DecSimTactic.decSim_mulhi_bracket`), the carry
chain, the two reloaded stores with the carry index between them, and the tail with the
back-edge compare. The segments without memory side conditions are closed by
`decsim_chain`; the machine registers `%rsp`, `%rax`, `%rbp` are carried by
`DecSim.frame` (`mul1P`).

## Main results

* `mul1LoopBody_rho`, `mul1Seeds_rho`: the renamed looped segment and seeds as literals.
* `mul1_trip`: one trip, for every `t < m ≤ 8`.
* `mul1_guard`, `mul1_guard_flag`, `mul1_guard_inv`, `mul1_trip_flag`, `mul1_trip_next`:
  the guard and the trip-indexed hypotheses of `decNode_halts`.
* `mul1_pre`: the prologue from the entry correspondence at `mul1Pi0`.
* `mul1_post`: the epilogue keeps the words of `a0` at their addresses (`mul1Out`).
* `mul1_node_halts`: `decNode_halts` at the `mpn_mul_1` node.
* `mul1_sep_of_regions`: the separation hypotheses from the word-level separation of
  `rp`, `up` and the stack words (`mul1Regions`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1BytesValue

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (mul1Update)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic

/-! ## 1. The renamed node as literals -/

/-- The register assignment of the `mpn_mul_1` loop node: each name of the renamed node
    to the machine register the decoded body keeps it in. -/
def mul1Pi (r : String) : String :=
  if r = "a0" then "%rbx" else if r = "a1" then "%rcx" else if r = "a2" then "%rsi"
  else if r = "a3" then "%rdi" else if r = "Lidx4" then "%rax" else if r = "Lctr4" then "%rbp"
  else if r = "L4_r4" then "%rsi" else if r = "L4_r5" then "%r8" else if r = "L4_r6" then "%r9"
  else if r = "L4_r7" then "%r10" else if r = "L4_r8" then "%r9" else if r = "L4_r9" then "%r8"
  else if r = "L4_r10" then "%r9" else if r = "L4_r11" then "%rsi"
  else if r = "L4_r12" then "%r9" else if r = "L4_r13" then "%r11"
  else if r = "L4_r14" then "%r9" else if r = "L4_r15" then "%r11"
  else if r = "L4_r16" then "%r9" else if r = "L4_r17" then "%r12"
  else if r = "L4_r18" then "%r13" else if r = "L4_r19" then "%r9"
  else if r = "L4_r20" then "%r10" else if r = "L4_r21" then "%r9"
  else if r = "L4_r22" then "%r10" else if r = "L4_r23" then "%r12"
  else if r = "L4_r24" then "%r9" else if r = "L4_r25" then "%r10"
  else if r = "L4_r26" then "%r10" else if r = "L4_r27" then "%r9"
  else if r = "L4_r28" then "%r10" else if r = "L4_r29" then "%r8"
  else if r = "L4_r31" then "%rsi" else if r = "L4_r32" then "%r9"
  else if r = "L4_r33" then "%rsi" else r

/-- The node renaming of `mpn_mul_1`: the accumulator register and the two store results
    to the output array argument `a0`, every other name fixed. -/
def mul1Rho (r : String) : String :=
  if r = "r4" ∨ r = "L4_r30" ∨ r = "L4_r34" then "a0" else r

/-- The looped segment of the `mpn_mul_1` node under `mul1Rho`. -/
def mul1LoopBodyLit : List LinstrRM :=
  [ (.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a0" "Lidx4" 8], .load 64 9)
  , (.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)
  , binRegI "MUL:64" "L4_r6" "L4_r5" "a3"
  , immShiftI "SHL" "L4_r7" "L4_r6" 0
  , mulhiI "L4_r8" "L4_r5" "a3"
  , immShiftI "SHL" "L4_r9" "L4_r8" 0
  , binRegI "ADD:64" "L4_r10" "L4_r7" "L4_r4"
  , immShiftI "SHL" "L4_r11" "L4_r10" 0
  , movII "L4_r12" 18446744073709551615
  , binRegI "XOR:64" "L4_r13" "L4_r11" "L4_r12"
  , binRegI "AND:64" "L4_r14" "L4_r13" "L4_r7"
  , immShiftI "SHL" "L4_r15" "L4_r14" 0
  , binRegI "XOR:64" "L4_r16" "L4_r11" "L4_r7"
  , movII "L4_r17" 18446744073709551615
  , binRegI "XOR:64" "L4_r18" "L4_r16" "L4_r17"
  , binRegI "SUB:64" "L4_r19" "L4_r11" "L4_r7"
  , binRegI "AND:64" "L4_r20" "L4_r18" "L4_r19"
  , immShiftI "SHL" "L4_r21" "L4_r20" 0
  , binRegI "XOR:64" "L4_r22" "L4_r15" "L4_r21"
  , binRegI "AND:64" "L4_r23" "L4_r15" "L4_r21"
  , binRegI "XOR:64" "L4_r24" "L4_r22" "L4_r23"
  , movII "L4_r25" 63
  , immShiftI "SHR" "L4_r26" "L4_r24" 63
  , immShiftI "SHL" "L4_r27" "L4_r26" 0
  , binRegI "ADD:64" "L4_r28" "L4_r9" "L4_r27"
  , immShiftI "SHL" "L4_r29" "L4_r28" 0
  , (.Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r11"], .store 64 9)
  , movII "L4_r31" 1
  , binRegI "ADD:64" "L4_r32" "Lidx4" "L4_r31"
  , immShiftI "SHL" "L4_r33" "L4_r32" 0
  , (.Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r33" 8, .reg "L4_r29"], .store 64 9)
  , movRI "a0" "a0"
  , addImmI "Lidx4" "Lidx4" 1
  , subImmI "Lctr4" "Lctr4" 1
  , cmpRI "Lctr4" (.reg "a3")
  , cmpRI "Lctr4" (.reg "a1") ]

/-- The renamed looped segment is the literal `mul1LoopBodyLit`. -/
theorem mul1LoopBody_rho : mul1LoopBody mul1Rho = mul1LoopBodyLit := by
  decide +kernel

/-- The renamed seeds are the accumulator touch, the index at `0` and the counter from
    `a2`. -/
theorem mul1Seeds_rho :
    mul1Seeds mul1Rho = [movRI "a0" "a0", movII "Lidx4" 0, movRI "Lctr4" "a2"] := by
  decide +kernel

theorem loopCtr_four : loopCtr 4 = "Lctr4" := by decide +kernel

/-- `mul1Rho` fixes every name other than the accumulator register and the two store
    results. -/
theorem mul1Rho_id :
    ∀ r, r ≠ regName 4 → r ≠ loopReg 4 30 → r ≠ loopReg 4 34 → mul1Rho r = r := by
  intro r h1 h2 h3
  rw [show regName 4 = "r4" by decide +kernel] at h1
  rw [show loopReg 4 30 = "L4_r30" by decide +kernel] at h2
  rw [show loopReg 4 34 = "L4_r34" by decide +kernel] at h3
  unfold mul1Rho
  rw [if_neg (by rintro (h | h | h) <;> contradiction)]

/-! ## 2. The layout and the relation along the trip -/

/-- The array layout of the `mpn_mul_1` loop: the output `a0` at `rp` with `9` words and
    its pointer in slot `s0`, the multiplicand `a1` at `up` with `8` words and its pointer
    in slot `s1`. -/
def mul1Lay (rp up : BitVec 64) : Layout where
  base A := if A = "a1" then up else rp
  len A := if A = "a1" then 8 else 9
  slot A := if A = "a0" then some "s0" else if A = "a1" then some "s1" else none

/-- The frame of the `mpn_mul_1` loop: the slot `s0` at `56(%rsp)` and `s1` at
    `48(%rsp)`. -/
def mul1Frame (rsp : BitVec 64) (q : String) : Option (BitVec 64) :=
  if q = "s0" then some (rsp + BitVec.ofInt 64 56)
  else if q = "s1" then some (rsp + BitVec.ofInt 64 48) else none

/-- The cells of the `mpn_mul_1` loop: every word of `a0` and of `a1`. -/
def mul1K (A : String) (j : Nat) : Prop := (A = "a0" ∧ j < 9) ∨ (A = "a1" ∧ j < 8)

/-- The names live at the loop head: the two array pointers, the multiplier, the index and
    the counter. -/
abbrev mul1Live (r : String) : Prop :=
  r = "a0" ∨ r = "a1" ∨ r = "a3" ∨ r = "Lidx4" ∨ r = "Lctr4"

/-- The machine registers the loop trip tracks: the stack pointer at `rsp`, the index
    register at `x` and the counter at `y`. -/
def mul1P (rsp : BitVec 64) (x y : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp ∧ sa.regs "%rax" = BitVec.ofNat 64 x ∧ sa.regs "%rbp" = BitVec.ofNat 64 y

/-- A block that writes none of `%rsp`, `%rax`, `%rbp` keeps `mul1P`. -/
theorem mul1P_runBlock (rsp : BitVec 64) (x y : Nat) (js : List (JInstr 64))
    (h : ∀ j ∈ js, ∀ R ∈ ["%rsp", "%rax", "%rbp"], R ∉ dsts j) (sa : AState)
    (hp : mul1P rsp x y sa) : mul1P rsp x y (aMachine.runBlock sa js) := by
  have e := runBlock_regs_of_not_mem _ js sa h
  exact ⟨by rw [e _ (by simp)]; exact hp.1, by rw [e _ (by simp)]; exact hp.2.1,
    by rw [e _ (by simp)]; exact hp.2.2⟩

/-- The cells and frame slots are disjoint from the word at `-128(%rsp)` that the high half
    saves `%rcx` to. -/
def mul1Save (rp up rsp : BitVec 64) : Prop :=
  (∀ A j, mul1K A j → Disjoint8 (rsp + BitVec.ofInt 64 (-128)) ((mul1Lay rp up).addr A j))
    ∧ ∀ q x, mul1Frame rsp q = some x → Disjoint8 (rsp + BitVec.ofInt 64 (-128)) x

/-- The loop-head relation after trip `t` of `m`: the index at `t + 1`, the counter at
    `m - (t + 1)`, and the machine zero flag the equality of the counter with `0`. -/
def mul1Q (rsp : BitVec 64) (m t : Nat) (sa : AState) : Prop :=
  mul1P rsp (t + 1) (m - (t + 1)) sa
    ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 (m - (t + 1)) == 0#64)

/-- The register map at the entry of `mpn_mul_1`: the four arguments in the System V
    argument registers. -/
def mul1Pi0 (r : String) : String :=
  if r = "a0" then "%rdi" else if r = "a1" then "%rsi" else if r = "a2" then "%rdx"
  else if r = "a3" then "%rcx" else r

/-- The four argument names. -/
abbrev mul1Args (r : String) : Prop := r = "a0" ∨ r = "a1" ∨ r = "a2" ∨ r = "a3"

/-- The layout of `mul1Lay` without pointer slots, for the entry, before the prologue has
    saved the pointers. -/
def mul1Lay0 (rp up : BitVec 64) : Layout := { mul1Lay rp up with slot := fun _ => none }

/-- The machine state at the entry of `mpn_mul_1`: the stack pointer `64` above the body's,
    `rp` in `%rdi`, `up` in `%rsi` and the count `m` in `%rdx`. -/
def mul1Entry (rp up rsp : BitVec 64) (m : Nat) (sa : AState) : Prop :=
  sa.regs "%rsp" = rsp + BitVec.ofInt 64 64 ∧ sa.regs "%rdi" = rp ∧ sa.regs "%rsi" = up
    ∧ sa.regs "%rdx" = BitVec.ofNat 64 m

/-- The cells are disjoint from the stack words at offsets `-128` to `56` from the body's
    stack pointer. -/
def mul1StackSep (rp up rsp : BitVec 64) : Prop :=
  ∀ A j, mul1K A j → ∀ o : Int, -128 ≤ o → o ≤ 56 →
    Disjoint8 (rsp + BitVec.ofInt 64 o) ((mul1Lay rp up).addr A j)

/-- The machine part of the prologue: the frame `leaq`, the ten saves and the four reloads
    of the arguments into their loop registers. -/
def mul1Pre16 : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48
  , .loadMem "%rsi" "%rsp" (-8), .loadMem "%rdi" "%rsp" (-16) ]

theorem mul1DecPre_eq : mul1DecPre = mul1Pre16 ++
    [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rbp" (.reg "%rsi")] := rfl

section Trip

variable (rp up rsp : BitVec 64)

/-- The relation along the loop trip: the correspondence at `mul1Pi`, the `mpn_mul_1`
    layout and frame, and a machine-state predicate. -/
abbrev mul1Rel (L : String → Prop) (K : String → Nat → Prop) (zl : Prop) (P : AState → Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr mul1Pi L (mul1Lay rp up) (mul1Frame rsp) K zl sa b zf ∧ P sa

/-! ## 3. The segments of one trip -/

/-- The load of `a0[Lidx4]`: the reload of `rp` from `56(%rsp)` into `%r14` and the
    indexed load into `%rsi`. -/
theorem mul1_seg_load0 (t y : Nat) (ht : t < 9) (zl : Prop) :
    DecSim (mul1Rel rp up rsp mul1Live mul1K zl (mul1P rsp t y))
      (mul1Rel rp up rsp (liveAfter mul1Pi mul1Live "L4_r4" "%rsi") mul1K zl (mul1P rsp t y))
      [(.Lopn [.reg "L4_r4"] "LOADIDX" [.arrIdx "a0" "Lidx4" 8], .load 64 9)]
      [.loadMem "%r14" "%rsp" 56, .loadMemIdx "%rsi" "%r14" "%rax" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := mul1Lay rp up) (frame := mul1Frame rsp) (K := mul1K) (zl := zl)
      (π := mul1Pi) (L := mul1Live) (L' := liveAfter mul1Pi mul1Live "L4_r4" "%rsi")
      "L4_r4" "a0" "Lidx4" "%r14" "%rsp" "s0" 56 rfl (by decide +kernel)
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
      (fun _ hr => hr))
    (fun sa hp => ⟨by rw [hp.1]; rfl, Or.inl ⟨rfl, by
      show (sa.regs "%rax").toNat < 9
      rw [hp.2.1, ofNat_toNat_lt t (by omega)]; exact ht⟩⟩)
    (mul1P_runBlock rsp t y _ (by decide +kernel))

/-- The load of `a1[Lidx4]`: the reload of `up` from `48(%rsp)` into `%r14` and the
    indexed load into `%r8`. -/
theorem mul1_seg_load1 (t y : Nat) (ht : t < 8) (zl : Prop) :
    DecSim (mul1Rel rp up rsp (liveAfter mul1Pi mul1Live "L4_r4" "%rsi") mul1K zl
        (mul1P rsp t y))
      (mul1Rel rp up rsp (liveAfter mul1Pi (liveAfter mul1Pi mul1Live "L4_r4" "%rsi") "L4_r5"
        "%r8") mul1K zl (mul1P rsp t y))
      [(.Lopn [.reg "L4_r5"] "LOADIDX" [.arrIdx "a1" "Lidx4" 8], .load 64 8)]
      [.loadMem "%r14" "%rsp" 48, .loadMemIdx "%r8" "%r14" "%rax" 8] :=
  DecSim.frameWith _ _ _
    (decSim_loadR (Lay := mul1Lay rp up) (frame := mul1Frame rsp) (K := mul1K) (zl := zl)
      (π := mul1Pi) (L := liveAfter mul1Pi mul1Live "L4_r4" "%rsi")
      (L' := liveAfter mul1Pi (liveAfter mul1Pi mul1Live "L4_r4" "%rsi") "L4_r5" "%r8")
      "L4_r5" "a1" "Lidx4" "%r14" "%rsp" "s1" 48 rfl (by decide +kernel)
      (fun r hr => by
        rcases hr with rfl | ⟨hr, -⟩
        · decide +kernel
        · rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
      (fun _ hr => hr))
    (fun sa hp => ⟨by rw [hp.1]; rfl, Or.inr ⟨rfl, by
      show (sa.regs "%rax").toNat < 8
      rw [hp.2.1, ofNat_toNat_lt t (by omega)]; exact ht⟩⟩)
    (mul1P_runBlock rsp t y _ (by decide +kernel))

/-- The names live before the high half: the low product's copy, the multiplicand limb,
    the output limb, and the names live at the loop head. -/
abbrev mul1LiveA (r : String) : Prop := r = "L4_r7" ∨ r = "L4_r5" ∨ r = "L4_r4" ∨ mul1Live r

/-- The low product and its copy. -/
theorem mul1_seg_lo (t y : Nat) (zl : Prop) :
    DecSim (mul1Rel rp up rsp (liveAfter mul1Pi (liveAfter mul1Pi mul1Live "L4_r4" "%rsi")
        "L4_r5" "%r8") mul1K zl (mul1P rsp t y))
      (mul1Rel rp up rsp mul1LiveA mul1K False (mul1P rsp t y))
      [binRegI "MUL:64" "L4_r6" "L4_r5" "a3", immShiftI "SHL" "L4_r7" "L4_r6" 0]
      [.mov "%r9" (.reg "%r8"), .imul "%r9" (.reg "%rdi"), .mov "%r10" (.reg "%r9")] := by
  refine DecSim.frame _ _ ?_ (mul1P_runBlock rsp t y _ (by decide +kernel))
  decsim_chain
  exact fun _ _ _ h => h.mono (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) id
    (fun _ _ h => h)

/-- The names live after the high half. -/
abbrev mul1LiveB : String → Prop :=
  liveAfter mul1Pi (liveOff mul1Pi mul1LiveA "%r15") "L4_r8" "%r9"

/-- The high half of the limb product, bracketed through `%r15`. -/
theorem mul1_seg_hi (t y : Nat) (hsave : mul1Save rp up rsp) :
    DecSim (mul1Rel rp up rsp mul1LiveA mul1K False (mul1P rsp t y))
      (mul1Rel rp up rsp mul1LiveB mul1K False (mul1P rsp t y))
      [mulhiI "L4_r8" "L4_r5" "a3"]
      [.mov "%r15" (.reg "%rdx"), .mov "%rdx" (.reg "%r8"), .storeMem "%rsp" (-128) (.reg "%rcx"),
        .mulx "%r9" "%rcx" (.reg "%rdx") (.reg "%rdi"), .loadMem "%rcx" "%rsp" (-128),
        .mov "%rdx" (.reg "%r15")] :=
  DecSim.frameWith _ _ _
    (decSim_mulhi_bracket (π := mul1Pi) (L := mul1LiveA) (Lay := mul1Lay rp up)
      (frame := mul1Frame rsp) (K := mul1K) (zl := False)
      "L4_r8" "L4_r5" "a3" "%rdx" "%rcx" "%r15" "%rsp" (-128) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (fun sa hp => by rw [hp.1]; exact hsave)
    (mul1P_runBlock rsp t y _ (by decide +kernel))

/-- The names live before the first store: the low result word, the carry-out word, and
    the names live at the loop head. -/
abbrev mul1LiveC (r : String) : Prop := r = "L4_r11" ∨ r = "L4_r29" ∨ mul1Live r

/-- The carry chain from the high half to the two result words. -/
theorem mul1_seg_carry (t y : Nat) :
    DecSim (mul1Rel rp up rsp mul1LiveB mul1K False (mul1P rsp t y))
      (mul1Rel rp up rsp mul1LiveC mul1K False (mul1P rsp t y))
      (mul1LoopBodyLit.drop 5 |>.take 21)
      [ .mov "%r8" (.reg "%r9"), .mov "%r9" (.reg "%r10"), .add "%r9" (.reg "%rsi")
      , .mov "%rsi" (.reg "%r9"), .mov "%r9" (.imm 18446744073709551615)
      , .mov "%r11" (.reg "%rsi"), .xor_ "%r11" (.reg "%r9"), .mov "%r9" (.reg "%r11")
      , .and_ "%r9" (.reg "%r10"), .mov "%r11" (.reg "%r9"), .mov "%r9" (.reg "%rsi")
      , .xor_ "%r9" (.reg "%r10"), .mov "%r12" (.imm 18446744073709551615)
      , .mov "%r13" (.reg "%r9"), .xor_ "%r13" (.reg "%r12"), .mov "%r9" (.reg "%rsi")
      , .sub "%r9" (.reg "%r10"), .mov "%r10" (.reg "%r13"), .and_ "%r10" (.reg "%r9")
      , .mov "%r9" (.reg "%r10"), .mov "%r10" (.reg "%r11"), .xor_ "%r10" (.reg "%r9")
      , .mov "%r12" (.reg "%r11"), .and_ "%r12" (.reg "%r9"), .mov "%r9" (.reg "%r10")
      , .xor_ "%r9" (.reg "%r12"), .mov "%r10" (.imm 63), .mov "%r10" (.reg "%r9")
      , .shr "%r10" (.imm 63), .mov "%r9" (.reg "%r10"), .mov "%r10" (.reg "%r8")
      , .add "%r10" (.reg "%r9"), .mov "%r8" (.reg "%r10") ] := by
  refine DecSim.frame _ _ ?_ (mul1P_runBlock rsp t y _ (by decide +kernel))
  simp only [mul1LoopBodyLit, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero]
  decsim_chain
  exact fun _ _ _ h => h.mono (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) id
    (fun _ _ h => h)

/-- Two distinct words of `a0` below its length lie at distinct addresses. -/
theorem mul1_addr_a0_ne {j j' : Nat} (hj : j < 9) (hj' : j' < 9) (hne : j' ≠ j) :
    (mul1Lay rp up).addr "a0" j' ≠ (mul1Lay rp up).addr "a0" j := by
  intro h
  have h' := congrArg BitVec.toNat (add_left_cancel h)
  simp only [BitVec.toNat_ofNat] at h'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

/-- The cells of `mul1K` survive the store to `a0[j]`, given that `a0` and `a1` are
    disjoint. -/
theorem mul1K_afterStore (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j'))
    (j : Nat) (hj : j < 9) :
    ∀ A j', mul1K A j' → afterStore (mul1Lay rp up) mul1K "a0" "a0" j A j' := by
  rintro A j' (⟨rfl, hj'⟩ | ⟨rfl, hj'⟩)
  · by_cases hjj : j' = j
    · exact Or.inl ⟨rfl, Or.inl hjj⟩
    · exact Or.inl ⟨rfl, Or.inr ⟨Or.inl ⟨rfl, hj'⟩, mul1_addr_a0_ne rp up hj hj' hjj⟩⟩
  · exact Or.inr ⟨by decide, Or.inr ⟨rfl, hj'⟩, ne_of_disjoint8 (hdis j j' hj hj')⟩

/-- The store of the low result word to `a0[Lidx4]` through the reloaded `rp`. -/
theorem mul1_seg_store0 (t y : Nat) (ht : t < 9)
    (hsep : (mul1Lay rp up).Sep (mul1Frame rsp))
    (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j')) :
    DecSim (mul1Rel rp up rsp mul1LiveC mul1K False (mul1P rsp t y))
      (mul1Rel rp up rsp mul1LiveC mul1K False (mul1P rsp t y))
      [(.Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "Lidx4" 8, .reg "L4_r11"], .store 64 9)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rax" 8 (.reg "%rsi")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ _
      (decSim_storeR (π := mul1Pi) (L := mul1LiveC) (Lay := mul1Lay rp up)
        (frame := mul1Frame rsp) (K := mul1K) (zl := False) hsep
        "a0" "a0" "Lidx4" "L4_r11" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel)
        (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
        t)
      (fun sa hp => ⟨by rw [hp.1]; rfl, by
        show (sa.regs "%rax").toNat = t
        rw [hp.2.1, ofNat_toNat_lt t (by omega)], Or.inl ⟨rfl, ht⟩⟩)
      (mul1P_runBlock rsp t y _ (by decide +kernel)))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (mul1K_afterStore rp up hdis t ht), h.2⟩)

/-- The names live before the second store: the carry index, the carry-out word, and the
    names live at the loop head. -/
abbrev mul1LiveD (r : String) : Prop := r = "L4_r33" ∨ r = "L4_r29" ∨ mul1Live r

/-- The carry index `Lidx4 + 1`, in `%rsi`. -/
theorem mul1_seg_idx1 (t y : Nat) :
    DecSim (mul1Rel rp up rsp mul1LiveC mul1K False (mul1P rsp t y))
      (mul1Rel rp up rsp mul1LiveD mul1K False
        (fun sa => mul1P rsp t y sa ∧ sa.regs "%rsi" = BitVec.ofNat 64 (t + 1)))
      [movII "L4_r31" 1, binRegI "ADD:64" "L4_r32" "Lidx4" "L4_r31",
        immShiftI "SHL" "L4_r33" "L4_r32" 0]
      [.mov "%rsi" (.imm 1), .mov "%r9" (.reg "%rax"), .add "%r9" (.reg "%rsi"),
        .mov "%rsi" (.reg "%r9")] := by
  refine DecSim.frame _ _ ?_ (fun sa hp =>
    ⟨mul1P_runBlock rsp t y _ (by decide +kernel) sa hp, ?_⟩)
  · decsim_chain
    exact fun _ _ _ h => h.mono (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) id
      (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.mov X (.imm n))).regs x
        = if x = X then BitVec.ofNat 64 n else s.regs x := fun _ _ _ _ => rfl
    have ea : ∀ (s : AState) (X Y x : String), (evalInstrA s (.add X (.reg Y))).regs x
        = if x = X then s.regs X + s.regs Y else s.regs x := fun _ _ _ _ => rfl
    show (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa (.mov "%rsi" (.imm 1)))
      (.mov "%r9" (.reg "%rax"))) (.add "%r9" (.reg "%rsi"))) (.mov "%rsi" (.reg "%r9"))).regs
      "%rsi" = _
    simp (config := { decide := true }) only [em, ei, ea, ite_true, ite_false]
    rw [hp.2.1]
    exact (BitVec.ofNat_add t 1).symm

/-- The store of the carry-out word to `a0[Lidx4 + 1]` through the reloaded `rp`. -/
theorem mul1_seg_store1 (t y : Nat) (ht : t + 1 < 9)
    (hsep : (mul1Lay rp up).Sep (mul1Frame rsp))
    (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j')) :
    DecSim (mul1Rel rp up rsp mul1LiveD mul1K False
        (fun sa => mul1P rsp t y sa ∧ sa.regs "%rsi" = BitVec.ofNat 64 (t + 1)))
      (mul1Rel rp up rsp mul1LiveD mul1K False (mul1P rsp t y))
      [(.Lopn [.reg "a0"] "STOREIDX" [.arrIdx "a0" "L4_r33" 8, .reg "L4_r29"], .store 64 9)]
      [.loadMem "%r14" "%rsp" 56, .storeMemIdx "%r14" "%rsi" 8 (.reg "%r8")] :=
  DecSim.weaken
    (DecSim.frameWith _ _ (mul1P rsp t y)
      (decSim_storeR (π := mul1Pi) (L := mul1LiveD) (Lay := mul1Lay rp up)
        (frame := mul1Frame rsp) (K := mul1K) (zl := False) hsep
        "a0" "a0" "L4_r33" "L4_r29" "%r14" "%rsp" "s0" 56 rfl rfl rfl (by decide +kernel)
        (by decide +kernel)
        (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
        (t + 1))
      (fun sa hp => ⟨by rw [hp.1.1]; rfl, by
        show (sa.regs "%rsi").toNat = t + 1
        rw [hp.2, ofNat_toNat_lt (t + 1) (by omega)], Or.inl ⟨rfl, ht⟩⟩)
      (fun sa hp => mul1P_runBlock rsp t y _ (by decide +kernel) sa hp.1))
    (fun _ _ _ h => h)
    (fun _ _ _ h => ⟨h.1.mono (fun _ hr => hr) id (mul1K_afterStore rp up hdis (t + 1) ht), h.2⟩)

/-- The accumulator touch, the index advance, the counter decrement and the three
    compares ending in the back-edge compare. -/
theorem mul1_seg_tail (m t : Nat) (htm : t < m) :
    DecSim (mul1Rel rp up rsp mul1LiveD mul1K False (mul1P rsp t (m - t)))
      (mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t))
      [movRI "a0" "a0", addImmI "Lidx4" "Lidx4" 1, subImmI "Lctr4" "Lctr4" 1,
        cmpRI "Lctr4" (.reg "a3"), cmpRI "Lctr4" (.reg "a1"), cmpRI "Lctr4" (.imm 0)]
      [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1), .sub "%rbp" (.imm 1),
        .cmp "%rbp" (.reg "%rdi"), .cmp "%rbp" (.reg "%rcx"), .cmp "%rbp" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ?_)
  · decsim_chain
    exact fun _ _ _ h => h.mono (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ea : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.add X (.imm k))).regs x
        = if x = X then s.regs X + BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
    have es : ∀ (s : AState) (X x : String) (k : Nat), (evalInstrA s (.sub X (.imm k))).regs x
        = if x = X then s.regs X - BitVec.ofNat 64 k else s.regs x := fun _ _ _ _ => rfl
    have ec : ∀ (s : AState) (X : String) (o : JOperand), (evalInstrA s (.cmp X o)).regs
        = s.regs := fun _ _ _ => rfl
    have ez : ∀ (s : AState) (X : String) (k : Nat),
        (evalInstrA s (.cmp X (.imm k))).flags.zf.getD false
          = ZF_of_word (s.regs X - BitVec.ofNat 64 k) := fun _ _ _ => rfl
    have hm : m - t = m - (t + 1) + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := hp
    rw [show aMachine.runBlock sa [.mov "%rbx" (.reg "%rbx"), .add "%rax" (.imm 1),
        .sub "%rbp" (.imm 1), .cmp "%rbp" (.reg "%rdi"), .cmp "%rbp" (.reg "%rcx"),
        .cmp "%rbp" (.imm 0)]
      = evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA (evalInstrA sa
        (.mov "%rbx" (.reg "%rbx"))) (.add "%rax" (.imm 1))) (.sub "%rbp" (.imm 1)))
        (.cmp "%rbp" (.reg "%rdi"))) (.cmp "%rbp" (.reg "%rcx"))) (.cmp "%rbp" (.imm 0))
      from rfl]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_false]
      exact h1
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h2]; exact (BitVec.ofNat_add t 1).symm
    · simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel]
    · rw [ez]
      simp (config := { decide := true }) only [ec, em, ea, es, ite_true, ite_false]
      rw [h3, hm, BitVec.ofNat_add, BitVec.add_sub_cancel, ZF_of_word_sub]

/-! ## 4. The trip, the guard and the loop hypotheses -/

/-- **One trip of the `mpn_mul_1` loop.** For each trip `t < m ≤ 8`, the looped segment of
    the renamed node followed by `CMP:64 Lctr4, #0` simulates the decoded loop body
    followed by `cmp %rbp, 0`: from the loop-head names live, the index at `t` and the
    counter at `m - t`, to the loop-head names live, the index at `t + 1`, the counter at
    `m - (t + 1)` and the zero flag tracked. -/
theorem mul1_trip (m : Nat) (hm : m ≤ 8) (hsave : mul1Save rp up rsp)
    (hsep : (mul1Lay rp up).Sep (mul1Frame rsp))
    (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j'))
    (t : Nat) (ht : t < m) :
    DecSim (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp t (m - t)))
      (mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t))
      (mul1LoopBodyLit ++ [cmpRI "Lctr4" (.imm 0)]) (mul1DecLoopBody ++ [.cmp "%rbp" (.imm 0)]) :=
  (mul1_seg_load0 rp up rsp t (m - t) (by omega) False).append <|
  (mul1_seg_load1 rp up rsp t (m - t) (by omega) False).append <|
  (mul1_seg_lo rp up rsp t (m - t) False).append <|
  (mul1_seg_hi rp up rsp t (m - t) hsave).append <|
  (mul1_seg_carry rp up rsp t (m - t)).append <|
  (mul1_seg_store0 rp up rsp t (m - t) (by omega) hsep hdis).append <|
  (mul1_seg_idx1 rp up rsp t (m - t)).append <|
  (mul1_seg_store1 rp up rsp t (m - t) (by omega) hsep hdis).append <|
  mul1_seg_tail rp up rsp m t ht

/-- The relation after the zero-trip guard `cmp %rbp, 0`: the loop-head names live, the
    index at `0`, the counter at `m`, and the zero flag tracked. -/
def mul1G (m : Nat) : AState → LstateM → Bool → Prop :=
  mul1Rel rp up rsp mul1Live mul1K True
    (fun sa => mul1P rsp 0 m sa ∧ sa.flags.zf.getD false = (BitVec.ofNat 64 m == 0#64))

/-- **The zero-trip guard.** `CMP:64 Lctr4, #0` against `cmp %rbp, 0`. -/
theorem mul1_guard (m : Nat) (zl : Prop) :
    DecSim (mul1Rel rp up rsp mul1Live mul1K zl (mul1P rsp 0 m)) (mul1G rp up rsp m)
      [cmpRI "Lctr4" (.imm 0)] [.cmp "%rbp" (.imm 0)] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ⟨hp, ?_⟩)
  · exact decSim_cmpImm_r "Lctr4" "%rbp" 0 rfl (by decide +kernel)
  · show ZF_of_word (sa.regs "%rbp" - BitVec.ofNat 64 0) = _
    rw [hp.2.2, ZF_of_word_sub]

theorem mul1_guard_flag (m : Nat) (hm : m ≤ 8) :
    ∀ sa b zf, mul1G rp up rsp m sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ m = 0) := by
  intro sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz]
  exact ofNat_beq_zero_iff m (by omega)

theorem mul1_guard_inv (m : Nat) :
    ∀ sa b zf pc, mul1G rp up rsp m sa b zf →
      mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 (m - 0)) sa (b.setLpc pc) zf :=
  fun _ _ _ pc ⟨h, hp, _⟩ => ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

theorem mul1_trip_flag (m : Nat) (hm : m ≤ 8) :
    ∀ t, t < m → ∀ sa b zf, mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t) sa b zf →
      sa.flags.zf.getD false = zf ∧ (zf = true ↔ t + 1 = m) := by
  intro t ht sa b zf ⟨h, _, hz⟩
  have e := h.zfEq trivial
  refine ⟨e, ?_⟩
  rw [← e, hz, ofNat_beq_zero_iff _ (by omega)]
  omega

theorem mul1_trip_next (m : Nat) :
    ∀ t, t < m → ∀ sa b zf pc, mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t) sa b zf →
      mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp (t + 1) (m - (t + 1))) sa
        (b.setLpc pc) zf :=
  fun _ _ _ _ _ pc ⟨h, hp, _⟩ =>
    ⟨(h.setLpc pc).mono (fun _ hr => hr) False.elim (fun _ _ h => h), hp⟩

/-! ## 5. The prologue and the epilogue -/

/-- **The machine part of the prologue.** From the entry correspondence at `mul1Pi0`, the
    sixteen machine instructions establish the correspondence at `mul1Pi` for the four
    arguments, with the two pointer slots of the frame holding `rp` and `up`. -/
theorem mul1_pre16 (m : Nat) (zl : Prop) (hstk : mul1StackSep rp up rsp) :
    DecSim (fun sa b zf => DecLsemCorr mul1Pi0 mul1Args (mul1Lay0 rp up) (fun _ => none) mul1K
        zl sa b zf ∧ mul1Entry rp up rsp m sa)
      (mul1Rel rp up rsp mul1Args mul1K False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      [] mul1Pre16 := by
  refine DecSim.machBlock fun sa b zf ⟨h, hrsp, hrdi, hrsi, hrdx⟩ => ?_
  have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
      = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
  have emm : ∀ (s : AState) (X Y : String), (evalInstrA s (.mov X (.reg Y))).mem = s.mem :=
    fun _ _ _ => rfl
  have es : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).regs = s.regs := fun _ _ _ _ => rfl
  have esm : ∀ (s : AState) (B X : String) (o : Int),
      (evalInstrA s (.storeMem B o (.reg X))).mem
        = write64 s.mem (s.regs B + BitVec.ofInt 64 o) (s.regs X) := fun _ _ _ _ => rfl
  have elm : ∀ (s : AState) (X B : String) (o : Int),
      (evalInstrA s (.loadMem X B o)).mem = s.mem := fun _ _ _ _ => rfl
  have ele : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int) (x : String),
      (evalInstrA s (.lea D B I sc o)).regs x
        = if x = D then s.regs B + s.regs I * BitVec.ofNat 64 sc + BitVec.ofInt 64 o
          else s.regs x := fun _ _ _ _ _ _ _ => rfl
  have elem : ∀ (s : AState) (D B I : String) (sc : Nat) (o : Int),
      (evalInstrA s (.lea D B I sc o)).mem = s.mem := fun _ _ _ _ _ _ => rfl
  have hlea : sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (-64)
      = rsp := by
    rw [hrsp, BitVec.mul_zero, BitVec.add_zero, BitVec.add_assoc,
      show BitVec.ofInt 64 64 + BitVec.ofInt 64 (-64) = 0#64 by decide +kernel, BitVec.add_zero]
  simp only [mul1Pre16, Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
  generalize hs' : evalInstrA _ (.loadMem "%rdi" "%rsp" (-16)) = s'
  have hmem := congrArg AState.mem hs'
  have hregs := fun x => congrArg (fun s => AState.regs s x) hs'
  simp (config := { decide := true }) only [em, emm, es, esm, elm, ele, elem,
    evalInstrA_loadMem_regs', ite_true, ite_false, hlea] at hmem hregs
  simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
    [read64_write64_same, read64_write64_of_disjoint] at hregs
  generalize hM : write64 (write64 (write64 (write64 (write64 (write64 (write64 (write64
    (write64 (write64 sa.mem _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _ = M at hmem
  have hcell : ∀ A j, mul1K A j → read64 M ((mul1Lay rp up).addr A j)
      = read64 sa.mem ((mul1Lay rp up).addr A j) := by
    intro A j hk
    have hd := fun o h1 h2 => hstk A j hk o h1 h2
    rw [← hM]
    rw [read64_write64_of_disjoint _ _ _ _ (hd (-16) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd (-8) (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 0 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 8 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 16 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 24 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 32 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 40 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 48 (by omega) (by omega)),
      read64_write64_of_disjoint _ _ _ _ (hd 56 (by omega) (by omega))]
  have hs0 : read64 M (rsp + BitVec.ofInt 64 56) = rp := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrdi
  have hs1 : read64 M (rsp + BitVec.ofInt 64 48) = up := by
    rw [← hM]
    simp (disch := exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)) only
      [read64_write64_same, read64_write64_of_disjoint]
    exact hrsi
  have hr : ∀ x, s'.regs x = _ := fun x => (hregs x).symm
  refine ⟨⟨fun r hr' => ?_, fun hz => hz.elim, fun A j hk => ?_, fun A q hq => ?_⟩, ?_, ?_⟩
  · rcases hr' with rfl | rfl | rfl | rfl
    · show _ = some (s'.regs "%rbx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a0" (Or.inl rfl)
    · show _ = some (s'.regs "%rcx")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a1" (Or.inr (Or.inl rfl))
    · show _ = some (s'.regs "%rsi")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a2" (Or.inr (Or.inr (Or.inl rfl)))
    · show _ = some (s'.regs "%rdi")
      rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
      exact h.regs "a3" (Or.inr (Or.inr (Or.inr rfl)))
  · obtain ⟨hj, arr, ha, hc⟩ := h.cells A j hk
    exact ⟨hj, arr, ha, by rw [← hmem, hcell A j hk]; exact hc⟩
  · simp only [mul1Lay] at hq
    split_ifs at hq with h0 h1
    · subst h0; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs0]; rfl⟩
    · subst h1; obtain rfl := Option.some.inj hq
      exact ⟨_, rfl, by rw [← hmem, hs1]; rfl⟩
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]
  · rw [hr]; simp (config := { decide := true }) only [ite_true, ite_false]; exact hrdx

/-- The three loop seeds: the accumulator touch, the index at `0` and the counter from
    `a2`. -/
theorem mul1_seg_seeds (m : Nat) :
    DecSim (mul1Rel rp up rsp mul1Args mul1K False
        (fun sa => sa.regs "%rsp" = rsp ∧ sa.regs "%rsi" = BitVec.ofNat 64 m))
      (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 m))
      [movRI "a0" "a0", movII "Lidx4" 0, movRI "Lctr4" "a2"]
      [.mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0), .mov "%rbp" (.reg "%rsi")] := by
  refine DecSim.frame _ _ ?_ (fun sa hp => ?_)
  · decsim_chain
    exact fun _ _ _ h => h.mono (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide +kernel) id (fun _ _ h => h)
  · have em : ∀ (s : AState) (X Y x : String), (evalInstrA s (.mov X (.reg Y))).regs x
        = if x = X then s.regs Y else s.regs x := fun _ _ _ _ => rfl
    have ei : ∀ (s : AState) (X x : String) (n : Nat), (evalInstrA s (.mov X (.imm n))).regs x
        = if x = X then BitVec.ofNat 64 n else s.regs x := fun _ _ _ _ => rfl
    simp only [Machine.runBlock_cons, Machine.runBlock_nil, aMachine_exec]
    refine ⟨?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [em, ei, ite_false]; exact hp.1
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]
    · simp (config := { decide := true }) only [em, ei, ite_true, ite_false]; exact hp.2

/-- **The prologue.** From the entry correspondence at `mul1Pi0`, the renamed seeds
    simulate `mul1DecPre` to the loop-head relation with the index at `0` and the counter
    at `m`. -/
theorem mul1_pre (m : Nat) (zl : Prop) (hstk : mul1StackSep rp up rsp) :
    DecSim (fun sa b zf => DecLsemCorr mul1Pi0 mul1Args (mul1Lay0 rp up) (fun _ => none) mul1K
        zl sa b zf ∧ mul1Entry rp up rsp m sa)
      (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 m))
      (mul1Seeds mul1Rho) mul1DecPre := by
  rw [mul1Seeds_rho, mul1DecPre_eq]
  exact (mul1_pre16 rp up rsp m zl hstk).append (mul1_seg_seeds rp up rsp m)

/-- The exit relation of the `mpn_mul_1` node: the flag machine's array `a0` has the shape
    `(64, 9)`, and each of its words sits little-endian at its layout address. -/
def mul1Out (sa : AState) (b : LstateM) : Prop :=
  ∃ arr : Fin 9 → BitVec 64, decodeArrM b "a0" 64 9 = some arr
    ∧ ∀ j, j < 9 → read64 sa.mem ((mul1Lay rp up).addr "a0" j) = stackGet arr j

/-- **The epilogue.** The restores and the closing `leaq` write no memory, so the words of
    `a0` stay at their layout addresses. -/
theorem mul1_post (m : Nat) :
    ∀ sa b, mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp m (m - m)) sa b true →
      mul1Out rp up (aMachine.runBlock sa mul1DecPost) b := by
  intro sa b ⟨h, _⟩
  have hmem : (aMachine.runBlock sa mul1DecPost).mem = sa.mem := rfl
  obtain ⟨_, arr, ha, _⟩ := h.cells "a0" 0 (Or.inl ⟨rfl, by decide⟩)
  refine ⟨arr, ha, fun j hj => ?_⟩
  obtain ⟨_, arr', ha', hr⟩ := h.cells "a0" j (Or.inl ⟨rfl, hj⟩)
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  rw [hmem]; exact hr

/-! ## 6. The node -/

/-- The fuel of the flag-machine run of the `mpn_mul_1` node at count `n`: three seeds,
    `38` steps for each pass (the `36` instructions of the looped segment and the
    back-edge), and four for the guard, the loop label and the skip label. -/
def mul1Fuel (n : Nat) : Nat := 38 * n + 7

@[simp] theorem mul1Fuel_eq (n : Nat) : mul1Fuel n = 38 * n + 7 := rfl

theorem mul1Fuel_mono {n n' : Nat} (h : n ≤ n') : mul1Fuel n ≤ mul1Fuel n' :=
  Nat.add_le_add_right (Nat.mul_le_mul_left 38 h) 7

/-- At a count `n ≤ 8` the fuel is at most `mul1Fuel 8`, which is `311`. -/
theorem mul1Fuel_le_eight {n : Nat} (h : n ≤ 8) : mul1Fuel n ≤ mul1Fuel 8 :=
  mul1Fuel_mono h

theorem mul1LoopBodyLit_length : mul1LoopBodyLit.length = 36 := rfl

/-- `mul1Fuel` is the node fuel `nodeFuel` at the renamed seeds and looped segment. -/
theorem nodeFuel_mul1 (n : Nat) :
    nodeFuel (mul1Seeds mul1Rho).length (mul1LoopBody mul1Rho).length n = mul1Fuel n := by
  rw [mul1LoopBody_rho, mul1Seeds_length, mul1LoopBodyLit_length, nodeFuel_eq, mul1Fuel_eq]
  omega

/-- **The `mpn_mul_1` node on both machines, with its fuel.** Given the prologue
    simulation `hpre` of the renamed seeds against `mul1DecPre`, from an entry relation
    `E₀` to the loop-head relation with the index at `0` and the counter at `m ≤ 8`, and
    an exit relation `Q` that the epilogue `mul1DecPost` reaches from the loop-exit
    relation: the machine halts on `nodeLayout mul1DecPre mul1DecLoop mul1DecPost` from
    index `0`, the flag machine halts on the renamed node at every fuel from `mul1Fuel m`
    on, and the end states satisfy `Q`. -/
theorem mul1_node_halts_fuel (m : Nat) (hm : m ≤ 8) (hsave : mul1Save rp up rsp)
    (hsep : (mul1Lay rp up).Sep (mul1Frame rsp))
    (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j'))
    (E₀ : AState → LstateM → Bool → Prop) (Q : AState → LstateM → Prop)
    (hpre : DecSim E₀ (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 m))
      (mul1Seeds mul1Rho) mul1DecPre)
    (hpost : ∀ sa b, mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp m (m - m)) sa b true →
      Q (aMachine.runBlock sa mul1DecPost) b)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : E₀ sa b zf) :
    ∃ sa' t, Halts aMachine (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) 0 sa sa'
      ∧ (∀ k, mul1Fuel m ≤ k →
          lsemFuelMemF (singletonProgM fn (mul1Seeds mul1Rho ++ guardedFlagLoopLinstrRM 4
            (4 + 0x40000000) (loopCtr 4) (mul1LoopBody mul1Rho))) k
            { prog := { base := b, lfn := fn }, zf := zf } = some t)
      ∧ Q sa' t.prog.base := by
  have hsim : ∀ t, t < m →
      DecSim (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp t (m - t)))
        (mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t))
        (mul1LoopBody mul1Rho ++ [cmpRI (loopCtr 4) (.imm 0)])
        (mul1DecLoop.body ++ [mul1DecLoop.cmpInstr]) := by
    intro t ht
    rw [mul1LoopBody_rho, loopCtr_four]
    exact mul1_trip rp up rsp m hm hsave hsep hdis t ht
  have hg : DecSim (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 m)) (mul1G rp up rsp m)
      [cmpRI (loopCtr 4) (.imm 0)] [mul1DecLoop.cmpInstr] := by
    rw [loopCtr_four]; exact mul1_guard rp up rsp m False
  have h := decNode_halts_fuel fn (mul1Seeds mul1Rho) (mul1LoopBody mul1Rho) 4
    (4 + 0x40000000) (loopCtr 4) mul1DecLoop m E₀ _ (mul1G rp up rsp m)
    (fun t => mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp t (m - t)))
    (fun t => mul1Rel rp up rsp mul1Live mul1K True (mul1Q rsp m t)) Q
    mul1DecPre mul1DecPost (mul1Seeds_isLopn _) (mul1LoopBody_isLopn _) (mul1Node_top _)
    (mul1Node_end _) hpre hg (mul1_guard_flag rp up rsp m hm) (mul1_guard_inv rp up rsp m)
    hsim (mul1_trip_flag rp up rsp m hm) (mul1_trip_next rp up rsp m) hpost sa b zf hpc hE
  rw [nodeFuel_mul1] at h
  exact h

/-- **The `mpn_mul_1` node on both machines.** `mul1_node_halts_fuel` with the fuel of the
    flag-machine run existentially quantified. -/
theorem mul1_node_halts (m : Nat) (hm : m ≤ 8) (hsave : mul1Save rp up rsp)
    (hsep : (mul1Lay rp up).Sep (mul1Frame rsp))
    (hdis : ∀ j j', j < 9 → j' < 8 →
      Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j'))
    (E₀ : AState → LstateM → Bool → Prop) (Q : AState → LstateM → Prop)
    (hpre : DecSim E₀ (mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp 0 m))
      (mul1Seeds mul1Rho) mul1DecPre)
    (hpost : ∀ sa b, mul1Rel rp up rsp mul1Live mul1K False (mul1P rsp m (m - m)) sa b true →
      Q (aMachine.runBlock sa mul1DecPost) b)
    (fn : String) (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hE : E₀ sa b zf) :
    ∃ sa' t k, Halts aMachine (nodeLayout mul1DecPre mul1DecLoop mul1DecPost) 0 sa sa'
      ∧ lsemFuelMemF (singletonProgM fn (mul1Seeds mul1Rho ++ guardedFlagLoopLinstrRM 4
          (4 + 0x40000000) (loopCtr 4) (mul1LoopBody mul1Rho))) k
          { prog := { base := b, lfn := fn }, zf := zf } = some t
      ∧ Q sa' t.prog.base := by
  obtain ⟨sa', t, hh, hrun, hQ⟩ := mul1_node_halts_fuel rp up rsp m hm hsave hsep hdis E₀ Q
    hpre hpost fn sa b zf hpc hE
  exact ⟨sa', t, _, hh, hrun _ (Nat.le_refl _), hQ⟩

end Trip

/-! ## 7. Separation from the regions -/

theorem mul1Lay_addr_a0 (rp up : BitVec 64) (j : Nat) :
    (mul1Lay rp up).addr "a0" j = rp + BitVec.ofNat 64 (8 * j) := rfl

theorem mul1Lay_addr_a1 (rp up : BitVec 64) (j : Nat) :
    (mul1Lay rp up).addr "a1" j = up + BitVec.ofNat 64 (8 * j) := rfl

/-- The separation of the `mpn_mul_1` memory at the word level: the words `rp + 8 j`
    (`j < 9`), the words `up + 8 j` (`j < 8`) and the stack words at offsets `-128` to `56`
    from the body's stack pointer are pairwise disjoint across the three regions. -/
def mul1Regions (rp up rsp : BitVec 64) : Prop :=
  (∀ j j', j < 9 → j' < 8 →
      Disjoint8 (rp + BitVec.ofNat 64 (8 * j)) (up + BitVec.ofNat 64 (8 * j')))
    ∧ (∀ (j : Nat) (o : Int), j < 9 → -128 ≤ o → o ≤ 56 →
      Disjoint8 (rsp + BitVec.ofInt 64 o) (rp + BitVec.ofNat 64 (8 * j)))
    ∧ (∀ (j : Nat) (o : Int), j < 8 → -128 ≤ o → o ≤ 56 →
      Disjoint8 (rsp + BitVec.ofInt 64 o) (up + BitVec.ofNat 64 (8 * j)))

/-- Two distinct words of one array below `9` words are disjoint. -/
theorem disjoint8_words (x : BitVec 64) {j j' : Nat} (hj : j < 9) (hj' : j' < 9)
    (hne : j ≠ j') : Disjoint8 (x + BitVec.ofNat 64 (8 * j)) (x + BitVec.ofNat 64 (8 * j')) := by
  apply disjoint8_add_left
  have key : ∀ j, j < 9 → ∀ j', j' < 9 → j ≠ j' →
      Disjoint8 (BitVec.ofNat 64 (8 * j)) (BitVec.ofNat 64 (8 * j')) := by
    unfold Disjoint8; decide +kernel
  exact key j hj j' hj' hne

theorem mul1_len_a0_of_ne (rp up : BitVec 64) {A : String} (h : A ≠ "a1") :
    (mul1Lay rp up).len A = 9 := by
  simp [mul1Lay, h]

/-- **Separation from the regions.** The word-level separation `mul1Regions` gives the
    four separation hypotheses of the loop node. -/
theorem mul1_sep_of_regions (rp up rsp : BitVec 64) (h : mul1Regions rp up rsp) :
    mul1Save rp up rsp ∧ (mul1Lay rp up).Sep (mul1Frame rsp)
      ∧ (∀ j j', j < 9 → j' < 8 →
        Disjoint8 ((mul1Lay rp up).addr "a0" j) ((mul1Lay rp up).addr "a1" j'))
      ∧ mul1StackSep rp up rsp := by
  obtain ⟨h01, hs0, hs1⟩ := h
  have hstk : mul1StackSep rp up rsp := by
    rintro A j (⟨rfl, hj⟩ | ⟨rfl, hj⟩) o ho1 ho2
    · exact hs0 j o hj ho1 ho2
    · exact hs1 j o hj ho1 ho2
  have hw : ∀ A j, j < (mul1Lay rp up).len A →
      (A = "a1" ∧ j < 8 ∧ (mul1Lay rp up).addr A j = up + BitVec.ofNat 64 (8 * j))
        ∨ (A ≠ "a1" ∧ j < 9 ∧ (mul1Lay rp up).addr A j = rp + BitVec.ofNat 64 (8 * j)) := by
    intro A j hj
    by_cases hA : A = "a1"
    · subst hA; exact Or.inl ⟨rfl, hj, rfl⟩
    · refine Or.inr ⟨hA, by rw [mul1_len_a0_of_ne rp up hA] at hj; exact hj, ?_⟩
      simp [Layout.addr, mul1Lay, hA]
  have hslot : ∀ q a, mul1Frame rsp q = some a →
      a = rsp + BitVec.ofInt 64 56 ∨ a = rsp + BitVec.ofInt 64 48 := by
    intro q a hq
    unfold mul1Frame at hq
    split_ifs at hq
    · exact Or.inl (Option.some.inj hq).symm
    · exact Or.inr (Option.some.inj hq).symm
  refine ⟨⟨fun A j hk => hstk A j hk (-128) (by omega) (by omega), fun q x hq => ?_⟩,
    ⟨fun A j A' j' hj hj' => ?_, fun A j B q a hj _ hq => ?_⟩, fun j j' hj hj' => h01 j j' hj hj',
    hstk⟩
  · rcases hslot q x hq with rfl | rfl
    · exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)
    · exact disjoint8_off _ _ _ (by unfold Disjoint8; decide +kernel)
  · rcases hw A j hj with ⟨_, hj1, e⟩ | ⟨_, hj1, e⟩ <;>
      rcases hw A' j' hj' with ⟨_, hj2, e'⟩ | ⟨_, hj2, e'⟩ <;> rw [e, e']
    · by_cases hjj : j = j'
      · exact Or.inl (by rw [hjj])
      · exact Or.inr (disjoint8_words _ (by omega) (by omega) hjj)
    · exact Or.inr (Disjoint8.symm (h01 j' j hj2 hj1))
    · exact Or.inr (h01 j j' hj1 hj2)
    · by_cases hjj : j = j'
      · exact Or.inl (by rw [hjj])
      · exact Or.inr (disjoint8_words _ hj1 hj2 hjj)
  · rcases hslot q a hq with rfl | rfl <;> rcases hw A j hj with ⟨_, hj1, e⟩ | ⟨_, hj1, e⟩ <;>
      rw [e]
    · exact Disjoint8.symm (hs1 j 56 hj1 (by omega) (by omega))
    · exact Disjoint8.symm (hs0 j 56 hj1 (by omega) (by omega))
    · exact Disjoint8.symm (hs1 j 48 hj1 (by omega) (by omega))
    · exact Disjoint8.symm (hs0 j 48 hj1 (by omega) (by omega))

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1BytesValue
