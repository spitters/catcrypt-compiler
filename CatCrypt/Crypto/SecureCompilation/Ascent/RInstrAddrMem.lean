/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx

/-!
# Decoded programs on the address machine, and the decoded `mpn_and_n`

@ascent-fixture theorems: binDecoded_and_eq, binDecoded_and_halts

`RInstrSemantics` runs a decoded program on any `Machine`. `aMachine` is the address
machine of `AddrMem`: `evalInstrA` on `AState`, with `AState.view` as the name-keyed
view. Its block fold is `runBlockA` and its counted loop is `runXLoopA`.

`LprogBytesDecode.and_n_roundtrip` decodes the function bytes of
`mpn_and_n_loop_owned` to `binDecoded (andMidDecoded .and_)`. That program is the
prologue `binPrologue` (indices `0`–`18`), the exit branch `je 37` (index `19`), the
loop segment of `AddrMemIdx.andLoop` (indices `20`–`36`: the body, `cmp %rdi, 0`,
`jne 20`), the epilogue `binEpilogue` (indices `37`–`43`) and `ret` (index `44`)
(`binDecoded_and_eq`). Run on `aMachine` from index `0`, it halts without a call in the state of the
prologue, the loop `runXLoopA fuel _ andLoop` when the counter is nonzero, and the
epilogue (`binDecoded_and_halts`, `binDecoded_and_halts_zero`).

## Main results

* `aMachine_runBlock`, `aMachine_runXLoop`: on `aMachine` the block fold is `runBlockA`
  and the loop is `runXLoopA`.
* `binDecoded_and_eq`: the decoded `mpn_and_n_loop_owned` is the segment layout around
  `andLoop`.
* `binDecoded_and_reaches_loop`: from index `20`, a terminating
  `runXLoopA fuel sa andLoop = some sa'` reaches index `37` in `sa'`.
* `binDecoded_and_halts`: from index `0` with a nonzero count after the prologue, the
  decoded program halts in `runBlockA sa' binEpilogue` for the loop's exit state `sa'`.
* `binDecoded_and_halts_zero`: with a zero count the loop is skipped.
* `binDecoded_and_transfer`: the exit state of the decoded loop is related by `LoopRel`
  to the exit state of the named-ref loop `andBodyNamed` (`andLoop_transfer`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr binDecoded
  andMidDecoded)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemIdx

/-! ## 1. The address machine -/

/-- The address machine: `evalInstrA` on `AState`, viewed through `AState.view`. -/
def aMachine : Machine AState := ⟨evalInstrA, AState.view⟩

theorem aMachine_view (sa : AState) : aMachine.view sa = sa.view := rfl

theorem aMachine_runBlock (sa : AState) (xs : List (JInstr 64)) :
    aMachine.runBlock sa xs = runBlockA sa xs := by
  induction xs generalizing sa with
  | nil => rfl
  | cons i is ih => exact ih (evalInstrA sa i)

theorem aMachine_pass (l : XLoop 64) (sa : AState) : aMachine.pass l sa = passA l sa := by
  simp [Machine.pass, passA, aMachine_runBlock]

theorem aMachine_runXLoop (fuel : Nat) (sa : AState) (l : XLoop 64) :
    aMachine.runXLoop fuel sa l = runXLoopA fuel sa l := by
  induction fuel generalizing sa with
  | zero => rfl
  | succ f ih => rw [Machine.runXLoop, runXLoopA, aMachine_pass, aMachine_view, ih]

/-! ## 2. The decoded `mpn_and_n_loop_owned` -/

/-- The prologue of the binary logical loops: the frame, the callee-saved stores, the
    argument spills, the reloads of `rp`, `ap` and `n`, the zero index and the count
    compare. -/
def binPrologue : List (JInstr 64) :=
  [ .lea "%rsp" "%rsp" "%rsp" 0 (-64)
  , .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi")
  , .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp")
  , .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13")
  , .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15")
  , .mov "%r14" (.reg "%rsi")
  , .storeMem "%rsp" (-8) (.reg "%rdx"), .storeMem "%rsp" (-16) (.reg "%rcx")
  , .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48
  , .loadMem "%rsi" "%rsp" (-16)
  , .mov "%rbx" (.reg "%rbx"), .mov "%rax" (.imm 0)
  , .mov "%rdi" (.reg "%rsi"), .cmp "%rdi" (.imm 0) ]

/-- The epilogue of the binary logical loops: the callee-saved reloads and the frame
    release. -/
def binEpilogue : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40, .loadMem "%rbp" "%rsp" 32
  , .loadMem "%r12" "%rsp" 24, .loadMem "%r13" "%rsp" 16
  , .loadMem "%r14" "%rsp" 8, .loadMem "%r15" "%rsp" 0
  , .lea "%rsp" "%rsp" "%rsp" 0 64 ]

/-- The segment before the loop: the prologue and the exit branch. -/
def binPre : List RInstr := binPrologue.map .op ++ [.jcc 4 37]

/-- The segment after the loop: the epilogue and `ret`. -/
def binPost : List RInstr := binEpilogue.map .op ++ [.ret]

/-- The decoded `and` loop program: the prologue, the exit branch, the loop segment of
    `andLoop`, the epilogue and `ret`. -/
theorem binDecoded_and_eq :
    binDecoded (andMidDecoded .and_)
      = binPre ++ (andLoop.body ++ [andLoop.cmpInstr]).map .op ++ [.jcc 5 binPre.length]
          ++ binPost := rfl

theorem binPre_length : binPre.length = 20 := rfl

/-- From the loop head, a terminating loop reaches the epilogue in its exit state. -/
theorem binDecoded_and_reaches_loop (fuel : Nat) (sa sa' : AState)
    (h : runXLoopA fuel sa andLoop = some sa') :
    Reaches aMachine (binDecoded (andMidDecoded .and_)) 20 sa 37 sa' := by
  have := reaches_xloop aMachine binPre andLoop binPost fuel sa sa'
    (by rwa [aMachine_runXLoop])
  rw [← binDecoded_and_eq, binPre_length] at this
  exact this

/-- The prologue runs from index `0` to the exit branch at index `19`. -/
theorem binDecoded_and_reaches_prologue (sa : AState) :
    Reaches aMachine (binDecoded (andMidDecoded .and_)) 0 sa 19 (runBlockA sa binPrologue) := by
  have := reaches_ops aMachine [] binPrologue ([.jcc 4 37]
    ++ (andLoop.body ++ [andLoop.cmpInstr]).map .op ++ [.jcc 5 binPre.length] ++ binPost) sa
  rw [aMachine_runBlock] at this
  exact this

/-- The epilogue runs from index `37` to `ret` at index `44`. -/
theorem binDecoded_and_reaches_epilogue (sa : AState) :
    Reaches aMachine (binDecoded (andMidDecoded .and_)) 37 sa 44 (runBlockA sa binEpilogue) := by
  have := reaches_ops aMachine (binPre ++ (andLoop.body ++ [andLoop.cmpInstr]).map .op
    ++ [.jcc 5 binPre.length]) binEpilogue [.ret] sa
  rw [aMachine_runBlock] at this
  exact this

theorem binDecoded_and_ret : (binDecoded (andMidDecoded .and_))[44]? = some .ret := by
  simp [binDecoded_and_eq, binPre, binPost, binPrologue, binEpilogue, andLoop]

theorem binDecoded_and_exit : (binDecoded (andMidDecoded .and_))[19]? = some (.jcc 4 37) := rfl

/-- The exit branch at index `19`: taken to the epilogue on `ZF`, else into the loop. -/
theorem binDecoded_and_step_exit (sa : AState) (b : Bool) (hz : sa.view.flagB (·.zf) = b) :
    step aMachine (binDecoded (andMidDecoded .and_)) 19 sa
      = some (if b then .go 37 sa else .go 20 sa) := by
  simp only [step, binDecoded_and_exit, condtOfNibble_four, Option.map_some, condB_e,
    aMachine_view, hz]

/-- **The decoded `mpn_and_n_loop_owned` runs as the prologue, `andLoop` and the
    epilogue.** From index `0`, when the counter after the prologue is nonzero and the
    loop of `AddrMemIdx.andLoop` exits in `sa'`, the decoded program halts without a call
    in `runBlockA sa' binEpilogue`. -/
theorem binDecoded_and_halts (fuel : Nat) (sa sa' : AState)
    (hz : (runBlockA sa binPrologue).view.flagB (·.zf) = false)
    (hl : runXLoopA fuel (runBlockA sa binPrologue) andLoop = some sa') :
    HaltsNoCall aMachine (binDecoded (andMidDecoded .and_)) 0 sa (runBlockA sa' binEpilogue) :=
  ⟨44, (binDecoded_and_reaches_prologue sa).trans
    ((Reaches.single (by rw [binDecoded_and_step_exit _ false hz, if_neg Bool.false_ne_true])).trans
      ((binDecoded_and_reaches_loop fuel _ sa' hl).trans
        (binDecoded_and_reaches_epilogue sa'))), binDecoded_and_ret⟩

/-- With a zero counter after the prologue the loop is skipped. -/
theorem binDecoded_and_halts_zero (sa : AState)
    (hz : (runBlockA sa binPrologue).view.flagB (·.zf) = true) :
    HaltsNoCall aMachine (binDecoded (andMidDecoded .and_)) 0 sa
      (runBlockA (runBlockA sa binPrologue) binEpilogue) :=
  ⟨44, (binDecoded_and_reaches_prologue sa).trans
    ((Reaches.single (by rw [binDecoded_and_step_exit _ true hz, if_pos rfl])).trans
      (binDecoded_and_reaches_epilogue _)), binDecoded_and_ret⟩

/-- The exit state of the decoded loop is related by `LoopRel` to the exit state of the
    named-ref loop: `andLoop_transfer` at the decoded program. -/
theorem binDecoded_and_transfer (P : String → BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hR : RegionsDisjoint andBank P (andRegions n)) (fuel : Nat) (sa sa' : AState)
    (js : JState 64) (hI : andInv n sa)
    (hrel : LoopRel andBank P (regionCells (andRegions n)) andA sa js)
    (hl : runXLoopA fuel sa andLoop = some sa') :
    Reaches aMachine (binDecoded (andMidDecoded .and_)) 20 sa 37 sa' ∧
      ∃ js', runXLoop fuel js { andLoop with body := andBodyNamed } = some js' ∧
        LoopRel andBank P (regionCells (andRegions n)) andA sa' js' := by
  refine ⟨binDecoded_and_reaches_loop fuel sa sa' hl, ?_⟩
  have h := andLoop_transfer P n hn hR fuel sa js hI hrel
  rw [hl] at h
  cases hj : runXLoop fuel js { andLoop with body := andBodyNamed } with
  | none => rw [hj] at h; exact h.elim
  | some js' => rw [hj] at h; exact ⟨js', rfl, h⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem
