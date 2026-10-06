/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfgTactic

/-!
# A leaf procedure called twice at the x86 instruction set

One `Lprog` program over `x86Isa.withCalls`, the x86 instruction set with the call and
return step of `VIR.LprogIsa`, written on virtual registers. It is an example of the call
rule `IsaCall.steps_call` inside the cut-point rule. The body of `callProg` holds a caller
and a leaf procedure:

* the procedure, at label `1`, doubles the register `x` and returns;
* the caller calls the procedure twice and jumps to the end of the body, label `2`.

The procedure has the specification `dbl_procSpec`: from label `1` with the word `a` in
`x`, one step reaches the `Lret` with `a + a` in `x`, every other register unchanged, and
the stack pointer and the memory unchanged. The caller is proved by the cut-point rule
`IsaCfg.corresIsa_of_cuts` with one segment, in which each call is an application of the
procedure-specification rule `IsaCall.steps_call` to `dbl_procSpec`, composed by
`IsaCfg.SegAt.of_seg`. The register `y` of the caller is carried across both calls by the
frame of the specification.

The example is a simpler relative of the x64 example `CallSwap` of the Kraken
verified-assembly framework: the callee changes one register and uses no stack frame. The
machine model maps no stack: the return address is one memory cell at the stack pointer,
and the callee has no local storage.

## Main results

* `dblI`, `lsemStepMem_dblI`: the doubling instruction and its step, registered with
  `isa_lopn`.
* `callProg`, `dbl_procSpec`: the program and the specification of its procedure.
* `call_corresIsa`: from counter `0`, `callProg` halts with four times the entry word of
  `x` in `x`, and `y` and the stack pointer unchanged.
* `call_run`: `call_corresIsa` on a machine state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCallDemo

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## The doubling instruction -/

/-- `d := a + a` at width `64`. -/
def dblI (d a : String) : LinstrRM := (.Lopn [.reg d] "ADD:64" [.reg a, .reg a], .reg none)

theorem lsemStepMem_dblI (d a : String) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (dblI d a) s = some (s.setReg d (va + va)).nextPc := by
  have := getW_of_lvm _ a va h
  isa_opn_proof dblI

macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnOne (lsemStepMem_dblI _ _))

/-! ## The program and the specification of its procedure -/

/-- Two calls of the procedure at label `1`, then a jump to the end, label `2`; the
    procedure doubles `x` and returns. -/
def callProg (fn : String) : LprogM := singletonProgM fn
  [ (.Lcall none (fn, 1), .reg none),
    (.Lcall none (fn, 1), .reg none),
    (.Lgoto (fn, 2), .reg none),
    (.Llabel .internal 1, .reg none),
    dblI "x" "x",
    (.Lret, .reg none),
    (.Llabel .internal 2, .reg none) ]

/-- The relation of the procedure: `x` holds the abstract word. -/
def dblSR (m : LstateMF) (a : BitVec 64) : Prop := m.prog.base.reg.lvm "x" = ⟨64, a⟩

/-- The frame of the procedure: every register other than `x` is unchanged. -/
def dblFrame (m m' : LstateMF) : Prop :=
  ∀ r : String, r ≠ "x" → m'.prog.base.reg.lvm r = m.prog.base.reg.lvm r

/-- **The specification of the doubling procedure.** From label `1` with the word `a` in
    `x`, one step reaches the `Lret` at counter `5` with `a + a` in `x`; the other registers,
    the stack pointer and the memory are unchanged. -/
theorem dbl_procSpec (fn : String) :
    ProcSpec x86Isa.withCalls (callProg fn) 1 5 dblSR (fun _ => True) (fun a => a + a)
      dblFrame 1 := by
  rintro m a ⟨q, hq, hat⟩ (hx : m.prog.base.reg.lvm "x" = ⟨64, a⟩) -
  obtain rfl : 3 = q := Option.some.inj hq
  refine SegAt.run ?_ hat
  isa_steps
  refine SegAt.done fun hat' => ⟨hat', ?_, ?_, ?_⟩
  · simp [dblSR]
  · intro r hr
    simp [hr]
  · exact fun v hv => ⟨(getW_congr (r := "RSP") 64 (by simp)).trans hv, by simp⟩

/-! ## The caller -/

/-- The state is in `fn` at the counter of the abstract triple, holds its words in `x` and
    `y`, and holds a word of width `64` in the stack pointer. -/
def callSR (fn : String) (sp : BitVec 64) (t : LstateMF) (a : BitVec 64 × BitVec 64 × Nat) :
    Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2.2 ∧ t.prog.base.reg.lvm "x" = ⟨64, a.1⟩ ∧
    t.prog.base.reg.lvm "y" = ⟨64, a.2.1⟩ ∧ t.prog.base.reg.lvm "RSP" = ⟨64, sp⟩

/-- One call of the procedure from a counter `k` of the caller: at most three steps reach
    the counter `k + 1` with `x` doubled and `y` and the stack pointer unchanged. -/
theorem call_segment (fn : String) {k : Nat} {m : LstateMF} {x y sp : BitVec 64}
    (hat : atPc (callProg fn) k m)
    (hi : (callProg fn).body[k]? = some (.Lcall none ((callProg fn).lfn, 1), .reg none))
    (hk : k + 1 < 2 ^ 64) (hx : m.prog.base.reg.lvm "x" = ⟨64, x⟩)
    (hy : m.prog.base.reg.lvm "y" = ⟨64, y⟩) (hsp : m.prog.base.reg.lvm "RSP" = ⟨64, sp⟩) :
    ∃ n m', n ≤ 3 ∧ Steps x86Isa.withCalls (callProg fn) n m m' ∧
      atPc (callProg fn) (k + 1) m' ∧ m'.prog.base.reg.lvm "x" = ⟨64, x + x⟩ ∧
      m'.prog.base.reg.lvm "y" = ⟨64, y⟩ ∧ m'.prog.base.reg.lvm "RSP" = ⟨64, sp⟩ := by
  obtain ⟨n, m₂, hn, hs, hat', hx2, hF⟩ := steps_call x86Isa (q := 3) (dbl_procSpec fn) rfl
    hat hi rfl (getW_of_lvm _ "RSP" sp hsp) hk
    (show dblSR (callEntry "RSP" sp 3 m) x by
      rw [dblSR, callEntry_lvm_of_ne _ _ _ _ (by decide), hx])
    trivial
  refine ⟨n, _, hn, hs, hat', ?_, ?_, retState_lvm_sp _ _ _ _⟩
  · rw [retState_lvm_of_ne _ _ _ _ (by decide)]
    exact hx2
  · rw [retState_lvm_of_ne _ _ _ _ (by decide), hF "y" (by decide),
      callEntry_lvm_of_ne _ _ _ _ (by decide), hy]

/-- **Two calls.** From counter `0` with a word of width `64` in the stack pointer,
    `callProg` halts at counter `7` with four times the entry word of `x` in `x`, and `y`
    and the stack pointer unchanged. -/
theorem call_corresIsa (fn : String) (sp : BitVec 64) :
    CorresIsa x86Isa.withCalls (callProg fn) (callSR fn sp) (fun a => a.2.2 = 0)
      (fun a => (a.1 + a.1 + (a.1 + a.1), a.2.1, 7)) (7 * (0 + 1)) := by
  isa_cutpoints (fun _ m a => callSR fn sp m a), (fun _ _ _ => 0), 7, 0 at []
  · rintro m a hSR hk
    exact ⟨⟨hSR.1, hSR.2.1.trans hk⟩, hSR, Nat.le_refl _⟩
  · rintro m ⟨x, y, pc⟩ - ⟨-, -, hx, hy, hsp⟩
    refine SegAt.of_seg (fun hat => call_segment fn hat rfl (by norm_num) hx hy hsp)
      fun m1 _ ⟨hx1, hy1, hsp1⟩ => ?_
    refine SegAt.of_seg (fun hat => call_segment fn hat rfl (by norm_num) hx1 hy1 hsp1)
      fun m2 ⟨hfn2, _⟩ ⟨hx2, hy2, hsp2⟩ => ?_
    isa_steps
    isa_exit
    simp [callSR, callProg, *]

/-- `call_corresIsa` on a machine state: from counter `0` in `fn` with the word `x` in `x`,
    `y` in `y` and `sp` in the stack pointer, the run of `callProg fn` returns a state with
    `x + x + (x + x)` in `x`, and `y` and the stack pointer unchanged. -/
theorem call_run (fn : String) (s : LstateMF) (x y sp : BitVec 64) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hx : s.prog.base.reg.lvm "x" = ⟨64, x⟩)
    (hy : s.prog.base.reg.lvm "y" = ⟨64, y⟩) (hsp : s.prog.base.reg.lvm "RSP" = ⟨64, sp⟩) :
    ∃ t, x86Isa.withCalls.lsemFuelMemF (callProg fn) 7 s = some t ∧
      t.prog.base.reg.lvm "x" = ⟨64, x + x + (x + x)⟩ ∧
      t.prog.base.reg.lvm "y" = ⟨64, y⟩ ∧ t.prog.base.reg.lvm "RSP" = ⟨64, sp⟩ := by
  obtain ⟨t, hrun, hSR⟩ := call_corresIsa fn sp s (x, y, 0) ⟨hfn, hpc, hx, hy, hsp⟩ rfl
  exact ⟨t, hrun, hSR.2.2.1, hSR.2.2.2.1, hSR.2.2.2.2⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCallDemo
