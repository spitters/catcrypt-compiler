/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminJumpLevel

/-!
# A Jasmin-source `while` loop at the jump level of the x86 instruction set

The Jasmin body `one = 1; while (n != 0) { acc = acc + x; n = n - one; }` adds `n` copies of
`x` to `acc`. `BignumToJLoops.toSB` translates it to a structured program `prog`, and
`JasminJumpLevel.compileS` compiles `prog` to labelled code `code` in the function `sum`: a
loop head label, the flag compare of `n` with `0`, a conditional jump to the exit label on
the zero flag, the two lowered assignments, and a back jump. The instruction list is the
value of the compilation; no instruction is written by hand.

`JasminJumpLevel.corresIsa_of_bignumExec` gives the `CorresIsa x86Isa` judgement of the
compiled program against `bignumExecFuel`, and `sum_run` restates it on a machine state
together with the exit property `n = 0` of the source loop.

@ascent-fixture theorems: sum_corresIsa, sum_run

## Main results

* `toSB_eq`, `compileS_eq`: the body is in the fragments of the two translations.
* `sum_corresIsa`: `CorresIsa x86Isa` of the compiled loop against `bignumExecFuel`.
* `n_eq_zero`: a run of the source loop ends with `n = 0`.
* `sum_run`: the run of the compiled loop on a machine state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.JasminJumpDemo

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.BignumToJLoops
open CatCrypt.Crypto.Jasmin.JazzToInstrR.RoundTrip
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.JasminJumpLevel

/-- The Jasmin body `one = 1; while (n != 0) { acc = acc + x; n = n - one; }`. -/
def body : List InstrR :=
  [ .Cassgn (lv (u "one")) .AT_none (.sword .U64) (.Pconst 1)
  , .Cwhile [] AddN.guard
      [ AddN.bin (.Oadd .U64) "acc" "acc" "x"
      , AddN.bin (.Osub .U64) "n" "n" "one" ] ]

theorem toSB_isSome : (toSB body).isSome = true := by decide

/-- The structured translation of the loop. -/
def prog : SProg := (toSB body).getD (.block [])

theorem toSB_eq : toSB body = some prog := by
  have h := toSB_isSome
  revert h
  unfold prog
  cases toSB body <;> simp

theorem compileS_isSome : (compileS "sum" prog 0).isSome = true := by decide

/-- The labelled code of the loop in the function `sum`. -/
def code : List LinstrRM := ((compileS "sum" prog 0).getD ([], 0)).1

theorem compileS_eq :
    compileS "sum" prog 0 = some (code, ((compileS "sum" prog 0).getD ([], 0)).2) := by
  have h := compileS_isSome
  revert h
  unfold code
  cases compileS "sum" prog 0 <;> simp

/-- **The loop at the jump level.** The compiled program corresponds to the run
    `bignumExecFuel reg fuel body` on the states where that run is defined. -/
theorem sum_corresIsa (reg : BignumRegistry) (fuel : Nat) :
    CorresIsa x86Isa (singletonProgM "sum" code) (RegSR "sum" BignumState.regs)
      (fun a => (bignumExecFuel reg fuel body a.1).isSome = true ∧ a.2 = 0)
      (fun a => ((bignumExecFuel reg fuel body a.1).getD a.1, code.length))
      (stepBound prog fuel) :=
  corresIsa_of_bignumExec reg fuel body prog toSB_eq "sum" 0 _ code compileS_eq

/-- A run of the loop ends with `n = 0`. -/
theorem n_eq_zero (reg : BignumRegistry) (fuel : Nat) {s s' : BignumState}
    (he : bignumExecFuel reg fuel body s = some s') : s'.regs "n" = 0 := by
  obtain ⟨m, -, h2⟩ := bignumExecFuel_append_same reg fuel (body.take 1) (body.drop 1) s s' he
  obtain ⟨v, hv, hz⟩ := while_exit reg fuel m s' h2
  simp only [AddN.guard, evalPExpr, pv, u, Option.bind_eq_bind, Option.bind_some,
    Option.some.injEq] at hv
  subst hv
  simpa using hz

/-- **The run of the loop on a machine state.** If `bignumExecFuel` takes `s` to `s'`, the
    run of the x86 instruction set on the compiled program at the fuel `stepBound prog fuel`,
    from a state of the function `sum` at the counter `0` whose registers read back those of
    `s`, halts at the end of the code in a state whose registers read back those of `s'`,
    with the register `n` at `0`. -/
theorem sum_run (reg : BignumRegistry) (fuel : Nat) {s s' : BignumState} {m : LstateMF}
    (he : bignumExecFuel reg fuel body s = some s') (hfn : m.prog.lfn = "sum")
    (hpc : m.prog.base.lpc = 0) (hreg : ∀ r, m.prog.base.reg.getW r 64 = some (s.regs r)) :
    ∃ m', x86Isa.lsemFuelMemF (singletonProgM "sum" code) (stepBound prog fuel) m = some m' ∧
      m'.prog.base.lpc = code.length ∧
      (∀ r, m'.prog.base.reg.getW r 64 = some (s'.regs r)) ∧
      m'.prog.base.reg.getW "n" 64 = some 0 := by
  obtain ⟨m', hrun, -, hpc', hreg'⟩ :=
    sum_corresIsa reg fuel m (s, 0) ⟨hfn, hpc, hreg⟩ ⟨by simp [he], rfl⟩
  simp only [he, Option.getD_some] at hpc' hreg'
  exact ⟨m', hrun, hpc', hreg', by rw [hreg' "n", n_eq_zero reg fuel he]⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.JasminJumpDemo
