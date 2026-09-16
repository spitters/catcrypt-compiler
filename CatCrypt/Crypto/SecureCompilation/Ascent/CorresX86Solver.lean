/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.CorresAttr
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresSolver
public import CatCrypt.Crypto.SecureCompilation.Ascent.XrunRunBlockTie
public import Lean

/-!
# `corres_solve_x86`: the value leaves of the x86 ascent and their solver

`corres_solve` (`CorresSolver`) composes the carry-family `@[corres]` leaves
(`corresJ_sbb`, `corresJ_adc`, `corresJ_mulx`, `corresJ_adcx`, …) over a
straight-line `JInstr` block. This module supplies the value leaves for the
instructions the x86 `ScalarTarget` emits (`x86Target.compile`, translated to
`JInstr` by `xinstrToJ`), registers them under the same `@[corres]` attribute,
and wraps the solver so that a block stated over the `Model`'s `Instr 64` —
the form the descent produces — is normalised to its `JInstr` transcription
first. The x86 twin of `corres_solve_rv` (`CorresRiscvSolver`).

* `AStateX` is the register-only abstract state, `String → BitVec 64`; `SRx`
  relates a machine state to it by agreement of every register. No flag is
  tracked, so the leaves are the flag-free value steps: an instruction that
  reads a flag (`adc`/`sbb`/`adcx`/`adox`/`cmov`) has no `SRx` leaf and is
  refined under `SRcarry`/`SRcarry2` by the carry-family leaves.
* `writeX` is the abstract register write, `evalX` the abstract operand read.
* `corresJ_of_regs` states the leaf once for any instruction whose effect on
  the register file is one write; `corresJ_movX` … `corresJ_negX` are its
  instances, and `corresJ_mulxX` is the two-write `mulx` leaf.
* `corres_solve_x86` normalises `x86Target.compile p`, `toX86`, and
  `List.map xinstrToJ` in the goal's block and runs `corres_solve`. `corres_sym`
  (`CorresSolver`) closes the same goals without the normalisation step.

## Main results

* `corresJ_of_regs`: the leaf for any instruction whose register effect is a
  single write.
* `corresJ_movX`, `corresJ_addX`, `corresJ_subX`, `corresJ_imulX`,
  `corresJ_andX`, `corresJ_orX`, `corresJ_xorX`, `corresJ_shlX`,
  `corresJ_shrX`, `corresJ_sarX`, `corresJ_notX`, `corresJ_negX`,
  `corresJ_mulxX`: one leaf per value instruction of `xinstrToJ`'s image.
* `corres_solve_x86`: the tactic composing the `@[corres]` leaves over a
  straight-line block given as `JInstr`s, as translated `Instr 64`s, or as
  the compiled output of the x86 `ScalarTarget`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## The register-only abstract state and its relation -/

/-- The register-only abstract x86 state. -/
abbrev AStateX : Type := String → BitVec 64

/-- `SRx`: machine and abstract states agree on every register. -/
def SRx (st : JState 64) (a : AStateX) : Prop :=
  ∀ r, st.regs r = a r

/-- The abstract register write. -/
def writeX (d : String) (v : BitVec 64) (a : AStateX) : AStateX :=
  fun r => if r = d then v else a r

/-- The abstract operand read: a register from the state, an immediate as its
    word. -/
def evalX (a : AStateX) : JOperand → BitVec 64
  | .reg r => a r
  | .imm v => BitVec.ofNat 64 v

/-- A machine operand read agrees with the abstract one across `SRx`. -/
theorem evalX_eq (st : JState 64) (a : AStateX) (h : SRx st a) (o : JOperand) :
    o.eval st = evalX a o := by
  cases o with
  | reg r => exact h r
  | imm v => rfl

/-- The leaf for any instruction whose effect on the register file is the single
    write `d := g s`: it refines the abstract write `writeX d (f a)` whenever the
    written word agrees across `SRx`. -/
theorem corresJ_of_regs (i : JInstr 64) (d : String) (g : JState 64 → BitVec 64)
    (f : AStateX → BitVec 64)
    (hi : ∀ s, (evalInstr s i).regs = fun r => if r = d then g s else s.regs r)
    (hfg : ∀ s a, SRx s a → g s = f a) :
    CorresJ SRx (fun _ => True) (fun a => writeX d (f a) a) [i] := by
  intro s a hSR _ r
  rw [runBlock_cons, runBlock_nil, hi]
  by_cases hr : r = d
  · subst hr
    simp [writeX, hfg s a hSR]
  · simp [writeX, hr, hSR r]

/-! ## The abstract single-instruction transitions -/

/-- `mov d o`: `d := o`. -/
def movStepX (d : String) (o : JOperand) (a : AStateX) : AStateX := writeX d (evalX a o) a

/-- `add d o`: `d := d + o`, wrapping. -/
def addStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d + evalX a o) a

/-- `sub d o`: `d := d - o`, wrapping. -/
def subStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d - evalX a o) a

/-- `imul d o`: `d :=` the low 64 bits of the product. -/
def imulStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d * evalX a o) a

/-- `and d o`: `d := d &&& o`. -/
def andStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d &&& evalX a o) a

/-- `or d o`: `d := d ||| o`. -/
def orStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d ||| evalX a o) a

/-- `xor d o`: `d := d ^^^ o`. -/
def xorStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d ^^^ evalX a o) a

/-- `shl d o`: `d := d <<< (o mod 64)`, the count masked as Jasmin masks it. -/
def shlStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d <<< ((evalX a o).toNat % 64)) a

/-- `shr d o`: `d := d >>> (o mod 64)`, the logical shift by the masked count. -/
def shrStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (a d >>> ((evalX a o).toNat % 64)) a

/-- `sar d o`: the arithmetic right shift by the masked count. -/
def sarStepX (d : String) (o : JOperand) (a : AStateX) : AStateX :=
  writeX d (BitVec.sshiftRight (a d) ((evalX a o).toNat % 64)) a

/-- `not d`: `d := ~~~d`. -/
def notStepX (d : String) (a : AStateX) : AStateX := writeX d (~~~ a d) a

/-- `neg d`: `d := 0 - d`. -/
def negStepX (d : String) (a : AStateX) : AStateX := writeX d (0 - a d) a

/-- `mulx dHi dLo x y`: `dLo :=` the low word and `dHi :=` the high word of the
    128-bit product `x * y`, the high write last (so it wins when `dHi = dLo`,
    the `umulh` selection of `toX86`). -/
def mulxStepX (dHi dLo : String) (x y : JOperand) (a : AStateX) : AStateX :=
  writeX dHi (BitVec.ofNat 64 ((evalX a x).toNat * (evalX a y).toNat / 2 ^ 64))
    (writeX dLo (BitVec.ofNat 64 ((evalX a x).toNat * (evalX a y).toNat)) a)

/-! ## The leaves -/

/-- `mov` refines `movStepX`. -/
theorem corresJ_movX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (movStepX d o) [.mov d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl) (fun s a h => evalX_eq s a h o)

/-- `add` refines `addStepX`. -/
theorem corresJ_addX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (addStepX d o) [.add d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_ADD, rflags_of_aluop, JState.get, h d, evalX_eq s a h])

/-- `sub` refines `subStepX`. -/
theorem corresJ_subX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (subStepX d o) [.sub d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_SUB, JState.get, h d, evalX_eq s a h])

/-- `imul` refines `imulStepX`. -/
theorem corresJ_imulX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (imulStepX d o) [.imul d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_IMULt, rflags_of_mul, JState.get, h d, evalX_eq s a h])

/-- `and` refines `andStepX`. -/
theorem corresJ_andX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (andStepX d o) [.and_ d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_AND, rflags_of_bwop, JState.get, h d, evalX_eq s a h])

/-- `or` refines `orStepX`. -/
theorem corresJ_orX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (orStepX d o) [.or_ d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_OR, rflags_of_bwop, JState.get, h d, evalX_eq s a h])

/-- `xor` refines `xorStepX`. -/
theorem corresJ_xorX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (xorStepX d o) [.xor_ d o] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl)
    (fun s a h => by simp only [x86_XOR, rflags_of_bwop, JState.get, h d, evalX_eq s a h])

/-- `shl` refines `shlStepX`. -/
theorem corresJ_shlX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (shlStepX d o) [.shl d o] :=
  corresJ_of_regs _ d (fun s => s.get d <<< ((o.eval s).toNat % 64)) _
    (fun s => by funext r; simp only [evalInstr, JState.writeB5W, x86_SHL_word, JState.get])
    (fun s a h => by simp only [JState.get, h d, evalX_eq s a h])

/-- `shr` refines `shrStepX`. -/
theorem corresJ_shrX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (shrStepX d o) [.shr d o] :=
  corresJ_of_regs _ d (fun s => s.get d >>> ((o.eval s).toNat % 64)) _
    (fun s => by funext r; simp only [evalInstr, JState.writeB5W, x86_SHR_word, JState.get])
    (fun s a h => by simp only [JState.get, h d, evalX_eq s a h])

/-- `sar` refines `sarStepX`. -/
theorem corresJ_sarX (d : String) (o : JOperand) :
    CorresJ SRx (fun _ => True) (sarStepX d o) [.sar d o] :=
  corresJ_of_regs _ d (fun s => BitVec.sshiftRight (s.get d) ((o.eval s).toNat % 64)) _
    (fun s => by funext r; simp only [evalInstr, JState.writeB5W, x86_SAR_word, JState.get])
    (fun s a h => by simp only [JState.get, h d, evalX_eq s a h])

/-- `not` refines `notStepX`. -/
theorem corresJ_notX (d : String) :
    CorresJ SRx (fun _ => True) (notStepX d) [.not_ d] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl) (fun s a h => by simp only [x86_NOT, JState.get, h d])

/-- `neg` refines `negStepX`. -/
theorem corresJ_negX (d : String) :
    CorresJ SRx (fun _ => True) (negStepX d) [.neg d] :=
  corresJ_of_regs _ d _ _ (fun _ => rfl) (fun s a h => by simp only [x86_NEG, JState.get, h d])

/-- `mulx` refines `mulxStepX`. -/
theorem corresJ_mulxX (dHi dLo : String) (x y : JOperand) :
    CorresJ SRx (fun _ => True) (mulxStepX dHi dLo x y) [.mulx dHi dLo x y] := by
  intro s a hSR _ r
  simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi, wumul, high_bits,
    JState.setReg, mulxStepX, writeX, evalX_eq s a hSR]
  by_cases hHi : r = dHi
  · simp [hHi]
  · by_cases hLo : r = dLo
    · simp [hLo]
    · simp [hHi, hLo, hSR r]

/-! ## The `@[corres]` registrations -/

attribute [corres] corresJ_movX corresJ_addX corresJ_subX corresJ_imulX corresJ_andX
  corresJ_orX corresJ_xorX corresJ_shlX corresJ_shrX corresJ_sarX corresJ_notX corresJ_negX
  corresJ_mulxX

/-! ## The tactic -/

/-- Refine a `CorresJ` over a straight-line x86 block by composing the registered
    `@[corres]` leaves. The block may be given as `JInstr`s, as the translation
    `xs.map xinstrToJ` of a `Model` block `xs : List (Instr 64)`, or as the
    compiled output `x86Target.compile p` of a `RegProg` literal; the
    normalisation unfolds `ScalarTarget.compile`, `toX86`, `List.map` and
    `xinstrToJ` to the `JInstr` list, and `corres_solve` composes the leaves
    against the goal's transition. -/
syntax "corres_solve_x86" : tactic
macro_rules
  | `(tactic| corres_solve_x86) =>
    `(tactic|
      ((try simp only [ScalarTarget.compile, x86Target, toX86, List.flatMap_cons,
          List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.append_nil, xinstrToJ, operandToJ])
       corres_solve))

/-! ## Tests

The tests are closed by `corres_sym` (`CorresSolver`), which puts a block given as
`xs.map xinstrToJ` or as `x86Target.compile p` in weak head normal form itself. -/

/-- A `JInstr` block: a move, an add, a subtract, a shift by an immediate. -/
theorem corres_solve_x86_alu (r a b c : String) :
    CorresJ SRx (fun _ => True)
      (fun st => shlStepX r (.imm 3) (subStepX r (.reg c) (addStepX r (.reg b)
        (movStepX r (.reg a) st))))
      [.mov r (.reg a), .add r (.reg b), .sub r (.reg c), .shl r (.imm 3)] := by
  corres_sym

/-- A `Model` block, translated by `xinstrToJ`. -/
theorem corres_solve_x86_translated (r a b : String) :
    CorresJ SRx (fun _ => True)
      (fun st => addStepX r (.reg b) (movStepX r (.reg a) st))
      ([Instr.mov r (.reg a), Instr.add r (.reg b)].map xinstrToJ) := by
  corres_sym

/-- The compiled output of the x86 `ScalarTarget` on a two-statement program,
    translated by `xinstrToJ`: each statement is the two-address pair `mov; op`. -/
theorem corres_solve_x86_compiled (r s a b : String) :
    CorresJ SRx (fun _ => True)
      (fun st => shrStepX s (.imm 3) (movStepX s (.reg r)
        (addStepX r (.reg b) (movStepX r (.reg a) st))))
      ((x86Target.compile [.add r a b, .shrI s r 3]).map xinstrToJ) := by
  corres_sym

/-- The `umulh` selection: `mulx d d a b` leaves the high word in `d`. -/
theorem corres_solve_x86_umulh (d a b : String) :
    CorresJ SRx (fun _ => True)
      (fun st => mulxStepX d d (.reg a) (.reg b) st)
      ((x86Target.compile [.umulh d a b]).map xinstrToJ) := by
  corres_sym

end CatCrypt.Crypto.SecureCompilation.Ascent
