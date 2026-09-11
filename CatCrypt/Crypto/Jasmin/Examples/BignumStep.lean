/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.Examples.Curve25519CryptoptOps


@[expose] public section
set_option autoImplicit false

/-!
# `bignum_step`: per-instruction reduction lemmas for `bignumExecPlus`

Reasoning about a long `bignumExecPlus body s` chain by hand is tedious
(see the original `bzhi_step_correct` proof's hand-fed
`simp only [bignumExecPlus, execInstrPlus, evalPExpr, pv', vU',
writeSingleVar, lvR', setReg']` list). This file collects the per-shape
reduction lemmas that turn one InstrR's effect on the state into a
closed-form `setReg`/`storeMem`/etc. Tagged `@[simp]` so a single
`simp only [bignum_step]`-style invocation reduces a body's interpreter
output to a sequence of state updates.

The lemmas are stated with explicit hypotheses on register-name
distinctness or specific control-register values, so they fire only
where the preconditions hold. This avoids the "simp loops on every
`setReg`" pathology.

## Coverage

Currently covers the Copn shapes the F1 work needs:
- `BZHI_64` — extracts low N bits.
- `Olsr` Cassgn — right-shift via `evalCassgnPlus`.
- The list-recursion shape itself (`nil` and `cons` of `bignumExecPlus`).

Each new asm vocabulary item that comes up in proof gets its own
`@[simp]`-tagged step lemma here.
-/

namespace CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec

/-! ## §1. Body-recursion shape

The two `bignumExecPlus` arms unfolded at simp level. With these
tagged `@[simp]`, a goal `bignumExecPlus (i :: is) s = …` reduces
automatically to the bind form, which then composes with the
per-instruction step lemmas below. -/

@[simp]
theorem bignumExecPlus_nil (s : BignumState) :
    bignumExecPlus [] s = some s := rfl

@[simp]
theorem bignumExecPlus_cons (i : InstrR) (is : List InstrR)
    (s : BignumState) :
    bignumExecPlus (i :: is) s
      = (execInstrPlus s i).bind (fun s' => bignumExecPlus is s') := by
  cases h : execInstrPlus s i with
  | none   => simp [bignumExecPlus, h]
  | some _ => simp [bignumExecPlus, h]

/-- Splitting a body at any point: `bignumExecPlus (xs ++ ys) s` runs
    `xs` first, then `ys` on the resulting state. This is the basic
    composition primitive for **chunked correctness proofs** — split
    `mulBody` into 10-instruction chunks, prove each chunk's effect
    as a small lemma below the kernel cliff, then compose via this
    lemma. -/
theorem bignumExecPlus_append (xs ys : List InstrR) (s : BignumState) :
    bignumExecPlus (xs ++ ys) s
      = (bignumExecPlus xs s).bind (fun s' => bignumExecPlus ys s') := by
  induction xs generalizing s with
  | nil => simp [bignumExecPlus]
  | cons i is ih =>
    simp only [List.cons_append, bignumExecPlus_cons]
    cases h : execInstrPlus s i with
    | none   => simp
    | some s' => simp [ih s']

/-! ## §2. Per-opcode step lemmas

Each lemma fires when `execInstrPlus` is applied to an InstrR matching
that opcode's shape. The output state is given as a closed-form
`setReg` chain. Marked `@[simp]` so they fire automatically. -/

/-- `BZHI r out, src, ctrl` step, when `s.regs ctrl = 51`. The output
    register is set to `src & mask51`; all other state is unchanged. -/
@[simp]
theorem execInstrPlus_BZHI_51
    (s : BignumState) (rdst rsrc rctrl : String)
    (h : s.regs rctrl = 51) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"BZHI_64"⟩)
        [.Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rctrl, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg s rdst
                ((s.regs rsrc) &&& BitVec.ofNat 64 (2^51 - 1))) := by
  simp only [execInstrPlus, evalPExpr, writeSingleVar, setReg', bzhi, h]
  congr 1

/-- `Cassgn r := r >>> k` step (immediate-shift form, dispatched
    through `evalCassgnPlus`'s `Olsr` arm). -/
@[simp]
theorem execInstrPlus_Olsr_imm
    (s : BignumState) (r : String) (k : Int) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := r, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Papp2 (.Olsr .U64)
          (.Pvar { gv := { var := { vname := r, vtype := .sword .U64 } },
                   gs := false })
          (.Pconst k)))
      = some (setReg s r ((s.regs r) >>> (k.toNat % 64))) := by
  unfold execInstrPlus evalCassgnPlus setReg'
  simp only

/-- `Cassgn dst := lea_add a b` step (the simple `lea dst, [a + b]`
    pattern, encoded as `Papp2 Oadd`). Uses base `evalPExpr`. -/
@[simp]
theorem execInstrPlus_Cassgn_Oadd
    (s : BignumState) (rdst ra rb : String) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := rdst, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Papp2 (.Oadd .U64)
          (.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                   gs := false })
          (.Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                   gs := false })))
      = some (setReg s rdst ((s.regs ra) + (s.regs rb))) := by
  unfold execInstrPlus
  -- Falls through to the base interpreter's Cassgn-Lvar-Papp2 handler:
  -- evalCassgnPlus returns `none` on Oadd-of-Pvar-Pvar (only Olsr/Olsl/
  -- Oadd-with-Omul are matched), then execInstr dispatches.
  simp only [evalCassgnPlus, execInstr, evalPExpr]
  rfl

/-- `Cassgn dst := src` register-to-register `mov` step. -/
@[simp]
theorem execInstrPlus_Cassgn_movReg
    (s : BignumState) (rdst rsrc : String) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := rdst, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false }))
      = some (setReg s rdst (s.regs rsrc)) := by
  unfold execInstrPlus execInstr evalPExpr
  rfl

/-- `Cassgn dst := imm` immediate-load `mov` step. -/
@[simp]
theorem execInstrPlus_Cassgn_movImm
    (s : BignumState) (rdst : String) (k : Int) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := rdst, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Pconst k))
      = some (setReg s rdst (BitVec.ofInt 64 k)) := by
  unfold execInstrPlus execInstr evalPExpr
  rfl

/-- `Cassgn dst := [base + k]` memory-load `mov` step. -/
@[simp]
theorem execInstrPlus_Cassgn_movFromMem
    (s : BignumState) (rdst rbase : String) (k : Int) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := rdst, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Pload .U64
          { var := { vname := rbase, vtype := .sword .U64 } }
          (.Pconst k)))
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).bind
          (fun addr => (load64Mem s.mem addr).map
            (fun v => setReg s rdst (BitVec.ofNat 64 v.toNat)))) := by
  unfold execInstrPlus execInstr evalPExpr
  -- The `do let addr ← …; let v ← …; some (BitVec.ofNat 64 v.toNat)`
  -- followed by `setReg` is the unfolded base interpreter; matches the
  -- bind-form spec.
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr =>
    cases h2 : load64Mem s.mem addr with
    | none => simp [h, h2]
    | some v => simp [h, h2]

/-- `Cassgn [base + k] := src` memory-store `mov` step. -/
@[simp]
theorem execInstrPlus_Cassgn_movToMem
    (s : BignumState) (rbase rsrc : String) (k : Int) :
    execInstrPlus s
      (.Cassgn (.Lmem .U64
                { var := { vname := rbase, vtype := .sword .U64 } }
                (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false }))
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).map
          (fun addr => storeMem s addr
            (UInt64.ofNat (s.regs rsrc).toNat))) := by
  unfold execInstrPlus execInstr evalPExpr
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr => simp [h]

/-- `Cassgn dst := a + scale * b` (the `lea dst, [a + scale * b]`
    pattern). Dispatches through `evalCassgnPlus`'s Oadd-with-Omul arm. -/
@[simp]
theorem execInstrPlus_Cassgn_leaScaledAdd
    (s : BignumState) (rdst ra rb : String) (scale : Int) :
    execInstrPlus s
      (.Cassgn (.Lvar { var := { vname := rdst, vtype := .sword .U64 } })
        .AT_none (.sword .U64)
        (.Papp2 (.Oadd .U64)
          (.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                   gs := false })
          (.Papp2 (.Omul .U64)
            (.Pconst scale)
            (.Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                     gs := false }))))
      = some (setReg s rdst
                ((s.regs ra) + BitVec.ofInt 64 scale * (s.regs rb))) := by
  unfold execInstrPlus evalCassgnPlus setReg'
  simp only

/-- `ADD_64 a b` step: 6-LVal flag bundle. Updates `cf` and `dst`;
    other flags are `Lnone`. -/
@[simp]
theorem execInstrPlus_ADD_64
    (s : BignumState) (rcf rdst ra rb : String) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64),
              .Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rcf
                        (addCarry (s.regs ra) (s.regs rb)).1)
                rdst (addCarry (s.regs ra) (s.regs rb)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeSubBundle
  rfl

/-- `ADC_64 a b cin` step. -/
@[simp]
theorem execInstrPlus_ADC_64
    (s : BignumState) (rcf rdst ra rb rcin : String) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64),
              .Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADC_64"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rcin, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rcf
                        (addCarryIn (s.regs ra) (s.regs rb) (s.regs rcin)).1)
                rdst (addCarryIn (s.regs ra) (s.regs rb) (s.regs rcin)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeSubBundle
  rfl

/-- `ADC_64 a imm cin` step (immediate RHS — used for the
    `adc r, 0` pattern that propagates the final carry). -/
@[simp]
theorem execInstrPlus_ADC_64_imm
    (s : BignumState) (rcf rdst ra rcin : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64),
              .Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADC_64"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pconst k,
         .Pvar { gv := { var := { vname := rcin, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rcf
                        (addCarryIn (s.regs ra) (BitVec.ofInt 64 k)
                          (s.regs rcin)).1)
                rdst (addCarryIn (s.regs ra) (BitVec.ofInt 64 k)
                          (s.regs rcin)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeSubBundle
  rfl

/-- `ADCX a b cin` step (BMI2 dual-carry CF chain). -/
@[simp]
theorem execInstrPlus_ADCX
    (s : BignumState) (rcf rdst ra rb : String) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADCX"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rcf, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rcf
                        (addCarryIn (s.regs ra) (s.regs rb)
                          (s.regs rcf)).1)
                rdst (addCarryIn (s.regs ra) (s.regs rb)
                          (s.regs rcf)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeAdxBundle
  rfl

/-- `ADOX a b cin` step (BMI2 dual-carry OF chain). -/
@[simp]
theorem execInstrPlus_ADOX
    (s : BignumState) (rof rdst ra rb : String) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rof, vtype := .sword .U64 } },
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADOX"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rof, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rof
                        (addCarryIn (s.regs ra) (s.regs rb)
                          (s.regs rof)).1)
                rdst (addCarryIn (s.regs ra) (s.regs rb)
                          (s.regs rof)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeAdxBundle
  rfl

/-- `MULX hi lo, src` step (register source). -/
@[simp]
theorem execInstrPlus_MULX_reg
    (s : BignumState) (rhi rlo rrdx rsrc : String) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rhi, vtype := .sword .U64 } },
              .Lvar { var := { vname := rlo, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"MULX"⟩)
        [.Pvar { gv := { var := { vname := rrdx, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rhi
                        (mulx (s.regs rrdx) (s.regs rsrc)).1)
                rlo (mulx (s.regs rrdx) (s.regs rsrc)).2) := by
  unfold execInstrPlus execInstr evalPExpr writeMulxBundle
  rfl

/-- `MULX hi lo, [base + k]` step (memory source). -/
@[simp]
theorem execInstrPlus_MULX_mem
    (s : BignumState) (rhi rlo rrdx rbase : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rhi, vtype := .sword .U64 } },
              .Lvar { var := { vname := rlo, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"MULX"⟩)
        [.Pvar { gv := { var := { vname := rrdx, vtype := .sword .U64 } },
                 gs := false },
         .Pload .U64
           { var := { vname := rbase, vtype := .sword .U64 } }
           (.Pconst k)])
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).bind
          (fun addr => (load64Mem s.mem addr).map
            (fun v =>
              let p := mulx (s.regs rrdx) (BitVec.ofNat 64 v.toNat)
              setReg (setReg s rhi p.1) rlo p.2))) := by
  unfold execInstrPlus execInstr evalPExpr writeMulxBundle
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr =>
    cases h2 : load64Mem s.mem addr with
    | none => simp [h, h2]
    | some v => simp [h, h2]

/-- `IMUL_imm dst, src, k` step (register source). -/
@[simp]
theorem execInstrPlus_IMUL_imm_reg
    (s : BignumState) (rdst rsrc : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"IMUL_imm_64"⟩)
        [.Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false },
         .Pconst k])
      = some (setReg s rdst (imulImm (s.regs rsrc) k)) := by
  unfold execInstrPlus evalPExpr setReg'
  rfl

/-- `IMUL_imm dst, [base + k], imm` step (memory source). -/
@[simp]
theorem execInstrPlus_IMUL_imm_mem
    (s : BignumState) (rdst rbase : String) (k imm : Int) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"IMUL_imm_64"⟩)
        [.Pload .U64
           { var := { vname := rbase, vtype := .sword .U64 } }
           (.Pconst k),
         .Pconst imm])
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).bind
          (fun addr => (load64Mem s.mem addr).map
            (fun v => setReg s rdst (imulImm (BitVec.ofNat 64 v.toNat) imm)))) := by
  unfold execInstrPlus evalPExpr setReg'
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr =>
    cases h2 : load64Mem s.mem addr with
    | none => simp [h, h2]
    | some v => simp [h, h2]

/-- `AND_64 a b` step (6-LVal flag bundle). -/
@[simp]
theorem execInstrPlus_AND_64
    (s : BignumState) (rdst ra rb : String) :
    execInstrPlus s
      (.Copn [.Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"AND_64"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg s rdst (and64 (s.regs ra) (s.regs rb))) := by
  unfold execInstrPlus evalPExpr setReg'
  rfl

/-- `XOR_64 dst dst` self-xor step (zero-and-clear-flags). The
    `BignumExec.execInstr` arm matches this on the full 6-LVal flag
    bundle with both `of` (position 0) and `cf` (position 1) written. -/
@[simp]
theorem execInstrPlus_XOR_64_self
    (s : BignumState) (rof rcf rdst : String) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rof, vtype := .sword .U64 } },
              .Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
              .Lnone {} (.sword .U64),
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"XOR_64"⟩)
        [.Pvar { gv := { var := { vname := rdst, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rdst, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg (setReg s rof 0) rcf 0) rdst
                ((s.regs rdst) ^^^ (s.regs rdst))) := by
  unfold execInstrPlus execInstr evalPExpr writeXorBundle
  rfl

/-- `SHRD dst, src, k` step. -/
@[simp]
theorem execInstrPlus_SHRD_imm
    (s : BignumState) (rdst rsrc : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"SHRD_64_imm"⟩)
        [.Pvar { gv := { var := { vname := rdst, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rsrc, vtype := .sword .U64 } },
                 gs := false },
         .Pconst k])
      = some (setReg s rdst
                (shrdImm (s.regs rdst) (s.regs rsrc) k.toNat)) := by
  unfold execInstrPlus evalPExpr writeSingleVar setReg'
  rfl

/-- `TEST a, b` step (for the `test al, al`-style flag-clear before
    ADCX/ADOX chains). The 2-LVal output `[Lvar of, Lvar cf]` resets
    both carry tracks to 0. -/
@[simp]
theorem execInstrPlus_TEST
    (s : BignumState) (rof rcf ra rb : String) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rof, vtype := .sword .U64 } },
              .Lvar { var := { vname := rcf, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"TEST_64"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pvar { gv := { var := { vname := rb, vtype := .sword .U64 } },
                 gs := false }])
      = some (setReg (setReg s rof 0) rcf 0) := by
  unfold execInstrPlus evalPExpr writeTestBundle test64 setReg'
  rfl

/-- `ADCX a, [base + k], cin` step (memory source variant). -/
@[simp]
theorem execInstrPlus_ADCX_mem
    (s : BignumState) (rcf rdst ra rbase : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rcf, vtype := .sword .U64 } },
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADCX"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pload .U64
           { var := { vname := rbase, vtype := .sword .U64 } }
           (.Pconst k),
         .Pvar { gv := { var := { vname := rcf, vtype := .sword .U64 } },
                 gs := false }])
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).bind
          (fun addr => (load64Mem s.mem addr).map
            (fun v =>
              let p := addCarryIn (s.regs ra) (BitVec.ofNat 64 v.toNat)
                                  (s.regs rcf)
              setReg (setReg s rcf p.1) rdst p.2))) := by
  unfold execInstrPlus execInstr evalPExpr writeAdxBundle
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr =>
    cases h2 : load64Mem s.mem addr with
    | none => simp [h, h2]
    | some v => simp [h, h2]

/-- `ADOX a, [base + k], oin` step (memory source variant). -/
@[simp]
theorem execInstrPlus_ADOX_mem
    (s : BignumState) (rof rdst ra rbase : String) (k : Int) :
    execInstrPlus s
      (.Copn [.Lvar { var := { vname := rof, vtype := .sword .U64 } },
              .Lvar { var := { vname := rdst, vtype := .sword .U64 } }]
        .AT_none (.Oasm ⟨"ADOX"⟩)
        [.Pvar { gv := { var := { vname := ra, vtype := .sword .U64 } },
                 gs := false },
         .Pload .U64
           { var := { vname := rbase, vtype := .sword .U64 } }
           (.Pconst k),
         .Pvar { gv := { var := { vname := rof, vtype := .sword .U64 } },
                 gs := false }])
      = ((resolveAddr s
            { var := { vname := rbase, vtype := .sword .U64 } }
            (.Pconst k)).bind
          (fun addr => (load64Mem s.mem addr).map
            (fun v =>
              let p := addCarryIn (s.regs ra) (BitVec.ofNat 64 v.toNat)
                                  (s.regs rof)
              setReg (setReg s rof p.1) rdst p.2))) := by
  unfold execInstrPlus execInstr evalPExpr writeAdxBundle
  cases h : resolveAddr s
              { var := { vname := rbase, vtype := .sword .U64 } }
              (.Pconst k) with
  | none => simp [h]
  | some addr =>
    cases h2 : load64Mem s.mem addr with
    | none => simp [h, h2]
    | some v => simp [h, h2]

/-! ## §3. State-projection helpers

These let the simp set evaluate `(setReg s r v).regs r'` cleanly when
`r ≠ r'`, which is the standard sub-goal after composing two step
lemmas. -/

@[simp]
theorem setReg_regs_same (s : BignumState) (r : String) (v : BitVec 64) :
    (setReg s r v).regs r = v := by
  simp [setReg]

/-- `setReg` doesn't touch memory; useful for chained chunk proofs that
    need to look up `(setReg-chain).mem`. -/
@[simp]
theorem setReg_mem (s : BignumState) (r : String) (v : BitVec 64) :
    (setReg s r v).mem = s.mem := by
  simp [setReg]

/-- `BignumExec.storeMem` doesn't touch registers; useful for chunked
    composition where memory writes are interleaved with register lookups. -/
@[simp]
theorem storeMem_regs (s : BignumState) (a : UInt64) (v : UInt64) :
    (BignumExec.storeMem s a v).regs = s.regs := by
  simp [BignumExec.storeMem]

theorem setReg_regs_other (s : BignumState) (r r' : String)
    (v : BitVec 64) (h : r' ≠ r) :
    (setReg s r v).regs r' = s.regs r' := by
  simp [setReg, h]

/-- Convenience corollary: setReg on r-named field, when projecting r'
    with `r' ≠ r` (in either argument order), yields the original. -/
@[simp]
theorem setReg_regs_diff (s : BignumState) (r r' : String) (v : BitVec 64)
    (h : ¬ (r' = r)) :
    (setReg s r v).regs r' = s.regs r' :=
  setReg_regs_other s r r' v h

/-! ## §4. Smoke tests

Re-prove the F1 Phase 4 lemmas using the simp set. They should
collapse to one-liners. -/

example (s : BignumState) (h_ctrl : s.regs "rdi" = 51) :
    bignumExecPlus
      [.Copn [.Lvar { var := { vname := "r14", vtype := .sword .U64 } }]
         .AT_none (.Oasm ⟨"BZHI_64"⟩)
         [.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
                  gs := false },
          .Pvar { gv := { var := { vname := "rdi", vtype := .sword .U64 } },
                  gs := false }]]
      s
    = some (setReg s "r14"
              ((s.regs "r13") &&& BitVec.ofNat 64 (2^51 - 1))) := by
  simp [h_ctrl]

example (s : BignumState) (h_ctrl : s.regs "rdi" = 51) :
    bignumExecPlus
      [.Copn [.Lvar { var := { vname := "r14", vtype := .sword .U64 } }]
         .AT_none (.Oasm ⟨"BZHI_64"⟩)
         [.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
                  gs := false },
          .Pvar { gv := { var := { vname := "rdi", vtype := .sword .U64 } },
                  gs := false }],
       .Cassgn (.Lvar { var := { vname := "r13", vtype := .sword .U64 } })
         .AT_none (.sword .U64)
         (.Papp2 (.Olsr .U64)
           (.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
                    gs := false })
           (.Pconst 51))]
      s
    = some (setReg (setReg s "r14"
                      ((s.regs "r13") &&& BitVec.ofNat 64 (2^51 - 1)))
              "r13" ((s.regs "r13") >>> 51)) := by
  simp [h_ctrl]
  -- One-line `simp [hyp]` closes both instructions of the original
  -- `extract_and_carry_correct` proof. Was 15 LoC; now 1.

/-! ## §5. Composition smoke test

Three instructions in sequence — BZHI extracts a tight limb, SHR
shifts the wide value, and `lea`-add combines with another wide
digit. This is the exact 3-instruction repeating block in mulBody's
final reduction (asm lines 155–158, 159–161, …). If the simp set
composes here, it'll compose for the rest of the reduction tail. -/

def threeStepReduction : List InstrR :=
  [-- bzhi r14, r13, rdi      ; r14 = r13 & mask51
   .Copn [.Lvar { var := { vname := "r14", vtype := .sword .U64 } }]
     .AT_none (.Oasm ⟨"BZHI_64"⟩)
     [.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
              gs := false },
      .Pvar { gv := { var := { vname := "rdi", vtype := .sword .U64 } },
              gs := false }],
   -- shr r13, 51              ; r13 := r13 >>> 51
   .Cassgn (.Lvar { var := { vname := "r13", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Papp2 (.Olsr .U64)
       (.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
                gs := false })
       (.Pconst 51)),
   -- lea r13, [r13 + r11]     ; r13 := r13 + r11
   .Cassgn (.Lvar { var := { vname := "r13", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Papp2 (.Oadd .U64)
       (.Pvar { gv := { var := { vname := "r13", vtype := .sword .U64 } },
                gs := false })
       (.Pvar { gv := { var := { vname := "r11", vtype := .sword .U64 } },
                gs := false }))]

example (s : BignumState) (h : s.regs "rdi" = 51) :
    bignumExecPlus threeStepReduction s
    = some (setReg (setReg (setReg s "r14"
                              ((s.regs "r13") &&& BitVec.ofNat 64 (2^51 - 1)))
                       "r13" ((s.regs "r13") >>> (51 % 64)))
              "r13" (((s.regs "r13") >>> (51 % 64)) + (s.regs "r11"))) := by
  simp [threeStepReduction, h]

/-! ## §6. Six-instruction smoke test: epilogue spill restores

The last six instructions of `mulBody` restore the System V AMD64
callee-saved registers from spill slots. Each is a register-only
`Cassgn` (Pvar source); none touches memory. Smoke-prove that
running this 6-block leaves `mem` invariant — relevant for showing
the output limbs (written earlier in the body) survive the epilogue.

Composes 6 `execInstrPlus_Cassgn_movReg` step lemmas. -/

def epilogueRestores : List InstrR :=
  [.Cassgn (.Lvar { var := { vname := "rbx", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_80", vtype := .sword .U64 } },
              gs := false }),
   .Cassgn (.Lvar { var := { vname := "rbp", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_78", vtype := .sword .U64 } },
              gs := false }),
   .Cassgn (.Lvar { var := { vname := "r12", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_70", vtype := .sword .U64 } },
              gs := false }),
   .Cassgn (.Lvar { var := { vname := "r13", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_68", vtype := .sword .U64 } },
              gs := false }),
   .Cassgn (.Lvar { var := { vname := "r14", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_60", vtype := .sword .U64 } },
              gs := false }),
   .Cassgn (.Lvar { var := { vname := "r15", vtype := .sword .U64 } })
     .AT_none (.sword .U64)
     (.Pvar { gv := { var := { vname := "s_58", vtype := .sword .U64 } },
              gs := false })]

/-- The 6-instruction spill-restore epilogue does NOT touch memory:
    after running it, `mem` is exactly the input `mem`. Smoke validation
    that the simp set handles a 6-step sequence cleanly. -/
example (s : BignumState) :
    (bignumExecPlus epilogueRestores s).map (·.mem) = some s.mem := by
  simp [epilogueRestores, setReg]

end CatCrypt.Crypto.Jasmin.Curve25519CryptoptOps
