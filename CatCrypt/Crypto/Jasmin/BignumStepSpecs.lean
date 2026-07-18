/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

set_option autoImplicit false

/-!
# mvcgen-native `@[spec]` lemmas for `stepInstrM` instruction shapes

Structural-proof pilot. Instead of unfolding `stepInstrM`/`execInstr`
into raw state-transformer goals inside `mvcgen` (the expensive recipe
parked in `BignumHoare/Sqr4Phases.lean`), each instruction SHAPE used
by the `bignum_sqr_4` phases gets one Q-parametric Hoare triple proved
once from the step equation. `mvcgen` then composes these through its
`@[spec]` database and the per-instruction VCs stay small.

Spec shape follows `Std.Do.Spec.modifyGet_StateT`: the precondition is
the explicit weakest precondition (the register/memory update pushed
into `Q`), so applying the spec leaves only the continuation goal for
pure register updates. State-dependent partial operations (memory
loads) expose the `Option` match in the precondition; the resulting VC
is resolved by the caller's load hypotheses.

Usage (see `BignumHoare/Sqr4Phases.lean:sqr4_init_triple`): rewrite the
body literal with `bignumExecM_cons`/`bignumExecM_nil`, run `mvcgen`;
it composes the pure-update specs and stops at the first load with one
leaf VC of shape `(match load64Mem … with …).down`. Resolve the match
with the load hypothesis (plus `setReg` projections and the address
bridge), then continue with `mspec load64_spec` per remaining load —
`mvcgen` re-emits load-headed `(wp⟦·⟧ Q s).down` goals unchanged, while
`mspec` walks them fine. A trailing `mvcgen` discharges the final
`pure ()` and leaves the postcondition as a pure conjunction.
-/

namespace CatCrypt.Crypto.Jasmin.BignumStepSpecs

open Std.Do
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec

/-- The `PostShape` of `BignumM = StateT BignumState Option`. -/
abbrev psBM : PostShape := .arg BignumState (.except PUnit .pure)

/-- Build a `Triple` for a concrete `BignumM` program from a pointwise
    evaluation of its weakest precondition: if `P s` equals
    `wp⟦x⟧ Q s` for every `s` (ground it via `wp_apply_stateT_option`),
    the triple holds by reflexivity of entailment. -/
theorem triple_of_apply_eq {α : Type} (x : BignumM α)
    (P : Assertion psBM) (Q : PostCond α psBM)
    (h : ∀ s, P s = (wp (m := StateT BignumState Option) x).apply Q s) :
    Triple x P Q := by
  have hP : P = (wp (m := StateT BignumState Option) x).apply Q := funext h
  rw [Triple, hP]

/-! ### Pure register-update shapes -/

/-- `assignConst x k` — constant into register. Pure state update. -/
@[spec]
theorem assignConst_spec (r : BignumRegistry) (x : String) (k : Int)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM r (S2NBignumSSA.assignConst x k))
      (fun s => Q.1 () (setReg s x (BitVec.ofInt 64 k))) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.loadRdx src` — register-to-register move into `"rdx"`.
    Pure state update. -/
@[spec]
theorem loadRdx_spec (r : BignumRegistry) (src : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM r (S2NBignumSSA.BignumSqr4.loadRdx src))
      (fun s => Q.1 () (setReg s "rdx" (s.regs src))) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.mulx hi lo b` — BMI2 MULX: `(hi, lo) = rdx * b`. Two
    register writes (`writeMulxBundle`), no flags. Pure state update. -/
@[spec]
theorem mulx_spec (r : BignumRegistry) (hi lo b : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM r (S2NBignumSSA.BignumSqr4.mulx hi lo b))
      (fun s => Q.1 ()
        (setReg (setReg s hi (BignumExec.mulx (s.regs "rdx") (s.regs b)).1)
          lo (BignumExec.mulx (s.regs "rdx") (s.regs b)).2)) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.addCopn cfOut r a b` — `ADD_64` through the 6-LVal
    flag bundle (`writeSubBundle`): writes carry-out then sum. Pure
    state update. -/
@[spec]
theorem addCopn_spec (reg : BignumRegistry) (cfOut r a b : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM reg (S2NBignumSSA.BignumSqr4.addCopn cfOut r a b))
      (fun s => Q.1 ()
        (setReg (setReg s cfOut (BignumExec.addCarry (s.regs a) (s.regs b)).1)
          r (BignumExec.addCarry (s.regs a) (s.regs b)).2)) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.adcCopn cfOut r a b cin` — `ADC_64` (carry-in chain)
    through the 6-LVal flag bundle. Pure state update. -/
@[spec]
theorem adcCopn_spec (reg : BignumRegistry) (cfOut r a b cin : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM reg (S2NBignumSSA.BignumSqr4.adcCopn cfOut r a b cin))
      (fun s => Q.1 ()
        (setReg (setReg s cfOut
            (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs cin)).1)
          r (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs cin)).2)) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.adcxCopn cfOut r a b cin` — BMI2 `ADCX` (CF-only dual
    chain) through the 2-LVal bundle (`writeAdxBundle`). Pure state
    update. -/
@[spec]
theorem adcxCopn_spec (reg : BignumRegistry) (cfOut r a b cin : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM reg (S2NBignumSSA.BignumSqr4.adcxCopn cfOut r a b cin))
      (fun s => Q.1 ()
        (setReg (setReg s cfOut
            (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs cin)).1)
          r (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs cin)).2)) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.adoxCopn ofOut r a b oin` — BMI2 `ADOX` (OF-only dual
    chain) through the 2-LVal bundle. Same arithmetic as ADCX with the
    OF register as chain head. Pure state update. -/
@[spec]
theorem adoxCopn_spec (reg : BignumRegistry) (ofOut r a b oin : String)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM reg (S2NBignumSSA.BignumSqr4.adoxCopn ofOut r a b oin))
      (fun s => Q.1 ()
        (setReg (setReg s ofOut
            (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs oin)).1)
          r (BignumExec.addCarryIn (s.regs a) (s.regs b) (s.regs oin)).2)) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-- `BignumSqr4.store64 base k src` — 8-byte store of register `src`
    at `regs base + k` (`Lmem` Cassgn). `resolveAddr`/`evalPExpr` are
    total on this shape, so the update is pure (memory-only, via
    `storeMem`). -/
@[spec]
theorem store64_spec (reg : BignumRegistry) (base : String) (k : Int)
    (src : String) (Q : PostCond Unit psBM) :
    Triple (stepInstrM reg (S2NBignumSSA.BignumSqr4.store64 base k src))
      (fun s => Q.1 ()
        (storeMem s (UInt64.ofNat ((s.regs base + BitVec.ofInt 64 k).toNat))
          (UInt64.ofNat (s.regs src).toNat))) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]; rfl)

/-! ### Partial (memory-load) shapes

The precondition exposes the `Option` match on the load result; the
`none` branch demands the failure postcondition (`False` for
`PostCond.noThrow` consumers), so the generated VC is exactly "the
load succeeds and the continuation holds at the updated state". -/

/-- `BignumSqr4.load64 x base k` — 8-byte load at `regs base + k` into
    register `x`. -/
@[spec]
theorem load64_spec (r : BignumRegistry) (x base : String) (k : Int)
    (Q : PostCond Unit psBM) :
    Triple (stepInstrM r (S2NBignumSSA.BignumSqr4.load64 x base k))
      (fun s =>
        match load64Mem s.mem
            (UInt64.ofNat ((s.regs base + BitVec.ofInt 64 k).toNat)) with
        | some w => Q.1 () (setReg s x (BitVec.ofNat 64 w.toNat))
        | none => Q.2.1 PUnit.unit) Q :=
  triple_of_apply_eq _ _ _ (fun s => by
    rw [wp_apply_stateT_option]
    simp only [StateT.run, stepInstrM, execInstr, S2NBignumSSA.BignumSqr4.load64,
               S2NBignumSSA.BignumSqr4.lvR, S2NBignumSSA.BignumSqr4.pload,
               S2NBignumSSA.v, evalPExpr, resolveAddr,
               Option.bind_eq_bind, Option.bind_some]
    cases load64Mem s.mem
        (UInt64.ofNat ((s.regs base + BitVec.ofInt 64 k).toNat)) <;> rfl)

/-! ### VC-closing helpers

Small rewrite lemmas for discharging the per-load VCs that
`load64_spec` leaves behind, without unfolding `setReg` into record
literals (keeps subsequent spec applications small). `setReg_regs` /
`setReg_mem` restate `Curve25519CryptoptOps.setReg_regs_*` from
`Examples/BignumStep.lean` locally to keep this file's import cone to
`BignumExec` + `S2NBignumSSA`. -/

/-- `setReg` projection: register reads go through pointwise; resolve
    the string comparison via `String.reduceEq` + `reduceIte`. -/
theorem setReg_regs (s : BignumState) (x y : String) (v : BitVec 64) :
    (setReg s x v).regs y = if y = x then v else s.regs y := rfl

/-- `setReg` does not touch memory. -/
theorem setReg_mem (s : BignumState) (x : String) (v : BitVec 64) :
    (setReg s x v).mem = s.mem := rfl

/-- Address bridge: the `BitVec`-level base+offset computation produced
    by `load64_spec`'s precondition equals `UInt64` base+offset. -/
theorem load_addr_bridge (b : UInt64) (k : BitVec 64) :
    UInt64.ofNat ((BitVec.ofNat 64 b.toNat + k).toNat)
      = b + UInt64.ofNat k.toNat := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, BitVec.toNat_add, Nat.add_mod]

end CatCrypt.Crypto.Jasmin.BignumStepSpecs
