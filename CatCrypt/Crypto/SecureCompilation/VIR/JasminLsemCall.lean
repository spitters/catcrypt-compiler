/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled

@[expose] public section

set_option autoImplicit false

/-!
# Internal calls in the labeled linear semantics: `Lcall` / `Lret`

The internal call/return control flow for the labeled, program-indexed linear
semantics (`JasminLsemLabeled`'s `find_label`/`eval_jump`/`find_instr`/`eval_instr`).

## Fidelity to `linear_sem.v`

jasmin's linear call/return threads a **return address** (`linear_sem.v`'s
`Lcall`/`Lret` use the RASP — return-address stack pointer — and `encode_label` /
`decode_label`). The control-flow content of that mechanism is modeled at the surface
as an explicit **return-address stack** of `(funname, pc)` resume points, abstracting
the pointer encoding/decoding (as `JasminLsemLabeled` does for `Lcond`'s
`sem_fexpr … >>= to_bool`):

* **`Lcall ra d`** records the resume point `(lfn, lpc+1)` — the instruction *after*
  the call (matching `eval_jump`'s `pc.+1` discipline) — pushes it, and jumps to the
  callee target `d` via the same `evalJump` the labeled layer uses.
* **`Lret`** pops the top resume point and resumes there (`setcpc`); on an empty stack
  it is `none` (return with no caller — jasmin's `type_error`).

`LstateC` wraps `LstateP` with the return stack (as `LstateP` wraps `Lstate` with
`lfn`), and `evalInstrC` delegates every non-call/return arm to `evalInstrP`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCall

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

variable {w : Nat}

/-! ## 1. The call-aware program state -/

/-- `LstateP` plus a **return-address stack** of `(funname, resume-pc)` pairs — the
    control-flow content of jasmin's RASP. `Lcall` pushes, `Lret` pops. -/
structure LstateC (w : Nat) extends LstateP w where
  /-- The return-address stack: resume points, innermost call on top. -/
  lretStack : List (String × Nat) := []

/-! ## 2. `eval_jump` carrying the return stack -/

/-- `evalJump` lifted to `LstateC`: resolve the remote label / set `(lfn, lpc)` exactly
    as the labeled layer does, carrying the return stack through unchanged. -/
def evalJumpC (P : Lprog) (d : String × LLabel) (s : LstateC w) : Option (LstateC w) :=
  (evalJump P d s.toLstateP).map (fun s' => { toLstateP := s', lretStack := s.lretStack })

/-! ## 3. `eval_instr` with the call/return arms -/

/-- The program step with internal-call control flow. Non-call/return instructions
    delegate to `JasminLsemLabeled.evalInstrP` (carrying the return stack); `Lcall`
    pushes the resume point and jumps; `Lret` pops and resumes. -/
def evalInstrC (P : Lprog) (i : LinstrR) (s : LstateC w) : Option (LstateC w) :=
  match i with
  | .Lcall _ d =>
      (evalJump P d s.toLstateP).map
        (fun s' => { toLstateP := s', lretStack := (s.lfn, s.base.lpc + 1) :: s.lretStack })
  | .Lret =>
      match s.lretStack with
      | (fn, pc) :: rest => some { toLstateP := s.toLstateP.setcpc fn pc, lretStack := rest }
      | [] => none
  | i =>
      (evalInstrP P i s.toLstateP).map
        (fun s' => { toLstateP := s', lretStack := s.lretStack })

/-! ## 4. The single-step structural lemmas -/

/-- **`Lcall` pushes the resume point and jumps.** The resume point is the instruction
    after the call (`lpc+1`), the call target is reached via `evalJump`. -/
theorem evalInstrC_Lcall (P : Lprog) (ra : Option String) (d : String × LLabel)
    (s : LstateC w) :
    evalInstrC P (.Lcall ra d) s
      = (evalJump P d s.toLstateP).map
          (fun s' => { toLstateP := s', lretStack := (s.lfn, s.base.lpc + 1) :: s.lretStack }) :=
  rfl

/-- **`Lret` pops the top resume point and resumes there.** -/
theorem evalInstrC_Lret_cons (P : Lprog) (fn : String) (pc : Nat)
    (rest : List (String × Nat)) (s : LstateC w) (h : s.lretStack = (fn, pc) :: rest) :
    evalInstrC P .Lret s
      = some { toLstateP := s.toLstateP.setcpc fn pc, lretStack := rest } := by
  simp only [evalInstrC, h]

/-- **`Lret` on an empty stack halts** (no caller to return to — jasmin `type_error`). -/
theorem evalInstrC_Lret_nil (P : Lprog) (s : LstateC w) (h : s.lretStack = []) :
    evalInstrC P .Lret s = none := by
  simp only [evalInstrC, h]

/-- **Non-call instructions delegate to the labeled layer** (carrying the return stack).
    So `evalInstrC` is a conservative extension of `evalInstrP`. -/
theorem evalInstrC_delegate (P : Lprog) (i : LinstrR) (s : LstateC w)
    (hcall : ∀ ra d, i ≠ .Lcall ra d) (hret : i ≠ .Lret) :
    evalInstrC P i s
      = (evalInstrP P i s.toLstateP).map
          (fun s' => { toLstateP := s', lretStack := s.lretStack }) := by
  cases i with
  | Lcall ra d => exact absurd rfl (hcall ra d)
  | Lret => exact absurd rfl hret
  | _ => rfl

/-! ## 5. The call/return roundtrip (the discipline `Lret` restores) -/

/-- **Call/return is balanced on the stack** (the stack discipline `Lret` restores). After
    a `Lcall` produces `s'`, an immediately-following `Lret` succeeds, pops exactly the
    frame the call pushed (restoring the caller's return stack), and resumes at the
    caller's return target: function `s.lfn`, pc `s.base.lpc + 1` (the instruction after
    the call). The base case of the discipline any well-bracketed, return-stack-neutral
    callee body respects between its entry `Lcall` and its `Lret`. -/
theorem call_ret_roundtrip (P : Lprog) (ra : Option String) (d : String × LLabel)
    (s s' : LstateC w)
    (hcall : evalInstrC P (.Lcall ra d) s = some s') :
    ∃ sret, evalInstrC P .Lret s' = some sret
      ∧ sret.lretStack = s.lretStack
      ∧ sret.lfn = s.lfn
      ∧ sret.base.lpc = s.base.lpc + 1 := by
  rw [evalInstrC_Lcall] at hcall
  rcases hj : evalJump P d s.toLstateP with _ | sj
  · rw [hj] at hcall; exact absurd hcall (by simp)
  · rw [hj] at hcall
    simp only [Option.map_some] at hcall
    obtain rfl := Option.some.inj hcall
    refine ⟨_, evalInstrC_Lret_cons P s.lfn (s.base.lpc + 1) s.lretStack _ rfl, rfl, ?_, ?_⟩
    · rfl
    · rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCall
