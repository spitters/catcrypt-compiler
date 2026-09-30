/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage

/-!
# The `CTLeak` leakage model of `Lprog`

`ctLeak w` is the leakage model `LprogLeak.LeakFn` in the event vocabulary
`CT.CTLeak` of `CT/Leakage.lean`:

* a conditional branch `Lcond c l` emits `CTLeak.branch b`, with `b` whether the
  condition operand is non-zero;
* an `Lopn` emits one `CTLeak.addr` event per `lmem` operand: `arr b i` at the
  offset `i` of region `b`, and `arrIdx b x sc` at the offset `sc·x` of region
  `b`, read from the state.

Register-shaped names (general-purpose registers, spill cells `k.N`, memory
cells `mem.<B>.<off>`) are `lvm` entries of the `Lprog` model. A spill cell is
printed at a fixed `%rsp` displacement and a memory cell at a fixed displacement
from its base register, so their addresses are the constant events
`MachineConstantTime.MLeak.mem base off` of the machine model; the model here
records no event for them. A renaming of registers and frame cells therefore
changes no event.

## Main results

* `ctLeak`: the model.
* `reallocLprog_ctLeak`: the register re-allocation preserves constant time from
  function entry in this model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (regOrImm reallocLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
  (ReallocOk reallocLprog_entryCT)

/-- The address event of an `lmem` operand. -/
def opLeak {w : Nat} (s : Lstate w) : LOperand → List CTLeak
  | .arr b i => [.addr b (Int.ofNat i)]
  | .arrIdx b x sc => [.addr b (Int.ofNat (sc * (s.lvm x).toNat))]
  | _ => []

/-- The events of one instruction: the branch outcome of a `Lcond`, the address
    events of the operands of an `Lopn`. -/
def instrLeak {w : Nat} (s : Lstate w) : LinstrR → List CTLeak
  | .Lopn ds _ ss => (ds ++ ss).flatMap (opLeak s)
  | .Lcond c _ => [.branch (evalOperand s c != 0)]
  | _ => []

/-- The `CTLeak` leakage model of `Lprog`. -/
def ctLeak (w : Nat) : LeakFn w CTLeak where
  ev := instrLeak
  length_eq := by
    intro s t i
    cases i with
    | Lopn ds opn ss =>
        simp only [instrLeak, List.length_flatMap]
        exact congrArg List.sum (List.map_congr_left (fun o _ => by cases o <;> rfl))
    | _ => rfl
  cond := by
    intro s t c l h
    simp only [instrLeak, List.cons.injEq, CTLeak.branch.injEq, and_true] at h
    simpa [bne_iff_ne] using congrArg (fun b : Bool => b = true) h
  congr := by
    intro s t i hm hv
    cases i with
    | Lopn ds opn ss =>
        simp only [instrLeak]
        refine List.flatMap_congr (fun o ho => ?_)
        cases o with
        | arrIdx b x sc =>
            have hx : s.lvm x = t.lvm x :=
              hv x (by simp only [readNames, List.mem_flatMap]; exact ⟨_, ho, by simp [opNames]⟩)
            simp [opLeak, hx]
        | _ => rfl
    | Lcond c l =>
        simp only [instrLeak]
        rw [evalOperand_agreeOn hm c (fun x hx => hv x (by simpa [readNames] using hx))]
    | _ => rfl
  frag := by
    intro s d opn ss h
    simp only [instrLeak, List.flatMap_eq_nil_iff, List.mem_append, List.mem_singleton]
    rintro o (rfl | ho)
    · rfl
    · have := List.all_eq_true.1 h o ho
      cases o <;> simp_all [regOrImm, opLeak]

/-- **The register re-allocation preserves constant time from function entry in
    the `CTLeak` model.** -/
theorem reallocLprog_ctLeak {w : Nat} (P : Lprog) (pub : LstateP w → LstateP w → Prop)
    (hok : ∀ fn fd, getFundef P fn = some fd → ReallocOk w fn fd)
    (h : EntryCT (ctLeak w) P pub) : EntryCT (ctLeak w) (reallocLprog P) pub :=
  reallocLprog_entryCT (ctLeak w) P pub hok h

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakCT
