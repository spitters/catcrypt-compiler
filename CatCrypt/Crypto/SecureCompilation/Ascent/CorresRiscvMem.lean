/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvLeaves
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64

/-!
# The ascent correspondence at the RV64 machine with memory

`CorresR` states the correspondence over `runRBlock64`, whose state is a register file.
`CorresRM` states it over `RiscvMem64.runX`, whose state adds a byte memory, so a block
may load and store doublewords. The abstract state of `SRrm` is a register valuation and
a byte memory; a load reads `Memory64.read64` at the computed address and a store writes
`Memory64.write64`.

## Main definitions

* `CorresRM`: the correspondence over `runX`.
* `SRrm`: the machine registers read as the valuation and the memory is the abstract one.

## Main results

* `corresRM_nil`, `corresRM_append`, `corresRM_weaken`: the structural rules.
* `corresRM_eq_corresM`: `CorresRM` is `CorresM` at the step of `runX`.
* `corresRM_ld`, `corresRM_sd`: the load and store leaves.
* `corresRM_lift`: a `CorresR` over a register block carries over, memory unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64 write64)

/-- From a machine state related by `SR` to an abstract state satisfying `P`, running the
    block lands in a state related to the abstract result. -/
def CorresRM {AState : Type} (SR : MState64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : List XInst64) : Prop :=
  ∀ s a, SR s a → P a → SR (runX s c) (fa a)

section Structural

variable {AState : Type} (SR : MState64 → AState → Prop)

theorem corresRM_nil : CorresRM SR (fun _ => True) id [] := fun _ _ h _ => h

theorem corresRM_append {P Q : AState → Prop} {fa ga : AState → AState}
    {xs ys : List XInst64} (hx : CorresRM SR P fa xs) (hy : CorresRM SR Q ga ys)
    (hPQ : ∀ a, P a → Q (fa a)) :
    CorresRM SR P (ga ∘ fa) (xs ++ ys) := by
  intro s a hSR hP
  rw [runX_append]
  exact hy _ (fa a) (hx s a hSR hP) (hPQ a hP)

theorem corresRM_weaken {P P' : AState → Prop} {fa : AState → AState}
    {c : List XInst64} (h : CorresRM SR P fa c) (hP : ∀ a, P' a → P a) :
    CorresRM SR P' fa c :=
  fun s a hSR hP' => h s a hSR (hP a hP')

/-- `runX` as a never-failing step. -/
def runXStep (c : List XInst64) (s : MState64) : Option MState64 := some (runX s c)

theorem corresRM_eq_corresM (P : AState → Prop) (fa : AState → AState) (c : List XInst64) :
    CorresRM SR P fa c ↔ CorresM runXStep SR P fa c := by
  constructor
  · intro h s a hSR hP
    exact ⟨runX s c, rfl, h s a hSR hP⟩
  · intro h s a hSR hP
    obtain ⟨s', hstep, hSR'⟩ := h s a hSR hP
    rw [runXStep, Option.some.injEq] at hstep
    exact hstep ▸ hSR'

end Structural

/-- The registers read as the valuation `a.1` and the memory is `a.2`. -/
def SRrm (s : MState64) (a : AStateR × AMem) : Prop := SRr s.regs a.1 ∧ s.mem = a.2

/-- **The load leaf.** `ld d, off(b)` writes the doubleword at `b + signExtend off`. -/
theorem corresRM_ld (d b : String) (off : BitVec 12) :
    CorresRM SRrm (fun _ => True)
      (fun a => (writeR d (read64 a.2 (a.1 b + off.signExtend 64)) a.1, a.2))
      [.ld d b off] := by
  intro s a ⟨hr, hm⟩ _
  refine ⟨fun r => ?_, hm⟩
  simp only [runX_cons, runX_nil, evalX, addr]
  rw [get_set_eq_writeR, hr b, hm]
  congr 1
  funext r'
  exact hr r'

/-- **The store leaf.** `sd v, off(b)` writes `v` to the eight bytes at
    `b + signExtend off`. -/
theorem corresRM_sd (v b : String) (off : BitVec 12) :
    CorresRM SRrm (fun _ => True)
      (fun a => (a.1, write64 a.2 (a.1 b + off.signExtend 64) (a.1 v)))
      [.sd v b off] := by
  intro s a ⟨hr, hm⟩ _
  refine ⟨hr, ?_⟩
  simp only [runX_cons, runX_nil, evalX, addr]
  rw [hr b, hr v, hm]

theorem runM64_map_base (s : RState64) (c : List RInst64) :
    runM64 s (c.map .base) = runRBlock64 s c := by
  induction c generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

/-- **A register block carries over.** A `CorresR` over `SRr` holds over `SRrm` for the
    same block, with the memory unchanged. -/
theorem corresRM_lift {P : AStateR → Prop} {f : AStateR → AStateR} {c : List RInst64}
    (h : CorresR SRr P f c) :
    CorresRM SRrm (fun a => P a.1) (fun a => (f a.1, a.2)) ((c.map .base).map .m) := by
  intro s a ⟨hr, hm⟩ hP
  rw [runX_lift]
  exact ⟨by rw [runM64_map_base]; exact h _ _ hr hP, hm⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
