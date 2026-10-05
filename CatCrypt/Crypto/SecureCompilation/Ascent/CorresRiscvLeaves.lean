/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscv
public import Lean

/-!
# The RV64 value leaves of the ascent

`CorresR` (`CorresRiscv`) is the ascent correspondence over `runRBlock64`. This
module supplies its abstract state, its state relation, and one value leaf per
`RInst64` constructor, the RV64 counterparts of `SRcarry` and the
`corresJ_sbb`/`corresJ_adc`/`corresJ_mulx` leaves in `RunBlockCorres`.

* `AStateR` is a register map at the word level, `String → BitVec 64`. RV64 has no
  flag register, so the abstract state has no carry component: a borrow or carry
  is an ordinary word written by `sltu`.
* `SRr` relates a machine state to an abstract state by agreement of every
  register read, through `RState64.get`, so the hard-wired zero register reads
  `0` on both sides.
* `writeR` is the abstract register write. It discards a write to `zero`/`x0`,
  as `RState64.set` does, so every leaf holds with the trivial precondition and
  no side condition on the destination name.
* `addStepR` … `slliStepR` are the abstract single-instruction transitions, each
  a `writeR` of the word the instruction computes, and `corresR_add` …
  `corresR_slli` are the leaves. All twelve are instances of `corresR_of_set`,
  which states the leaf once for any instruction whose semantics is a single
  register write.

The `@[corresR]` label attribute registered here collects the leaves for
`corres_solve_rv` (`CorresRiscvSolver`); the registry itself is populated there,
since a label attribute is usable only in modules that import the registering one.

## Main results

* `corresR_of_set`: the leaf for any instruction whose semantics is one register
  write.
* `corresR_add`, `corresR_sub`, `corresR_sltu`, `corresR_and`, `corresR_or`,
  `corresR_xor`, `corresR_mul`, `corresR_mulhu`, `corresR_li`, `corresR_mv`,
  `corresR_srli`, `corresR_slli`: one leaf per `RInst64` constructor.
-/

@[expose] public section

set_option autoImplicit false

/-- Per-instruction `CorresR` ascent leaves, composed by `corres_solve_rv`. -/
register_label_attr corresR

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## The abstract state and the state relation -/

/-- The abstract RV64 state: a register map at the word level. -/
abbrev AStateR : Type := String → X64R

/-- The abstract register write. A write to the zero register `zero`/`x0` is
    discarded, matching `RState64.set`. -/
def writeR (d : String) (v : X64R) (st : AStateR) : AStateR :=
  if d = "zero" ∨ d = "x0" then st else fun r => if r = d then v else st r

/-- `SRr`: machine and abstract states agree on every register read. Reads go
    through `RState64.get`, so `zero`/`x0` read `0` on the machine side and the
    relation forces `0` on the abstract side. -/
def SRr (s : RState64) (a : AStateR) : Prop :=
  ∀ r, s.get r = a r

/-- A machine write, read back through `get`, is the abstract write applied to
    the machine's read map. -/
theorem get_set_eq_writeR (s : RState64) (d : String) (v : X64R) (r : String) :
    (s.set d v).get r = writeR d v s.get r := by
  by_cases hd : d = "zero" ∨ d = "x0"
  · simp [RState64.set, writeR, hd]
  · by_cases hr : r = d
    · subst hr
      rw [RState64.get_set_same _ _ _ hd]
      simp [writeR, hd]
    · rw [RState64.get_set_other _ _ _ _ hr]
      simp [writeR, hd, hr]

/-- The leaf for any instruction whose semantics is one register write
    `s.set d (g s)`: it refines the abstract write `writeR d (f st)` whenever the
    written word agrees across `SRr`. -/
theorem corresR_of_set (i : RInst64) (d : String) (g : RState64 → X64R)
    (f : AStateR → X64R) (hi : ∀ s, evalRInst64 s i = s.set d (g s))
    (hfg : ∀ s a, SRr s a → g s = f a) :
    CorresR SRr (fun _ => True) (fun st => writeR d (f st) st) [i] := by
  intro s a hSR _ r
  rw [runRBlock64_cons, runRBlock64_nil, hi, get_set_eq_writeR, hfg s a hSR, funext hSR]

/-! ## The abstract single-instruction transitions -/

/-- `add d a b`: `d := a + b`, wrapping. -/
def addStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a + st b) st

/-- `sub d a b`: `d := a - b`, wrapping. -/
def subStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a - st b) st

/-- `sltu d a b`: `d := 1` if `a <ᵘ b`, else `0` — the borrow word of `a - b`. -/
def sltuStepR (d a b : String) (st : AStateR) : AStateR :=
  writeR d (if st a < st b then 1 else 0) st

/-- `and d a b`: `d := a &&& b`. -/
def andStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a &&& st b) st

/-- `or d a b`: `d := a ||| b`. -/
def orStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a ||| st b) st

/-- `xor d a b`: `d := a ^^^ b`. -/
def xorStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a ^^^ st b) st

/-- `mul d a b`: `d :=` the low 64 bits of the product. -/
def mulStepR (d a b : String) (st : AStateR) : AStateR := writeR d (st a * st b) st

/-- `mulhu d a b`: `d :=` the high 64 bits of the unsigned 128-bit product. -/
def mulhuStepR (d a b : String) (st : AStateR) : AStateR :=
  writeR d (BitVec.ofNat 64 (((st a).toNat * (st b).toNat) >>> 64)) st

/-- `li d imm`: `d := imm`. -/
def liStepR (d : String) (imm : Nat) (st : AStateR) : AStateR :=
  writeR d (BitVec.ofNat 64 imm) st

/-- `mv d a`: `d := a`. -/
def mvStepR (d a : String) (st : AStateR) : AStateR := writeR d (st a) st

/-- `srli d a sh`: `d := a >>> sh`, the logical right shift by an immediate. -/
def srliStepR (d a : String) (sh : Nat) (st : AStateR) : AStateR :=
  writeR d (st a >>> sh) st

/-- `slli d a sh`: `d := a <<< sh`, the logical left shift by an immediate. -/
def slliStepR (d a : String) (sh : Nat) (st : AStateR) : AStateR :=
  writeR d (st a <<< sh) st

/-! ## The leaves, one per `RInst64` constructor -/

/-- `add` refines `addStepR`. -/
theorem corresR_add (d a b : String) :
    CorresR SRr (fun _ => True) (addStepR d a b) [.add d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opAdd64, h a, h b])

/-- `sub` refines `subStepR`. -/
theorem corresR_sub (d a b : String) :
    CorresR SRr (fun _ => True) (subStepR d a b) [.sub d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opSub64, h a, h b])

/-- `sltu` refines `sltuStepR`. -/
theorem corresR_sltu (d a b : String) :
    CorresR SRr (fun _ => True) (sltuStepR d a b) [.sltu d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl)
    (fun _ _ h => by simp only [opSltu, h a, h b, BitVec.lt_def])

/-- `and` refines `andStepR`. -/
theorem corresR_and (d a b : String) :
    CorresR SRr (fun _ => True) (andStepR d a b) [.and d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opAnd64, h a, h b])

/-- `or` refines `orStepR`. -/
theorem corresR_or (d a b : String) :
    CorresR SRr (fun _ => True) (orStepR d a b) [.or d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opOr64, h a, h b])

/-- `xor` refines `xorStepR`. -/
theorem corresR_xor (d a b : String) :
    CorresR SRr (fun _ => True) (xorStepR d a b) [.xor d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opXor64, h a, h b])

/-- `mul` refines `mulStepR`. -/
theorem corresR_mul (d a b : String) :
    CorresR SRr (fun _ => True) (mulStepR d a b) [.mul d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opMul64, h a, h b])

/-- `mulhu` refines `mulhuStepR`. -/
theorem corresR_mulhu (d a b : String) :
    CorresR SRr (fun _ => True) (mulhuStepR d a b) [.mulhu d a b] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by simp only [opMulhu, h a, h b])

/-- `li` refines `liStepR`. -/
theorem corresR_li (d : String) (imm : Nat) :
    CorresR SRr (fun _ => True) (liStepR d imm) [.li d imm] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ _ => rfl)

/-- `mv` refines `mvStepR`. -/
theorem corresR_mv (d a : String) :
    CorresR SRr (fun _ => True) (mvStepR d a) [.mv d a] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => h a)

/-- `srli` refines `srliStepR`. -/
theorem corresR_srli (d a : String) (sh : Fin 64) :
    CorresR SRr (fun _ => True) (srliStepR d a sh) [.srli d a sh] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by rw [h a])

/-- `slli` refines `slliStepR`. -/
theorem corresR_slli (d a : String) (sh : Fin 64) :
    CorresR SRr (fun _ => True) (slliStepR d a sh) [.slli d a sh] :=
  corresR_of_set _ d _ _ (fun _ => rfl) (fun _ _ h => by rw [h a])

end CatCrypt.Crypto.SecureCompilation.Ascent
