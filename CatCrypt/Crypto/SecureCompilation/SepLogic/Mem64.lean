/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Lift
public import CatCrypt.Crypto.SecureCompilation.SepLogic.Array
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmModel
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64

/-!
# The separation logic over the AArch64 and RV64 machine states

The data memory `MachineMem64.Mem64` of the AArch64 and RV64 models is the byte memory
`MemW 64`: its doubleword read and write are `readLE 8` and `writeLE 8`, and `MemSep` is
disjointness of eight-byte ranges. An array of doublewords `arrAt 8 base xs` gives the
array predicate `MachineMem64.ArrAt`.

The locations of the AArch64 state `BMState` are its `X` registers by name, the flags `C` and
`Z`, the memory bytes and the program counter (`Arm.Loc`); those of the RV64 state `RMState64`
are its registers by name, the memory bytes and the program counter (`Rv.Loc`). A register
location holds the value the register read returns (`BState.get`, `RState64.get`). The
memory points-to assertions `Arm.memPts` and `Rv.memPts` are the lifts of `ptsLE` along the
memory projections.

## Main definitions

* `Arm.Loc`, `Arm.loc`, `Arm.regPts`, `Arm.memPts`: locations and points-to of `BMState`.
* `Rv.Loc`, `Rv.loc`, `Rv.regPts`, `Rv.memPts`: locations and points-to of `RMState64`.

## Main results

* `readLE_eight_eq_read64`, `writeLE_eight_eq_write64`: the doubleword access of
  `MachineMem64` is the eight-byte little-endian access.
* `memSep_iff_disj`: `MemSep` is disjointness of eight-byte ranges.
* `arrAt_holds_arrAt`: an array of doublewords satisfies `MachineMem64.ArrAt`.
* `Arm.triple_setMem64`, `Rv.triple_setMem64`: a doubleword store turns `a ↦ x` into
  `a ↦ v`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic

open SAssert

/-! ## Doubleword access -/

/-- The doubleword read of `MachineMem64` is the eight-byte little-endian read. -/
theorem readLE_eight_eq_read64 (m : MachineMem64.Mem64) (a : BitVec 64) :
    readLE 8 m a = MachineMem64.read64 m a := by
  simp only [readLE, MachineMem64.read64, BitVec.add_assoc]
  norm_num
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  simp

/-- The doubleword write of `MachineMem64` is the eight-byte little-endian write. -/
theorem writeLE_eight_eq_write64 (m : MachineMem64.Mem64) (a v : BitVec 64) :
    writeLE 8 m a v = MachineMem64.write64 m a v := by
  funext x
  obtain ⟨d, rfl⟩ : ∃ d, x = a + d := ⟨x - a, by abel⟩
  simp only [writeLE, MachineMem64.write64, Function.update_apply, BitVec.add_assoc]
  norm_num
  by_cases hd : d.toNat < 8
  · have h8 : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by bv_omega
    rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;>
      (ext i hi
       simp only [BitVec.getElem_extractLsb', BitVec.getElem_setWidth,
         BitVec.getLsbD_extractLsb']
       try simp (disch := omega) only [decide_eq_true, Bool.true_and]
       try (congr 1; omega))
  · have hne : ∀ k : BitVec 64, k.toNat < 8 → ¬ d = k := fun k hk h => hd (h ▸ hk)
    simp only [hne 7 (by decide), hne 6 (by decide), hne 5 (by decide), hne 4 (by decide),
      hne 3 (by decide), hne 2 (by decide), hne 1 (by decide), hne 0 (by decide), ite_eq_right hd,
      ite_false]

/-- `MemSep` is disjointness of eight-byte ranges. -/
theorem memSep_iff_disj {a b : BitVec 64} :
    MachineMem64.MemSep a b ↔ (⟨a, 8⟩ : Rng 64).Disj ⟨b, 8⟩ := Iff.rfl

/-- An array of doublewords satisfies the array predicate of `MachineMem64`. -/
theorem arrAt_holds_arrAt {base : BitVec 64} {xs : List (BitVec (8 * 8))}
    {m : MachineMem64.Mem64} (h : (arrAt 8 base xs).holds m) :
    MachineMem64.ArrAt m base xs.length fun k => xs[k] := by
  intro k
  have hk := (holds_bigSep.1 h).2 _ (List.mem_mapIdx.2 ⟨k.val, k.isLt, rfl⟩)
  rw [holds_ptsLE, readLE_eight_eq_read64] at hk
  exact hk

/-! ## AArch64 -/

namespace Arm

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-- A location of `BMState`: an `X` register by name, a flag, a memory byte, or the program
    counter. -/
inductive Loc
  | reg (r : String)
  | cf
  | zf
  | mem (a : BitVec 64)
  | pc
  deriving DecidableEq

/-- The type of the value held at a location. -/
abbrev Loc.Val : Loc → Type
  | .reg _ => BitVec 64
  | .cf => Bool
  | .zf => Bool
  | .mem _ => BitVec 8
  | .pc => BitVec 64

/-- The value of a location: a register location holds the value `BState.get` reads. -/
def loc (s : BMState) : (l : Loc) → l.Val
  | .reg r => s.regs.get r
  | .cf => s.regs.cf
  | .zf => s.zf
  | .mem a => s.mem a
  | .pc => s.pc

instance : Footprinted BMState Loc := Footprinted.ofGet loc

/-- The register `r` reads `v`. -/
def regPts (r : String) (v : BitVec 64) : SAssert BMState Loc where
  fp := {.reg r}
  holds s := s.regs.get r = v
  supp s t h hs := (show s.regs.get r = t.regs.get r from h (.reg r) rfl).symm.trans hs

theorem projCompat_mem : ProjCompat BMState.mem Loc.mem :=
  fun _ _ _ h a ha => h (.mem a) ⟨a, ha, rfl⟩

theorem loc_mem_injective : Function.Injective Loc.mem := fun _ _ h => Loc.mem.inj h

/-- The `n` memory bytes at `a` hold `v` little-endian. -/
def memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n)) : SAssert BMState Loc :=
  (ptsLE n a v).comap BMState.mem Loc.mem projCompat_mem

/-- The state after storing the doubleword `v` at `a`. -/
def setMem64 (a v : BitVec 64) (s : BMState) : BMState :=
  { s with mem := MachineMem64.write64 s.mem a v }

/-- A doubleword store writes in the memory bytes of its range. -/
theorem writesIn_setMem64 (a v : BitVec 64) :
    WritesIn (setMem64 a v) (fun _ => Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet) := by
  rintro s (_ | _ | _ | x | _) hx
  · rfl
  · rfl
  · rfl
  · show s.mem x = MachineMem64.write64 s.mem a v x
    rw [← writeLE_eight_eq_write64]
    exact (writeLE_outside 8 s.mem a v fun h => hx ⟨x, h, rfl⟩).symm
  · rfl

/-- A doubleword store turns `a ↦ x` into `a ↦ v`. -/
theorem triple_setMem64 (a x v : BitVec 64) :
    Triple (memPts 8 a x) (setMem64 a v) (memPts 8 a v) :=
  Triple.comap (g := fun m => writeLE 8 m a v)
    (fun s => (writeLE_eight_eq_write64 s.mem a v).symm) (triple_writeLE 8 a x v (by decide))

/-- A store to the first cell of a two-cell array preserves the second cell and a
    register. -/
example (a x y v w : BitVec 64) (r : String) :
    Triple (memPts 8 a x ∗ (memPts 8 (a + 8) y ∗ regPts r w)) (setMem64 a v)
      (memPts 8 a v ∗ (memPts 8 (a + 8) y ∗ regPts r w)) :=
  Triple.frame _ (triple_setMem64 a x v) (writesIn_setMem64 a v) (fun _ _ => subset_rfl)
    subset_rfl

/-- Separated doubleword points-to assertions satisfy `MemSep`. -/
theorem memPts_memSep {a b v w : BitVec 64} {s : BMState}
    (h : (memPts 8 a v ∗ memPts 8 b w).holds s) : MachineMem64.MemSep a b :=
  Rng.disj_of_disjoint (Nat.succ_pos 7) (Nat.succ_pos 7)
    ((Set.disjoint_image_iff loc_mem_injective).1 h.1)

end Arm

/-! ## RV64 -/

namespace Rv

open CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-- A location of `RMState64`: a register by name, a memory byte, or the program counter. -/
inductive Loc
  | reg (r : String)
  | mem (a : BitVec 64)
  | pc
  deriving DecidableEq

/-- The type of the value held at a location. -/
abbrev Loc.Val : Loc → Type
  | .reg _ => BitVec 64
  | .mem _ => BitVec 8
  | .pc => BitVec 64

/-- The value of a location: a register location holds the value `RState64.get` reads. -/
def loc (s : RMState64) : (l : Loc) → l.Val
  | .reg r => s.regs.get r
  | .mem a => s.mem a
  | .pc => s.pc

instance : Footprinted RMState64 Loc := Footprinted.ofGet loc

/-- The register `r` reads `v`. -/
def regPts (r : String) (v : BitVec 64) : SAssert RMState64 Loc where
  fp := {.reg r}
  holds s := s.regs.get r = v
  supp s t h hs := (show s.regs.get r = t.regs.get r from h (.reg r) rfl).symm.trans hs

theorem projCompat_mem : ProjCompat RMState64.mem Loc.mem :=
  fun _ _ _ h a ha => h (.mem a) ⟨a, ha, rfl⟩

/-- The `n` memory bytes at `a` hold `v` little-endian. -/
def memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n)) : SAssert RMState64 Loc :=
  (ptsLE n a v).comap RMState64.mem Loc.mem projCompat_mem

/-- The state after storing the doubleword `v` at `a`. -/
def setMem64 (a v : BitVec 64) (s : RMState64) : RMState64 :=
  { s with mem := MachineMem64.write64 s.mem a v }

/-- A doubleword store writes in the memory bytes of its range. -/
theorem writesIn_setMem64 (a v : BitVec 64) :
    WritesIn (setMem64 a v) (fun _ => Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet) := by
  rintro s (_ | x | _) hx
  · rfl
  · show s.mem x = MachineMem64.write64 s.mem a v x
    rw [← writeLE_eight_eq_write64]
    exact (writeLE_outside 8 s.mem a v fun h => hx ⟨x, h, rfl⟩).symm
  · rfl

/-- A doubleword store turns `a ↦ x` into `a ↦ v`. -/
theorem triple_setMem64 (a x v : BitVec 64) :
    Triple (memPts 8 a x) (setMem64 a v) (memPts 8 a v) :=
  Triple.comap (g := fun m => writeLE 8 m a v)
    (fun s => (writeLE_eight_eq_write64 s.mem a v).symm) (triple_writeLE 8 a x v (by decide))

/-- A store preserves a separated register. -/
example (a x v w : BitVec 64) (r : String) :
    Triple (memPts 8 a x ∗ regPts r w) (setMem64 a v) (memPts 8 a v ∗ regPts r w) :=
  Triple.frame _ (triple_setMem64 a x v) (writesIn_setMem64 a v) (fun _ _ => subset_rfl)
    subset_rfl

end Rv

end CatCrypt.Crypto.SecureCompilation.SepLogic
