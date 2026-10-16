/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.Mem64
public import CatCrypt.Crypto.SecureCompilation.Ascent.Rng
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemWord

/-!
# The separation logic over the x86 address-memory machine

The locations of the state `Ascent.AddrMem.AState` are its registers by name, its five flags
and its memory bytes (`X86.Loc`). Two states agree on a set of locations when they hold equal
values there (`Footprinted.ofGet X86.loc`). The points-to assertions are `X86.regPts` for a
register, `X86.flagPts` for a flag, and `X86.memPts n a v`, the lift of the byte-memory
assertion `ptsLE n a v` along the projection `AState.mem`.

The eight-byte read and write of `AddrMem` are `readLE 8` and `writeLE 8`. The byte range
`Rng 64` of the separation logic is the range `Ascent.Footprint.Rng`, with the same
disjointness, and `AddrMem.Disjoint8` is disjointness of eight-byte ranges.

## Main definitions

* `X86.Flag`, `X86.Loc`, `X86.loc`: the locations of `AState` and their values.
* `X86.regPts`, `X86.flagPts`, `X86.memPts`: points-to assertions.
* `X86.setMem64`: the state after an eight-byte store.
* `X86.rngEquiv`: the byte ranges of the two libraries.

## Main results

* `X86.readLE_eight_eq_addrMem_read64`, `X86.writeLE_eight_eq_addrMem_write64`: the word
  access of `AddrMem`
  is the eight-byte little-endian access.
* `X86.rngEquiv_disj_iff`, `X86.disjoint8_iff_disj`: `Footprint.Rng.Disj` and `Disjoint8` as
  `Rng.Disj`.
* `X86.memPts_disj`: separated eight-byte points-to assertions satisfy `Disjoint8`.
* `X86.writesIn_setMem64`, `X86.triple_setMem64`: an eight-byte store writes in its range
  and establishes its points-to assertion; with `Triple.frame` it preserves every separated
  register, flag and memory assertion.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.X86

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open SAssert

/-- The five flags of `RFlags`. -/
inductive Flag
  | cf
  | pf
  | zf
  | sf
  | of
  deriving DecidableEq

/-- The value of a flag. -/
def Flag.get (fl : RFlags) : Flag → JFlag
  | .cf => fl.cf
  | .pf => fl.pf
  | .zf => fl.zf
  | .sf => fl.sf
  | .of => fl.of

/-- A location of `AState`: a register by name, a flag, or a memory byte. -/
inductive Loc
  | reg (r : String)
  | flag (f : Flag)
  | mem (a : BitVec 64)
  deriving DecidableEq

/-- The type of the value held at a location. -/
abbrev Loc.Val : Loc → Type
  | .reg _ => BitVec 64
  | .flag _ => JFlag
  | .mem _ => BitVec 8

/-- The value of a location in a state. -/
def loc (s : AState) : (l : Loc) → l.Val
  | .reg r => s.regs r
  | .flag f => f.get s.flags
  | .mem a => s.mem a

instance : Footprinted AState Loc := Footprinted.ofGet loc

theorem agreeOn_iff {S : Set Loc} {s t : AState} :
    Footprinted.AgreeOn S s t ↔ ∀ l ∈ S, loc s l = loc t l := Iff.rfl

/-- The register `r` holds `v`. -/
def regPts (r : String) (v : BitVec 64) : SAssert AState Loc where
  fp := {.reg r}
  holds s := s.regs r = v
  supp s t h hs := (show s.regs r = t.regs r from h (.reg r) rfl).symm.trans hs

/-- The flag `f` holds `b`. -/
def flagPts (f : Flag) (b : JFlag) : SAssert AState Loc where
  fp := {.flag f}
  holds s := f.get s.flags = b
  supp s t h hs :=
    (show f.get s.flags = f.get t.flags from h (.flag f) rfl).symm.trans hs

/-- The memory projection and the memory locations are compatible. -/
theorem projCompat_mem : ProjCompat AState.mem Loc.mem :=
  fun _ _ _ h a ha => h (.mem a) ⟨a, ha, rfl⟩

theorem loc_mem_injective : Function.Injective Loc.mem := fun _ _ h => Loc.mem.inj h

/-- The `n` memory bytes at `a` hold `v` little-endian. -/
def memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n)) : SAssert AState Loc :=
  (ptsLE n a v).comap AState.mem Loc.mem projCompat_mem

@[simp] theorem holds_regPts (r : String) (v : BitVec 64) (s : AState) :
    (regPts r v).holds s ↔ s.regs r = v := Iff.rfl

@[simp] theorem holds_flagPts (f : Flag) (b : JFlag) (s : AState) :
    (flagPts f b).holds s ↔ f.get s.flags = b := Iff.rfl

@[simp] theorem holds_memPts (n : Nat) (a : BitVec 64) (v : BitVec (8 * n)) (s : AState) :
    (memPts n a v).holds s ↔ readLE n s.mem a = v := Iff.rfl

/-! ## The word access of `AddrMem` -/

/-- The word read of `AddrMem` is the eight-byte little-endian read. -/
theorem readLE_eight_eq_addrMem_read64 (m : AMem) (a : BitVec 64) :
    readLE 8 m a = read64 m a :=
  (readLE_eight_eq_read64 m a).trans (Ascent.Footprint.read64_eq m a).symm

/-- The word store of `AddrMem` is the eight-byte little-endian write. -/
theorem writeLE_eight_eq_addrMem_write64 (m : AMem) (a v : BitVec 64) :
    writeLE 8 m a v = write64 m a v :=
  (writeLE_eight_eq_write64 m a v).trans (Ascent.Footprint.write64_eq m a v).symm

/-! ## Byte ranges -/

/-- The byte ranges of the separation logic at `A = 64` are the ranges of
    `Ascent.Footprint`. -/
def rngEquiv : Rng 64 ≃ Ascent.Footprint.Rng where
  toFun r := ⟨r.base, r.len⟩
  invFun r := ⟨r.base, r.len⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mem_rngEquiv_iff {r : Rng 64} {x : BitVec 64} : x ∈ rngEquiv r ↔ x ∈ r := Iff.rfl

/-- Disjointness of `Footprint.Rng` is disjointness of `Rng 64`. -/
theorem rngEquiv_disj_iff {r s : Rng 64} : (rngEquiv r).Disj (rngEquiv s) ↔ r.Disj s :=
  Iff.rfl

/-- `Disjoint8` is disjointness of eight-byte ranges. -/
theorem disjoint8_iff_disj {a b : BitVec 64} :
    Disjoint8 a b ↔ (⟨a, 8⟩ : Rng 64).Disj ⟨b, 8⟩ := Iff.rfl

/-- Separated eight-byte points-to assertions address disjoint words. -/
theorem memPts_disj {a b v w : BitVec 64} {s : AState}
    (h : (memPts 8 a v ∗ memPts 8 b w).holds s) : Disjoint8 a b :=
  Rng.disj_of_disjoint (Nat.succ_pos 7) (Nat.succ_pos 7)
    ((Set.disjoint_image_iff loc_mem_injective).1 h.1)

/-! ## The eight-byte store -/

/-- The state after storing `v` at the eight bytes from `a`. -/
def setMem64 (a v : BitVec 64) (s : AState) : AState := { s with mem := write64 s.mem a v }

/-- The eight-byte store writes in the memory bytes of its range. -/
theorem writesIn_setMem64 (a v : BitVec 64) :
    WritesIn (setMem64 a v) (fun _ => Loc.mem '' (⟨a, 8⟩ : Rng 64).toSet) := by
  rintro s (_ | _ | x) hx
  · rfl
  · rfl
  · exact (write64_of_not_inRange _ _ _ _ fun h => hx ⟨x, h, rfl⟩).symm

/-- The eight-byte store turns `a ↦ x` into `a ↦ v`. -/
theorem triple_setMem64 (a x v : BitVec 64) :
    Triple (memPts 8 a x) (setMem64 a v) (memPts 8 a v) :=
  Triple.comap (g := fun m => writeLE 8 m a v)
    (fun s => (writeLE_eight_eq_addrMem_write64 s.mem a v).symm) (triple_writeLE 8 a x v (by decide))

/-- The store at `a` preserves a separated register and a separated word. -/
example (a b x v w u : BitVec 64) (r : String) :
    Triple (memPts 8 a x ∗ (regPts r u ∗ memPts 8 b w)) (setMem64 a v)
      (memPts 8 a v ∗ (regPts r u ∗ memPts 8 b w)) :=
  Triple.frame _ (triple_setMem64 a x v) (writesIn_setMem64 a v) (fun _ _ => subset_rfl)
    subset_rfl

example (a b x y : BitVec 64) (f : Flag) (c : JFlag) :
    flagPts f c ∗ memPts 8 a x ∗ memPts 8 b y ⊢ₛ memPts 8 b y ∗ flagPts f c := by
  sep_cancel

end CatCrypt.Crypto.SecureCompilation.SepLogic.X86
