/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import CatCrypt.Crypto.SecureCompilation.MachineMem64

/-!
# The word access of `AddrMem` and of `MachineMem64`

The x86 byte memory `AddrMem.AMem` and the ARM/RISC-V byte memory `MachineMem64.Mem64` are
the same type, and their little-endian 64-bit reads and writes agree. The two lemmas sit in
a module with no further imports, so both the footprint calculus (`Ascent/Footprint.lean`)
and the separation logic (`SepLogic/X86State.lean`) use them.

## Main results

* `read64_eq`: `AddrMem.read64 = MachineMem64.read64`.
* `write64_eq`: `AddrMem.write64 = MachineMem64.write64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

theorem or_shift8 (a b : Nat) (h : b < 2 ^ 8) : a <<< 8 ||| b = a * 2 ^ 8 + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]

/-- The little-endian word of `AddrMem` is the doubleword of `MachineMem64`. -/
theorem read64_eq (m : AMem) (a : BitVec 64) : read64 m a = MachineMem64.read64 m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [read64, MachineMem64.read64, BitVec.toNat_cast, BitVec.toNat_append,
    BitVec.toNat_ofNat, or_shift8 _ _ (BitVec.isLt _)]
  have h0 := (m a).isLt
  have h1 := (m (a + 1)).isLt
  have h2 := (m (a + 2)).isLt
  have h3 := (m (a + 3)).isLt
  have h4 := (m (a + 4)).isLt
  have h5 := (m (a + 5)).isLt
  have h6 := (m (a + 6)).isLt
  have h7 := (m (a + 7)).isLt
  simp only [BitVec.ofNat_eq_ofNat] at *
  omega

/-- The little-endian store of `AddrMem` is the store of `MachineMem64`. -/
theorem write64_eq (m : AMem) (a v : BitVec 64) :
    write64 m a v = MachineMem64.write64 m a v := by
  funext x
  by_cases h : (x - a).toNat < 8
  · have h' : InRange8 a x := h
    simp only [write64, MachineMem64.write64, ite_eq_left h, ite_eq_left h']
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  · rw [write64_of_not_inRange _ _ _ _ h]
    simp only [MachineMem64.write64, ite_eq_right h]

end CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
