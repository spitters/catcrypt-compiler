/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem
public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

/-!
# The vector load on the byte memory of the vector machine

`vecLoad w a i` (`VIR/X86VecMem.lean`) is the value of the operation `vload`: the 512-bit
register whose lane `j` is the element of the array `a` at `i + j`. `readBytes 64 mem p`
(`X86Backend/VecMach.lean`) is the value a 512-bit `VInstr.ld` reads at the address `p`.

Under the layout hypothesis that element `k` of the array occupies the `w / 8` bytes of `mem`
from `base + (w / 8) * k`, little-endian, and for an index with `i + 512 / w ≤ N`, the two
values are equal at the address `base + (w / 8) * i`.

## Main results

* `readBytes_vecLoad_qword`: the 64 bytes at `base + 8 * i` are `vecLoad 64 a i`, for
  `i + 8 ≤ N`.
* `readBytes_vecLoad_dword`: the 64 bytes at `base + 4 * i` are `vecLoad 32 a i`, for
  `i + 16 ≤ N`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecMemExec

open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (readBytes getLsbD_readBytes)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackGet_id)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (ofLanes getLsbD_ofLanes)
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecMem (vecLoad)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AMem)

/-- **A vector load of 64-bit lanes reads the bytes of the array.** When element `k` of the
    array `a` occupies the 8 bytes of `mem` from `base + 8 * k`, little-endian, and
    `i + 8 ≤ N`, the 64 bytes of `mem` from `base + 8 * i` are the register `vecLoad 64 a i`. -/
theorem readBytes_vecLoad_qword {N : Nat} (mem : AMem) (base : BitVec 64)
    (a : Fin N → BitVec 64) (i : Nat)
    (hlay : ∀ (k : Fin N) (b : Nat), b < 8 →
      mem (base + BitVec.ofNat 64 (8 * k.val + b)) = (a k).extractLsb' (8 * b) 8)
    (hi : i + 8 ≤ N) :
    readBytes 64 mem (base + BitVec.ofNat 64 (8 * i)) = vecLoad 64 a i := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  unfold vecLoad
  rw [getLsbD_readBytes, getLsbD_ofLanes]
  have hk : i + p / 64 < N := by omega
  have hget : stackGet a (i + p / 64) = a ⟨i + p / 64, hk⟩ := stackGet_id a ⟨_, hk⟩
  have haddr : base + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 (p / 8) =
      base + BitVec.ofNat 64 (8 * (i + p / 64) + (p % 64) / 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [haddr, hlay ⟨_, hk⟩ ((p % 64) / 8) (by omega), hget, BitVec.getLsbD_extractLsb']
  have h8 : p % 8 < 8 := Nat.mod_lt _ (by omega)
  have he : 8 * (p % 64 / 8) + p % 8 = p % 64 := by omega
  simp [hp, h8, he, show p / 8 < 64 by omega]

/-- **A vector load of 32-bit lanes reads the bytes of the array.** When element `k` of the
    array `a` occupies the 4 bytes of `mem` from `base + 4 * k`, little-endian, and
    `i + 16 ≤ N`, the 64 bytes of `mem` from `base + 4 * i` are the register
    `vecLoad 32 a i`. -/
theorem readBytes_vecLoad_dword {N : Nat} (mem : AMem) (base : BitVec 64)
    (a : Fin N → BitVec 32) (i : Nat)
    (hlay : ∀ (k : Fin N) (b : Nat), b < 4 →
      mem (base + BitVec.ofNat 64 (4 * k.val + b)) = (a k).extractLsb' (8 * b) 8)
    (hi : i + 16 ≤ N) :
    readBytes 64 mem (base + BitVec.ofNat 64 (4 * i)) = vecLoad 32 a i := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  unfold vecLoad
  rw [getLsbD_readBytes, getLsbD_ofLanes]
  have hk : i + p / 32 < N := by omega
  have hget : stackGet a (i + p / 32) = a ⟨i + p / 32, hk⟩ := stackGet_id a ⟨_, hk⟩
  have haddr : base + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 (p / 8) =
      base + BitVec.ofNat 64 (4 * (i + p / 32) + (p % 32) / 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [haddr, hlay ⟨_, hk⟩ ((p % 32) / 8) (by omega), hget, BitVec.getLsbD_extractLsb']
  have h8 : p % 8 < 8 := Nat.mod_lt _ (by omega)
  have he : 8 * (p % 32 / 8) + p % 8 = p % 32 := by omega
  simp [hp, h8, he, show p / 8 < 64 by omega]

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecMemExec
