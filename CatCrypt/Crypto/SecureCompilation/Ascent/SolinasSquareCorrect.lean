/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresX86Mem
public import CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquareSpec

/-!
# Functional correctness of CryptOpt's `solinas_square`

`SolinasSquareBlock.solinasSquareBlock` is CryptOpt's `fiat_curve25519_solinas_square`,
and `CorresX86Mem.solinasSquareBlock_corres` states that it refines the abstract run
`absRunMem solinasSquareBlock` over `SRmem solinasCells`. This module proves that the
abstract run meets fiat-crypto's `sqr_correct` (`SolinasSquareSpec`) and transports the
result to the machine.

The abstract run is evaluated instruction by instruction. The abstract state is kept in
the form `mkS base V cf of m`: the thirteen written registers in a record `V`, every other
register from the initial valuation `base`, the two carry flags and the memory. One
transport lemma per instruction form (`run_adcx`, `run_mulxMem`, `run_storeMem`, …)
replaces the head instruction by fresh names for the words it computes, together with
their equation over `Nat` (`w + 2^64 c = x + y + cin`, `hi 2^64 + lo = x y`). The
limb arithmetic is then closed in two pure `Nat` lemmas: `square_limbs` (the eight-limb
square) and `reduce_limbs` (the two folds by `38 = 2^256 mod p`), both by `omega` with the
partial products as atoms.

## Main results

* `square_limbs`, `reduce_limbs`, `square_reduce_correct`: the limb arithmetic of the
  kernel.
* `absRunMem_solinas_sqOut`, `absRunMem_solinas_spec`: the abstract run leaves `%rdi`
  unchanged and meets `SolinasSquareSpec` when the spill slots are apart from the input
  limbs (`SpillsApart`).
* `solinasSquare_correct`: for every machine state whose `solinasCells` are separated,
  the output words of `runBlock st solinasSquareBlock` at `[rdi + 8i]` meet
  `SolinasSquareSpec` against the input words at `[rsi + 8i]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquare

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (limbsNat p25519)

/-! ## A flat register valuation -/

/-- The values of the thirteen registers the kernel writes. -/
structure Reg13 where
  /-- `%rax`. -/
  rax : BitVec 64
  /-- `%rbx`. -/
  rbx : BitVec 64
  /-- `%rcx`. -/
  rcx : BitVec 64
  /-- `%rdx`. -/
  rdx : BitVec 64
  /-- `%rbp`. -/
  rbp : BitVec 64
  /-- `%r8`. -/
  r8 : BitVec 64
  /-- `%r9`. -/
  r9 : BitVec 64
  /-- `%r10`. -/
  r10 : BitVec 64
  /-- `%r11`. -/
  r11 : BitVec 64
  /-- `%r12`. -/
  r12 : BitVec 64
  /-- `%r13`. -/
  r13 : BitVec 64
  /-- `%r14`. -/
  r14 : BitVec 64
  /-- `%r15`. -/
  r15 : BitVec 64

/-- The register valuation with the thirteen written registers from `v` and every
    other register from `base`. -/
def regsOf (v : Reg13) (base : String → BitVec 64) (r : String) : BitVec 64 :=
  if r = "%rax" then v.rax else if r = "%rbx" then v.rbx else if r = "%rcx" then v.rcx
  else if r = "%rdx" then v.rdx else if r = "%rbp" then v.rbp else if r = "%r8" then v.r8
  else if r = "%r9" then v.r9 else if r = "%r10" then v.r10 else if r = "%r11" then v.r11
  else if r = "%r12" then v.r12 else if r = "%r13" then v.r13 else if r = "%r14" then v.r14
  else if r = "%r15" then v.r15 else base r

/-- The abstract state with registers `regsOf v base`, carry flags `cf`, `of` and
    memory `m`. -/
def mkS (base : String → BitVec 64) (v : Reg13) (cf of : Bool) (m : BitVec 64 → BitVec 64) :
    AMemX :=
  ⟨⟨regsOf v base, cf, of⟩, m⟩

/-- A register read of `regsOf`. -/
class RegRead (d : String) where
  /-- The value read. -/
  get : Reg13 → (String → BitVec 64) → BitVec 64
  /-- The read agrees with `regsOf`. -/
  get_eq : ∀ v base, regsOf v base d = get v base

/-- A register write of `regsOf`. -/
class RegWrite (d : String) where
  /-- The updated valuation. -/
  set : Reg13 → BitVec 64 → Reg13
  /-- The update is a pointwise write at `d`. -/
  set_eq : ∀ v w base, regsOf (set v w) base = fun r => if r = d then w else regsOf v base r

/-- A register that `regsOf` reads from the base valuation. -/
class BaseReg (b : String) where
  /-- The read is the base value. -/
  eq : ∀ v base, regsOf v base b = base b

instance : BaseReg "%rsi" := ⟨fun _ _ => by simp [regsOf]⟩
instance : BaseReg "%rdi" := ⟨fun _ _ => by simp [regsOf]⟩
instance : BaseReg "%rsp" := ⟨fun _ _ => by simp [regsOf]⟩

instance instReadRax : RegRead "%rax" := ⟨fun v _ => v.rax, fun _ _ => by simp [regsOf]⟩
instance instReadRbx : RegRead "%rbx" := ⟨fun v _ => v.rbx, fun _ _ => by simp [regsOf]⟩
instance instReadRcx : RegRead "%rcx" := ⟨fun v _ => v.rcx, fun _ _ => by simp [regsOf]⟩
instance instReadRdx : RegRead "%rdx" := ⟨fun v _ => v.rdx, fun _ _ => by simp [regsOf]⟩
instance instReadRbp : RegRead "%rbp" := ⟨fun v _ => v.rbp, fun _ _ => by simp [regsOf]⟩
instance instReadR8 : RegRead "%r8" := ⟨fun v _ => v.r8, fun _ _ => by simp [regsOf]⟩
instance instReadR9 : RegRead "%r9" := ⟨fun v _ => v.r9, fun _ _ => by simp [regsOf]⟩
instance instReadR10 : RegRead "%r10" := ⟨fun v _ => v.r10, fun _ _ => by simp [regsOf]⟩
instance instReadR11 : RegRead "%r11" := ⟨fun v _ => v.r11, fun _ _ => by simp [regsOf]⟩
instance instReadR12 : RegRead "%r12" := ⟨fun v _ => v.r12, fun _ _ => by simp [regsOf]⟩
instance instReadR13 : RegRead "%r13" := ⟨fun v _ => v.r13, fun _ _ => by simp [regsOf]⟩
instance instReadR14 : RegRead "%r14" := ⟨fun v _ => v.r14, fun _ _ => by simp [regsOf]⟩
instance instReadR15 : RegRead "%r15" := ⟨fun v _ => v.r15, fun _ _ => by simp [regsOf]⟩

/-- The write instances share one proof: split on the written register. -/
macro "regwrite_tac" d:str : tactic =>
  `(tactic| (funext r; by_cases h : r = $d
             · subst h; simp [regsOf]
             · simp only [regsOf, h, if_false]))

instance instWriteRax : RegWrite "%rax" := ⟨fun v w => { v with rax := w },
  fun _ _ _ => by regwrite_tac "%rax"⟩
instance instWriteRbx : RegWrite "%rbx" := ⟨fun v w => { v with rbx := w },
  fun _ _ _ => by regwrite_tac "%rbx"⟩
instance instWriteRcx : RegWrite "%rcx" := ⟨fun v w => { v with rcx := w },
  fun _ _ _ => by regwrite_tac "%rcx"⟩
instance instWriteRdx : RegWrite "%rdx" := ⟨fun v w => { v with rdx := w },
  fun _ _ _ => by regwrite_tac "%rdx"⟩
instance instWriteRbp : RegWrite "%rbp" := ⟨fun v w => { v with rbp := w },
  fun _ _ _ => by regwrite_tac "%rbp"⟩
instance instWriteR8 : RegWrite "%r8" := ⟨fun v w => { v with r8 := w },
  fun _ _ _ => by regwrite_tac "%r8"⟩
instance instWriteR9 : RegWrite "%r9" := ⟨fun v w => { v with r9 := w },
  fun _ _ _ => by regwrite_tac "%r9"⟩
instance instWriteR10 : RegWrite "%r10" := ⟨fun v w => { v with r10 := w },
  fun _ _ _ => by regwrite_tac "%r10"⟩
instance instWriteR11 : RegWrite "%r11" := ⟨fun v w => { v with r11 := w },
  fun _ _ _ => by regwrite_tac "%r11"⟩
instance instWriteR12 : RegWrite "%r12" := ⟨fun v w => { v with r12 := w },
  fun _ _ _ => by regwrite_tac "%r12"⟩
instance instWriteR13 : RegWrite "%r13" := ⟨fun v w => { v with r13 := w },
  fun _ _ _ => by regwrite_tac "%r13"⟩
instance instWriteR14 : RegWrite "%r14" := ⟨fun v w => { v with r14 := w },
  fun _ _ _ => by regwrite_tac "%r14"⟩
instance instWriteR15 : RegWrite "%r15" := ⟨fun v w => { v with r15 := w },
  fun _ _ _ => by regwrite_tac "%r15"⟩

/-! ## Word facts -/

/-- The carry-out form of `add_carry` with a carry-in at most one. -/
theorem add_carry_fact (x y : BitVec 64) (c : Nat) (hc : c ≤ 1) :
    (add_carry x y c).toNat + 2 ^ 64 * (if decide (2 ^ 64 ≤ x.toNat + y.toNat + c) then 1 else 0)
      = x.toNat + y.toNat + c := by
  rw [add_carry, BitVec.toNat_ofNat]
  have := x.isLt
  have := y.isLt
  split <;> simp_all <;> omega

/-- The high and low words of a 128-bit product recompose it. -/
theorem mulx_fact (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 (x * y / 2 ^ 64)).toNat * 2 ^ 64 + (BitVec.ofNat 64 (x * y)).toNat
      = x * y := by
  have hxy : x * y < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  have hq : x * y / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hxy
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  have := Nat.div_add_mod (x * y) (2 ^ 64)
  rw [Nat.mul_comm] at this
  exact this

/-- A carry flag read as a number is at most one. -/
theorem bit_le (b : Bool) : (if b then 1 else 0 : Nat) ≤ 1 := by
  cases b <;> simp

/-- A carry bit as a word has the bit as its value. -/
theorem bit_toNat (b : Bool) : (BitVec.ofNat 64 (if b then 1 else 0)).toNat = (if b then 1 else 0) := by
  cases b <;> rfl

/-- The word `38` has value `38`. -/
theorem toNat_ofNat_38 : (BitVec.ofNat 64 38).toNat = 38 := rfl

/-- The word `0` has value `0`. -/
theorem toNat_ofNat_0 : (BitVec.ofNat 64 0).toNat = 0 := rfl

/-- The `lea r15, [r15 + rax]` of the kernel on a carry bit and a word. -/
theorem lea_bit_toNat (b : Bool) (y : BitVec 64) :
    (BitVec.ofNat 64 (if b then 1 else 0) + y * BitVec.ofNat 64 1 + BitVec.ofInt 64 0).toNat
      = ((if b then 1 else 0) + y.toNat) % 2 ^ 64 := by
  have h0 : BitVec.ofInt 64 0 = 0#64 := rfl
  rw [h0, BitVec.mul_one, BitVec.add_zero, BitVec.toNat_add, bit_toNat]

/-- The `cmovo r9, rdx` of the kernel on `r9 = 0`, `rdx = 38`. -/
theorem cmov_toNat (b : Bool) :
    (if b then BitVec.ofNat 64 38 else (0 : BitVec 64)).toNat = 38 * (if b then 1 else 0) := by
  cases b <;> rfl

/-- The low byte of the `SETcc` merge is the condition bit. -/
theorem setcc_byte (x : BitVec 64) (b : Bool) :
    ((x &&& ~~~(0xFF : BitVec 64)) ||| (if b then 1 else 0)).toNat % 2 ^ 8
      = (if b then 1 else 0 : Nat) := by
  rw [← BitVec.toNat_setWidth]
  have : BitVec.setWidth 8 ((x &&& ~~~(0xFF : BitVec 64)) ||| (if b then 1 else 0))
      = if b then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    cases b <;> simp
  rw [this]
  cases b <;> rfl

/-! ## The limb arithmetic of the kernel

The kernel squares in two passes: the off-diagonal partial products `x_i x_j`, `i < j`,
are summed along two carry chains and doubled, the diagonal squares `x_i^2` are added,
giving eight limbs (`square_limbs`); the upper four limbs are multiplied by
`38 = 2^256 mod (2^255 - 19)` and folded into the lower four twice (`reduce_limbs`). -/

/-- The eight-limb square: the carry equations of instructions 1–63 of `solinas_square`
    determine the eight limbs `l00, r9a, …, r15d` as the digits of the square. The
    partial products are the atoms `pij`; the dropped carry-outs `c32`, `c60` and `c63`
    are zero because the high word of `x2 x3` is at most `2^64 - 2` and the square is
    below `2^512`. -/
theorem square_limbs
    (p00 p01 p02 p03 p11 p12 p13 p22 p23 p33 : Nat)
    (h00 l00 h01 l01 h02 l02 h03 l03 h11 l11 h12 l12 h13 l13 h22 l22 h23 l23 h33 l33 : Nat)
    (m01 : h01 * 2 ^ 64 + l01 = p01) (m02 : h02 * 2 ^ 64 + l02 = p02)
    (m00 : h00 * 2 ^ 64 + l00 = p00) (m03 : h03 * 2 ^ 64 + l03 = p03)
    (m11 : h11 * 2 ^ 64 + l11 = p11) (m12 : h12 * 2 ^ 64 + l12 = p12)
    (m13 : h13 * 2 ^ 64 + l13 = p13) (m23 : h23 * 2 ^ 64 + l23 = p23)
    (m22 : h22 * 2 ^ 64 + l22 = p22) (m33 : h33 * 2 ^ 64 + l33 = p33)
    (hp23 : p23 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (hl23 : l23 < 2 ^ 64)
    (r11a r10a rcxa r10b r13a rbxa r14a r10c raxa r15a r11b rcxb r13b r14b r9a rbpa r12a raxb r11c
      r15b rcxc raxc r15c r15d : Nat)
    (c6 c16 c20 c24 c25 c28 c31 c32 c35 c38 c39 c40 c41 c42 c45 c46 c47 c50 c51 c52 c57 c60
      c63 : Nat)
    (b28 : c28 ≤ 1) (b32 : c32 ≤ 1) (b38 : c38 ≤ 1) (b52 : c52 ≤ 1) (b60 : c60 ≤ 1)
    (e6 : r11a + 2 ^ 64 * c6 = l02 + h01)
    (e16 : r10a + 2 ^ 64 * c16 = l03 + h02 + c6)
    (e20 : rcxa + 2 ^ 64 * c20 = l12 + r10a)
    (e24 : r10b + 2 ^ 64 * c24 = l13 + h03 + c16)
    (e25 : r13a + 2 ^ 64 * c25 = h12 + r10b + c20)
    (e28 : rbxa + 2 ^ 64 * c28 = l23 + h13 + c24)
    (e31 : r14a + 2 ^ 64 * c31 = rbxa + c25)
    (e32 : r10c + 2 ^ 64 * c32 = h23 + c28)
    (e35 : raxa + 2 ^ 64 * c35 = l01 + l01)
    (e38 : r15a + 2 ^ 64 * c38 = r10c + c31)
    (e39 : r11b + 2 ^ 64 * c39 = r11a + r11a + c35)
    (e40 : rcxb + 2 ^ 64 * c40 = rcxa + rcxa + c39)
    (e41 : r13b + 2 ^ 64 * c41 = r13a + r13a + c40)
    (e42 : r14b + 2 ^ 64 * c42 = r14a + r14a + c41)
    (e45 : r9a + 2 ^ 64 * c45 = h00 + raxa)
    (e46 : rbpa + 2 ^ 64 * c46 = l11 + r11b + c45)
    (e47 : r12a + 2 ^ 64 * c47 = h11 + rcxb + c46)
    (e50 : raxb + 2 ^ 64 * c50 = l22 + r13b + c47)
    (e51 : r11c + 2 ^ 64 * c51 = h22 + r14b + c50)
    (e52 : r15b + 2 ^ 64 * c52 = r15a + r15a + c42)
    (e57 : rcxc + 2 ^ 64 * c57 = l33 + r15b + c51)
    (e60 : raxc + 2 ^ 64 * c60 = c38 + c52)
    (e62 : r15c = (c38 + raxc) % 2 ^ 64)
    (e63 : r15d + 2 ^ 64 * c63 = r15c + h33 + c57)
    (hsq : p00 + 2 ^ 64 * (2 * p01) + 2 ^ 128 * (2 * p02 + p11) + 2 ^ 192 * (2 * p03 + 2 * p12)
      + 2 ^ 256 * (2 * p13 + p22) + 2 ^ 320 * (2 * p23) + 2 ^ 384 * p33 < 2 ^ 512) :
    l00 + 2 ^ 64 * r9a + 2 ^ 128 * rbpa + 2 ^ 192 * r12a + 2 ^ 256 * raxb + 2 ^ 320 * r11c
      + 2 ^ 384 * rcxc + 2 ^ 448 * r15d
      = p00 + 2 ^ 64 * (2 * p01) + 2 ^ 128 * (2 * p02 + p11) + 2 ^ 192 * (2 * p03 + 2 * p12)
      + 2 ^ 256 * (2 * p13 + p22) + 2 ^ 320 * (2 * p23) + 2 ^ 384 * p33 := by
  have hc32 : c32 = 0 := by clear * - m23 hp23 hl23 e32 b28 b32; omega
  have hc60 : c60 = 0 := by clear * - e60 b38 b52 b60; omega
  have hr15c : r15c = c38 + raxc := by clear * - e62 e60 b38 b52 hc60; omega
  subst hc32 hc60 hr15c
  have key : l00 + 2 ^ 64 * r9a + 2 ^ 128 * rbpa + 2 ^ 192 * r12a + 2 ^ 256 * raxb
      + 2 ^ 320 * r11c + 2 ^ 384 * rcxc + 2 ^ 448 * r15d + 2 ^ 512 * c63
      = p00 + 2 ^ 64 * (2 * p01) + 2 ^ 128 * (2 * p02 + p11) + 2 ^ 192 * (2 * p03 + 2 * p12)
      + 2 ^ 256 * (2 * p13 + p22) + 2 ^ 320 * (2 * p23) + 2 ^ 384 * p33 := by
    clear * - m01 m02 m00 m03 m11 m12 m13 m23 m22 m33 e6 e16 e20 e24 e25 e28 e31 e32 e35 e38
      e39 e40 e41 e42 e45 e46 e47 e50 e51 e52 e57 e60 e63
    omega
  omega

/-- The two Solinas folds: the carry equations of instructions 64–93 of `solinas_square`
    turn the eight limbs `t0, …, t7` into four output limbs `r8c, r12b, r15e, r10e`
    whose value differs from the eight-limb value by a multiple of `2^256 - 38`. The
    dropped carry-outs are zero because the fifth limb of the first fold is at most `39`. -/
theorem reduce_limbs (t0 t1 t2 t3 t4 t5 t6 t7 : Nat) (ht7 : t7 < 2 ^ 64)
    (hi56 lo56 hi64 lo64 hi67 lo67 hi69 lo69 hi78 lo78 : Nat)
    (m56 : hi56 * 2 ^ 64 + lo56 = 38 * t4) (m64 : hi64 * 2 ^ 64 + lo64 = 38 * t5)
    (m67 : hi67 * 2 ^ 64 + lo67 = 38 * t6) (m69 : hi69 * 2 ^ 64 + lo69 = 38 * t7)
    (r10d r9b rbpb rcxd r14c rbxb r13c r11d rcxe r8b r12b r15e r10e r8c : Nat)
    (hr14c : r14c < 2 ^ 64) (hrbxb : rbxb < 2 ^ 64) (hr13c : r13c < 2 ^ 64) (hr11d : r11d < 2 ^ 64)
    (hr8b : r8b < 2 ^ 64) (hr8c : r8c < 2 ^ 64) (hlo78 : lo78 < 2 ^ 64)
    (m78 : hi78 * 2 ^ 64 + lo78 = 38 * rcxe)
    (c66 c68 c70 c72 c73 c74 c75 c76 c77 c80 c82 c85 c87 c91 : Nat)
    (b70 : c70 ≤ 1) (b76 : c76 ≤ 1) (b87 : c87 ≤ 1)
    (e66 : r10d + 2 ^ 64 * c66 = lo64 + t1)
    (e68 : r9b + 2 ^ 64 * c68 = lo67 + t2 + c66)
    (e70 : rbpb + 2 ^ 64 * c70 = lo69 + t3 + c68)
    (e72 : rcxd + 2 ^ 64 * c72 = hi69 + c70)
    (e73 : r14c + 2 ^ 64 * c73 = lo56 + t0)
    (e74 : rbxb + 2 ^ 64 * c74 = hi56 + r10d + c73)
    (e75 : r13c + 2 ^ 64 * c75 = hi64 + r9b + c74)
    (e76 : r11d + 2 ^ 64 * c76 = hi67 + rbpb + c75)
    (e77 : rcxe + 2 ^ 64 * c77 = rcxd + c76)
    (e80 : r8b + 2 ^ 64 * c80 = lo78 + r14c)
    (e82 : r12b + 2 ^ 64 * c82 = rbxb + c80)
    (e85 : r15e + 2 ^ 64 * c85 = r13c + c82)
    (e87 : r10e + 2 ^ 64 * c87 = r11d + c85)
    (e91 : r8c + 2 ^ 64 * c91 = r8b + 38 * c87) :
    r8c + 2 ^ 64 * r12b + 2 ^ 128 * r15e + 2 ^ 192 * r10e
      + (2 ^ 256 - 38) * (t4 + 2 ^ 64 * t5 + 2 ^ 128 * t6 + 2 ^ 192 * t7 + rcxe + c87)
      = t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4 + 2 ^ 320 * t5
        + 2 ^ 384 * t6 + 2 ^ 448 * t7 := by
  have hhi69 : hi69 ≤ 37 := by clear * - m69 ht7; omega
  have e72' : rcxd = hi69 + c70 := by clear * - hhi69 e72 b70; omega
  have e77' : rcxe = rcxd + c76 := by clear * - hhi69 e72' b70 e77 b76; omega
  have m78' : lo78 = 38 * rcxe := by clear * - hhi69 e72' b70 e77' b76 m78 hlo78; omega
  have e91' : r8c = r8b + 38 * c87 := by
    have hrcxe : rcxe ≤ 39 := by omega
    clear * - hr14c hrbxb hr13c hr11d hr8b hr8c hrcxe m78' b87 e80 e82 e85 e87 e91
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b87 with h | h <;> subst h <;> omega
  have h : ((2 : Nat) ^ 256 - 38 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639898 := by
    norm_num
  rw [h]
  clear * - m56 m64 m67 m69 m78' e66 e68 e70 e72' e73 e74 e75 e76 e77' e80 e82 e85 e87 e91'
  omega

/-! ## One transport lemma per instruction form

Each lemma rewrites `Q (absRunMem (i :: rest) (mkS base V cf of m))` to a goal about
`rest`, naming the words the instruction computes and recording their arithmetic. -/

section Transport

variable {Q : AMemX → Prop} {rest : List (JInstr 64)} {base : String → BitVec 64}
  {V : Reg13} {cf of : Bool} {m : BitVec 64 → BitVec 64}

/-- One step of the abstract run, from the step's result. -/
theorem run_step {i : JInstr 64} {s t : AMemX} (hst : absStepMem i s = t)
    (h : Q (absRunMem rest t)) : Q (absRunMem (i :: rest) s) := by
  subst hst; exact h

/-- `loadMem d b o` from a base register `b`: `d` receives the memory word at `base b + o`. -/
theorem run_loadMem (d b : String) (o : Int) [RegWrite d] [BaseReg b] (x : BitVec 64)
    (hm : m (cellAddr base (b, o)) = x)
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V x) cf of m))) :
    Q (absRunMem (.loadMem d b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ h
  simp only [mkS, absStepMem, loadStepM, RegWrite.set_eq, cellAddr, BaseReg.eq] at hm ⊢
  rw [hm]

/-- `mov d, k`: `d` receives the word `k`. -/
theorem run_mov_imm (d : String) (k : Nat) [RegWrite d]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (BitVec.ofNat 64 k)) cf of m))) :
    Q (absRunMem (.mov d (.imm k) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, movStep2, RegWrite.set_eq, evalX]) h

/-- `mov d, src`: `d` receives the word in `src`. -/
theorem run_mov_reg (d src : String) [RegWrite d] [RegRead src]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (RegRead.get src V base)) cf of m))) :
    Q (absRunMem (.mov d (.reg src) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, movStep2, RegWrite.set_eq, evalX, RegRead.get_eq]) h

/-- `xor d, d`: `d` becomes `0` and both carry flags are cleared. -/
theorem run_xor_self (d : String) [RegWrite d] [RegRead d]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V 0) false false m))) :
    Q (absRunMem (.xor_ d (.reg d) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, xorStep2, RegWrite.set_eq, evalX, BitVec.xor_self]; rfl) h

/-- `inc d`: `d` is incremented and `OF` becomes the given value `o` of the signed-overflow
    bit. -/
theorem run_inc (d : String) [RegWrite d] [RegRead d] (o : Bool)
    (ho : decide ((RegRead.get d V base + 1).toInt ≠ (RegRead.get d V base).toInt + 1) = o)
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (RegRead.get d V base + 1)) cf o m))) :
    Q (absRunMem (.inc d :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ h
  subst ho
  simp only [mkS, absStepMem, incStep2, RegWrite.set_eq, RegRead.get_eq]

/-- `clc`: `CF` is cleared. -/
theorem run_clc (h : Q (absRunMem rest (mkS base V false of m))) :
    Q (absRunMem (.clc :: rest) (mkS base V cf of m)) :=
  run_step rfl h

/-- `test` at any operand size: both carry flags are cleared. -/
theorem run_testN (sz : Nat) (x : String) (o : JOperand)
    (h : Q (absRunMem rest (mkS base V false false m))) :
    Q (absRunMem (.testN sz x o :: rest) (mkS base V cf of m)) :=
  run_step rfl h

/-- `setc d`: the low byte of `d` becomes `CF`. -/
theorem run_setcc_b (d : String) [RegWrite d] [RegRead d]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V
      ((RegRead.get d V base &&& ~~~(0xFF : BitVec 64)) ||| (if cf then 1 else 0))) cf of m))) :
    Q (absRunMem (.setcc .b d :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, setccStep2, condStep2, RegWrite.set_eq,
    RegRead.get_eq]; rfl) h

/-- `movzx d, src` from the low `sz` bits: `d` receives the given word `z` equal to the
    residue. -/
theorem run_movzx (d : String) (sz : Nat) (src : String) [RegWrite d] [RegRead src]
    (z : BitVec 64) (hz : BitVec.ofNat 64 ((RegRead.get src V base).toNat % 2 ^ sz) = z)
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V z) cf of m))) :
    Q (absRunMem (.movzx d sz src :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ h
  subst hz
  simp only [mkS, absStepMem, movzxStep2, RegWrite.set_eq, RegRead.get_eq]

/-- `lea d, [b + i * sc + off]`: `d` receives the address. -/
theorem run_lea (d b i : String) (sc : Nat) (off : Int) [RegWrite d] [RegRead b] [RegRead i]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V (RegRead.get b V base +
      RegRead.get i V base * BitVec.ofNat 64 sc + BitVec.ofInt 64 off)) cf of m))) :
    Q (absRunMem (.lea d b i sc off :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, leaStep2, RegWrite.set_eq, RegRead.get_eq]) h

/-- `adc d, k`: `d` and `CF` receive the sum word and carry-out of `d + k + CF`; the new
    `OF` is a name `o'` with no recorded value. -/
theorem run_adc_imm (d : String) (k : Nat) [RegWrite d] [RegRead d]
    (h : ∀ (w : BitVec 64) (c o' : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (BitVec.ofNat 64 k).toNat + (if cf then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c o' m))) :
    Q (absRunMem (.adc d (.imm k) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, adcStep2, RegWrite.set_eq, RegRead.get_eq, evalX]; rfl)
    (h _ _ _ (add_carry_fact _ _ _ (bit_le cf)))

/-- `cmovo d, src`: `d` receives `src` when `OF` is set. -/
theorem run_cmovo (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : Q (absRunMem rest (mkS base (RegWrite.set d V
      (if of then RegRead.get src V base else RegRead.get d V base)) cf of m))) :
    Q (absRunMem (.cmovcc .o d (.reg src) :: rest) (mkS base V cf of m)) :=
  run_step (by simp only [mkS, absStepMem, cmovccStep2, condStep2, RegWrite.set_eq,
    RegRead.get_eq, evalX]) h

/-- `storeMem b o src` to a base register `b`: the new memory holds `src` at `base b + o`
    and agrees with the old one elsewhere. -/
theorem run_storeMem (b : String) (o : Int) (src : String) [BaseReg b] [RegRead src]
    (h : ∀ m' : BitVec 64 → BitVec 64, m' (cellAddr base (b, o)) = RegRead.get src V base →
      (∀ p, p ≠ cellAddr base (b, o) → m' p = m p) → Q (absRunMem rest (mkS base V cf of m'))) :
    Q (absRunMem (.storeMem b o (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h (fun p => if p = cellAddr base (b, o) then RegRead.get src V base else m p)
    (if_pos rfl) (fun p hp => if_neg hp))
  simp only [mkS, absStepMem, storeStepM, cellAddr, BaseReg.eq, RegRead.get_eq, evalX]
  rfl

/-- `mulx dHi, dLo, [b + o]` with `%rdx` as the implicit operand: `dHi` and `dLo` receive
    the high and low words of the 128-bit product. -/
theorem run_mulxMem (dHi dLo : String) (b : String) (o : Int) [RegWrite dHi] [RegWrite dLo]
    [BaseReg b] (x : BitVec 64) (hm : m (cellAddr base (b, o)) = x)
    (h : ∀ hi lo : BitVec 64, hi.toNat * 2 ^ 64 + lo.toNat = (RegRead.get "%rdx" V base).toNat * x.toNat →
      Q (absRunMem rest (mkS base (RegWrite.set dHi (RegWrite.set dLo V lo) hi) cf of m))) :
    Q (absRunMem (.mulxMem dHi dLo (.reg "%rdx") b o :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (mulx_fact _ _ (RegRead.get "%rdx" V base).isLt x.isLt))
  simp only [mkS, absStepMem, mulxMemStepM, RegWrite.set_eq, cellAddr, BaseReg.eq, evalX,
    RegRead.get_eq] at hm ⊢
  rw [hm]

/-- Register-operand `mulx`: `dHi` and `dLo` receive the high and low words of the product. -/
theorem run_mulx (dHi dLo ra rb : String) [RegWrite dHi] [RegWrite dLo] [RegRead ra] [RegRead rb]
    (h : ∀ hi lo : BitVec 64,
      hi.toNat * 2 ^ 64 + lo.toNat = (RegRead.get ra V base).toNat * (RegRead.get rb V base).toNat →
      Q (absRunMem rest (mkS base (RegWrite.set dHi (RegWrite.set dLo V lo) hi) cf of m))) :
    Q (absRunMem (.mulx dHi dLo (.reg ra) (.reg rb) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (mulx_fact _ _ (RegRead.get ra V base).isLt (RegRead.get rb V base).isLt))
  simp only [mkS, absStepMem, mulxStep2, RegWrite.set_eq, RegRead.get_eq]

/-- `adcx d, src`: `d` and `CF` receive the sum word and carry-out of `d + src + CF`. -/
theorem run_adcx (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (RegRead.get src V base).toNat + (if cf then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) c of m))) :
    Q (absRunMem (.adcx d (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le cf)))
  simp only [mkS, absStepMem, adcxStep2, RegWrite.set_eq, RegRead.get_eq]
  rfl

/-- `adox d, src`: `d` and `OF` receive the sum word and carry-out of `d + src + OF`. -/
theorem run_adox (d src : String) [RegWrite d] [RegRead d] [RegRead src]
    (h : ∀ (w : BitVec 64) (c : Bool),
      w.toNat + 2 ^ 64 * (if c then 1 else 0) =
        (RegRead.get d V base).toNat + (RegRead.get src V base).toNat + (if of then 1 else 0) →
      Q (absRunMem rest (mkS base (RegWrite.set d V w) cf c m))) :
    Q (absRunMem (.adox d (.reg src) :: rest) (mkS base V cf of m)) := by
  refine run_step ?_ (h _ _ (add_carry_fact _ _ _ (bit_le of)))
  simp only [mkS, absStepMem, adoxStep2, RegWrite.set_eq, RegRead.get_eq]
  rfl

end Transport

/-- The word `0` has value `0`. -/
theorem toNat_zero_64 : (0 : BitVec 64).toNat = 0 := rfl

set_option exponentiation.threshold 600 in
/-- The limb equations of the whole kernel over 64-bit words give the field
    specification: the output limbs `r8c, r12b, r15e, r10e` represent a value congruent
    to the square of the input limbs `x0 … x3` modulo `2^255 - 19`. The hypotheses are
    the word-level carry and product equations that the abstract run of
    `solinas_square` produces, instruction by instruction. -/
theorem square_reduce_correct {x0 x1 x2 x3 : BitVec 64}
    {h00 l00 h01 l01 h02 l02 h03 l03 h11 l11 h12 l12 h13 l13 h22 l22 h23 l23 h33 l33 : BitVec 64}
    {hi56 lo56 hi64 lo64 hi67 lo67 hi69 lo69 hi78 lo78 : BitVec 64}
    {r11a r10a rcxa r10b r13a rbxa r14a r10c raxa r15a r11b rcxb r13b r14b r9a rbpa r12a raxb
      r11c r15b rcxc raxc r15d : BitVec 64}
    {r10d r9b rbpb rcxd r14c rbxb r13c r11d rcxe r8b r12b r15e r10e r8c : BitVec 64}
    {c6 c16 c20 c24 c25 c28 c31 c32 c35 c38 c39 c40 c41 c42 c45 c46 c47 c50 c51 c52 c57 c60
      c63 : Bool}
    {c66 c68 c70 c72 c73 c74 c75 c76 c77 c80 c82 c85 c87 c91 : Bool}
    (m01 : h01.toNat * 2 ^ 64 + l01.toNat = x0.toNat * x1.toNat)
    (m02 : h02.toNat * 2 ^ 64 + l02.toNat = x0.toNat * x2.toNat)
    (m00 : h00.toNat * 2 ^ 64 + l00.toNat = x0.toNat * x0.toNat)
    (m03 : h03.toNat * 2 ^ 64 + l03.toNat = x3.toNat * x0.toNat)
    (m11 : h11.toNat * 2 ^ 64 + l11.toNat = x1.toNat * x1.toNat)
    (m12 : h12.toNat * 2 ^ 64 + l12.toNat = x1.toNat * x2.toNat)
    (m13 : h13.toNat * 2 ^ 64 + l13.toNat = x1.toNat * x3.toNat)
    (m23 : h23.toNat * 2 ^ 64 + l23.toNat = x2.toNat * x3.toNat)
    (m22 : h22.toNat * 2 ^ 64 + l22.toNat = x2.toNat * x2.toNat)
    (m33 : h33.toNat * 2 ^ 64 + l33.toNat = x3.toNat * x3.toNat)
    (e6 : r11a.toNat + 2 ^ 64 * (if c6 then 1 else 0) = l02.toNat + h01.toNat)
    (e16 : r10a.toNat + 2 ^ 64 * (if c16 then 1 else 0)
      = l03.toNat + h02.toNat + (if c6 then 1 else 0))
    (e20 : rcxa.toNat + 2 ^ 64 * (if c20 then 1 else 0) = l12.toNat + r10a.toNat)
    (e24 : r10b.toNat + 2 ^ 64 * (if c24 then 1 else 0)
      = l13.toNat + h03.toNat + (if c16 then 1 else 0))
    (e25 : r13a.toNat + 2 ^ 64 * (if c25 then 1 else 0)
      = h12.toNat + r10b.toNat + (if c20 then 1 else 0))
    (e28 : rbxa.toNat + 2 ^ 64 * (if c28 then 1 else 0)
      = l23.toNat + h13.toNat + (if c24 then 1 else 0))
    (e31 : r14a.toNat + 2 ^ 64 * (if c31 then 1 else 0) = rbxa.toNat + (if c25 then 1 else 0))
    (e32 : r10c.toNat + 2 ^ 64 * (if c32 then 1 else 0) = h23.toNat + (if c28 then 1 else 0))
    (e35 : raxa.toNat + 2 ^ 64 * (if c35 then 1 else 0) = l01.toNat + l01.toNat)
    (e38 : r15a.toNat + 2 ^ 64 * (if c38 then 1 else 0) = r10c.toNat + (if c31 then 1 else 0))
    (e39 : r11b.toNat + 2 ^ 64 * (if c39 then 1 else 0)
      = r11a.toNat + r11a.toNat + (if c35 then 1 else 0))
    (e40 : rcxb.toNat + 2 ^ 64 * (if c40 then 1 else 0)
      = rcxa.toNat + rcxa.toNat + (if c39 then 1 else 0))
    (e41 : r13b.toNat + 2 ^ 64 * (if c41 then 1 else 0)
      = r13a.toNat + r13a.toNat + (if c40 then 1 else 0))
    (e42 : r14b.toNat + 2 ^ 64 * (if c42 then 1 else 0)
      = r14a.toNat + r14a.toNat + (if c41 then 1 else 0))
    (e45 : r9a.toNat + 2 ^ 64 * (if c45 then 1 else 0) = h00.toNat + raxa.toNat)
    (e46 : rbpa.toNat + 2 ^ 64 * (if c46 then 1 else 0)
      = l11.toNat + r11b.toNat + (if c45 then 1 else 0))
    (e47 : r12a.toNat + 2 ^ 64 * (if c47 then 1 else 0)
      = h11.toNat + rcxb.toNat + (if c46 then 1 else 0))
    (e50 : raxb.toNat + 2 ^ 64 * (if c50 then 1 else 0)
      = l22.toNat + r13b.toNat + (if c47 then 1 else 0))
    (e51 : r11c.toNat + 2 ^ 64 * (if c51 then 1 else 0)
      = h22.toNat + r14b.toNat + (if c50 then 1 else 0))
    (e52 : r15b.toNat + 2 ^ 64 * (if c52 then 1 else 0)
      = r15a.toNat + r15a.toNat + (if c42 then 1 else 0))
    (e57 : rcxc.toNat + 2 ^ 64 * (if c57 then 1 else 0)
      = l33.toNat + r15b.toNat + (if c51 then 1 else 0))
    (e60 : raxc.toNat + 2 ^ 64 * (if c60 then 1 else 0)
      = (if c38 then 1 else 0) + (if c52 then 1 else 0))
    (e63 : r15d.toNat + 2 ^ 64 * (if c63 then 1 else 0)
      = ((if c38 then 1 else 0) + raxc.toNat) % 2 ^ 64 + h33.toNat + (if c57 then 1 else 0))
    (m56 : hi56.toNat * 2 ^ 64 + lo56.toNat = 38 * raxb.toNat)
    (m64 : hi64.toNat * 2 ^ 64 + lo64.toNat = 38 * r11c.toNat)
    (m67 : hi67.toNat * 2 ^ 64 + lo67.toNat = 38 * rcxc.toNat)
    (m69 : hi69.toNat * 2 ^ 64 + lo69.toNat = 38 * r15d.toNat)
    (m78 : hi78.toNat * 2 ^ 64 + lo78.toNat = 38 * rcxe.toNat)
    (e66 : r10d.toNat + 2 ^ 64 * (if c66 then 1 else 0) = lo64.toNat + r9a.toNat)
    (e68 : r9b.toNat + 2 ^ 64 * (if c68 then 1 else 0)
      = lo67.toNat + rbpa.toNat + (if c66 then 1 else 0))
    (e70 : rbpb.toNat + 2 ^ 64 * (if c70 then 1 else 0)
      = lo69.toNat + r12a.toNat + (if c68 then 1 else 0))
    (e72 : rcxd.toNat + 2 ^ 64 * (if c72 then 1 else 0) = hi69.toNat + (if c70 then 1 else 0))
    (e73 : r14c.toNat + 2 ^ 64 * (if c73 then 1 else 0) = lo56.toNat + l00.toNat)
    (e74 : rbxb.toNat + 2 ^ 64 * (if c74 then 1 else 0)
      = hi56.toNat + r10d.toNat + (if c73 then 1 else 0))
    (e75 : r13c.toNat + 2 ^ 64 * (if c75 then 1 else 0)
      = hi64.toNat + r9b.toNat + (if c74 then 1 else 0))
    (e76 : r11d.toNat + 2 ^ 64 * (if c76 then 1 else 0)
      = hi67.toNat + rbpb.toNat + (if c75 then 1 else 0))
    (e77 : rcxe.toNat + 2 ^ 64 * (if c77 then 1 else 0) = rcxd.toNat + (if c76 then 1 else 0))
    (e80 : r8b.toNat + 2 ^ 64 * (if c80 then 1 else 0) = lo78.toNat + r14c.toNat)
    (e82 : r12b.toNat + 2 ^ 64 * (if c82 then 1 else 0) = rbxb.toNat + (if c80 then 1 else 0))
    (e85 : r15e.toNat + 2 ^ 64 * (if c85 then 1 else 0) = r13c.toNat + (if c82 then 1 else 0))
    (e87 : r10e.toNat + 2 ^ 64 * (if c87 then 1 else 0) = r11d.toNat + (if c85 then 1 else 0))
    (e91 : r8c.toNat + 2 ^ 64 * (if c91 then 1 else 0) = r8b.toNat + 38 * (if c87 then 1 else 0)) :
    limbsNat r8c r12b r15e r10e % curve25519P
      = (limbsNat x0 x1 x2 x3 * limbsNat x0 x1 x2 x3) % curve25519P := by
  have hp23 : x2.toNat * x3.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    have := x2.isLt
    have := x3.isLt
    apply Nat.mul_le_mul <;> omega
  have hX : limbsNat x0 x1 x2 x3 < 2 ^ 256 := by
    unfold limbsNat
    have := x0.isLt
    have := x1.isLt
    have := x2.isLt
    have := x3.isLt
    omega
  have hbound : x0.toNat * x0.toNat + 2 ^ 64 * (2 * (x0.toNat * x1.toNat))
      + 2 ^ 128 * (2 * (x0.toNat * x2.toNat) + x1.toNat * x1.toNat)
      + 2 ^ 192 * (2 * (x3.toNat * x0.toNat) + 2 * (x1.toNat * x2.toNat))
      + 2 ^ 256 * (2 * (x1.toNat * x3.toNat) + x2.toNat * x2.toNat)
      + 2 ^ 320 * (2 * (x2.toNat * x3.toNat)) + 2 ^ 384 * (x3.toNat * x3.toNat)
      = limbsNat x0 x1 x2 x3 * limbsNat x0 x1 x2 x3 := by
    unfold limbsNat
    ring
  have hlt : limbsNat x0 x1 x2 x3 * limbsNat x0 x1 x2 x3 < 2 ^ 512 :=
    lt_of_lt_of_eq (Nat.mul_lt_mul'' hX hX) (by norm_num)
  have hsq := square_limbs (m01 := m01) (m02 := m02) (m00 := m00) (m03 := m03) (m11 := m11)
    (m12 := m12) (m13 := m13) (m23 := m23) (m22 := m22) (m33 := m33) (hp23 := hp23)
    (hl23 := l23.isLt) (b28 := bit_le c28) (b32 := bit_le c32) (b38 := bit_le c38)
    (b52 := bit_le c52) (b60 := bit_le c60) (e6 := e6) (e16 := e16) (e20 := e20) (e24 := e24)
    (e25 := e25) (e28 := e28) (e31 := e31) (e32 := e32) (e35 := e35) (e38 := e38) (e39 := e39)
    (e40 := e40) (e41 := e41) (e42 := e42) (e45 := e45) (e46 := e46) (e47 := e47) (e50 := e50)
    (e51 := e51) (e52 := e52) (e57 := e57) (e60 := e60) (e62 := rfl) (e63 := e63)
    (hsq := hbound.symm ▸ hlt)
  have hred := reduce_limbs (ht7 := r15d.isLt) (m56 := m56) (m64 := m64) (m67 := m67)
    (m69 := m69) (hr14c := r14c.isLt) (hrbxb := rbxb.isLt) (hr13c := r13c.isLt)
    (hr11d := r11d.isLt) (hr8b := r8b.isLt) (hr8c := r8c.isLt) (hlo78 := lo78.isLt)
    (m78 := m78) (b70 := bit_le c70) (b76 := bit_le c76) (b87 := bit_le c87) (e66 := e66)
    (e68 := e68) (e70 := e70) (e72 := e72) (e73 := e73) (e74 := e74) (e75 := e75) (e76 := e76)
    (e77 := e77) (e80 := e80) (e82 := e82) (e85 := e85) (e87 := e87) (e91 := e91)
  have h38 : (2 : Nat) ^ 256 - 38 = curve25519P * 2 := by
    norm_num [curve25519P, p25519]
  rw [← hbound, ← hsq, ← hred, h38, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  rfl

/-! ## The layout conditions -/

/-- The input limb cells `[rsi + 8i]`. -/
def solinasInputCells : List (String × Int) :=
  [("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24)]

/-- The spill slots `[rsp - 0x80]` … `[rsp - 0x58]`. -/
def solinasSpillCells : List (String × Int) :=
  [("%rsp", -0x80), ("%rsp", -0x78), ("%rsp", -0x70), ("%rsp", -0x68), ("%rsp", -0x60),
   ("%rsp", -0x58)]

/-- No spill slot shares an address with an input limb. -/
def SpillsApart (regs : String → BitVec 64) : Prop :=
  ∀ c ∈ solinasSpillCells, ∀ c' ∈ solinasInputCells, cellAddr regs c ≠ cellAddr regs c'

/-- The memory `m` holds the input limbs `x0 … x3` at `[rsi + 8i]`. -/
def Inputs (m : BitVec 64 → BitVec 64) (base : String → BitVec 64) (x0 x1 x2 x3 : BitVec 64) :
    Prop :=
  m (cellAddr base ("%rsi", 0)) = x0 ∧ m (cellAddr base ("%rsi", 8)) = x1 ∧
    m (cellAddr base ("%rsi", 16)) = x2 ∧ m (cellAddr base ("%rsi", 24)) = x3

/-- A store to a spill slot keeps the input limbs. -/
theorem inputs_store {m m' : BitVec 64 → BitVec 64} {base : String → BitVec 64}
    {c : String × Int} (hc : c ∈ solinasSpillCells) (hsep : SpillsApart base)
    (f : ∀ p, p ≠ cellAddr base c → m' p = m p) {x0 x1 x2 x3 : BitVec 64}
    (h : Inputs m base x0 x1 x2 x3) : Inputs m' base x0 x1 x2 x3 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have ne : ∀ c' ∈ solinasInputCells, cellAddr base c' ≠ cellAddr base c :=
    fun c' hc' he => hsep c hc c' hc' he.symm
  refine ⟨(f _ (ne _ ?_)).trans h0, (f _ (ne _ ?_)).trans h1, (f _ (ne _ ?_)).trans h2,
    (f _ (ne _ ?_)).trans h3⟩ <;> simp [solinasInputCells]

/-- The output condition on a final state: `%rdi` holds its initial value, and the four
    words at `[rdi + 8i]` (addresses under the initial registers `base`) represent a
    value congruent to the square of the input value. -/
def SqOut (base : String → BitVec 64) (x0 x1 x2 x3 : BitVec 64) (s : AMemX) : Prop :=
  s.c.regs "%rdi" = base "%rdi" ∧
  limbsNat (s.mem (cellAddr base ("%rdi", 0))) (s.mem (cellAddr base ("%rdi", 8)))
      (s.mem (cellAddr base ("%rdi", 16))) (s.mem (cellAddr base ("%rdi", 24))) % curve25519P
    = (limbsNat x0 x1 x2 x3 * limbsNat x0 x1 x2 x3) % curve25519P

/-! ## The abstract run of `solinas_square` -/

/-- The abstract run of `solinas_square` from any state whose spill slots are apart from
    its input limbs satisfies `SqOut`: `%rdi` is unchanged and the output limbs represent
    the square of the input limbs modulo `2^255 - 19`. -/
theorem absRunMem_solinas_sqOut (base : String → BitVec 64) (V : Reg13) (cf of : Bool)
    (mem : BitVec 64 → BitVec 64) (hsep : SpillsApart base) :
    SqOut base (mem (cellAddr base ("%rsi", 0))) (mem (cellAddr base ("%rsi", 8)))
      (mem (cellAddr base ("%rsi", 16))) (mem (cellAddr base ("%rsi", 24)))
      (absRunMem X86Backend.SolinasSquareBlock.solinasSquareBlock (mkS base V cf of mem)) := by
  generalize hx0 : mem (cellAddr base ("%rsi", 0)) = x0
  generalize hx1 : mem (cellAddr base ("%rsi", 8)) = x1
  generalize hx2 : mem (cellAddr base ("%rsi", 16)) = x2
  generalize hx3 : mem (cellAddr base ("%rsi", 24)) = x3
  have hI : Inputs mem base x0 x1 x2 x3 := ⟨hx0, hx1, hx2, hx3⟩
  clear hx0 hx1 hx2 hx3
  unfold X86Backend.SolinasSquareBlock.solinasSquareBlock
  -- instructions 1–33: partial products and the undoubled carry chains
  refine run_loadMem "%rdx" "%rsi" 0 x0 hI.1 ?_
  refine run_mulxMem "%r10" "%rax" "%rsi" 8 x1 hI.2.1 fun h01 l01 m01 => ?_
  refine run_loadMem "%rdx" "%rsi" 0 x0 hI.1 ?_
  refine run_mulxMem "%rcx" "%r11" "%rsi" 16 x2 hI.2.2.1 fun h02 l02 m02 => ?_
  refine run_xor_self "%rdx" ?_
  refine run_adox "%r11" "%r10" fun r11a c6 e6 => ?_
  refine run_loadMem "%rdx" "%rsi" 0 x0 hI.1 ?_
  refine run_mulx "%r9" "%r8" "%rdx" "%rdx" fun h00 l00 m00 => ?_
  refine run_loadMem "%rdx" "%rsi" 24 x3 hI.2.2.2 ?_
  refine run_storeMem "%rsp" (-128) "%rbx" fun m1 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_mulxMem "%rbx" "%r10" "%rsi" 0 x0 hI.1 fun h03 l03 m03 => ?_
  refine run_loadMem "%rdx" "%rsi" 8 x1 hI.2.1 ?_
  refine run_storeMem "%rsp" (-120) "%rbp" fun m2 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_storeMem "%rsp" (-112) "%r12" fun m3 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_mulx "%r12" "%rbp" "%rdx" "%rdx" fun h11 l11 m11 => ?_
  refine run_adox "%r10" "%rcx" fun r10a c16 e16 => ?_
  refine run_loadMem "%rdx" "%rsi" 8 x1 hI.2.1 ?_
  refine run_storeMem "%rsp" (-104) "%r13" fun m4 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_mulxMem "%r13" "%rcx" "%rsi" 16 x2 hI.2.2.1 fun h12 l12 m12 => ?_
  refine run_adcx "%rcx" "%r10" fun rcxa c20 e20 => ?_
  refine run_loadMem "%rdx" "%rsi" 8 x1 hI.2.1 ?_
  refine run_storeMem "%rsp" (-96) "%r14" fun m5 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_mulxMem "%r14" "%r10" "%rsi" 24 x3 hI.2.2.2 fun h13 l13 m13 => ?_
  refine run_adox "%r10" "%rbx" fun r10b c24 e24 => ?_
  refine run_adcx "%r13" "%r10" fun r13a c25 e25 => ?_
  refine run_loadMem "%rdx" "%rsi" 16 x2 hI.2.2.1 ?_
  refine run_mulxMem "%r10" "%rbx" "%rsi" 24 x3 hI.2.2.2 fun h23 l23 m23 => ?_
  refine run_adox "%rbx" "%r14" fun rbxa c28 e28 => ?_
  refine run_mov_imm "%rdx" 0 ?_
  refine run_mov_reg "%r14" "%rdx" ?_
  refine run_adcx "%r14" "%rbx" fun r14a c31 e31 => ?_
  refine run_adox "%r10" "%rdx" fun r10c c32 e32 => ?_
  refine run_mov_imm "%rbx" 18446744073709551613 ?_
  -- instructions 34–65: doubling, diagonal squares, first reduction multiplies
  refine run_inc "%rbx" false (by dsimp only [RegRead.get, RegWrite.set]; rfl) ?_
  refine run_adox "%rax" "%rax" fun raxa c35 e35 => ?_
  refine run_storeMem "%rsp" (-88) "%r15" fun m6 _ f => ?_
  replace hI := inputs_store (by simp [solinasSpillCells]) hsep f hI
  clear f
  refine run_mov_reg "%r15" "%rdx" ?_
  refine run_adcx "%r15" "%r10" fun r15a c38 e38 => ?_
  refine run_adox "%r11" "%r11" fun r11b c39 e39 => ?_
  refine run_adox "%rcx" "%rcx" fun rcxb c40 e40 => ?_
  refine run_adox "%r13" "%r13" fun r13b c41 e41 => ?_
  refine run_adox "%r14" "%r14" fun r14b c42 e42 => ?_
  refine run_setcc_b "%r10" ?_
  refine run_clc ?_
  refine run_adcx "%r9" "%rax" fun r9a c45 e45 => ?_
  refine run_adcx "%rbp" "%r11" fun rbpa c46 e46 => ?_
  refine run_adcx "%r12" "%rcx" fun r12a c47 e47 => ?_
  refine run_loadMem "%rdx" "%rsi" 16 x2 hI.2.2.1 ?_
  refine run_mulx "%r11" "%rax" "%rdx" "%rdx" fun h22 l22 m22 => ?_
  refine run_adcx "%rax" "%r13" fun raxb c50 e50 => ?_
  refine run_adcx "%r11" "%r14" fun r11c c51 e51 => ?_
  refine run_adox "%r15" "%r15" fun r15b c52 e52 => ?_
  refine run_loadMem "%rdx" "%rsi" 24 x3 hI.2.2.2 ?_
  refine run_mulx "%r13" "%rcx" "%rdx" "%rdx" fun h33 l33 m33 => ?_
  refine run_mov_imm "%rdx" 38 ?_
  refine run_mulx "%rbx" "%r14" "%rdx" "%rax" fun hi56 lo56 m56 => ?_
  refine run_adcx "%rcx" "%r15" fun rcxc c57 e57 => ?_
  refine run_movzx "%rax" 8 "%r10" (BitVec.ofNat 64 (if c38 then 1 else 0))
    (by dsimp only [RegRead.get, RegWrite.set]; rw [setcc_byte]) ?_
  refine run_mov_imm "%r15" 0 ?_
  refine run_adox "%rax" "%r15" fun raxc c60 e60 => ?_
  refine run_movzx "%r15" 8 "%r10" (BitVec.ofNat 64 (if c38 then 1 else 0))
    (by dsimp only [RegRead.get, RegWrite.set]; rw [setcc_byte]) ?_
  refine run_lea "%r15" "%r15" "%rax" 1 0 ?_
  refine run_adcx "%r15" "%r13" fun r15d c63 e63 => ?_
  refine run_mulx "%r13" "%r10" "%rdx" "%r11" fun hi64 lo64 m64 => ?_
  refine run_testN 8 "%rax" (.reg "%rax") ?_
  -- instructions 66–93: the two folds and the output stores
  refine run_adox "%r10" "%r9" fun r10d c66 e66 => ?_
  refine run_mulx "%r11" "%r9" "%rdx" "%rcx" fun hi67 lo67 m67 => ?_
  refine run_adox "%r9" "%rbp" fun r9b c68 e68 => ?_
  refine run_mulx "%rcx" "%rbp" "%rdx" "%r15" fun hi69 lo69 m69 => ?_
  refine run_adox "%rbp" "%r12" fun rbpb c70 e70 => ?_
  refine run_mov_imm "%r12" 0 ?_
  refine run_adox "%rcx" "%r12" fun rcxd c72 e72 => ?_
  refine run_adcx "%r14" "%r8" fun r14c c73 e73 => ?_
  refine run_adcx "%rbx" "%r10" fun rbxb c74 e74 => ?_
  refine run_adcx "%r13" "%r9" fun r13c c75 e75 => ?_
  refine run_adcx "%r11" "%rbp" fun r11d c76 e76 => ?_
  refine run_adc_imm "%rcx" 0 fun rcxe c77 _ e77 => ?_
  refine run_mulx "%rax" "%r8" "%rdx" "%rcx" fun hi78 lo78 m78 => ?_
  refine run_xor_self "%rax" ?_
  refine run_adox "%r8" "%r14" fun r8b c80 e80 => ?_
  refine run_mov_reg "%r12" "%rax" ?_
  refine run_adox "%r12" "%rbx" fun r12b c82 e82 => ?_
  refine run_storeMem "%rdi" 8 "%r12" fun m7 s83 _ => ?_
  refine run_mov_reg "%r15" "%rax" ?_
  refine run_adox "%r15" "%r13" fun r15e c85 e85 => ?_
  refine run_mov_reg "%r10" "%rax" ?_
  refine run_adox "%r10" "%r11" fun r10e c87 e87 => ?_
  refine run_storeMem "%rdi" 24 "%r10" fun m8 s88 f88 => ?_
  refine run_mov_reg "%r9" "%rax" ?_
  refine run_cmovo "%r9" "%rdx" ?_
  refine run_adcx "%r8" "%r9" fun r8c c91 e91 => ?_
  refine run_storeMem "%rdi" 16 "%r15" fun m9 s92 f92 => ?_
  refine run_storeMem "%rdi" 0 "%r8" fun m10 s93 f93 => ?_
  -- instructions 94–99: restores
  refine run_loadMem "%rbx" "%rsp" (-128) _ rfl ?_
  refine run_loadMem "%rbp" "%rsp" (-120) _ rfl ?_
  refine run_loadMem "%r12" "%rsp" (-112) _ rfl ?_
  refine run_loadMem "%r13" "%rsp" (-104) _ rfl ?_
  refine run_loadMem "%r14" "%rsp" (-96) _ rfl ?_
  refine run_loadMem "%r15" "%rsp" (-88) _ rfl ?_
  -- the output cells and the limb equations
  dsimp only [RegRead.get, RegWrite.set, absRunMem, mkS, SqOut] at *
  refine ⟨BaseReg.eq _ _, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, toNat_ofNat_0, toNat_ofNat_38,
    bit_toNat, toNat_zero_64, lea_bit_toNat, cmov_toNat] at *
  have n8_0 : cellAddr base ("%rdi", 8) ≠ cellAddr base ("%rdi", 0) := by simp [cellAddr]
  have n16_0 : cellAddr base ("%rdi", 16) ≠ cellAddr base ("%rdi", 0) := by simp [cellAddr]
  have n24_0 : cellAddr base ("%rdi", 24) ≠ cellAddr base ("%rdi", 0) := by simp [cellAddr]
  have n8_16 : cellAddr base ("%rdi", 8) ≠ cellAddr base ("%rdi", 16) := by simp [cellAddr]
  have n24_16 : cellAddr base ("%rdi", 24) ≠ cellAddr base ("%rdi", 16) := by simp [cellAddr]
  have n8_24 : cellAddr base ("%rdi", 8) ≠ cellAddr base ("%rdi", 24) := by simp [cellAddr]
  rw [s93, f93 _ n16_0, s92, f93 _ n24_0, f92 _ n24_16, s88, f93 _ n8_0, f92 _ n8_16,
    f88 _ n8_24, s83]
  exact square_reduce_correct m01 m02 m00 m03 m11 m12 m13 m23 m22 m33 e6 e16 e20 e24 e25 e28
    e31 e32 e35 e38 e39 e40 e41 e42 e45 e46 e47 e50 e51 e52 e57 e60 e63 m56 m64 m67 m69 m78
    e66 e68 e70 e72 e73 e74 e75 e76 e77 e80 e82 e85 e87 e91

/-- **The abstract run of `solinas_square` meets the field specification.** For every
    abstract state `a` whose spill slots `[rsp - 0x80]` … `[rsp - 0x58]` are apart from its
    input limbs `[rsi + 8i]`, the run leaves `%rdi` unchanged and its output limbs
    `[rdi + 8i]` represent a value congruent to the square of the input value modulo
    `2^255 - 19`. -/
theorem absRunMem_solinas_spec (a : AMemX) (hsep : SpillsApart a.c.regs) :
    (absRunMem X86Backend.SolinasSquareBlock.solinasSquareBlock a).c.regs "%rdi" = a.c.regs "%rdi" ∧
    SolinasSquareSpec (fun i => a.mem (cellAddr a.c.regs ("%rsi", 8 * (i.val : Int))))
      (fun i => (absRunMem X86Backend.SolinasSquareBlock.solinasSquareBlock a).mem
        (cellAddr a.c.regs ("%rdi", 8 * (i.val : Int)))) := by
  have step : ∀ {regs : String → BitVec 64} {r s : String} {x : BitVec 64}, x = regs r →
      (if r = s then regs s else x) = regs r := by
    intro regs r s x h
    by_cases e : r = s
    · subst e; exact if_pos rfl
    · rw [if_neg e, h]
  obtain ⟨⟨regs, cf, of⟩, mem⟩ := a
  have hr : regsOf ⟨regs "%rax", regs "%rbx", regs "%rcx", regs "%rdx", regs "%rbp", regs "%r8",
      regs "%r9", regs "%r10", regs "%r11", regs "%r12", regs "%r13", regs "%r14", regs "%r15"⟩
      regs = regs := by
    funext r
    exact step (step (step (step (step (step (step (step (step (step (step (step (step
      rfl))))))))))))
  have h := absRunMem_solinas_sqOut regs ⟨regs "%rax", regs "%rbx", regs "%rcx", regs "%rdx",
    regs "%rbp", regs "%r8", regs "%r9", regs "%r10", regs "%r11", regs "%r12", regs "%r13",
    regs "%r14", regs "%r15"⟩ cf of mem hsep
  rw [mkS, hr] at h
  exact h

/-! ## The machine statement -/

/-- Separation of the `solinas_square` cells gives the spill/input separation. -/
theorem spillsApart_of_cellsSeparated (regs : String → BitVec 64)
    (hsep : CellsSeparated solinasCells regs) : SpillsApart regs := by
  intro c hc c' hc' he
  simp only [solinasSpillCells, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [solinasInputCells, List.mem_cons, List.not_mem_nil, or_false] at hc'
  have h1 : c ∈ solinasCells := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [solinasCells]
  have h2 : c' ∈ solinasCells := by
    rcases hc' with rfl | rfl | rfl | rfl <;> simp [solinasCells]
  have := hsep c h1 c' h2 he
  subst this
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hc'


/-- **Functional correctness of CryptOpt's `fiat_curve25519_solinas_square`.** For every
    machine state whose fourteen `solinas_square` cells (input limbs `[rsi + 8i]`, output
    limbs `[rdi + 8i]`, six spill slots below `rsp`) have pairwise distinct addresses, the
    four words the parsed kernel writes at `[rdi + 8i]` represent a value congruent to the
    square of the value of the four input words at `[rsi + 8i]` modulo `2^255 - 19`
    (fiat-crypto's `sqr_correct`). -/
theorem solinasSquare_correct (st : JState 64) (hsep : CellsSeparated solinasCells st.regs) :
    SolinasSquareSpec (fun i => st.mem "%rsi" (8 * (i.val : Int)))
      (fun i => (runBlock st X86Backend.SolinasSquareBlock.solinasSquareBlock).mem "%rdi"
        (8 * (i.val : Int))) := by
  let a : AMemX := ⟨⟨st.regs, st.flagB (·.cf), st.flagB (·.of)⟩, cellMem solinasCells st⟩
  have hSR : SRmem solinasCells st a :=
    ⟨⟨fun _ => rfl, rfl, rfl⟩, fun c hc => (cellMem_eq _ _ hsep c hc).symm, hsep⟩
  have hrun := solinasSquareBlock_corres st a hSR trivial
  obtain ⟨hdi, hspec⟩ := absRunMem_solinas_spec a (spillsApart_of_cellsSeparated _ hsep)
  have hin : ∀ i : Fin 4, st.mem "%rsi" (8 * (i.val : Int))
      = a.mem (cellAddr a.c.regs ("%rsi", 8 * (i.val : Int))) := by
    intro i
    have hc : ("%rsi", 8 * (i.val : Int)) ∈ solinasCells := by
      fin_cases i <;> simp [solinasCells]
    exact (cellMem_eq _ _ hsep _ hc).symm
  have hout : ∀ i : Fin 4,
      (runBlock st X86Backend.SolinasSquareBlock.solinasSquareBlock).mem "%rdi" (8 * (i.val : Int))
      = (absRunMem X86Backend.SolinasSquareBlock.solinasSquareBlock a).mem
          (cellAddr a.c.regs ("%rdi", 8 * (i.val : Int))) := by
    intro i
    have hc : ("%rdi", 8 * (i.val : Int)) ∈ solinasCells := by
      fin_cases i <;> simp [solinasCells]
    rw [hrun.2.1 _ hc]
    simp only [cellAddr, hdi]
  rw [funext hin, funext hout]
  exact hspec

end CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquare
