/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# Widening multiply (two-output `MULX`): source→machine lowering with both outputs

The scalar-ANF source fragment bridged in `LowCTToJInstrCT.lean` (`ArithSrc`,
`lowerArith`) covers only **single-output** scalar arithmetic — `add`/`and`/
`xor`/`imul`, each writing one destination register.  The **two-output widening
multiply** (`MULX`: `(hi, lo) := a · b`, the full 128-bit product split into two
64-bit words) was outside that fragment (audit point 4): the generic
`MachineModel` per-statement denote writes a single named destination, which
does not fit an instruction that defines *two* registers at once.

This module closes that gap.  It introduces a source-level widening-multiply
statement `MulxSrc` (`(hi, lo) := widening_mul a b`), its source denotation
`mulxDenote` (two scalar updates — the high and low 64-bit words of the `Nat`
product), the lowering `lowerMulx` to the single machine `JInstr.mulx`, and the
two guarantees:

* **Functional correctness, both outputs** (`lowerMulx_denote`): under register
  allocation well-formedness (`ρ` injective, `hi ≠ lo`, operands disjoint from
  the destinations) and the state relation `StateMatch ρ`, after running the
  lowered block the machine register `ρ lo` holds the low word and `ρ hi` the
  high word, matching the source `mulxDenote`.  The load-bearing step is the
  **widening-multiply Nat↔BitVec identity** `wumul_split` — that the `wumul`
  `(hi, lo)` pair of the truncated operands equals the `Nat` product split at
  `2⁶⁴`.

* **Constant-time, free** (`lowerMulx_constant_time`): `MULX` is `IsDirect`
  (it is neither `loadMemIdx` nor `storeMemIdx`), so the lowering is in the
  decidable constant-time class and CT follows from `allDirect_constant_time`.

The two-output handling is done **directly in the per-statement denote**: the
single-written-name generic `MachineModel`/`ArithSrc` denote does not fit `MULX`,
so `mulxDenote` performs two scalar updates and `lowerMulx_denote` reasons about
both destination registers explicitly (the `hi ≠ lo` hypothesis is exactly what
keeps the second write from clobbering the first).

A worked kernel `widenMulKernel` instantiates the full chain on a real bignum
step (a single `1×1 → 2` widening multiply, the atom of every schoolbook
multiply), with both the functional theorem, the CT theorem, and a one-vector
value KAT (`a = b = 2⁶⁴−1 ⟹ lo = 1, hi = 2⁶⁴−2`).

**Note (cross-construct unification, separate).** Composing `MulxSrc`
statements with the scalar `lowerSeq` into a *unified* multi-statement program
type — a single source command type ranging over both single- and two-output
statements, lowered by one `lowerSeq` — is the cross-construct unification (w7),
out of scope here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The crux: the widening-multiply Nat↔BitVec identity

`wumul` (`JasminModel.lean`) is `wumul x y = (high_bits (x.toNat * y.toNat),
BitVec.ofNat 64 (x.toNat * y.toNat))` with `high_bits n = BitVec.ofNat 64
(n / 2⁶⁴)`.  The load-bearing identity is that, for source `Nat` operands
`x, y < 2⁶⁴`, the `wumul` pair of the truncated operands is exactly the `Nat`
product `x * y` split into its low and high 64-bit words.  This is what ties the
source `Nat` semantics (`mulxDenote`) to the machine `BitVec` semantics
(`x86_MULX_lo_hi`). -/

/-- **Low-word half of the widening-multiply identity.**  For `x, y < 2⁶⁴`, the
    low word of `wumul (ofNat x) (ofNat y)` is `ofNat ((x*y) % 2⁶⁴)`. -/
theorem wumul_lo (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (wumul (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).2 = BitVec.ofNat 64 ((x * y) % 2 ^ 64) := by
  simp only [wumul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  -- both sides are `BitVec.ofNat 64 (x*y)` up to a `% 2⁶⁴` that `ofNat` absorbs
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd]

/-- **High-word half of the widening-multiply identity.**  For `x, y < 2⁶⁴`, the
    high word of `wumul (ofNat x) (ofNat y)` is `ofNat ((x*y) / 2⁶⁴)`.  Because
    `x*y < 2¹²⁸`, the quotient `(x*y) / 2⁶⁴ < 2⁶⁴` is already in range, but the
    statement keeps the truncating `ofNat` so it matches `high_bits` literally. -/
theorem wumul_hi (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (wumul (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).1 = BitVec.ofNat 64 ((x * y) / 2 ^ 64) := by
  simp only [wumul, high_bits, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-! ## 2. The widening-multiply source statement (a two-output assignment) -/

/-- The two-output widening-multiply source statement: `(hi, lo) := a · b`, where
    `hi`/`lo` are the high/low 64-bit words of the full `Nat` product of the two
    scalar reads `a`, `b`.  This is the source object outside the single-output
    `ArithSrc` fragment. -/
structure MulxSrc where
  hi : String
  lo : String
  a  : String
  b  : String
  deriving Repr

/-- **Source denotation.**  `(hi, lo) := a · b`: two scalar updates of the source
    state — `lo` gets the low 64-bit word `(a·b) % 2⁶⁴`, `hi` the high word
    `(a·b) / 2⁶⁴`.  The low word is written **first**, then the high word, so the
    final state has both; with `hi ≠ lo` (the well-formedness condition the
    lowering also needs) the second write does not clobber the first. -/
def mulxDenote (m : MulxSrc) (rs : RustState) : RustState :=
  let prod := rs.rsScalar m.a * rs.rsScalar m.b
  rsSetScalar (rsSetScalar rs m.lo (prod % 2 ^ 64)) m.hi (prod / 2 ^ 64)

/-! ## 3. The lowering to a single machine `MULX` -/

/-- **The lowering.**  `(hi, lo) := a · b` lowers to the **single** machine
    instruction `MULX ρhi, ρlo, ρa, ρb`, which writes both destination registers
    at once (`evalInstr (.mulx ..)` sets `ρlo := lo`, `ρhi := hi`).  No `mov` is
    needed: `MULX` is non-destructive in its sources. -/
def lowerMulx (ρ : RegMap) (m : MulxSrc) : List (JInstr 64) :=
  [ .mulx (ρ m.hi) (ρ m.lo) (.reg (ρ m.a)) (.reg (ρ m.b)) ]

/-! ## 4. Constant-time, free (`MULX` is `IsDirect`) -/

/-- The lowering is in the decidable constant-time class: `MULX` is neither
    `loadMemIdx` nor `storeMemIdx`, the only two `¬ IsDirect` opcodes, so
    `allDirect` holds by `rfl`. -/
theorem lowerMulx_allDirect (ρ : RegMap) (m : MulxSrc) :
    allDirect (lowerMulx ρ m) = true := rfl

/-- **Source→machine constant-time (free).**  The lowering of a widening-multiply
    statement produces the **same** machine leakage trace from any two initial
    states: its observable control-flow + memory-address sequence is a function
    of the program text alone, leaking nothing about the (possibly secret)
    operand values.  Delivered by the machine keystone `allDirect_constant_time`
    from the trivial `allDirect` check — `MULX` is `IsDirect`, so CT is free. -/
theorem lowerMulx_constant_time (ρ : RegMap) (m : MulxSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerMulx ρ m) = blockLeak s₂ (lowerMulx ρ m) :=
  allDirect_constant_time (lowerMulx ρ m) (lowerMulx_allDirect ρ m) s₁ s₂

/-! ## 5. Functional correctness: both 64-bit outputs (the crux)

`lowerMulx_denote`: under register allocation well-formedness and `StateMatch ρ`,
after running the lowered block the machine state matches the source post-state
`mulxDenote m rs` — i.e. `ρ lo` holds the low word and `ρ hi` the high word,
*both* established via the `wumul` Nat↔BitVec identity.

The well-formedness hypotheses are exactly the constraints a real register
allocator guarantees for a two-output instruction:

* `ρ` injective — distinct source slots get distinct machine registers;
* `hi ≠ lo` — the two destinations are different slots (a `MULX` with equal
  destinations is malformed; this is what keeps the high write from clobbering
  the low one);
* `a ≠ hi`, `a ≠ lo`, `b ≠ hi`, `b ≠ lo` — the source operands are read before
  (and are disjoint from) the two destinations.

`StateMatch ρ` additionally needs the source operands to be in `u64` range
(`rs.rsScalar a, b < 2⁶⁴`) for the truncating `ofNat` on the source side to be
the identity — the scalar-bounds invariant the `LowCT→Jasmin` lowering already
maintains (`ScalarsBounded`). -/

/-- **Functional correctness (both outputs, the crux).**  If the machine state
    `js` matches the source state `rs` under `ρ` and the operands are in `u64`
    range, then after running the lowered `MULX` block the machine state matches
    the source post-state `mulxDenote m rs`: `ρ lo` holds the low word and `ρ hi`
    the high word of the full product, both via `wumul_lo`/`wumul_hi`. -/
theorem lowerMulx_denote (ρ : RegMap) (m : MulxSrc) (rs : RustState) (js : JState 64)
    (hρ : Function.Injective ρ)
    (hhilo : m.hi ≠ m.lo)
    (ha : rs.rsScalar m.a < 2 ^ 64) (hb : rs.rsScalar m.b < 2 ^ 64)
    (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (mulxDenote m rs) (runBlock js (lowerMulx ρ m)) := by
  intro v
  -- Run the single MULX: it sets ρlo := lo then ρhi := hi.
  have hrun : runBlock js (lowerMulx ρ m)
      = (js.setReg (ρ m.lo) (wumul (js.get (ρ m.a)) (js.get (ρ m.b))).2).setReg
          (ρ m.hi) (wumul (js.get (ρ m.a)) (js.get (ρ m.b))).1 := by
    simp [lowerMulx, runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi,
          JOperand.eval]
  rw [hrun]
  -- The operand reads, transported across StateMatch and the wumul identity.
  have hav : js.get (ρ m.a) = BitVec.ofNat 64 (rs.rsScalar m.a) := hmatch m.a
  have hbv : js.get (ρ m.b) = BitVec.ofNat 64 (rs.rsScalar m.b) := hmatch m.b
  set prod := rs.rsScalar m.a * rs.rsScalar m.b with hprod
  have hlo : (wumul (js.get (ρ m.a)) (js.get (ρ m.b))).2
      = BitVec.ofNat 64 (prod % 2 ^ 64) := by
    rw [hav, hbv, hprod]; exact wumul_lo _ _ ha hb
  have hhi : (wumul (js.get (ρ m.a)) (js.get (ρ m.b))).1
      = BitVec.ofNat 64 (prod / 2 ^ 64) := by
    rw [hav, hbv, hprod]; exact wumul_hi _ _ ha hb
  rw [hlo, hhi]
  -- Now case on which slot `v` we are reading.
  by_cases hvhi : v = m.hi
  · -- v = hi: the second write lands here.
    subst hvhi
    rw [JState.get_setReg_same]
    simp [mulxDenote, rsSetScalar, ← hprod]
  · by_cases hvlo : v = m.lo
    · -- v = lo: the first write, undisturbed by the hi write (ρ lo ≠ ρ hi).
      subst hvlo
      have hne : ρ m.lo ≠ ρ m.hi := fun h => hhilo (hρ h).symm
      rw [JState.get_setReg_other _ _ _ _ hne, JState.get_setReg_same]
      simp [mulxDenote, rsSetScalar, ← hprod]
      rw [if_neg hvhi]
    · -- v ∉ {hi, lo}: untouched on both sides.
      have hnehi : ρ v ≠ ρ m.hi := fun h => hvhi (hρ h)
      have hnelo : ρ v ≠ ρ m.lo := fun h => hvlo (hρ h)
      rw [JState.get_setReg_other _ _ _ _ hnehi,
          JState.get_setReg_other _ _ _ _ hnelo]
      simp [mulxDenote, rsSetScalar, hvhi, hvlo]
      exact hmatch v

/-! ## 6. Worked bignum kernel: a single `1×1 → 2` widening multiply

`widenMulKernel` is the atom of every schoolbook multiply: one `MULX` forming the
full 128-bit product of two 64-bit words, split into `(hi, lo)`.  We instantiate
the full chain — functional correctness (both outputs), constant-time, and a
one-vector value KAT — on the concrete register allocation `idRho` (identity on
the slot names, trivially injective). -/

/-- The widening-multiply source atom: `(hi, lo) := a · b`. -/
def widenMul : MulxSrc := { hi := "hi", lo := "lo", a := "a", b := "b" }

/-- A concrete (injective) register allocation: the identity on slot names. -/
def idRho : RegMap := id

theorem idRho_injective : Function.Injective idRho := fun _ _ h => h

/-- **The kernel: a single machine `MULX`.**  The lowering of `widenMul` under the
    identity allocation. -/
def widenMulKernel : List (JInstr 64) := lowerMulx idRho widenMul

/-- **Constant-time, kernel.**  The widening-multiply kernel leaks nothing about
    its operands: same leakage trace from any two states. -/
theorem widenMulKernel_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ widenMulKernel = blockLeak s₂ widenMulKernel :=
  lowerMulx_constant_time idRho widenMul s₁ s₂

/-- **Functional correctness, kernel.**  For any `u64`-bounded source operands,
    the kernel run matches the source widening multiply (both outputs). -/
theorem widenMulKernel_denote (rs : RustState) (js : JState 64)
    (ha : rs.rsScalar "a" < 2 ^ 64) (hb : rs.rsScalar "b" < 2 ^ 64)
    (hmatch : StateMatch idRho rs js) :
    StateMatch idRho (mulxDenote widenMul rs) (runBlock js widenMulKernel) :=
  lowerMulx_denote idRho widenMul rs js idRho_injective (by decide) ha hb hmatch

/-- A concrete initial machine state holding `a`/`b` in the source registers. -/
def kernelState (a b : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "a" then a else if r = "b" then b else 0 }

/-- The `(lo, hi)` pair the kernel writes, read back from the final machine state. -/
def kernelOut (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := runBlock (kernelState a b) widenMulKernel
  (s.get "lo", s.get "hi")

/-- **Value KAT (one vector).**  `a = b = 2⁶⁴−1`: the full product is
    `(2⁶⁴−1)² = 2¹²⁸ − 2⁶⁵ + 1`, whose low word is `1` and high word is
    `2⁶⁴ − 2`.  This is the boundary case of the widening multiply (largest
    operands, both output words exercised), checked against the concrete machine
    run on a single test input. -/
theorem widenMulKernel_kat :
    kernelOut 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
      = (0x1, 0xFFFFFFFFFFFFFFFE) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
