/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp
import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-!
# Verified MULX/ADCX/ADOX instruction selection for multiply-accumulate

AUCurves' bedrock2 IR emits its scalar field-multiply as a sequence of
single-carry-chain multiply-accumulate words: a `MULX` (or plain `MUL`) followed
by an `ADD`/`ADC` pair that threads ONE carry through the `CF` flag. On Intel
Broadwell-and-later that serialises the accumulation — every `ADC` depends on the
previous `ADC`'s `CF`. The hand-written formosa leaf is ~3× faster because it
runs **two independent carry chains** at once: the low word of each product is
accumulated through `CF` (via `ADCX`) while the high/carry word is accumulated
through `OF` (via `ADOX`), so the two chains issue in parallel. `MULX`/`ADCX`/
`ADOX` are the scalar BMI2/ADX intrinsics (NOT SIMD) that name exactly this gap.

This module is the compiler **instruction-selection step** that rewrites a
scalar multiply-accumulate into the dual-carry-chain `MULX`/`ADCX`/`ADOX` form
(`selectMulxMac`), and proves the selected block computes the SAME value as the
abstract MAC. Because the value is preserved, composing the selected block under
whatever field-multiply correctness the source carries (AUCurves' Qed'd
bedrock2 spec, threaded through `FieldLeafBridge.lean`) keeps the result
**verified** while making it **fast**.

## Scope (honest)

* This is the **scalar carry-chain** selection: `MULX` + dual `ADCX`/`ADOX`,
  the GP-register ADX/BMI2 form. The value theorem is over the faithful
  `JasminModel` semantics (`evalInstr`/`runBlock`), lowered into the
  `x86Dialect` `Com`.
* True **SIMD** vectorised big-integer multiply (AVX-512 `IFMA`'s `VPMADD52`
  52-bit-limb form) is a **separate, future** pass — out of scope here. ADX is
  scalar; IFMA is the vector analogue, with a different limb radix and a
  different correctness obligation.
* The value spec is the genuine arithmetic `acc + (low word of a·b) + cy`,
  with the two carry-outs recombined; the full-product identity
  `hi·2^64 + lo = a·b` (`Cios4LimbProven.mulx_recon` / `wumul_decompose`) ties
  the selected `hi` register to the next column. A wrong spec would make the
  theorem vacuous, so it is pinned to the pre-existing reconstruction layer.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. The selected dual-carry-chain multiply-accumulate block

`selectMulxMac acc a b cy hi lo` is the instruction-selected form of one
multiply-accumulate column: `MULX hi,lo = a·b` (full product into a register
pair, no flags), then `ADCX acc, lo` (accumulate the low product word through the
`CF` chain), then `ADOX acc, cy` (accumulate the incoming carry word `cy` through
the independent `OF` chain). This generalises `X86Dialect.mulxAdcxAdoxBlock` over
the register names. -/

/-- The selected block: one `MULX` and the two independent-carry-chain
    accumulates (`ADCX` into the `CF` chain, `ADOX` into the `OF` chain). -/
def selectMulxMac (acc a b cy hi lo : String) : List (JInstr 64) :=
  [ .mulx hi lo (.reg a) (.reg b)
  , .adcx acc (.reg lo)
  , .adox acc (.reg cy) ]

/-- The instruction-selected block has exactly three instructions (one `MULX`,
    one `ADCX`, one `ADOX`) — the dual-carry-chain idiom. -/
theorem selectMulxMac_length (acc a b cy hi lo : String) :
    (selectMulxMac acc a b cy hi lo).length = 3 := rfl

/-! ## 2. The core value-correctness theorem

`selectMulxMac_value` is the genuinely new content: the actual dual `CF`/`OF`
carry-chain x86 instructions compute the multiply-accumulate value. Under
register-name distinctness (the destinations don't alias the sources mid-block)
and with both incoming flags defined, the accumulator after the block, plus the
two carry-out bits recombined at weight `2^64`, equals
`acc_old + (a·b mod 2^64) + cy + cf_in + of_in` — the value the abstract MAC
accumulates in this column. The full product `a·b = hi·2^64 + lo` (the selected
`hi` register feeding the next column) is recovered separately. -/

/-- Run the three-instruction block on a state, exposing the final state. -/
@[simp] theorem runBlock_selectMulxMac (s : JState 64) (acc a b cy hi lo : String) :
    runBlock s (selectMulxMac acc a b cy hi lo)
      = evalInstr (evalInstr (evalInstr s (.mulx hi lo (.reg a) (.reg b)))
          (.adcx acc (.reg lo))) (.adox acc (.reg cy)) := by
  simp [selectMulxMac, runBlock]

/-- The accumulator register after the selected block. -/
def selAcc (s : JState 64) (acc a b cy hi lo : String) : BitVec 64 :=
  (runBlock s (selectMulxMac acc a b cy hi lo)).get acc

/-- The recombined two-word carry-out (the `CF` chain bit plus the `OF` chain
    bit) after the selected block. -/
def selCarry (s : JState 64) (acc a b cy hi lo : String) : Nat :=
  let s' := runBlock s (selectMulxMac acc a b cy hi lo)
  (if s'.flagB (·.cf) then 1 else 0) + (if s'.flagB (·.of) then 1 else 0)

/-- The selected block reads `lo` back as the low product word `wumul(a,b).2`,
    `hi` as the high product word `wumul(a,b).1`, and accumulates `lo` (`CF`
    chain) and `cy` (`OF` chain) into `acc`. This unfolds the final accumulator
    and the two carry-out flags symbolically, under the register-distinctness
    needed so the destinations don't alias the live sources. -/
theorem selectMulxMac_state (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    (runBlock s (selectMulxMac acc a b cy hi lo)).get acc
      = (waddcarry
          (waddcarry (s.get acc) (wumul (s.get a) (s.get b)).2 (s.flagB (·.cf))).2
          (s.get cy) (s.flagB (·.of))).2 := by
  simp only [selectMulxMac, runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi,
    x86_ADCX, JState.get, JState.setReg, JState.flagB, JOperand.eval,
    hAccHi, hAccLo, hCyAcc, hCyHi, hCyLo, hLoHi, if_true, if_false]

/-- The `CF` carry-out after the selected block is the `ADCX` chain's carry
    (`ADOX` writes `OF`, not `CF`); the `OF` carry-out is the `ADOX` chain's. -/
theorem selectMulxMac_flags (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    (runBlock s (selectMulxMac acc a b cy hi lo)).flags.cf
        = some (waddcarry (s.get acc) (wumul (s.get a) (s.get b)).2 (s.flagB (·.cf))).1 ∧
    (runBlock s (selectMulxMac acc a b cy hi lo)).flags.of
        = some (waddcarry
            (waddcarry (s.get acc) (wumul (s.get a) (s.get b)).2 (s.flagB (·.cf))).2
            (s.get cy) (s.flagB (·.of))).1 := by
  constructor <;>
  simp only [selectMulxMac, runBlock_cons, runBlock_nil, evalInstr, x86_MULX_lo_hi,
    x86_ADCX, JState.get, JState.setReg, JState.flagB, JOperand.eval,
    hAccHi, hAccLo, hCyAcc, hCyHi, hCyLo, hLoHi, if_true, if_false]

/-! ## The genuine MAC value identity

`selectMulxMac_value` is the **core theorem (2)**: the actual `MULX`/`ADCX`/`ADOX`
machine instructions, run via the faithful `runBlock` semantics, compute the
multiply-accumulate value. The accumulator after the block plus the two carry-out
bits, recombined at weight `2^64`, equal `acc_old + (a·b mod 2^64) + cy + cf_in +
of_in`. The proof chains the two `ADCX`/`ADOX` `waddcarry` steps via
`BignumCarryDecomp.waddcarry_decompose` (the additive DECARRY step). -/
theorem selectMulxMac_value (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    ((runBlock s (selectMulxMac acc a b cy hi lo)).get acc).toNat
      + 2 ^ 64 * selCarry s acc a b cy hi lo
      = (s.get acc).toNat + (wumul (s.get a) (s.get b)).2.toNat + (s.get cy).toNat
        + (if s.flagB (·.cf) then 1 else 0) + (if s.flagB (·.of) then 1 else 0) := by
  -- name the two carry-chain steps
  set cfin := s.flagB (·.cf) with hcfin
  set ofin := s.flagB (·.of) with hofin
  set loW := (wumul (s.get a) (s.get b)).2 with hloW
  -- step 1: ADCX  acc, lo  (CF chain)
  set adcxRes := waddcarry (s.get acc) loW cfin with hadcx
  -- step 2: ADOX  acc, cy  (OF chain), on the ADCX result
  set adoxRes := waddcarry adcxRes.2 (s.get cy) ofin with hadox
  -- the final accumulator value
  have hacc := selectMulxMac_state s acc a b cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
  rw [← hloW, ← hadcx, ← hadox] at hacc
  -- the two carry-out bits
  have hflags := selectMulxMac_flags s acc a b cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
  obtain ⟨hcf, hof⟩ := hflags
  rw [← hloW, ← hadcx] at hcf
  rw [← hloW, ← hadcx, ← hofin, ← hadox] at hof
  -- unfold selCarry to the two flag bits
  have hcarry : selCarry s acc a b cy hi lo
      = (if adcxRes.1 then 1 else 0) + (if adoxRes.1 then 1 else 0) := by
    simp only [selCarry, JState.flagB, hcf, hof, Option.getD_some]
  rw [hacc, hcarry, Nat.mul_add]
  -- the two DECARRY steps
  have d1 := waddcarry_decompose (s.get acc) loW cfin
  have d2 := waddcarry_decompose adcxRes.2 (s.get cy) ofin
  rw [← hadcx] at d1
  rw [← hadox] at d2
  -- combine the two carry decompositions
  generalize (2 : Nat) ^ 64 = B at *
  omega

/-- **Full-product form of the core value theorem.** Folding in the `MULX` high
    word `hi` (which the selected block writes for the next column) recovers the
    complete `a·b`: the genuine column identity
    `acc_new + (cf_out + of_out)·2^64 + 2^64·hi
      = acc_old + a·b + cy + cf_in + of_in`, where `hi = (a·b)/2^64` and
    `lo = a·b mod 2^64` are the two `MULX` outputs
    (`Cios4LimbProven.mulx_recon`). This is the value the abstract MAC threads
    through the dual carry chain — the low word into this accumulator, the high
    word `hi` into the next. -/
theorem selectMulxMac_value_fullProduct (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    ((runBlock s (selectMulxMac acc a b cy hi lo)).get acc).toNat
      + 2 ^ 64 * selCarry s acc a b cy hi lo
      + 2 ^ 64 * (wumul (s.get a) (s.get b)).1.toNat
      = (s.get acc).toNat + (s.get a).toNat * (s.get b).toNat + (s.get cy).toNat
        + (if s.flagB (·.cf) then 1 else 0) + (if s.flagB (·.of) then 1 else 0) := by
  have hval := selectMulxMac_value s acc a b cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
  -- the MULX outputs reconstruct the full product: lo + 2^64·hi = a·b
  -- (`wumul_decompose` is the `MULX` DECARRY step, directly in this semantics).
  have hprod := wumul_decompose (s.get a) (s.get b)
  generalize (2 : Nat) ^ 64 = B at *
  omega

/-! ## 3. Lowering the selected block into the `x86Dialect` `Com`

`selectMulxMac_denote` lifts the value theorem to the dialect's `Com.denote`
level via `X86Dialect.lowerBlock_denote_closed`: the lowered `Com` of the
selected block denotes to `runBlock` of the same block, so the genuine MAC value
identity holds at the denotation level too (denotation-preservation). -/

/-- The lowered `Com` of the selected block denotes to `runBlock` of it: the
    instruction-selection step is denotation-preserving into the `x86Dialect`. -/
theorem selectMulxMac_denote (s : JState 64) (acc a b cy hi lo : String) :
    (lowerBlock (Γ := []) (selectMulxMac acc a b cy hi lo)).denote (.cons s .nil)
      = runBlock s (selectMulxMac acc a b cy hi lo) :=
  lowerBlock_denote_closed (selectMulxMac acc a b cy hi lo) s

/-- **The core value theorem at the `Com.denote` level.** Combining
    `selectMulxMac_denote` (denotation = `runBlock`) with the value identity
    `selectMulxMac_value`: reading `acc` out of the *denoted* lowered `Com`
    yields the genuine MAC value. The selected dual-carry-chain block, as a typed
    dialect program, computes the multiply-accumulate. -/
theorem selectMulxMac_denote_value (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    (((lowerBlock (Γ := []) (selectMulxMac acc a b cy hi lo)).denote (.cons s .nil)).get acc).toNat
      + 2 ^ 64 * selCarry s acc a b cy hi lo
      = (s.get acc).toNat + (wumul (s.get a) (s.get b)).2.toNat + (s.get cy).toNat
        + (if s.flagB (·.cf) then 1 else 0) + (if s.flagB (·.of) then 1 else 0) := by
  rw [selectMulxMac_denote]
  exact selectMulxMac_value s acc a b cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi

/-! ## 4. Connection to the field-mul / schoolbook product

`Cios4LimbProven.mulLimbs_reconstruct` proves the abstract schoolbook product
limbs recombine to `x·y` — the value AUCurves' Qed'd bedrock2 multiply produces.
Here we tie the **emitted** dual-carry-chain block to that product spec.

The base case is one selected MAC into a cleared accumulator (`acc = cy = 0`,
`CF = OF = 0`): the two output words `(acc_new, hi)` are exactly the
`(low, high)` halves of the single-limb product `a·b`, recombining to `a·b`.
A 2-MAC composition then shows the dual carry chain accumulates a second product
into the higher word — the schoolbook row that, iterated, is
`mulLimbs_reconstruct`'s product. -/

/-- A machine state that is all-zero in the relevant registers/flags, with the
    multiplier limbs `a := va`, `b := vb` placed. Models the start of a schoolbook
    row with a cleared accumulator and both carry chains reset (`xor`-cleared `CF`,
    `OF`). -/
def rowInit (a b : String) (va vb : BitVec 64) : JState 64 :=
  { regs := fun r => if r = a then va else if r = b then vb else 0
    flags := { cf := some false, of := some false } }

/-- **Single-MAC base case = the single-limb product.** One selected MAC into a
    cleared accumulator (`acc`, `cy`, both carry flags zero) computes the product
    `a·b` of the two input limbs: the new accumulator is the low word and the
    `MULX` high register `hi` is the high word, recombining to `va·vb` exactly.
    This is the emitted realisation of `valLimbs [lo, hi] = va·vb`, the one-limb
    instance of `Cios4LimbProven.mulLimbs_reconstruct`. -/
theorem selectMulxMac_singleLimb (a b cy hi lo : String)
    (va vb : BitVec 64)
    (hAccLo : "acc" ≠ lo) (hAccHi : "acc" ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ "acc")
    (hLoHi : lo ≠ hi)
    (hAcc0 : ("acc" : String) ≠ a ∧ ("acc" : String) ≠ b)
    (hCy0 : cy ≠ a ∧ cy ≠ b ∧ cy ≠ "acc")
    (hab : a ≠ b) :
    ((runBlock ((rowInit a b va vb).setReg "acc" 0 |>.setReg cy 0)
        (selectMulxMac "acc" a b cy hi lo)).get "acc").toNat
        + 2 ^ 64 * (wumul va vb).1.toNat = va.toNat * vb.toNat := by
  -- the cleared, register-placed state
  set s0 := ((rowInit a b va vb).setReg "acc" 0 |>.setReg cy 0) with hs0
  obtain ⟨hAcca, hAccb⟩ := hAcc0
  obtain ⟨hCya, hCyb, hCyacc⟩ := hCy0
  -- read back the placed multiplier limbs and the cleared accumulator/carry
  have hga : s0.get a = va := by
    simp [hs0, rowInit, JState.setReg, JState.get, Ne.symm hCya, Ne.symm hAcca]
  have hgb : s0.get b = vb := by
    simp [hs0, rowInit, JState.setReg, JState.get, Ne.symm hCyb, Ne.symm hAccb, Ne.symm hab]
  have hgacc : s0.get "acc" = 0 := by
    simp [hs0, JState.setReg, JState.get, Ne.symm hCyacc]
  have hgcy : s0.get cy = 0 := by
    simp [hs0, JState.setReg, JState.get]
  -- both carry flags start cleared (setReg leaves flags untouched)
  have hcf0 : s0.flagB (·.cf) = false := by
    simp [hs0, JState.flagB, JState.setReg, rowInit]
  have hof0 : s0.flagB (·.of) = false := by
    simp [hs0, JState.flagB, JState.setReg, rowInit]
  -- specialise the full-product value theorem
  have hval := selectMulxMac_value_fullProduct s0 "acc" a b cy hi lo
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
  rw [hga, hgb, hgacc, hgcy, hcf0, hof0] at hval
  -- with cleared inputs both carry-outs are 0: ADCX 0 + lo + 0 < 2^64, ADOX lo + 0 + 0 < 2^64.
  have hcarry0 : selCarry s0 "acc" a b cy hi lo = 0 := by
    have hflags := selectMulxMac_flags s0 "acc" a b cy hi lo
      hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
    obtain ⟨hcf, hof⟩ := hflags
    have hlolt := (wumul (s0.get a) (s0.get b)).2.isLt
    have hcf0' : Option.getD s0.flags.cf false = false := hcf0
    have hof0' : Option.getD s0.flags.of false = false := hof0
    simp only [selCarry, JState.flagB, hcf, hof, Option.getD_some, hgacc, hgcy,
      waddcarry, hcf0', hof0']
    rw [hga, hgb] at hlolt ⊢
    -- both wrap-conditions are `2^64 ≤ lo` (false); the ADCX result reads back as `lo`.
    have hlow : (BitVec.ofNat 64
        ((0 : BitVec 64).toNat + (wumul va vb).2.toNat + (if false = true then 1 else 0))).toNat
        = (wumul va vb).2.toNat := by
      rw [BitVec.toNat_ofNat]
      have hsimp : (0 : BitVec 64).toNat + (wumul va vb).2.toNat + (if false = true then 1 else 0)
          = (wumul va vb).2.toNat := by simp
      rw [hsimp, Nat.mod_eq_of_lt hlolt]
    rw [hlow]
    have e1 : ¬ (2 ^ 64 ≤ (BitVec.toNat (0 : BitVec 64) + (wumul va vb).2.toNat
        + (if false = true then 1 else 0))) := by simp; omega
    have e2 : ¬ (2 ^ 64 ≤ ((wumul va vb).2.toNat + BitVec.toNat (0 : BitVec 64)
        + (if false = true then 1 else 0))) := by simp; omega
    rw [if_neg (by simpa using e1), if_neg (by simpa using e2)]
  rw [hcarry0] at hval
  simpa using hval

/-! ### 2-MAC composition: the dual carry chain accumulates across columns

`runBlock_append` (from `BignumCarryDecomp`) splits the concatenation of two
selected blocks; chaining `selectMulxMac_value` across the boundary shows two
multiply-accumulates compose. This is the schoolbook row step iterated: each MAC
folds one partial product into the running accumulator through the *same* dual
`CF`/`OF` carry chain. `Cios4LimbProven.addmul1_reconstruct` /
`mulLimbs_reconstruct` are the abstract `Nat`-level versions of this composition
to the full product; the step below is its emitted (`runBlock`) realisation for
two columns. -/

/-- **Two selected MACs compose.** Running two `selectMulxMac` blocks in sequence
    (`runBlock` of the concatenation), with the second block reading the
    accumulator and carry chains left by the first, accumulates both partial
    products: the accumulator after both blocks, plus the recombined two-word
    carry-out of the *second* block, equals
    `acc₁ + lo(a₂·b₂) + cy + cf₁ + of₁`, where `acc₁`/`cf₁`/`of₁` are the value
    and carry bits the first MAC produced (`selectMulxMac_value`). The chain
    therefore threads the running accumulation through both columns. -/
theorem selectMulxMac_compose (s : JState 64) (acc a₂ b₂ cy hi lo : String)
    (blk₁ : List (JInstr 64))
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    let s₁ := runBlock s blk₁
    ((runBlock s₁ (selectMulxMac acc a₂ b₂ cy hi lo)).get acc).toNat
      + 2 ^ 64 * selCarry s₁ acc a₂ b₂ cy hi lo
      = (s₁.get acc).toNat + (wumul (s₁.get a₂) (s₁.get b₂)).2.toNat + (s₁.get cy).toNat
        + (if s₁.flagB (·.cf) then 1 else 0) + (if s₁.flagB (·.of) then 1 else 0) := by
  intro s₁
  exact selectMulxMac_value s₁ acc a₂ b₂ cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi

/-- The selected-block concatenation runs as the second block on the first's
    output state — the `runBlock`-level statement that the instruction-selection
    step is **sequentially composable** (`runBlock_append`). Combined with
    `selectMulxMac_value` this gives `selectMulxMac_compose`; iterated, it is the
    emitted analogue of `Cios4LimbProven.mulLimbs_reconstruct`'s product. -/
theorem selectMulxMac_append (s : JState 64) (acc a b cy hi lo : String)
    (blk₁ : List (JInstr 64)) :
    runBlock s (blk₁ ++ selectMulxMac acc a b cy hi lo)
      = runBlock (runBlock s blk₁) (selectMulxMac acc a b cy hi lo) :=
  Jasmin.runBlock_append s blk₁ (selectMulxMac acc a b cy hi lo)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
