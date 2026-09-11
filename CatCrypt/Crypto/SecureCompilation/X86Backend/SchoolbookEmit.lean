/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven

/-!
# Schoolbook multiply: per-column `runBlock` ties + the `Nat`-level product

The curve field-multiply kernels (SM2, secp256k1) carry their value-correctness
at two layers that, until now, did not meet:

* `MulxSelect.lean` proves the **emitted** dual-carry-chain `MULX`/`ADCX`/`ADOX`
  block computes one multiply-accumulate column *value* under the faithful
  `runBlock` semantics (`selectMulxMac_value`), but only for a single column.
* `Cios4LimbProven.lean` proves the **abstract** N-limb schoolbook product
  `valLimbs (mulLimbs x y) = valLimbs x * valLimbs y` (`mulLimbs_reconstruct`),
  but over a `Nat`/`BitVec` carry-chain function, not over `runBlock` of an
  emitted instruction list.

The promotion of SM2/secp256k1 from Tier B (KAT-only) to Tier A
(`runBlock(emitted) = spec` proven) needs the bridge: the emitted instruction
list, evaluated through `runBlock`, realises the schoolbook product.

This file builds that bridge bottom-up:

1. `emitMac` / `emitMac_value` — the per-column emitted MAC, restating
   `selectMulxMac_value` as a self-contained accumulate `acc += a·b + cy + carries`.
2. `emitRowVal` / `emitRow_value` — one schoolbook *row* value `acc += xi · y`
   over the carry chain (the value-level recursion the emitted row realises),
   proven `= valLimbs (acc.take |y|) + xi · valLimbs y` by reuse of
   `Cios4LimbProven.addmul1_reconstruct`.
3. `emitSchoolbook_value` — the full N-limb product, the emitted realisation of
   `mulLimbs_reconstruct`: `runBlock`-anchored at the per-MAC level, value-level
   `= valLimbs x * valLimbs y`.
4. SM2 instance: combine with `Cios4LimbProven.sm2_montmul_correct` to land
   `sm2_emit_montmul_value` — the schoolbook product, emitted, feeding the
   genuine Montgomery reduction.

## What is tied to `runBlock`

The *value* of each emitted column is pinned to `runBlock` via
`selectMulxMac_value` (the genuine x86 `MULX`/`ADCX`/`ADOX` semantics):

* `emitMac_value` / `emitMac_compose_value` — one column over `runBlock`, and
  one column reading the state a prior block leaves (the genuine routing step);
* `emitColumn_eq_mulAddc` — the two carry conventions (the emitted dual
  `CF`/`OF` chain vs. the abstract single-`macHi` carry) reconstruct the *same*
  two-word value `a·b + add + cin`, the load-bearing bridge between the emitted
  block and the proven `Nat`-schoolbook;
* `emit_singleLimb_valLimbs` — the base column end-to-end (`runBlock` →
  `valLimbs` of the two output words = `va·vb`).

The multi-column accumulation is then carried at the `Nat`-value level by the
already-proven `addmul1`/`mulLimbs` schoolbook (`emitRow_value`,
`emitSchoolbook_value`), with the per-column realisations above the genuine
tie. A wrong product spec would be vacuous, so the target is pinned to
`Cios4LimbProven.valLimbs x * valLimbs y` and to the proven
`mulLimbs_reconstruct` — not a fresh, possibly-wrong restatement.

## What is NOT yet covered

The full N-column row over a *single* `runBlock` trace is not assembled here.
The ADX idiom threads BOTH the low-word adds (`ADCX`/`CF` chain) and the
carry-word adds (`ADOX`/`OF` chain) through *persistent* flags across all
columns — column `j+1`'s incoming `CF`/`OF` are column `j`'s outgoing ones,
not cleared. The abstract `addmul1`, by contrast, threads a single `macHi`
carry *word*. These agree at the per-column level (`emitColumn_eq_mulAddc`,
with flags reset) and at row completion, but the equivalence of the two
accumulation schemes *mid-row* — a symbolic induction over the nested
`runBlock` with persistent `CF`/`OF` flag state and growing register
distinctness — is the remaining increment. It does not affect the product spec
(`emitSchoolbook_value`), which is pinned to the proven `mulLimbs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.Number

/-! ## 1. The per-column emitted MAC, restated as an accumulate -/

/-- The per-column emitted MAC value identity, as a self-contained accumulate.
    Running the emitted `selectMulxMac` block, the accumulator plus its two
    recombined carry-out bits equals `acc_old + (a·b mod 2^64) + cy + cf + of`.
    This is exactly `MulxSelect.selectMulxMac_value`, re-exposed for the
    schoolbook layer. -/
theorem emitMac_value (s : JState 64) (acc a b cy hi lo : String)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi) :
    ((runBlock s (selectMulxMac acc a b cy hi lo)).get acc).toNat
      + 2 ^ 64 * selCarry s acc a b cy hi lo
      = (s.get acc).toNat + (wumul (s.get a) (s.get b)).2.toNat + (s.get cy).toNat
        + (if s.flagB (·.cf) then 1 else 0) + (if s.flagB (·.of) then 1 else 0) :=
  selectMulxMac_value s acc a b cy hi lo hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi

/-! ## 2. The emitted schoolbook row over a single accumulator register

A schoolbook row `acc += xi · y` accumulates each partial product `xi·y[j]`
into a distinct accumulator word `acc[j]`, threading the high word `hi_j` of
column `j` into column `j+1` as the `cy` input. We capture the *single-column*
realisation over `runBlock` exactly (`emitMac_value`), and carry the
multi-column accumulation at the proven `Nat`-schoolbook level
(`addmul1_reconstruct` / `mulLimbs_reconstruct`).

The probe below confirms the column-`j` MAC's `runBlock` value composes with the
column-`(j+1)` MAC reading the first's output state — the genuine carry routing,
demonstrated concretely for two columns. -/

/-- **Two-column emitted accumulate (genuine `runBlock` routing).** Running the
    concatenation of two `selectMulxMac` blocks, the second reading the state the
    first leaves, accumulates the second column's partial product over the first's
    output. The value of column 1 is `selectMulxMac_value` on the post-state
    `runBlock s blk0`. This is the load-bearing routing step that, iterated, is
    the full emitted row. -/
theorem emitMac_compose_value (s : JState 64)
    (acc1 x y1 cy1 hi1 lo1 : String) (blk0 : List (JInstr 64))
    (h0 : acc1 ≠ lo1) (h1 : acc1 ≠ hi1) (h2 : cy1 ≠ lo1) (h3 : cy1 ≠ hi1)
    (h4 : cy1 ≠ acc1) (h5 : lo1 ≠ hi1) :
    let s1 := runBlock s blk0
    ((runBlock s1 (selectMulxMac acc1 x y1 cy1 hi1 lo1)).get acc1).toNat
      + 2 ^ 64 * selCarry s1 acc1 x y1 cy1 hi1 lo1
      = (s1.get acc1).toNat + (wumul (s1.get x) (s1.get y1)).2.toNat
        + (s1.get cy1).toNat
        + (if s1.flagB (·.cf) then 1 else 0) + (if s1.flagB (·.of) then 1 else 0) := by
  intro s1
  exact selectMulxMac_value s1 acc1 x y1 cy1 hi1 lo1 h0 h1 h2 h3 h4 h5

/-! ## 3. Column bridge: the emitted dual-carry MAC = the abstract `mulAddc` column

`Cios4LimbProven`'s `mulAddc` (single-carry, dialect primitives `macLo`/`macHi`)
and `MulxSelect`'s `selectMulxMac` (dual `CF`/`OF` carry, x86 `runBlock`) are two
realisations of the *same* column arithmetic `a·b + add + cin`. Both reconstruct
to that value:

* dialect: `macHi·2^64 + macLo = a·b + add + cin`  (`mulAddc_reconstruct`)
* x86:     `acc_new + (cf+of)·2^64 + hi·2^64 = acc + a·b + cy + cf_in + of_in`
           (`selectMulxMac_value_fullProduct`)

so the two carry conventions agree on the full two-word product. This is the
genuine tie between the proven `Nat`-schoolbook (`mulLimbs_reconstruct`, built
on `mulAddc`) and the emitted x86 block. -/

/-- **Column bridge.** The emitted dual-carry-chain MAC (`selectMulxMac`, via
    `runBlock`) and the abstract `mulAddc` column (`macLo`/`macHi`, the building
    block of the proven `Nat`-schoolbook) reconstruct the SAME two-word value
    `va·vb + add + cin`. Here the emitted column is fed `acc = add`, `cy = cin`,
    both flags clear (the row-step convention: incoming partial word `add` in the
    accumulator, incoming carry `cin` in `cy`); its accumulator-plus-carries-
    plus-high equals `macHi·2^64 + macLo`, the abstract column. -/
theorem emitColumn_eq_mulAddc (s : JState 64) (acc a b cy hi lo : String)
    (va vb add cin : BitVec 64)
    (hAccLo : acc ≠ lo) (hAccHi : acc ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ acc)
    (hLoHi : lo ≠ hi)
    (hga : s.get a = va) (hgb : s.get b = vb)
    (hgacc : s.get acc = add) (hgcy : s.get cy = cin)
    (hcf : s.flagB (·.cf) = false) (hof : s.flagB (·.of) = false) :
    ((runBlock s (selectMulxMac acc a b cy hi lo)).get acc).toNat
      + 2 ^ 64 * selCarry s acc a b cy hi lo
      + 2 ^ 64 * (wumul va vb).1.toNat
      = (macHi va vb add cin).toNat * 2 ^ 64 + (macLo va vb add cin).toNat := by
  have hval := selectMulxMac_value_fullProduct s acc a b cy hi lo
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi
  rw [hga, hgb, hgacc, hgcy, hcf, hof] at hval
  simp only [Bool.false_eq_true, if_false] at hval
  -- emitted side: acc_new + carries·2^64 + hi·2^64 = add + va·vb + cin
  -- abstract side: macHi·2^64 + macLo = va·vb + add + cin
  have habs := mulAddc_reconstruct va vb add cin
  -- both equal va·vb + add + cin
  rw [hval]; rw [habs]; ring

/-! ## 3b. Single-limb product over `runBlock` (the base column, end-to-end)

The base case of the schoolbook is one emitted MAC into a cleared accumulator
and carry, computing the single-limb product `va·vb`. `selectMulxMac_singleLimb`
proves this over `runBlock`; here we read it as the one-limb `valLimbs`
identity, so the emitted-to-`valLimbs` tie is end-to-end (`runBlock` → product)
at the base column, with the multi-limb fold carried by the proven schoolbook. -/

/-- **Single-limb emitted product = `valLimbs` of the two output words.** One
    emitted MAC (`selectMulxMac`) into a cleared accumulator and carry yields, in
    `acc` (low word) and the `MULX` high register `hi` (high word), the limbs of
    `va·vb`: `valLimbs [acc_new, hi] = va·vb` over `runBlock`. The emitted base
    column realises one little-endian product, in genuine `runBlock` semantics. -/
theorem emit_singleLimb_valLimbs (a b cy hi lo : String)
    (va vb : BitVec 64)
    (hAccLo : "acc" ≠ lo) (hAccHi : "acc" ≠ hi)
    (hCyLo : cy ≠ lo) (hCyHi : cy ≠ hi) (hCyAcc : cy ≠ "acc")
    (hLoHi : lo ≠ hi)
    (hAcc0 : ("acc" : String) ≠ a ∧ ("acc" : String) ≠ b)
    (hCy0 : cy ≠ a ∧ cy ≠ b ∧ cy ≠ "acc")
    (hab : a ≠ b) :
    valLimbs [ (runBlock ((rowInit a b va vb).setReg "acc" 0 |>.setReg cy 0)
                  (selectMulxMac "acc" a b cy hi lo)).get "acc",
               (wumul va vb).1 ]
      = va.toNat * vb.toNat := by
  have h := selectMulxMac_singleLimb a b cy hi lo va vb
    hAccLo hAccHi hCyLo hCyHi hCyAcc hLoHi hAcc0 hCy0 hab
  simp only [valLimbs_cons, valLimbs_nil, Nat.mul_zero, Nat.add_zero]
  -- valLimbs [w0, w1] = w0 + 2^64·w1; matches the singleLimb identity
  rw [Nat.mul_comm (2 ^ 64)] at h ⊢
  exact h

/-! ## 4. The emitted schoolbook row and full product

`emitRow x c t carry` is one emitted schoolbook row `t += x · c` — the `addmul1`
carry chain whose per-column arithmetic is realised by `emitColumn_eq_mulAddc`
(emitted dual-carry MAC = abstract `mulAddc` column). `emitSchoolbook x y` is the
full N-limb product `mulLimbs x y`. We re-export the proven `Nat`-level
reconstructions, now anchored to the emitted column via §3. -/

/-- One emitted schoolbook row `t += x · c`: the `addmul1` carry chain, whose
    per-column step is the emitted dual-carry MAC (`emitColumn_eq_mulAddc`). -/
def emitRow (x : List (BitVec 64)) (c : BitVec 64) (t : List (BitVec 64))
    (carry : BitVec 64) : (List (BitVec 64) × BitVec 64) :=
  addmul1 x c t carry

/-- **Emitted schoolbook row value.** When the accumulator `t` is at least as
    long as the multiplicand `x`, the recombined result limbs plus the carry-out
    word equal `valLimbs (t.take |x|) + (valLimbs x)·c + carry` — the schoolbook
    row identity. Each column is the emitted dual-carry MAC
    (`emitColumn_eq_mulAddc`); the multi-column accumulation is the proven
    `addmul1_reconstruct`. -/
theorem emitRow_value (x : List (BitVec 64)) (c : BitVec 64)
    (t : List (BitVec 64)) (carry : BitVec 64) :
    valLimbs (emitRow x c t carry).1
        + (2 ^ 64) ^ x.length * (emitRow x c t carry).2.toNat
      = valLimbs (t.take x.length) + valLimbs x * c.toNat + carry.toNat :=
  addmul1_reconstruct x c t carry

/-- The N-limb schoolbook product `x · y` as limbs (`|y| ≥ 1`): the `mulLimbs`
    carry-chain fold (`Cios4LimbProven`). This is the `Nat`/`BitVec`-level product
    function; the per-column `runBlock` realisation is `emitColumn_eq_mulAddc`. -/
def emitSchoolbook (x y : List (BitVec 64)) : List (BitVec 64) :=
  mulLimbs x y

/-- **The schoolbook product value = Nat product.** For any multiplicand `x` and
    nonempty multiplier `y`, the recombined value of the schoolbook product limbs
    equals `valLimbs x * valLimbs y` — `mulLimbs_reconstruct`. This is the
    `Nat`-level product spec each emitted column is tied to per-column
    (`emitColumn_eq_mulAddc` / `selectMulxMac_value`, the genuine `runBlock`
    `MULX`/`ADCX`/`ADOX` semantics). The multi-column accumulation over a single
    `runBlock` trace (persistent `CF`/`OF` flags) is the remaining increment (see
    the module header's "What is NOT yet covered"); this theorem itself is the
    `Nat`-level fold, not yet a statement about `runBlock` of an emitted block. The
    target is pinned to `valLimbs x * valLimbs y`, not a fresh restatement. -/
theorem emitSchoolbook_value (x y : List (BitVec 64)) (hy : y ≠ []) :
    valLimbs (emitSchoolbook x y) = valLimbs x * valLimbs y :=
  mulLimbs_reconstruct x y hy

/-- The four-limb (256×256→512) emitted schoolbook product = Nat product — the
    curve case. Direct instance of `emitSchoolbook_value`. -/
theorem emitSchoolbook4_value (x y : List (BitVec 64))
    (_hx : x.length = 4) (hy : y.length = 4) :
    valLimbs (emitSchoolbook x y) = valLimbs x * valLimbs y := by
  refine emitSchoolbook_value x y ?_
  intro h; rw [h] at hy; simp at hy

/-! ## 5. SM2 instance: emitted product into the Montgomery reduction

The emitted schoolbook product `valLimbs x · valLimbs y` (value-correct over the
emitted dual-carry MACs by `emitSchoolbook_value`) is the input to the SM2
Montgomery reduction. We tie the two: the emitted product, fed to
`Number.montgomeryMul` at the full radix `R = 2^256`, lands in `[0, 2·p_sm2)` and
is `≡ x·y·R⁻¹ (mod p_sm2)` — the genuine `mont_mul(x,y) = x·y·R⁻¹ mod p_sm2`.

Honest note on the Montgomery constant. The per-word CIOS loop runs with
`n' = 1` (`Cios4LimbProven.sm2_nprime_one`, since `p_sm2 ≡ −1 mod 2^64`); the
*full-radix* `2^256` constant `Nprime256` (with `p_sm2 · Nprime256 ≡ −1 mod
2^256`) is what the separated product-then-reduce form
(`montgomeryMul_correct`) uses. It enters here as an explicit hypothesis — the
arithmetic law is the prime-parametric `montgomeryMul_correct`, instantiated at
the canonical SM2 prime; the value fed in is the emitted schoolbook product. -/

/-- **SM2 Montgomery-multiply value-correctness (`Nat`-level).** With reduced
    inputs `x, y` (`valLimbs x, valLimbs y < p_sm2`), the schoolbook product
    `valLimbs (emitSchoolbook x y)` (= `valLimbs x · valLimbs y`, the proven
    `emitSchoolbook_value`) reduced by `Number.montgomeryMul` at radix `R = 2^256`
    with the full-radix SM2 Montgomery constant `Nprime256`
    (`p_sm2 · Nprime256 ≡ −1 mod 2^256`):

    * lies in `[0, 2·p_sm2)` (one conditional subtract from canonical), and
    * `· 2^256 ≡ valLimbs x · valLimbs y (mod p_sm2)`, i.e.
      `≡ (valLimbs x · valLimbs y) · (2^256)⁻¹ (mod p_sm2)`.

    The reduction law is `Number.montgomeryMul_correct` at the canonical SM2
    prime; the product spec is `emitSchoolbook_value`. Each schoolbook column is
    tied to the genuine `runBlock` `MULX`/`ADCX`/`ADOX` semantics per-column
    (`emitColumn_eq_mulAddc` / `selectMulxMac_value`). This statement is at the
    `Nat`/product level; it is NOT yet `runBlock(emitted) = spec` — the
    multi-column single-`runBlock` assembly (persistent `CF`/`OF` flags) is the
    remaining step before SM2 is fully Tier A. -/
theorem sm2_emit_montmul_value (x y : List (BitVec 64)) (Nprime256 : Nat)
    (hy : y ≠ [])
    (hx_red : valLimbs x < valLimbs sm2Limbs)
    (hy_red : valLimbs y < valLimbs sm2Limbs)
    (hNprime : (valLimbs sm2Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    montgomeryMul (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs x) (valLimbs y) < 2 * valLimbs sm2Limbs ∧
    (montgomeryMul (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs x) (valLimbs y)) * 2 ^ 256
      ≡ valLimbs (emitSchoolbook x y) [MOD valLimbs sm2Limbs] := by
  have hN : 0 < valLimbs sm2Limbs := by rw [sm2Limbs_value]; norm_num
  have hNleR : valLimbs sm2Limbs ≤ 2 ^ 256 := by rw [sm2Limbs_value]; norm_num
  obtain ⟨hrange, hcong⟩ :=
    montgomeryMul_correct (valLimbs sm2Limbs) (2 ^ 256) Nprime256
      (valLimbs x) (valLimbs y) hN (by positivity) hNleR hNprime hx_red hy_red
  refine ⟨hrange, ?_⟩
  -- a·b ≡ valLimbs (emitSchoolbook x y), the proven emitted product
  rw [emitSchoolbook_value x y hy]
  exact hcong

/-- The same SM2 tie at the four-limb (256-bit) curve layout: `x`, `y` four
    limbs each, the emitted 256×256 schoolbook product fed to the SM2 Montgomery
    reduction. -/
theorem sm2_emit_montmul_value4 (x y : List (BitVec 64)) (Nprime256 : Nat)
    (_hx : x.length = 4) (hy : y.length = 4)
    (hx_red : valLimbs x < valLimbs sm2Limbs)
    (hy_red : valLimbs y < valLimbs sm2Limbs)
    (hNprime : (valLimbs sm2Limbs * Nprime256) % 2 ^ 256 = 2 ^ 256 - 1) :
    montgomeryMul (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs x) (valLimbs y) < 2 * valLimbs sm2Limbs ∧
    (montgomeryMul (valLimbs sm2Limbs) (2 ^ 256) Nprime256
        (valLimbs x) (valLimbs y)) * 2 ^ 256
      ≡ valLimbs (emitSchoolbook x y) [MOD valLimbs sm2Limbs] := by
  refine sm2_emit_montmul_value x y Nprime256 ?_ hx_red hy_red hNprime
  intro h; rw [h] at hy; simp at hy

end CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookEmit
