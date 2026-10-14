/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttAbstractCom
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ReduceZModTie
public import CatCrypt.Crypto.Number.MontgomeryReduction

/-!
# Abstract ML-KEM 3329 Montgomery REDC chain on the unified `Com jasminDialect` (model-free)

`MlkemNttAbstractCom.lean` (the pilot) re-anchored the FIPS-203 field-domain
butterfly value `t = a + w·b (mod q)` — the *input* to the Montgomery REDC chain —
onto the unified `zmmPackQ` denotation, off the bespoke `runZBlock` machine. Its
scope note named the remaining NTT work explicitly: the **Montgomery REDC
chain** (`montDigitBlock` = `vpmuludq`+`vpandq`, `montFoldBlock` =
`vpmuludq`+`vpaddq`+`vpsrlq`, `csubBlock`), whose unified `Com` migration this
module supplies.

This module closes that remaining lane: it re-expresses the two REDC sub-blocks as
straight-line `Com jasminDialect` programs over the packed `zmmPackQ` 8×u64
denotation, and re-proves — on that denotation, with **no `Avx512Model`/`runZBlock`
in the import set** — the two central identities the bespoke realization web
proved over `runZBlock`:

* `montFoldVal_lane_toNat` — the composed REDC output lane equals the value-level
  `Number.montgomeryReduce N R N' t`, and
* the `csubLane_zmod` capping `(csub output : ZMod N)·R = (t : ZMod N)`,

now over the verified `Com jasminDialect` `zmmPackQ` denotation.

## The pattern (established by the pilot)

`zmmPackQ_lane` + `JasminBinOp.applyLane` bridge any packed `Com` denotation to the
bespoke scalar lane math: lane `k` of `zmmPackQ bop a b` is
`bop.applyLane (zmmLane a k) (zmmLane b k)`, and `JasminBinOp.applyLane` unfolds `.mul` to
`a * b`, `.and` to `a &&& b`, `.add` to `a + b`, `.shr` to `a >>> b.toNat`. So the
unified packed REDC lane is **definitionally** the bespoke `BitVec 64` lane
expression — *except* that the unified `.mul` is the FULL 64-bit product `a * b`,
whereas the bespoke `vpmuludq` masks to 32 bits. On the ML-KEM 3329 operand range
(`< 2³²`) these coincide: `laneMuludq_exact` (reused, model-free) proves
`laneMuludq a b = a * b` there. So the unified `zmmPackQ .mul` is *already* the
exact Montgomery product on the 3329 range — the masking the bespoke op carried is
the identity, and the FULL multiply is what we want.

The model-free number theory — `Number.montgomeryReduce_correct`,
`ReduceZModTie.csubLane_zmod`/`csubLane_lt`, `laneMuludq_exact` — transfers
**UNCHANGED** (it is `BitVec 64`/`Nat`/`ZMod` level, with no machine in sight).

## The moot-vs-central split

The model-free abstract tie is the only content this module retains: the REDC
number theory (`montgomeryReduce`, `montgomeryReduce_correct` — `·R ≡ t (mod N)`)
from `Crypto.Number`, the csub lane facts (`csubLane`, `csubLane_zmod` — csub
preserves the residue, `csubLane_lt` — canonicality) from the model-free
`ReduceZModTie`, and `laneMuludq_exact` (the 32-bit masking is the identity
on range) from the pilot. All `BitVec`/`Nat`/`ZMod` level, imported and reused
here unchanged. The `runZBlock`-wrapper plumbing of the bespoke realization web —
which proved the `ZInstr`/`runZBlock` machine writes the spec into `"zr"` — is
the SIMD-model machinery this module replaces with the verified `Com
jasminDialect` `zmmPackQ` denotation; it is **not** imported here. The Montgomery
radix constants `montR`/`montLogR`/`montMaskR` (§0) are defined locally as the
model-free numeric values, off the realization web.

## What is re-anchored (over the unified denotation, no `runZBlock`)

* `montDigitCom_lane` / `montFoldCom_lane` — lane `k` of the unified REDC Com
  denotations is the bespoke `BitVec 64` REDC lane expression (pure, via
  `zmmPackQ_lane`).
* `montFoldCom_lane_toNat` — **the central REDC identity, re-anchored.** Under
  the ML-KEM 3329 operand bounds, the unified fold-Com output lane `k` has `toNat`
  exactly `Number.montgomeryReduce N R N' t`. The two multiplies are the unified
  `zmmPackQ .mul` (full product), exact on range by `laneMuludq_exact`.
* `montRedcCom_zmod` — **the payoff, re-anchored.** Under the ML-KEM 3329
  Montgomery preconditions, the csub of the unified REDC output lane, cast to
  `ZMod N` and multiplied by `R`, equals the field-domain butterfly value `t`.
  Equivalently the lane is the Montgomery form `t·R⁻¹ (mod N)` — one REDC, the
  Montgomery domain, not the plain residue (the scope inherited from the
  bespoke web).
* `montRedcCom_lt` — the canonicality companion: the csub output lane is `< N`.

No `runZBlock` / `ZInstr` / `ZState` / `jasminc` in any theorem's `#print axioms`:
the tie is between the verified `Com jasminDialect` `zmmPackQ` denotation and the
abstract `ZMod N` / `montgomeryReduce` Montgomery property.

## References
* FIPS 203 — ML-KEM (the NTT, §4.3); the Montgomery REDC of the butterfly value.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.MlkemMontRedcAbstractCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemMontRedcAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom
open CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttAbstractCom
open CatCrypt.Crypto.SecureCompilation.X86Backend.ReduceZModTie
  (csubLane csubLane_zmod csubLane_lt)
open CatCrypt.Crypto.Number (montgomeryReduce montgomeryReduce_correct)

/-! ## 0. The ML-KEM Montgomery radix constants (model-free)

`R = 2^16` (the ML-KEM Montgomery radix), `log₂R = 16`, and the radix mask
`R − 1 = 0xffff`. These are pure numeric constants — defined locally so this
module imports no `Avx512Model`/realization web. (The bespoke
`MontReducedButterflyRealization` carries the same three constants for its
`runZBlock` plumbing; here they are the model-free values the unified `Com`
denotation reduces against.) -/

/-- The Montgomery REDC radix `R = 2^16` for ML-KEM. -/
def montR : Nat := 2 ^ 16

/-- `log₂ R = 16`: the right-shift amount that divides by the radix. -/
def montLogR : Nat := 16

/-- The radix mask `R − 1 = 0xffff` as a `BitVec 64` lane constant: `& maskR`
    realizes `mod R`. -/
def montMaskR : BitVec 64 := 0xffff

/-! ## 1. The unified REDC sub-blocks as `Com jasminDialect` programs

`R = 2^16` (the ML-KEM Montgomery radix). The REDC of the butterfly value `t` (a
`reg 512` ZMM) is two straight-line `Com`s over `zmmPackQ`:

* `montDigitCom` — `m = (t ⊗ np) ⊓ mask`  (`vpackZMM .mul`, `vpackZMM .and`):
  the Montgomery digit `m = (t·N') mod R` (mask broadcasts `R−1`).
* `montFoldCom` — `u = (t ⊕ (m ⊗ nn)) ≫ sh`  (`vpackZMM .mul`, `vpackZMM .add`,
  `vpackZMM .shr`): the high-fold `u = (t + m·N) >>> log₂R` (shift register `sh`
  broadcasts `log₂R = 16`).

All three ops are existing `vpackZMM` arms — no new `JasminOp`/`SimdOp` constructor.
(`vpsrlq`-by-immediate is realized as `zmmPackQ .shr` against a broadcast shift
register, the same `JasminBinOp.shr = a >>> b.toNat` the dialect already carries.) -/

/-- The digit-Com input context `[t, np, mask]` (each `reg 512`): the butterfly
    value `t`, the Montgomery constant `N'` (broadcast in `np`), the radix mask
    `R−1` (broadcast in `mask`). -/
abbrev digitCtx : Ctxt jasminDialect := [r512, r512, r512]

/-- The Montgomery digit Com `m = (t ⊗ np) ⊓ mask`:
    `prod := vpackZMM mul t np`, then `m := vpackZMM and prod mask`. The
    dialect-native equivalent of the bespoke `montDigitBlock`
    (`vpmuludq`/`vpandq`). -/
def montDigitCom : Com jasminDialect digitCtx r512 :=
  -- prod := t ⊗ np   (t = .here, np = .there .here)
  .var (.mk (.vpackZMM .mul) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- m := prod ⊓ mask   (prod = .here, mask = .there (.there (.there .here)))
    (.var (.mk (.vpackZMM .and) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      (.ret .here))

/-- The fold-Com input context `[t, m, nn, sh]` (each `reg 512`): the butterfly
    value `t`, the Montgomery digit `m`, the modulus `N` (broadcast in `nn`), the
    shift count `log₂R` (broadcast in `sh`). -/
abbrev foldCtx : Ctxt jasminDialect := [r512, r512, r512, r512]

/-- The Montgomery high-fold Com `u = (t ⊕ (m ⊗ nn)) ≫ sh`:
    `mn := vpackZMM mul m nn`, `sum := vpackZMM add t mn`, `u := vpackZMM shr sum sh`.
    The dialect-native equivalent of the bespoke `montFoldBlock`
    (`vpmuludq`/`vpaddq`/`vpsrlq`). The `vpsrlq`-by-immediate is `zmmPackQ .shr`
    against the broadcast shift register `sh`. -/
def montFoldCom : Com jasminDialect foldCtx r512 :=
  -- mn := m ⊗ nn   (m = .there .here, nn = .there (.there .here))
  .var (.mk (.vpackZMM .mul) rfl
          (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
    -- sum := t ⊕ mn   (t = .there .here under [mn,t,m,nn,sh], mn = .here)
    (.var (.mk (.vpackZMM .add) rfl
            (.cons (.there .here) (.cons .here .nil)))
      -- u := sum ≫ sh   (sum = .here, sh = .there (.there (.there (.there (.there .here)))))
      (.var (.mk (.vpackZMM .shr) rfl
              (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
        (.ret .here)))

/-! ## 2. Denotation pins (`rfl`) and per-lane characterization

Each Com denotes to the verified-dialect packed REDC expression; the proofs are
`rfl` (the straight-line programs unfold through the `vpackZMM` denote arm). Then
`zmmPackQ_lane` (from the pilot) reads each lane as the bespoke `BitVec 64` REDC
lane expression. -/

/-- **Digit-Com denotation pin.** On `⟨t, np, mask⟩`, `montDigitCom` denotes to
    `zmmPackQ .and (zmmPackQ .mul t np) mask` — the packed `(t ⊗ np) ⊓ mask`. -/
theorem montDigitCom_denote (t np mask : BitVec 512) :
    montDigitCom.denote (.cons t (.cons np (.cons mask .nil)))
      = zmmPackQ .and (zmmPackQ .mul t np) mask :=
  rfl

/-- **Fold-Com denotation pin.** On `⟨t, m, nn, sh⟩`, `montFoldCom` denotes to
    `zmmPackQ .shr (zmmPackQ .add t (zmmPackQ .mul m nn)) sh` — the packed
    `(t ⊕ (m ⊗ nn)) ≫ sh`. -/
theorem montFoldCom_denote (t m nn sh : BitVec 512) :
    montFoldCom.denote (.cons t (.cons m (.cons nn (.cons sh .nil))))
      = zmmPackQ .shr (zmmPackQ .add t (zmmPackQ .mul m nn)) sh :=
  rfl

/-- **Digit lane.** Lane `k` of `montDigitCom`'s denotation on `⟨t, np, mask⟩` is
    the bespoke `BitVec 64` digit lane `(t_k * np_k) &&& mask_k` (the unified
    `.mul` is the FULL product; on the ML-KEM range it equals the masked
    `vpmuludq`, by `laneMuludq_exact`). -/
theorem montDigitCom_lane (t np mask : BitVec 512) (k : Fin 8) :
    zmmLane (montDigitCom.denote (.cons t (.cons np (.cons mask .nil)))) k
      = (zmmLane t k * zmmLane np k) &&& zmmLane mask k := by
  rw [montDigitCom_denote, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.applyLane]

/-- **Fold lane.** Lane `k` of `montFoldCom`'s denotation on `⟨t, m, nn, sh⟩` is
    the bespoke `BitVec 64` fold lane `(t_k + m_k * nn_k) >>> (sh_k).toNat`. -/
theorem montFoldCom_lane (t m nn sh : BitVec 512) (k : Fin 8) :
    zmmLane (montFoldCom.denote (.cons t (.cons m (.cons nn (.cons sh .nil))))) k
      = (zmmLane t k + zmmLane m k * zmmLane nn k) >>> (zmmLane sh k).toNat := by
  rw [montFoldCom_denote, zmmPackQ_lane, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.applyLane]

/-! ## 3. The central REDC identity, re-anchored

Lane `k` of the unified fold-Com denotation (digit computed by `montDigitCom`,
then folded by `montFoldCom`) equals the value-level `Number.montgomeryReduce`.
This reuses the EXACT number theory of the bespoke `montFoldVal_lane_toNat`
(`laneMuludq_exact` + `montgomeryReduce` unfold), now over the `zmmPackQ`
denotation. -/

/-- **THE CENTRAL REDC IDENTITY — re-anchored.** Under the ML-KEM 3329 operand
    bounds — the butterfly value `t < 2³²`, the Montgomery constant `N' < 2³²`, the
    modulus `N < 2³²`, the radix mask broadcast `= 0xffff`, the shift broadcast
    `= 16`, and the no-wrap headroom `t + ((t·N') mod R)·N < 2⁶⁴` — the unified
    fold-Com output lane `k` (with the digit lane supplied by `montDigitCom`) has
    `toNat` exactly `montgomeryReduce N R N' t`.

    The two `zmmPackQ .mul`s are the FULL 64-bit product; on the `< 2³²` range each
    equals the bespoke masked `vpmuludq` by `laneMuludq_exact`, so the masking the
    bespoke op carried is invisible. The `& 0xffff` is `mod R`, the `+` does not
    wrap (headroom), the `>>> 16` is `/R`. Lane-for-lane identification of the
    unified packed REDC with the abstract REDC, off the bespoke machine. -/
theorem montFoldCom_lane_toNat
    (t np mask nn shc : BitVec 512) (k : Fin 8) (Nv Np : BitVec 64)
    (hnp : zmmLane np k = Np) (hnn : zmmLane nn k = Nv)
    (hmask : zmmLane mask k = montMaskR) (hsh : (zmmLane shc k).toNat = montLogR)
    (ht32 : (zmmLane t k).toNat < 2 ^ 32)
    (hnp32 : Np.toNat < 2 ^ 32) (hnn32 : Nv.toNat < 2 ^ 32)
    (hwrap : (zmmLane t k).toNat
        + ((zmmLane t k).toNat * Np.toNat % montR) * Nv.toNat < 2 ^ 64) :
    (zmmLane (montFoldCom.denote
        (.cons t (.cons (montDigitCom.denote (.cons t (.cons np (.cons mask .nil))))
          (.cons nn (.cons shc .nil))))) k).toNat
      = montgomeryReduce Nv.toNat montR Np.toNat (zmmLane t k).toNat := by
  -- Abbreviate the butterfly value lane.
  set tl := zmmLane t k with htl
  -- The digit lane m = (t·Np) & maskR.
  have hdig : zmmLane (montDigitCom.denote (.cons t (.cons np (.cons mask .nil)))) k
      = tl * Np &&& montMaskR := by
    rw [montDigitCom_lane, ← htl, hnp, hmask]
  -- The fold lane u = (t + m·Nv) >>> 16.  The unified `.mul` is the FULL 64-bit
  -- product `tl * Np` — on the ML-KEM `< 2³²` range this equals the bespoke masked
  -- `vpmuludq` (the masking is the identity), so the FULL product IS what we want.
  rw [montFoldCom_lane, hdig, ← htl, hnn, hsh, montLogR]
  -- m as a Nat: m = (t·Np) mod R, using no-wrap on the product and `& (R-1)`.
  have hprod : tl.toNat * Np.toNat < 2 ^ 64 := by
    calc tl.toNat * Np.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ht32 hnp32
      _ = 2 ^ 64 := by norm_num
  have hmNat : (tl * Np &&& montMaskR).toNat = (tl.toNat * Np.toNat) % montR := by
    have hmaskNat : (montMaskR : BitVec 64).toNat = 2 ^ 16 - 1 := by decide
    rw [BitVec.toNat_and, hmaskNat, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_mul, Nat.mod_eq_of_lt hprod, montR]
  have hm32 : (tl * Np &&& montMaskR).toNat < 2 ^ 32 := by
    rw [hmNat]; exact lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  -- Compute toNat through the add and the shift.  The second multiply m·Nv is also
  -- exact (no wrap): `m < 2³²`, `Nv < 2³²`.
  have hmNlt : ((tl.toNat * Np.toNat) % montR) * Nv.toNat < 2 ^ 64 := by
    have h1 : (tl.toNat * Np.toNat) % montR < 2 ^ 32 := by rw [← hmNat]; exact hm32
    calc ((tl.toNat * Np.toNat) % montR) * Nv.toNat < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul'' h1 hnn32
      _ = 2 ^ 64 := by norm_num
  have hmN : ((tl * Np &&& montMaskR) * Nv).toNat
      = ((tl.toNat * Np.toNat) % montR) * Nv.toNat := by
    rw [BitVec.toNat_mul, hmNat]
    exact Nat.mod_eq_of_lt hmNlt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, hmN, Nat.mod_eq_of_lt hwrap]
  -- shift by 16 = / 2^16 = / montR.
  simp only [montgomeryReduce, montR, Nat.shiftRight_eq_div_pow]

/-! ## 4. The payoff — the unified csub'd REDC output is the Montgomery-domain butterfly

The csub canonicalization is `csubLane` (model-free, `BitVec 64`). Composing it
with the unified fold-Com lane and the value-level `montgomeryReduce_correct`
yields the defining Montgomery property over `ZMod N`, off the bespoke machine. -/

/-- **THE PAYOFF — Montgomery-form residue, re-anchored.** Under the ML-KEM 3329
    Montgomery preconditions — the operand `< 2³²` bounds (making the two
    `zmmPackQ .mul`s exact) and no-wrap headroom; the Montgomery constant law
    `N·N' ≡ −1 [MOD R]`; the REDC input bound `t < R·N`; and `2N ≤ 2⁶³` — the
    `csubLane` of the unified fold-Com output lane `k`, cast to the ML-KEM
    coefficient field `ZMod N` and multiplied by `R`, equals the field-domain
    butterfly value `t`:

    `(csubLane u N : ZMod N) · R = (t : ZMod N)`,

    where `u` is the unified REDC output lane and `t` the butterfly value. The lane
    is therefore the Montgomery form `t·R⁻¹ (mod N)` — **one** REDC, the Montgomery
    domain, not the plain residue (the scope inherited from the bespoke web).
    Proved over the verified `Com jasminDialect` `zmmPackQ` denotation, with no
    `runZBlock` / `jasminc`. -/
theorem montRedcCom_zmod
    (t np mask nn shc : BitVec 512) (k : Fin 8) (Nv Np : BitVec 64)
    (hnp : zmmLane np k = Np) (hnn : zmmLane nn k = Nv)
    (hmask : zmmLane mask k = montMaskR) (hsh : (zmmLane shc k).toNat = montLogR)
    (ht32 : (zmmLane t k).toNat < 2 ^ 32)
    (hnp32 : Np.toNat < 2 ^ 32) (hnn32 : Nv.toNat < 2 ^ 32)
    (hwrap : (zmmLane t k).toNat
        + ((zmmLane t k).toNat * Np.toNat % montR) * Nv.toNat < 2 ^ 64)
    (hNpos : 0 < Nv.toNat)
    (hNprime : (Nv.toNat * Np.toNat) % montR = montR - 1)
    (hTbound : (zmmLane t k).toNat < montR * Nv.toNat)
    (hP : 2 * Nv.toNat ≤ 2 ^ 63) :
    ((csubLane
        (zmmLane (montFoldCom.denote
          (.cons t (.cons (montDigitCom.denote (.cons t (.cons np (.cons mask .nil))))
            (.cons nn (.cons shc .nil))))) k) Nv).toNat : ZMod Nv.toNat) * montR
      = ((zmmLane t k).toNat : ZMod Nv.toNat) := by
  -- The unified REDC output lane = value-level montgomeryReduce.
  set redcv := montgomeryReduce Nv.toNat montR Np.toNat (zmmLane t k).toNat with hredc
  have hfold := montFoldCom_lane_toNat t np mask nn shc k Nv Np hnp hnn hmask hsh
    ht32 hnp32 hnn32 hwrap
  -- Value-level Montgomery correctness: redcv ∈ [0,2N) and redcv·R ≡ t (mod N).
  have hcorr := montgomeryReduce_correct Nv.toNat montR Np.toNat
    (zmmLane t k).toNat hNpos (by decide) hNprime hTbound
  obtain ⟨hlt2N, hmodeq⟩ := hcorr
  -- The csub input lane is on the [0,2N) domain.
  have hdom : (zmmLane (montFoldCom.denote
      (.cons t (.cons (montDigitCom.denote (.cons t (.cons np (.cons mask .nil))))
        (.cons nn (.cons shc .nil))))) k).toNat < 2 * Nv.toNat := by
    rw [hfold]; exact hlt2N
  -- csub preserves the residue mod N.
  have hcsub := csubLane_zmod _ Nv Nv.toNat rfl hP hdom
  rw [hcsub, hfold]
  -- redcv·R ≡ t [MOD N] ⇒ (redcv : ZMod N)·R = (t : ZMod N).
  have hcast : ((redcv * montR : Nat) : ZMod Nv.toNat)
      = ((zmmLane t k).toNat : ZMod Nv.toNat) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq
  rw [Nat.cast_mul] at hcast
  rw [hcast]

/-- **THE PAYOFF — canonicality, re-anchored.** Companion to `montRedcCom_zmod`:
    the `csubLane` of the unified fold-Com output lane is `< N` — the canonical
    residue representative in `[0, N)`. The `[0,2N)` range from
    `montgomeryReduce_correct` is the csub's domain, and `csubLane_lt`
    canonicalizes it, over the unified `zmmPackQ` denotation. -/
theorem montRedcCom_lt
    (t np mask nn shc : BitVec 512) (k : Fin 8) (Nv Np : BitVec 64)
    (hnp : zmmLane np k = Np) (hnn : zmmLane nn k = Nv)
    (hmask : zmmLane mask k = montMaskR) (hsh : (zmmLane shc k).toNat = montLogR)
    (ht32 : (zmmLane t k).toNat < 2 ^ 32)
    (hnp32 : Np.toNat < 2 ^ 32) (hnn32 : Nv.toNat < 2 ^ 32)
    (hwrap : (zmmLane t k).toNat
        + ((zmmLane t k).toNat * Np.toNat % montR) * Nv.toNat < 2 ^ 64)
    (hNpos : 0 < Nv.toNat)
    (hNprime : (Nv.toNat * Np.toNat) % montR = montR - 1)
    (hTbound : (zmmLane t k).toNat < montR * Nv.toNat)
    (hP : 2 * Nv.toNat ≤ 2 ^ 63) :
    (csubLane
        (zmmLane (montFoldCom.denote
          (.cons t (.cons (montDigitCom.denote (.cons t (.cons np (.cons mask .nil))))
            (.cons nn (.cons shc .nil))))) k) Nv).toNat < Nv.toNat := by
  have hfold := montFoldCom_lane_toNat t np mask nn shc k Nv Np hnp hnn hmask hsh
    ht32 hnp32 hnn32 hwrap
  have hcorr := montgomeryReduce_correct Nv.toNat montR Np.toNat
    (zmmLane t k).toNat hNpos (by decide) hNprime hTbound
  have hdom : (zmmLane (montFoldCom.denote
      (.cons t (.cons (montDigitCom.denote (.cons t (.cons np (.cons mask .nil))))
        (.cons nn (.cons shc .nil))))) k).toNat < 2 * Nv.toNat := by
    rw [hfold]; exact hcorr.1
  exact csubLane_lt _ Nv Nv.toNat rfl hP hdom

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemMontRedcAbstractCom
