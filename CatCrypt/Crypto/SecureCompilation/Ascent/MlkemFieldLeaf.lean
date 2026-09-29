/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.ExprLeaf
public import CatCrypt.Crypto.Util.ZMod3329
public import Transfer.Examples.PrimeWord

/-!
# A `ZMod 3329` coefficient value leaf for the ascent — the ML-KEM field spike

The word-layer ascent (`Ascent.Corres`, `Ascent.ExprLeaf`) abstracts a 64-bit word
to `ZMod 2^64` through the **unconditional** encoding `wEnc` and the `RelatedBinOp
wEnc` squares (`wEncAdd`/`wEncSub`/`wEncMul`), because `BitVec 64` *is* the ring
`ZMod 2^64`. This module builds the analogue value leaf for ML-KEM's coefficient
field `Zq3329 = ZMod 3329`, and — by building it — pins down exactly which pieces
of the word layer are `ZMod 2^64`-specific and had to change.

## The encoding `fqEnc`

`fqEnc w := (w.toNat : ZMod 3329)`, mirroring `wEnc w := (w.toNat : ZMod 2^64)`.
We carry the coefficient in a **64-bit slot** (`.sword 64`), reusing the whole
`semScalar` / `semLowerSExpr` machinery unchanged (that layer is hardwired to
`.sword 64`). The deployed ML-KEM emit carries coefficients as 16-bit SIMD lanes;
relating a *16-bit* lane word to `ZMod 3329` needs the entire scalar-denotation
layer re-indexed at width 16 (`SEnvScalar`, `envReader`, `SExpr.evalBV`,
`semLowerSExpr_ok'`, `corres_for`'s `BitVec.ofNat 64`), which is a separate,
large, width-parametricity lift — see the frontier note at the end.

## The square is CONDITIONAL — the first `ZMod 2^64`-specific break

`RelatedBinOp` (ParamTransfer) requires an *unconditional* commuting square
`∀ x y, enc (op x y) = bop (enc x) (enc y)`. For `wEnc` that holds because a
64-bit wraparound is a `ZMod 2^64` no-op. For `fqEnc` it is FALSE: a `BitVec 64`
add wraps mod `2^64`, and `2^64 ≢ 0 (mod 3329)`, so `fqEnc (x + y) = fqEnc x +
fqEnc y` needs the no-overflow side condition `x.toNat + y.toNat < 2^64`
(`fqEnc_add_of_lt`), implied by canonical inputs `< 3329` (`fqEnc_add_of_canonical`).
So `fqEnc` is **not** a `RelatedBinOp` instance; the square carries a hypothesis.

## The state relation must carry the representative range — and add breaks it

Because the square is conditional on the concrete representatives, the range
`w.toNat < 3329` must live in the *state relation* (which sees the concrete env),
not in `Corres`'s abstract precondition `P` (which sees only `ZMod 3329` values and
has lost the representative). But an ML-KEM `poly_add` coefficient step `r := a + b`
is **not reduced**: the output word is in `[0, 6658)`, non-canonical. So the
canonical input relation `SRfqCanon` is NOT preserved by the add — the correct
output relation is the value-only `SRfqVal` (no range). The homogeneous `Corres`
(same relation pre and post) that the word layer uses therefore cannot state this
leaf; we introduce the minimal **heterogeneous** `CorresH SRi SRo` and prove the
leaf as `CorresH SRfqCanon SRfqVal`. This asymmetry is the essential difference
from the word layer, where every 64-bit word is a valid `ZMod 2^64` element and no
range invariant exists to break.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Util

/-! ## The `ZMod 3329` coefficient encoding -/

/-- The coefficient encoding: a 64-bit slot word to `ZMod 3329`. The `fqEnc`
    analogue of `wEnc : BitVec 64 → ZMod 2^64`. -/
def fqEnc (w : BitVec 64) : ZMod 3329 := (w.toNat : ZMod 3329)

/-- `fqEnc` is the decoder of the canonical prime word at `p = 3329`. -/
theorem fqEnc_eq_primeDec : fqEnc = Transfer.PrimeWord.primeDec 3329 := rfl

/-! ## The conditional add square (the `RelatedBinOp` analogue) -/

/-- **The coefficient add square, conditional.** `fqEnc (x + y) = fqEnc x + fqEnc y`
    provided the representatives do not overflow the 64-bit slot. Unlike `wEncAdd`
    (unconditional `RelatedBinOp`), this carries the no-overflow hypothesis, because
    `2^64 ≢ 0 (mod 3329)`. It is the registered guarded square
    `Transfer.PrimeWord.decAddRelatedOn` at `p = 3329`. -/
theorem fqEnc_add_of_lt (x y : BitVec 64) (h : x.toNat + y.toNat < 2 ^ 64) :
    fqEnc (x + y) = fqEnc x + fqEnc y :=
  (Transfer.PrimeWord.decAddRelatedOn (p := 3329)).comm x y h

/-- Canonical corollary: for canonical coefficients (`< 3329`), the add square holds
    (the sum `< 6658 ≪ 2^64` never overflows the slot). This is the regime an
    ML-KEM `poly_add` step runs in on canonical inputs. -/
theorem fqEnc_add_of_canonical (x y : BitVec 64) (hx : x.toNat < 3329) (hy : y.toNat < 3329) :
    fqEnc (x + y) = fqEnc x + fqEnc y :=
  fqEnc_add_of_lt x y (by
    have h : x.toNat + y.toNat < 6658 := by omega
    exact lt_of_lt_of_le h (by norm_num))

/-! ## The heterogeneous correspondence `CorresH`

`Corres` (`Ascent.Corres`) uses ONE state relation for pre- and post-state. That
is sound for the word layer (`SRword` is a total ring iso preserved by every op),
but an unreduced `ZMod 3329` add takes a canonical env to a non-canonical one, so
no single relation with a range invariant is preserved. `CorresH` is the minimal
heterogeneous generalization: an input relation `SRi` and an output relation `SRo`.
(`Corres SR = CorresH SR SR`.) -/

/-- Heterogeneous forward simulation: from `SRi`-related states, `c` runs to an
    `SRo`-related result. Generalizes `Corres` (which is the `SRi = SRo` diagonal). -/
def CorresH {AState : Type} (SRi SRo : SEnvScalar → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : LowCT) : Prop :=
  ∀ env a, SRi env a → P a → ∃ env', semScalar c env = some env' ∧ SRo env' (fa a)

/-! ## The coefficient state relations -/

/-- The canonical input relation: every non-temp name holds a `.sword 64` word whose
    representative is canonical (`< 3329`) and whose `fqEnc` is the abstract
    coefficient. This is the invariant ML-KEM keeps on reduced polynomials. -/
def SRfqCanon (env : SEnvScalar) (a : String → ZMod 3329) : Prop :=
  ∀ x, ¬ isTmpName x →
    ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ w.toNat < 3329 ∧ fqEnc w = a x

/-- The value-only output relation: every non-temp name holds a `.sword 64` word
    whose `fqEnc` is the abstract coefficient, with NO range bound. This is the
    exact post-state of an unreduced coefficient add (the output is in `[0,6658)`). -/
def SRfqVal (env : SEnvScalar) (a : String → ZMod 3329) : Prop :=
  ∀ x, ¬ isTmpName x → ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ fqEnc w = a x

/-! ## The `ZMod 3329` `SAdd` value leaf -/

/-- **The coefficient-add value leaf.** A single unreduced coefficient add
    `r := a + b` over canonical source coefficients ascends to its `ZMod 3329` spec
    `φ a + φ b`, as a `CorresH SRfqCanon SRfqVal`. The value transfer runs through
    the conditional square `fqEnc_add_of_canonical`, whose no-overflow hypothesis is
    discharged from the canonical input relation `SRfqCanon` (`w.toNat < 3329`).
    Progress is `semLowerSExpr_ok'`, exactly as in the word leaf `corres_setExpr`. -/
theorem corres_setExpr_fqAdd (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName) :
    CorresH SRfqCanon SRfqVal (fun _ => True)
      (fun φ s => if s = rName then φ aName + φ bName else φ s)
      (.RScalarSetExpr rName (.SAdd (.SVar aName) (.SVar bName))) := by
  intro env a hSR _
  set e : SExpr := .SAdd (.SVar aName) (.SVar bName) with he
  -- the arithmetic expression is source-clean
  have hclean : srcClean e := ⟨hna, hnb⟩
  -- a witnessing rust state whose scalar store reads back the env words
  set rs : RustState := ⟨fun _ => none, fun y => (envReader env y).toNat⟩ with hrs
  have hEB : EnvBoundOn rs env (fun _ => True) := by
    intro y _ hnt
    obtain ⟨w, hw, _, _⟩ := hSR y hnt
    have hr : envReader env y = w := by simp only [envReader, hw]
    have hround : BitVec.ofNat 64 w.toNat = w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt w.isLt
    show env y = some ⟨.sword 64, BitVec.ofNat 64 ((envReader env y).toNat)⟩
    rw [hr, hround]; exact hw
  obtain ⟨env2, nm, cnt', hsem, _, hotb, _, _⟩ :=
    semLowerSExpr_ok' rs (fun _ => True) e env 0 hEB (varsBoundIn_true e) hclean
  -- read back the two canonical source coefficients
  obtain ⟨wa, hwa, hwalt, hwaEnc⟩ := hSR aName hna
  obtain ⟨wb, hwb, hwblt, hwbEnc⟩ := hSR bName hnb
  have hra : envReader env aName = wa := by simp only [envReader, hwa]
  have hrb : envReader env bName = wb := by simp only [envReader, hwb]
  -- the stored word evaluates to `wa + wb`
  have hev : SExpr.evalBV (envReader env) e = wa + wb := by
    simp only [he, SExpr.evalBV, hra, hrb]
  -- and its `fqEnc` is the clean spec, via the conditional square
  have hval : fqEnc (SExpr.evalBV (envReader env) e) = a aName + a bName := by
    rw [hev, fqEnc_add_of_canonical wa wb hwalt hwblt, hwaEnc, hwbEnc]
  refine ⟨env2.upd rName (t := .sword 64) (SExpr.evalBV (envReader env) e), ?_, ?_⟩
  · simp only [semScalar, hsem]
  · intro y hnt
    by_cases hyx : y = rName
    · refine ⟨SExpr.evalBV (envReader env) e, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_pos hyx]
      · show fqEnc (SExpr.evalBV (envReader env) e) = if y = rName then a aName + a bName else a y
        rw [if_pos hyx]; exact hval
    · obtain ⟨w, hw, _, hwEnc⟩ := hSR y hnt
      refine ⟨w, ?_, ?_⟩
      · simp only [SEnvScalar.upd, if_neg hyx]
        rw [hotb y (Or.inl hnt)]; exact hw
      · show fqEnc w = if y = rName then a aName + a bName else a y
        rw [if_neg hyx]; exact hwEnc

end CatCrypt.Crypto.SecureCompilation.Ascent
