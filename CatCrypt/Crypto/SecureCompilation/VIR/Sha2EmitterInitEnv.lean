/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition

/-!
# `Sha2Emit.initEnv` discharges the faithful-environment Prop

Task #115 (`Sha2EmitterComposition`) discovered that the denotation reduction
of `Sha2Emit.emitRound` to the `Sha2DiffuseExact.roundClosedForm` form needs a
**faithful-environment** hypothesis on the valuation `V`: the shift-amount
input words `amt n = .iw (200 + n)` must read as the literal `n` (so the
emitted `>>> (readInp e V (200 + n)).toNat` aligns with the closed form's
`>>> n`), and the all-ones mask `allOnesIdx = .iw 199` must read as
`BitVec.allOnes sp.w`.

`Sha2Emit.initEnv` (and the C harness in `bench/sha2_compare/`) populates the
input slots faithfully: input `200 + n` is `BitVec.ofNat sp.w n`, and input
`199` is `BitVec.allOnes sp.w`. This file packages that faithfulness as the
predicates the `EmitRoundDenotesClosedFormFaithful` Prop carries.

The remaining content of the Prop — discharging the existential `(envF, VF)`
witness with the closed-form readout under the now-active faithfulness — is
the 46-step substrate composition described in `Sha2EmitterComposition`
§6–§8. This file delivers the **faithfulness predicates** as concrete
inhabitants of the two Prop hypotheses, plus the bridge form that consumes a
proof of the inner existential to deliver the unconditional FIPS bridges for
`emitRound`.

## Status

* `initEnv_amt_faithful`, `initEnv_allOnes_faithful` — the two faithfulness
  hypotheses, proven for any valuation `V` that populates the input slots
  per the spec convention. We expose them as **conditions on a generic `V`**
  (the C harness runtime store is one such `V`), not as universal facts about
  every valuation — `initEnv` only fixes the De Bruijn variable mapping, not
  the underlying value of each input.

* `EmitRoundFaithful` predicate — the conjunction of the two faithfulness
  facts that the C harness's runtime store satisfies by construction.

* `emitRound_eq_fips_sha256_on_initEnv`, `_sha512_on_initEnv` — the
  **bridge form** of the FIPS identity: given a valuation that is faithful,
  if the substrate-composition Prop holds, then the emitted `emitRound`
  on `initEnv` denotes to the FIPS-spec round. This is the form
  `bench/sha2_compare/`'s KAT consumes.

The status of the inner-existential composition (the 46-step chain) is the
same residual as in `Sha2EmitterComposition`: this file does **not** discharge
that residual. What it delivers is the **faithfulness side** of the env
hypothesis, ensuring that once the substrate composition is complete, the
bridge composes without any further KAT-side check on the shift-amount or
mask inputs.

## Axiom budget

Verified by `lean_verify`:

* `initEnv_amt_faithful`: `[propext, Classical.choice, Quot.sound]`.
* `initEnv_allOnes_faithful`: `[propext, Quot.sound]`.
* `faithful_sha256` / `faithful_sha512`: `[propext, Classical.choice,
  Quot.sound]`.
* `emitRound_initEnv_eq_fips_sha256`: `[propext, Classical.choice, Quot.sound]`
  plus the six standard `bv_decide` LRAT certs from `Sha2DiffuseExact.crotr_eq_
  rotr_sha256` (#110), inherited via `closed_form_eq_fips_sha256`.
* `emitRound_initEnv_eq_fips_sha512`: same shape, inheriting the six
  `crotr_eq_rotr_sha512` LRAT certs.

No `sorry`, no `native_decide`, no new custom axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterInitEnv

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition

/-! ## 1. The "faithful store" for `inCtxt sp.w`

A `Ctxt.Valuation (inCtxt sp.w)` over the homogeneous reg-`w` input context
is a function from De Bruijn variables to `BitVec sp.w`. The C harness in
`bench/sha2_compare/` populates the store by indexing the runtime `inp[]`
buffer: input slot `i` receives the buffer entry, with the convention:

* `0 .. 15` — message words
* `16 .. 23` — chaining words
* `24 .. 24 + rounds - 1` — round constants `K[t]`
* `199` — the all-ones mask `BitVec.allOnes sp.w`
* `200 + n` — the shift literal `BitVec.ofNat sp.w n`

We express this convention as a **runtime store builder** parametric in the
message / chaining / constant words. -/

/-- The faithful value the C harness writes into the input slot at index `i`.

    Inputs in `[0, 16) ∪ [16, 24) ∪ [24, 24+rounds)` are read from the
    user-supplied buffers `msg`, `chain`, `K`. The mask at index `199` is the
    all-ones BitVec. Shift literals at `200 + n` are `BitVec.ofNat sp.w n`.
    Indices outside these ranges are `0` (irrelevant — never read in the
    emitted body, including dead `inp` slots in the `inCtxt sp.w` context). -/
def initInpVal (sp : Sha2Spec)
    (msg : Nat → BitVec sp.w) (chain : Nat → BitVec sp.w)
    (Kc : Nat → BitVec sp.w) (i : Nat) : BitVec sp.w :=
  if i < 16 then msg i
  else if i < 24 then chain (i - 16)
  else if i < 24 + sp.rounds then Kc (i - 24)
  else if i = allOnesIdx then BitVec.allOnes sp.w
  else if 200 ≤ i ∧ i < 200 + (sp.w + 1) then BitVec.ofNat sp.w (i - 200)
  else 0

/-! ## 2. Faithfulness lemmas

The two predicates `EmitRoundDenotesClosedFormFaithful` carries as
hypotheses are statements about `readInp e V` at specific slots. Under any
valuation `V` for which `(inVar sp.w i).lookup V = initInpVal sp msg chain Kc i`,
those predicates are provable by direct rewrite. -/

/-- Abbreviation: a valuation `V` is **input-faithful** with respect to a
    given (message, chaining, constant) layout iff every De Bruijn input
    variable resolves to the spec value. -/
def InpFaithful (sp : Sha2Spec) (V : Ctxt.Valuation (inCtxt sp.w))
    (msg : Nat → BitVec sp.w) (chain : Nat → BitVec sp.w)
    (Kc : Nat → BitVec sp.w) : Prop :=
  ∀ i, (inVar sp.w i).lookup V = initInpVal sp msg chain Kc i

/-- **Shift-amount faithfulness**: under an input-faithful valuation,
    `readInp (initEnv sp) V (amtIdx n) = BitVec.ofNat sp.w n` for every
    `n ≤ sp.w`. The `.toNat` of this is `n` (`BitVec.toNat_ofNat`). -/
theorem initEnv_amt_faithful (sp : Sha2Spec) (V : Ctxt.Valuation (inCtxt sp.w))
    (msg : Nat → BitVec sp.w) (chain : Nat → BitVec sp.w)
    (Kc : Nat → BitVec sp.w) (h : InpFaithful sp V msg chain Kc)
    (hsp : sp.rounds + 24 ≤ 200) (n : Nat) (hn : n ≤ sp.w) :
    (readInp (initEnv sp) V (amtIdx n)).toNat = n := by
  -- `readInp (initEnv sp) V (amtIdx n) = (inVar sp.w (200 + n)).lookup V`
  -- by `initEnv.inp` = `inVar sp.w`. Under `h`, this is `initInpVal sp …
  -- (200 + n)`, which evaluates to `BitVec.ofNat sp.w n`.
  unfold readInp initEnv amtIdx
  rw [h (200 + n)]
  -- `initInpVal sp msg chain Kc (200 + n) = BitVec.ofNat sp.w n` by
  -- short-circuit on the `200 ≤ 200 + n` and `200 + n < 200 + (sp.w + 1)`
  -- branches.
  unfold initInpVal
  have h1 : ¬ (200 + n < 16) := by omega
  have h2 : ¬ (200 + n < 24) := by omega
  have h3 : ¬ (200 + n < 24 + sp.rounds) := by
    -- This requires sp.rounds ≤ 176 (i.e., 200 ≥ 24 + rounds). For
    -- sha256Spec.rounds = 64 (so 24+64 = 88 < 200) and sha512Spec.rounds =
    -- 80 (24+80 = 104 < 200) this holds. We need it as a side hypothesis
    -- for a general `sp`, but the use sites are only the two concrete
    -- specs, so we discharge it via the assumption `sp.rounds + 24 ≤ 200`.
    -- For our concrete users (sha256, sha512), this is `decide`.
    omega
  have h4 : 200 + n ≠ allOnesIdx := by unfold allOnesIdx; omega
  have h5 : 200 ≤ 200 + n := by omega
  have h6 : 200 + n < 200 + (sp.w + 1) := by omega
  simp [h1, h2, h3, h4, h5, h6]
  -- Goal after simp: `n % 2 ^ sp.w = n`. Since `n ≤ sp.w < 2^sp.w` (for
  -- `sp.w ≥ 1` via `Nat.lt_two_pow_self`; trivially for `sp.w = 0` since
  -- `n = 0`), `Nat.mod_eq_of_lt` closes.
  have : n < 2 ^ sp.w := by
    have hpow : sp.w < 2 ^ sp.w := Nat.lt_two_pow_self
    omega
  exact Nat.mod_eq_of_lt this

/-- **All-ones-mask faithfulness**: under an input-faithful valuation,
    `readInp (initEnv sp) V allOnesIdx = BitVec.allOnes sp.w`. -/
theorem initEnv_allOnes_faithful (sp : Sha2Spec) (V : Ctxt.Valuation (inCtxt sp.w))
    (msg : Nat → BitVec sp.w) (chain : Nat → BitVec sp.w)
    (Kc : Nat → BitVec sp.w) (h : InpFaithful sp V msg chain Kc)
    (hsp : sp.rounds + 24 ≤ allOnesIdx) :
    readInp (initEnv sp) V allOnesIdx = BitVec.allOnes sp.w := by
  unfold readInp initEnv
  rw [h allOnesIdx]
  unfold initInpVal
  have h1 : ¬ (allOnesIdx < 16) := by unfold allOnesIdx; omega
  have h2 : ¬ (allOnesIdx < 24) := by unfold allOnesIdx; omega
  have h3 : ¬ (allOnesIdx < 24 + sp.rounds) := by omega
  simp [h1, h2, h3]

/-! ## 3. The combined faithfulness witness

`EmitRoundFaithfulOn initEnv V` packages the two predicates the
`EmitRoundDenotesClosedFormFaithful` Prop demands. It is a corollary of
`InpFaithful`, modulo a small side condition (`sp.rounds + 24 ≤ allOnesIdx =
199`, satisfied by both `sha256Spec` and `sha512Spec`). -/

/-- The faithfulness witnesses required to discharge the hypotheses of
    `EmitRoundDenotesClosedFormFaithful sp rt (initEnv sp) V`. -/
structure FaithfulHyps (sp : Sha2Spec) (V : Ctxt.Valuation (inCtxt sp.w)) : Prop where
  /-- Shift-amount input slots read as the literal `n` (modulo word size). -/
  amt : ∀ n, n ≤ sp.w → (readInp (initEnv sp) V (amtIdx n)).toNat = n
  /-- All-ones-mask input slot reads as `BitVec.allOnes sp.w`. -/
  allOnes : readInp (initEnv sp) V allOnesIdx = BitVec.allOnes sp.w

/-- An input-faithful valuation for `sha256Spec` gives the `FaithfulHyps`
    bundle (no extra side conditions — `24 + 64 = 88 < 199`). -/
theorem faithful_sha256 (V : Ctxt.Valuation (inCtxt sha256Spec.w))
    (msg chain Kc : Nat → BitVec sha256Spec.w)
    (h : InpFaithful sha256Spec V msg chain Kc) :
    FaithfulHyps sha256Spec V where
  amt n hn := initEnv_amt_faithful sha256Spec V msg chain Kc h (by decide) n hn
  allOnes := initEnv_allOnes_faithful sha256Spec V msg chain Kc h (by decide)

/-- An input-faithful valuation for `sha512Spec` gives the `FaithfulHyps`
    bundle (`24 + 80 = 104 < 199`). -/
theorem faithful_sha512 (V : Ctxt.Valuation (inCtxt sha512Spec.w))
    (msg chain Kc : Nat → BitVec sha512Spec.w)
    (h : InpFaithful sha512Spec V msg chain Kc) :
    FaithfulHyps sha512Spec V where
  amt n hn := initEnv_amt_faithful sha512Spec V msg chain Kc h (by decide) n hn
  allOnes := initEnv_allOnes_faithful sha512Spec V msg chain Kc h (by decide)

/-! ## 4. Bridge to FIPS — the Prop-consuming form

`EmitRoundDenotesClosedFormFaithful sp rt e V` already takes the faithfulness
hypotheses **internally**. Specialising to `(initEnv sp, V)` with a
`FaithfulHyps` bundle, the bridge to FIPS via `emitRound_eq_fips_sha{256,512}
_via_residual` requires only the substrate composition (the inner existential)
to be inhabited.

We expose two forms:

1. **`emitRound_initEnv_via_faithful`** — given a `FaithfulHyps` bundle, the
   Faithful Prop's two hypotheses are discharged, leaving the inner
   existential. This is the form the substrate composition will plug into.

2. **`emitRound_initEnv_eq_fips_sha{256,512}`** — given (a) `FaithfulHyps`
   and (b) the inner existential, the FIPS bit-exact identity holds for
   `emitRound` on `initEnv`. -/

/-- Discharge the two faithfulness hypotheses of
    `EmitRoundDenotesClosedFormFaithful sp rt (initEnv sp) V` from a
    `FaithfulHyps` bundle, returning the inner existential. -/
theorem emitRound_initEnv_via_faithful (sp : Sha2Spec) (rt : Nat)
    (V : Ctxt.Valuation (inCtxt sp.w)) (hF : FaithfulHyps sp V)
    (hProp : EmitRoundDenotesClosedFormFaithful sp rt (initEnv sp) V)
    (k : SCont sp.w (Rw sp.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sp.w Γ') (VF : Ctxt.Valuation Γ'),
      (emitRound sp rt (initEnv sp) k).denote V = (k envF).denote VF ∧
      readSt sp envF VF
        = roundClosedForm sp (readSt sp (initEnv sp) V)
            (readInp (initEnv sp) V (kIdx rt))
            (readSlot (initEnv sp) V rt) := by
  exact hProp hF.amt hF.allOnes k

/-- **SHA-256 unconditional-on-`initEnv` bridge**: given a faithful runtime
    valuation, the emitted `emitRound` for `sha256Spec` denotes to the FIPS
    180-4 round (via the closed-form intermediate). The only remaining
    hypothesis is the substrate composition `EmitRoundDenotesClosedFormFaithful`
    — `bench/sha2_compare/`'s KAT is no longer needed for the shift-amount or
    mask side. -/
theorem emitRound_initEnv_eq_fips_sha256 (rt : Nat)
    (V : Ctxt.Valuation (inCtxt sha256Spec.w))
    (msg chain Kc : Nat → BitVec sha256Spec.w)
    (hV : InpFaithful sha256Spec V msg chain Kc)
    (hProp : EmitRoundDenotesClosedFormFaithful sha256Spec rt (initEnv sha256Spec) V)
    (k : SCont sha256Spec.w (Rw sha256Spec.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha256Spec.w Γ')
      (VF : Ctxt.Valuation Γ'),
      (emitRound sha256Spec rt (initEnv sha256Spec) k).denote V = (k envF).denote VF ∧
      readSt sha256Spec envF VF
        = fipsRound sha256Spec (readSt sha256Spec (initEnv sha256Spec) V)
            (readInp (initEnv sha256Spec) V (kIdx rt))
            (readSlot (initEnv sha256Spec) V rt) := by
  obtain ⟨Γ', envF, VF, hDen, hSt⟩ :=
    emitRound_initEnv_via_faithful sha256Spec rt V (faithful_sha256 V msg chain Kc hV) hProp k
  refine ⟨Γ', envF, VF, hDen, ?_⟩
  rw [hSt, closed_form_eq_fips_sha256]

/-- **SHA-512 unconditional-on-`initEnv` bridge**: same as SHA-256, at width 64. -/
theorem emitRound_initEnv_eq_fips_sha512 (rt : Nat)
    (V : Ctxt.Valuation (inCtxt sha512Spec.w))
    (msg chain Kc : Nat → BitVec sha512Spec.w)
    (hV : InpFaithful sha512Spec V msg chain Kc)
    (hProp : EmitRoundDenotesClosedFormFaithful sha512Spec rt (initEnv sha512Spec) V)
    (k : SCont sha512Spec.w (Rw sha512Spec.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha512Spec.w Γ')
      (VF : Ctxt.Valuation Γ'),
      (emitRound sha512Spec rt (initEnv sha512Spec) k).denote V = (k envF).denote VF ∧
      readSt sha512Spec envF VF
        = fipsRound sha512Spec (readSt sha512Spec (initEnv sha512Spec) V)
            (readInp (initEnv sha512Spec) V (kIdx rt))
            (readSlot (initEnv sha512Spec) V rt) := by
  obtain ⟨Γ', envF, VF, hDen, hSt⟩ :=
    emitRound_initEnv_via_faithful sha512Spec rt V (faithful_sha512 V msg chain Kc hV) hProp k
  refine ⟨Γ', envF, VF, hDen, ?_⟩
  rw [hSt, closed_form_eq_fips_sha512]

/-! ## 5. Scope note: what #124 delivers, and what stays residual

`EmitRoundDenotesClosedFormFaithful sp rt (initEnv sp) V` is the
**substrate-composition Prop** itself — the 46-step chain composition
factoring `emitRound`'s `Com.denote` through the closed-form readout under
the faithfulness hypotheses. Discharging it is the residual structural task
described in `Sha2EmitterComposition` §6–§8; the substrate's per-helper
`_denote` lemmas (`emitOp_denote`, `emitRotr_denote`, `cp_denote'`,
`readSlot_envAfterOp_*`) plus the faithfulness rewrites are exactly the
pieces needed.

This file therefore delivers:

* The **faithfulness side** of the Prop hypothesis — every faithful runtime
  store discharges the two predicates the Prop carries.
* The **bridge composition** — once the inner existential is supplied, the
  FIPS bit-exact identity on `initEnv` follows by combining with
  `Sha2DiffuseExact.closed_form_eq_fips_sha{256,512}`.

What is **not** delivered here is the inner existential itself — the
46-step substrate composition. That is the same residual as in
`Sha2EmitterComposition`. With it, this file's `emitRound_initEnv_eq_fips_
sha{256,512}` becomes the unconditional SHA-2 FIPS bridge for the emitted
round on a faithful runtime store, with no `EmitRoundDenotesClosedForm`
hypothesis remaining and no KAT dependence (modulo the substrate
composition).
-/

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterInitEnv
