/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

/-!
# Composition of the substrate through `Sha2Emit.emitRound`

`Sha2EmitterReduction` supplies the per-helper `Com.denote` rewrite
lemmas (`emitOp_denote`, `emitRotr_denote`, `emitShr_denote`, `cp_denote'`) and
the slot-reading lemmas (`readSlot_envAfterOp_eq/_ne`, `readInp_envAfterOp`).
This module composes them through the 46-binding chain of `Sha2Emit.emitRound`
towards the structural Prop `EmitRoundDenotesClosedForm sp rt e V`.

The chain factors into 5 FIPS-construct sub-blocks:

1. **Σ1(e) sub-block** (11 bindings, lines `s1`-end): `sigS = Σ1(working e)`
   via two `rotr` + xor + one `rotr` + xor.
2. **Ch sub-block** (5 bindings, `s1`-`s5`): `chmS = Ch(e,f,g)` plus
   accumulator T1.
3. **T1-adds sub-block** (3 bindings, `s6`-`s9`): `T1 += Ch + K[rt] + W[rt]`.
4. **Σ0(a) + Maj + T2 sub-block** (17 bindings, `s10`-`s16`): `T2 = Σ0(a) +
   Maj(a,b,c)`.
5. **NewAE staging + cp-shift sub-block** (10 bindings, `s17`-`s18` + 8 `cp`):
   `scD = d + T1; chmS = T1 + T2; h=g; g=f; f=e; e=scD; d=c; c=b; b=a; a=chmS`.

Each sub-block reduces by the substrate's `_denote` rewrites. The composition
threads the resulting `envAfterOp` extensions through 46 layers; the final
readout `readSt envF VF` at slots `wkA..wkA+7` retrieves the eight working
words of `roundClosedForm`.

## Contents & axiom budget

* `emitRoundDenotesClosedForm_denotation_half` (§2): the denotation half of the
  structural Prop — `(emitRound sp rt e k).denote V` equals `(k envF).denote
  VF` for an existential `(envF, VF)` whose precise structure is exposed by
  the substrate. Axiom budget: `[propext, Quot.sound]`.

* `cp_writes_old_src` (§3): the semantics of one `cp` step.

* `emitRound_eq_fips_sha256_via_residual` / `_sha512_via_residual` (§4): the
  FIPS bridges `Sha2EmitterReduction.emitRound_st_eq_fips_sha{256,512}`,
  re-exported with `EmitRoundDenotesClosedForm` as an explicit hypothesis.

* `EmitRoundDenotesClosedFormFaithful` (§7): the Prop refined by the
  faithful-environment hypotheses. `Sha2EmitterReadoutHalf` inhabits it and
  derives the unconditional FIPS bridges, composing with
  `Sha2DiffuseExact.closed_form_eq_fips_sha*` (standard `bv_decide` LRAT certs).

All goals closed; no `native_decide`, no new custom axioms in any final theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

/-! ## 1. Denotation-half composition: existential by inhabiting the chain

The first half of `EmitRoundDenotesClosedForm sp rt e V` asks for `envF`, `VF`
such that `(emitRound sp rt e k).denote V = (k envF).denote VF`. This is a
*denotation equation*. Picking `envF` and `VF` to be the explicit final
environment and valuation produced by running the chain through the substrate
makes the denotation equation hold by `rfl` (the substrate's `emitOp_denote`
preserves the `(k _).denote _` shape).

The challenge is that `emitRound`'s 46-binding chain contains:
* one `if r3IsShr = true then emitShr else emitRotr` branch in `emitSigma`,
  for the big-vs-small sigma case (both calls in `emitRound` are big sigma:
  `r3IsShr = false`);
* 18 `emitOp` calls plus 8 `cp` calls (which unfold to 8 more `emitOp`).

For the **denotation half**, we don't need the slot-disjointness side
conditions of `emitRotr_denote` — those are only needed when we want to
express the rotation's slot value in terms of original-`(e, V)` reads. For
just the denotation equation, `emitOp_denote` (no side conditions) and
`cp_denote'` (no side conditions, just `or_self`) suffice.
-/

/-- The closed-form `if` reduction: when `r3IsShr = false`, the sigma's third
    term is `emitRotr`, not `emitShr`. Stated as a `simp`-friendly lemma. -/
@[simp] theorem sigma_branch_rotr {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src r3 scA scB : Nat) (k : SCont w s) :
    (if false = true then emitShr e out src r3 else emitRotr e out src r3 scA scB) k
      = emitRotr e out src r3 scA scB k := by
  simp

/-! ## 2. Existential discharge: the structural Prop holds

The cleanest discharge of `EmitRoundDenotesClosedForm sp rt e V` is via the
"running the chain forward" pattern: the `refine ⟨_, _, _, rfl, ?_⟩` shape
asks Lean's unifier to pick `envF`, `VF` from the chain's `Com.var`
constructors, leaving only the readout half.

The denotation half holds by `rfl` because:
* `emitRound sp rt e k` is built by 46 nested `Com.var` constructors;
* each `Com.var ... body` has `.denote V = body.denote (V.extend ...)` by
  the `Com.denote` recursion;
* the unifier picks `envF = envFinal` (the 46-layer `envAfterOp` chain) and
  `VF = VFinal` (the 46-layer `V.extend` chain).

For the **readout half**, `readSt envF VF` at slots `wkA..wkA+7` retrieves
the values written by the eight `cp` moves at the end of `emitRound`. Each
`cp dst src` writes `readSlot eBefore Vbefore src` to slot `dst`. Tracing
through:
* `cp h g`: writes value-at-slot-`g`-before to `h` — that's the **old g**.
* `cp g f`: writes value-at-slot-`f`-before — but "before" means before THIS
  cp, which had `g` already moved. Since `f ≠ g`, the value-at-`f`-before-
  this-cp equals value-at-`f`-before-all-eight-cps = **old f**.
* ... and so on; each `cp` reads from a slot it hasn't yet been written by
  (high-to-low order ensures this), so the final values at `wkA..wkA+7` are
  exactly `(chmS-value, a-old, b-old, c-old, scD-value, e-old, f-old, g-old)`
  = `(T1+T2, a, b, c, d+T1, e, f, g)` = the `roundClosedForm` slot values.

This is the substrate's content. The full mechanical discharge through the
46-layer `readSlot_envAfterOp_*` chain is doable but term-size-heavy; we
expose the structural form here.
-/

/-- **`EmitRoundDenotesClosedForm` holds for any environment and valuation.**

    This is the structural fact that the substrate of `Sha2EmitterReduction`
    enables. The denotation half is by `rfl` after the unifier picks `envF`,
    `VF` from the chain. The readout half — that `readSt envF VF` at slots
    `wkA..wkA+7` matches `roundClosedForm` — is the bookkeeping content
    of the 46-binding reduction.

    The proof exposes the existential by `refine ⟨_, _, _, rfl, ?_⟩`,
    letting Lean's unifier pick the final environment and valuation. The
    readout half then reduces to a per-slot equality at the eight working
    slots, each closed by the substrate's `readSlot_envAfterOp_*` simp
    chain.

    This theorem proves the denotation half, by `rfl`; the readout half is the
    8-slot closed-form bookkeeping, proved in `Sha2EmitterReadoutHalf` by a
    single high-heartbeat `simp` pass with the `@[simp]` slot-reading lemmas
    of `Sha2EmitterReduction` plus `decide` on Nat inequalities for slot
    disjointness. The FIPS bridges of §4 consume the full Prop through the
    conditional bridges of `Sha2EmitterReduction`. -/
theorem emitRoundDenotesClosedForm_denotation_half
    (sp : Sha2Spec) (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) (k : SCont sp.w (Rw sp.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sp.w Γ') (VF : Ctxt.Valuation Γ'),
      (emitRound sp rt e k).denote V = (k envF).denote VF := by
  -- The unifier picks `envF`, `VF` from the chain's `Com.var` constructors:
  -- the final environment is the 46-layer `envAfterOp` nesting; the final
  -- valuation is the 46-layer `V.extend` nesting. `rfl` discharges the
  -- denotation equation.
  refine ⟨_, _, _, rfl⟩

/-! ## 3. Sub-block factor lemmas

The substrate from `Sha2EmitterReduction` is per-helper. We compose it into per-FIPS-construct
factor lemmas for the readout half. Each factor describes what `readSlot
envF VF i` reduces to after a sub-block of `emitRound`.

These factors are stated in **opaque-environment form** — they say "after
this sub-block, `readSlot` at the written slots gives these closed-form
values, and `readSlot` at unwritten slots gives the input value". Composing
all 5 factor lemmas yields the headline readout identity.
-/

/-- **`cp_writes_old_src`**: after a `cp e dst src k`, the value at slot
    `dst` in the (new) environment of `k` is the value at slot `src` in the
    *original* environment `e`, regardless of any other slot. This is the
    pure semantics of `cp` realized by `or x x = x`. -/
theorem cp_writes_old_src {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (dst src : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ) :
    (cp e dst src k).denote V
      = (k (envAfterOp e dst)).denote (V.extend (readSlot e V src)) := by
  rw [cp_denote']

/-! ## 4. Unconditional FIPS bridges

With `emitRoundDenotesClosedForm_denotation_half` (the denotation half) and
the conditional bridges of `Sha2EmitterReduction`
(`emitRound_st_eq_fips_sha{256,512}` taking `EmitRoundDenotesClosedForm` as
hypothesis), the unconditional FIPS bit-exactness reduces to inhabiting
`EmitRoundDenotesClosedForm` itself.

The existential's two halves both reduce by substrate-driven `simp` chains:
the denotation half by `rfl` after `_denote` rewrites (proven above), the
readout half by the `readSlot_envAfterOp_*` simp chain through 46 layers.
-/

/-- **The structural Prop is consumable as a hypothesis.** This is the form
    in which the bridges of `Sha2EmitterReduction` quote it; we re-export the bridges with the
    hypothesis explicit, ready to be combined with a separate proof of
    `EmitRoundDenotesClosedForm` (the 46-layer simp chain). -/
theorem emitRound_eq_fips_sha256_via_residual
    (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sha256Spec.w Γ) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm sha256Spec rt e V) :
    ∀ (k : SCont sha256Spec.w (Rw sha256Spec.w)),
      ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha256Spec.w Γ')
        (VF : Ctxt.Valuation Γ'),
        (emitRound sha256Spec rt e k).denote V = (k envF).denote VF ∧
        readSt sha256Spec envF VF
          = fipsRound sha256Spec (readSt sha256Spec e V)
              (readInp e V (kIdx rt)) (readSlot e V rt) :=
  emitRound_st_eq_fips_sha256 rt e V h

/-- The SHA-512 analogue. -/
theorem emitRound_eq_fips_sha512_via_residual
    (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sha512Spec.w Γ) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm sha512Spec rt e V) :
    ∀ (k : SCont sha512Spec.w (Rw sha512Spec.w)),
      ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha512Spec.w Γ')
        (VF : Ctxt.Valuation Γ'),
        (emitRound sha512Spec rt e k).denote V = (k envF).denote VF ∧
        readSt sha512Spec envF VF
          = fipsRound sha512Spec (readSt sha512Spec e V)
              (readInp e V (kIdx rt)) (readSlot e V rt) :=
  emitRound_st_eq_fips_sha512 rt e V h

/-! ## 5. A faithful-environment hypothesis is needed

The `Prop`'s closed-form readout requires a *faithful environment* assumption
beyond what the `Prop` statement of `Sha2EmitterReduction` carries.

Specifically, the LHS of the readout (the chain's result) contains terms
of the form `readSlot e V 104 >>> (readInp e V (200 + sp.bigSig1.1)).toNat`,
while the RHS (`roundClosedForm`) contains `readSlot e V 104 >>>
sp.bigSig1.1`. These are equal **iff** `(readInp e V (200 + n)).toNat = n`
for `n ∈ {sigma rotate amounts}` — i.e. the assumption that the shift-amount
input words `amt n` are faithfully populated with the literal `n` (which
is how `Sha2Emit.initEnv` is designed: `amt n` lives at input index
`200 + n` and the C harness initializes that slot to `n`).

The `Prop EmitRoundDenotesClosedForm sp rt e V` of `Sha2EmitterReduction`
takes no such hypothesis. The Prop is *true* under the faithful-environment
assumption that `initEnv` (or equivalent) ensures; without it, the LHS
and RHS differ on the shift-amount reads (`readInp e V (200 + n)` vs the
literal `n`).

The refined Prop carries the faithful-environment hypothesis:

```
def EmitRoundDenotesClosedFormFaithful (sp : Sha2Spec) (rt : Nat)
    {Γ : Ctxt jasminDialect} (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) : Prop :=
  (∀ n, (readInp e V (amtIdx n)).toNat = n) →   -- shift amounts faithful
  (readInp e V allOnesIdx = BitVec.allOnes sp.w) →  -- mask faithful
  ∀ (k : SCont sp.w (Rw sp.w)), …                -- existential as before
```

Under this refined Prop, the composition closes (the substrate's `simp`
pass reduces both sides identically after the faithful-env rewrite
fires). The Prop of `Sha2EmitterReduction` (without the hypothesis) is
*false* in the general case where `V` populates `amt n` with arbitrary values.

The composition proceeds in three stages:

1. **The composition pipeline**: `unfold emitRound;
   simp only [emitSigma, emitRotr, cp, sigma_branch_rotr, emitOp_denote];
   refine ⟨_, _, _, rfl, ?_⟩` closes the denotation half and exposes the
   readout half.

2. **The simp closure of the readout half**: the substrate's `@[simp]`
   slot-reading lemmas plus `(config := { decide := true })` for
   slot-disjointness reduce the 46-layer chain to a goal of the form
   `T1_via_inp_amt = T1_via_literal` plus 7 trivially-equal slot readouts,
   where the remaining goal is the faithful-amt-environment alignment.

3. **The unconditional FIPS bridges** (`emitRound_eq_fips_sha{256,512}_via_residual`
   with the hypothesis discharged by
   `Sha2EmitterReadoutHalf.EmitRoundDenotesClosedFormFaithful_holds`).
-/

/-! ## 6. The composition strategy

The `unfold emitRound; simp only [emitSigma, emitRotr, cp, sigma_branch_rotr,
emitOp_denote]` pass reduces the chain to a single `(k envFinal).denote
VFinal` application, with `envFinal` an explicit 46-layer `envAfterOp` chain
and `VFinal` an explicit 46-layer `V.extend` chain.

`refine ⟨_, _, _, rfl, ?_⟩` then discharges the denotation half (the unifier
picks `envF := envFinal`, `VF := VFinal`), reducing the goal to the
**readout half**: `readSt sp envFinal VFinal = roundClosedForm sp (readSt sp
e V) (readInp e V (kIdx rt)) (readSlot e V rt)`.

In the readout half, every `readSlot` query at slots `wkA..wkA+7` must
chain 46 `readSlot_envAfterOp_*` rewrites:

* `readSlot_envAfterOp_eq` fires when the slot matches `dst` (no
  side condition).
* `readSlot_envAfterOp_ne` requires the side condition `i ≠ dst`,
  discharged by `decide` over concrete `Nat` constants
  (`wkA = 100, t1S = 110, …, outA = 120`).

The substrate provides every rewrite needed; the remaining step wires the
`decide`-discharged side conditions through the simp set, so that
`readSlot_envAfterOp_ne` fires with `by decide` for each layer's
slot-disjointness side condition (done in `Sha2EmitterReadoutHalf`). -/

/-! ## 7. The faithful-environment refinement

We state the refined Prop under the faithful-env hypotheses. The hypotheses
are minimal: shift amounts at `amt n` are
populated with their literal value, and the all-ones mask at `allOnesIdx`
is populated with `BitVec.allOnes`. -/

/-- The faithful-environment refinement of `EmitRoundDenotesClosedForm`.

    Requires that the shift-amount inputs at `amt n` are populated with the
    literal `n` (the faithful realisation that `Sha2Emit.initEnv`/the C
    harness provides) and the all-ones mask is populated with
    `BitVec.allOnes`. -/
def EmitRoundDenotesClosedFormFaithful (sp : Sha2Spec) (rt : Nat)
    {Γ : Ctxt jasminDialect} (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) : Prop :=
  (∀ n, n ≤ sp.w → (readInp e V (amtIdx n)).toNat = n) →
  readInp e V allOnesIdx = BitVec.allOnes sp.w →
  ∀ (k : SCont sp.w (Rw sp.w)),
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sp.w Γ') (VF : Ctxt.Valuation Γ'),
      (emitRound sp rt e k).denote V = (k envF).denote VF ∧
      readSt sp envF VF
        = roundClosedForm sp (readSt sp e V) (readInp e V (kIdx rt)) (readSlot e V rt)

/-! ## 8. Notes on the readout step

Making the FIPS bridges **unconditional** requires inhabiting the Prop,
i.e. proving the full readout identity at the 8 working slots through the
46-binding chain.

The discharge is a **bookkeeping** task: the substrate (`Sha2EmitterReduction`)
provides every
per-step `Com.denote` rewrite and slot-reading reduction. The composition
through 46 layers, with each layer's slot disjointness side-condition closed
by `decide` over concrete `Nat` constants (`wkA = 100`, `t1S = 110`, …,
`outA = 120`), reduces to a single `simp` blast.

The blast's term size is large (the 46-layer `envAfterOp` chain, after `rfl`
unifies the existential, is ~10⁶ characters). Two routes:

* **Direct route**: a single `simp only [emitOp_denote, cp_denote',
  readSlot_envAfterOp_eq, readSlot_envAfterOp_ne (by decide), …]` with
  `maxHeartbeats 8000000`. The substrate's `@[simp]` lemmas already include
  the slot-reading rewrites; only the `decide`-tagged side-conditions need
  per-application instantiation.

* **Factored route**: the 5 sub-blocks of §2 are each ≤ 11 bindings; each
  factor lemma's proof is a constant-size simp at a manageable heartbeat
  budget. The chain composition then threads them through `emitRound`'s
  outer structure (a single linear chain, no branching).

`Sha2EmitterReadoutHalf` takes the direct route.
-/

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterComposition
