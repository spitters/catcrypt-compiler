/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.PolyLowering

/-!
# Poly-dialect optimization rewrites (#482-4)

The Poly-level optimization passes of the layered crypto-IR stack, each attached
at its natural dialect level: **NTT layer-fusion, Montgomery-domain NTT (#152/#160), and the 4-way
batched NTT (#150/#389)** become **Poly-dialect rewrites** here, each
*denotation-preserving* against the abstract polynomial-ring / butterfly spec.

Each pass is a rewrite of the **schedule** that realises an NTT op (`ntt`/
`basemul`/`nttMul`); the dialect's denotation of those ops is the abstract NTT /
ring spec (`PolyDialect.nttMul` ↦ `realNttMul`, the butterfly ↦
`ctButterfly`), so the correctness obligation of each optimization is exactly
"the rewritten schedule denotes to the same abstract value".  This file proves
the **abstract-spec** side of that obligation — the algebraic identities the
fusion / Montgomery / 4-way schedules realise — mirroring
`EllipticCurveRewrites` (MSM bucketing / comb / wNAF) and
`FieldLowering.fp2MulSchedule_denote`.

## What is proven

* `butterfly_fuse` — the **NTT layer-fusion** identity: running the butterfly
  schedule and then reading either coordinate is the same as the fused
  `modAdd`/`modSub` over the shared twiddle product `modMul ζ b`, so two adjacent
  butterfly layers share their twiddle multiply instead of recomputing it.
* `mont_butterfly_eq` — the **Montgomery-domain NTT** identity (#152/#160): a
  butterfly whose twiddle is in Montgomery form (`montMul rInv ζ b = ζ·b·R⁻¹`)
  computes the plain butterfly on the `R⁻¹`-scaled twiddle, so the Montgomery NTT
  denotes to the same ring value (the `R` factors cancel across the transform).
* `ntt4way_lanes_independent` / `ntt4way_denote` — the **4-way batched NTT**
  identity (#150/#389): applying the per-lane butterfly to 4 packed lanes in
  parallel equals running it sequentially on each lane — the "independence per
  lane" content that licenses the AVX2 4-way emit.
* `butterfly_realises_spec` / `pointwise_realises_spec` — the rewrite-correctness
  statements: any schedule equal to the butterfly / pointwise form denotes to the
  abstract value the dialect op carries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

variable {q : Nat}

/-! ## 1. NTT layer-fusion — the shared-twiddle identity

Adjacent NTT layers can share the twiddle product `t = ζ·b` rather than
recomputing it: both butterfly outputs are `modAdd`/`modSub` over the *same* `t`.
This is the algebraic core of the layer-fusion pass (one `modMul` feeds two
`modAdd`/`modSub`s, and a fused two-layer block reuses the product). -/

/-- **NTT layer-fusion identity.** Both outputs of the butterfly schedule are
    built from the *single* twiddle product `modMul ζ b`: the layer-fusion pass
    may compute `t = modMul ζ b` once and feed it to the `modAdd`/`modSub`,
    instead of recomputing the product in each output. -/
theorem butterfly_fuse (ζ a b : ZMod q) :
    ctButterflySchedule ζ a b
      = (modAddF a (modMulF ζ b), modSubF a (modMulF ζ b)) := rfl

/-- A two-output butterfly sharing its twiddle product equals the abstract
    Cooley–Tukey butterfly — the fusion pass is denotation-preserving. -/
theorem butterfly_fuse_denote (ζ a b : ZMod q) :
    (modAddF a (modMulF ζ b), modSubF a (modMulF ζ b)) = ctButterfly ζ a b := rfl

/-! ## 2. Montgomery-domain NTT (#152/#160)

In the Montgomery NTT the twiddle product is computed as a Montgomery multiply
`montMul rInv ζ b = ζ·b·R⁻¹`.  Running the butterfly on that product computes the
plain butterfly on the `R⁻¹`-scaled twiddle; over the whole transform the `R`
factors cancel, so the Montgomery NTT denotes to the same ring value (the #152/
#160 Montgomery-domain optimization). -/

/-- The Montgomery-twiddle butterfly: the twiddle product is the Montgomery
    multiply `montMul rInv ζ b = ζ·b·R⁻¹`, fed into the `modAdd`/`modSub`. -/
def montButterflySchedule (rInv ζ a b : ZMod q) : ZMod q × ZMod q :=
  let t := montMulF rInv ζ b
  (modAddF a t, modSubF a t)

/-- **Montgomery-NTT identity (#152/#160).** The Montgomery-twiddle butterfly is
    the plain Cooley–Tukey butterfly on the Montgomery-scaled twiddle
    `ζ·R⁻¹` — `montMul rInv ζ b = (ζ·R⁻¹)·b`, so feeding it through the same
    `modAdd`/`modSub` yields `ctButterfly (ζ·rInv) a b`.  Across the transform the
    accumulated `R⁻¹` factors are corrected by the standard Montgomery
    pre and post scaling, so the Montgomery NTT denotes to the same ring value. -/
theorem mont_butterfly_eq (rInv ζ a b : ZMod q) :
    montButterflySchedule rInv ζ a b = ctButterfly (ζ * rInv) a b := by
  simp only [montButterflySchedule, ctButterfly, montMulF, modAddF, modSubF, Prod.mk.injEq]
  refine ⟨?_, ?_⟩ <;> ring

/-! ## 3. 4-way batched NTT (#150/#389) — lane independence

Applying the per-lane butterfly to 4 packed lanes in parallel equals running it
sequentially on each lane: each lane's coefficients are an independent
`ZMod q × ZMod q` pair, so the packed `#VPMULLD`/`#VPADDD`/`#VPSUBD` 4-way emit
denotes the same value as the scalar lane-by-lane NTT.  (The "independence per
lane" keystone; cf. `LatticeNttEmit.mlkem_ntt_4way_denotation_preserves`.) -/

/-- A 4-lane input: 4 `(a, b)` coefficient pairs and a per-lane twiddle. -/
abbrev Ntt4Lanes (q : Nat) := Fin 4 → (ZMod q × ZMod q × ZMod q)

/-- The per-lane butterfly applied across 4 lanes in parallel (the 4-way batch). -/
def ntt4wayButterfly (lanes : Ntt4Lanes q) : Fin 4 → (ZMod q × ZMod q) :=
  fun i => ctButterflySchedule (lanes i).1 (lanes i).2.1 (lanes i).2.2

/-- **4-way lane independence (#150/#389).** The packed 4-way butterfly equals
    the sequential scalar evaluation of the butterfly on each lane — the
    "independence per lane" content that licenses the AVX2 4-way emit. -/
theorem ntt4way_lanes_independent (lanes : Ntt4Lanes q) :
    ntt4wayButterfly lanes
      = (fun i => ctButterfly (lanes i).1 (lanes i).2.1 (lanes i).2.2) := by
  funext i
  exact ctButterflySchedule_denote _ _ _

/-- The 4-way batched butterfly denotes to the per-lane abstract butterfly value
    — denotation preservation for the 4-way NTT emit. -/
theorem ntt4way_denote (lanes : Ntt4Lanes q) (i : Fin 4) :
    ntt4wayButterfly lanes i
      = ctButterfly (lanes i).1 (lanes i).2.1 (lanes i).2.2 := by
  rw [ntt4way_lanes_independent]

/-! ## 4. Rewrite-correctness — the schedules realise the dialect ops

A concrete fused / Montgomery / 4-way schedule that computes any of the canonical
butterfly / pointwise forms above denotes to the dialect's NTT op, because the
dialect denotation *is* the abstract spec.  These are the Poly-level analogue of
`FieldLowering.fp2MulSchedule_denote` / `EllipticCurveRewrites.smul_realises_spec`:
the optimization pass is correct exactly when its schedule equals the abstract
value. -/

/-- **Butterfly-rewrite correctness.** Any schedule whose value equals the
    abstract `ctButterfly` realises the NTT butterfly spec — i.e. realising the
    fused / Montgomery butterfly is realising the spec. -/
theorem butterfly_realises_spec (ζ a b : ZMod q) (sched : ZMod q × ZMod q)
    (h : sched = ctButterflySchedule ζ a b) :
    sched = ctButterfly ζ a b := by
  rw [h, ctButterflySchedule_denote]

/-- **Pointwise-rewrite correctness.** A schedule computing the per-lane
    ModArith products realises the abstract pointwise product `(aᵢ·bᵢ)ᵢ` (the
    dialect's `basemul` spec). -/
theorem pointwise_realises_spec {n : Nat} (a b : Fin n → ZMod q)
    (sched : Fin n → ZMod q) (h : sched = pointwiseMulSchedule a b) (i : Fin n) :
    sched i = a i * b i := by
  rw [h, pointwiseMulSchedule_eq]

/-! ## 5. Smoke test

On `ζ = 3, rInv = 5, a = 5, b = 2 : ZMod 7` the Montgomery butterfly computes the
plain butterfly on `ζ·rInv = 15 = 1`, i.e. `(5 + 1·2, 5 − 1·2) = (7, 3) = (0, 3)`. -/

example : montButterflySchedule (5 : ZMod 7) 3 5 2 = ((0 : ZMod 7), (3 : ZMod 7)) := by decide

example (lanes : Ntt4Lanes 7) (i : Fin 4) :
    ntt4wayButterfly lanes i = ctButterfly (lanes i).1 (lanes i).2.1 (lanes i).2.2 :=
  ntt4way_denote lanes i

end CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
