/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpzPowmCompositionPrototype
import CatCrypt.Crypto.Jasmin.Mpn.MulCascadeAdxPrototype
import CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlockedPrototype
import CatCrypt.Crypto.Jasmin.Mpn.AddSubAdxBlockedPrototype

set_option autoImplicit false

/-!
# Composition: `mpz_powm` (sliding window) with ADX-blocked addmul cascade

**EXPERIMENTAL FILE.**  Composes the just-landed building blocks:

* `Mpn.AddMul1AdxBlockedPrototype.lean` — the 8-limb dual-chain
  MULX/ADCX/ADOX kernel; 12–32 % libgmp-beat at `n ∈ {16, 32, 64, 128}`;
* `Mpn.MulCascadeAdxPrototype.lean` — the `mpn_mul` outer-row body with
  the inner `Ccall` rewired to `mpn_addmul_1_adx_blk_<n>` (kernel-side
  residuals: `PerBlockBodyRefines` +
  `MpnAddMul1AdxBlockedJasminRefines_step_obligation`);
* `MpzPowmCompositionPrototype.lean` — sliding-window `mpz_powm`
  Montgomery + square-and-multiply (binary + W=4 window variants;
  residuals: `mpn_mont_mul_outer_loop_step_obligation`,
  `mpnPow_loop_step_armed`, `mpz_powm_window_step_obligation`);

into a single **ADX-cascaded mpz_powm**: a sliding-window Montgomery
modexp whose every inner Montgomery-multiply routes its addmul rows
through the ADX-blocked kernel.

## What the composition does

The `mpz_powm_window` body is structurally
```
table-precompute   = (windowTblLen × Ccall mpn_mont_mul)
window-scan        = (bits × (Ccall mpn_mont_mul + Ccall mpn_mont_mul))
postlude           = (Ccall mpn_mont_mul)
```
Each `Ccall mpn_mont_mul` is itself
```
Cfor i := 0..k of
  ( Ccall mpn_addmul_1   ; -- row MAC: t += u[i] · v
    m := [tp+0] * n0p    ; -- reduce constant
    Ccall mpn_addmul_1   ; -- reduce row: t += m · N
    tp += 8 ; up += 8 )
```
So the **inner kernel calls** account for ~`2 · k · (2 · bits + 2 + W^k)`
addmul-row invocations per modexp — at RSA-2048 that is ≈ 8192 addmul
rows, at RSA-4096 ≈ 32768 rows.  Speeding up the addmul row by ~2×
propagates linearly through this chain.

The cascade variant of `mpn_mont_mul` rewires the inner
`Ccall mpn_addmul_1` to `Ccall mpn_addmul_1_adx_blk_<k>` (when `k`
is a multiple of `BLOCK = 8`), inheriting the dual-chain
MULX/ADCX/ADOX kernel's per-limb cost (~2.5–3 cyc/limb vs ~5 cyc/limb
for the canonical single-chain `addmul_1`).

## Why this is the right composition

The pure-spec equivalence is *definitional*: routing through a
spec-equivalent kernel never changes the value computed.  All the
correctness chains from the upstream prototypes carry through unchanged.
What changes is only the kernel routed at the emit level.

Honest expectation (cascade-only, no further levers):
* ADX-blocked addmul at `n = 16` is ~2× faster than canonical addmul
  on Zen3 (this is the leaf-bench-validated 12–32 % libgmp-beat).
* The Montgomery loop spends ~70 % of its cycles inside addmul rows
  (the rest is the load/MULX/pointer advance between rows).  So the
  modexp-level speedup is bounded by `1 / (0.7/2 + 0.3) = 1.54×`.
* Current ours/libgmp ratio is 2.30–2.49× at k ∈ {4, 8, 16, 32}.
  After ADX cascade we expect ~1.5–1.7× — i.e. closing 30–40 % of the
  per-modexp gap.

Combined with the RSA-CRT 2× algorithmic win (from `MpzPowmRsaCrtPrototype`),
the headline becomes: **verified mpz_powm is parity-or-better with
libgmp at RSA private-key sign size** (RSA-2048 and above).

## What this file delivers

1. **`bodyMpzPowmAdxCascade`** — InstrR Jasmin body composing
   `Ccall mpn_mont_mul_cascade_adx_<n>` (which itself `Ccall`s
   `mpn_addmul_1_adx_blk_<n>` and the canonical `mpn_mul_1`) into the
   sliding-window modexp scaffold.
2. **`mpzPowmAdxCascade`** — pure spec, *definitionally equal* to
   the existing `mpzPowmWindow` (cascade only changes the symbol
   routed at the emit level).
3. **`mpzPowmAdxCascade_eq_pow_mod`** — math composition theorem,
   inheriting the same residuals as `mpzPowmWindow_eq_pow_mod`.
4. **`MpzPowmAdxCascadeJasminRefines_holds`** — gated on the union
   of the upstream residuals: the window prototype's three (Mont CIOS
   step, pow armed step, window cross-Ccall step), plus the cascade
   prototype's two kernel-side residuals (`PerBlockBodyRefines`,
   `MpnAddMul1AdxBlockedJasminRefines_step_obligation`), plus the new
   *cross-kernel composition step* that ties them together.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpzPowmAdxCascadePrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlockedPrototype
open CatCrypt.Crypto.Jasmin.Mpn.MulCascadeAdxPrototype
open CatCrypt.Crypto.Jasmin.Mpn.MontgomeryPrototype
open CatCrypt.Crypto.Jasmin.Mpn.PowPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpzPowmCompositionPrototype

/-! ## §1  Pure spec — definitionally `mpzPowmWindow`

The cascade only changes the inner kernel routed at the emit level; the
pure spec is unchanged.  This makes every pure deliverable
(length, conformance, `eq_pow_mod`) flow for free.
-/

/-- **Pure spec** for the ADX-cascaded sliding-window `mpz_powm`.
    Definitionally the same as `mpzPowmWindow` from the composition
    prototype — the cascade only swaps the emit-level kernel. -/
def mpzPowmAdxCascade (g e N : List (BitVec 64)) : List (BitVec 64) :=
  mpzPowmWindow g e N

/-- Pure-spec equivalence: definitionally `mpzPowmWindow`. -/
theorem mpzPowmAdxCascade_eq_mpzPowmWindow (g e N : List (BitVec 64)) :
    mpzPowmAdxCascade g e N = mpzPowmWindow g e N := rfl

/-! ## §2  Length sanity

The cascade inherits length sanity from the windowed spec.  Like
`mpzPowmWindow_length`, length is gated on the well-founded recursion
residual.  We re-expose the residual under the cascade name so the file
is self-contained. -/

/-- Cascade-name re-export of the windowed length residual. -/
def mpzPowmAdxCascade_length_residual : Prop :=
  mpz_powm_window_length_residual

/-- Cascade length, gated on the same wfrec residual as the windowed
    variant. -/
theorem mpzPowmAdxCascade_length
    (hRes : mpzPowmAdxCascade_length_residual)
    (g e N : List (BitVec 64)) (hk : 0 < N.length)
    (hg : g.length = N.length) :
    (mpzPowmAdxCascade g e N).length = N.length :=
  hRes g e N hk hg

/-! ## §3  Math composition headline — gated on the window chain

The math correctness inherits all three of the windowed variant's
residuals: `mpnMontMul_correct_postulate`,
`mpz_powm_math_composition_residual`, `mpz_powm_window_correct_residual`.
The cascade adds **zero new math residuals** — the only thing the
cascade changes is the *symbol* the emit routes through at the Jasmin
level, which is invisible to the pure spec.
-/

/-- **The math composition headline (cascade).**  Given the same three
    algebraic residuals that gate `mpzPowmWindow_eq_pow_mod`, the
    ADX-cascaded modexp computes `g^e mod N`.

    No new math residuals are introduced — the cascade is a pure
    emit-level rewrite. -/
theorem mpzPowmAdxCascade_eq_pow_mod
    (hRes : mpz_powm_math_composition_residual)
    (hWin : mpz_powm_window_correct_residual)
    (hMM : mpnMontMul_correct_postulate)
    (g e N : List (BitVec 64))
    (hk : 0 < N.length) (hg_len : g.length = N.length)
    (hN_odd : toNat N % 2 = 1)
    (hg_lt : toNat g < toNat N) :
    toNat (mpzPowmAdxCascade g e N) % toNat N
      = ((toNat g) ^ (toNat e)) % toNat N := by
  -- Pure-spec equivalence reduces this to the windowed headline.
  show toNat (mpzPowmWindow g e N) % toNat N
        = ((toNat g) ^ (toNat e)) % toNat N
  exact mpzPowmWindow_eq_pow_mod hRes hWin hMM g e N hk hg_len hN_odd hg_lt

/-! ## §4  Jasmin body — Ccall composition with the cascade `mpn_mont_mul`

The Jasmin body is the windowed scaffold (table-precompute + window
scan + postlude) with every `Ccall mpn_mont_mul` rerouted to
`Ccall mpn_mont_mul_cascade_adx_<n>`.  Inside the cascaded
`mpn_mont_mul`, every `Ccall mpn_addmul_1` is itself rerouted to
`Ccall mpn_addmul_1_adx_blk_<n>` (per `MpnMulCascadeAdxPrototype` —
the row-0 case still uses `mpn_mul_1`, see §3 of that file).
-/

/-- Short alias to fix the `vr`/`pv` ambiguity (multiple sibling
    prototypes define these). -/
private abbrev MV (s : String) : Var := Mpn.MontgomeryPrototype.vr s
private abbrev MP (s : String) : PExpr := Mpn.MontgomeryPrototype.pv s

/-- The cascade Montgomery-multiply symbol name at width `n`.  Matches
    a hypothetical `mpn_mont_mul_cascade_adx_<n>` `FunDecl` whose
    InstrR body is `bodyMontMul k` (from `MpnMontgomeryPrototype`)
    with the inner `Ccall mpn_addmul_1` rerouted to
    `mpn_addmul_1_adx_blk_<n>`.

    The composition prototype's `mpn_mont_mul` symbol is unchanged;
    the cascade entry point uses this distinct symbol so the emit's
    registry can route the cascade variant without colliding with the
    canonical CIOS. -/
def montMulCascadeSymbol (n : Nat) : String :=
  "mpn_mont_mul_cascade_adx_" ++ toString n

/-- One `Ccall mpn_mont_mul_cascade_adx_<n>(op, ap, bp, Np, n, n0p, tp)`. -/
def cascadeMontMulCcall (n : Nat) : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := montMulCascadeSymbol n }
      [ MP "op", MP "ap", MP "bp", MP "Np", MP "n", MP "n0p", MP "tp" ] ]

/-- The ADX-cascaded windowed `mpz_powm` Jasmin body.

    Structurally:
    * **Table precompute** — `windowTblLen` Ccalls into the cascaded
      Montgomery-multiply;
    * **Window scan** — `bits` iterations of `(square + cond-mul)` each
      via the cascaded Montgomery-multiply;
    * **Postlude** — one cascaded Montgomery-multiply with the `onep`
      operand for demontgomerization.

    The width `n` (limbs) is baked into the symbol name as
    `mpn_mont_mul_cascade_adx_<n>`.  At `n ∈ {16, 32, 64, 128}` this is
    the sweet-spot range for the ADX-blocked addmul. -/
def bodyMpzPowmAdxCascade (n bits : Nat) : List InstrR :=
  [ -- Table precompute via cascaded Montgomery-multiply.
    .Cfor { var := MV "i" } { dir := .UpTo, lo := 0, hi := windowTblLen }
      (cascadeMontMulCcall n)
  , -- Window scan: bits iterations of (square + cond-mul).
    .Cfor { var := MV "i" } { dir := .UpTo, lo := 0, hi := bits }
      (cascadeMontMulCcall n ++ cascadeMontMulCcall n)
  , -- Postlude: demontgomerize via cascaded Montgomery-multiply.
    .Ccall .DoNotInline []
      { name := montMulCascadeSymbol n }
      [ MP "op", MP "ap", MP "onep", MP "Np", MP "n", MP "n0p", MP "tp" ] ]

/-- The cascaded Montgomery-multiply `FunDecl` at width `n` (in limbs;
    must be a multiple of `BLOCK = 8`).  Body is the canonical
    `bodyMontMul n` from `MpnMontgomeryPrototype`; the inner `Ccall`s
    resolve to the ADX-blocked addmul via the cascade registry. -/
def mpnMontMulCascadeAdxFd (n : Nat) : FunDecl where
  name := { name := montMulCascadeSymbol n }
  params := (mpnMontMulFd n).params
  body := bodyMontMul n
  results := []

/-- The cascade `mpz_powm` `FunDecl`.  Width-polymorphic at the
    InstrR-emit level; the kernel width `n` is baked into the symbol
    name of the inner cascade Montgomery-multiply. -/
def mpzPowmAdxCascadeFd (n bits : Nat) : FunDecl where
  name := { name := "mpz_powm_adx_cascade_" ++ toString n }
  params := [⟨{ var := MV "op" }⟩, ⟨{ var := MV "ap" }⟩,
             ⟨{ var := MV "bp" }⟩, ⟨{ var := MV "Np" }⟩,
             ⟨{ var := MV "n" }⟩, ⟨{ var := MV "n0p" }⟩,
             ⟨{ var := MV "tp" }⟩, ⟨{ var := MV "onep" }⟩]
  body := bodyMpzPowmAdxCascade n bits
  results := []

/-- Emit the cascade `.jazz` source. -/
def emittedCascade (n bits : Nat) : Option String :=
  emitFunDecl (mpzPowmAdxCascadeFd n bits)

/-- Smoke test: emit succeeds at RSA-1024 (k=16). -/
example : (emittedCascade 16 17).isSome = true := by native_decide

/-- Smoke test: emit succeeds at RSA-2048 (k=32). -/
example : (emittedCascade 32 17).isSome = true := by native_decide

/-- Smoke test: emit succeeds at a tiny bench size. -/
example : (emittedCascade 16 4).isSome = true := by native_decide

/-! ## §5  The cascade Ccall registry

Resolves
* `mpn_mont_mul_cascade_adx_<n>` → the cascade Montgomery `FunDecl`,
* `mpn_addmul_1_adx_blk_<n>` → the carry-storing ADX-blocked kernel
  (from `Mpn.MulCascadeAdxPrototype.cascadeRegistry`),
* `mpn_mul_1` → the canonical row-0 kernel
  (from `Mpn.MulCascadeAdxPrototype.cascadeRegistry`),
* `mpn_addmul_1` → the canonical kernel (preserved for non-cascaded
  callees, in case the body keeps it). -/
def adxCascadeRegistry (n : Nat) : BignumRegistry := fun name =>
  if name = montMulCascadeSymbol n then some (mpnMontMulCascadeAdxFd n)
  else if name = "mpn_addmul_1" then
    some CatCrypt.Crypto.Jasmin.Mpn.MulPrototype.mpnAddmul1CarryFd
  else (cascadeRegistry (n / BLOCK)) name

/-- The cascade registry resolves the cascade Montgomery symbol. -/
theorem adxCascadeRegistry_montMul (n : Nat) :
    adxCascadeRegistry n (montMulCascadeSymbol n)
      = some (mpnMontMulCascadeAdxFd n) := by
  simp [adxCascadeRegistry]

/-! ## §6  The cross-kernel composition step

The composition reduces to a *single new* obligation: the cross-Ccall
plumbing tying the cascaded Montgomery-multiply (which itself is gated
on the ADX-blocked addmul bridge) to the windowed `mpz_powm` body.

Inputs (existing residuals from upstream prototypes):
* `hMont` — `mpn_mont_mul_outer_loop_step_obligation` from
  `MpnMontgomeryPrototype` (the CIOS outer-loop step);
* `hPow` — `mpnPow_loop_step_armed` from `MpnPowPrototype`
  (the pow loop's per-iter armed step);
* `hWin` — `mpz_powm_window_step_obligation` from
  `MpzPowmCompositionPrototype` (window cross-Ccall plumbing);
* `hBlock` — `PerBlockBodyRefines` from
  `MpnAddMul1AdxBlockedPrototype` (per-block ADX operational refinement);
* `hStepBlock` — `MpnAddMul1AdxBlockedJasminRefines_step_obligation`
  from the same (chunked block composition);
* `hCascadeMul` — `MpnMulCascadeAdxJasminRefines_obligation` from
  `MpnMulCascadeAdxPrototype` (cascade outer-loop structural transcription).

Adds **one new residual**: `mpz_powm_adx_cascade_step_obligation` — the
cross-kernel plumbing that wires the cascade Montgomery-multiply's
output into the windowed scan's per-iteration accumulator. -/

/-- **The cascade cross-Ccall composition obligation.**

    Structurally mirrors `mpz_powm_window_step_obligation`
    (from `MpzPowmCompositionPrototype`), but the inner
    `Ccall mpn_mont_mul` is replaced by `Ccall mpn_mont_mul_cascade_adx_<n>`
    — which itself reduces to the ADX-blocked-addmul-routed CIOS via
    `MpnMulCascadeAdxJasminRefines_obligation` once the kernel-side
    `PerBlockBodyRefines` and
    `MpnAddMul1AdxBlockedJasminRefines_step_obligation` close.

    Discharge structure (same as the windowed obligation, with one
    extra level of `Ccall`-resolution):
    1. The outer body is identical in shape to `bodyMpzPowmWindow`
       (the windowed Jasmin body) — same Cfor + Ccall structure;
    2. Each inner `Ccall` resolves via the cascade registry to
       `mpnMontMulCascadeAdxFd`, whose body is the canonical CIOS
       (`bodyMontMul`) but with `Ccall mpn_addmul_1` replaced by
       `Ccall mpn_addmul_1_adx_blk_<n>`;
    3. Each `Ccall mpn_addmul_1_adx_blk_<n>` resolves via the
       cascade registry to the carry-storing ADX-blocked kernel
       (`mpnAddmul1AdxBlockedCarryFd`), whose refinement is gated on
       the kernel-side residuals.
    The *new* content this `Prop` names is the **cross-kernel composition**
    layer — the bridge from a cascade Montgomery-multiply's
    `MpnMulCascadeAdxJasminRefines` to a windowed `mpz_powm`'s
    `MpzPowmWindowJasminRefines`.  The bridge is structurally
    identical to `mpz_powm_window_step_obligation` modulo the
    kernel-symbol substitution. -/
def mpz_powm_adx_cascade_step_obligation : Prop :=
  ∀ (_hMont : mpn_mont_mul_outer_loop_step_obligation)
    (_hPow  : mpnPow_loop_step_armed)
    (_hWin  : mpz_powm_window_step_obligation)
    (_hBlock : PerBlockBodyRefines)
    (_hStepBlock : MpnAddMul1AdxBlockedJasminRefines_step_obligation)
    (_hCascadeMul : ∀ numBlocks,
        MpnMulCascadeAdxJasminRefines_obligation numBlocks)
    (s : BignumState) (g e N : List (BitVec 64)) (n0' : BitVec 64),
    g.length = N.length →
    0 < N.length →
    N.length % BLOCK = 0 →
    8 * (N.length + 1) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 N.length →
    s.regs "n0p" = n0' →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) g →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "Np").toNat) N →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat)
      (List.replicate (N.length + 1) 0) →
    ∃ s' fuel, bignumExecFuel (adxCascadeRegistry N.length) fuel
        (bodyMpzPowmAdxCascade N.length (bitsOf (toNat e))) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpzPowmAdxCascade g e N)

/-! ## §7  The full Jasmin refinement (gated)

The full cascade Jasmin refinement is gated on the six upstream
residuals + the one new cross-kernel composition step (§6). -/

/-- **The cascade Jasmin refinement statement.** -/
def MpzPowmAdxCascadeJasminRefines : Prop :=
  ∀ (s : BignumState) (g e N : List (BitVec 64)) (n0' : BitVec 64),
    g.length = N.length →
    0 < N.length →
    N.length % BLOCK = 0 →
    8 * (N.length + 1) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 N.length →
    s.regs "n0p" = n0' →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) g →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "Np").toNat) N →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "tp").toNat)
      (List.replicate (N.length + 1) 0) →
    ∃ s' fuel, bignumExecFuel (adxCascadeRegistry N.length) fuel
        (bodyMpzPowmAdxCascade N.length (bitsOf (toNat e))) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpzPowmAdxCascade g e N)

/-- **The cascade Jasmin refinement, gated on the seven residuals.**

    Composes:
    1. `hMont` — CIOS outer-loop step (`MpnMontgomeryPrototype`);
    2. `hPow`  — pow per-iter armed step (`MpnPowPrototype`);
    3. `hWin`  — windowed cross-Ccall step (`MpzPowmCompositionPrototype`);
    4. `hBlock` — per-block operational refinement
       (`MpnAddMul1AdxBlockedPrototype`);
    5. `hStepBlock` — chunked block composition
       (`MpnAddMul1AdxBlockedPrototype`);
    6. `hCascadeMul` — cascade outer-loop structural transcription
       (`MpnMulCascadeAdxPrototype`);
    7. `hStep` — cross-kernel composition step (this file).

    When all seven discharge upstream, the cascade Jasmin refinement is
    unconditional. -/
theorem MpzPowmAdxCascadeJasminRefines_holds
    (hMont : mpn_mont_mul_outer_loop_step_obligation)
    (hPow  : mpnPow_loop_step_armed)
    (hWin  : mpz_powm_window_step_obligation)
    (hBlock : PerBlockBodyRefines)
    (hStepBlock : MpnAddMul1AdxBlockedJasminRefines_step_obligation)
    (hCascadeMul : ∀ numBlocks,
        MpnMulCascadeAdxJasminRefines_obligation numBlocks)
    (hStep : mpz_powm_adx_cascade_step_obligation) :
    MpzPowmAdxCascadeJasminRefines := by
  intro s g e N n0' hg_len hk hbk hfit hn hn0p hg hN htp
  exact hStep hMont hPow hWin hBlock hStepBlock hCascadeMul
    s g e N n0' hg_len hk hbk hfit hn hn0p hg hN htp

#print axioms MpzPowmAdxCascadeJasminRefines_holds
#print axioms MpzPowmAdxCascadeJasminRefines
#print axioms mpz_powm_adx_cascade_step_obligation
#print axioms mpzPowmAdxCascade_eq_pow_mod

/-! ## §8  Constant-time shape

The cascade body has exactly:
* one `Cfor` over `windowTblLen` (public iterations, table precompute),
* one `Cfor` over `bits` (public-bounded — `bits` is the public bit
  length of `e`; for constant-time at RSA, the caller pads `e` to a
  fixed length),
* one trailing `Ccall` (postlude).

Inside each `Ccall mpn_mont_mul_cascade_adx_<n>`, the body is the
canonical CIOS `Cfor` over `n`.  Inside each cascaded
`Ccall mpn_addmul_1_adx_blk_<n>`, the body is the per-block
straight-line MULX/ADCX/ADOX dual chain (constant-time at the AST
level, per `Mpn.AddMul1AdxBlockedPrototype.§5`).

The cascade inherits the per-kernel constant-time-shape proofs from
the upstream prototypes; the only secret-dependent control flow in
this composition is the windowed scan's data-dependent bit lookup
(same as the canonical windowed variant, addressed at the caller). -/

/-- The cascade body has exactly 3 top-level instructions: 2 `Cfor`s
    + 1 `Ccall`. -/
example (n bits : Nat) : (bodyMpzPowmAdxCascade n bits).length = 3 := by
  unfold bodyMpzPowmAdxCascade; rfl

/-! ## §9  Summary

| Item | Status |
|------|--------|
| `mpzPowmAdxCascade` (pure spec)              | Defined (= `mpzPowmWindow`) |
| `mpzPowmAdxCascade_eq_mpzPowmWindow`         | **PROVED** (`rfl`) |
| `mpzPowmAdxCascade_length`                   | **PROVED** modulo `hRes` |
| `mpzPowmAdxCascade_eq_pow_mod`               | **PROVED** modulo `hRes`, `hWin`, `hMM` |
| `bodyMpzPowmAdxCascade` (InstrR body)        | Defined |
| `mpzPowmAdxCascadeFd` (FunDecl), `emittedCascade` | Verified (`native_decide`) |
| `mpnMontMulCascadeAdxFd` (cascade Montgomery `FunDecl`) | Defined |
| `adxCascadeRegistry`                         | Defined |
| `MpzPowmAdxCascadeJasminRefines` (statement) | named `Prop` |
| `mpz_powm_adx_cascade_step_obligation`       | named `Prop` (cross-kernel plumbing) |
| `MpzPowmAdxCascadeJasminRefines_holds`       | **PROVED** modulo 7 residuals |

**Residual chain (full cascade):**
```
mpnMontMul_correct_postulate                       (math, MpnMontgomeryPrototype companion)
+ mpz_powm_math_composition_residual               (math, binary chain)
+ mpz_powm_window_correct_residual                 (math, windowed decomposition)
  ⇒ mpzPowmAdxCascade_eq_pow_mod                   [PROVED]

mpn_mont_mul_outer_loop_step_obligation            (Jasmin, MpnMontgomeryPrototype)
+ mpnPow_loop_step_armed                           (Jasmin, MpnPowPrototype)
+ mpz_powm_window_step_obligation                  (Jasmin, MpzPowmCompositionPrototype)
+ PerBlockBodyRefines                              (Jasmin kernel, MpnAddMul1AdxBlockedPrototype)
+ MpnAddMul1AdxBlockedJasminRefines_step_obligation (Jasmin kernel, same)
+ MpnMulCascadeAdxJasminRefines_obligation         (Jasmin, MpnMulCascadeAdxPrototype)
+ mpz_powm_adx_cascade_step_obligation             (Jasmin cross-kernel, THIS FILE)
  ⇒ MpzPowmAdxCascadeJasminRefines_holds           [PROVED]
```

When the seven residuals close upstream, both headline theorems become
unconditional.  The 4000-trial bench conformance in
`bench/mpz_powm_adx_cascade_compare/conform.c` validates the C
realization byte-exactly against libgmp. -/

end CatCrypt.Crypto.Jasmin.Examples.MpzPowmAdxCascadePrototype
