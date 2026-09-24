/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

/-!
# Variable-time bignum modular inverse for public-input paths

This module applies the variable-time support (noninterference modulo
public, `LowCTVartimeLeak.lean`) to a GMP-class operation: a **data-dependent,
early-terminating modular inverse**.

The early-terminating GCD step count is ~21–25 % of the CT safegcd fixed
divstep budget. A *plain* extended-Euclid / binary-GCD runs a full-precision
bignum division per GCD step and is *slower* than CT in wall-clock; the
realisation therefore uses **Lehmer acceleration**
(`bench/mpn_invert_safegcd_compare/lehmer_invert_ref.c`,
`mpn_invert_lehmer`): the GCD is simulated on the **top ~63 bits** of the two
operands, accumulating a single-word 2×2 cofactor matrix `[[A,B],[C,D]]`
(Collins/Jebelean exact-quotient guard) that is then applied to the full
bignums in **one batched multiply+add** — folding ~17–21 elementary GCD steps
into each O(n) update. This is the same asymptotic structure GMP's
`mpz_invert` uses (Lehmer = the single-word base case; HGCD = the recursive
generalisation). The control-flow shape is the `RWhileNz` loop modelled below,
guarded by the *batched* remainder rather than the per-elementary-step one, so
the taint gating below applies verbatim: the loop is licensed exactly when its
guard is public, and rejected (fail-closed) when secret.

The bench headline (k = 16/32, i.e. 1024/2048-bit RSA): OUR Lehmer-vartime
inverse **beats** CT safegcd in wall-clock (LEH/CT ≈ 0.85 at 1024-bit,
≈ 0.62 at 2048-bit), which plain EEA/BGCD does not (EEA/CT ≈ 3.0–3.5
throughout). At 256/512-bit it is at parity (≈ 1.05–1.12), where the
per-call generic-bignum (`mpz`) constant overhead dominates the structural
win; the remaining gap to GMP's asm-tuned ceiling (LEH/GMP ≈ 3) is raw-`mpn`
arithmetic and HGCD recursion.

## The two inverses

The constant-time Bernstein–Yang safegcd kernel
(`CatCrypt/Crypto/Vale/MpnInvert.lean`, emitted in
`SafegcdDivstep62Emit.lean`) runs a **fixed** number of divsteps (590 at
256-bit, 1416 at 512-bit, …, per the EUROCRYPT 2026 bound) *regardless of
input* — that is exactly what makes it constant-time, and what makes it the
mandatory path for a **secret-dependent** inverse (ECDSA nonce, RSA-CRT
private exponent).

A variable-time inverse (classical extended Euclid / binary GCD) instead
runs a **data-dependent** number of GCD steps and **terminates early** when
the running remainder reaches `0`. Its iteration count is a function of the
operand magnitudes, so it leaks them through timing. This is sound to use
**only when the inputs are public** — RSA *verify* (public modulus `n`,
public exponent `e`), public modular arithmetic, the curve order — where the
Public-taint typing rule of `LowCTVartimeLeak.lean` permits leakage ≤ the
public inputs.

## What this module establishes

The early-terminating GCD loop is an `RWhileNz` whose guard is the running
remainder `"g"` (nonzero ⇒ keep iterating). Each iteration calls the verified
divstep/quotient leaf (`vartime_modinv_step`) that shrinks `(f, g)` toward
the GCD and folds the Bezout coefficient.

* **Public-input acceptance** (`vartimeInvertBody_accepted_public`): under a
  table classifying the loop guard (and the public operands) as `Public`,
  `cmdCT` accepts the body — via `cmdCT_RWhileNz_iff`. The
  data-dependent early-exit loop is *licensed* because its guard is public.

* **Secret-input rejection** (`vartimeInvertBody_secret_rejected`): the *same*
  body, with the loop guard classified `Secret` (a secret-dependent operand),
  is **rejected** by `cmdCT` — fail-closed. This is the GMP-vs-CT split: a
  secret-dependent inverse must fall back to the fixed-step constant-time
  safegcd kernel.

* **Noninterference modulo public** (`vartimeInvert_noninterference`): on
  public inputs the dynamic leak trace — which records one `iter` event per
  executed GCD step, i.e. the very iteration count that varies with the
  operands — is **identical across any two runs that agree on the public
  inputs**, relative to the named `BodyStepPreservesPublic` hypothesis (the
  loop-body small-step semantics, which the `cmdCT` chain does not expose).
  Differences confined to secret slots
  are invisible; on public inputs everything is "secret-free", so the trace
  leaks at most the public operands — exactly the policy.

All of this uses the existing taint machinery (`cmdCT`, `guardPublic`,
`cmdCT_RWhileNz_iff`, `cmdCT_RWhileNz`, `dynLeakTrace_while_noninterference`,
`PublicEquiv`).

## Scope

* The acceptance / rejection (the **typing/gating** side) is proved outright
  by reduction to `cmdCT`.
* The loop noninterference is proved **relative to**
  `BodyStepPreservesPublic`, a named hypothesis on the loop-body state
  evolution (which a verified `LowCT.exec` would discharge); it is neither an
  admitted proof nor an axiom.
* The bench (`bench/mpn_invert_safegcd_compare/vartime_invert_bench.c`) and
  KAT (`vartime_invert_kat.c`) live on the C side: the Lehmer inverse is
  checked byte-exact (5-way KAT: `Lehmer == EEA == BGCD == GMP mpz_invert == CT
  safegcd`, random + corner inputs at 256/512/1024/2048-bit) and timed against
  CT safegcd and GMP. The wall-clock result is that OUR Lehmer-vartime beats
  CT at 1024/2048-bit (LEH/CT ≈ 0.85 / 0.62), at parity at 256/512-bit; the
  residual ≈ 3× gap to GMP is generic-`mpz` constant overhead + the HGCD
  recursion GMP has and this Lehmer base case does not.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VartimeBignumInverse

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace
open CatCrypt.Crypto.SecureCompilation.LowCTVartimeLeak

set_option autoImplicit false

/-! ## §1. The variable-time modular-inverse body

We model the early-terminating GCD loop directly in the `LowCT` IR. The slots:

* `"g"`   — the running remainder; the loop guard. Nonzero ⇒ keep going. This
  is the data-dependent control quantity. On a public-modulus path it is a
  function of public operands only; on a secret-operand path it is secret.
* `"f"`, `"d"`, `"e"` — the running `(f, g)` pair and the Bezout
  coefficients `(d, e)` that accumulate the inverse.

Each iteration calls the verified leaf `vartime_modinv_step`, which performs
one Euclidean / divstep reduction (shrink `(f, g)`, fold the coefficient) and
writes the new running remainder back into `"g"`. Because the *number* of
iterations is `RWhileNz`-driven by `"g"`, the body early-terminates on the
actual GCD path — unlike the fixed-trip-count CT kernel. -/

/-- A `TU64` slot at the given variable name. -/
def u64 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TU64 }

/-- The verified leaf performing one variable-time GCD reduction: shrinks
`(f, g)` and folds the Bezout coefficient `d`, updating the running remainder
`"g"`. In the Lehmer realisation (on the C/bench side
`mpn_invert_lehmer`) this leaf is one **batched** reduction — a single-word
2×2 cofactor matrix applied to the full bignums in one multiply+add, folding
~17–21 elementary GCD steps — rather than a single full-precision
Euclidean step (`mpn_invert_vartime_eea`). Either way it is an opaque CT leaf
called inside the loop; the loop shape, and hence the taint gating, is
identical. -/
def vartimeStepLeaf : String := "vartime_modinv_step"

/-- The early-terminating GCD loop body: one verified-leaf reduction per
iteration. The destination and operands are the running state slots. -/
def stepBody : LowCT :=
  LowCT.RCall vartimeStepLeaf (u64 "g") [u64 "f", u64 "g", u64 "d", u64 "e"]

/-- **The variable-time modular-inverse body.** The data-dependent,
early-terminating GCD loop: `while g != 0 { (f,g,d,e) := step(f,g,d,e) }`,
followed by a normalisation leaf producing the canonical `[0, m)` inverse.
The loop trip count is the GCD step count for *this* input — early
termination, the speedup lever for public inputs. -/
def vartimeInvertBody : LowCT :=
  LowCT.RSeq
    (LowCT.RWhileNz "g" stepBody)
    (LowCT.RCall "vartime_modinv_normalize" (u64 "out") [u64 "d", u64 "modulus"])

/-! ## §2. The level tables: public-input vs secret-input paths -/

/-- **Public-input path** (RSA verify, public modular arithmetic): every slot
— the loop guard `"g"`, the operands, the output — is `Public`. This is the
classification under which the variable-time inverse is *licensed*. -/
def publicInvertLT : LevelTable := LevelTable.allPublic

/-- **Secret-input path** (ECDSA nonce, RSA-CRT private exponent): the loop
guard `"g"` (the running remainder, a function of the secret operand) is
`Secret`. Under this table the variable-time inverse must be rejected — the
code has to fall back to the constant-time fixed-step kernel. -/
def secretInvertLT : LevelTable := fun v => if v = "g" then .Secret else .Public

/-- The leaf-CT table: both leaves are declared constant-time
(the per-step reduction and the normaliser are CT; only the *number* of
iterations is data-dependent, and that is what the policy governs). -/
def invertLeafCT : LeafCTTable :=
  fun f => f == vartimeStepLeaf || f == "vartime_modinv_normalize"

/-! ## §3. Public-input acceptance -/

/-- The per-step leaf call is accepted under the all-public table: the leaf is
CT, and the destination/operands are all public. -/
theorem stepBody_accepted_public :
    cmdCT stepBody publicInvertLT invertLeafCT = true := by
  simp only [stepBody, cmdCT_RCall, publicInvertLT, LevelTable.allPublic,
    invertLeafCT, vartimeStepLeaf, beq_self_eq_true, Bool.true_or,
    List.all_eq_true, Bool.and_eq_true, true_and]
  decide

/-- **The variable-time inverse is accepted on a public-input path.**
Under the all-public classification (RSA verify / public modular
arithmetic), `cmdCT` accepts the data-dependent early-terminating GCD loop —
because the loop guard `"g"` is `Public`. This is `cmdCT_RWhileNz_iff`
in action: a data-dependent loop is *licensed* exactly
when its guard is public-derived. -/
theorem vartimeInvertBody_accepted_public :
    cmdCT vartimeInvertBody publicInvertLT invertLeafCT = true := by
  rw [vartimeInvertBody, cmdCT_RSeq, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [cmdCT_RWhileNz_iff]
    refine ⟨?_, stepBody_accepted_public⟩
    unfold guardPublic publicInvertLT LevelTable.allPublic
    rfl
  · simp only [cmdCT_RCall, publicInvertLT, LevelTable.allPublic, invertLeafCT,
      beq_self_eq_true, Bool.or_true, List.all_eq_true,
      Bool.and_eq_true, true_and]
    decide

/-! ## §4. Secret-input rejection (the GMP/CT split) -/

/-- **The same variable-time inverse is REJECTED on a secret-input path.**
When the loop guard `"g"` (the running remainder, a function of a *secret*
operand) is classified `Secret`, `cmdCT` rejects the data-dependent loop —
fail-closed. This is the central soundness property: a secret-dependent
inverse may NOT use the variable-time early-terminating loop (it would leak
the secret through its iteration count); the code must fall back to the
fixed-step constant-time safegcd kernel. This is the GMP-vs-CT split. -/
theorem vartimeInvertBody_secret_rejected :
    cmdCT vartimeInvertBody secretInvertLT invertLeafCT = false := by
  -- The whole sequence fails because its first component, the loop, fails.
  rw [vartimeInvertBody, cmdCT_RSeq]
  have hloop : cmdCT (.RWhileNz "g" stepBody) secretInvertLT invertLeafCT = false := by
    rw [cmdCT_RWhileNz]
    have : secretInvertLT "g" = .Secret := by unfold secretInvertLT; rfl
    rw [this]
    rfl
  rw [hloop, Bool.false_and]

/-- The rejection is *specifically* the public-taint guard firing, not an
incidental leaf failure: the loop guard is secret. (Restates the gate via the
named predicate `guardPublic`.) -/
theorem vartimeInvert_guard_not_public_on_secret :
    ¬ guardPublic secretInvertLT "g" := by
  unfold guardPublic secretInvertLT
  simp

/-! ## §5. Noninterference modulo public (the NI guarantee) -/

/-- **Noninterference for the variable-time inverse on public inputs**,
relative to the `BodyStepPreservesPublic` hypothesis.

The dynamic leak trace `dynLeakTraceWhile` records **one `iter` event per
executed GCD step** — i.e. the data-dependent iteration count that varies
with the operands. This theorem shows that, on the public-input path, that
trace is **identical across any two runs that agree on the public inputs**:
the early-termination timing leaks at most the public operands, which the
policy already declassifies. (For full constant time — the all-secret
endpoint — the same machinery forces the trace constant; but here the point
is the public-input regime where the variable-time loop is *licensed*.)

This is `dynLeakTrace_while_noninterference` applied to the GCD loop;
the `bodyStep` is the loop-body state transition (the divstep reduction), and
`BodyStepPreservesPublic` is the named hypothesis on it, which a verified
`LowCT.exec` would discharge. -/
theorem vartimeInvert_noninterference
    (bodyStep : RustState → RustState)
    (hstep : BodyStepPreservesPublic publicInvertLT bodyStep)
    (fuel : Nat) {rs1 rs2 : RustState}
    (hPE : PublicEquiv publicInvertLT rs1 rs2) :
    dynLeakTraceWhile "g" stepBody bodyStep fuel rs1 =
      dynLeakTraceWhile "g" stepBody bodyStep fuel rs2 := by
  refine dynLeakTrace_while_noninterference publicInvertLT invertLeafCT
    "g" stepBody bodyStep ?_ stepBody_accepted_public hstep fuel hPE
  unfold guardPublic publicInvertLT LevelTable.allPublic
  rfl

/-! ## §6. The GMP/CT split, stated as one theorem

The two faces of the policy, side by side: the *same* variable-time inverse
body is accepted on a public-input path and rejected on a secret-input path.
This is the formal content of "vartime is only valid for public-input paths;
the CT path remains mandatory for secret-dependent inverses". -/

/-- **The public-input-only caveat, formalised.** The variable-time
early-terminating modular inverse is accepted exactly on the public-input
path and rejected on the secret-input path. The accept side licenses the
faster vartime kernel for RSA verify / public modular arithmetic; the reject
side forces the constant-time safegcd fallback for secret-dependent
inverses. -/
theorem vartimeInvert_public_only :
    cmdCT vartimeInvertBody publicInvertLT invertLeafCT = true ∧
      cmdCT vartimeInvertBody secretInvertLT invertLeafCT = false :=
  ⟨vartimeInvertBody_accepted_public, vartimeInvertBody_secret_rejected⟩

end CatCrypt.Crypto.SecureCompilation.VartimeBignumInverse
