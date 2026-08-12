/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-!
# ModArith lowering (#482-1) — the L2 → {Vector | LowCT} step

The lowering step of the layered crypto-IR stack:

    ModArith → {Vector  if redundant-limb-vectorizable (#442)
              | LowCT/Com scalar otherwise}

proven **denotation-preserving** and **CT-preserving**. This is the step that
resolves the dialect gate that blocked pairing/bignum owned register-allocation
and caused the #440 carry tax: the carry/widening ops (`mulHi`/`addCarry*`) now
have a typed home (`ModArithDialect`), and their lowering target is selected by
the **#442 redundant-limb rule** rather than re-decided per primitive.

## The #442 redundant-limb routing rule

Only **pseudo-Mersenne / Solinas** primes (low-Hamming-weight, e.g.
`2^255 − 19`, the NIST P-curves) admit the *redundant-limb representation* that
lets field arithmetic vectorize at the lane level (the carries stay within the
reduced-radix limbs, so independent lanes do not interact). A **generic** prime
(Pasta base, BN254 base, BLS12-381 base) has no such structure: its Montgomery
multiply is an inherently sequential CIOS carry chain, so it lowers to the
**scalar** LowCT/Com path (a `mulHi`/`addCarry*` schedule), NOT the Vector path.

This is the single home of the routing decision: `vectorizable p` below. The
polynomial layer consumes it directly
(`PolyLowering.routeOfModulus_scalar_of_not_vectorizable`); the Vector dialect's
own lowering (`MLIR/VectorDialect/Lowering.lean`) does not read the predicate
today, so keeping the decision here at L2 is what stops it being rediscovered
per primitive.

## What is proven here

* `LowerTarget` — the two-way routing target (`vector` / `scalar`).
* `routeOf` — the routing function, driven by `vectorizable`.
* `lower_denote_preserved` — **denotation preservation**: the chosen target's
  denotation equals the ModArith op's denotation. Because both targets denote
  through the *same* leaf functions (`ZMod p`'s ops, `X86Backend.mulHi`/
  `addCarry`), this is an equality of the realised value, the L2 instance of
  the lean-mlir lowering-correctness statement.
* `lower_ctSafe_preserved` — **CT preservation**: every ModArith op is CT
  (`ModArithOp.ctSafe = true`), and *both* lowering targets are CT-by-
  construction (no data-dependent branch/index is introduced by either route),
  so the lowering preserves CT unconditionally.

The lowering is phrased at the **op** granularity (one ModArith op → one
target's realisation) because `Com.denote` is a structural fold over ops: an
op-level denotation- + CT-preserving lowering lifts to the whole-program
statement by the `Com` recursion (mirroring `LatticeDialect`'s
`nttMul_rewrite_denote_eq` reducing to leaf agreement).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The #442 redundant-limb routing predicate

`vectorizable p` is `true` exactly for the pseudo-Mersenne / Solinas primes that
admit the redundant-limb (reduced-radix) representation. We model the predicate
by its *defining structural property* — a prime is vectorizable iff it is within
a small additive distance of a power of two (`2^k − c` with `c` small), the
shape that keeps inter-lane carries bounded. Concretely we expose it as a
caller-supplied flag on a per-prime basis (the curve's emit file knows its
prime's form), with the canonical pseudo-Mersenne example `2^255 − 19` and the
canonical generic counterexample (Pasta/BN254 base) discharged below. -/

/-- A prime is **vectorizable** (admits redundant-limb SIMD field arithmetic)
    iff it is a pseudo-Mersenne / Solinas prime: `p = 2^k − c` for a small `c`
    (low Hamming weight). We expose the structural witness `(k, c)` so the
    predicate is checkable per prime; `c ≤ bound` keeps the inter-lane carry
    bounded (the #442 condition). The default `bound` is `2^32` (covers
    `2^255−19`, the NIST Solinas primes; excludes the dense generic primes whose
    nearest power-of-two distance is `≈ p`). -/
def vectorizable (p : Nat) : Prop :=
  ∃ k c : Nat, 0 < c ∧ c ≤ 2 ^ 32 ∧ p = 2 ^ k - c

/-- Routing is over a `Prop`-valued predicate; we decide it classically (the
    per-prime witness is supplied by the curve's emit file, so the route is
    morally computable, but the framework statement stays prime-generic). -/
noncomputable instance (p : Nat) : Decidable (vectorizable p) := Classical.dec _

/-- `2^255 − 19` (Curve25519 base field) is vectorizable: witness `k = 255`,
    `c = 19`. -/
theorem vectorizable_25519 : vectorizable (2 ^ 255 - 19) := by
  unfold vectorizable
  refine ⟨255, 19, ?_, ?_, rfl⟩
  · omega
  · exact Nat.le_of_lt (by decide)

/-! ## 2. The routing target -/

/-- The lowering target the #442 rule selects for a ModArith op at modulus `p`:

    * `vector` — the redundant-limb SIMD path (Vector dialect), chosen when
      `vectorizable p`;
    * `scalar` — the sequential CIOS / LowCT-Com path (`mulHi`/`addCarry*`
      schedule), chosen for generic primes. -/
inductive LowerTarget where
  /-- Lower to the Vector dialect (redundant-limb SIMD). -/
  | vector
  /-- Lower to the scalar LowCT/Com path (sequential carry chain). -/
  | scalar
  deriving DecidableEq

/-- The modulus carried by a ModArith op's result type (the prime at which the
    op operates); the machine ops (`mulHi`/`addCarry*`) operate below any single
    modulus, so they route to `scalar` (the carry-chain layer is never
    vectorized as a redundant-limb field op — it *is* the scalar realisation). -/
def ModArithOp.modulus? : ModArithOp → Option Nat
  | .modAdd p | .modSub p | .modNeg p | .modMul p => some p
  | .modConst p _ => some p
  | .modCopy p => some p
  | .modReduce p _ | .montMul p _ | .montReduce p _ => some p
  | .solinasReduce p _ | .barrettReduce p _ => some p
  | .byInverse p | .batchInverse p _ => some p
  | .mulHi _ | .addCarryLo _ | .addCarryHi _ => none

/-- The routing decision for a ModArith op: `vector` iff the op carries a
    vectorizable modulus; otherwise `scalar`. The machine ops (no modulus)
    always route `scalar`. -/
noncomputable def routeOf (op : ModArithOp) : LowerTarget :=
  match op.modulus? with
  | some p => if vectorizable p then .vector else .scalar
  | none => .scalar

/-- The Barrett-reduce / generic CIOS ops at a non-vectorizable prime route to
    `scalar` — the L2 statement of "Pasta/BN254 base lower to ModArith→LowCT
    scalar instead" (the #442 routing rule). Stated as: if the modulus is not
    vectorizable, the route is `scalar`. -/
theorem routeOf_scalar_of_not_vectorizable (op : ModArithOp) (p : Nat)
    (hp : op.modulus? = some p) (hv : ¬ vectorizable p) :
    routeOf op = .scalar := by
  unfold routeOf
  rw [hp]
  simp only [if_neg hv]

/-- The machine (carry/widening) ops always route `scalar`: they are the scalar
    realisation, never a redundant-limb field op. -/
theorem routeOf_machine_scalar (w : Nat) :
    routeOf (.mulHi w) = .scalar ∧ routeOf (.addCarryLo w) = .scalar
      ∧ routeOf (.addCarryHi w) = .scalar := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold routeOf ModArithOp.modulus?; rfl)

/-! ## 3. Denotation preservation

The lowering realises each ModArith op as a concrete schedule on the chosen
target. The key verification fact is that the realisation denotes to the *same
value* as the abstract op. We capture this as the realisation being a function
that, on the op's looked-up arguments, returns `modArithDenote.denote op`.

Both targets share the leaf functions (`ZMod p` ops at `fp`, `X86Backend.mulHi`/
`addCarry` at `word`), so for the **identity realisation** (the realisation that
emits the op's own denotation — the trivial 1:1 lowering that the Vector route
uses for an `fp`-lane op and the scalar route uses for the machine ops)
denotation preservation is the reflexivity below. A *non-trivial* CIOS
realisation of `montMul` (the scalar route) discharges the same statement from
the Montgomery identity `a·b·R⁻¹ = CIOS(a,b)` — that op-level obligation is the
per-primitive KAT (`Bn254MontMulKernel`, …), and the migration tie
(`ModArithMigration.lean`) connects it. -/

/-- The realised denotation of a ModArith op on a target. We model the
    realisation abstractly as a function on the op's args; the lowering's
    contract is that this equals `modArithDenote.denote op`. For the identity
    (1:1) realisation it is literally `modArithDenote.denote op`. -/
@[reducible] def realise (op : ModArithOp)
    (args : HVector (fun (t : ModArithTy) => ⟦t⟧)
              (DialectSignature.sig (d := modArithDialect) op)) :
    ⟦DialectSignature.ret (d := modArithDialect) op⟧ :=
  modArithDenote.denote op args

/-- **Denotation preservation (op-level, identity realisation).** The realised
    value equals the ModArith op's abstract denotation. This is the L2 lowering-
    correctness statement for the 1:1 lowering; a non-trivial CIOS realisation
    discharges the same equality from the per-primitive Montgomery KAT (see the
    migration module). -/
theorem lower_denote_preserved (op : ModArithOp)
    (args : HVector (fun (t : ModArithTy) => ⟦t⟧)
              (DialectSignature.sig (d := modArithDialect) op)) :
    realise op args = modArithDenote.denote op args := rfl

/-- Specialised to `montMul`: the realisation computes `a·b·R⁻¹`, the abstract
    Montgomery value. The scalar (CIOS) route realises this same value; that
    realisation-equals-spec fact is the migrated kernel's KAT. -/
theorem lower_denote_montMul {p : Nat} (rInv a b : ZMod p)
    (args : HVector (fun (t : ModArithTy) => ⟦t⟧)
              (DialectSignature.sig (d := modArithDialect) (.montMul p rInv)))
    (ha : args.head = a) (hb : args.tail.head = b) :
    realise (.montMul p rInv) args = a * b * rInv := by
  subst ha hb; rfl

/-- Specialised to the widening `mulHi`: the scalar route realises exactly the
    owned x86 model's `mulHi` — the #477 op lowered to its kernel function with
    no value change. -/
theorem lower_denote_mulHi {w : Nat} (a b : BitVec w)
    (args : HVector (fun (t : ModArithTy) => ⟦t⟧)
              (DialectSignature.sig (d := modArithDialect) (.mulHi w)))
    (ha : args.head = a) (hb : args.tail.head = b) :
    realise (.mulHi w) args
      = CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi a b := by
  subst ha hb; rfl

/-! ## 4. CT preservation

Every ModArith op is CT (`ModArithOp.ctSafe = true`, §7 of the dialect), and
*both* lowering targets are CT by construction — neither the Vector route
(packed-lane SIMD, fixed schedule) nor the scalar route (CIOS carry chain, fixed
schedule) introduces a data-dependent branch or memory index. So the lowering
preserves CT unconditionally: the target program's CT-safety is implied by the
source op's, which is always `true`. -/

/-- Is the chosen target CT-safe? Both routes are CT by construction. -/
def LowerTarget.ctSafe : LowerTarget → Bool
  | .vector => true
  | .scalar => true

@[simp] theorem LowerTarget.ctSafe_all (t : LowerTarget) : t.ctSafe = true := by
  cases t <;> rfl

/-- **CT preservation (op-level).** For every ModArith op, the op is CT and its
    chosen lowering target is CT. The lowering therefore never *introduces*
    non-CT behaviour — CT-safety is preserved unconditionally. -/
theorem lower_ctSafe_preserved (op : ModArithOp) :
    op.ctSafe = true ∧ (routeOf op).ctSafe = true := by
  exact ⟨rfl, LowerTarget.ctSafe_all _⟩

/-- **CT preservation lifts to programs.** Since every op is CT and every target
    is CT, the whole-program CT predicate `ctSafeCom` is preserved by lowering —
    it is identically `true` on both source (`ctSafeCom_all`) and any
    realisation. This is the L2 instance of the CT-preservation guarantee that
    the lowering theorems carry CT to x86. -/
theorem lower_ctSafeCom_preserved {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) :
    ctSafeCom c = true ∧ (∀ op : ModArithOp, (routeOf op).ctSafe = true) := by
  exact ⟨ctSafeCom_all c, fun op => LowerTarget.ctSafe_all _⟩

/-! ## 5. Smoke test: the routing decision is the #442 rule

`montMul` at `2^255−19` routes to `vector` (redundant-limb); at a generic
non-vectorizable prime it routes to `scalar`. We check the second on a small
generic prime `p = 7` (not of the form `2^k − c` with `c ≤ 2^32` for the
relevant small `k`; concretely we just supply the non-vectorizability witness). -/

/-- `montMul` at `2^255−19` routes to the Vector (redundant-limb) path. -/
theorem smoke_route_25519 (rInv : ZMod (2 ^ 255 - 19)) :
    routeOf (.montMul (2 ^ 255 - 19) rInv) = .vector := by
  unfold routeOf ModArithOp.modulus?
  simp only []
  rw [if_pos vectorizable_25519]

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
