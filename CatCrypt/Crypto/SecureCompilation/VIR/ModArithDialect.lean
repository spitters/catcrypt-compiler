/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Model
public import Mathlib.Data.ZMod.Basic

/-!
# ModArith VIR dialect (#482-1 — the L2 algebraic layer)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The single, shared modular-arithmetic dialect of the PrimeIR-style layered
crypto-IR stack. It is the **L2** level
between the abstract field math and the IR backends:

    EllipticCurve(L4) → Field(L3) → **ModArith(L2)** → {Vector | LowCT} → {jasmin | x86}

Today Montgomery is *re-derived per primitive* (fe25519, Pasta, BN254, P-256,
ML-KEM — 6+ separate derivations), and the #261/#477 widening-multiply +
carry-chain ops have no single home — they live ad hoc in `JasminDialect`. This
dialect gives the whole algebraic layer **one** verified home:

* `mod add/sub/neg/mul/reduce` — the residue-ring ops, denoting into `ZMod p`;
* **Montgomery** (`montMul`, `montReduce`), parametric over modulus `p` and the
  Montgomery constant `n′ = −p⁻¹ mod 2^64` — denoting into `ZMod p` as
  `a·b·R⁻¹` and `t·R⁻¹` respectively;
* **Solinas / Barrett** reduce (`solinasReduce`, `barrettReduce`) — fast reduces
  for special-form / generic primes, denoting to `· % p`;
* **Bernstein–Yang / safegcd inverse** (`byInverse`) — the divstep field inverse,
  denoting to `ZMod`'s native inverse `a⁻¹`;
* **batch inverse** (`batchInverse`, Montgomery's trick #481) — `n` inverses with
  one inversion + `3n` mults, denoting pointwise to `aᵢ⁻¹`;
* **Montgomery-domain inverse** (`montInverse`) — `x ↦ x⁻¹ · R²`, the residue
  whose Montgomery product with `x̃` is the Montgomery unit `R`;
* the **structural reinterprets** (`polyToTensor`, `polyFromTensor`,
  `residueEncode`, `residueDecode`) — the coefficient-vector ↔ tensor and
  residue ↔ fixed-width-bits maps, carrying no arithmetic;
* the **widening-multiply + carry-chain** ops (`mulHi`, `addCarryLo`,
  `addCarryHi` — the #261/#477 ops) — their single verified home, with the
  `BitVec` semantics **reused from the owned x86 model**
  (`X86Backend.mulHi` / `.addCarry`).

## Types (`ModArithTy`)

* `fp p`        — a residue-ring element, `⟦·⟧ = ZMod p`. The modulus lives in
                  the *type*, so a pass that mixes two moduli is ill-typed.
* `fpVec p n`   — `n` residue-ring elements (the batch-inverse / vectorised lane
                  shape), `⟦·⟧ = Fin n → ZMod p`.
* `word w`      — a `w`-bit machine word, `⟦·⟧ = BitVec w` (the carry/widening
                  layer; the bignum limbs of a `fp p` element).
* `carry`       — a 1-bit carry flag threading a carry chain, `⟦·⟧ = BitVec 1`.

The `fp`-vs-`word` split is the dialect's contribution: the *algebraic* ops
(`modMul`, `montMul`, `byInverse`, …) live at `fp p` and denote into `ZMod p`;
the *machine* ops (`mulHi`, `addCarry*`) live at `word w` and denote into
`BitVec`. The lowering (`ModArithToLower.lean`) connects them — a `montMul` at
`fp p` lowers to a CIOS schedule of `mulHi`/`addCarry*` at `word 64`.

## Denotation: every op into its `ZMod p` / bignum spec

This is the verification payoff. Each algebraic op denotes to the *abstract math*
(`ZMod p`), so the CatCrypt security realization ties connect **once per dialect
level** (structural) instead of per-primitive. The Montgomery ops denote with the
`R⁻¹` factor explicit, so `montMul a b = a·b·R⁻¹` is a definitional fact at the
dialect, not a re-proved obligation per curve.

## Pure-only + constant-time

Like `JasminDialect` / `LatticeDialect`, all op denotations are total pure
functions; no memory or sampling effect. **Every** ModArith op is
data-oblivious — the entire point of constant-time field arithmetic is that the
schedule is fixed and index-independent — so `ctSafe` is `true` for all ops
(see `§ CT predicate`). This is the L2 instance of the VIR `ctSafe` story
(`CTPredicate.lean`): the algebraic layer is CT by construction; the only
data-dependent constructs (variable-time `div`/table lookups) are *not* in the
op alphabet.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Types -/

/-- The ModArith dialect's value-type alphabet. The modulus `p` lives in the
    `fp`/`fpVec` types so a pass mixing two moduli is ill-typed; `word`/`carry`
    are the machine layer the algebraic ops lower onto. -/
inductive ModArithTy where
  /-- A residue-ring element mod `p`, `⟦·⟧ = ZMod p`. -/
  | fp (p : Nat)
  /-- `n` residue-ring elements mod `p` (the batch / lane shape). -/
  | fpVec (p n : Nat)
  /-- A `w`-bit machine word (the bignum-limb / carry-chain layer). -/
  | word (w : Nat)
  /-- A 1-bit carry flag threading a carry chain. -/
  | carry
  deriving DecidableEq

/-- Total denotation of `ModArithTy`. The algebraic types denote into `ZMod p`
    (the abstract field math); the machine types into `BitVec`. -/
@[reducible] instance : TyDenote ModArithTy where
  denote
    | .fp p => ZMod p
    | .fpVec p n => Fin n → ZMod p
    | .word w => BitVec w
    | .carry => BitVec 1

/-! ## 2. Concrete leaf functions

The algebraic leaves are `ZMod p`'s native operations (so the denotation is the
abstract field math); the Montgomery / Barrett / safegcd leaves carry the
relevant constant (`R⁻¹`, `n′`) explicitly. The machine leaves reuse the owned
x86 model (`X86Backend.Model`) byte-for-byte — `mulHi`/`addCarry` are *the same
functions* the Montgomery CIOS kernels run on, so the lowering tie is a direct
equality, not a re-derivation. -/

/-- Modular add: `ZMod p`'s native `+`. -/
@[reducible] def modAddF {p : Nat} (a b : ZMod p) : ZMod p := a + b

/-- Modular sub: `ZMod p`'s native `-`. -/
@[reducible] def modSubF {p : Nat} (a b : ZMod p) : ZMod p := a - b

/-- Modular negate: `ZMod p`'s native unary `-`. -/
@[reducible] def modNegF {p : Nat} (a : ZMod p) : ZMod p := -a

/-- Modular multiply: `ZMod p`'s native `*`. -/
@[reducible] def modMulF {p : Nat} (a b : ZMod p) : ZMod p := a * b

/-- Reduce a `Nat` (an unreduced product / accumulator) into `ZMod p`. This is
    the abstract spec of *every* concrete reduce (Solinas, Barrett, CIOS final
    subtract): the cast `(· : ZMod p)`, which is `· % p` on the canonical
    representative. -/
@[reducible] def modReduceF {p : Nat} (a : Nat) : ZMod p := (a : ZMod p)

/-- Nullary residue-ring constant: the fixed element `c : ZMod p`, independent of
    any input. This is the L2 home of a field/round constant — the single
    constant-producing op the residue-ring layer previously lacked (every other
    ModArith op takes at least one `fp`/`word` argument). -/
@[reducible] def modConstF {p : Nat} (c : ZMod p) : ZMod p := c

/-- Unary identity/copy on `fp p`: returns its single argument unchanged. The L2
    home of a **designated-output lane copy** — materializing a value as its own
    fresh binding (the shape a multi-output store ABI reads as one output slot).
    Distinct from `modConst` (nullary); `modCopy` is unary. -/
@[reducible] def modCopyF {p : Nat} (a : ZMod p) : ZMod p := a

/-- Montgomery multiply, denoted **into `ZMod p`** with the `R⁻¹` factor
    explicit: `montMulF rInv a b = a · b · R⁻¹` where `rInv = (R : ZMod p)⁻¹`
    is the dialect's Montgomery-radix-inverse parameter. The concrete CIOS
    kernel (`Bn254MontMulKernel`, …) realises exactly this value; making `R⁻¹`
    a denotation parameter means the abstract Montgomery identity is definitional
    here, not re-proved per curve. -/
@[reducible] def montMulF {p : Nat} (rInv : ZMod p) (a b : ZMod p) : ZMod p :=
  a * b * rInv

/-- Montgomery reduce: `montReduceF rInv t = t · R⁻¹`. The single-argument
    Montgomery step (REDC) denoted into `ZMod p`. -/
@[reducible] def montReduceF {p : Nat} (rInv : ZMod p) (t : ZMod p) : ZMod p :=
  t * rInv

/-- Bernstein–Yang / safegcd field inverse, denoted into `ZMod p` as `ZMod`'s
    native inverse `a⁻¹`. The divstep schedule (#258) is a *realisation* of this
    spec; the dialect op is the spec. -/
@[reducible] def byInverseF {p : Nat} (a : ZMod p) : ZMod p := a⁻¹

/-- Montgomery-domain inverse: `x ↦ x⁻¹ · rInv⁻¹ · rInv⁻¹` (`= x⁻¹ · R²`, since
    `rInv⁻¹ = R`). The residue whose Montgomery product with `x̃` is the
    Montgomery unit `R`, under the `montMulF` / `montReduceF` convention. -/
@[reducible] def montInverseF {p : Nat} (rInv x : ZMod p) : ZMod p :=
  x⁻¹ * rInv⁻¹ * rInv⁻¹

/-- Coefficient-vector-to-tensor reinterpret: a degree-`< n` coefficient-form
    polynomial over `Z_p` viewed as its rank-1 length-`n` coefficient tensor.
    Both sides are the coefficient vector, so the map is the identity. -/
@[reducible] def polyToTensorF (p n : Nat) (v : Fin n → ZMod p) : Fin n → ZMod p := v

/-- Tensor-to-coefficient-vector reinterpret, inverse to `polyToTensorF`; again
    the identity on the coefficient vector. -/
@[reducible] def polyFromTensorF (p n : Nat) (v : Fin n → ZMod p) : Fin n → ZMod p := v

/-- Residue-to-bits reinterpret: a residue `a : ZMod p` as its canonical
    fixed-width `BitVec w` storage, the little-endian bits of `a.val`. -/
@[reducible] def residueEncodeF (p w : Nat) (a : ZMod p) : BitVec w :=
  BitVec.ofNat w a.val

/-- Bits-to-residue reinterpret: a `BitVec w` storage `b` as the residue
    `b.toNat : ZMod p`, inverse to `residueEncodeF` when the storage neither
    truncates the modulus nor holds a non-canonical value. -/
@[reducible] def residueDecodeF (p w : Nat) (b : BitVec w) : ZMod p :=
  (b.toNat : ZMod p)

/-- Batch inverse (Montgomery's trick, #481): invert all `n` lanes. Denoted
    pointwise to `aᵢ⁻¹` — the abstract spec the prefix-product schedule (one
    inversion + `3n` mults) realises. -/
@[reducible] def batchInverseF {p n : Nat} (a : Fin n → ZMod p) : Fin n → ZMod p :=
  fun i => (a i)⁻¹

/-! ### Machine layer — reused from the owned x86 model (#261/#477)

These are the **single verified home** for the widening-multiply + carry-chain
ops. The denotations are `X86Backend.mulHi` / `.addCarry` *unchanged* —
the same functions the CIOS Montgomery kernels run on — so the lowering tie
(`montMul → CIOS schedule of these ops`) is a direct equality. -/

/-- High word of the widening product `a * b` (the `hi` output of `MULX`),
    reused verbatim from the owned x86 model. The low word is `modMul`-at-`word`
    (`a * b`); together they are MULX's `(hi, lo)`. (#477) -/
@[reducible] def mulHiF {w : Nat} (a b : BitVec w) : BitVec w :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi a b

/-- The data word of one carry-chain add `a + b + cin` (the data effect of
    `ADCX`/`ADOX`): `a + b + cin`. The carry-in is a 1-bit word. (#477) -/
@[reducible] def addCarryLoF {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec w :=
  a + b + BitVec.ofNat w cin.toNat

/-- The carry-out bit of one carry-chain add `a + b + cin` (the propagated carry
    of `ADCX`/`ADOX`): reuses the owned model's `addCarry` predicate, packaged as
    a `BitVec 1` so it threads into the next limb's carry-in. (#477) -/
@[reducible] def addCarryHiF {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec 1 :=
  if CatCrypt.Crypto.SecureCompilation.X86Backend.addCarry a b (cin = 1)
  then 1 else 0

/-! ## 3. Op tags -/

/-- Operation tags for the ModArith dialect. The algebraic ops (`modAdd` …
    `batchInverse`) live at `fp`/`fpVec` and denote into `ZMod p`; the machine
    ops (`mulHi`/`addCarryLo`/`addCarryHi`) live at `word`/`carry` and denote
    into `BitVec` (the #261/#477 ops, here getting their single home). -/
inductive ModArithOp where
  /-- Modular add `a + b : fp p`. -/
  | modAdd (p : Nat)
  /-- Modular sub `a - b : fp p`. -/
  | modSub (p : Nat)
  /-- Modular negate `-a : fp p`. -/
  | modNeg (p : Nat)
  /-- Modular multiply `a * b : fp p`. -/
  | modMul (p : Nat)
  /-- Reduce a machine word into `fp p` (the abstract reduce). Arg is a
      `word w`; result is `fp p` (cast of `.toNat`). -/
  | modReduce (p w : Nat)
  /-- Nullary residue-ring constant `c : fp p` (sig `[]`). The L2 home of a
      field/round constant. -/
  | modConst (p : Nat) (c : ZMod p)
  /-- Unary identity/copy `a : fp p` (sig `[fp p]`). Materializes a
      designated-output lane as its own binding. -/
  | modCopy (p : Nat)
  /-- Montgomery multiply `a·b·R⁻¹ : fp p`, carrying the radix-inverse `rInv`. -/
  | montMul (p : Nat) (rInv : ZMod p)
  /-- Montgomery reduce `t·R⁻¹ : fp p`. -/
  | montReduce (p : Nat) (rInv : ZMod p)
  /-- Solinas (fast special-prime) reduce of a `word w` into `fp p`. Denotes to
      the same spec as `modReduce` (the cast); the *schedule* is the Solinas
      shift-add chain, attached at lowering. -/
  | solinasReduce (p w : Nat)
  /-- Barrett (generic-prime) reduce of a `word w` into `fp p`. Same spec as
      `modReduce`; the schedule is the Barrett `μ`-multiply. -/
  | barrettReduce (p w : Nat)
  /-- Bernstein–Yang / safegcd field inverse `a⁻¹ : fp p`. -/
  | byInverse (p : Nat)
  /-- Batch inverse `(aᵢ⁻¹)ᵢ : fpVec p n` (Montgomery's trick, #481). -/
  | batchInverse (p n : Nat)
  /-- Montgomery-domain inverse `x⁻¹ · R² : fp p`, carrying the radix-inverse
      `rInv` (prime-ir `mod_arith.mont_inverse`). Folded in from
      `montInverseDialect` rather than kept as a dialect of its own: a `Com`
      carries ops from one dialect only, so an op in a separate dialect can
      never appear beside `montMul`. A coproduct
      `modArithDialect ⊕ montInverseDialect` with an injection was the
      alternative; the carriers already coincide (`MontInverseTy.fp p` and
      `ModArithTy.fp p` both denote `ZMod p`). -/
  | montInverse (p : Nat) (rInv : ZMod p)
  /-- Coefficient-vector-to-tensor reinterpret `fpVec p n → fpVec p n`
      (prime-ir `poly.to_tensor`). Folded in from `structDialect`, whose four
      types all land in `ModArithTy`; the one-dialect indexing of `Com` is what
      rules out keeping it separate, and a dialect coproduct with an injection
      was the alternative. -/
  | polyToTensor (p n : Nat)
  /-- Tensor-to-coefficient-vector reinterpret `fpVec p n → fpVec p n`
      (prime-ir `poly.from_tensor`), folded in from `structDialect` with
      `polyToTensor`. -/
  | polyFromTensor (p n : Nat)
  /-- Residue-to-bits reinterpret `fp p → word w` (prime-ir `field.bitcast` /
      `mod_arith.bitcast`, encode direction), folded in from `structDialect`
      (`StructTy.residue p` is `fp p`, `StructTy.bits w` is `word w`). -/
  | residueEncode (p w : Nat)
  /-- Bits-to-residue reinterpret `word w → fp p` (prime-ir `field.bitcast` /
      `mod_arith.bitcast`, decode direction), folded in from `structDialect`
      with `residueEncode`.

      It shares `modReduce`'s signature and denotation, and is distinct for the
      reason `solinasReduce` and `barrettReduce` are: the spec coincides while the
      intent does not. `modReduce` reduces a word; this reinterprets bits already
      known to lie below `p`, and `structDialect`'s round-trip laws hold only
      under that range condition. -/
  | residueDecode (p w : Nat)
  /-- High word of the widening multiply (the `hi` of `MULX`): `[word w, word w]
      → word w`. (#477) -/
  | mulHi (w : Nat)
  /-- Carry-chain add **data** word `a + b + cin` (`ADCX`/`ADOX` data):
      `[word w, word w, carry] → word w`. (#477) -/
  | addCarryLo (w : Nat)
  /-- Carry-chain add **carry-out** bit (`ADCX`/`ADOX` carry):
      `[word w, word w, carry] → carry`. (#477) -/
  | addCarryHi (w : Nat)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The ModArith dialect: `Op` is `ModArithOp`, `Ty` is `ModArithTy`. -/
@[reducible] def modArithDialect : Dialect :=
  { Op := ModArithOp, Ty := ModArithTy }

/-! ## 5. Op signatures (arg types + return type) -/

instance : DialectSignature modArithDialect where
  sig op := match op with
    | .modAdd p => [.fp p, .fp p]
    | .modSub p => [.fp p, .fp p]
    | .modNeg p => [.fp p]
    | .modMul p => [.fp p, .fp p]
    | .modReduce _ w => [.word w]
    | .modConst _ _ => []
    | .modCopy p => [.fp p]
    | .montMul p _ => [.fp p, .fp p]
    | .montReduce p _ => [.fp p]
    | .solinasReduce _ w => [.word w]
    | .barrettReduce _ w => [.word w]
    | .byInverse p => [.fp p]
    | .batchInverse p n => [.fpVec p n]
    | .montInverse p _ => [.fp p]
    | .polyToTensor p n => [.fpVec p n]
    | .polyFromTensor p n => [.fpVec p n]
    | .residueEncode p _ => [.fp p]
    | .residueDecode _ w => [.word w]
    | .mulHi w => [.word w, .word w]
    | .addCarryLo w => [.word w, .word w, .carry]
    | .addCarryHi w => [.word w, .word w, .carry]
  ret op := match op with
    | .modAdd p => .fp p
    | .modSub p => .fp p
    | .modNeg p => .fp p
    | .modMul p => .fp p
    | .modReduce p _ => .fp p
    | .modConst p _ => .fp p
    | .modCopy p => .fp p
    | .montMul p _ => .fp p
    | .montReduce p _ => .fp p
    | .solinasReduce p _ => .fp p
    | .barrettReduce p _ => .fp p
    | .byInverse p => .fp p
    | .batchInverse p n => .fpVec p n
    | .montInverse p _ => .fp p
    | .polyToTensor p n => .fpVec p n
    | .polyFromTensor p n => .fpVec p n
    | .residueEncode _ w => .word w
    | .residueDecode p _ => .fp p
    | .mulHi w => .word w
    | .addCarryLo w => .word w
    | .addCarryHi _ => .carry

/-! ## 6. Op denotation -/

instance modArithDenote : DialectDenote modArithDialect where
  denote op := match op with
    | .modAdd _ => fun args => modAddF args.head args.tail.head
    | .modSub _ => fun args => modSubF args.head args.tail.head
    | .modNeg _ => fun args => modNegF args.head
    | .modMul _ => fun args => modMulF args.head args.tail.head
    | .modReduce _ _ => fun args => modReduceF (args.head : BitVec _).toNat
    | .modConst _ c => fun _ => modConstF c
    | .modCopy _ => fun args => modCopyF args.head
    | .montMul _ rInv => fun args => montMulF rInv args.head args.tail.head
    | .montReduce _ rInv => fun args => montReduceF rInv args.head
    | .solinasReduce _ _ => fun args => modReduceF (args.head : BitVec _).toNat
    | .barrettReduce _ _ => fun args => modReduceF (args.head : BitVec _).toNat
    | .byInverse _ => fun args => byInverseF args.head
    | .batchInverse _ _ => fun args => batchInverseF args.head
    | .montInverse _ rInv => fun args => montInverseF rInv args.head
    | .polyToTensor p n => fun args => polyToTensorF p n args.head
    | .polyFromTensor p n => fun args => polyFromTensorF p n args.head
    | .residueEncode p w => fun args => residueEncodeF p w args.head
    | .residueDecode p w => fun args => residueDecodeF p w args.head
    | .mulHi _ => fun args => mulHiF args.head args.tail.head
    | .addCarryLo _ => fun args => addCarryLoF args.head args.tail.head args.tail.tail.head
    | .addCarryHi _ => fun args => addCarryHiF args.head args.tail.head args.tail.tail.head

/-! ## 7. Constant-time predicate (L2 instance of `CTPredicate.lean`)

Every ModArith op is data-oblivious: the schedule is fixed (no `ite` on data,
no data-dependent memory index — the only data-dependent constructs would be
variable-time `div` or table lookups, which are *not* in the op alphabet). So
`ctSafe` is `true` for all ops, mirroring `CTPredicate.ctSafe`'s shape but with
no non-CT constructor to exclude. -/

/-- Per-op CT predicate: every ModArith op is constant-time (the algebraic layer
    is CT by construction — no data-dependent branch or index). -/
def ModArithOp.ctSafe : ModArithOp → Bool
  | _ => true

@[simp] theorem ModArithOp.ctSafe_all (op : ModArithOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (e : Expr modArithDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (e : Expr modArithDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is. Since all ModArith ops are CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt modArithDialect} {t : ModArithTy} :
    Com modArithDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every ModArith program is constant-time. This is the
    L2-level realisation of the VIR CT-safety guarantee: the algebraic layer
    introduces no data-dependent control flow or memory index, so CT-safety is
    free — it does not have to be re-checked per primitive. -/
theorem ctSafeCom_all {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-- Propositional form, decidable (trivially, by `ctSafeCom_all`). -/
def ctSafePropCom {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 8. Algebraic denotation facts (the once-per-dialect ties)

These hold **definitionally** because the op denotations are `ZMod p`'s native
operations. The point is that they are stated *once* at the dialect, rather than
re-proved per migrated primitive. -/

/-- `modMul` denotes to `ZMod p` multiplication. -/
theorem modMul_denote {p : Nat} (a b : ZMod p) :
    modArithDenote.denote (.modMul p) (.cons a (.cons b .nil)) = a * b := rfl

/-- `modConst` denotes to its carried constant `c`, independent of the (empty)
    argument vector. -/
theorem modConst_denote {p : Nat} (c : ZMod p) :
    modArithDenote.denote (.modConst p c) .nil = c := rfl

/-- `montMul` denotes to `a · b · R⁻¹` — the abstract Montgomery identity, here
    definitional (the `R⁻¹` factor is the op's denotation parameter). -/
theorem montMul_denote {p : Nat} (rInv a b : ZMod p) :
    modArithDenote.denote (.montMul p rInv) (.cons a (.cons b .nil)) = a * b * rInv := rfl

/-- `byInverse` denotes to `ZMod`'s native inverse. -/
theorem byInverse_denote {p : Nat} (a : ZMod p) :
    modArithDenote.denote (.byInverse p) (.cons a .nil) = a⁻¹ := rfl

/-- `batchInverse` denotes pointwise to the inverse — the batch is the abstract
    `(aᵢ⁻¹)ᵢ`, independent of the (one-inversion) schedule that realises it. -/
theorem batchInverse_denote {p n : Nat} (a : Fin n → ZMod p) (i : Fin n) :
    modArithDenote.denote (.batchInverse p n) (.cons a .nil) i = (a i)⁻¹ := rfl

/-- `mulHi` denotes to the owned x86 model's `mulHi` — the #477 widening op's
    single home, tied directly to the kernel-level function. -/
theorem mulHi_denote {w : Nat} (a b : BitVec w) :
    modArithDenote.denote (.mulHi w) (.cons a (.cons b .nil))
      = CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi a b := rfl

/-! ## 9. Smoke test

A tiny two-op `Com modArithDialect` over `ZMod 7`: `let c = a * b; ret c`.
On `a = 5, b = 4 : ZMod 7`, `c = 20 = 6 (mod 7)`. -/

/-- Two-op smoke program: one `montMul` (with `rInv = 1`, i.e. plain product)
    over `[fp 7, fp 7]`. -/
def smokeProg : Com modArithDialect [.fp 7, .fp 7] (.fp 7) :=
  .var (.mk (.montMul 7 1) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The smoke program denotes to `a * b * 1 = a * b` over `ZMod 7`; on
    `a = 5, b = 4` that is `20 = 6 (mod 7)`. -/
example :
    smokeProg.denote (.cons (5 : ZMod 7) (.cons (4 : ZMod 7) .nil)) = (6 : ZMod 7) := by
  rfl

/-- Smoke: the carry/widening op is in scope and denotes to the owned model. -/
example : modArithDenote.denote (.mulHi 8) (.cons (200 : BitVec 8) (.cons (3 : BitVec 8) .nil))
    = CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi (200 : BitVec 8) 3 := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
