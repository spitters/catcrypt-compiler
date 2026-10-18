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
# ModArith VIR dialect (the L2 algebraic layer)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The single, shared modular-arithmetic dialect of the PrimeIR-style layered
crypto-IR stack. It is the **L2** level
between the abstract field math and the IR backends:

    EllipticCurve(L4) → Field(L3) → **ModArith(L2)** → {Vector | LowCT} → {jasmin | x86}

Montgomery arithmetic is otherwise derived per primitive (fe25519, Pasta, BN254,
P-256, ML-KEM), and the widening-multiply + carry-chain ops are otherwise
scattered in `JasminDialect`. This dialect gives the whole algebraic layer **one**
verified home:

* `mod add/sub/neg/mul/reduce` — the residue-ring ops, denoting into `ZMod p`;
* **Montgomery** (`montMul`, `montReduce`), parametric over modulus `p` and the
  Montgomery constant `n′ = −p⁻¹ mod 2^64` — denoting into `ZMod p` as
  `a·b·R⁻¹` and `t·R⁻¹` respectively;
* **Solinas / Barrett** reduce (`solinasReduce`, `barrettReduce`) — fast reduces
  for special-form / generic primes, denoting to `· % p`;
* **Bernstein–Yang / safegcd inverse** (`byInverse`) — the divstep field inverse,
  denoting to `ZMod`'s native inverse `a⁻¹`;
* **batch inverse** (`batchInverse`, Montgomery's trick) — `n` inverses with
  one inversion + `3n` mults, denoting pointwise to `aᵢ⁻¹`;
* **Montgomery-domain inverse** (`montInverse`) — `x ↦ x⁻¹ · R²`, the residue
  whose Montgomery product with `x̃` is the Montgomery unit `R`;
* the **structural reinterprets** (`polyToTensor`, `polyFromTensor`,
  `residueEncode`, `residueDecode`) — the coefficient-vector ↔ tensor and
  residue ↔ fixed-width-bits maps, carrying no arithmetic;
* the **widening-multiply + carry-chain** ops (`mulHi`, `addCarryLo`,
  `addCarryHi`) — their single verified home, with the
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

## Pure denotations

Like `JasminDialect` / `LatticeDialect`, all op denotations are total pure
functions; no memory or sampling effect. The op alphabet contains no
variable-time `div` and no table lookup. The dialect carries no constant-time
predicate; constant time is a property of the code a program lowers to
(`Dialects.CryptoDialectCTLeak.catCT` at the dialect level,
`DecodedCT.bytesCTCheck_sound` at the bytes).

## Main results

* `modArithDialect` with its signature and denotation `modArithDenote`;
* the denotation facts `modMul_denote`, `modConst_denote`, `montMul_denote`,
  `byInverse_denote`, `batchInverse_denote` and `mulHi_denote`.
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
    constant-producing op of the residue-ring layer (every other
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
    native inverse `a⁻¹`. The divstep schedule is a *realisation* of this
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

/-- Batch inverse (Montgomery's trick): invert all `n` lanes. Denoted
    pointwise to `aᵢ⁻¹` — the abstract spec the prefix-product schedule (one
    inversion + `3n` mults) realises. -/
@[reducible] def batchInverseF {p n : Nat} (a : Fin n → ZMod p) : Fin n → ZMod p :=
  fun i => (a i)⁻¹

/-! ### Machine layer — reused from the owned x86 model

These are the **single verified home** for the widening-multiply + carry-chain
ops. The denotations are `X86Backend.mulHi` / `.addCarry` *unchanged* —
the same functions the CIOS Montgomery kernels run on — so the lowering tie
(`montMul → CIOS schedule of these ops`) is a direct equality. -/

/-- High word of the widening product `a * b` (the `hi` output of `MULX`),
    reused verbatim from the owned x86 model. The low word is `modMul`-at-`word`
    (`a * b`); together they are MULX's `(hi, lo)`. -/
@[reducible] def mulHiF {w : Nat} (a b : BitVec w) : BitVec w :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi a b

/-- The data word of one carry-chain add `a + b + cin` (the data effect of
    `ADCX`/`ADOX`): `a + b + cin`. The carry-in is a 1-bit word. -/
@[reducible] def addCarryLoF {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec w :=
  a + b + BitVec.ofNat w cin.toNat

/-- The carry-out bit of one carry-chain add `a + b + cin` (the propagated carry
    of `ADCX`/`ADOX`): reuses the owned model's `addCarry` predicate, packaged as
    a `BitVec 1` so it threads into the next limb's carry-in. -/
@[reducible] def addCarryHiF {w : Nat} (a b : BitVec w) (cin : BitVec 1) : BitVec 1 :=
  if CatCrypt.Crypto.SecureCompilation.X86Backend.addCarry a b (cin = 1)
  then 1 else 0

/-! ## 3. Op tags -/

/-- Operation tags for the ModArith dialect. The algebraic ops (`modAdd` …
    `batchInverse`) live at `fp`/`fpVec` and denote into `ZMod p`; the machine
    ops (`mulHi`/`addCarryLo`/`addCarryHi`) live at `word`/`carry` and denote
    into `BitVec` (their single home). -/
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
  /-- Batch inverse `(aᵢ⁻¹)ᵢ : fpVec p n` (Montgomery's trick). -/
  | batchInverse (p n : Nat)
  /-- Montgomery-domain inverse `x⁻¹ · R² : fp p`, carrying the radix-inverse
      `rInv` (prime-ir `mod_arith.mont_inverse`). An op of this dialect
      rather than of a dialect of its own: a `Com`
      carries ops from one dialect only, so an op in a separate dialect can
      never appear beside `montMul`. A dialect coproduct with an injection is
      the alternative; the carriers coincide (`MontInverseTy.fp p` and
      `ModArithTy.fp p` both denote `ZMod p`). -/
  | montInverse (p : Nat) (rInv : ZMod p)
  /-- Coefficient-vector-to-tensor reinterpret `fpVec p n → fpVec p n`
      (prime-ir `poly.to_tensor`). The structural reinterprets' four types all
      land in `ModArithTy`; the one-dialect indexing of `Com` rules out a
      separate dialect, and a dialect coproduct with an injection is the
      alternative. -/
  | polyToTensor (p n : Nat)
  /-- Tensor-to-coefficient-vector reinterpret `fpVec p n → fpVec p n`
      (prime-ir `poly.from_tensor`), the reverse direction of `polyToTensor`. -/
  | polyFromTensor (p n : Nat)
  /-- Residue-to-bits reinterpret `fp p → word w` (prime-ir `field.bitcast` /
      `mod_arith.bitcast`, encode direction). -/
  | residueEncode (p w : Nat)
  /-- Bits-to-residue reinterpret `word w → fp p` (prime-ir `field.bitcast` /
      `mod_arith.bitcast`, decode direction), the reverse direction of `residueEncode`.

      It shares `modReduce`'s signature and denotation, and is distinct for the
      reason `solinasReduce` and `barrettReduce` are: the spec coincides while the
      intent does not. `modReduce` reduces a word; this reinterprets bits already
      known to lie below `p`, and `structDialect`'s round-trip laws hold only
      under that range condition. -/
  | residueDecode (p w : Nat)
  /-- High word of the widening multiply (the `hi` of `MULX`): `[word w, word w]
      → word w`. -/
  | mulHi (w : Nat)
  /-- Carry-chain add **data** word `a + b + cin` (`ADCX`/`ADOX` data):
      `[word w, word w, carry] → word w`. -/
  | addCarryLo (w : Nat)
  /-- Carry-chain add **carry-out** bit (`ADCX`/`ADOX` carry):
      `[word w, word w, carry] → carry`. -/
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

/-! ## 7. Algebraic denotation facts (the once-per-dialect ties)

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

/-- `mulHi` denotes to the owned x86 model's `mulHi` — the widening op's
    single home, tied directly to the kernel-level function. -/
theorem mulHi_denote {w : Nat} (a b : BitVec w) :
    modArithDenote.denote (.mulHi w) (.cons a (.cons b .nil))
      = CatCrypt.Crypto.SecureCompilation.X86Backend.mulHi a b := rfl

/-! ## 8. Smoke test

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

/-! ## 9. Representation annotations

prime-ir's `!mod_arith.int<p : iW, true>` carries the storage width `W` of the
modulus and the Montgomery flag. A representation map `ρ` assigns each modulus a
`ModArithRepr`; `modArithDialectAt ρ` is `modArithDialect` with its type alphabet
indexed by `ρ`, so that the type of a program records the representation of each of
its moduli. The lowerings read `ρ` from that type.

The index is a reducible annotation: `ModArithTyAt ρ` and `modArithDialectAt ρ`
unfold to `ModArithTy` and `modArithDialect`, so the constructors, the signatures,
the instances and the `ZMod p` denotation are those of the unannotated dialect, and
`annotateCom`/`unannotateCom` are identities on the program and its denotation. The
representation is a property of the lowering, as `DESIGN.md` states. -/

/-- The representation of a modulus: its storage width and its Montgomery flag, each
    `none` where the program leaves it to the lowering. -/
structure ModArithRepr where
  /-- The storage width `W` of the modulus, printed as `: iW`. -/
  width : Option Nat := none
  /-- Whether residues mod the modulus are stored in Montgomery form. -/
  mont : Option Bool := none
  deriving DecidableEq, Repr, Inhabited

/-- A representation per modulus. -/
abbrev ModArithReprMap : Type := Nat → ModArithRepr

/-- The representation map that fixes nothing: every width and flag is left to the
    lowering. -/
def ModArithReprMap.unfixed : ModArithReprMap := fun _ => {}

/-- The type alphabet of `modArithDialect` indexed by the representation map `ρ`:
    `fp p` and `fpVec p n` are stored as `ρ p` fixes. -/
abbrev ModArithTyAt (_ρ : ModArithReprMap) : Type := ModArithTy

/-- The representation a type carries: `ρ p` at `fp p` and `fpVec p n`, none at the
    machine types. -/
def ModArithTyAt.repr {ρ : ModArithReprMap} : ModArithTyAt ρ → Option ModArithRepr
  | .fp p => some (ρ p)
  | .fpVec p _ => some (ρ p)
  | .word _ => none
  | .carry => none

/-- `modArithDialect` with its types indexed by the representation map `ρ`. -/
@[reducible] def modArithDialectAt (_ρ : ModArithReprMap) : Dialect :=
  { Op := ModArithOp, Ty := ModArithTyAt _ρ }

/-- The dialect indexed by the map that fixes nothing is `modArithDialect`. -/
theorem modArithDialectAt_unfixed : modArithDialectAt .unfixed = modArithDialect := rfl

/-- An annotated type denotes what the unannotated type denotes: `ZMod p` at `fp p`. -/
theorem denote_fp_at (ρ : ModArithReprMap) (p : Nat) :
    TyDenote.denote (ModArithTy.fp p : ModArithTyAt ρ) = ZMod p := rfl

/-- A program of `modArithDialect` annotated with the representation map `ρ`. -/
def annotateCom (ρ : ModArithReprMap) {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (c : Com modArithDialect Γ t) : Com (modArithDialectAt ρ) Γ t := c

/-- The program of `modArithDialect` underlying an annotated program. -/
def unannotateCom {ρ : ModArithReprMap} {Γ : Ctxt (modArithDialectAt ρ)}
    {t : ModArithTyAt ρ} (c : Com (modArithDialectAt ρ) Γ t) :
    Com modArithDialect Γ t := c

/-- The annotation does not change the denotation. -/
theorem denote_annotateCom (ρ : ModArithReprMap) {Γ : Ctxt modArithDialect}
    {t : ModArithTy} (c : Com modArithDialect Γ t) (V : Ctxt.Valuation Γ) :
    (annotateCom ρ c).denote V = c.denote V := rfl

/-- Removing the annotation does not change the denotation. -/
theorem denote_unannotateCom {ρ : ModArithReprMap} {Γ : Ctxt (modArithDialectAt ρ)}
    {t : ModArithTyAt ρ} (c : Com (modArithDialectAt ρ) Γ t) (V : Ctxt.Valuation Γ) :
    (unannotateCom c).denote V = c.denote V := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
