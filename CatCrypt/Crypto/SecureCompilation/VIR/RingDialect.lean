/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.ChineseRemainder
public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttBasemul

/-!
# Ring dialect — RNS quotient rings `Z_Q[X]/(X^N + 1)`

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

The counterpart of prime-ir's `ring` dialect (`fractalyze/prime-ir`,
`prime_ir/Dialect/Ring/IR/Ring{Ops,Types}.td`). Its type `!ring.rq<moduli, N,
storage, domain>` is the ring `R_Q = Z_Q[X]/(X^N + 1)` with `Q` the product of
the pairwise coprime `moduli`, written in the coefficient basis or in the fully
split evaluation basis. The storage layout is a limb-major `[L, N]` array of
residues, one row per modulus.

Here `RingTy.rq ms n w d` denotes that array, `Limbs ms n`: row `i` holds `N`
residues in `ZMod (ms.get i)`. The storage width `w` and the basis `d` are type
indices that the denotation ignores, except that `mul` is typed at the
evaluation basis and `rescale`/`baseConvert` at the coefficient basis, as the
upstream verifiers require.

## Main definitions

* `Limbs ms n` — the residue array of an element of `R_Q` in the basis `ms`.
* `addF`, `subF`, `negF`, `mulF` — the per-limb, per-position ring operations.
* `autoCoeffF g`, `autoEvalF g` — the Galois automorphism `X ↦ X^g` in the
  coefficient basis (a signed coefficient permutation) and in the evaluation
  basis (a slot permutation), with the index maps of upstream's lowering.
* `rescaleF` — exact division by the dropped trailing modulus.
* `baseConvertF` — fast basis conversion (no `-vQ` correction).
* `fromTensorF`, `toTensorF`, `limbsOfHVector` — the structural conversions.
* `rowLanes`, `nttF` — a row as a lane function, and the per-limb negacyclic NTT
  with a layer count, the coefficient-to-evaluation conversion of `R_Q`.
* `inttF` — its inverse: per limb, the Gentleman–Sande layers and the scaling.
* `negaMulF`, `basemulF` — the product of `R_Q` in the coefficient basis, and the
  blockwise product of the evaluation form after `L` layers.
* `RingTy` / `RingOp` / `ringDialect` — the dialect, its signature and its
  denotation.
* `ofInts ms c` — the residues of an integer coefficient vector in the basis `ms`.

## Main results

* `addF_ofInts`, `subF_ofInts`, `negF_ofInts`, `mulF_ofInts` — the limb
  operations are the integer operations read through `ofInts`.
* `ofInts_eq_iff` — for a pairwise coprime basis, `ofInts` identifies exactly
  the vectors congruent modulo `Q = ms.prod`, so `Limbs ms n` represents
  `(Z_Q)^N` faithfully.
* `rescaleF_ofInts` — `rescale` sends the residues of `c` in `ms ++ [qL]` to the
  residues of `(c - c mod qL) / qL` in `ms`, when `qL` is coprime to every
  modulus of `ms`.
* `autoEvalF_one`, `autoCoeffF_one` — the automorphism at `g = 1` is the identity.
* `toTensorF_fromTensorF`, `fromTensorF_toTensorF` — the tensor conversions are
  mutually inverse on in-range words and for moduli that fit the storage width.
* `ringDialect_ctSafe_all` — every op of the dialect is data-oblivious.
* `ntt_denote`, `lowerNega_denote` — the `ntt` op denotes `nttF`, and row `i` of
  it is the `fieldDialect` program `NegacyclicNttTemplate.nttProg` at the
  parameter record of limb `i`.
* `intt_denote`, `lowerIntt_denote` — the same for `intt` and
  `NegacyclicNttTemplate.inttProg`.
* `inttF_nttF`, `nttF_inttF` — under the per-limb side conditions `NttParams.Ok`
  and `ScaleOk`, `intt` and `ntt` are mutually inverse.
* `basemul_denote`, `nttF_negaMulF`, `basemulF_eq_mulF` — `basemul` denotes
  `basemulF`, `ntt` carries the product of `R_Q` to it, and at `L = logN` it is
  `mul`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RingDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Bases and residue arrays -/

/-- The CRT basis a ring value is written in: coefficients or evaluations at
    the primitive `2N`-th roots of unity (upstream `Ring_Domain`). -/
inductive Domain where
  /-- The coefficient basis. -/
  | coeff
  /-- The fully split evaluation basis. -/
  | eval
  deriving DecidableEq, Repr

/-- The residue array of an element of `R_Q` in the RNS basis `ms`: row `i`
    holds `n` residues modulo `ms.get i`. -/
abbrev Limbs (ms : List Nat) (n : Nat) : Type :=
  (i : Fin ms.length) → Fin n → ZMod (ms.get i)

variable {ms : List Nat} {n : Nat}

/-- Ring addition, per limb and per position. -/
def addF (x y : Limbs ms n) : Limbs ms n := fun i j => x i j + y i j

/-- Ring subtraction, per limb and per position. -/
def subF (x y : Limbs ms n) : Limbs ms n := fun i j => x i j - y i j

/-- Ring negation, per limb and per position. -/
def negF (x : Limbs ms n) : Limbs ms n := fun i j => -x i j

/-- The pointwise product, per limb and per position. In the evaluation basis
    this is the product of `R_Q`. -/
def mulF (x y : Limbs ms n) : Limbs ms n := fun i j => x i j * y i j

/-- Row `i` of a residue array as a lane function, zero past the last position. -/
def rowLanes (x : Limbs ms n) (i : Fin ms.length) (k : Nat) : ZMod (ms.get i) :=
  if h : k < n then x i ⟨k, h⟩ else 0

/-- The negacyclic NTT of length `2 ^ logN` with `L` merged-twiddle layers, per
    limb: row `i` is `NegacyclicNttTemplate.nttSpec` at the root `psis.getD i 0`
    modulo `ms.get i`.  At `L = logN` the result is the fully split evaluation
    basis; at `L < logN` position `c · 2 ^ (logN - L) + t` holds coefficient `t`
    of the residue modulo `X ^ (2 ^ (logN - L)) - ψ ^ (2 · BitRev_L c + 1)`. -/
def nttF (ms : List Nat) (logN L : Nat) (psis : List Nat) (x : Limbs ms (2 ^ logN)) :
    Limbs ms (2 ^ logN) := fun i j =>
  NegacyclicNttTemplate.nttSpec ((psis.getD i 0 : Nat) : ZMod (ms.get i)) L logN
    (rowLanes x i) j

/-- The inverse of `nttF`, per limb: row `i` is `NegacyclicNttTemplate.inttSpec`,
    the `L` Gentleman–Sande layers at the root `psis.getD i 0` followed by the
    scaling by `scales.getD i 0`, modulo `ms.get i`. -/
def inttF (ms : List Nat) (logN L : Nat) (psis scales : List Nat) (x : Limbs ms (2 ^ logN)) :
    Limbs ms (2 ^ logN) := fun i j =>
  NegacyclicNttTemplate.inttSpec ((psis.getD i 0 : Nat) : ZMod (ms.get i)) L logN
    ((scales.getD i 0 : Nat) : ZMod (ms.get i)) (rowLanes x i) j

/-- The product of `R_Q` in the coefficient basis, per limb: the negacyclic
    product `NegacyclicNttTemplate.negaMul` of length `2 ^ logN`. -/
def negaMulF (logN : Nat) (x y : Limbs ms (2 ^ logN)) : Limbs ms (2 ^ logN) := fun i j =>
  NegacyclicNttTemplate.negaMul (2 ^ logN) (rowLanes x i) (rowLanes y i) j

/-- The product of the evaluation form after `L` layers, per limb: the product in
    `ZMod q [X]/(X ^ B - γ_c)` within every block of length `B = 2 ^ (logN - L)`,
    `NegacyclicNttTemplate.blockMul` at the block roots of `psis.getD i 0`.  At
    `L = logN` it is `mulF` (`basemulF_eq_mulF`). -/
def basemulF (logN L : Nat) (psis : List Nat) (x y : Limbs ms (2 ^ logN)) :
    Limbs ms (2 ^ logN) := fun i j =>
  NegacyclicNttTemplate.blockMul (2 ^ (logN - L))
    (NegacyclicNttTemplate.blockRoot ((psis.getD i 0 : Nat) : ZMod (ms.get i)) L)
    (rowLanes x i) (rowLanes y i) j

/-- The automorphism `X ↦ X^g` in the coefficient basis: coefficient `k` moves
    to position `g·k mod N`, negated when `g·k mod 2N ≥ N` (the wrap
    `X^N = -1`). Written as a sum over source positions; for odd `g` and `N` a
    power of two exactly one source position contributes. -/
def autoCoeffF (g : Nat) (x : Limbs ms n) : Limbs ms n := fun i j =>
  ∑ k : Fin n,
    if (g * k.val) % n = j.val then
      (if n ≤ (g * k.val) % (2 * n) then -x i k else x i k)
    else 0

/-- The automorphism `X ↦ X^g` in the evaluation basis: slot `j` evaluates at
    `ψ^(2j+1)`, so output slot `j` reads input slot `r / 2` with
    `r = g·(2j+1) mod 2N`. For odd `g` the residue `r` is odd and `r / 2` is
    upstream's `(r - 1) / 2`. -/
def autoEvalF (g : Nat) (x : Limbs ms n) : Limbs ms n := fun i j =>
  x i ⟨((g * (2 * j.val + 1)) % (2 * n)) / 2,
    Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by have := j.isLt; omega))⟩

/-- Exact division by the trailing modulus `qL`: output limb `i` is
    `(x_i - x_last) · qL⁻¹ mod q_i`, with `x_last` the residue modulo `qL`
    read as an integer. -/
def rescaleF (ms : List Nat) (qL n : Nat) (x : Limbs (ms ++ [qL]) n) : Limbs ms n :=
  fun i j =>
    (ZMod.cast (x ⟨i.val, by rw [List.length_append, List.length_singleton]; omega⟩ j)
        - ZMod.cast (x ⟨ms.length, by
            rw [List.length_append, List.length_singleton]; omega⟩ j))
      * ((qL : ZMod (ms.get i)))⁻¹

/-- Fast basis conversion from `ms` to `ps`: with `Q̂_i = Q / q_i`,
    `y_i = x_i · Q̂_i⁻¹ mod q_i` and `out_j = Σ_i y_i · Q̂_i mod p_j`. The exact
    CRT correction `-vQ` is not applied. -/
def baseConvertF (ms ps : List Nat) (n : Nat) (x : Limbs ms n) : Limbs ps n :=
  fun o k =>
    ∑ i : Fin ms.length,
      (((x i k * ((ms.prod / ms.get i : Nat) : ZMod (ms.get i))⁻¹).val : ZMod (ps.get o)))
        * ((ms.prod / ms.get i : Nat) : ZMod (ps.get o))

/-- `ring.from_tensor`: each storage word is read as a residue of its row's
    modulus. -/
def fromTensorF (ms : List Nat) (n w : Nat) (t : Fin ms.length → Fin n → BitVec w) :
    Limbs ms n :=
  fun i j => ((t i j).toNat : ZMod (ms.get i))

/-- `ring.to_tensor`: each residue is written as its canonical representative in
    a `w`-bit word. -/
def toTensorF (ms : List Nat) (n w : Nat) (x : Limbs ms n) :
    Fin ms.length → Fin n → BitVec w :=
  fun i j => BitVec.ofNat w (x i j).val

/-! ## 2. Types -/

/-- The dialect's value types. -/
inductive RingTy where
  /-- `!ring.rq<ms, n, iw, d>`: an element of `Z_Q[X]/(X^n+1)`, `Q = ms.prod`. -/
  | rq (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `tensor<n x !field.pf<q>>`: one residue row. -/
  | limb (q n : Nat)
  /-- `tensor<l x n x iw>`: the raw residue words. -/
  | words (l n w : Nat)
  deriving DecidableEq

/-- Denotation of `RingTy`. -/
@[reducible] instance : TyDenote RingTy where
  denote
    | .rq ms n _ _ => Limbs ms n
    | .limb q n => Fin n → ZMod q
    | .words l n w => Fin l → Fin n → BitVec w

/-- `ring.from_limbs` on a heterogeneous vector of residue rows: row `i` is the
    `i`-th entry. -/
def limbsOfHVector {n : Nat} : (ms : List Nat) →
    HVector (fun t : RingTy => TyDenote.denote t) (ms.map (fun q => RingTy.limb q n)) →
    Limbs ms n
  | [], _ => fun i => i.elim0
  | _ :: ms, .cons x xs => fun i =>
    match i with
    | ⟨0, _⟩ => x
    | ⟨k + 1, h⟩ => limbsOfHVector ms xs ⟨k, by simp at h; omega⟩

/-! ## 3. Op tags -/

/-- Operation tags, one per upstream `ring` op. `toLimb` is the `i`-th result of
    the multi-result `ring.to_limbs`. -/
inductive RingOp where
  /-- `ring.add`. -/
  | add (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `ring.sub`. -/
  | sub (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `ring.negate`. -/
  | negate (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `ring.mul`, evaluation basis only. -/
  | mul (ms : List Nat) (n w : Nat)
  /-- `ring.automorphism` with exponent `g`. -/
  | automorphism (ms : List Nat) (n w : Nat) (d : Domain) (g : Nat)
  /-- `ring.rescale`, dropping the trailing modulus `qL`; coefficient basis. -/
  | rescale (ms : List Nat) (qL n w : Nat)
  /-- `ring.base_convert` from basis `ms` to basis `ps`; coefficient basis. -/
  | baseConvert (ms ps : List Nat) (n w : Nat)
  /-- `ring.from_tensor`. -/
  | fromTensor (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `ring.to_tensor`. -/
  | toTensor (ms : List Nat) (n w : Nat) (d : Domain)
  /-- `ring.from_limbs`. -/
  | fromLimbs (ms : List Nat) (n w : Nat) (d : Domain)
  /-- Result `i` of `ring.to_limbs`. -/
  | toLimb (ms : List Nat) (n w : Nat) (d : Domain) (i : Fin ms.length)
  /-- The coefficient-to-evaluation conversion of `R_Q` at length `2 ^ logN`, with
      `L` butterfly layers and per-limb roots `psis` (`nttF`). -/
  | ntt (ms : List Nat) (logN w L : Nat) (psis : List Nat)
  /-- The evaluation-to-coefficient conversion inverse to `ntt`, with per-limb
      scaling constants `scales` (`inttF`). -/
  | intt (ms : List Nat) (logN w L : Nat) (psis scales : List Nat)
  /-- The product of the evaluation form after `L` layers (`basemulF`); FIPS 203's
      `MultiplyNTTs` at `L = 7`, `ring.mul` at `L = logN`. -/
  | basemul (ms : List Nat) (logN w L : Nat) (psis : List Nat)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The ring dialect: `Op` is `RingOp`, `Ty` is `RingTy`. -/
@[reducible] def ringDialect : Dialect :=
  { Op := RingOp, Ty := RingTy }

instance : DialectSignature ringDialect where
  sig op := match op with
    | .add ms n w d => [.rq ms n w d, .rq ms n w d]
    | .sub ms n w d => [.rq ms n w d, .rq ms n w d]
    | .negate ms n w d => [.rq ms n w d]
    | .mul ms n w => [.rq ms n w .eval, .rq ms n w .eval]
    | .automorphism ms n w d _ => [.rq ms n w d]
    | .rescale ms qL n w => [.rq (ms ++ [qL]) n w .coeff]
    | .baseConvert ms _ n w => [.rq ms n w .coeff]
    | .fromTensor ms n w _ => [.words ms.length n w]
    | .toTensor ms n w d => [.rq ms n w d]
    | .fromLimbs ms n _ _ => ms.map (fun q => RingTy.limb q n)
    | .toLimb ms n w d _ => [.rq ms n w d]
    | .ntt ms logN w _ _ => [.rq ms (2 ^ logN) w .coeff]
    | .intt ms logN w _ _ _ => [.rq ms (2 ^ logN) w .eval]
    | .basemul ms logN w _ _ => [.rq ms (2 ^ logN) w .eval, .rq ms (2 ^ logN) w .eval]
  ret op := match op with
    | .add ms n w d => .rq ms n w d
    | .sub ms n w d => .rq ms n w d
    | .negate ms n w d => .rq ms n w d
    | .mul ms n w => .rq ms n w .eval
    | .automorphism ms n w d _ => .rq ms n w d
    | .rescale ms _ n w => .rq ms n w .coeff
    | .baseConvert _ ps n w => .rq ps n w .coeff
    | .fromTensor ms n w d => .rq ms n w d
    | .toTensor ms n w _ => .words ms.length n w
    | .fromLimbs ms n w d => .rq ms n w d
    | .toLimb ms n _ _ i => .limb (ms.get i) n
    | .ntt ms logN w _ _ => .rq ms (2 ^ logN) w .eval
    | .intt ms logN w _ _ _ => .rq ms (2 ^ logN) w .coeff
    | .basemul ms logN w _ _ => .rq ms (2 ^ logN) w .eval

/-- Op denotation. -/
instance ringDenote : DialectDenote ringDialect where
  denote op := match op with
    | .add _ _ _ _ => fun args => addF args.head args.tail.head
    | .sub _ _ _ _ => fun args => subF args.head args.tail.head
    | .negate _ _ _ _ => fun args => negF args.head
    | .mul _ _ _ => fun args => mulF args.head args.tail.head
    | .automorphism _ _ _ .coeff g => fun args => autoCoeffF g args.head
    | .automorphism _ _ _ .eval g => fun args => autoEvalF g args.head
    | .rescale ms qL n _ => fun args => rescaleF ms qL n args.head
    | .baseConvert ms ps n _ => fun args => baseConvertF ms ps n args.head
    | .fromTensor ms n w _ => fun args => fromTensorF ms n w args.head
    | .toTensor ms n w _ => fun args => toTensorF ms n w args.head
    | .fromLimbs ms _ _ _ => fun args => limbsOfHVector ms args
    | .toLimb _ _ _ _ i => fun args => args.head i
    | .ntt ms logN _ L psis => fun args => nttF ms logN L psis args.head
    | .intt ms logN _ L psis scales => fun args => inttF ms logN L psis scales args.head
    | .basemul _ logN _ L psis => fun args => basemulF logN L psis args.head args.tail.head

/-- `ntt` denotes `nttF`. -/
theorem ntt_denote (ms : List Nat) (logN w L : Nat) (psis : List Nat)
    (x : Limbs ms (2 ^ logN)) :
    ringDenote.denote (.ntt ms logN w L psis) (.cons x .nil) = nttF ms logN L psis x := rfl

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate in
/-- **The `ntt` op lowers to the template.** Row `i` of the `ntt` op's
    denotation is, lane by lane, the `fieldDialect` program `nttProg` at the
    parameter record of limb `i`, run on that row, whenever the record satisfies
    `NttParams.Ok`. -/
theorem lowerNega_denote (ms : List Nat) (logN w L : Nat) (psis : List Nat)
    (i : Fin ms.length) (hP : (NttParams.mk (ms.get i) logN L (psis.getD i 0)).Ok)
    (x : Limbs ms (2 ^ logN)) (j : Fin (2 ^ logN)) :
    ringDenote.denote (.ntt ms logN w L psis) (.cons x .nil) i j
      = NttStageFieldGeneral.hvGetD
          ((nttProg ⟨ms.get i, logN, L, psis.getD i 0⟩).denote
            (fnVal (ms.get i) (rowLanes x i) (2 ^ logN) 0)) j := by
  rw [ntt_denote, nttProg_denote _ hP _ j j.isLt]
  rfl

/-- `intt` denotes `inttF`. -/
theorem intt_denote (ms : List Nat) (logN w L : Nat) (psis scales : List Nat)
    (x : Limbs ms (2 ^ logN)) :
    ringDenote.denote (.intt ms logN w L psis scales) (.cons x .nil)
      = inttF ms logN L psis scales x := rfl

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate in
/-- **The `intt` op lowers to the inverse template.** Row `i` of the `intt` op's
    denotation is, lane by lane, the `fieldDialect` program `inttProg` at the
    parameter record and scaling constant of limb `i`, run on that row. -/
theorem lowerIntt_denote (ms : List Nat) (logN w L : Nat) (psis scales : List Nat)
    (i : Fin ms.length) (hP : (NttParams.mk (ms.get i) logN L (psis.getD i 0)).Ok)
    (x : Limbs ms (2 ^ logN)) (j : Fin (2 ^ logN)) :
    ringDenote.denote (.intt ms logN w L psis scales) (.cons x .nil) i j
      = NttStageFieldGeneral.hvGetD
          ((inttProg ⟨ms.get i, logN, L, psis.getD i 0⟩ (scales.getD i 0)).denote
            (fnVal (ms.get i) (rowLanes x i) (2 ^ logN) 0)) j := by
  rw [intt_denote, inttProg_denote _ hP _ _ j j.isLt]
  rfl

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate in
/-- **`intt` inverts `ntt`.** When every limb's parameter record satisfies
    `NttParams.Ok` and its scaling constant `ScaleOk`, `inttF` after `nttF` is the
    identity. -/
theorem inttF_nttF (ms : List Nat) (logN L : Nat) (psis scales : List Nat)
    (hP : ∀ i : Fin ms.length, (NttParams.mk (ms.get i) logN L (psis.getD i 0)).Ok ∧
      ScaleOk ⟨ms.get i, logN, L, psis.getD i 0⟩ (scales.getD i 0))
    (x : Limbs ms (2 ^ logN)) : inttF ms logN L psis scales (nttF ms logN L psis x) = x := by
  funext i j
  obtain ⟨hOk, hs⟩ := hP i
  have hψ := NttParams.psi_pow _ hOk
  have hsc := ScaleOk.cast _ _ hs
  simp only [inttF, inttSpec]
  rw [invRun_congr _ L logN L hOk.2.1 _ (nttSpec ((psis.getD i 0 : Nat) : ZMod (ms.get i)) L logN
    (rowLanes x i)) (fun k hk => by simp only [rowLanes, dite_eq_left hk]; rfl) j j.isLt]
  have := inttSpec_nttSpec _ L logN hψ hOk.1 hOk.2.1 _ hsc (rowLanes x i) j j.isLt
  simp only [inttSpec] at this
  rw [this, rowLanes, dite_eq_left j.isLt]

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate in
/-- **`ntt` inverts `intt`.** Under the same side conditions, `nttF` after `inttF`
    is the identity. -/
theorem nttF_inttF (ms : List Nat) (logN L : Nat) (psis scales : List Nat)
    (hP : ∀ i : Fin ms.length, (NttParams.mk (ms.get i) logN L (psis.getD i 0)).Ok ∧
      ScaleOk ⟨ms.get i, logN, L, psis.getD i 0⟩ (scales.getD i 0))
    (x : Limbs ms (2 ^ logN)) : nttF ms logN L psis (inttF ms logN L psis scales x) = x := by
  funext i j
  obtain ⟨hOk, hs⟩ := hP i
  have hψ := NttParams.psi_pow _ hOk
  have hsc := ScaleOk.cast _ _ hs
  simp only [nttF]
  rw [nttSpec_congr _ L logN hOk.2.1 _ (inttSpec ((psis.getD i 0 : Nat) : ZMod (ms.get i)) L logN
    ((scales.getD i 0 : Nat) : ZMod (ms.get i)) (rowLanes x i))
    (fun k hk => by simp only [rowLanes, dite_eq_left hk]; rfl) j,
    nttSpec_inttSpec _ L logN hψ hOk.1 hOk.2.1 _ hsc (rowLanes x i) j j.isLt, rowLanes,
    dite_eq_left j.isLt]

/-- `basemul` denotes `basemulF`. -/
theorem basemul_denote (ms : List Nat) (logN w L : Nat) (psis : List Nat)
    (x y : Limbs ms (2 ^ logN)) :
    ringDenote.denote (.basemul ms logN w L psis) (.cons x (.cons y .nil))
      = basemulF logN L psis x y := rfl

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate in
/-- **`ntt` turns the product of `R_Q` into `basemul`.** When every limb's
    parameter record satisfies `NttParams.Ok`, the transform of the negacyclic
    product is the block product of the transforms. -/
theorem nttF_negaMulF (ms : List Nat) (logN L : Nat) (psis : List Nat)
    (hP : ∀ i : Fin ms.length, (NttParams.mk (ms.get i) logN L (psis.getD i 0)).Ok)
    (x y : Limbs ms (2 ^ logN)) :
    nttF ms logN L psis (negaMulF logN x y)
      = basemulF logN L psis (nttF ms logN L psis x) (nttF ms logN L psis y) := by
  funext i j
  have hOk := hP i
  have hψ := NttParams.psi_pow _ hOk
  have hLM : L ≤ logN := hOk.2.1
  have hN : (2 : ℕ) ^ logN = 2 ^ L * 2 ^ (logN - L) := by
    rw [← pow_add]; congr 1; omega
  simp only [nttF, basemulF]
  rw [nttSpec_congr _ L logN hLM _ (negaMul (2 ^ logN) (rowLanes x i) (rowLanes y i))
    (fun k hk => by simp only [rowLanes, dite_eq_left hk]; rfl) j,
    nttSpec_negaMul _ L logN hψ hOk.2.1 _ _ j]
  refine blockMul_congr (2 ^ (logN - L)) (2 ^ L) (Nat.two_pow_pos _) _ _ _ _ _
    (fun k hk => by rw [← hN] at hk; simp only [rowLanes, dite_eq_left hk]; rfl)
    (fun k hk => by rw [← hN] at hk; simp only [rowLanes, dite_eq_left hk]; rfl) j
    (by rw [← hN]; exact j.isLt)

/-- With `L = logN` layers, `basemul` is the pointwise product `mul`. -/
theorem basemulF_eq_mulF (logN : Nat) (psis : List Nat) (x y : Limbs ms (2 ^ logN)) :
    basemulF logN logN psis x y = mulF x y := by
  funext i j
  simp only [basemulF, Nat.sub_self, pow_zero, NegacyclicNttTemplate.blockMul_one, mulF,
    rowLanes, dite_eq_left j.isLt]

/-- `add` denotes the per-limb sum. -/
theorem add_denote (ms : List Nat) (n w : Nat) (d : Domain) (x y : Limbs ms n) :
    ringDenote.denote (.add ms n w d) (.cons x (.cons y .nil)) = addF x y := rfl

/-- `mul` denotes the pointwise product. -/
theorem mul_denote (ms : List Nat) (n w : Nat) (x y : Limbs ms n) :
    ringDenote.denote (.mul ms n w) (.cons x (.cons y .nil)) = mulF x y := rfl

/-- `rescale` denotes `rescaleF`. -/
theorem rescale_denote (ms : List Nat) (qL n w : Nat) (x : Limbs (ms ++ [qL]) n) :
    ringDenote.denote (.rescale ms qL n w) (.cons x .nil) = rescaleF ms qL n x := rfl

/-! ## 5. Correspondence with integer coefficient vectors -/

/-- The residues of an integer vector in the basis `ms`. -/
def ofInts (ms : List Nat) {n : Nat} (c : Fin n → ℤ) : Limbs ms n :=
  fun i j => (c j : ZMod (ms.get i))

/-- `add` is integer addition read through `ofInts`. -/
theorem addF_ofInts (a b : Fin n → ℤ) :
    addF (ofInts ms a) (ofInts ms b) = ofInts ms (a + b) := by
  funext i j; simp [addF, ofInts]

/-- `sub` is integer subtraction read through `ofInts`. -/
theorem subF_ofInts (a b : Fin n → ℤ) :
    subF (ofInts ms a) (ofInts ms b) = ofInts ms (a - b) := by
  funext i j; simp [subF, ofInts]

/-- `negate` is integer negation read through `ofInts`. -/
theorem negF_ofInts (a : Fin n → ℤ) :
    negF (ofInts ms a) = ofInts ms (-a) := by
  funext i j; simp [negF, ofInts]

/-- The pointwise product is the pointwise integer product read through
    `ofInts`; in the evaluation basis this is the product of `R_Q`. -/
theorem mulF_ofInts (a b : Fin n → ℤ) :
    mulF (ofInts ms a) (ofInts ms b) = ofInts ms (a * b) := by
  funext i j; simp [mulF, ofInts]

/-- Chinese remaindering for a pairwise coprime basis: two integers agree modulo
    `ms.prod` exactly when they agree modulo every `ms.get i`. -/
theorem intCast_eq_iff_forall_limb (hco : ms.Pairwise Nat.Coprime) (x y : ℤ) :
    (x : ZMod ms.prod) = y ↔ ∀ i : Fin ms.length, (x : ZMod (ms.get i)) = y := by
  simp only [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natCast_dvd]
  rw [← Nat.modEq_zero_iff_dvd, Nat.modEq_list_prod_iff hco]
  simp only [Nat.modEq_zero_iff_dvd]

/-- **The residue array is faithful.** For a pairwise coprime basis, two integer
    vectors have the same residues exactly when they agree modulo `Q = ms.prod`
    at every position. -/
theorem ofInts_eq_iff (hco : ms.Pairwise Nat.Coprime) (a b : Fin n → ℤ) :
    ofInts ms a = ofInts ms b ↔ ∀ j, (a j : ZMod ms.prod) = b j := by
  constructor
  · intro h j
    rw [intCast_eq_iff_forall_limb hco]
    intro i
    exact congrFun (congrFun h i) j
  · intro h
    funext i j
    exact (intCast_eq_iff_forall_limb hco _ _).1 (h j) i

/-- Casting the image of an integer between two equal moduli is the image. -/
theorem cast_intCast_of_eq {a b : Nat} (h : a = b) (k : ℤ) :
    (ZMod.cast (k : ZMod a) : ZMod b) = k := by
  subst h
  exact ZMod.cast_intCast (dvd_refl _) k

/-- Casting the image of `k` modulo `a = q` into any `ZMod m` is the image of the
    representative `k % q`. -/
theorem cast_intCast_of_eq_emod {a q m : Nat} [NeZero q] (h : a = q) (k : ℤ) :
    (ZMod.cast (k : ZMod a) : ZMod m) = ((k % q : ℤ) : ZMod m) := by
  subst h
  rw [ZMod.cast_eq_val, ← Int.cast_natCast, ZMod.val_intCast]

/-- **Rescale is exact division.** For `qL` coprime to every modulus of `ms`,
    rescaling the residues of `c` in `ms ++ [qL]` gives the residues of
    `(c - c mod qL) / qL` in `ms`. -/
theorem rescaleF_ofInts (qL : Nat) [NeZero qL]
    (hcop : ∀ i : Fin ms.length, Nat.Coprime qL (ms.get i)) (c : Fin n → ℤ) :
    rescaleF ms qL n (ofInts (ms ++ [qL]) c)
      = ofInts ms (fun j => (c j - c j % qL) / qL) := by
  funext i j
  have hi : i.val < (ms ++ [qL]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have hl : ms.length < (ms ++ [qL]).length := by
    rw [List.length_append, List.length_singleton]; omega
  have ha : (ms ++ [qL]).get ⟨i.val, hi⟩ = ms.get i := by
    simp [List.getElem_append_left i.isLt]
  have hb : (ms ++ [qL]).get ⟨ms.length, hl⟩ = qL := by simp
  simp only [rescaleF, ofInts, cast_intCast_of_eq ha, cast_intCast_of_eq_emod hb]
  have hq : (qL : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne qL
  rw [Int.emod_def, sub_sub_cancel, Int.mul_ediv_cancel_left _ hq]
  push_cast
  rw [sub_sub_cancel, mul_right_comm, ZMod.coe_mul_inv_eq_one _ (hcop i), one_mul]

/-! ## 6. The automorphism at `g = 1` -/

/-- The evaluation-basis automorphism at `g = 1` is the identity. -/
theorem autoEvalF_one (x : Limbs ms n) : autoEvalF 1 x = x := by
  funext i j
  simp only [autoEvalF, one_mul]
  congr 1
  ext
  simp only
  have := j.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The coefficient-basis automorphism at `g = 1` is the identity. -/
theorem autoCoeffF_one (x : Limbs ms n) : autoCoeffF 1 x = x := by
  funext i j
  simp only [autoCoeffF, one_mul]
  have h1 : ∀ k : Fin n, k.val % n = k.val := fun k => Nat.mod_eq_of_lt k.isLt
  have h2 : ∀ k : Fin n, ¬ n ≤ k.val % (2 * n) := fun k => by
    have := k.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simp only [h1, h2, ite_false, Fin.val_inj]
  simp

/-! ## 7. Tensor round trips -/

/-- Reading in-range words and writing them back returns the words. -/
theorem toTensorF_fromTensorF (w : Nat) (t : Fin ms.length → Fin n → BitVec w)
    (hlt : ∀ i j, (t i j).toNat < ms.get i) :
    toTensorF ms n w (fromTensorF ms n w t) = t := by
  funext i j
  simp only [toTensorF, fromTensorF, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt i j)]
  simp

/-- Writing residues to `w`-bit words and reading them back returns the
    residues, when every modulus is positive and at most `2^w`. -/
theorem fromTensorF_toTensorF (w : Nat) (x : Limbs ms n)
    (hpos : ∀ i, 0 < ms.get i) (hle : ∀ i, ms.get i ≤ 2 ^ w) :
    fromTensorF ms n w (toTensorF ms n w x) = x := by
  funext i j
  have : NeZero (ms.get i) := ⟨(hpos i).ne'⟩
  have hv : (x i j).val < 2 ^ w := lt_of_lt_of_le (ZMod.val_lt _) (hle i)
  simp only [fromTensorF, toTensorF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    ZMod.natCast_zmod_val]

/-! ## 8. Constant-time predicate

Every op is a fixed per-position schedule of modular operations with public
index maps, so each is data-oblivious. -/

/-- Per-op CT predicate: every op of this dialect is constant-time. -/
def RingOp.ctSafe : RingOp → Bool
  | _ => true

@[simp] theorem RingOp.ctSafe_all (op : RingOp) : op.ctSafe = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound op is. -/
def ctSafeCom {Γ : Ctxt ringDialect} {t : RingTy} :
    Com ringDialect Γ t → Bool
  | .ret _ => true
  | .var e body => e.op.ctSafe && ctSafeCom body

/-- Every program of the dialect is constant-time. -/
theorem ringDialect_ctSafe_all {Γ : Ctxt ringDialect} {t : RingTy}
    (c : Com ringDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ih]

end CatCrypt.Crypto.SecureCompilation.VIR.RingDialect
