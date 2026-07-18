/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic

/-!
# TensorExt VIR dialect — bit-reversal as a first-class tensor op

A minimal `VIR.Dialect` whose single op is `bitReverse`, the bit-reversal
permutation of a `2^k`-lane tensor.  It is the CatCrypt counterpart of
fractalyze/prime-ir's **TensorExt** dialect, whose one op is
`tensor_ext.bit_reverse` (`source`/`dest` tensor, `dimension` attr).

## Why this dialect exists (the gap it closes)

Per `PRIME_IR_GAP_ANALYSIS.md` (repo root, §5), CatCrypt already *had* the
bit-reversal functionality, but only **inlined** inside the NTT emit kernels:
`Plonky3ProveEmit.bitReverse`/`bitReversePermute` (`ntt.rs::bit_reverse`,
reverse-the-low-`logN`-bits, used by `bbNtt`), and the same permutation reused
by `LatticeNttEmit` / `Plonky3LdeColumnEmit` / `FheNttLoopOwnedEmit`.  The gap
analysis classified it **PARTIAL** — "functionality present, not factored as a
reusable tensor op."  This dialect **factors that inlined permutation as a
standalone op**, matching prime-ir's `tensor_ext.bit_reverse` one-for-one.

## The op (`TensorExtOp`)

* `bitReverse k` — permute a `2^k`-lane tensor by the bit-reversal of its lane
  index: lane `i ↦` lane `bitrev_k(i)`, where `bitrev_k` reverses the `k` index
  bits.  `k` is the dialect-level analogue of prime-ir's `dimension` attribute.

## Type (`TensorExtTy`)

* `tensor k` — a tensor of `2^k` lanes, `⟦·⟧ = Fin (2^k) → BitVec 64`.  The lane
  payload is `BitVec 64`, matching the `List (BitVec 64)` carrier the inlined NTT
  bit-reversal (`Plonky3ProveEmit.bitReversePermute`) operates on (the
  reference's `&mut [u64]`).

## The bit-reversal permutation (`bitrevPerm`)

`bitrevPerm k : Equiv.Perm (Fin (2^k))` reindexes the bit-vector domain of a lane
index by `Fin.revPerm` (reverse the `k` bit positions), via the
`finFunctionFinEquiv : (Fin k → Fin 2) ≃ Fin (2^k)` Mathlib bijection.  Because it
is built from the involutive `Fin.revPerm`, it is an `Equiv.Perm` and the
involution `bitrevPerm k (bitrevPerm k i) = i` holds structurally
(`bitrevPerm_involutive`).  It agrees value-for-value with the established
`Plonky3ProveEmit.bitReverse` NTT semantics (reverse-the-low-`k`-bits): e.g. at
`k = 3` both give `[0,4,2,6,1,5,3,7]` (machine-checked by `#eval` during
development; the structural facts proved here are the bound-free `Equiv` form).

## Denotation (`bitReverseF`)

`bitReverseF k f = f ∘ bitrevPerm k`: the output tensor's lane `i` reads the
input's lane `bitrev_k(i)`.  This is the per-lane permutation prime-ir's
`tensor_ext.bit_reverse` denotes to.  The dialect denotation
(`tensorExtDenote`) plugs this leaf in directly, so the op's meaning is the
**genuine** index permutation, not a stub.

## Honest classification (read `VIR/DIALECTS.md`)

This is a **HIGH-tier, prime-ir-corresponding / agreement** dialect, NOT an
emit-wired one.  It has **no lowering out** (no `→ Com jasminDialect`, no
backend edge): like `mlirArithDialect` & friends in DIALECTS.md's
"correspondence-only" table, it substantiates the "prime-ir TensorExt aligned"
claim and factors the previously-inlined bit-reversal into one reusable op with
a verified denotation + involution law.  It does **not** add a new lowering or
emit path — the bytes-reaching NTT bit-reversal still flows through the inlined
`Plonky3ProveEmit`/`LatticeNttEmit` kernels (the genuine `Com → jasmin → ELF`
spine in DIALECTS.md).  Do not overclaim an emit this file does not build.

## Pure-only + constant-time

The op is a fixed, data-independent index permutation (the bit-reversal schedule
is index-only, never data-dependent), so its denotation is a total pure function
and it is constant-time by construction (`ctSafe = true`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.TensorExtDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The bit-reversal permutation

`bitrevPerm k` reverses the `k` index bits of a lane index in `Fin (2^k)`.  It
reuses Mathlib's `finFunctionFinEquiv : (Fin k → Fin 2) ≃ Fin (2^k)` to view a
lane index as its bit-vector, applies `Fin.revPerm` to the bit *positions*, and
maps back.  This is exactly the `Plonky3ProveEmit.bitReverse` permutation
(`ntt.rs::bit_reverse`, reverse the low `k` bits), now in bound-free `Equiv`
form so the involution and lane-permutation facts are structural. -/

/-- The bit-reversal permutation of a `2^k`-lane tensor's index set: reverse the
    `k` bit positions of the lane index.  Built from the involutive `Fin.revPerm`
    via the bit-vector bijection `finFunctionFinEquiv`, so it is an
    `Equiv.Perm (Fin (2^k))` by construction. -/
def bitrevPerm (k : Nat) : Equiv.Perm (Fin (2 ^ k)) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).trans finFunctionFinEquiv)

/-- **Involution.** Applying the bit-reversal permutation twice is the identity —
    reversing `k` bit positions twice restores them.  Holds structurally because
    `bitrevPerm` is built from the involutive `Fin.revPerm`. -/
theorem bitrevPerm_involutive (k : Nat) (i : Fin (2 ^ k)) :
    bitrevPerm k (bitrevPerm k i) = i := by
  unfold bitrevPerm
  simp [Equiv.arrowCongr, Function.comp_def, Fin.revPerm]

/-! ## 2. Type -/

/-- The TensorExt dialect's value-type alphabet: a tensor of `2^k` lanes.  `k` is
    the dialect-level analogue of prime-ir `tensor_ext.bit_reverse`'s `dimension`
    attribute. -/
inductive TensorExtTy where
  /-- A tensor of `2^k` lanes. -/
  | tensor (k : Nat)
  deriving DecidableEq

/-- Total denotation of `TensorExtTy`: a `2^k`-lane tensor is a function
    `Fin (2^k) → BitVec 64`.  The `BitVec 64` lane payload matches the
    `List (BitVec 64)` carrier of the inlined NTT bit-reversal. -/
@[reducible] instance : TyDenote TensorExtTy where
  denote
    | .tensor k => Fin (2 ^ k) → BitVec 64

/-! ## 3. Concrete leaf function (the bit-reversal permutation of a tensor) -/

/-- Permute a `2^k`-lane tensor by bit-reversal of its lane index: the output
    lane `i` reads the input lane `bitrev_k(i)`.  This is the index permutation
    prime-ir's `tensor_ext.bit_reverse` denotes to, and the standalone form of
    `Plonky3ProveEmit.bitReversePermute`. -/
@[reducible] def bitReverseF (k : Nat) (f : Fin (2 ^ k) → BitVec 64) :
    Fin (2 ^ k) → BitVec 64 :=
  fun i => f (bitrevPerm k i)

/-! ## 4. Op tag -/

/-- Operation tags for the TensorExt dialect — a single op, the tensor
    bit-reversal, mirroring prime-ir's lone `tensor_ext.bit_reverse`. -/
inductive TensorExtOp where
  /-- Bit-reverse a `2^k`-lane tensor (prime-ir `tensor_ext.bit_reverse`,
      `dimension = k`). -/
  | bitReverse (k : Nat)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The TensorExt dialect: `Op` is `TensorExtOp`, `Ty` is `TensorExtTy`. -/
@[reducible] def tensorExtDialect : Dialect :=
  { Op := TensorExtOp, Ty := TensorExtTy }

/-! ## 6. Op signature (arg types + return type) -/

instance : DialectSignature tensorExtDialect where
  sig op := match op with
    | .bitReverse k => [.tensor k]
  ret op := match op with
    | .bitReverse k => .tensor k

/-! ## 7. Op denotation (into the genuine index permutation) -/

instance tensorExtDenote : DialectDenote tensorExtDialect where
  denote op := match op with
    | .bitReverse k => fun args => bitReverseF k args.head

/-! ## 8. Per-op correctness / agreement facts -/

/-- **Denotation agreement.** The `bitReverse k` op denotes to the bit-reversal
    permutation of the input tensor: output lane `i` reads input lane
    `bitrev_k(i)`.  This is the standalone form of the previously-inlined NTT
    bit-reversal, matching prime-ir's `tensor_ext.bit_reverse`. -/
theorem bitReverse_denote (k : Nat) (f : Fin (2 ^ k) → BitVec 64) :
    tensorExtDenote.denote (.bitReverse k) (.cons f .nil)
      = fun i => f (bitrevPerm k i) := rfl

/-- **Involution at the op level.** Bit-reversing a tensor twice yields the
    original tensor — the op is its own inverse, the tensor-level lift of
    `bitrevPerm_involutive`. -/
theorem bitReverse_denote_involutive (k : Nat) (f : Fin (2 ^ k) → BitVec 64) :
    tensorExtDenote.denote (.bitReverse k)
        (.cons (tensorExtDenote.denote (.bitReverse k) (.cons f .nil)) .nil)
      = f := by
  funext i
  show f (bitrevPerm k (bitrevPerm k i)) = f i
  rw [bitrevPerm_involutive]

/-! ## 9. Constant-time predicate (the dialect's CT instance)

The bit-reversal schedule is a fixed, index-only permutation — no `ite` on data,
no data-dependent memory index — so `ctSafe` is `true` for the op. -/

/-- Per-op CT predicate: the bit-reversal op is constant-time. -/
def TensorExtOp.ctSafe : TensorExtOp → Bool
  | _ => true

@[simp] theorem TensorExtOp.ctSafe_all (op : TensorExtOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt tensorExtDialect} {t : TensorExtTy}
    (e : Expr tensorExtDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt tensorExtDialect} {t : TensorExtTy}
    (e : Expr tensorExtDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since the only op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt tensorExtDialect} {t : TensorExtTy} :
    Com tensorExtDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every TensorExt program is constant-time: the
    bit-reversal permutation introduces no data-dependent control flow or memory
    index. -/
theorem ctSafeCom_all {Γ : Ctxt tensorExtDialect} {t : TensorExtTy}
    (c : Com tensorExtDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

end CatCrypt.Crypto.SecureCompilation.VIR.TensorExtDialect
