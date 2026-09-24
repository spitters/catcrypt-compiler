/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# FAEST symmetric-leaf specs (AES-128 and SHAKE128)

FAEST — and the Round-3 MPC-in-the-head signature candidates **MQOM** and
**SDitH** — orchestrate exactly two symmetric primitives:

* `aes128_encrypt(key, input) -> block` — the one-way function *and* the GGM-tree
  PRG that expands seeds during VOLE-in-the-head commitment;
* `shake128` — all hashing and the Fiat-Shamir transform.

The verified front-end emits these as **opaque external leaves** (`extCall`) in
the Jasmin dialect (`JasminDialect.lean`). This file declares the *leaf specs*
for those two leaves: the named-leaf semantics carrier (`FaestLeafSem`, the
`extCall` interpretation, same shape as `jasminExtSem`) together with the
agreement proposition (`FaestLeafAgrees`) that ties a concrete leaf semantics to
the abstract symmetric primitives. This is the FAEST analogue of
`LatticeToJasminDenote.LeafAgrees` (the NTT leaves) and of the parametric leaf
edge in `JasminPrintSemCorrect` (`LeafSem` / `LeafAgrees`): the leaf semantics is
opaque, and its agreement with the primitive is the carried obligation.

The KAT under `bench/faest_leaves/` discharges that obligation operationally:
the libjade/jasmin leaves we bind here (`aes_enc` via AES-NI; the libjade
`jade_xof_shake128_amd64_ref` SHAKE128 XOF) are confirmed byte-identical to the
NIST FIPS-197 / FIPS-202 / CAVP vectors **and** to the faest-hax `specs::aes128`
/ `specs::shake128` Rust the hax pipeline extracts. So binding `faest_aes128` /
`faest_shake128` to those leaves computes FAEST's expected primitives.

## Leaf dialect types

| leaf            | `extCall` signature                                   | meaning                       |
|-----------------|-------------------------------------------------------|-------------------------------|
| `faest_aes128`  | `[reg 128, reg 128] → reg 128`                        | one 128-bit ECB block (key,pt)|
| `faest_shake128`| `[stackArr 8 inlen] → stackArr 8 outlen`              | byte-stream XOF (variable len)|

AES is a fixed 128-bit block transform, so it is naturally a `reg 128` leaf.
SHAKE128 is a variable-length XOF over bytes, so it is a byte (`reg 8`)
stack-array leaf, parameterised by the input/output lengths.

This file imports **only** the stable dialect (`JasminDialect.lean`); it is
independent of the emitter (`JasminAbiEmit` / `JasmincSemAlignment` /
`JasminPrint` / `GlueVectorization`) and builds standalone.

All goals closed. The leaf edge is parametric (a hypothesis), never an admitted proof.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FAEST.Leaves

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Leaf names -/

/-- The leaf name the front-end emits for the AES-128 single-block one-way
    function / GGM-tree PRG core. -/
def aesLeafName : String := "faest_aes128"

/-- The leaf name the front-end emits for the SHAKE128 XOF (hashing /
    Fiat-Shamir). -/
def shakeLeafName : String := "faest_shake128"

/-! ## 2. The two leaf signatures

These pin the dialect typing of each leaf: AES is a fixed 128-bit block, SHAKE
is a variable-length byte XOF. -/

/-- Dialect signature of the AES-128 leaf: `(key : reg 128, plaintext : reg 128)
    → ciphertext : reg 128`. -/
def aesArgTys : List JasminTy := [.reg 128, .reg 128]

/-- Return type of the AES-128 leaf. -/
def aesRetTy : JasminTy := .reg 128

/-- Dialect signature of the SHAKE128 XOF leaf on input length `inlen` and
    output length `outlen`: `(input : stackArr 8 inlen) → output : stackArr 8
    outlen`, a byte (`reg 8`) stream. -/
def shakeArgTys (inlen : Nat) : List JasminTy := [.stackArr 8 inlen]

/-- Return type of the SHAKE128 leaf for output byte length `outlen`. -/
def shakeRetTy (outlen : Nat) : JasminTy := .stackArr 8 outlen

/-! ## 3. The named-leaf semantics carrier

`FaestLeafSem` has the exact shape of `jasminExtSem` / `JasminPrintSemCorrect`'s
`LeafSem`: it reads the already-resolved typed arguments of an `extCall` and
returns the typed result. A concrete binding (e.g. the validated libjade/jasmin
leaves) is a value of this type; the *abstract* symmetric primitives below say
what such a value must compute on the two FAEST leaf names. -/

/-- External-leaf semantics: same shape as `jasminExtSem`, opaque. -/
abbrev FaestLeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-! ## 4. The abstract symmetric primitives

The two functions FAEST/MQOM/SDitH call. They are the *spec*: a 128-bit block
transform and a byte-stream XOF. We keep them abstract (a `structure` of the two
primitives) — the FAEST security proof reasons against this interface, and the
KAT confirms the bound leaves realise it. -/

/-- The symmetric-primitive interface FAEST orchestrates: AES-128 as a 128-bit
    block transform and SHAKE128 as a byte-stream XOF. Validated concretely by
    `bench/faest_leaves/` (libjade/jasmin leaves vs. NIST + faest-hax spec). -/
structure FaestPrimitives where
  /-- AES-128 single-block ECB: `(key, plaintext) ↦ ciphertext`, all 128-bit. -/
  aes128 : BitVec 128 → BitVec 128 → BitVec 128
  /-- SHAKE128 XOF: `(inlen, input bytes, outlen) ↦ output bytes`. Bytes are
      `reg 8` stack arrays; the length parameters make the signature concrete. -/
  shake128 : (inlen : Nat) → (Fin inlen → BitVec 8) → (outlen : Nat) →
    (Fin outlen → BitVec 8)

/-! ## 5. Leaf agreement

`FaestLeafAgrees prims leafSem` says the concrete leaf semantics `leafSem`
computes the abstract primitives `prims` on the two FAEST leaf names (at the
leaf's declared signature). This is the FAEST counterpart of
`LatticeToJasminDenote.LeafAgrees` / `JasminPrintSemCorrect.LeafAgrees`: opaque
leaf, carried agreement obligation — never an admitted proof. -/

/-- AES-128 leaf agreement: on the `faest_aes128` signature, the leaf semantics
    is `prims.aes128` of its two `reg 128` arguments. -/
def AesLeafAgrees (prims : FaestPrimitives) (leafSem : FaestLeafSem) : Prop :=
  ∀ args : HVector (fun t => ⟦t⟧) aesArgTys,
    leafSem aesLeafName aesArgTys aesRetTy args
      = prims.aes128 (args.head) (args.tail.head)

/-- SHAKE128 leaf agreement: on the `faest_shake128` signature at lengths
    `inlen`/`outlen`, the leaf semantics is `prims.shake128` of its input byte
    array. -/
def ShakeLeafAgrees (prims : FaestPrimitives) (leafSem : FaestLeafSem) : Prop :=
  ∀ (inlen outlen : Nat) (args : HVector (fun t => ⟦t⟧) (shakeArgTys inlen)),
    leafSem shakeLeafName (shakeArgTys inlen) (shakeRetTy outlen) args
      = (fun (j : Fin outlen) =>
          prims.shake128 inlen
            (fun (i : Fin inlen) => stackGet (args.head) i.val) outlen j)

/-- The full FAEST symmetric-leaf agreement: `leafSem` realises both primitives
    on both leaf names. The validated libjade/jasmin AES-NI + SHAKE128 leaves
    are the intended witness. -/
def FaestLeafAgrees (prims : FaestPrimitives) (leafSem : FaestLeafSem) : Prop :=
  AesLeafAgrees prims leafSem ∧ ShakeLeafAgrees prims leafSem

/-! ## 6. Denotation of an emitted leaf `Expr`

For a leaf emitted as an `extCall` `Expr` in a context `Γ` under a valuation `V`,
its dialect denotation `Expr.denote` is exactly `jasminExtSem` of the resolved
arguments. We expose the two FAEST leaves as `Expr` builders so a later
end-to-end argument (in the emitter-side files, owned by the parallel agent) can
relate `Com.denote` of an emitted leaf to the symmetric primitive via
`FaestLeafAgrees`. The builders need only the dialect, so they live here. -/

/-- Build the AES-128 leaf `Expr` from two `reg 128` variables (key, plaintext)
    in scope. -/
def aesLeafExpr {Γ : Ctxt jasminDialect}
    (key plaintext : Ctxt.Var Γ (.reg 128)) :
    Expr jasminDialect Γ aesRetTy :=
  { op := .extCall aesLeafName aesArgTys aesRetTy
    retTy_eq := rfl
    args := .cons key (.cons plaintext .nil) }

/-- Build the SHAKE128 leaf `Expr` from one `stackArr 8 inlen` input variable in
    scope, at output length `outlen`. -/
def shakeLeafExpr {Γ : Ctxt jasminDialect} {inlen outlen : Nat}
    (input : Ctxt.Var Γ (.stackArr 8 inlen)) :
    Expr jasminDialect Γ (shakeRetTy outlen) :=
  { op := .extCall shakeLeafName (shakeArgTys inlen) (shakeRetTy outlen)
    retTy_eq := rfl
    args := .cons input .nil }

/-- The AES leaf `Expr` denotes (under any valuation) to `jasminExtSem` of the
    looked-up key and plaintext — the dialect's opaque-leaf semantics. By `rfl`:
    `Expr.denote` of an `extCall` is `jasminExtSem` applied to the resolved
    args. This is the bridge point a concrete `leafSem` discharges via
    `AesLeafAgrees`. -/
theorem aesLeafExpr_denote {Γ : Ctxt jasminDialect}
    (key plaintext : Ctxt.Var Γ (.reg 128)) (V : Ctxt.Valuation Γ) :
    (aesLeafExpr key plaintext).denote V
      = jasminExtSem aesLeafName aesArgTys aesRetTy
          (.cons (key.lookup V) (.cons (plaintext.lookup V) .nil)) :=
  rfl

/-- The SHAKE leaf `Expr` denotes (under any valuation) to `jasminExtSem` of the
    looked-up input byte array. By `rfl`. -/
theorem shakeLeafExpr_denote {Γ : Ctxt jasminDialect} {inlen outlen : Nat}
    (input : Ctxt.Var Γ (.stackArr 8 inlen)) (V : Ctxt.Valuation Γ) :
    (shakeLeafExpr (outlen := outlen) input).denote V
      = jasminExtSem shakeLeafName (shakeArgTys inlen) (shakeRetTy outlen)
          (.cons (input.lookup V) .nil) :=
  rfl

end CatCrypt.Crypto.FAEST.Leaves
