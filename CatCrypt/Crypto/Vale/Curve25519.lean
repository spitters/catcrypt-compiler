/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import CatCrypt.Crypto.Jasmin.LeafSig
public import CatCrypt.Crypto.Jasmin.LeafSig
public meta import CatCrypt.Crypto.Vale.LeafLeakage
public import CatCrypt.Crypto.Vale.LeafLeakage


@[expose] public section
set_option autoImplicit false

/-!
# Vale-verified Curve25519 (HACL\* `Hacl_Curve25519_64`) leaf

This module declares the Vale-verified HACL\* `Hacl_Curve25519_64`
implementation — a 4-limb saturated radix-2^64 X25519 driven by the
Vale-verified ADX/MULX field-arithmetic primitives in
`curve25519-x86_64-linux.S` — as an opaque verified-CT leaf for
CatCrypt's verified front, following the established extCall pattern
(Jasmin.LowCT `RCall`).

## Pilot scope (Option A — Vale-leaf adoption)

Second adoption (after `Vale/ChaCha20Vec256.lean`) of a Vale-verified
leaf into CatCrypt's verified-front pipeline. The pattern established
for ChaCha20-Vec256 scales here directly.

## Architectural claim (the composition)

```
CatCrypt(glue) + Vale(leaf)
    via the extCall denotation at the Veir/Jasmin extCall boundary
    -> verified-CT pipeline
```

CatCrypt's verified front discharges the orchestration; the leaf's
denotation matches the Vale F\* proof (cited below); CT is inherited
from Vale's taint-tracking proof on the implementation side.

## The HACL\* / Vale provenance

* **C driver**: `Hacl_Curve25519_64.c` (libcrux/HACL*),
  exported with C symbol `Hacl_Curve25519_64_scalarmult`. The driver
  composes nine Vale-verified field-arithmetic primitives
  (`add_scalar`, `fadd`, `fsub`, `fmul`, `fmul2`, `fmul_scalar`,
  `fsqr`, `fsqr2`, `cswap2`) around the standard Montgomery ladder.
* **Vale assembly**: `curve25519-x86_64-linux.S` (libcrux/HACL* Vale)
  contains the exported `*_e` symbols (`add_scalar_e`, `fadd_e`,
  `fsub_e`, `fmul_e`, `fmul2_e`, `fmul_scalar_e`, `fsqr_e`, `fsqr2_e`,
  `cswap2_e`); the inline-asm path in `curve25519-inline.h` uses the
  same Vale code with inline `asm("...")` instead of extern call.
* **F\* / Vale proof**: the field-arithmetic primitives are proved
  functionally correct in Vale (Bond et al. PLDI 2017) against the
  F\* spec `Spec.Curve25519`; the ladder driver is in turn proved in
  F\* against the same spec (Polubelova et al. CHES 2020).
* **NIST CAVP**: HACL\*'s `Hacl_Curve25519_64_scalarmult` matches RFC
  7748 §5.2 test vectors byte-for-byte (validated by the bench
  `bench/curve25519_vale_compare/conform.c`).

## Leaf C signature

```c
extern void Hacl_Curve25519_64_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub);
```

That is: `out = X25519(priv, pub)` over 32-byte buffers (RFC 7748
clamping is performed inside).

## Trust delta (what we trust ABOVE CatCrypt's normal axiom set)

By adopting this leaf we additionally trust:

1. **Vale_Hacl_Curve25519_64_denote**: the leaf computes
   `Spec.Curve25519.scalarmult` per RFC 7748. Sourced from the F\*
   driver proof in `Hacl.Curve25519_64.fst` and the Vale field-
   arithmetic proofs in the `*_e` primitives.

2. **Vale_Hacl_Curve25519_64_CT**: the leaf is constant-time in
   `priv` (the secret scalar). Sourced from Vale's taint-tracking
   proof on the field-arithmetic primitives plus the constant-time
   Montgomery ladder + `cswap2` in the driver.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls is the Vale-extracted HACL\* code (not, say, a maliciously
   substituted X25519 implementation). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is the ADX-Montgomery prototype in
`Curve25519AdxPrototype.lean` (Lean-spec → C transliteration → gcc),
because:

* The Vale F\* proof discharges the field-arithmetic correctness
  axiom that our prototype assumes about `curve25519_64.h`'s
  fiat-crypto primitives.
* The Vale taint-tracking proof discharges the CT axiom that our
  prototype assumes about gcc's `-O3` output.
* The leaf is a fixed binary symbol; no compiler dependency beyond
  the trusted assembler (gas/clang-as) to encode the `.S`.
-/

namespace CatCrypt.Crypto.Vale.Curve25519

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Opaque surface type

The 32-byte X25519 buffer (scalar / point / output share the shape).
Opaque — the concrete leaf at link time is the HACL\* C symbol. -/

opaque Curve25519Buf.Impl : NonemptyType.{0}
/-- A 32-byte Curve25519 buffer (scalar, point, or output). Opaque;
    the concrete leaf is the HACL\* Vale-verified
    `Hacl_Curve25519_64_scalarmult`. -/
def Curve25519Buf : Type := Curve25519Buf.Impl.type
instance : Nonempty Curve25519Buf := Curve25519Buf.Impl.property
/-- An inhabitant. -/
noncomputable opaque Curve25519Buf.default : Curve25519Buf
noncomputable instance : Inhabited Curve25519Buf :=
  ⟨Curve25519Buf.default⟩

/-! ## §2. Vale-leaf axioms (the trust delta)

These are the two axioms we add to CatCrypt's axiom budget when we
permit Vale-verified leaves. Each is sourced from HACL\* / Vale's
upstream F\* proofs. -/

/-- **Denotation axiom**: the Vale-verified `Hacl_Curve25519_64`
    leaf computes the RFC 7748 X25519 scalar multiplication (with
    clamping) of its `priv` scalar and `pub` base point. Discharged
    by the F\* functional-correctness proof in
    `Hacl.Curve25519_64.fst` against `Spec.Curve25519.scalarmult`,
    and the Vale proofs on the field-arithmetic `*_e` primitives. -/
axiom Vale_Hacl_Curve25519_64_denote
    (priv : Curve25519Buf) (pub : Curve25519Buf) : Curve25519Buf

/-- **Leakage function**: the observable trace the `Hacl_Curve25519_64`
    leaf emits on the scalar `priv` and the point `pub`. -/
axiom Vale_Hacl_Curve25519_64_leak
    (priv : Curve25519Buf) (pub : Curve25519Buf) : LeafLeak

/-- **Constant-time axiom**: the leakage trace of the `Hacl_Curve25519_64`
    leaf is the same at every pair of arguments. Both the scalar and the point
    carry HACL\*'s secret integer types, so no branch or memory index in the
    Montgomery ladder reads either; the ladder swap is a `cswap2` mask. Cited
    in `ValeCoqAxioms.lean`, which also records that the inline-assembly build
    of this leaf is not re-checked by Vale's taint analyser. -/
axiom Vale_Hacl_Curve25519_64_CT :
    SecretIndependent (fun q : Curve25519Buf × Curve25519Buf =>
      Vale_Hacl_Curve25519_64_leak q.1 q.2)

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the `Vale/ChaCha20Vec256.lean` pilot pattern: registering
the leaf so the verified front accepts `RCall
"Hacl_Curve25519_64_scalarmult"` as a well-formed extCall whose
argument shape is `2 × TBytes 32`. -/

/-- Register `Vale_Hacl_Curve25519_64_denote` → leaf
    `Hacl_Curve25519_64_scalarmult` (the C symbol name, matching the
    HACL\* `Hacl_Curve25519_64.c` export). -/
@[rust_cmd_pattern]
def curve25519_64Pattern : LowCTPattern where
  name      := "Hacl_Curve25519_64_scalarmult"
  fnHead    := ``Vale_Hacl_Curve25519_64_denote
  arity     := 2
  towerType := .TBytes 32   -- 32-byte X25519 buffer (scalar / point / out)

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a Curve25519 buffer
    (`TBytes 32` — 32 bytes, the RFC 7748 buffer size). -/
def curve25519BufTowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the Vale leaf

The Vale Curve25519 leaf is **non-aliasing** at the SSA level:
`out`, `priv`, `pub` are all distinct buffers in the HACL\* C
signature. We declare `destAliasOk := []` (the conservative
default) — the borrow checker correctly forbids aliased calls. -/

/-- Per-leaf signature for `Hacl_Curve25519_64_scalarmult`:
    no aliasing permitted (out / priv / pub all distinct in
    HACL\*'s C signature). -/
def curve25519_64LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "Hacl_Curve25519_64_scalarmult"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the Curve25519 scalar multiplication,
serving as the front-end input to the reflection pipeline. The body
is the single Vale-leaf call. -/

/-- One Curve25519 X25519 scalar-multiplication invocation. -/
noncomputable def valeCurve25519Lean
    (priv pub : Curve25519Buf) : Curve25519Buf :=
  Vale_Hacl_Curve25519_64_denote priv pub

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `VaesReflect.vaesEnc2WayBody` / `ChaCha20Vec256` pattern:
the front-end `reifyLowCT%` macro reads `knownOps` only, so we
hand-build the single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `valeCurve25519Lean`. Shape:
    `RSeq RSkip (RCall "Hacl_Curve25519_64_scalarmult"
                       __result [priv, pub])`. -/
def valeCurve25519Body : LowCT :=
  let priv_l   := loc "priv"     curve25519BufTowerType
  let pub_l    := loc "pub"      curve25519BufTowerType
  let result_l := loc "__result" curve25519BufTowerType
  .RSeq .RSkip
    (.RCall "Hacl_Curve25519_64_scalarmult"
            result_l [priv_l, pub_l])

/-- `ReifiedFunc` bundle for the Vale Curve25519 leaf. -/
def valeCurve25519Reified : ReifiedFunc :=
  { args    := [("priv", curve25519BufTowerType),
                ("pub",  curve25519BufTowerType)]
    body    := valeCurve25519Body
    retName := "__result" }

/-! ## §8. Inspection -/

#eval valeCurve25519Reified.args.map Prod.fst
  -- [priv, pub]
#eval valeCurve25519Reified.args.length     -- 2
#eval valeCurve25519Reified.retName         -- __result

end CatCrypt.Crypto.Vale.Curve25519
