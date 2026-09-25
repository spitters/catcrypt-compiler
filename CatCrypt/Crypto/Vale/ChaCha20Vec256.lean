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
public meta import CatCrypt.Crypto.Jasmin.ChaCha20Block
public import CatCrypt.Crypto.Jasmin.ChaCha20Block


@[expose] public section
set_option autoImplicit false

/-!
# Vale-verified ChaCha20-Vec256 leaf

This module declares the Vale-verified HACL\* `Hacl_Chacha20_Vec256`
implementation (AVX2 4-way SIMD, 256-bit lane-parallel) as an opaque
verified-CT leaf for CatCrypt's verified front, following the established
extCall pattern (Jasmin.LowCT `RCall`).

## Pilot scope (Option A — Vale-leaf adoption)

This is the FIRST adoption of a Vale-verified leaf into CatCrypt's
verified-front pipeline. The pattern established here scales to:

* AES-GCM (Vale-verified AES-NI + GHASH)
* Curve25519 (Vale-verified Montgomery ladder)
* SHA-256-asm (Vale-verified SHA extensions)
* GHASH (Vale-verified PCLMULQDQ)

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

* **File**: `Hacl_Chacha20_Vec256.c` (libcrux/HACL*)
  (built via libcrux's HACL\* mirror, exported with C symbol
  `Hacl_Chacha20_Vec256_chacha20_encrypt_256`).
* **F\* source**: `Hacl.Streaming.Chacha20_Vec256.fst` in the upstream
  hacl-star repository; the AVX2 4-way SIMD-vectorised body is in
  `Hacl.Impl.Chacha20.Vec.fst` (parametric over a vector width that
  Hacl_Chacha20_Vec256 instantiates at 8 lanes × 32-bit = 256-bit).
* **Vale proof**: ChaCha20 vectorisation is established functionally
  in F\* by `Spec.Chacha20` agreement (proof in `Hacl.Impl.Chacha20.Vec`);
  the Vec256 instantiation inherits this. CT comes from the lane-
  parallel structure (no data-dependent branches or memory accesses).
* **NIST CAVP**: the HACL\* tests vendor RFC 8439 §2.3.2 + §2.4.2 KATs;
  `Hacl_Chacha20_Vec256_chacha20_encrypt_256` matches RFC 8439's
  published byte 0 = `0x76` on the zero-key keystream.

## Leaf C signature

```c
extern void Hacl_Chacha20_Vec256_chacha20_encrypt_256(
    uint32_t len, uint8_t *out, uint8_t *text, uint8_t *key, uint8_t *n,
    uint32_t ctr);
```

That is: `out = chacha20(key, nonce, ctr) XOR text` over `len` bytes.

## Denotation and trust delta

The leaf denotation is grounded in CatCrypt's own RFC 8439 ChaCha20 block
function, so no leaf-specific value axiom enters:

1. **Vale_Hacl_Chacha20_Vec256_denote**: defined as keystream-XOR using the
   owned `ChaCha20Block.chachaBlock` (RFC 8439 §2.3 20-round block function
   with feedforward, `native_decide`-validated against the RFC 8439 §2.3.2
   test vector). The keystream block is XORed into the plaintext operand.

Above CatCrypt's normal axiom set we still trust:

2. **Vale_Hacl_Chacha20_Vec256_CT**: the leaf is constant-time in `key`
   and `text`. Sourced from Vale's taint-tracking proof / HACL\*'s
   secret-independence proof on the vectorised body.

3. **Symbol identity at link time**: the C symbol our jasmin/C-bridge
   calls agrees with this denotation (not, say, a maliciously substituted
   ChaCha20 implementation). Standard C-linker trust.

The trust delta is **strictly smaller** than the all-our-emit path
when the alternative is a hand-emitted SIMD body we have not proved
against Vec256's published F\* spec.
-/

namespace CatCrypt.Crypto.Vale.ChaCha20Vec256

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.Vale.LeafLeakage

/-! ## §1. Surface type

The ChaCha20 operand at the leaf's verified-front ABI, a concrete 16-word
state (`Fin 16 → BitVec 32`) shared with the owned RFC 8439 block function.
The four ABI operands (`key`, `nonce`, `counter`, `pt`) each carry their
RFC 8439 words in this packed word vector. -/

/-- A ChaCha20 operand word vector (16 × 32-bit words), the state type of
    the owned `ChaCha20Block.chachaBlock`. -/
abbrev ChaCha20Vec256Block : Type :=
  CatCrypt.Crypto.Jasmin.ChaCha20Block.ChaChaState

/-! ## §2. Leaf denotation (grounded in the owned RFC 8439 block function)

The leaf denotation is the RFC 8439 ChaCha20 encrypt: assemble the initial
state from the key/counter/nonce operands, run the owned block function
`ChaCha20Block.chachaBlock` to produce the keystream block, and XOR it into
the plaintext operand. No leaf-specific value axiom enters here. -/

/-- The leaf denotation: the RFC 8439 ChaCha20 encrypt of the plaintext
    operand under the key/nonce/counter operands. The initial state is
    assembled by `ChaCha20Block.initState` from the key words (state slots
    4–11), counter word (slot 12), and nonce words (slots 13–15) of the
    operands; the keystream block is the owned `ChaCha20Block.chachaBlock`
    of that state, and the ciphertext is the pointwise XOR of the keystream
    with the plaintext operand.

    The C signature `Hacl_Chacha20_Vec256_chacha20_encrypt_256` processes a
    `len`-byte buffer as `len/256` 4-way (256-byte) SIMD groups; the verified
    front emits the single-block ABI (one 64-byte block per call). -/
noncomputable def Vale_Hacl_Chacha20_Vec256_denote
    (key nonce counter pt : ChaCha20Vec256Block) : ChaCha20Vec256Block :=
  let init : CatCrypt.Crypto.Jasmin.ChaCha20Block.ChaChaState :=
    CatCrypt.Crypto.Jasmin.ChaCha20Block.initState
      (fun i : Fin 8 => key ⟨i.val + 4, by omega⟩)
      (counter 12)
      (fun i : Fin 3 => nonce ⟨i.val + 13, by omega⟩)
  let keystream := CatCrypt.Crypto.Jasmin.ChaCha20Block.chachaBlock init
  fun i => keystream i ^^^ pt i

/-- **Leakage function**: the observable trace the `Hacl_Chacha20_Vec256`
    leaf emits on the given nonce, counter, key and plaintext. -/
noncomputable opaque Vale_Hacl_Chacha20_Vec256_leak
    (nonce counter : ChaCha20Vec256Block)
    (secrets : ChaCha20Vec256Block × ChaCha20Vec256Block) : LeafLeak

/-- **Constant-time axiom**: at each fixed nonce and block counter, the
    leakage trace of the `Hacl_Chacha20_Vec256` leaf is the same at every key
    and plaintext. The lane-parallel round function is add / xor / rotate on
    vector registers with no data-dependent branch or memory access. The nonce
    and the counter are the public parameters; the key and the text are the
    secret ones. Cited in `ValeCoqAxioms.lean`. -/
axiom Vale_Hacl_Chacha20_Vec256_CT
    (nonce counter : ChaCha20Vec256Block) :
    SecretIndependent (Vale_Hacl_Chacha20_Vec256_leak nonce counter)

/-! ## §3. `@[rust_cmd_pattern]` registration

Following the VAES / `vaesenc_2way_256` pattern: registering the
leaf so the verified front accepts `RCall
"Hacl_Chacha20_Vec256_chacha20_encrypt_256"` as a well-formed
extCall whose argument shape is `4 × TBytes 32`. -/

/-- Register `Vale_Hacl_Chacha20_Vec256_denote` → leaf
    `Hacl_Chacha20_Vec256_chacha20_encrypt_256` (the C symbol name,
    matching the HACL\* `Hacl_Chacha20_Vec256.c` export). -/
@[rust_cmd_pattern]
def chacha20Vec256Pattern : LowCTPattern where
  name      := "Hacl_Chacha20_Vec256_chacha20_encrypt_256"
  fnHead    := ``Vale_Hacl_Chacha20_Vec256_denote
  arity     := 4
  towerType := .TBytes 32   -- 4 × 64 B packed across 256-bit lanes

/-! ## §4. Tower-type abbreviation -/

/-- Tower type of a Vec256 4-way ChaCha20 operand
    (`TBytes 32` = `memref 4`, the canonical 256-bit packed shape). -/
def chacha20Vec256TowerType : TowerType := .TBytes 32

/-! ## §5. `LeafSig` entry for the Vale leaf

The Vale leaf is **non-aliasing** at the SSA level: `out`, `text`,
`key`, `nonce` are all distinct buffers in the HACL\* C signature.
We declare `destAliasOk := []` (the conservative default) — the
borrow checker correctly forbids aliased calls. -/

/-- Per-leaf signature for `Hacl_Chacha20_Vec256_chacha20_encrypt_256`:
    no aliasing permitted (out / text / key / nonce all distinct in
    HACL\*'s C signature). -/
def chacha20Vec256LeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "Hacl_Chacha20_Vec256_chacha20_encrypt_256"
  destAliasOk := []

/-! ## §6. Pure-Lean wrapper — the spec

A pure-Lean wrapper for the 4-way Vec256 ChaCha20 keystream block,
serving as the front-end input to the reflection pipeline. The body
is the single Vale-leaf call. -/

/-- One Vec256 4-way ChaCha20 keystream-block invocation. -/
noncomputable def valeChaCha20Vec256Lean
    (key nonce counter pt : ChaCha20Vec256Block) : ChaCha20Vec256Block :=
  Vale_Hacl_Chacha20_Vec256_denote key nonce counter pt

/-! ## §7. Hand-built `LowCT` body (front-end input)

Following the `VaesReflect.vaesEnc2WayBody` pattern: the front-end
`reifyLowCT%` macro reads `knownOps` only, so we hand-build the
single-`RCall` body the reifier would produce. -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `valeChaCha20Vec256Lean`. Shape:
    `RSeq RSkip (RCall "Hacl_Chacha20_Vec256_chacha20_encrypt_256"
                        __result [key, nonce, counter, pt])`. -/
def valeChaCha20Vec256Body : LowCT :=
  let key_l     := loc "key"      chacha20Vec256TowerType
  let nonce_l   := loc "nonce"    chacha20Vec256TowerType
  let counter_l := loc "counter"  chacha20Vec256TowerType
  let pt_l      := loc "pt"       chacha20Vec256TowerType
  let result_l  := loc "__result" chacha20Vec256TowerType
  .RSeq .RSkip
    (.RCall "Hacl_Chacha20_Vec256_chacha20_encrypt_256"
            result_l [key_l, nonce_l, counter_l, pt_l])

/-- `ReifiedFunc` bundle for the Vale ChaCha20-Vec256 leaf. -/
def valeChaCha20Vec256Reified : ReifiedFunc :=
  { args    := [("key",     chacha20Vec256TowerType),
                ("nonce",   chacha20Vec256TowerType),
                ("counter", chacha20Vec256TowerType),
                ("pt",      chacha20Vec256TowerType)]
    body    := valeChaCha20Vec256Body
    retName := "__result" }

/-! ## §8. Inspection -/

#eval valeChaCha20Vec256Reified.args.map Prod.fst
  -- [key, nonce, counter, pt]
#eval valeChaCha20Vec256Reified.args.length     -- 4
#eval valeChaCha20Vec256Reified.retName         -- __result

end CatCrypt.Crypto.Vale.ChaCha20Vec256
