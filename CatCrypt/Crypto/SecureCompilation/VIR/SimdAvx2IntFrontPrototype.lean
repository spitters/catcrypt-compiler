/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# SIMD AVX2 INTEGER-VECTOR front prototype (`vpxor` end-to-end) + breadth map

This file scopes the AVX2 integer-vector op family in the FRONT dialect and
prototypes the representative op (`vpxor`, 128-bit lane-wise xor), mirroring the
`SimdFrontPilot` `gf2p8mulb` template.

## The AVX2 integer family in `SimdOp`

The front `SimdOp` alphabet is larger than `{gf2p8mulb, vpshufb}`. The core
`SimdOp` inductive (`JasminDialect.lean`) carries the whole AVX2 integer family through
**two parametric constructors** plus one specialised one:

  * `bitwise (bop : JasminBinOp)` — the carry-free 128-bit bitwise ops. Covers
    `VPXOR` (`.xor`), `VPAND` (`.and`), `VPOR` (`.or`), and `VPANDN` (`.andn`,
    the Keccak-χ `(¬a)∧b` fused op). Denote = `bop.apply` at 128 bits (no
    cross-lane carry, so whole-register = lane-wise at any lane width).
  * `packed (bop : JasminBinOp) (laneW : Nat)` — packed per-lane arithmetic on a
    128-bit register split into `128/laneW` lanes. Covers `VPADDD`
    (`.add 32`), `VPADDQ` (`.add 64`), `VPSUBD`/`VPSUBQ` (`.sub 32/64`),
    `VPADDW`/`VPSUBW` (`.add/.sub 16`), `VPMULLW` (`.mul 16`), and the
    variable per-lane shifts `VPSLLVD/Q`, `VPSRLVD/Q` (`.shl/.shr 32/64`).
    Denote = `v128PackLanesW laneW bop` (per-lane, no cross-lane carry).
  * `mulhi16` — `VPMULHW` (packed signed high-16 multiply; ML-KEM NTT Montgomery).

The FRONT dialect exposes them all: `CatCryptOp.vsimd (op : SimdOp)` (binary,
both operands `.sword 128`) denotes via the backend `SimdOp.denote` waist
(`CatCryptDialect.lean`), and `DialectToJasminCom.toJExprD` lowers
`.vsimd (.bitwise b)` and `.vsimd (.packed b lw)` **1:1** to the matching
`JasminOp.vsimd` (arms already present, `DialectToJasminCom.lean`). So a `vpxor`,
`vpand`, `vpor`, `vpaddd`, `vpaddq`, `vpsub*`, `vpsllvq`, `vpsrlvq`, `vporq`
front body already translates, lowers, and denotes **with zero core edits** —
this file proves it for `vpxor`.

**The BYTE ENCODER and one op are outside this front coverage.**
`VsimdByteEncoder.encodeVsimdInst` has correct VEX bytes for bitwise
and/or/xor and packed add/sub/mullw/mulhi, but the packed SHIFT arms and
`.bitwise .andn` fall through to WRONG catch-all bytes, and `VPMULUDQ`
(Poly1305) has no `SimdOp` at all. See the worklist at the end.

## The op family and what it covers

`vpaddd/vpaddq/vpxor/vpand/vpor/vpsub + vpslld/vpsrld/vpsllvq/vpsrlvq/vporq`
is exactly the alphabet of the ARX + NTT + Keccak-SIMD + Poly1305 group. All of
it is representable in the front dialect; the remaining work is byte-level.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SimdAvx2IntFrontPrototype

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect SimdOp JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## The `vpxor` prototype — the representative integer op, end-to-end

This is the `SimdFrontPilot` skeleton verbatim, with `.gf2p8mulb` replaced by
`.bitwise .xor`. No core `SimdOp` constructor is added: `.bitwise .xor` already
exists and already lowers, so the prototype is a REAL end-to-end front op, not a
scaffold with a hole. (Had the op been missing — e.g. `VPMULUDQ` —
this same skeleton would compile only after the one-line constructor + denote +
lowering + encoder arms listed in the worklist; the structure is identical.) -/

/-- Context `[a, b]`, each a 128-bit vector carried as `.sword 128`. -/
abbrev xorCtx : Ctx := [.sword 128, .sword 128]

def vA : Ctxt.Var (d := catCryptDialect) xorCtx (.sword 128) := .here
def vB : Ctxt.Var (d := catCryptDialect) xorCtx (.sword 128) := .there .here

/-- `VPXOR` (128-bit lane-wise xor) expressed as a real FRONT-dialect
    `.vsimd (.bitwise .xor)` op — the OWNED inlined route, not an `extCall` leaf. -/
def eXorV : Expr catCryptDialect xorCtx (.sword 128) :=
  .mk (.vsimd (.bitwise .xor)) rfl (.cons vA (.cons vB .nil))

/-- A one-op front body: `r := vpxor(a, b)` then return. -/
def xorComCD : Com catCryptDialect xorCtx (.sword 128) :=
  .var eXorV (.ret .here)

/-! ### 1. Translates + lowers (the OWNED inlined route) -/

/-- The front body lowers through the VERIFIED `cryptoDialectToJasminCom` map:
    `.vsimd (.bitwise .xor)` maps 1:1 to jasmin `.vsimd (.bitwise .xor)`, an
    inlined `VPXOR` (not a `call` leaf). -/
theorem xorComCD_isSome : (cryptoDialectToJasminCom xorComCD).isSome := by
  native_decide

/-- The lowered Jasmin-dialect program (in the `mapTy`-mapped context). -/
def xorComJ : Com jasminDialect (mapCtx xorCtx) (mapTy (.sword 128)) :=
  (cryptoDialectToJasminCom xorComCD).get xorComCD_isSome

/-! ### 2. Denote = spec (BitVec lane-wise xor over 128 bits) -/

/-- A concrete valuation builder for `xorCtx`. -/
def xorVal (a b : BitVec 128) : Ctxt.Valuation (d := catCryptDialect) xorCtx :=
  .cons a (.cons b .nil)

/-- **Front `denote = spec` (symbolic).** On `[a, b]` the front body denotes to the
    128-bit lane-wise xor `a ^^^ b`. `rfl`: the `.vsimd (.bitwise .xor)` denote IS
    `SimdOp.denote (.bitwise .xor) a b = (JasminBinOp.xor).apply a b = a ^^^ b`
    (carry-free, so whole-register xor = lane-wise xor at any lane width). -/
theorem xorComCD_denote (a b : BitVec 128) :
    xorComCD.denote (xorVal a b) = a ^^^ b := rfl

/-! ## Mapping table — every AVX2 integer op → BitVec denotation → primitive family

`kind` column: **B**oolean (carry-free, trivial denote), **A**rithmetic (mod 2^k
per lane), **S**hift (per-lane variable/immediate). `front?` = expressible in the
front dialect TODAY; `bytes?` = has correct VEX bytes in `encodeVsimdInst`.

| AVX2 op   | SimdOp                | BitVec denotation (per 128-bit reg) | kind | front? | bytes? | needed by |
|-----------|-----------------------|-------------------------------------|------|--------|--------|-----------|
| VPXOR     | `.bitwise .xor`       | `a ^^^ b`                           | B    | yes    | yes    | ChaCha/BLAKE/Keccak/SHA-mb/Poly (all ARX) |
| VPAND     | `.bitwise .and`       | `a &&& b`                           | B    | yes    | yes    | SHA-mb Ch/Maj, masking |
| VPOR      | `.bitwise .or`        | `a ||| b`                           | B    | yes    | yes    | rotate-synthesis (`shl∨shr`) everywhere |
| VPORQ     | `.bitwise .or`        | `a ||| b` (AVX512 alias @128)       | B    | yes    | yes    | Keccak-avx2 rotate `vpsllvq∨vpsrlvq∨vporq` |
| VPANDN    | `.bitwise .andn`      | `(~~~a) &&& b`                      | B    | yes    | NO*    | Keccak χ `(¬B₊₁)∧B₊₂` (fused, 1 op) |
| VPADDD    | `.packed .add 32`     | per-32-lane `a+b (mod 2^32)`        | A    | yes    | yes    | ChaCha/BLAKE quarter-round add; SHA-mb Σ/Δ add |
| VPADDQ    | `.packed .add 64`     | per-64-lane `a+b (mod 2^64)`        | A    | yes    | yes    | Poly1305 limb accumulate; Keccak lane add |
| VPSUBD    | `.packed .sub 32`     | per-32-lane `a-b (mod 2^32)`        | A    | yes    | yes    | NTT butterfly (u32-lane) subtract |
| VPSUBQ    | `.packed .sub 64`     | per-64-lane `a-b (mod 2^64)`        | A    | yes    | yes    | field-lane subtract |
| VPADDW    | `.packed .add 16`     | per-16-lane `a+b (mod 2^16)`        | A    | yes    | yes    | ML-KEM NTT add (8×i16) |
| VPSUBW    | `.packed .sub 16`     | per-16-lane `a-b (mod 2^16)`        | A    | yes    | yes    | ML-KEM NTT butterfly subtract |
| VPMULLW   | `.packed .mul 16`     | per-16-lane low `a*b (mod 2^16)`    | A    | yes    | yes    | ML-KEM NTT Montgomery low half |
| VPMULHW   | `.mulhi16`            | per-16-lane signed high `(a*b)>>16` | A    | yes    | yes    | ML-KEM NTT Montgomery high half |
| VPSLLD    | `.packed .shl 32`     | per-32-lane `a <<< b.toNat`         | S    | yes    | NO*    | ARX rotate-left synthesis (imm shift) |
| VPSRLD    | `.packed .shr 32`     | per-32-lane `a >>> b.toNat`         | S    | yes    | NO*    | ARX rotate-right synthesis; SHA-mb σ shift |
| VPSLLVQ   | `.packed .shl 64`     | per-64-lane `a <<< b.toNat`         | S    | yes    | NO*    | Keccak-avx2 ρ per-lane variable rotate |
| VPSRLVQ   | `.packed .shr 64`     | per-64-lane `a >>> b.toNat`         | S    | yes    | NO*    | Keccak-avx2 ρ per-lane variable rotate |
| VPMULUDQ  | (NONE — new op)       | even-lane `(a&2^32-1)*(b&2^32-1)`→u64 | A  | NO     | NO     | Poly1305 32×32→64 limb multiply |

`*` bytes gap: `.bitwise .andn` and every `.packed .sh{l,r} _` hit the
`encodeVsimdInst` catch-alls (`.bitwise _ => 0xEF` = VPXOR bytes; `.packed _ _ =>
0xFE` = VPADDD bytes), so they denote + lower correctly but would emit WRONG
machine bytes. `VPMULUDQ` is an even-lane widening multiply (like
`mulhi16`), not expressible via `packed`/`bitwise` — it needs a new constructor.

### Rotate is synthesised, not a primitive

No `VPROL*`/`VPROR*` is needed: a lane rotate is `(x <<< n) ||| (x >>> (w-n))` =
`.packed .shl w ∘ .packed .shr w ∘ .bitwise .or`. This is the KAT-pinned idiom in
`KeccakAvx2Emit.laneRotl` and `Sha2MultiBufAvx2Emit.rotrSynth`
(`rotrSynth_eq : rotrSynth x n = BitVec.rotateRight x n`). So closing the two
SHIFT byte arms + `VPORQ` (already an `.or` alias) is what unlocks all of
ChaCha/BLAKE/Keccak/SHA-mb rotation.

### Per-primitive coverage summary

| primitive        | op set needed                                    | front-expressible?     | byte-blocked on |
|------------------|--------------------------------------------------|------------------------|-----------------|
| ChaCha / BLAKE   | VPADDD + VPXOR + rotate(VPSLLD∨VPSRLD∨VPOR)       | yes                    | VPSLLD/VPSRLD bytes |
| Keccak-avx2      | VPXOR + VPANDN + rotate(VPSLLVQ∨VPSRLVQ∨VPORQ)    | yes                    | VPANDN + VPSLLVQ/VPSRLVQ bytes |
| SHA-multibuf     | VPADDD + VPAND/VPXOR + shift(VPSRLD/VPSLLD)       | yes                    | VPSLLD/VPSRLD bytes |
| ML-KEM NTT       | VPMULLW + VPMULHW + VPADDW/VPSUBW                 | yes                    | none (fully wired) |
| Poly1305         | VPMULUDQ + VPADDQ                                 | partial (VPADDQ only)  | VPMULUDQ (new op) |

**ML-KEM NTT is already fully wired end-to-end (semantics + lowering + bytes).**

## Core-wiring worklist (byte/op gaps)

Two constructors are NOT needed (bitwise/packed already cover the family). The
precise remaining edits, all in files this prototype does NOT own:

1. **Packed-shift VEX bytes** (`VsimdByteEncoder.encodeVsimdInst`, ~4 arms +
   mnemonics). Add before the `.packed _ _` catch-all:
     * `.packed .shl 32 → VPSLLVD` (VEX 0F38 `0x47`),
       `.packed .shr 32 → VPSRLVD` (0F38 `0x45`),
       `.packed .shl 64 → VPSLLVQ` (VEX.W 0F38 `0x47`),
       `.packed .shr 64 → VPSRLVQ` (VEX.W 0F38 `0x45`).
   These are the variable per-lane shifts (`0F38` map), matching the
   `v128PackLanesW` per-lane-`b` denotation. `encAvx2_0F38` already exists (used
   by `vpshufb`); reuse it with the opcode + W bit. Add the two-way gas pins
   next to the existing ones. Effort: ~S per arm (encoder reuse + 1 pin each);
   ~1h total. Semantics + front + lowering already done → zero proof churn there.
   (If immediate-form `VPSLLD`/`VPSRLD` (0F 72 /6, /2) is also wanted for the
   broadcast-imm case, that is a separate `encodeVsimdShift`-style arm — but the
   variable form suffices for the front denote, which reads `b` per lane.)

2. **`VPANDN` bytes + mnemonic** (`VsimdByteEncoder.encodeVsimdInst` line ~124,
   `SimdOp.mnemonic` line ~534). Add `.bitwise .andn → encAvx2Alu 0xDF`
   (`VPANDN`) BEFORE the `.bitwise _ => 0xEF` catch-all, and
   `.bitwise .andn => "VPANDN"` before the `VPBITWISE` catch-all. Effort: ~S
   (~20min). Semantics (`(~~~a)&&&b`) + front + lowering already done.

3. **`VPMULUDQ` — new op** (Poly1305 32×32→64 even-lane multiply). This
   is the ONLY constructor addition. Full add:
     * `SimdOp.vpmuludq` constructor (+ `argTys`/`retTy` = `[reg128,reg128]→reg128`,
       `mnemonic "VPMULUDQ"`) in `JasminDialect.lean`.
     * denote arm `SimdOp.denote .vpmuludq := vpmuludqW` where
       `vpmuludqW a b := zext32(evenLane0 a)*zext32(evenLane0 b) ‖
        zext32(evenLane2 a)*zext32(evenLane2 b)` (2×u64 result from the two
       even u32 lanes) — copy the KAT-pinned `Vec128Model` even-lane multiply.
     * lowering arm `| .vpmuludq => some (… .vsimd .vpmuludq …)` in
       `DialectToJasminCom.toJExprD` (`.vsimd op` block, alongside `.mulhi16`).
     * byte arm `.vpmuludq → encAvx2Alu 0xF4` in `encodeVsimdInst` + gas pin.
   Effort: ~M (~half day: the denote def + its Vec128 KAT bridge is the bulk;
   the front/lowering/byte arms are mechanical 1-liners each). Only needed if
   Poly1305-SIMD is prioritised; ARX+NTT+Keccak need none of this.

Net: the "which SIMD extensions for what primitive" answer is that the front
BREADTH is essentially DONE for ARX/NTT/Keccak/SHA-mb — the residue is ~1h of
byte-encoder arms (items 1–2), and Poly1305 alone needs the one new op (item 3).
-/

end CatCrypt.Crypto.SecureCompilation.VIR.SimdAvx2IntFrontPrototype
