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


@[expose] public section
set_option autoImplicit false

/-!
# Ed25519 point-decompression leaf over `Fp_{25519}`

This module is the point-decompression leaf for Ed25519 (RFC 8032 §5.1.3),
wired into CatCrypt's verified front via the extCall pattern
(`Jasmin.LowCT` `RCall`), following the leaf shape of
`Vale/Secp256k1FieldMul.lean` and `Vale/PallasFieldMul.lean`.

The leaf recovers a twisted-Edwards point `(x, y)` from a 32-byte compressed
encoding — the `y` coordinate in the low 255 bits, the sign bit of `x` in
bit 255 — and packs it into the 200-byte extended-coordinate slot
`X ‖ Y ‖ Z ‖ Ta ‖ Tb`. It is the missing owned kernel behind the Wycheproof
EdDSA verify path (which needs decompression of both `R` and the public key
`A` before checking `[S]B == R + [h]A`).

## Value grounding

`ed25519DecompressDenote` mirrors, definitionally, the AUCurves Gallina
reference `ed25519_decompress_gallina`
(`AUCurves/src/Bedrock/End2End/Ed25519/DecompressVerified.v:88`), which is the
executable spec the AUCurves WP bridge ties the `fe25519_decompress_*` leaf to
(`DecompressBody.v`, `ed25519_decompress_{R,A}_spec`). The recovery formula
`recoverX` mirrors `recover_x`
(`DecompressVerified.v:65`): with `p = 2^255 − 19`, `d = ed25519D`,

```
  y2 = y²                 u = y2 − 1              v = d·y2 + 1
  x  = (u·v⁷)·(u·v³)^((p−5)/8)          (the p ≡ 5 mod 8 sqrt shortcut)
  if v·x² ≠ u then x ← x·√(−1)
  choose the sign of x to match the sign bit
```

and the packing `packXyzt5 x y 1 x y` mirrors `pack_xyzt5`
(`XyztAddVerified.v:82`). The two named exports of the Coq twin
(`ed25519_decompress_R_spec`, `ed25519_decompress_A_spec`) are both this same
function; `_R` consumes the first 32 bytes of a 64-byte signature, `_A` the
32-byte public key — both are `firstn 32 bs`, matched here by `bs.take 32`.

## Scope of what is proved here

* `ed25519DecompressDenote_length`: the output is 200 bytes — mirrors
  `ed25519_decompress_gallina_length` (`DecompressVerified.v:100`).
* `ed25519DecompressDenote_eq`: the output is `packXyzt5 (recoverX y sign) y 1
  (recoverX y sign) y`, the extended-coordinate packing of the recovered point.
* `ed25519D_pin` / `ed25519Sqrtm1_sq`: the two curve constants are pinned to
  their defining congruences (`121666·d ≡ −121665`, `√(−1)² ≡ −1 mod p`),
  mirroring the AUCurves `ed25519_d` definition and `ed25519_sqrtm1_sq`
  (`DecompressVerified.v:60`, proved there by `vm_compute`).

The AUCurves twin is `Global Opaque` and, by its own comment
(`DecompressVerified.v:11`), does not branch on validity — it never returns
`None` and does not itself certify that the recovered `(x, y)` lies on the
curve. This module makes no curve-membership claim beyond the twin: it grounds
the byte-level value of the leaf on the AUCurves Gallina reference and the two
constant congruences, nothing more.

## Leaf C signature

```c
extern void ed25519_decompress(uint8_t out[200], const uint8_t in[32]);
```

`out` is the extended-coordinate slot `X ‖ Y ‖ Z ‖ Ta ‖ Tb` (five 40-byte
little-endian field limbs); `in` is the 32-byte compressed point. The emitted
call site is `RCall "ed25519_decompress"`, binding the C symbol; symbol
identity at link time is standard C-linker trust.
-/

namespace CatCrypt.Crypto.Vale.Ed25519Decompress

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## §1. The Ed25519 base prime, curve constant, and `√(−1)` -/

/-- The Ed25519 base-field prime `p = 2^255 − 19`. -/
def ed25519P : Nat := 2 ^ 255 - 19

/-- The twisted-Edwards curve constant `d = −121665 / 121666 mod p`
    (`AUCurves` `XyztAddVerified.v` `ed25519_d`). -/
def ed25519D : Nat :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `121666 · d ≡ −121665 (mod p)` — the constant `d`'s defining congruence
    (`d = −121665 / 121666`). -/
theorem ed25519D_pin :
    (121666 * ed25519D) % ed25519P = ed25519P - 121665 := by
  unfold ed25519D ed25519P; rfl

/-- `√(−1) mod p = 2^((p−1)/4) mod p`, used when the trial root needs the
    quadratic-non-residue correction (`AUCurves` `ed25519_sqrtm1`). -/
def ed25519Sqrtm1 : Nat :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- `√(−1)² ≡ −1 (mod p)` — mirrors `AUCurves` `ed25519_sqrtm1_sq`
    (`DecompressVerified.v:60`, proved there by `vm_compute`). -/
theorem ed25519Sqrtm1_sq :
    (ed25519Sqrtm1 * ed25519Sqrtm1) % ed25519P = ed25519P - 1 := by
  unfold ed25519Sqrtm1 ed25519P; rfl

/-! ## §2. Little-endian byte codec (mirroring `le_combine` / `le_split`) -/

/-- Little-endian combine: byte list to a natural, least-significant byte
    first (mirrors `coqutil` `le_combine`). -/
def leCombine : List (BitVec 8) → Nat
  | []      => 0
  | b :: bs => b.toNat + 256 * leCombine bs

/-- Little-endian split of `v` into `n` bytes, least-significant first
    (mirrors `coqutil` `le_split`). -/
def leSplit (n : Nat) (v : Nat) : List (BitVec 8) :=
  (List.range n).map (fun i => BitVec.ofNat 8 (v / 256 ^ i % 256))

/-- `leSplit n v` has exactly `n` bytes. -/
theorem leSplit_length (n v : Nat) : (leSplit n v).length = n := by
  simp [leSplit]

/-! ## §3. The decompression denotation (grounded in the AUCurves twin) -/

/-- Recover `x` from `y` and the sign bit, the `p ≡ 5 mod 8` sqrt shortcut.
    Mirrors `recover_x` (`AUCurves` `DecompressVerified.v:65`). Field
    subtractions are written `(a + (p − b)) % p` on reduced operands, matching
    the Coq `(· − ·) mod p` over `Z`. -/
def recoverX (y sign : Nat) : Nat :=
  let p       := ed25519P
  let y2      := (y * y) % p
  let u       := (y2 + (p - 1)) % p
  let v       := (ed25519D * y2 + 1) % p
  let uv3     := (u * (v ^ 3 % p)) % p
  let uv7     := (u * (v ^ 7 % p)) % p
  let expVal  := uv3 ^ ((p - 5) / 8) % p
  let xCand   := (uv7 * expVal) % p
  let vxx     := (v * xCand * xCand) % p
  let xPre    := if vxx = u then xCand else (xCand * ed25519Sqrtm1) % p
  if xPre % 2 = sign then xPre else (p - xPre) % p

/-- Pack five field elements into the 200-byte extended-coordinate slot
    (five 40-byte little-endian limbs). Mirrors `pack_xyzt5`
    (`AUCurves` `XyztAddVerified.v:82`). -/
def packXyzt5 (x y z ta tb : Nat) : List (BitVec 8) :=
  leSplit 40 x ++ leSplit 40 y ++ leSplit 40 z ++ leSplit 40 ta ++ leSplit 40 tb

/-- `packXyzt5` produces exactly 200 bytes — mirrors `pack_xyzt5_length`. -/
theorem packXyzt5_length (x y z ta tb : Nat) :
    (packXyzt5 x y z ta tb).length = 200 := by
  simp [packXyzt5, List.length_append, leSplit_length]

/-- **Denotation**: the `ed25519_decompress` leaf recovers a twisted-Edwards
    point from the 32-byte compressed encoding and packs it as the 200-byte
    extended-coordinate slot. Definitionally the AUCurves Gallina reference
    `ed25519_decompress_gallina` (`DecompressVerified.v:88`): strip the sign
    bit from byte 31, read `y` from the low 255 bits mod `p`, recover `x` via
    `recoverX`, pack `X = x, Y = y, Z = 1, Ta = x, Tb = y`. Inputs longer than
    32 bytes (the 64-byte signature for the `R` component) consult only the
    first 32 bytes. -/
def ed25519DecompressDenote (bs : List (BitVec 8)) : List (BitVec 8) :=
  let bs32   := bs.take 32
  let b31    := (bs32[31]?).getD 0#8
  let sign   := b31.toNat / 128
  let b31low : BitVec 8 := BitVec.ofNat 8 (b31.toNat % 128)
  let low31  := bs32.take 31
  let yBytes := low31 ++ [b31low]
  let y      := leCombine yBytes
  let yMod   := y % ed25519P
  let x      := recoverX yMod sign
  packXyzt5 x yMod 1 x yMod

/-- **Value spec (structure).** The leaf output is the extended-coordinate
    packing of the recovered point, `packXyzt5 x y 1 x y` with `y` the parsed
    coordinate and `x = recoverX y sign`. Definitional. -/
theorem ed25519DecompressDenote_eq (bs : List (BitVec 8)) :
    ed25519DecompressDenote bs =
      (let b31  := ((bs.take 32)[31]?).getD 0#8
       let sign := b31.toNat / 128
       let y    := leCombine ((bs.take 32).take 31 ++
                     [BitVec.ofNat 8 (b31.toNat % 128)]) % ed25519P
       packXyzt5 (recoverX y sign) y 1 (recoverX y sign) y) :=
  rfl

/-- **Value spec (length).** The leaf output is 200 bytes — mirrors
    `ed25519_decompress_gallina_length` (`DecompressVerified.v:100`). -/
theorem ed25519DecompressDenote_length (bs : List (BitVec 8)) :
    (ed25519DecompressDenote bs).length = 200 := by
  simp only [ed25519DecompressDenote]
  exact packXyzt5_length _ _ _ _ _

/-! ## §4. `@[rust_cmd_pattern]` registration -/

/-- Register `ed25519DecompressDenote` → leaf `ed25519_decompress`.
    The `towerType` field names the destination type (the 200-byte extended
    slot). The single argument is the 32-byte compressed point, typed
    precisely in the hand-built body (`§8`); this leaf is not homogeneous in
    the argument/result width, so the hand-built body — not the reifier — is
    the authoritative source of the per-slot typing. -/
@[rust_cmd_pattern]
def ed25519DecompressPattern : LowCTPattern where
  name      := "ed25519_decompress"
  fnHead    := ``ed25519DecompressDenote
  arity     := 1
  towerType := .TBytes 200

/-! ## §5. Tower-type abbreviations -/

/-- Tower type of the 32-byte compressed input point. -/
def ed25519CompressedTowerType : TowerType := .TBytes 32

/-- Tower type of the 200-byte extended-coordinate output slot. -/
def ed25519XyztTowerType : TowerType := .TBytes 200

/-! ## §6. `LeafSig` entry -/

/-- Per-leaf signature for `ed25519_decompress`: no aliasing permitted
    (out / in distinct; the output slot is wider than the input). -/
def ed25519DecompressLeafSig : CatCrypt.Crypto.Jasmin.LeafSig where
  name        := "ed25519_decompress"
  destAliasOk := []

/-! ## §7. Pure-Lean wrapper -/

/-- One Ed25519 point-decompression invocation. -/
def ed25519DecompressLean (bs : List (BitVec 8)) : List (BitVec 8) :=
  ed25519DecompressDenote bs

/-! ## §8. Hand-built `LowCT` body (front-end input) -/

def loc (n : String) (t : TowerType) : Located :=
  { locVar := n, locSrc := t }

/-- The `LowCT` body for `ed25519DecompressLean`. Shape:
    `RSeq RSkip (RCall "ed25519_decompress" __result [pt])`, with `pt` the
    32-byte compressed input and `__result` the 200-byte extended slot. -/
def ed25519DecompressBody : LowCT :=
  let pt_l     := loc "pt"       ed25519CompressedTowerType
  let result_l := loc "__result" ed25519XyztTowerType
  .RSeq .RSkip
    (.RCall "ed25519_decompress" result_l [pt_l])

/-- `ReifiedFunc` bundle for the Ed25519 point-decompression leaf. -/
def ed25519DecompressReified : ReifiedFunc :=
  { args    := [("pt", ed25519CompressedTowerType)]
    body    := ed25519DecompressBody
    retName := "__result" }

/-! ## §9. Verify orchestration body (`[S]B == R + [h]A`)

The verify equation `[S]B == R + [h]A` composes this decompression leaf with
the Ed25519 scalar-mult, Edwards-add, compress, hash, and scalar leaves.
`ed25519VerifyBody` sequences those leaf `RCall`s exactly as the AUCurves
rustcmd `ed25519_verify`
(`AUCurves/curve25519-jasmin-rs/src/ed25519_rustcmd/verify.rs`), which is
verified end-to-end by AUCurves `safe_cmd_correct_ed` / `Verify_Strong_Correctness`.
Each leaf named below is a trust boundary at its own layer:

* `ed25519_decompress` — bridged in this module (grounded on the AUCurves
  Gallina decompression twin).
* `ed25519_scalarmult_base`, `ed25519_scalarmult`, `ed25519_xyzt_add`,
  `ed25519_compress` — the group leaves; their field-leaf `Com`s live in
  `EdDSA/Ed25519GroupEmit.lean` / `Jasmin/Ed25519/CompressEmit.lean`.
* `sha512_64`, `scalar_reduce`, `scalar_lt_L`, `bytes_equal_32`, the
  `memmove_*` region copies — the hash / scalar / plumbing leaves.

This body is the owned accept/reject entry point; end-to-end verify
correctness (the reduction of `[S]B == R + [h]A` to the leaf specs) is the
cited AUCurves twin, not re-proved here. -/

/-- The verify orchestration `LowCT` body, sequencing the leaf `RCall`s of the
    AUCurves rustcmd `ed25519_verify`. `sig` is the 64-byte signature `R ‖ S`,
    `pub` the 32-byte public key, `msg` the message with `chal` the challenge
    scratch buffer; `result` is the 1-byte accept/reject flag. -/
def ed25519VerifyBody : LowCT :=
  let sig      := loc "sig"      (.TBytes 64)
  let pub      := loc "pub"      (.TBytes 32)
  let msg      := loc "msg"      (.TBytes 4096)
  let result   := loc "result"   (.TBytes 1)
  let rXyzt    := loc "R_xyzt"   ed25519XyztTowerType
  let aXyzt    := loc "A_xyzt"   ed25519XyztTowerType
  let rBytes   := loc "R_bytes"  (.TBytes 32)
  let sBytes   := loc "S_bytes"  (.TBytes 32)
  let chal     := loc "chal"     (.TBytes 4160)
  let hFull    := loc "h_full"   (.TBytes 64)
  let hRed     := loc "h_red"    (.TBytes 32)
  let sB       := loc "sB"       ed25519XyztTowerType
  let hA       := loc "hA"       ed25519XyztTowerType
  let rCheckA  := loc "RcheckA"  ed25519XyztTowerType
  let checkB   := loc "check"    (.TBytes 32)
  let checkSB  := loc "check_sB" (.TBytes 32)
  .RSeq (.RCall "scalar_lt_L" result [sig])
  (.RSeq (.RCall "ed25519_decompress" rXyzt [sig])
  (.RSeq (.RCall "ed25519_decompress" aXyzt [pub])
  (.RSeq (.RCall "memmove_R_from_sig" rBytes [sig])
  (.RSeq (.RCall "memmove_chal_R" chal [rBytes])
  (.RSeq (.RCall "memmove_chal_A" chal [pub])
  (.RSeq (.RCall "memmove_chal_M" chal [msg])
  (.RSeq (.RCall "sha512_64" hFull [chal])
  (.RSeq (.RCall "scalar_reduce" hRed [hFull])
  (.RSeq (.RCall "memmove_S_from_sig" sBytes [sig])
  (.RSeq (.RCall "ed25519_scalarmult_base" sB [sBytes])
  (.RSeq (.RCall "ed25519_scalarmult" hA [hRed, aXyzt])
  (.RSeq (.RCall "ed25519_xyzt_add" rCheckA [rXyzt, hA])
  (.RSeq (.RCall "ed25519_compress" checkB [rCheckA])
  (.RSeq (.RCall "ed25519_compress" checkSB [sB])
         (.RCall "bytes_equal_32" result [checkSB, checkB])))))))))))))))

/-- `ReifiedFunc` bundle for the Ed25519 verify orchestration. -/
def ed25519VerifyReified : ReifiedFunc :=
  { args    := [("sig", .TBytes 64), ("pub", .TBytes 32), ("msg", .TBytes 4096)]
    body    := ed25519VerifyBody
    retName := "result" }

/-! ## §10. Inspection -/

#eval ed25519DecompressReified.args.map Prod.fst   -- [pt]
#eval ed25519DecompressReified.args.length         -- 1
#eval ed25519DecompressReified.retName             -- __result
#eval ed25519VerifyReified.args.map Prod.fst       -- [sig, pub, msg]

#print axioms ed25519DecompressDenote_length
#print axioms ed25519D_pin
#print axioms ed25519Sqrtm1_sq

end CatCrypt.Crypto.Vale.Ed25519Decompress
