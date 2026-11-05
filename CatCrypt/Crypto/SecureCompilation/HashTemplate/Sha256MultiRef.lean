/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2
public import CatCrypt.Crypto.Primitives.HMACMulti
public import Transfer.Combinators.ParamArray

/-!
# Multi-block SHA-256 at the SHA-2 template's compression

`Primitives.SHA256.compress` acts on eight `UInt32` chaining words and a 64-byte block; the
template's compression `sha2CompressRef sha256P` acts on eight `BitVec 32` chaining words and
sixteen `BitVec 32` message words. The two agree up to `toBitVec` of the chaining words and the
big-endian parsing `sha256BlockWords` of the block into words.

`sha256MultiRef s block` is the template's compression on a 64-byte block. The Merkle–Damgård
iteration `mdIterate` of `HMACMulti` folds a compression over the padded blocks; the fold of
`compressVec` from the SHA-256 initial value and the fold of `sha256MultiRef` from `sha256P.H0`
are related by `toBitVec` of the eight words at every step, by the relational fold rule
`Transfer.Param.foldlR_list`.

## Main results

* `sha256_compress_toBitVec`: `SHA256.compress` is `sha2CompressRef sha256P` on the words.
* `mdIterate_compressVec_toBitVec`: the iterated `compressVec` is the iterated template
  compression on the words.
* `sha256Multi_eq_ref`: `sha256Multi` is the serialization of the iterated template
  compression.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.Primitives.HMACMulti

/-- `Primitives.SHA256.compress` is the template's compression `sha2CompressRef sha256P` on the
    words of the state and the big-endian words of the block. -/
theorem sha256_compress_toBitVec (H : Fin 8 → UInt32) (block : Fin 64 → UInt8) :
    (fun i => (Primitives.SHA256.compress H block i).toBitVec) =
      sha256P.sha2CompressRef (fun i => (H i).toBitVec) (sha256BlockWords block) :=
  (sha2CompressBody_sha256 H block).symm.trans (sha2CompressBody_value sha256P _ _)

/-- The template's compression at SHA-256 on a 64-byte block. -/
def sha256MultiRef (s : Fin 8 → BitVec 32) (block : Fin 64 → UInt8) : Fin 8 → BitVec 32 :=
  sha256P.sha2CompressRef s (sha256BlockWords block)

/-- The Merkle–Damgård iteration of `compressVec` from the SHA-256 initial value is, word by word
    under `toBitVec`, the iteration of the template's compression from `sha256P.H0`. -/
theorem mdIterate_compressVec_toBitVec (msg : List UInt8) :
    (fun i : Fin 8 =>
        (mdIterate compressVec (Vector.ofFn Primitives.SHA256.hInit) msg)[i].toBitVec) =
      mdIterate sha256MultiRef sha256P.H0 msg := by
  unfold mdIterate
  refine Transfer.Param.foldlR_list (fun b b' => b = b')
    (fun (v : Vector UInt32 8) s => (fun i : Fin 8 => v[i].toBitVec) = s)
    compressVec sha256MultiRef ?_ ?_ (List.forall₂_same.2 fun _ _ => rfl)
  · rintro v s b b' hs rfl
    subst hs
    rw [sha256MultiRef, ← sha256_compress_toBitVec]
    funext i
    simp [compressVec]
  · funext i
    simp [Primitives.SHA256.hInit, sha256P]

/-- SHA-256 of a message of any length is the serialization of the Merkle–Damgård iteration of
    the template's compression at SHA-256 from `sha256P.H0`. -/
theorem sha256Multi_eq_ref (msg : List UInt8) :
    sha256Multi msg = List.ofFn (Primitives.SHA256.serializeState fun i =>
      UInt32.ofBitVec (mdIterate sha256MultiRef sha256P.H0 msg i)) := by
  rw [← mdIterate_compressVec_toBitVec]
  rfl

end CatCrypt.Crypto.SecureCompilation.HashTemplate
