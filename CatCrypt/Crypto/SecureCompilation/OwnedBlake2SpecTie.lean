/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.OwnedBlake2AbstractCom

/-!
# Tying the unified-`Com` BLAKE2b `G` kernel to the abstract BLAKE2b `G` spec

The model-free source for the owned BLAKE2b `G` mixing block is the unified
`Com jasminDialect` `zmmPackQ` kernel in
`VIR.OwnedBlake2AbstractCom`: its four single-output packed specs
`gSpec{A,B,C,D}` (over the carry-free `vpackZMM` alphabet, denoted by the
verified-dialect 8×u64 lane semantics `zmmPackQ`/`zmmLane`), with the headline
per-lane tie `blake2GCom_lane_abstract` to the abstract RFC-7693 §3.1
`ThirToComFront.blake2bGSpec`.

This module re-anchors the BLAKE2b `G` abstract-spec tie onto that model-free
`Com` source. The conclusion is the **same** RFC-7693 §3.1 tie — only the source
side is the unified `Com jasminDialect` denotation rather than a bespoke
`Avx512Model` `runZBlock` machine. There is no `runZBlock` / `ZInstr` /
`Avx512Model` / `jasminc` / `jasminc_preserves_ct` in any theorem's axioms.

## What is tied (re-exported here)

* **rotate tie** (`rotrSpec_lane_eq_rotateRight`): the `vpsrlvq | vpsllvq | vporq`
  shift decomposition `(v ≫ k) ||| (v ≪ (64 − k))` (`0 < k < 64`) over a
  `BitVec 64` lane equals the genuine `BitVec.rotateRight v k`. Bit-exact at 64
  bits. (= `OwnedBlake2AbstractCom.rotateRight_shiftor`.)
* **`G` tie** (`owned_blake2GSpec_eq_abstract_G`, the headline): at the BLAKE2b
  rotation constants `32/24/16/63`, every qword lane `k` of the four unified
  `Com jasminDialect` `G` output specs `gSpec{A,B,C,D}` equals the four
  components `(a', b', c', d')` of the abstract `blake2bGSpec` on lane `k` of the
  six input registers. (= `OwnedBlake2AbstractCom.blake2GCom_lane_abstract`.)

## Why BLAKE2b ties cleanly: bit-exact at 64 bits

BLAKE2b's words are 64-bit, which is exactly the width of one ZMM lane
(`BitVec 64`). The `zmmPackQ .add` is `BitVec 64` wrapping add per lane =
BLAKE2b's mod-`2^64` word add *exactly* (no truncation gap), and the
shift-decomposition rotate is the genuine 64-bit `BitVec.rotateRight` (no
complement mask) — both because the lane *is* `BitVec 64`. So every lane of the
packed `G` spec equals the abstract `blake2bGSpec` applied to that lane's words,
with no approximation. The only trust is that `ThirToComFront.blake2bGSpec`
faithfully encodes RFC 7693 §3.1 (it does — `+`, `^^^`, `.rotateRight` at
`32/24/16/63`). No KAT, no jasminc.

## References
* RFC 7693 — The BLAKE2 Cryptographic Hash and MAC (§3.1, the `G` mixing function).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.OwnedBlake2SpecTie

open CatCrypt.Crypto.SecureCompilation.VIR.OwnedBlake2AbstractCom
  (rotateRight_shiftor blake2GCom_lane_abstract gSpecA gSpecB gSpecC gSpecD)
open CatCrypt.Crypto.SecureCompilation.VIR.OwnedShaRoundAbstractCom (constZmm)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (zmmLane)
open CatCrypt.Crypto.SecureCompilation.ThirToComFront (blake2bGSpec)

/-! ## §1  The bit-exact 64-bit rotate-right tie

The `vpsrlvq | vpsllvq | vporq` shift decomposition `(v ≫ k) ||| (v ≪ (64 − k))`
over a `BitVec 64` lane is the genuine `(v).rotateRight k` — bit-exact because the
lane *is* `BitVec 64`. Re-exported from the unified-`Com` twin. -/

/-- **Rotate tie (bit-exact, per-lane).**  For `0 < k < 64`, the
    `vpsrlvq | vpsllvq | vporq` shift decomposition `(v ≫ k) ||| (v ≪ (64 − k))`
    over a `BitVec 64` lane equals the abstract `v.rotateRight k`.  Because the
    ZMM lane is `BitVec 64` and BLAKE2b's rotate is a 64-bit rotate, this is
    exact — no truncation, no mask.  (= the unified-`Com` twin's
    `OwnedBlake2AbstractCom.rotateRight_shiftor`.) -/
theorem rotrSpec_lane_eq_rotateRight (v : BitVec 64) (k : Nat)
    (_hk0 : 0 < k) (hk : k < 64) :
    (v >>> k) ||| (v <<< (64 - k)) = v.rotateRight k :=
  rotateRight_shiftor v k hk

/-! ## §2  The headline: owned `G` spec = abstract `G`, bit-exact at 64 bits

The four packed `Com jasminDialect` `G` output specs `gSpec{A,B,C,D}`, run with
the BLAKE2b rotation constants `32/24/16/63` as broadcast amount operands,
compute — in **every** qword lane `k` — exactly the four components of the
abstract `blake2bGSpec` on lane `k`. Re-exported from the unified-`Com` twin. -/

/-- **Headline — owned BLAKE2b `G` spec = abstract `G`, bit-exact (per-lane).**
    With the BLAKE2b rotation constants `32/24/16/63` as broadcast amount
    operands, every qword lane `k` of the four unified `Com jasminDialect` `G`
    output specs `gSpec{A,B,C,D}` equals the four components `(a', b', c', d')`
    of the abstract `ThirToComFront.blake2bGSpec` (RFC 7693 §3.1) on lane `k` of
    the six input registers.

    This is **bit-exact at 64 bits** — the `zmmPackQ .add` is `BitVec 64` add =
    BLAKE2b's mod-`2^64` word add *exactly*, and the shift-decomposition rotate
    is `BitVec.rotateRight` *exactly* (§1), because the ZMM lane width equals the
    BLAKE2b word width. No truncation gap, no complement mask, no `Avx512Model` /
    `runZBlock` / `jasminc` in any axiom.  (= the unified-`Com` twin's
    `OwnedBlake2AbstractCom.blake2GCom_lane_abstract`.) -/
theorem owned_blake2GSpec_eq_abstract_G
    (a b c d x y : BitVec 512) (k : Fin 8) :
    zmmLane (gSpecA a b c d x y (constZmm 32) (constZmm 32) (constZmm 24)
        (constZmm 40) (constZmm 16) (constZmm 48) (constZmm 63) (constZmm 1)) k
      = (blake2bGSpec (zmmLane a k) (zmmLane b k) (zmmLane c k) (zmmLane d k)
          (zmmLane x k) (zmmLane y k)).1
    ∧ zmmLane (gSpecB a b c d x y (constZmm 32) (constZmm 32) (constZmm 24)
        (constZmm 40) (constZmm 16) (constZmm 48) (constZmm 63) (constZmm 1)) k
      = (blake2bGSpec (zmmLane a k) (zmmLane b k) (zmmLane c k) (zmmLane d k)
          (zmmLane x k) (zmmLane y k)).2.1
    ∧ zmmLane (gSpecC a b c d x y (constZmm 32) (constZmm 32) (constZmm 24)
        (constZmm 40) (constZmm 16) (constZmm 48) (constZmm 63) (constZmm 1)) k
      = (blake2bGSpec (zmmLane a k) (zmmLane b k) (zmmLane c k) (zmmLane d k)
          (zmmLane x k) (zmmLane y k)).2.2.1
    ∧ zmmLane (gSpecD a b c d x y (constZmm 32) (constZmm 32) (constZmm 24)
        (constZmm 40) (constZmm 16) (constZmm 48) (constZmm 63) (constZmm 1)) k
      = (blake2bGSpec (zmmLane a k) (zmmLane b k) (zmmLane c k) (zmmLane d k)
          (zmmLane x k) (zmmLane y k)).2.2.2 :=
  blake2GCom_lane_abstract a b c d x y k

end CatCrypt.Crypto.SecureCompilation.OwnedBlake2SpecTie
