/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
public import CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane

/-!
# The P3×P4 bridge, mechanized: `lo32` transport via `BinOpHomOn2`

The model-free dword-lane module (`VIR/Sha256DwordLane.lean`) provides the
width-32 SHA-256 round bodies and their bit-exact ties; this file documents that
the dword projection
`lo32 : BitVec 64 → BitVec 32` (`setWidth 32`, the 32↔64 lane view) is a Trocq /
`ReprTransfer` decode `map₁`, and that along it the **homomorphic** lane ops
(`&&&`, `|||`, `^^^`, and the low bits of `+`) transport from the 64-bit-lane
proofs while the **rotate** does NOT (it must be supplied natively at width 32).

This file *builds* that transport, instead of merely asserting it.  Using the
joint-domain homomorphism `BinOpHomOn2` from `ReprTransferBinaryDom.lean` (the P3
side), we exhibit, for each homomorphic op, a `BinOpHomOn2 lo32 (fun _ _ => True)`
square whose realization is exactly `lo32 (a ⊙₆₄ b) = lo32 a ⊙₃₂ lo32 b`.  The
crucial point — and the reason the domain is the *full* `True` (no truncation
precondition) — is `BitVec.setWidth_add`: the low 32 bits of a 64-bit add ARE the
32-bit add, **unconditionally**.  So even `+` transports with no domain
restriction.

The **negative** half is the whole point of the boundary: we exhibit a concrete
counterexample showing `lo32 (rotateRight₆₄ a k) ≠ rotateRight₃₂ (lo32 a) k`, so
there is no `BinOpHomOn2`/unary-hom for the rotate along `lo32`.  That is exactly
why the model-free `Sha256DwordLane.rorD_eq_rotateRight` supplies the rotate
natively at width 32.

Finally we connect to SHA-256: the dword `Ch`/`Maj` (`Sha256DwordLane.chD`/`majD`)
are recovered from the 64-bit-lane bitwise structure by pushing `lo32` through the
`andHomLo`/`xorHomLo`/`notHomLo` transports — the bitwise round functions
transport.  The rotate-containing `Σ₀`/`Σ₁` stay native (cite
`Sha256DwordLane.bigSigma0_dword_bitExact`).  Bitwise/add transport, rotate native:
that is the P3×P4 boundary made concrete.

## Scope

`lo32` is `BitVec.setWidth 32` — the Trocq map₁ / univalence-free transport
witness.  Map-level: no injectivity, **no univalence**, no `jasminc_preserves_ct`.
The transport squares are the `setWidth_{and,or,xor,add}` `BitVec` homomorphisms;
the rotate non-transport is a single `native_decide` counterexample.  The trust is
the `BitVec` lane-arithmetic TCB the model-free dword-lane ties already carry.

## References
* FIPS 180-4 — Secure Hash Standard (§4.1.2 `Ch`/`Maj`/`Σ₀`/`Σ₁`).
* Intel SDM — `VPANDD`/`VPORD`/`VPXORD`/`VPADDD`/`VPRORD` (`AVX512F`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TransferDwordTransport

open CatCrypt.Crypto.Bridges.ReprTransferBinaryDom
open CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane
  (chD majD sigma0D)

/-! ## §1  The decode map `lo32 : BitVec 64 → BitVec 32` -/

/-- The dword projection `lo32 : BitVec 64 → BitVec 32`, `setWidth 32` — the
    32↔64 lane view of the model-free dword-lane bodies.  This is the Trocq /
    `ReprTransfer` decode `map₁`: it takes a 64-bit lane to the low 32 bits the
    dword bodies operate on.  Univalence-free (no inverse, no injectivity asserted). -/
def lo32 (a : BitVec 64) : BitVec 32 := BitVec.setWidth 32 a

/-! ## §2  The homomorphic ops transport: `BinOpHomOn2 lo32 (fun _ _ => True)`

For `&&&`, `|||`, `^^^`, the truncation `setWidth 32` is a bitwise homomorphism
(`BitVec.setWidth_and/or/xor`) with no hypothesis.  For `+`, `BitVec.setWidth_add`
gives `(a + b).setWidth 32 = a.setWidth 32 + b.setWidth 32` UNCONDITIONALLY — the
low 32 bits of the 64-bit add ARE the 32-bit add — so the add ALSO transports on
the full `True` domain, with no no-wrap precondition.  Each homomorphism is read
off `.realizes`. -/

/-- **`&&&` transports.**  `BinOpHomOn2 lo32 True (&&&) (&&&)`: decoding the 64-bit
    and through `lo32` is the 32-bit and of the decodes — `lo32 (a &&& b) =
    lo32 a &&& lo32 b`.  Hypothesis-free (`setWidth_and`). -/
def andHomLo : BinOpHomOn2 lo32 (fun _ _ => True)
    (fun a b => a &&& b) (fun a b => a &&& b) where
  app_eq a b _ := by simp only [lo32, BitVec.setWidth_and]

/-- **`|||` transports.**  `lo32 (a ||| b) = lo32 a ||| lo32 b`, hypothesis-free
    (`setWidth_or`). -/
def orHomLo : BinOpHomOn2 lo32 (fun _ _ => True)
    (fun a b => a ||| b) (fun a b => a ||| b) where
  app_eq a b _ := by simp only [lo32, BitVec.setWidth_or]

/-- **`^^^` transports.**  `lo32 (a ^^^ b) = lo32 a ^^^ lo32 b`, hypothesis-free
    (`setWidth_xor`). -/
def xorHomLo : BinOpHomOn2 lo32 (fun _ _ => True)
    (fun a b => a ^^^ b) (fun a b => a ^^^ b) where
  app_eq a b _ := by simp only [lo32, BitVec.setWidth_xor]

/-- **`+` transports, on the FULL domain.**  `lo32 (a + b) = lo32 a + lo32 b` with
    NO no-wrap precondition.  This is the key fact distinguishing the add from a
    field-`+`: `BitVec.setWidth_add` says the low 32 bits of the 64-bit add ARE the
    32-bit add (the truncation is exact for `+`), so the add transports on the same
    unrestricted `True` domain as the bitwise ops — no per-operand `< 2^31` bound
    is needed. -/
def addHomLo : BinOpHomOn2 lo32 (fun _ _ => True)
    (fun a b => a + b) (fun a b => a + b) where
  app_eq a b _ := by simp only [lo32]; exact BitVec.setWidth_add a b (by omega)

/-! The realization equations, read off `.realizes` of each transport. -/

/-- Realization of `andHomLo`: `lo32 (a &&& b) = lo32 a &&& lo32 b`. -/
theorem andHomLo_realizes (a b : BitVec 64) :
    lo32 (a &&& b) = lo32 a &&& lo32 b := andHomLo.realizes (a := a) (b := b) trivial

/-- Realization of `orHomLo`: `lo32 (a ||| b) = lo32 a ||| lo32 b`. -/
theorem orHomLo_realizes (a b : BitVec 64) :
    lo32 (a ||| b) = lo32 a ||| lo32 b := orHomLo.realizes (a := a) (b := b) trivial

/-- Realization of `xorHomLo`: `lo32 (a ^^^ b) = lo32 a ^^^ lo32 b`. -/
theorem xorHomLo_realizes (a b : BitVec 64) :
    lo32 (a ^^^ b) = lo32 a ^^^ lo32 b := xorHomLo.realizes (a := a) (b := b) trivial

/-- Realization of `addHomLo`: `lo32 (a + b) = lo32 a + lo32 b`, unconditionally. -/
theorem addHomLo_realizes (a b : BitVec 64) :
    lo32 (a + b) = lo32 a + lo32 b := addHomLo.realizes (a := a) (b := b) trivial

/-- **`~~~` transports** (unary, for `Ch`'s `~e`).  `lo32 (~~~a) = ~~~ lo32 a`,
    hypothesis-free (`setWidth_not`).  Stated as a plain unary homomorphism. -/
theorem notHomLo_realizes (a : BitVec 64) : lo32 (~~~ a) = ~~~ (lo32 a) := by
  simp only [lo32]
  ext i
  simp [BitVec.getElem_setWidth, BitVec.getElem_not]

/-! ## §3  The NEGATIVE: the rotate does NOT transport along `lo32`

The whole point of the boundary.  We exhibit a concrete `(a, k)` with
`lo32 (a.rotateRight k) ≠ (lo32 a).rotateRight k`, so there is no
`BinOpHomOn2`/unary-hom square for the rotate along `lo32` — the rotate must be
proved natively at width 32 (which is what `Sha256DwordLane.rorD_eq_rotateRight`
does).  Lift of the dword-lane divergence pin (`rorD 1 1` wraps to bit
31, not bit 63). -/

/-- **Rotate non-transport counterexample.**  At `a = 1`, `k = 1`: the 64-bit
    right-rotate sends the low bit to bit 63 (above the low 32 bits), so
    `lo32 (rotateRight₆₄ 1 1) = 0`; whereas the 32-bit rotate of `lo32 1 = 1`
    sends the low bit to bit 31, so `(rotateRight₃₂ (lo32 1)) 1 = 0x80000000`.
    These differ — the rotate does NOT commute with `lo32`. -/
theorem rotate_not_transport :
    lo32 ((1 : BitVec 64).rotateRight 1) ≠ ((lo32 (1 : BitVec 64)).rotateRight 1) := by
  native_decide

/-- **No unary-hom for the rotate.**  Concretely: there is no function `r : BitVec
    64 → BitVec 32 → BitVec 32` agreeing with both sides; the canonical candidate
    (the abstract `rotateRight` pushed through `lo32`) already fails at `(1,1)`.
    Packaged as the explicit "the rotate square cannot close" witness — the
    negative `BinOpHomOn2`-style statement: there is no homomorphism square
    `lo32 (rotateRight₆₄ a k) = rotateRight₃₂ (lo32 a) k` valid for all `a`. -/
theorem no_rotate_hom :
    ¬ (∀ (a : BitVec 64) (k : Nat),
        lo32 (a.rotateRight k) = (lo32 a).rotateRight k) := by
  intro h
  exact rotate_not_transport (h (1 : BitVec 64) 1)

/-! ## §4  Connect to SHA-256: `Ch`/`Maj` transport, `Σ` stays native

The dword `Ch`/`Maj` bodies (`Sha256DwordLane.chD`/`majD`, pure `&&&`/`^^^`/`~~~`) are
recovered from the 64-bit lane bitwise structure by pushing `lo32` through the
`andHomLo`/`xorHomLo`/`notHomLo` transports.  Concretely: if `x,y,z : BitVec 64`
are 64-bit lanes, the dword `Ch` of their decodes equals the decode of the 64-bit
`Ch` body — the composition of §2's transports.  The `Σ` round functions contain a
rotate and therefore do NOT transport; they are supplied natively at width 32 by
`Sha256DwordLane.bigSigma0_dword_bitExact` / `bigSigma1_dword_bitExact`. -/

/-- The 64-bit-lane `Ch` body (`(x &&& y) ^^^ (~~~x &&& z)` at `BitVec 64`). -/
def chQ (x y z : BitVec 64) : BitVec 64 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- The 64-bit-lane `Maj` body at `BitVec 64`. -/
def majQ (x y z : BitVec 64) : BitVec 64 := ((x &&& y) ^^^ (x &&& z)) ^^^ (y &&& z)

/-- **`Ch` transports through `lo32`.**  The dword `Ch` body of the decoded lanes
    equals the decode of the 64-bit `Ch` body: `chD (lo32 x) (lo32 y) (lo32 z) =
    lo32 (chQ x y z)`.  Proved purely by the §2 bitwise transports
    (`xorHomLo`/`andHomLo`/`notHomLo`) — no native 32-bit reasoning, the round
    function transports.  This is the homomorphic-op half of the P3×P4 boundary. -/
theorem chD_transports (x y z : BitVec 64) :
    chD (lo32 x) (lo32 y) (lo32 z) = lo32 (chQ x y z) := by
  simp only [chD, chQ,
    xorHomLo_realizes, andHomLo_realizes, notHomLo_realizes]

/-- **`Maj` transports through `lo32`.**  `majD (lo32 x) (lo32 y) (lo32 z) =
    lo32 (majQ x y z)`, again purely by the §2 bitwise transports — the `Maj` round
    function transports. -/
theorem majD_transports (x y z : BitVec 64) :
    majD (lo32 x) (lo32 y) (lo32 z) = lo32 (majQ x y z) := by
  simp only [majD, majQ,
    xorHomLo_realizes, andHomLo_realizes]

/-- **The boundary, stated.**  `Σ₀` contains a rotate, so its dword tie is NOT a
    transport of a 64-bit-lane `Σ₀`: it is the native width-32 result
    `Sha256DwordLane.bigSigma0_dword_bitExact`.  We re-export that native tie here as
    the rotate-side of the boundary, alongside the transported `Ch`/`Maj` — making
    explicit that `Σ` stays native exactly because of `no_rotate_hom`. -/
theorem sigma0_native (a : UInt32) :
    CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane.sigma0D a.toBitVec
      = (CatCrypt.Crypto.Primitives.SHA256.bigSigma0 a).toBitVec :=
  CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordLane.bigSigma0_dword_bitExact a

end CatCrypt.Crypto.SecureCompilation.TransferDwordTransport
