/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit
public meta import CatCrypt.Crypto.Jasmin.ChaCha20Block
public import CatCrypt.Crypto.Jasmin.ChaCha20Block

/-!
# The whole ChaCha20 block routed through `catCryptDialect`

[`Chacha20QRCatCryptEmit.lean`](Chacha20QRCatCryptEmit.lean) builds the RFC-8439
§2.1 ChaCha20 *quarter-round* natively as a straight-line `Com catCryptDialect`
program (`chacha20QRCatCrypt{A,B,C,D}` / `qrBlock`) and proves it denotes to the
canonical RFC quarter-round (`chacha20QR_catcrypt_denote{A,B,C,D}`). But the
quarter-round is a *sub*-kernel; the **benchmarked** primitive
(`bench/chacha_compare`) is the whole 20-round ChaCha20 block.

This file closes that gap: it composes the committed catCrypt-dialect quarter-round
`Com` into the **whole block** and proves the composite equals the canonical
RFC-8439 §2.3 block spec `ChaCha20Block.chachaBlock` (the 16-word state threaded
through 10 column+diagonal double-rounds, then the feed-forward add). So the whole
benchmarked primitive — not just a sub-kernel — now routes through the high
`catCryptDialect` surface.

## Structural composition (NOT a monolithic 16-word `Com`)

A single straight-line 16-word `Com catCryptDialect` for the whole block is
~5440 de-Bruijn-threaded ops (80 quarter-rounds × 68 bindings), which is neither
hand-authorable nor `rfl`/`native_decide`-closable at MCP heartbeats. Instead the
block is composed **structurally**, mirroring how
[`Chacha20DwordBlockCom.lean`](Chacha20DwordBlockCom.lean) assembles the
packed quarter-round into the whole block:

1. **`qrCatCrypt`** (`§1`) — the four quarter-round outputs *computed by the
   committed catCrypt-dialect `Com` programs* `chacha20QRCatCrypt{A,B,C,D}`
   (each via `.denote (inV a b c d)`). The single point where the high dialect
   does the arithmetic. `qrCatCrypt_eq` collapses it to the RFC `quarterRound`
   by the four committed denote lemmas.

2. **`quarterRoundAtCatCrypt`** (`§2`) — `ChaCha20Block.quarterRoundAt` but
   driven by `qrCatCrypt`; `quarterRoundAtCatCrypt_eq` rewrites it to the RFC
   `quarterRoundAt` via `qrCatCrypt_eq`.

3. **`columnRoundCatCrypt` / `diagonalRoundCatCrypt` / `doubleRoundCatCrypt` /
   `chachaCoreCatCrypt` / `chacha20BlockCatCrypt`** (`§3`) — the RFC-8439 §2.3
   round structure (the SAME column/diagonal index sets as `ChaCha20Block`),
   each step the catCrypt-dialect quarter-round. Ten double-rounds, then the
   feed-forward `ChaChaState.add`.

4. **`chacha20Block_catcrypt_denote`** (`§4`) — the core result: the whole catCrypt
   block equals the canonical RFC-8439 §2.3 block `ChaCha20Block.chachaBlock`,
   proved by folding the per-quarter-round denote equality through the round
   structure (`Function.iterate_congr` for the 10 double-rounds), NOT one
   monolithic `rfl`. Every quarter-round in the whole block is evaluated by the
   committed `Com catCryptDialect` program.

0 sorries.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.Jasmin.ChaCha20QR (quarterRound)

/-! ## 1. The quarter-round computed by the committed catCrypt-dialect `Com`

`qrCatCrypt a b c d` runs the four committed `Com catCryptDialect` quarter-round
programs `chacha20QRCatCrypt{A,B,C,D}` on the input valuation `inV a b c d` and
collects their denotations. `qrCatCrypt_eq` collapses the tuple to the RFC-8439
`quarterRound` by the four committed denote lemmas — this is the only place the
high dialect performs the ARX arithmetic; everything below is plumbing. -/

/-- The four quarter-round outputs, each computed by the committed catCrypt-dialect
    quarter-round `Com` (`chacha20QRCatCrypt{A,B,C,D}.denote`). -/
def qrCatCrypt (a b c d : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  ( chacha20QRCatCryptA.denote (inV a b c d),
    chacha20QRCatCryptB.denote (inV a b c d),
    chacha20QRCatCryptC.denote (inV a b c d),
    chacha20QRCatCryptD.denote (inV a b c d) )

/-- **The catCrypt quarter-round computes the RFC-8439 `quarterRound`.** Folds the
    four committed denote lemmas `chacha20QR_catcrypt_denote{A,B,C,D}`. -/
theorem qrCatCrypt_eq (a b c d : BitVec 32) :
    qrCatCrypt a b c d = quarterRound a b c d := by
  simp only [qrCatCrypt, chacha20QR_catcrypt_denoteA, chacha20QR_catcrypt_denoteB,
    chacha20QR_catcrypt_denoteC, chacha20QR_catcrypt_denoteD]

/-! ## 2. The quarter-round on the 16-word state, driven by the catCrypt `Com`

`quarterRoundAtCatCrypt` is `ChaCha20Block.quarterRoundAt` with `quarterRound`
replaced by `qrCatCrypt`: it writes the four catCrypt-`Com` outputs back into the
four state positions `(a, b, c, d)` and leaves the other twelve fixed. -/

/-- Apply the catCrypt-dialect quarter-round to four state positions. Mirrors
    `ChaCha20Block.quarterRoundAt`, but the arithmetic is the committed
    `Com catCryptDialect` program (via `qrCatCrypt`). -/
def quarterRoundAtCatCrypt (s : ChaChaState) (a b c d : Fin 16) : ChaChaState :=
  let (ra, rb, rc, rd) := qrCatCrypt (s a) (s b) (s c) (s d)
  s |>.update a ra |>.update b rb |>.update c rc |>.update d rd

/-- **The catCrypt state quarter-round equals the RFC `quarterRoundAt`.** -/
theorem quarterRoundAtCatCrypt_eq (s : ChaChaState) (a b c d : Fin 16) :
    quarterRoundAtCatCrypt s a b c d = quarterRoundAt s a b c d := by
  simp only [quarterRoundAtCatCrypt, quarterRoundAt, qrCatCrypt_eq]

/-! ## 3. The whole-block round structure over the catCrypt quarter-round

The RFC-8439 §2.3 column round, diagonal round, double-round, ten-double-round
core, and feed-forward — each quarter-round the committed catCrypt-dialect `Com`.
The column/diagonal index sets are identical to `ChaCha20Block.columnRound` /
`diagonalRound`. -/

/-- Column round over the catCrypt quarter-round: `QR(0,4,8,12)`, `QR(1,5,9,13)`,
    `QR(2,6,10,14)`, `QR(3,7,11,15)`. -/
def columnRoundCatCrypt (s : ChaChaState) : ChaChaState :=
  s |> (quarterRoundAtCatCrypt ·  0  4  8 12)
    |> (quarterRoundAtCatCrypt ·  1  5  9 13)
    |> (quarterRoundAtCatCrypt ·  2  6 10 14)
    |> (quarterRoundAtCatCrypt ·  3  7 11 15)

/-- Diagonal round over the catCrypt quarter-round: `QR(0,5,10,15)`,
    `QR(1,6,11,12)`, `QR(2,7,8,13)`, `QR(3,4,9,14)`. -/
def diagonalRoundCatCrypt (s : ChaChaState) : ChaChaState :=
  s |> (quarterRoundAtCatCrypt ·  0  5 10 15)
    |> (quarterRoundAtCatCrypt ·  1  6 11 12)
    |> (quarterRoundAtCatCrypt ·  2  7  8 13)
    |> (quarterRoundAtCatCrypt ·  3  4  9 14)

/-- One double-round over the catCrypt quarter-round (diagonal after column). -/
def doubleRoundCatCrypt (s : ChaChaState) : ChaChaState :=
  diagonalRoundCatCrypt (columnRoundCatCrypt s)

/-- Ten catCrypt double-rounds (the ChaCha20 round schedule). -/
def chachaCoreCatCrypt (s : ChaChaState) : ChaChaState :=
  (doubleRoundCatCrypt)^[10] s

/-- The whole ChaCha20 block over the catCrypt quarter-round: ten double-rounds,
    then the feed-forward add with the initial state (RFC-8439 §2.3). -/
def chacha20BlockCatCrypt (s : ChaChaState) : ChaChaState :=
  ChaChaState.add (chachaCoreCatCrypt s) s

/-! ## 4. The whole catCrypt block equals the RFC-8439 §2.3 block

The core result. Each level of the round structure equals its `ChaCha20Block`
counterpart by the level below; the ten double-rounds are folded with
`Function.iterate_congr` (NOT a monolithic `rfl` over 80 quarter-rounds), so the
whole catCrypt block equals the canonical RFC block `ChaCha20Block.chachaBlock`. -/

/-- The catCrypt column round equals the RFC column round. -/
theorem columnRoundCatCrypt_eq (s : ChaChaState) :
    columnRoundCatCrypt s = columnRound s := by
  simp only [columnRoundCatCrypt, columnRound, quarterRoundAtCatCrypt_eq]

/-- The catCrypt diagonal round equals the RFC diagonal round. -/
theorem diagonalRoundCatCrypt_eq (s : ChaChaState) :
    diagonalRoundCatCrypt s = diagonalRound s := by
  simp only [diagonalRoundCatCrypt, diagonalRound, quarterRoundAtCatCrypt_eq]

/-- The catCrypt double-round equals the RFC double-round. -/
theorem doubleRoundCatCrypt_eq (s : ChaChaState) :
    doubleRoundCatCrypt s = doubleRound s := by
  simp only [doubleRoundCatCrypt, doubleRound, columnRoundCatCrypt_eq,
    diagonalRoundCatCrypt_eq]

/-- The catCrypt core (ten double-rounds) equals the RFC core, folded through the
    iterate with `funext`-driven function equality (the 80 quarter-rounds are NOT
    unfolded by `rfl`). -/
theorem chachaCoreCatCrypt_eq (s : ChaChaState) :
    chachaCoreCatCrypt s = chachaCore s := by
  have hfun : doubleRoundCatCrypt = doubleRound :=
    funext doubleRoundCatCrypt_eq
  simp only [chachaCoreCatCrypt, chachaCore, hfun]

/-- **Whole-block result.** The whole ChaCha20 block computed over the committed
    catCrypt-dialect quarter-round `Com` equals the canonical RFC-8439 §2.3 block
    `ChaCha20Block.chachaBlock`. Every quarter-round in the block is evaluated by
    the committed `Com catCryptDialect` program `chacha20QRCatCrypt{A,B,C,D}`, so
    the whole benchmarked ChaCha20 primitive routes through the high dialect. -/
theorem chacha20Block_catcrypt_denote (s : ChaChaState) :
    chacha20BlockCatCrypt s = chachaBlock s := by
  simp only [chacha20BlockCatCrypt, chachaBlock, chachaCoreCatCrypt_eq]

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockCatCryptEmit
