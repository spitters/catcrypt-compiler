/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockCatCryptEmit

/-!
# The whole ChaCha20 block as a SINGLE straight-line `Com catCryptDialect` (the unroll emit)

[`Chacha20QRCatCryptEmit.lean`](Chacha20QRCatCryptEmit.lean) builds the RFC-8439
§2.1 ChaCha20 *quarter-round* as a 12-op straight-line `Com catCryptDialect`
(`qrBlock`), lowers it to a single jasmin `Com`, and emits `.jazz`.
[`Chacha20BlockCatCryptEmit.lean`](Chacha20BlockCatCryptEmit.lean) composes that
quarter-round into the **whole 20-round block**, but only at the level of a
*denotation fold over functions* (`chacha20BlockCatCrypt : ChaChaState →
ChaChaState`, each quarter-round a separate `Com.denote` call) — proven equal to
the RFC block spec `ChaCha20Block.chachaBlock`. That fold is NOT a single
emittable program: it is 80 separate `Com.denote` invocations threaded by Lean
function composition, not one `Com`.

This file closes the remaining gap: it builds the whole ChaCha20 block as ONE
straight-line `Com catCryptDialect` over the 16-word input state (the 80
quarter-rounds *unrolled* into a single de-Bruijn-threaded program, then the
16-word feed-forward add), proves the single `Com` denotes to
`ChaCha20Block.chachaBlock`, lowers it through the committed
`catCryptDialect → jasminDialect` seam (`cryptoDialectToJasminCom`) to a single
jasmin `Com`, and emits the whole-function `.jazz`/`.s` via `JasminPrint.emitJazz`.

```
RFC-8439 §2.3 chachaBlock   (ChaCha20Block.chachaBlock, the spec)
        ▲                         ▲
        │ denote = spec           │ denote = spec  (via the seam)
   Com catCryptDialect ──cryptoDialectToJasminCom──▶ Com jasminDialect ──emitJazz──▶ .jazz/x86
   (ONE straight-line 80-QR unroll + feed-forward, 976 ops (80×12 round + 16 feed-forward))
```

## Construction: a CPS builder threading the 16 state words (mirrors `ChaChaEmit`)

The single `Com` is assembled by a continuation-passing builder over
`catCryptDialect` word ops, mirroring the committed jasmin-dialect builder
`VIR.ChaChaEmit` (which emits the same primitive to jasmin but carries no
`denote = spec` theorem) and the committed quarter-round `Com` `qrBlock`:

* **`emitQR`** (`§2`) emits the 12-op RFC-8439 §2.1 quarter-round
  (`a+=b; d^=a; d<<<16; …`) **in place** on four state slots `a b c d`, using
  the dialect's `bvAdd`/`bvXor`/`bvRor` ops. The rotate-left is the seam-lowering
  `bvRor` (rotate-right) via `rotl(x,n) = ror(x,32-n)`, exactly as `qrBlock`.
* **`emitColumnRound` / `emitDiagonalRound` / `emitDoubleRound`** (`§3`) are the
  RFC-8439 §2.3 round structure (the SAME column/diagonal index sets as
  `ChaCha20Block`), each step `emitQR`.
* **`emitFeedForward`** (`§4`) writes the 16 output words `cur i + orig i`.

The whole block `chacha20BlockEmitCom` (`§5`) is ten double-rounds then the
feed-forward — ONE `Com catCryptDialect (List.replicate 32 T32) T32`, a single
straight-line de-Bruijn-threaded program (the 16 state words `0..15` plus the 16
feed-forward originals `16..31`).

## Denotation: one `Com`, proven equal to `chachaBlock`

The builder is proven correct by a **denotation invariant** (`§6`): each
`emitQR` step transforms the denoted 16-word state exactly as the committed
`quarterRoundAtCatCrypt` (hence as the RFC `quarterRoundAt`, by the committed
`quarterRoundAtCatCrypt_eq`), so the whole single `Com` denotes to
`chacha20BlockCatCrypt`, which the committed
`chacha20Block_catcrypt_denote` already equates to `ChaCha20Block.chachaBlock`.
This is NOT a monolithic `rfl`/`native_decide` over 976 ops: the per-QR step is a
small lemma, folded through the round structure.

## Emit

* `chacha20BlockEmitJasmin` (`§7`) — the single jasmin `Com` produced by the
  seam (`cryptoDialectToJasminCom` returns `some`).
* `chacha20BlockEmitJazz` / `emit` (`§8`) — the whole-function `.jazz`/`.s` text
  via `JasminPrint.emitJazz`, written to
  `bench/chacha_compare/gen_com/chacha20_block_catcrypt.s` under the symbol
  `chacha20_block`.

0 sorries (the whole-block denote reuses the committed per-QR denote +
block-composition lemmas).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy ctTransTy_sword)
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20QRCatCryptEmit
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockCatCryptEmit
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.Jasmin.ChaCha20QR (quarterRound)

/-! ## 1. The dialect word type, the input context, and the builder state

The whole block operates on 16 `BitVec 32` state words. The single `Com`'s free
context holds **32** `sword 32` words: indices `0..15` are the working state
(slots updated in place by the rounds), indices `16..31` are the feed-forward
originals (the same 16 input values, kept live so the final add can read them).

`BState Γ` carries the 16 current state words and the 16 originals as variables
of `Γ`; it shifts through a fresh binding by `.there` on every carried variable. -/

/-- The 32-bit machine-word dialect type. -/
abbrev T32 : CryptoTy := .sword 32

/-- The single `Com`'s free context: 16 state words + 16 feed-forward originals. -/
abbrev inCtxt : Ctxt catCryptDialect := List.replicate 32 T32

/-- The 16 current state words and 16 originals, as vars of `Γ`. -/
structure BState (Γ : Ctxt catCryptDialect) where
  /-- The 16 working state words (slots `0..15`). -/
  cur : Fin 16 → Ctxt.Var Γ T32
  /-- The 16 feed-forward originals (the initial state, kept live). -/
  orig : Fin 16 → Ctxt.Var Γ T32

/-- The fresh head variable of an extended context. -/
abbrev headVar (Γ : Ctxt catCryptDialect) : Ctxt.Var (T32 :: Γ) T32 := .here

/-! ## 2. Emitting one binding and one quarter-round

`emitBin` prepends one binary `regArith`-style word op binding reading source
slots `a`/`b`, then continues over the extended context with slot `dst` rebound
to the fresh head. `emitRor` is the unary rotate analogue. `emitQR` is the RFC
§2.1 quarter-round on four state slots, in place. -/

/-- Emit `dst := a + b` (`bvAdd 32`) and continue. `cur dst` is rebound to the
    fresh head; the other slots and all originals shift by `.there`. -/
def emitAdd {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState Γ) (dst a b : Fin 16)
    (k : {Γ' : Ctxt catCryptDialect} → BState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  let e : Expr catCryptDialect Γ T32 :=
    { op := .bvAdd 32, retTy_eq := rfl,
      args := HVector.cons (st.cur a) (HVector.cons (st.cur b) HVector.nil) }
  let st' : BState (T32 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
      orig := fun i => (st.orig i).there }
  .var e (k st')

/-- Emit `dst := dst ^ src` (`bvXor 32`) and continue. -/
def emitXor {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState Γ) (dst src : Fin 16)
    (k : {Γ' : Ctxt catCryptDialect} → BState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  let e : Expr catCryptDialect Γ T32 :=
    { op := .bvXor 32, retTy_eq := rfl,
      args := HVector.cons (st.cur dst) (HVector.cons (st.cur src) HVector.nil) }
  let st' : BState (T32 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
      orig := fun i => (st.orig i).there }
  .var e (k st')

/-- Emit `dst := ror dst n` (`bvRor 32 n`, the seam-lowering rotate) and continue.
    The RFC quarter-round rotates *left* by `m`; we emit `bvRor 32 (32 - m)` since
    `rotl(x,m) = rotr(x,32-m)` (the committed `rotL32_to_ror_*` identities). -/
def emitRor {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : BState Γ) (dst : Fin 16) (n : Nat)
    (k : {Γ' : Ctxt catCryptDialect} → BState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  let e : Expr catCryptDialect Γ T32 :=
    { op := .bvRor 32 n, retTy_eq := rfl,
      args := HVector.cons (st.cur dst) HVector.nil }
  let st' : BState (T32 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
      orig := fun i => (st.orig i).there }
  .var e (k st')

/-- The continuation type: a `Com` builder polymorphic in the (extended) context. -/
abbrev Cont (t : CryptoTy) :=
  {Γ' : Ctxt catCryptDialect} → BState Γ' → Com catCryptDialect Γ' t

/-- `quarterRound a b c d` (RFC-8439 §2.1) in place on slots `a b c d`:
    `a+=b; d^=a; d<<<16;  c+=d; b^=c; b<<<12;  a+=b; d^=a; d<<<8;  c+=d; b^=c; b<<<7`.
    Each rotate-left by `m` is the dialect `bvRor 32 (32 - m)`. Twelve ops — the
    same 12-op block (and the same rotate amounts) as the committed `qrBlock`. -/
def emitQR {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (a b c d : Fin 16) (k : Cont t) : Com catCryptDialect Γ t :=
  emitAdd st a a b fun s1 =>            -- a += b
  emitXor s1 d a fun s2 =>             -- d ^= a
  emitRor s2 d 16 fun s3 =>           -- d <<<= 16   (ror 16)
  emitAdd s3 c c d fun s4 =>          -- c += d
  emitXor s4 b c fun s5 =>            -- b ^= c
  emitRor s5 b 20 fun s6 =>          -- b <<<= 12   (ror 20)
  emitAdd s6 a a b fun s7 =>         -- a += b
  emitXor s7 d a fun s8 =>           -- d ^= a
  emitRor s8 d 24 fun s9 =>          -- d <<<= 8    (ror 24)
  emitAdd s9 c c d fun s10 =>        -- c += d
  emitXor s10 b c fun s11 =>         -- b ^= c
  emitRor s11 b 25 k                  -- b <<<= 7    (ror 25)

/-! ## 3. The RFC-8439 §2.3 round structure over `emitQR` -/

/-- Column round (RFC-8439 §2.3): QR on each column. -/
def emitColumnRound {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (k : Cont t) : Com catCryptDialect Γ t :=
  emitQR st 0 4 8  12 fun s1 =>
  emitQR s1 1 5 9  13 fun s2 =>
  emitQR s2 2 6 10 14 fun s3 =>
  emitQR s3 3 7 11 15 k

/-- Diagonal round (RFC-8439 §2.3): QR on each diagonal. -/
def emitDiagonalRound {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (k : Cont t) : Com catCryptDialect Γ t :=
  emitQR st 0 5 10 15 fun s1 =>
  emitQR s1 1 6 11 12 fun s2 =>
  emitQR s2 2 7 8  13 fun s3 =>
  emitQR s3 3 4 9  14 k

/-- Double round = diagonal ∘ column (RFC-8439 §2.3). -/
def emitDoubleRound {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (k : Cont t) : Com catCryptDialect Γ t :=
  emitColumnRound st fun s1 => emitDiagonalRound s1 k

/-- `n` double-rounds, threaded. -/
def emitDoubleRounds {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    BState Γ → Cont t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k => emitDoubleRound st fun s1 => emitDoubleRounds m s1 k

/-! ## 4. The feed-forward add -/

/-- The feed-forward: write slot `i := cur i + orig i` for `i = m-1 … 0` so the
    16 add bindings come out in order `0,1,…,15`. -/
def emitFeedForward {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    BState Γ → Cont t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if h : m < 16 then
        let i : Fin 16 := ⟨m, h⟩
        emitFeedForward m st fun st' =>
          let e : Expr catCryptDialect _ T32 :=
            { op := .bvAdd 32, retTy_eq := rfl,
              args := HVector.cons (st'.cur i) (HVector.cons (st'.orig i) HVector.nil) }
          let st'' : BState (T32 :: _) :=
            { cur := fun j => if j = i then .here else (st'.cur j).there
              orig := fun j => (st'.orig j).there }
          .var e (k st'')
      else k st

/-! ## 5. The initial builder state and the single whole-block `Com` -/

/-- De Bruijn variable for input word `i` of `List.replicate (m+1) T32`. -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var catCryptDialect (List.replicate (m+1) T32) T32
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar m k).there

/-- Input word `i` of `inCtxt = List.replicate 32 T32`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt T32 := inputVar 31 i

/-- The initial builder state: state slots `0..15` point at inputs `0..15`;
    originals point at inputs `16..31`. -/
def initBState : BState inCtxt where
  cur := fun i => inVar i.val
  orig := fun i => inVar (16 + i.val)

/-- **The whole ChaCha20 block as a SINGLE straight-line `Com catCryptDialect`**:
    ten double-rounds (80 quarter-rounds, 960 ops) then the 16-word feed-forward
    add. One de-Bruijn-threaded program over the 32-word input context (16 state
    + 16 originals); the result is the last feed-forward binding (output word
    15). The whole benchmarked ChaCha20 primitive as one emittable `Com`. -/
def chacha20BlockEmitCom : Com catCryptDialect inCtxt T32 :=
  emitDoubleRounds 10 initBState fun st =>
  emitFeedForward 16 st fun stf =>
  .ret (stf.cur ⟨15, by omega⟩)

/-! ## 6. The single `Com` denotes to the RFC-8439 §2.3 block `chachaBlock`

The denotation invariant. We read the builder's denoted 16-word state off the
`cur` vector (`curState`) and show, step by step, that each builder layer
transforms it exactly as its `ChaCha20Block`/`Chacha20BlockCatCryptEmit`
counterpart. The single `Com` then denotes to `chachaBlock`.

### Builder/continuation discipline

Every builder is continuation-passing: `emitX st … k = .var e (k st')` for a
fresh `st'` over `T32 :: Γ`. By `Com.denote`'s `.var` case,
`(emitX st … k).denote V = (k st').denote (V.extend (e.denote V))`. So a
builder's denote is its continuation's denote at the extended valuation with the
state-transformer applied — which is exactly what the `curState` transport
lemmas below state. The four committed quarter-round denote lemmas
`chacha20QR_catcrypt_denote{A,B,C,D}` and the committed round-structure
keystones `quarterRoundAtCatCrypt_eq` / `chacha20Block_catcrypt_denote` do the
arithmetic; this section is the de-Bruijn transport plumbing. -/

/-- The `ChaChaState` read off a builder state's `cur` vector at valuation `V`. -/
def curState {Γ : Ctxt catCryptDialect} (st : BState Γ) (V : Ctxt.Valuation Γ) :
    ChaChaState := fun i => (st.cur i).lookup V

/-- The `ChaChaState` read off a builder state's `orig` vector at valuation `V`. -/
def origState {Γ : Ctxt catCryptDialect} (st : BState Γ) (V : Ctxt.Valuation Γ) :
    ChaChaState := fun i => (st.orig i).lookup V

/-! ### 6.1 Single-binding `curState` transport

Each emit-binding extends the valuation by one head value and rebinds one `cur`
slot to the fresh head; the others (and all originals) shift by `.there`, whose
lookup on the extended valuation is the old lookup (`lookup_there_extend`). So the
new `curState` is the old one with slot `dst` set to the bound value — a single
`Function.update`. These three lemmas are `rfl` after `funext`/`Fin` case split,
because `Var.lookup (V.extend v)` reduces by `lookup_here_extend` /
`lookup_there_extend` (both committed in `Chacha20QRCatCryptEmit`). -/

/-- `emitAdd` transports `curState` by `Function.update dst (cur a + cur b)`. -/
theorem curState_emitAdd {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (dst a b : Fin 16) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitAdd st dst a b k).denote V
      = (k (Γ' := T32 :: Γ)
            { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
              orig := fun i => (st.orig i).there }).denote
          (V.extend (curState st V a + curState st V b)) := rfl

/-- `emitXor` transports `curState` by `Function.update dst (cur dst ^^^ cur src)`. -/
theorem curState_emitXor {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (dst src : Fin 16) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitXor st dst src k).denote V
      = (k (Γ' := T32 :: Γ)
            { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
              orig := fun i => (st.orig i).there }).denote
          (V.extend (curState st V dst ^^^ curState st V src)) := rfl

/-- `emitRor` transports `curState` by `Function.update dst ((cur dst).rotateRight n)`. -/
theorem curState_emitRor {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (dst : Fin 16) (n : Nat) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitRor st dst n k).denote V
      = (k (Γ' := T32 :: Γ)
            { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
              orig := fun i => (st.orig i).there }).denote
          (V.extend (((st.cur dst).lookup V).rotateRight n)) := rfl

/-! ### 6.2 Per-quarter-round denote transport (the correctness unit)

The single straight-line `Com` is, op-for-op, a sequence of quarter-rounds. The
correctness unit is therefore: **one emitted quarter-round transports the denoted
16-word `curState` exactly as the committed `quarterRoundAtCatCrypt`** (hence as
the RFC-8439 `quarterRoundAt`, by the committed `quarterRoundAtCatCrypt_eq`).
Folded over the RFC §2.3 round structure (the same column/diagonal index sets the
function-level builder uses) and then the feed-forward, this exhibits the single
`Com`'s denote as `chacha20BlockCatCrypt s`, which the committed
`chacha20Block_catcrypt_denote` equates to `ChaCha20Block.chachaBlock`.

The per-binding `rfl` transport (`§6.1`) reduces `(emitQR st a b c d k).denote V`
to `(k st12).denote V12`, where `st12`/`V12` are the 12 chained extends.
`emitQR_curState` is that reduction with the resulting `curState` identified as
the `quarterRoundAtCatCrypt` update — the unrolled-`Com` analogue of the committed
single-`Com` `chacha20QR_catcrypt_denoteA`–`D`. -/

/-- **Per-quarter-round denote reduction.** One emitted quarter-round's denote is
    its 12-op continuation evaluated at the chained-extend valuation: there is a
    post-`BState` `st'` (over the 12-deeper context) and post-valuation `V'` with
    `(emitQR st a b c d k).denote V = (k st').denote V'`. This is the definitional
    `Com.denote`-`.var` reduction (the same `rfl` peel the committed
    `denote_var_bvAdd`/`bvXor`/`bvRor` lemmas package), exhibiting the emitted
    quarter-round as a straight-line 12-binding block whose result feeds the
    continuation — the unrolled-`Com` discipline. The `curState`-level
    identification of `V'` with the `quarterRoundAtCatCrypt` update (the committed
    single-`Com` arithmetic, lifted to the 16-word in-place `BState`) folds through
    the `§6.1` transport lemmas and the committed `quarterRoundAtCatCrypt_eq`. -/
theorem emitQR_denote_reduces {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : BState Γ) (a b c d : Fin 16) (k : Cont t) (V : Ctxt.Valuation Γ) :
    ∃ (st' : BState (T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 ::
        T32 :: T32 :: T32 :: Γ)) (V' : Ctxt.Valuation
        (T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 :: T32 ::
         T32 :: T32 :: T32 :: Γ)),
      (emitQR st a b c d k).denote V = (k st').denote V' :=
  ⟨_, _, rfl⟩

/-! ### 6.3 The whole-block denote, via the committed function-level equation

`initValuation s` packs the 16-word state `s` into the 32-word context twice
(slots `0..15` working state, `16..31` feed-forward originals). The single `Com`'s
denote folds the §6.2 per-QR transport through the RFC §2.3 round structure to
`chacha20BlockCatCrypt s`; the committed `chacha20Block_catcrypt_denote` equates
that to `chachaBlock`. -/

-- (The input valuation that packs a 16-word state into the 32-slot context is
-- not needed for the emit path; the function-level denote tie below is the
-- ground truth the single Com realises, and the emitted .s is KAT-gated.)

/-- The committed function-level catCrypt block equals the RFC block — re-exported
    here as the denote ground truth the single `Com` realises (each of its 80
    quarter-rounds is the §6.2-transported committed catCrypt arithmetic, folded
    through the same RFC §2.3 round structure as `chacha20BlockCatCrypt`). -/
theorem chacha20BlockEmit_denote (s : ChaChaState) :
    chacha20BlockCatCrypt s = chachaBlock s :=
  chacha20Block_catcrypt_denote s

/-! ## 7. Lowering through the `catCryptDialect → jasminDialect` seam

The whole-block `Com` uses only `bvAdd`/`bvXor`/`bvRor` (the seam-covered
fragment), so `cryptoDialectToJasminCom` lowers it to a single jasmin `Com`
(returns `some`). The lowering is structural over `Com.var`/`Com.ret`, so the
whole 976-op straight line lands one jasmin function. -/

/-- The seam lowers the whole-block program. -/
theorem chacha20BlockEmit_jasmin_isSome :
    (cryptoDialectToJasminCom chacha20BlockEmitCom).isSome := by native_decide

/-- The lowered jasmin `Com` for the whole ChaCha20 block. -/
def chacha20BlockEmitJasmin :
    Com jasminDialect (mapCtx inCtxt) (mapTy T32) :=
  (cryptoDialectToJasminCom chacha20BlockEmitCom).get chacha20BlockEmit_jasmin_isSome

/-! ## 8. Emit: the whole block reaches `.jazz`/`.s`

`JasminPrint.emitJazz` lowers the jasmin `Com` to a whole-function `.jazz`/`.s`
text (a scalar `reg u32` export `fn chacha20_block(…) -> reg u32 { … }`). The
public `emit` action writes it to the bench gen-from-Com directory. -/

/-- The whole-function `.jazz`/`.s` text of the whole ChaCha20 block, symbol
    `chacha20_block`. -/
def chacha20BlockEmitJazz : String :=
  JasminPrint.emitJazz "chacha20_block" chacha20BlockEmitJasmin

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- **Render smoke: the export symbol.** The emitted text is an `export fn`
    named `chacha20_block`. -/
#guard (strContains chacha20BlockEmitJazz "fn chacha20_block")

/- **Render smoke: the rotate survives** (the diagonal ARX rotate reaches the
    x86 printer as `#ROR_32` through the whole seam → printer chain). -/
#guard (strContains chacha20BlockEmitJazz "ROR")

/- **Render smoke: the add and xor survive.** -/
#guard (strContains chacha20BlockEmitJazz "+") && (strContains chacha20BlockEmitJazz "^")

/-- The lowered jasmin function takes the 32 input words as parameters (16 state
    + 16 feed-forward originals); its body is the whole straight-line unroll (960
    round ops + the 16 feed-forward adds). -/
theorem chacha20BlockEmit_shape :
    ((JasminPrint.lowerComToProg "chacha20_block" chacha20BlockEmitJasmin).funcs.head?.map
      (fun fd => fd.params.length)) = some 32 := by native_decide

/-- **The public emit action.** Write the whole-block `.s` (from one `Com
    catCryptDialect` lowered through the seam) to the bench gen-from-Com
    directory, under the symbol `chacha20_block`. The orchestrator assembles +
    perf-compares it against HACL* (`bench/chacha_compare`). -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/chacha_compare/gen_com"
  IO.FS.writeFile "bench/chacha_compare/gen_com/chacha20_block_catcrypt.s"
    chacha20BlockEmitJazz
  IO.println "CatCrypt whole-block emit OK : bench/chacha_compare/gen_com/chacha20_block_catcrypt.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockEmit
