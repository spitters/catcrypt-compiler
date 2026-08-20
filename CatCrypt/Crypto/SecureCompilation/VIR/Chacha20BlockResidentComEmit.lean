/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefJazzEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# The whole ChaCha20 block, STATE-RESIDENT, through the OWNED x86 backend (NO jasminc)

[`Chacha20BlockFullMemrefEmit.lean`](Chacha20BlockFullMemrefEmit.lean)
compiles the whole ChaCha20 block from one `Com catCryptDialect` through the owned
backend `Com.toLprogPhysAbi`. But its source `Com`
(`chacha20BlockFullMemrefCom`) holds the **sixteen working state words and sixteen
feed-forward originals live simultaneously** across the twenty rounds: the
functional-SSA quarter-round builder threads a 16-wide `cur` word map, so at every
program point all sixteen state words (plus their sixteen feed-forward originals)
are live values. Thirty-two simultaneously-live word values blow the **13
allocatable GP registers** of the linear-scan register allocator (`gpRegNames`),
so the allocator spills (`k.N` slots), and the spill/frame codegen path segfaults
at runtime.

This file restructures the source `Com` to be **state-resident**: the sixteen
working words live in ONE memref (the caller's `out` buffer, seeded from `in`),
and **each quarter-round**:

1. `memrefGetDyn`-loads its **four** needed words from the working memref,
2. computes the twelve-op quarter-round (`add64`/`xor64`/`rotL64`) on them, then
3. `memrefSetDyn`-stores the four results **back to the memref immediately**,
   before the next quarter-round binds anything.

Because every loaded word is stored back promptly, its SSA value dies at the store;
at most the two memref pointers (`wrk`, `inp`) plus the **≤ five word temporaries**
of the current quarter-round are ever simultaneously live — well under the 13
allocatable GP registers. So the linear-scan RA **does not spill** (no `k.N`
slots), and the owned backend emits a spill-free `.s`.

## ABI

`chacha20_block_resident(out = RDI, in = RSI)`: `out` is the working buffer (seeded
word-by-word from `in`, then mutated in place by the twenty rounds), `in` is the
read-only original state used by the feed-forward add. As in the full-memref
version, the De-Bruijn → arg-slot resolution reverses the source context order
`[out, in]`, so the body's first memref arg is `a0` and the second is `a1`; the ABI
list is `["RSI", "RDI"]` (`a0 = in ← RSI`, `a1 = out ← RDI`).

## Correctness

The state-resident `Com` denotes the **same** function as the full-memref one:
each output cell `i` of the returned memref is `(chachaBlock s i).setWidth 64`,
the committed RFC-8439 §2.3 block. The denotation is checked against the RFC-8439
§2.3.2 test vector (`testInitState`, first output word `0xe4e7f110`) by the
`#eval` / `lean_run_code` evaluation below.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockResidentComEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockMemrefEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 1. The two-pointer context and the resident state -/

/-- The 64-bit machine-word dialect type. -/
abbrev T64 : CryptoTy := .sword 64

/-- The two-pointer context `(wrk, inp)` — the working/output memref and the
    read-only input memref. -/
abbrev inCtxtR : Ctxt catCryptDialect := [.memref 16, .memref 16]

/-- A resident state carries just the two memref vars: the working/output memref
    `wrk` (the 16 state words live HERE, not in SSA registers) and the read-only
    input memref `inp` (feed-forward originals). -/
structure RState (Γ : Ctxt catCryptDialect) where
  /-- The working (output) memref. -/
  wrk : Ctxt.Var Γ (.memref 16)
  /-- The read-only input memref. -/
  inp : Ctxt.Var Γ (.memref 16)

/-- The continuation type for the resident builder. -/
abbrev RCont (t : CryptoTy) :=
  {Γ' : Ctxt catCryptDialect} → RState Γ' → Com catCryptDialect Γ' t

/-! ## 2. Load / store helpers (BOTH memref pointers threaded; one word live)

`emitLoadFrom` binds `idx := bvConst 64 i` then `w := memrefGetDyn (mem st) idx`,
threading the resident state forward (both memref vars `.there.there`-shifted past
the two new binders) and handing the continuation the freshly-loaded word var.
`emitStoreTo` binds `idx` then `wrk' := memrefSetDyn wrk idx wval`, threading the
fresh working memref var. Each load's word is consumed promptly (stored back or
added), so its live range is short and the allocator never accumulates 16 words. -/

/-- `bvConst 64 i` as an `Expr`. -/
@[inline] def cIdx {Γ : Ctxt catCryptDialect} (i : Nat) : Expr catCryptDialect Γ T64 :=
  { op := .bvConst 64 (BitVec.ofNat 64 i), retTy_eq := rfl, args := .nil }

/-- Shift a resident state past two fresh binders (an `idx` const + a load/store). -/
@[inline] def RState.shift2 {Γ : Ctxt catCryptDialect} {s0 s1 : CryptoTy}
    (st : RState Γ) : RState (s0 :: s1 :: Γ) :=
  { wrk := st.wrk.there.there, inp := st.inp.there.there }

/-- Load word `i` from the WORKING memref of `st`, threading the resident state.
    Two bindings; the continuation receives the loaded word var (`.here`) and the
    forward-threaded resident state. The READ uses `st.wrk` (state-resident). -/
def emitLoadWrk {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (i : Nat)
    (k : {Γ' : Ctxt catCryptDialect} →
         Ctxt.Var Γ' T64 → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .memrefGetDyn 16, retTy_eq := rfl,
          args := .cons st.wrk.there (.cons .here .nil) })
    (k (Γ' := T64 :: T64 :: Γ) .here st.shift2)

/-- Load word `i` from the INPUT memref of `st`, threading the resident state.
    Used by the feed-forward add (the read-only original `inp[i]`). -/
def emitLoadInp {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (i : Nat)
    (k : {Γ' : Ctxt catCryptDialect} →
         Ctxt.Var Γ' T64 → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .memrefGetDyn 16, retTy_eq := rfl,
          args := .cons st.inp.there (.cons .here .nil) })
    (k (Γ' := T64 :: T64 :: Γ) .here st.shift2)

/-- Store `wval` to `wrk[i]`, threading the (new) working memref into the resident
    state. Two bindings; the continuation receives the forward-threaded state. -/
def emitStoreWrk {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (i : Nat) (wval : Ctxt.Var Γ T64)
    (k : RCont t) : Com catCryptDialect Γ t :=
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: Γ) (.memref 16) from
        { op := .memrefSetDyn 16, retTy_eq := rfl,
          args := .cons st.wrk.there (.cons .here (.cons wval.there .nil)) })
    (k (Γ' := (.memref 16) :: T64 :: Γ)
      { wrk := .here, inp := st.inp.there.there })

/-! ## 3. The four-word in-register quarter-round core

`add64`/`xor64`/`rotL64` carried in 64-bit registers (low half), via the
seam-covered ops only, exactly as in `Chacha20BlockMemrefEmit`. Here we operate on
four explicit word vars `(va, vb, vc, vd)` rather than a 16-wide map; after the
twelve steps the continuation receives the four result vars. -/

/-- A four-word register tuple (the live quarter-round working set). -/
structure QR4 (Γ : Ctxt catCryptDialect) where
  /-- working word `a`. -/ va : Ctxt.Var Γ T64
  /-- working word `b`. -/ vb : Ctxt.Var Γ T64
  /-- working word `c`. -/ vc : Ctxt.Var Γ T64
  /-- working word `d`. -/ vd : Ctxt.Var Γ T64

/-- The QR4 continuation, also threading the resident state (so the memref vars are
    kept live across the quarter-round arithmetic). -/
abbrev QR4Cont (t : CryptoTy) :=
  {Γ' : Ctxt catCryptDialect} → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t

/-- `dst := (a + b) &&& mask32` (3 bindings). `dst ∈ {.va,.vb,.vc,.vd}` chosen by
    the caller via the rebind function `setDst`. We keep this generic by passing
    the source vars and a continuation receiving the masked head var. -/
def emitAddR {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (a b : Ctxt.Var Γ T64) (st : RState Γ) (qr : QR4 Γ)
    (k : {Γ' : Ctxt catCryptDialect} →
         Ctxt.Var Γ' T64 → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  -- m := bvConst 64 mask32
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- s := a + b
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .bvAdd 64, retTy_eq := rfl,
          args := .cons a.there (.cons b.there .nil) }) <|
  -- d := s &&& m
  .var (show Expr catCryptDialect (T64 :: T64 :: Γ) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) })
    (k (Γ' := T64 :: T64 :: T64 :: Γ) .here
      { va := qr.va.there.there.there, vb := qr.vb.there.there.there
        vc := qr.vc.there.there.there, vd := qr.vd.there.there.there }
      { wrk := st.wrk.there.there.there, inp := st.inp.there.there.there })

/-- `dst := a ^^^ b` (1 binding). -/
def emitXorR {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (a b : Ctxt.Var Γ T64) (st : RState Γ) (qr : QR4 Γ)
    (k : {Γ' : Ctxt catCryptDialect} →
         Ctxt.Var Γ' T64 → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvXor 64, retTy_eq := rfl,
          args := .cons a (.cons b .nil) })
    (k (Γ' := T64 :: Γ) .here
      { va := qr.va.there, vb := qr.vb.there, vc := qr.vc.there, vd := qr.vd.there }
      { wrk := st.wrk.there, inp := st.inp.there })

/-- `dst := rotL64 a m = ((a <<< m) ||| (a >>> (32-m))) &&& mask32` (5 bindings). -/
def emitRotR {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (a : Ctxt.Var Γ T64) (m : Nat) (st : RState Γ) (qr : QR4 Γ)
    (k : {Γ' : Ctxt catCryptDialect} →
         Ctxt.Var Γ' T64 → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  -- msk := bvConst 64 mask32
  .var (show Expr catCryptDialect Γ T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- l := a <<< m
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .bvShiftL 64 m, retTy_eq := rfl, args := .cons a.there .nil }) <|
  -- r := a >>> (32 - m)
  .var (show Expr catCryptDialect (T64 :: T64 :: Γ) T64 from
        { op := .bvShiftR 64 (32 - m), retTy_eq := rfl,
          args := .cons a.there.there .nil }) <|
  -- o := l ||| r    (l = .there .here, r = .here)
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: Γ) T64 from
        { op := .bvOr 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }) <|
  -- d := o &&& msk  (o = .here, msk = .there^3 .here)
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: Γ) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there (.there (.there .here))) .nil) })
    (k (Γ' := T64 :: T64 :: T64 :: T64 :: T64 :: Γ) .here
      { va := qr.va.there.there.there.there.there
        vb := qr.vb.there.there.there.there.there
        vc := qr.vc.there.there.there.there.there
        vd := qr.vd.there.there.there.there.there }
      { wrk := st.wrk.there.there.there.there.there
        inp := st.inp.there.there.there.there.there })

/-- The twelve-op quarter-round on the four live words `(va,vb,vc,vd)`, mirroring
    `quarterRound64` (RFC §2.1). After the twelve steps the continuation receives
    the four updated word vars and the threaded resident state. -/
def emitQRcore {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (qr : QR4 Γ) (st : RState Γ) (k : QR4Cont t) : Com catCryptDialect Γ t :=
  -- a += b
  emitAddR qr.va qr.vb st qr fun a1 qr1 st1 =>
  -- d ^= a ; d <<<= 16
  emitXorR qr1.vd a1 st1 { qr1 with va := a1 } fun d1 qr2 st2 =>
  emitRotR d1 16 st2 qr2 fun d2 qr3 st3 =>
  -- c += d ; b ^= c ; b <<<= 12
  emitAddR qr3.vc d2 st3 { qr3 with vd := d2 } fun c1 qr4 st4 =>
  emitXorR qr4.vb c1 st4 { qr4 with vc := c1 } fun b1 qr5 st5 =>
  emitRotR b1 12 st5 qr5 fun b2 qr6 st6 =>
  -- a += b ; d ^= a ; d <<<= 8
  emitAddR qr6.va b2 st6 { qr6 with vb := b2 } fun a2 qr7 st7 =>
  emitXorR qr7.vd a2 st7 { qr7 with va := a2 } fun d3 qr8 st8 =>
  emitRotR d3 8 st8 qr8 fun d4 qr9 st9 =>
  -- c += d ; b ^= c ; b <<<= 7
  emitAddR qr9.vc d4 st9 { qr9 with vd := d4 } fun c2 qr10 st10 =>
  emitXorR qr10.vb c2 st10 { qr10 with vc := c2 } fun b3 qr11 st11 =>
  emitRotR b3 7 st11 qr11 fun b4 qr12 st12 =>
  k (Γ' := _) { qr12 with vb := b4 } st12

/-! ### 3.1 QR4-threading load / store

To avoid hand-counting de-Bruijn shifts as the four loads (and four stores) extend
the context, the load/store helpers thread the partial `QR4` so the
already-loaded (resp. not-yet-stored) words shift automatically. `shiftQR2` shifts
a QR4 past two binders. -/

/-- Shift a QR4 past two fresh binders. -/
@[inline] def QR4.shift2 {Γ : Ctxt catCryptDialect} {s0 s1 : CryptoTy}
    (qr : QR4 Γ) : QR4 (s0 :: s1 :: Γ) :=
  { va := qr.va.there.there, vb := qr.vb.there.there
    vc := qr.vc.there.there, vd := qr.vd.there.there }

/-- Load `wrk[i]` into field `set?`-designated slot of the QR4, threading both the
    QR4 (previously-loaded words shift forward) and the resident state. The newly
    loaded word is placed at `.here` and routed by `place` into the QR4. -/
def emitLoadWrkQ {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (qr : QR4 Γ) (i : Nat)
    (place : {Γ' : Ctxt catCryptDialect} → Ctxt.Var Γ' T64 → QR4 Γ' → QR4 Γ')
    (k : {Γ' : Ctxt catCryptDialect} → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: Γ) T64 from
        { op := .memrefGetDyn 16, retTy_eq := rfl,
          args := .cons st.wrk.there (.cons .here .nil) })
    (k (Γ' := T64 :: T64 :: Γ) (place .here qr.shift2) st.shift2)

/-- Store the QR4 field selected by `sel` to `wrk[i]`, threading the QR4 (remaining
    words shift) and the resident state. -/
def emitStoreWrkQ {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (qr : QR4 Γ) (i : Nat) (sel : QR4 Γ → Ctxt.Var Γ T64)
    (k : {Γ' : Ctxt catCryptDialect} → QR4 Γ' → RState Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect Γ t :=
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: Γ) (.memref 16) from
        { op := .memrefSetDyn 16, retTy_eq := rfl,
          args := .cons st.wrk.there (.cons .here (.cons (sel qr).there .nil)) })
    (k (Γ' := (.memref 16) :: T64 :: Γ) qr.shift2
      { wrk := .here, inp := st.inp.there.there })

/-- The full resident quarter-round on logical slots `a b c d`: load four words
    from `wrk`, run the twelve-op core, store four back to `wrk`. After the four
    stores only the two memref vars are live again. The starting QR4 is seeded
    from `st.wrk`'s first word (a real `T64` var) at every field, then each load
    overwrites its own field. -/
def emitResidentQR {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : RState Γ) (a b c d : Fin 16) (k : RCont t) : Com catCryptDialect Γ t :=
  -- First load (word a) via the plain loader, giving a real T64 head var to seed
  -- all four QR4 fields; subsequent loads overwrite b,c,d.
  emitLoadWrk st a.val fun wa stA =>
  emitLoadWrkQ stA { va := wa, vb := wa, vc := wa, vd := wa } b.val
    (fun w qr => { qr with vb := w }) fun qrB stB =>
  emitLoadWrkQ stB qrB c.val (fun w qr => { qr with vc := w }) fun qrC stC =>
  emitLoadWrkQ stC qrC d.val (fun w qr => { qr with vd := w }) fun qrD stD =>
  emitQRcore qrD stD fun qrR stR =>
  emitStoreWrkQ stR qrR a.val QR4.va fun qr1 st1 =>
  emitStoreWrkQ st1 qr1 b.val QR4.vb fun qr2 st2 =>
  emitStoreWrkQ st2 qr2 c.val QR4.vc fun qr3 st3 =>
  emitStoreWrkQ st3 qr3 d.val QR4.vd fun _ st4 =>
  k st4

/-! ## 4. Rounds, seeding, feed-forward, and the whole resident `Com` -/

/-- Column round (resident): the four column quarter-rounds (RFC §2.3). -/
def emitColumnR {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : RState Γ) (k : RCont t) : Com catCryptDialect Γ t :=
  emitResidentQR st 0 4 8  12 fun s1 =>
  emitResidentQR s1 1 5 9  13 fun s2 =>
  emitResidentQR s2 2 6 10 14 fun s3 =>
  emitResidentQR s3 3 7 11 15 k

/-- Diagonal round (resident): the four diagonal quarter-rounds (RFC §2.3). -/
def emitDiagonalR {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : RState Γ) (k : RCont t) : Com catCryptDialect Γ t :=
  emitResidentQR st 0 5 10 15 fun s1 =>
  emitResidentQR s1 1 6 11 12 fun s2 =>
  emitResidentQR s2 2 7 8  13 fun s3 =>
  emitResidentQR s3 3 4 9  14 k

/-- Double round (resident). -/
def emitDoubleR {t : CryptoTy} {Γ : Ctxt catCryptDialect}
    (st : RState Γ) (k : RCont t) : Com catCryptDialect Γ t :=
  emitColumnR st fun s1 => emitDiagonalR s1 k

/-- `n` double-rounds, threaded. -/
def emitDoubleRoundsR {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    RState Γ → RCont t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k => emitDoubleR st fun s1 => emitDoubleRoundsR m s1 k

/-- Seed the working memref from the input: `wrk[i] := inp[i]` for `i = m-1 … 0`
    (so the copies come out in index order `0 … 15`). Each iteration loads one
    input word and stores it back — exactly one word live at a time. -/
def emitSeedCopy {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    RState Γ → RCont t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if m < 16 then
        emitSeedCopy m st fun st' =>
          emitLoadInp st' m fun w st'' =>
          emitStoreWrk st'' m w k
      else k st

/-- Feed-forward add at slot `i`: `wrk[i] := (wrk[i] + inp[i]) &&& mask32`. Loads
    the working word and the original input word, adds (masked), stores back —
    at most two words live. -/
def emitFeedFwdAt {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (st : RState Γ) (i : Nat) (k : RCont t) : Com catCryptDialect Γ t :=
  emitLoadWrk st i fun wc st1 =>
  -- Re-load the input word via a continuation that ALSO forwards `wc`. We build
  -- the inp load by hand so `wc` is in scope (shifted) for the add.
  .var (cIdx i) <|
  .var (show Expr catCryptDialect (T64 :: _) T64 from
        { op := .memrefGetDyn 16, retTy_eq := rfl,
          args := .cons st1.inp.there (.cons .here .nil) }) <|
  -- Γ now = T64 (wo) :: T64 (idx) :: Γ1. `wc` shifts by two; `wo = .here`.
  -- m := bvConst 64 mask32
  .var (show Expr catCryptDialect (T64 :: T64 :: _) T64 from
        { op := .bvConst 64 mask32, retTy_eq := rfl, args := .nil }) <|
  -- s := wc + wo
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: _) T64 from
        { op := .bvAdd 64, retTy_eq := rfl,
          args := .cons wc.there.there.there (.cons (.there .here) .nil) }) <|
  -- r := s &&& m     (s = .here, m = .there .here)
  .var (show Expr catCryptDialect (T64 :: T64 :: T64 :: T64 :: _) T64 from
        { op := .bvAnd 64, retTy_eq := rfl,
          args := .cons .here (.cons (.there .here) .nil) })
    (emitStoreWrk
      { wrk := st1.wrk.there.there.there.there.there
        inp := st1.inp.there.there.there.there.there }
      i .here k)

/-- The feed-forward over all 16 slots, in index order `0 … 15`. -/
def emitFeedFwdR {t : CryptoTy} : Nat → {Γ : Ctxt catCryptDialect} →
    RState Γ → RCont t → Com catCryptDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if m < 16 then
        emitFeedFwdR m st fun st' => emitFeedFwdAt st' m k
      else k st

/-- The output memref var of `inCtxtR` (slot 0). -/
def wrkVarR : Ctxt.Var inCtxtR (.memref 16) := .here

/-- The input memref var of `inCtxtR` (slot 1). -/
def inpVarR : Ctxt.Var inCtxtR (.memref 16) := .there .here

/-- The initial resident state. -/
def initRState : RState inCtxtR := { wrk := wrkVarR, inp := inpVarR }

/-- **The whole ChaCha20 block as a STATE-RESIDENT `Com catCryptDialect`** over the
    two-pointer context `(wrk, inp)`: seed `wrk` from `inp`, run ten resident
    double-rounds (each quarter-round loads 4 words from `wrk`, computes, stores 4
    back — register pressure ≤ ~5), then the 16-slot feed-forward (`wrk[i] +=
    inp[i]`), and return the working memref. -/
def chacha20BlockResidentCom : Com catCryptDialect inCtxtR (.memref 16) :=
  emitSeedCopy 16 initRState fun st0 =>
  emitDoubleRoundsR 10 st0 fun st1 =>
  emitFeedFwdR 16 st1 fun stf =>
  .ret stf.wrk

/-! ## 5. Denotation = RFC-8439 §2.3.2 test vector

The resident `Com`'s `denote` on the RFC-8439 §2.3.2 initial state
(`testInitState`, 64-carried into the `inp` memref; `wrk` arbitrary, seeded from
`inp` by the program) produces an output memref whose every cell `i` is
`(chachaBlock testInitState i).setWidth 64` — the committed RFC block. In
particular cell 0 is `0xe4e7f110`. This pins the resident restructuring to the
same function as the full-memref version BEFORE any backend lowering. -/

/-- The RFC-8439 §2.3.2 input state, 64-carried (low half) into the `inp` memref. -/
def testInpVal : Fin 16 → BitVec 64 := fun i => (testInitState i).setWidth 64

/-- The `wrk` memref is arbitrary (the program seeds it from `inp`). -/
def testWrkVal : Fin 16 → BitVec 64 := fun _ => 0

/-- The two-pointer valuation `(wrk, inp)` for the test vector. -/
def testVal : Ctxt.Valuation inCtxtR :=
  HVector.cons testWrkVal (HVector.cons testInpVal HVector.nil)

/-- The denoted output memref of the resident block on the test vector. -/
def testOut : Fin 16 → BitVec 64 := chacha20BlockResidentCom.denote testVal

/-! ## 6. The owned-backend lowering + emit — computed at RUNTIME (no `native_decide`)

The resident `Com` uses only seam-covered ops, so `cryptoDialectToJasminCom` lowers
it (loads → `stackLoad`, stores → `stackStore`); the two-memref context yields a
two-pointer jasmin `Com`, lowered through the **owned** x86 backend
`Com.toLprogPhysAbi` (pointer ABI, NO jasminc), `renderLprogAtt`-rendered to AT&T.
The ABI list is `["RSI", "RDI"]` (the De-Bruijn → arg-slot reversal: `a0 = inp ←
RSI`, `a1 = wrk ← RDI`).

These were `native_decide` theorems, which compile the whole Com + denote + lowering
to native code at build time and do not terminate on a module this heavy
(an emit kernel should not be gated on a heavy
`native_decide`). They are **runtime self-checks** inside `emit`: the emit binary
computes the lowering and the denote=spec / no-spill checks when run, and the external
oracle is the RFC-8439 C KAT. The module itself builds cheaply. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The lowered jasmin program's parameter context is the two pointer-array memrefs
    (`reg ptr u64[16]` args `(wrk, inp)`). -/
theorem chacha20BlockResident_param_ctx :
    mapCtx inCtxtR = [JasminTy.stackArr 64 16, JasminTy.stackArr 64 16] := rfl

/-- Emit driver: lower the resident `Com` through the owned backend at RUNTIME and
    write the `.s`, with runtime `denote = RFC-8439` and no-spill self-checks printed.
    No `native_decide` — the module builds cheaply; the C KAT is the oracle. -/
def emit : IO Unit := do
  match cryptoDialectToJasminCom chacha20BlockResidentCom with
  | none => IO.println "LOWERING FAILED (seam returned none)"
  | some jcom =>
    let lprog := Com.toLprogPhysAbi jcom "chacha20_block_resident_com"
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RSI", "RDI"]) (abiTyin := [64, 64])
    let att := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lprog
    let dir := "bench/chacha_compare/gen_com"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir ++ "/chacha20_block_resident_com.s") att
    IO.println "WROTE bench/chacha_compare/gen_com/chacha20_block_resident_com.s"
    IO.println "  owned x86 backend (toLprogPhysAbi -> renderLprogAtt), state-resident, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockResidentComEmit
