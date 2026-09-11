/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# BIT-EXACT 16-way ChaCha20 dword quarter-round on the UNIFIED `Com jasminDialect`

SIMD-dialect-unification migration of the 16-way (512-bit, `16 × u32`) ChaCha20
quarter-round off the bespoke `Avx512DwordModel` (`ZInstr32D`/`runZBlock32D`)
machine onto the verified `Com jasminDialect`. The pre-existing realization
(`X86Backend/Chacha20DwordRealization.lean`) expresses the quarter-round as
a straight-line `ZInstr32D` block (`qrBlockP32`) over the bespoke dword ZMM
register machine (`ZState32`, `runZBlock32D`); this module re-expresses the same
ARX data flow as a single-output `Com jasminDialect` program built only from the
verified-dialect dword ops added for the dword migration:

* `JasminOp.vpackZMMd .add` — `VPADDD`, 16-lane `u32` wrapping add (`zmmPackD .add`);
* `JasminOp.vpackZMMd .xor` — `VPXORD`, 16-lane `u32` xor (`zmmPackD .xor`);
* `JasminOp.vprordZMM n` — `VPRORD`, per-lane `u32` rotate-RIGHT by `n` (`zmmRorD n`).

## The quarter-round and its op coverage

RFC 8439 §2.1 `QUARTERROUND(a,b,c,d)` is

```
a += b ; d ^= a ; d <<<= 16
c += d ; b ^= c ; b <<<= 12
a += b ; d ^= a ; d <<<=  8
c += d ; b ^= c ; b <<<=  7
```

with `+` mod-2³² add and `<<<` the 32-bit rotate-LEFT. On the dword ZMM lane the
add is `VPADDD` and the xor `VPXORD`; the rotate-left is `VPROLD`, but the
verified dialect carries `VPRORD` (`vprordZMM` = `zmmRorD`, per-lane rotate-RIGHT).
Since a `u32` rotate-left by `k` equals a rotate-right by `32-k`:

| QR rotate | rotate-left amount | `vprordZMM` arg (`32 - k`) |
|-----------|--------------------|----------------------------|
| `<<<16`   | 16                 | `vprordZMM 16`             |
| `<<<12`   | 12                 | `vprordZMM 20`             |
| `<<< 8`   | 8                  | `vprordZMM 24`             |
| `<<< 7`   | 7                  | `vprordZMM 25`             |

so every op of the quarter-round is one of `vpackZMMd .add` / `vpackZMMd .xor` /
`vprordZMM` — **no new op is needed**, and unlike the 128-bit 4-way variant
(`bench/chacha_compare/chacha_4way_qr_com_emit.lean`) the non-byte-aligned
`<<<12` / `<<<7` rotates need **no** `VPSLLD`/`VPSRLD`/`VPOR` shift-or
decomposition and **no** broadcast shift-count or `VPSHUFB` mask registers: the
dword lane has a single-op rotate, so the input context is just the four state
registers `a b c d`.

## What is proved here

A `Com` is single-output; the quarter-round threads four registers through a
sequential dependency chain. The whole straight-line quarter-round is given as
four `Com jasminDialect` programs over the shared 4-register input context — one
per output register `a' b' c' d'` — each denoting to the corresponding component
of the pure spec `qrSpecZ`, the RFC-8439 §2.1 quarter-round written directly in
the verified-dialect dword waist functions `zmmPackD` / `zmmRorD`. The denote
lemmas peel one binding at a time (`peel_qr`): `Com.denote` of the straight-line
program steps through the `vpackZMMd` / `vprordZMM` denote arms to the
`zmmPackD` / `zmmRorD` waist calls — the carry-free packed semantics shared with
the bespoke `ZState32` lane math (no re-proof of the lane arithmetic).

A `#eval`-backed lane-0 cross-check against the RFC-8439 §2.1 single quarter-round
test vector (`a=0x11111111 b=0x01020304 c=0x9b8d6f43 d=0x01234567` ↦
`a=0xea2a92f4 b=0xcb1cf8ce c=0x4581472e d=0x5881c4bb`) pins the four programs to a
real reference output, catching any de-Bruijn off-by-one the denote pin would miss.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register type and the input context

A single `reg 512` (one ZMM, `16 × u32` lane-vector — the dword ChaCha state
register) is the working type. The quarter-round threads the four state
registers `a b c d`; there are no constant registers (the dword rotate is a
single op, so no broadcast shift-count or shuffle-mask registers). -/

/-- The `reg 512` dialect type (one `16 × u32` ZMM lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- The input context of the dword quarter-round: the four state registers
    `a b c d`, each `reg 512`. De Bruijn order `a = .here`, `b = .there .here`,
    `c = .there (.there .here)`, `d = .there (.there (.there .here))`. -/
abbrev qrCtx : Ctxt jasminDialect := [r512, r512, r512, r512]

/-! ### Single-binding denote step lemmas

A whole-program `unfold; rfl` forces `Com.denote` to whnf the entire 12-binding
nest at once (each `Expr.denote` carries a `retTy_eq ▸` cast over `BitVec 512`),
which blows past the heartbeat budget. Instead we peel one binding at a time with
these single-layer step lemmas — each a cheap `rfl` — so the denote proofs are a
linear `rw` chain (the `KeccakThetaPiCom.lean` pattern). -/

/-- **One `vpackZMMd` binding peels to a `zmmPackD` and an extended valuation.** -/
theorem denote_var_vpackZMMd {Γ : Ctxt jasminDialect} {s : JasminTy}
    (bop : JasminBinOp) (va vb : Ctxt.Var Γ r512)
    (body : Com jasminDialect (r512 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (JasminOp.vpackZMMd bop) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (zmmPackD bop (va.lookup V) (vb.lookup V))) :=
  rfl

/-- **One `vprordZMM` binding peels to a `zmmRorD` and an extended valuation.** -/
theorem denote_var_vprordZMM {Γ : Ctxt jasminDialect} {s : JasminTy}
    (n : Nat) (va : Ctxt.Var Γ r512)
    (body : Com jasminDialect (r512 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (JasminOp.vprordZMM n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (zmmRorD n (va.lookup V))) :=
  rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt jasminDialect} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head. -/
@[simp] theorem lookup_here_cons {Γ : Ctxt jasminDialect} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (.cons v V) = w.lookup V := rfl

/-! ## 2. The pure spec in the verified-dialect dword waist functions

Each op is the verified-dialect dword denotation, so the `Com` denote lemmas are
`rfl`. `pAdd = zmmPackD .add` (`VPADDD`), `pXor = zmmPackD .xor` (`VPXORD`), and
the rotate-left-by-`k` is `vprordZMM (32-k) = zmmRorD (32-k)` (`VPRORD`). -/

/-- Packed `16 × u32` add (`VPADDD`). -/
def pAdd (x y : BitVec 512) : BitVec 512 := zmmPackD .add x y
/-- Packed `16 × u32` xor (`VPXORD`). -/
def pXor (x y : BitVec 512) : BitVec 512 := zmmPackD .xor x y

/-- The dword quarter-round spec on the four state registers, the RFC-8439 §2.1
    quarter-round computed directly in the verified-dialect dword waist functions:
    `+` is `zmmPackD .add` (per-lane mod-2³² add), `^` is `zmmPackD .xor`, and
    each `<<<k` is `zmmRorD (32-k)` (per-lane `u32` rotate-left by `k`). Returns
    `(a', b', c', d')`. -/
def qrSpecZ (a b c d : BitVec 512) :
    BitVec 512 × BitVec 512 × BitVec 512 × BitVec 512 :=
  let a := pAdd a b
  let d := zmmRorD 16 (pXor d a)        -- d ^= a ; d <<<= 16
  let c := pAdd c d
  let b := zmmRorD 20 (pXor b c)        -- b ^= c ; b <<<= 12
  let a := pAdd a b
  let d := zmmRorD 24 (pXor d a)        -- d ^= a ; d <<<=  8
  let c := pAdd c d
  let b := zmmRorD 25 (pXor b c)        -- b ^= c ; b <<<=  7
  (a, b, c, d)

/-! ## 3. The dialect-native quarter-round programs `Com jasminDialect`

The straight-line quarter-round, threading `a b c d` through the `vpackZMMd` /
`vprordZMM` ops. Each `.var` extends the context at the front, so the inputs (and
earlier results) shift one slot deeper after each binding. The four programs
share the same straight-line body and return the matching final register.

The op sequence (12 bindings) is:
```
 0  t0  = vpackZMMd .add  a   b      -- a += b
 1  t1  = vpackZMMd .xor  d   t0     -- d ^= a
 2  t2  = vprordZMM 16    t1         -- d <<<= 16
 3  t3  = vpackZMMd .add  c   t2     -- c += d
 4  t4  = vpackZMMd .xor  b   t3     -- b ^= c
 5  t5  = vprordZMM 20    t4         -- b <<<= 12
 6  t6  = vpackZMMd .add  t0  t5     -- a += b
 7  t7  = vpackZMMd .xor  t2  t6     -- d ^= a
 8  t8  = vprordZMM 24    t7         -- d <<<=  8
 9  t9  = vpackZMMd .add  t3  t8     -- c += d
10  t10 = vpackZMMd .xor  t5  t9     -- b ^= c
11  t11 = vprordZMM 25    t10        -- b <<<=  7
```
Final outputs: `a' = t6`, `b' = t11`, `c' = t9`, `d' = t8`. -/

/-- The shared 12-binding dword quarter-round body, continued by `k` which selects
    the output variable in the final (extended) context `[t11,…,t0] ++ qrCtx`. -/
def qrBody (k : Com jasminDialect
    ([r512, r512, r512, r512, r512, r512,
      r512, r512, r512, r512, r512, r512] ++ qrCtx) r512) :
    Com jasminDialect qrCtx r512 :=
  -- 0  t0 = a + b           a=.here(0), b=.there.here(1)
  .var (.mk (.vpackZMMd .add) rfl
          (.cons .here (.cons (.there .here) .nil)))
  -- 1  t1 = d ^ t0          d was idx 3 → now .there^4 .here ; t0 = .here
  (.var (.mk (.vpackZMMd .xor) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- 2  t2 = vprordZMM 16 t1 t1 = .here
  (.var (.mk (.vprordZMM 16) rfl
          (.cons .here .nil))
  -- 3  t3 = c + t2          c was idx 2 → now .there^5 .here ; t2 = .here
  (.var (.mk (.vpackZMMd .add) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  -- 4  t4 = b ^ t3          b was idx 1 → now .there^5 .here ; t3 = .here
  (.var (.mk (.vpackZMMd .xor) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  -- 5  t5 = vprordZMM 20 t4 t4 = .here
  (.var (.mk (.vprordZMM 20) rfl
          (.cons .here .nil))
  -- 6  t6 = t0 + t5         t0 depth (6-1)-0 = 5 = .there^5 .here ; t5 = .here
  (.var (.mk (.vpackZMMd .add) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  -- 7  t7 = t2 ^ t6         t2 depth (7-1)-2 = 4 = .there^4 .here ; t6 = .here
  (.var (.mk (.vpackZMMd .xor) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- 8  t8 = vprordZMM 24 t7 t7 = .here
  (.var (.mk (.vprordZMM 24) rfl
          (.cons .here .nil))
  -- 9  t9 = t3 + t8         t3 depth (9-1)-3 = 5 = .there^5 .here ; t8 = .here
  (.var (.mk (.vpackZMMd .add) rfl
          (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  -- 10 t10 = t5 ^ t9        t5 depth (10-1)-5 = 4 = .there^4 .here ; t9 = .here
  (.var (.mk (.vpackZMMd .xor) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)))
  -- 11 t11 = vprordZMM 25 t10 t10 = .here
  (.var (.mk (.vprordZMM 25) rfl
          (.cons .here .nil))
  k)))))))))))

/-- Quarter-round program returning `a' = t6`. In the final context the bindings
    are `[t11,…,t0]`, so `t6` is index `11 - 6 = 5` from the front. -/
def qrComA : Com jasminDialect qrCtx r512 :=
  qrBody (.ret (.there (.there (.there (.there (.there .here))))))

/-- Quarter-round program returning `b' = t11` (the front-most binding). -/
def qrComB : Com jasminDialect qrCtx r512 :=
  qrBody (.ret .here)

/-- Quarter-round program returning `c' = t9` (index `11 - 9 = 2`). -/
def qrComC : Com jasminDialect qrCtx r512 :=
  qrBody (.ret (.there (.there .here)))

/-- Quarter-round program returning `d' = t8` (index `11 - 8 = 3`). -/
def qrComD : Com jasminDialect qrCtx r512 :=
  qrBody (.ret (.there (.there (.there .here))))

/-! ## 4. Denotation characterization

Each program denotes to its component of the pure spec `qrSpecZ`, the RFC-8439
§2.1 quarter-round written directly in the verified-dialect dword waist
functions `zmmPackD` / `zmmRorD`. -/

/-- Abbreviation for the 4-register valuation. -/
abbrev qrVal (a b c d : BitVec 512) : Ctxt.Valuation qrCtx :=
  .cons a (.cons b (.cons c (.cons d .nil)))

/-- The 12 peel + lookup-resolve steps shared by the four `qrCom{A,B,C,D}` denote
    lemmas: unfold `qrBody`, peel each binding with its `denote_var_*` step lemma
    (each a `rfl`), then resolve the de-Bruijn lookups with the `lookup_*` simp
    lemmas, leaving the continuation `.ret v` over the fully extended valuation. -/
macro "peel_qr" : tactic =>
  `(tactic|
    (unfold qrBody;
     rw [denote_var_vpackZMMd, denote_var_vpackZMMd, denote_var_vprordZMM,
       denote_var_vpackZMMd, denote_var_vpackZMMd, denote_var_vprordZMM,
       denote_var_vpackZMMd, denote_var_vpackZMMd, denote_var_vprordZMM,
       denote_var_vpackZMMd, denote_var_vpackZMMd, denote_var_vprordZMM];
     simp only [Com.denote, lookup_here_extend, lookup_there_extend,
       lookup_here_cons, lookup_there_cons]))

theorem qrComA_denote (a b c d : BitVec 512) :
    qrComA.denote (qrVal a b c d) = (qrSpecZ a b c d).1 := by
  rw [qrComA]; peel_qr; rfl

theorem qrComB_denote (a b c d : BitVec 512) :
    qrComB.denote (qrVal a b c d) = (qrSpecZ a b c d).2.1 := by
  rw [qrComB]; peel_qr; rfl

theorem qrComC_denote (a b c d : BitVec 512) :
    qrComC.denote (qrVal a b c d) = (qrSpecZ a b c d).2.2.1 := by
  rw [qrComC]; peel_qr; rfl

theorem qrComD_denote (a b c d : BitVec 512) :
    qrComD.denote (qrVal a b c d) = (qrSpecZ a b c d).2.2.2 := by
  rw [qrComD]; peel_qr; rfl

/-- The four programs together compute the whole dword quarter-round: their
    denotations are exactly the four components of `qrSpecZ`. -/
theorem qrCom_realizes (a b c d : BitVec 512) :
    qrComA.denote (qrVal a b c d) = (qrSpecZ a b c d).1
      ∧ qrComB.denote (qrVal a b c d) = (qrSpecZ a b c d).2.1
      ∧ qrComC.denote (qrVal a b c d) = (qrSpecZ a b c d).2.2.1
      ∧ qrComD.denote (qrVal a b c d) = (qrSpecZ a b c d).2.2.2 :=
  ⟨qrComA_denote .., qrComB_denote .., qrComC_denote .., qrComD_denote ..⟩

/-! ## 5. RFC-8439 §2.1 single-quarter-round test vector (lane-0 cross-check)

RFC 8439 §2.1 gives a worked single quarter-round:
`a=0x11111111 b=0x01020304 c=0x9b8d6f43 d=0x01234567` ↦
`a=0xea2a92f4 b=0xcb1cf8ce c=0x4581472e d=0x5881c4bb`. We broadcast each input
word into lane 0 of a `reg 512` (the other lanes are zero, computed independently
per lane), denote the four programs, read lane 0, and check it equals the RFC
output — a real reference vector pinning the de-Bruijn wiring. -/

/-- Broadcast a `u32` into lane 0 of a `reg 512` (high lanes zero). -/
def lane0 (w : BitVec 32) : BitVec 512 := w.zeroExtend 512

/-- Read lane 0 (`u32`) of a `reg 512`. -/
def getLane0 (v : BitVec 512) : BitVec 32 := v.extractLsb' 0 32

-- RFC-8439 §2.1 inputs.
def rfcA : BitVec 32 := 0x11111111
def rfcB : BitVec 32 := 0x01020304
def rfcC : BitVec 32 := 0x9b8d6f43
def rfcD : BitVec 32 := 0x01234567

/-- Lane-0 output of the four programs on the RFC §2.1 input vector. -/
def rfcOut : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let V := qrVal (lane0 rfcA) (lane0 rfcB) (lane0 rfcC) (lane0 rfcD)
  ( getLane0 (qrComA.denote V)
  , getLane0 (qrComB.denote V)
  , getLane0 (qrComC.denote V)
  , getLane0 (qrComD.denote V) )

-- Expected RFC-8439 §2.1 single-quarter-round output
-- (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb in decimal).
/-- info: (3928658676#32, 3407673550#32, 1166100270#32, 1484899515#32) -/
#guard_msgs in
#eval rfcOut

/-- **RFC-8439 §2.1 lane-0 cross-check.** The four dword quarter-round programs,
    evaluated on the RFC §2.1 input vector and read at lane 0, equal the RFC §2.1
    reference output `(0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)`. This
    decides by `native_decide` over the concrete `BitVec` values, pinning the
    de-Bruijn wiring of `qrComA/B/C/D` to a real reference quarter-round. -/
theorem rfcOut_eq :
    rfcOut = (0xea2a92f4#32, 0xcb1cf8ce#32, 0x4581472e#32, 0x5881c4bb#32) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordCom
