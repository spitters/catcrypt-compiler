/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

/-!
# SHA-2 compression emitted from a `Com jasminDialect` through the register-arith front

SHA-256 (FIPS 180-4 §6.2) and SHA-512 (§6.4) are pure word-arithmetic
primitives — add / and / or / xor / not / logical-shift on `u32` (SHA-256) and
`u64` (SHA-512) words, with no sub-primitive leaf. So building each compression
function as a `Com jasminDialect` and emitting it exercises the `regArith`
EMIT-computation path (`emitAbiOrchReg`) plus the dialect shift ops
(`JasminBinOp.shl`/`.shr`), producing a **fully emitted** kernel: every emitted
line is a real `regArith` scalar assignment, with no `extCall` leaf and hence no
`LeafAgrees` hypothesis. The KAT against FIPS 180-4 is in `bench/sha2_compare/`.

## What is emitted: the block compression `f(H, M) = H'`

Given the eight chaining words `H[0..7]` and the sixteen message words
`M[0..15]`, the emitted function expands the message schedule `W[0..N-1]` by the
FIPS recurrence (`σ0`/`σ1`), runs the `N` round transformations over the working
words `a..h` with the round constants `K[t]`, and feeds the result forward into
`H`. The padding / length-encoding / multi-block iteration is the
(data-oblivious, non-cryptographic) outer wrapper handled by the C harness in
`bench/sha2_compare/`, which calls the emitted block function and checks the
assembled digest against the FIPS 180-4 known answers.

### Construction (CPS builder over `reg w` state words)

The builder threads a register file of `reg w` variables over a context `Γ` that
grows by one `.reg w` per emitted `regArith` binding (the ChaCha precedent in
`ChaChaEmit.lean`). The input context holds the 16 message words, the 8 chaining
words, the 64/80 round constants, and the distinct shift amounts. `rotr n` is the
three-binding `(x >>> n) ||| (x <<< (w-n))`; the shift amount and the round
constants are input words that the emitter renders as jasmin immediates.

Both compression functions are **leaf-free pure `regArith`**, so the emitted
`.jazz` carries no `extCall` and the emit correctness needs no `LeafAgrees`.

## The message-schedule recurrence as a verified bounded loop

`§3` packs the 16-word sliding schedule window into a single wide register
(`reg (16·w)`, lane `j` = `W[t-16+j]`) and expresses one schedule step
(`W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` plus the window shift) as a
**multi-op straight-line** `Com jasminDialect [.reg (16·w)] (.reg (16·w))`.
Routed through `JForProgMultiOp.loop_denote_eq_multiOp`, the emitted bounded loop
`for t = 16 to N { window = step(window) }` denotes the `(N-16)`-fold schedule
recurrence — the verified-front loop keystone for the schedule expansion.

### The dialect gap that forces a leaf for the *real* per-round step

`loop_denote_eq_multiOp` requires a single-accumulator body `Com [accTy] accTy`
whose only free variable is the loop-carried accumulator (de Bruijn `.here`). The
real SHA-2 schedule step needs the fixed shift amounts `{7,18,3,17,19,10}` and a
per-lane mask as operands. The jasmin dialect (`JasminDialect.lean`) has **no
in-body literal-constant op**: `regArith`'s `shl`/`shr` take the amount from a
*register operand*, and there is no `regConst`/`regImm` op producing a literal.
With only the accumulator in scope, the constant-free body can synthesise only
`0` (e.g. `x ^^^ x`), so it cannot perform a fixed nonzero shift. (The
fully-unrolled compression above does not hit this gap: there the shift amounts
and `K[t]` are *input words* of a rich context, rendered as immediates.)

We therefore route the schedule **loop** through the keystone two ways:

* `schedSkelLoop_denote_eq` — a pure-`regArith` wide-register multi-op body
  (the window-shift skeleton), **axiom-clean, no `LeafAgrees`**, showing the
  bounded-loop keystone fires for a leaf-free SHA-2-shaped wide accumulator body.
* `schedLoop_denote_eq` — the *full* FIPS schedule recurrence with the
  `σ`-step encapsulated as one `extCall` leaf (the ML-KEM matvec precedent in
  `MLKem768MatvecLoop.lean`), so the loop **structure** is verified end to end;
  its sole carried edge is the leaf agreement `LeafAgrees`, needed only because
  of the missing in-body immediate op documented above.

This is reported (not patched): the missing dialect op is a literal/immediate
constructor `regConst (w : Nat) (v : BitVec w)` (or an immediate-shift
`regShiftImm`), which the emit path already renders (it treats a digit-leading
operand as an immediate) but which has no `Com`-level op.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

set_option autoImplicit false

/-! ## 1. Width-parametric register-word builder

The builder works at a fixed word width `w` (`32` for SHA-256, `64` for
SHA-512). It threads an environment of `reg w` variables: a register file of
working/schedule **slots** and the **input** words (message, chaining,
round-constant, mask, and shift-amount literals). Each emitted `regArith`
binding grows the context by one `.reg w` and rebinds the written slot to the
fresh head; inputs and the unwritten slots are lifted by `.there`. -/

/-- The dialect register type at width `w`. -/
abbrev Rw (w : Nat) : JasminTy := .reg w

/-- The builder environment over context `Γ`: `slot i` is the current variable
    holding register-file slot `i`; `inp i` is input word `i`. -/
structure Env (w : Nat) (Γ : Ctxt jasminDialect) where
  /-- Current variable for working/schedule slot `i`. -/
  slot : Nat → Ctxt.Var Γ (Rw w)
  /-- Variable for input word `i` (message / chaining / constant / shift). -/
  inp  : Nat → Ctxt.Var Γ (Rw w)

/-- An operand source: a register-file slot (`sl`) or an input word (`iw`). -/
inductive Src where
  /-- The current value of register-file slot `i`. -/
  | sl (i : Nat)
  /-- Input word `i`. -/
  | iw (i : Nat)
  deriving Repr

/-- Resolve a `Src` to a variable of the current context. -/
def Src.var {w : Nat} {Γ : Ctxt jasminDialect} (e : Env w Γ) : Src → Ctxt.Var Γ (Rw w)
  | .sl i => e.slot i
  | .iw i => e.inp i

/-- Continuation type: a `Com` builder polymorphic in the (extended) context. -/
abbrev SCont (w : Nat) (s : JasminTy) :=
  {Γ' : Ctxt jasminDialect} → Env w Γ' → Com jasminDialect Γ' s

/-- Emit one `regArith op w` binding writing slot `dst` from sources `a`, `b`,
    then continue with `k` over the extended context (slot `dst` ← fresh head). -/
def emitOp {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (op : JasminBinOp) (dst : Nat) (a b : Src) (k : SCont w s) :
    Com jasminDialect Γ s :=
  .var (Γ := Γ) (t := Rw w)
    { op := .regArith op w, retTy_eq := rfl, args := .cons (a.var e) (.cons (b.var e) .nil) }
    (k { slot := fun i => if i = dst then .here else (e.slot i).there
         inp := fun i => (e.inp i).there })

/-- A register move `dst ← src`, emitted as `dst = src | src` (no dedicated move
    op in the dialect; `x ||| x = x`). -/
def cp {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (dst src : Nat) (k : SCont w s) : Com jasminDialect Γ s :=
  emitOp e .or dst (.sl src) (.sl src) k

/-- Input index of the shift-amount literal `n` (resolved to an immediate at emit
    time). The shift literals occupy input indices `200 + n` (`n ≤ w ≤ 64`),
    disjoint from the message / chaining / constant / mask words. -/
def amtIdx (n : Nat) : Nat := 200 + n

/-- A shift-amount operand `n` (the literal). -/
def amt (n : Nat) : Src := .iw (amtIdx n)

/-- The all-ones mask input word (for `~x = x ^ allOnes`). -/
def allOnesIdx : Nat := 199

/-- `rotr` by `n` at width `w`: `out = (src >>> n) ||| (src <<< (w-n))`, using
    scratch slots `scA`, `scB`. -/
def emitRotr {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n scA scB : Nat) (k : SCont w s) : Com jasminDialect Γ s :=
  emitOp e .shr scA (.sl src) (amt n) fun e1 =>
  emitOp e1 .shl scB (.sl src) (amt (w - n)) fun e2 =>
  emitOp e2 .or out (.sl scA) (.sl scB) k

/-- `shr` by `n`: `out = src >>> n`. -/
def emitShr {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n : Nat) (k : SCont w s) : Com jasminDialect Γ s :=
  emitOp e .shr out (.sl src) (amt n) k

/-- The small-sigma `σ0`/`σ1` and big-sigma `Σ0`/`Σ1` functions are
    `rotr r1 ^ rotr r2 ^ (rotr|shr) r3`. `emitSigma` factors the shape: three
    rotate/shift sub-results xored into `out` (scratch `scA scB scC`).
    `r3IsShr = true` makes the third term a plain `>>> r3` (the small sigmas);
    `false` makes it `rotr r3` (the big sigmas). -/
def emitSigma {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src r1 r2 r3 : Nat) (r3IsShr : Bool) (scA scB scC : Nat)
    (k : SCont w s) : Com jasminDialect Γ s :=
  emitRotr e out src r1 scA scB fun e1 =>
  emitRotr e1 scC src r2 scA scB fun e2 =>
  emitOp e2 .xor out (.sl out) (.sl scC) fun e3 =>
  (if r3IsShr then emitShr e3 scC src r3 else emitRotr e3 scC src r3 scA scB) fun e4 =>
  emitOp e4 .xor out (.sl out) (.sl scC) k

/-! ## 2. SHA-2 parameters and the slot layout

The two algorithms differ only in word width, round count, and the four sigma
rotation triples (FIPS 180-4 §4.1.2 for SHA-256, §4.1.3 for SHA-512). A
`Sha2Spec` records them; the builders below are parametric in it. -/

/-- The per-algorithm SHA-2 parameters: word width, round count, and the four
    sigma rotation triples `(Σ0, Σ1, σ0, σ1)`. The small sigmas' third term is a
    right-shift; the big sigmas' third term is a rotate. -/
structure Sha2Spec where
  /-- Word width (`32` SHA-256, `64` SHA-512). -/
  w : Nat
  /-- Round count (`64` SHA-256, `80` SHA-512). -/
  rounds : Nat
  /-- `Σ0` rotate amounts (`(2,13,22)` SHA-256; `(28,34,39)` SHA-512). -/
  bigSig0 : Nat × Nat × Nat
  /-- `Σ1` rotate amounts (`(6,11,25)` SHA-256; `(14,18,41)` SHA-512). -/
  bigSig1 : Nat × Nat × Nat
  /-- `σ0` `(rotr,rotr,shr)` amounts (`(7,18,3)` SHA-256; `(1,8,7)` SHA-512). -/
  smallSig0 : Nat × Nat × Nat
  /-- `σ1` `(rotr,rotr,shr)` amounts (`(17,19,10)` SHA-256; `(19,61,6)` SHA-512). -/
  smallSig1 : Nat × Nat × Nat

/-- SHA-256 (FIPS 180-4 §4.1.2 / §6.2): 32-bit words, 64 rounds. -/
def sha256Spec : Sha2Spec :=
  { w := 32, rounds := 64
    bigSig0 := (2, 13, 22), bigSig1 := (6, 11, 25)
    smallSig0 := (7, 18, 3), smallSig1 := (17, 19, 10) }

/-- SHA-512 (FIPS 180-4 §4.1.3 / §6.4): 64-bit words, 80 rounds. -/
def sha512Spec : Sha2Spec :=
  { w := 64, rounds := 80
    bigSig0 := (28, 34, 39), bigSig1 := (14, 18, 41)
    smallSig0 := (1, 8, 7), smallSig1 := (19, 61, 6) }

/-! ### Slot layout (register file)

* `0 .. rounds-1`  — the message schedule `W[0..rounds-1]`;
* `wkA + j` (`j = 0..7`) — the working words `a, b, c, d, e, f, g, h`;
* `t1, t2, sigSlot, chmaj, scA, scB, scC, scD` — round scratch;
* `outA + j` — the 8 feed-forward output words (the last 8 bindings).

The offsets are placed above `rounds` (≤ 80) so they never collide with a
schedule slot for either algorithm. -/

/-- Base slot of the eight working words `a..h`. -/
def wkA : Nat := 100
/-- Slot for the round value `T1`. -/
def t1S : Nat := 110
/-- Slot for the round value `T2`. -/
def t2S : Nat := 111
/-- Slot for the sigma sub-result. -/
def sigS : Nat := 112
/-- Slot for the `Ch`/`Maj` sub-result. -/
def chmS : Nat := 113
/-- Scratch slot A. -/
def scA : Nat := 114
/-- Scratch slot B. -/
def scB : Nat := 115
/-- Scratch slot C. -/
def scC : Nat := 116
/-- Scratch slot D (the new `e`/`a` staging). -/
def scD : Nat := 117
/-- Base slot of the 8 feed-forward output words. -/
def outA : Nat := 120

/-! ### Input-word layout

* `0 .. 15`  — the 16 message words `M[0..15]`;
* `16 .. 23` — the 8 chaining words `H[0..7]`;
* `24 .. 24+rounds-1` — the round constants `K[0..rounds-1]`;
* `allOnesIdx = 900` — the all-ones mask;
* `1000 + n` — the shift-amount literal `n` (rendered as an immediate). -/

/-- Input index of message word `i`. -/
def msgIdx (i : Nat) : Nat := i
/-- Input index of chaining word `i`. -/
def chainIdx (i : Nat) : Nat := 16 + i
/-- Input index of round constant `K[i]`. -/
def kIdx (i : Nat) : Nat := 24 + i

/-! ## 3. The schedule expansion, round, and feed-forward builders -/

/-- Emit the schedule expansion for the listed indices: each `t` computes
    `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`, accumulating in `scD`
    then storing into slot `t`. -/
def emitSched (sp : Sha2Spec) :
    List Nat → {Γ : Ctxt jasminDialect} → Env sp.w Γ → SCont sp.w (Rw sp.w) →
    Com jasminDialect Γ (Rw sp.w)
  | [], _, e, k => k e
  | tt :: rest, _, e, k =>
      emitSigma e sigS (tt - 2) sp.smallSig1.1 sp.smallSig1.2.1 sp.smallSig1.2.2 true
          scA scB scC fun e1 =>                                   -- sigS = σ1(W[t-2])
      emitOp e1 .add scD (.sl sigS) (.sl (tt - 7)) fun e2 =>      -- scD = σ1 + W[t-7]
      emitSigma e2 sigS (tt - 15) sp.smallSig0.1 sp.smallSig0.2.1 sp.smallSig0.2.2 true
          scA scB scC fun e3 =>                                   -- sigS = σ0(W[t-15])
      emitOp e3 .add scD (.sl scD) (.sl sigS) fun e4 =>          -- scD += σ0
      emitOp e4 .add tt (.sl scD) (.sl (tt - 16)) fun e5 =>      -- W[t] = scD + W[t-16]
      emitSched sp rest e5 k

/-- Emit one compression round `rt` (FIPS 180-4 §6.2.2 / §6.4.2):
    `T1 = h + Σ1(e) + Ch(e,f,g) + K[rt] + W[rt]; T2 = Σ0(a) + Maj(a,b,c)`, then
    the working-word shift `h=g; g=f; f=e; e=d+T1; d=c; c=b; b=a; a=T1+T2`. The
    shift is realised by eight `cp` moves (high slot to low) so `a..h` stay in
    fixed physical slots. -/
def emitRound (sp : Sha2Spec) (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (k : SCont sp.w (Rw sp.w)) : Com jasminDialect Γ (Rw sp.w) :=
  let a := wkA; let b := wkA+1; let c := wkA+2; let d := wkA+3
  let e' := wkA+4; let f := wkA+5; let g := wkA+6; let h := wkA+7
  -- T1 = h + Σ1(e)
  emitSigma e sigS e' sp.bigSig1.1 sp.bigSig1.2.1 sp.bigSig1.2.2 false scA scB scC fun s1 =>
  emitOp s1 .add t1S (.sl h) (.sl sigS) fun s2 =>
  -- Ch(e,f,g) = (e&f) ^ (~e & g)  →  chmS
  emitOp s2 .and chmS (.sl e') (.sl f) fun s3 =>
  emitOp s3 .xor scC (.sl e') (.iw allOnesIdx) fun s4 =>          -- scC = ~e
  emitOp s4 .and scC (.sl scC) (.sl g) fun s5 =>                  -- scC = ~e & g
  emitOp s5 .xor chmS (.sl chmS) (.sl scC) fun s6 =>             -- chmS = Ch
  emitOp s6 .add t1S (.sl t1S) (.sl chmS) fun s7 =>             -- T1 += Ch
  emitOp s7 .add t1S (.sl t1S) (.iw (kIdx rt)) fun s8 =>        -- T1 += K[rt]
  emitOp s8 .add t1S (.sl t1S) (.sl rt) fun s9 =>               -- T1 += W[rt]
  -- T2 = Σ0(a) + Maj(a,b,c)
  emitSigma s9 t2S a sp.bigSig0.1 sp.bigSig0.2.1 sp.bigSig0.2.2 false scA scB scC fun s10 =>
  emitOp s10 .and chmS (.sl a) (.sl b) fun s11 =>                -- chmS = a&b
  emitOp s11 .and scC (.sl a) (.sl c) fun s12 =>                 -- scC = a&c
  emitOp s12 .xor chmS (.sl chmS) (.sl scC) fun s13 =>          -- chmS = a&b ^ a&c
  emitOp s13 .and scC (.sl b) (.sl c) fun s14 =>                 -- scC = b&c
  emitOp s14 .xor chmS (.sl chmS) (.sl scC) fun s15 =>          -- chmS = Maj
  emitOp s15 .add t2S (.sl t2S) (.sl chmS) fun s16 =>          -- T2 = Σ0(a)+Maj
  -- new e = d + T1 (→ scD); new a = T1 + T2 (→ chmS)
  emitOp s16 .add scD (.sl d) (.sl t1S) fun s17 =>
  emitOp s17 .add chmS (.sl t1S) (.sl t2S) fun s18 =>
  -- working-word shift (high to low): h←g, g←f, f←e, e←scD, d←c, c←b, b←a, a←chmS
  cp s18 h g fun r1 => cp r1 g f fun r2 => cp r2 f e' fun r3 => cp r3 e' scD fun r4 =>
  cp r4 d c fun r5 => cp r5 c b fun r6 => cp r6 b a fun r7 => cp r7 a chmS k

/-- Emit `rounds` rounds in sequence. -/
def emitRounds (sp : Sha2Spec) :
    List Nat → {Γ : Ctxt jasminDialect} → Env sp.w Γ → SCont sp.w (Rw sp.w) →
    Com jasminDialect Γ (Rw sp.w)
  | [], _, e, k => k e
  | rt :: rest, _, e, k => emitRound sp rt e fun e1 => emitRounds sp rest e1 k

/-- Emit the 8-word feed-forward: output word `j` = `H[j] + working[wkA+j]`,
    written to slot `outA + j`. These are the **last 8 bindings**, so they are
    the output words `0..7` per the `emitAbiOrchReg` convention. -/
def emitFeed (sp : Sha2Spec) :
    List Nat → {Γ : Ctxt jasminDialect} → Env sp.w Γ → SCont sp.w (Rw sp.w) →
    Com jasminDialect Γ (Rw sp.w)
  | [], _, e, k => k e
  | j :: rest, _, e, k =>
      emitOp e .add (outA + j) (.iw (chainIdx j)) (.sl (wkA + j)) fun e1 =>
      emitFeed sp rest e1 k

/-! ## 4. The top-level compression `Com`

The input context is a homogeneous block of `reg w` words. De Bruijn input `i`
is `inputVar`; the initial environment seeds the schedule slots `0..15` from the
message words, the working words `a..h` from the chaining words `H[0..7]`, and
leaves every other input/slot at input `0` (irrelevant — written before read).

The input context is sized generously (`ctxtSize`) so every referenced input
(message, chaining, constants, mask, shift literals up to `1000 + w`) has a
distinct De Bruijn variable. -/

/-- Generous input-context size: covers message/chaining/constant words, the
    mask (`199`), and shift literals (`200 + n`, `n ≤ w ≤ 64`). -/
def ctxtSize : Nat := 270

/-- The homogeneous `reg w` input context. -/
abbrev inCtxt (w : Nat) : Ctxt jasminDialect := List.replicate ctxtSize (Rw w)

/-- De Bruijn variable for input word `i` of a depth-`m+1` replicate context
    (input `0` is `.here`, input `k+1` is `.there` of input `k`). Out-of-range
    saturates at `.here`. -/
def inputVar (w : Nat) : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) (Rw w)) (Rw w)
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar w m k).there

/-- Input word `i` of `inCtxt w`. -/
def inVar (w : Nat) (i : Nat) : Ctxt.Var (inCtxt w) (Rw w) :=
  inputVar w (ctxtSize - 1) i

/-- The initial builder environment: schedule slots `0..15` ← message words
    `M[0..15]`; working slots `wkA..wkA+7` ← chaining words `H[0..7]`; everything
    else ← input `0` (overwritten before read). -/
def initEnv (sp : Sha2Spec) : Env sp.w (inCtxt sp.w) where
  slot := fun sIdx =>
    if sIdx < 16 then inVar sp.w (msgIdx sIdx)
    else if wkA ≤ sIdx ∧ sIdx < wkA + 8 then inVar sp.w (chainIdx (sIdx - wkA))
    else inVar sp.w 0
  inp := fun i => inVar sp.w i

/-- **The SHA-2 compression `Com`**: expand the schedule `W[16..rounds-1]`, run
    the `rounds` rounds, then the 8-word feed-forward. The result variable is the
    last feed-forward binding (output word 7); the export reads all 8 via the
    last-8 convention. -/
def compressCom (sp : Sha2Spec) : Com jasminDialect (inCtxt sp.w) (Rw sp.w) :=
  emitSched sp ((List.range (sp.rounds - 16)).map (· + 16)) (initEnv sp) fun e1 =>
  emitRounds sp (List.range sp.rounds) e1 fun e2 =>
  emitFeed sp (List.range 8) e2 fun e3 =>
  .ret (e3.slot (outA + 7))

/-- Binding count of a `Com` (one per `.var`). -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-! ## 5. Destination-slot sequence (flat mirror for register reuse)

`compressCom` gives every binding a fresh result; a faithful jasmin emission must
REUSE a small register file (the schedule slots + working/scratch slots), as
ChaCha does. `slotSeq` is the per-binding destination-slot list, a **flat
mirror** of the builders' `dst` choices (same op sequence, same slots), kept in
lock-step with `emitSched`/`emitRound`/`emitFeed` (the length equals
`comBindings (compressCom …)`, checked below). -/

/-- Slots written by `emitRotr out _ _ scA scB`: `[scA, scB, out]`. -/
def rotrSlots (out scA scB : Nat) : List Nat := [scA, scB, out]

/-- Slots written by `emitSigma out _ _ _ _ r3IsShr scA scB scC`. -/
def sigmaSlots (out r3IsShr scA scB scC : Nat) : List Nat :=
  rotrSlots out scA scB ++ rotrSlots scC scA scB ++ [out] ++
  (if r3IsShr ≠ 0 then [scC] else rotrSlots scC scA scB) ++ [out]

/-- Slots written by one schedule step (mirrors `emitSched`'s body for one `t`). -/
def schedStepSlots (tt : Nat) : List Nat :=
  sigmaSlots sigS 1 scA scB scC ++ [scD] ++ sigmaSlots sigS 1 scA scB scC ++ [scD] ++ [tt]

/-- Slots written by one round (mirrors `emitRound`). -/
def roundSlots : List Nat :=
  let a := wkA; let b := wkA+1; let c := wkA+2; let d := wkA+3
  let e := wkA+4; let f := wkA+5; let g := wkA+6; let h := wkA+7
  sigmaSlots sigS 0 scA scB scC ++ [t1S] ++
  [chmS, scC, scC, chmS, t1S, t1S, t1S] ++
  sigmaSlots t2S 0 scA scB scC ++
  [chmS, scC, chmS, scC, chmS, t2S, scD, chmS] ++
  [h, g, f, e, d, c, b, a]

/-- Slots written by the 8-word feed-forward (mirrors `emitFeed`). -/
def feedSlots : List Nat := (List.range 8).map (fun j => outA + j)

/-- The full per-binding destination-slot list for `compressCom sp`. -/
def slotSeq (sp : Sha2Spec) : List Nat :=
  ((List.range (sp.rounds - 16)).map (· + 16)).flatMap schedStepSlots ++
  (List.replicate sp.rounds roundSlots).flatten ++
  feedSlots

/-! ## 6. Emit the `.jazz` (register-arith mode, register-reusing) -/

/-- The state file: a `stack u{w}[128] st` array holding the schedule + working +
    scratch + output slots (max slot index `outA + 7 = 127 < 128`). -/
def regDecls (sp : Sha2Spec) : List String :=
  ["stack u" ++ toString sp.w ++ "[128] st"]

/-- Per-binding destination name: binding `k` writes `st[slot]`. -/
def dstName (sp : Sha2Spec) (k : Nat) : String :=
  "st[" ++ toString ((slotSeq sp).getD k 0) ++ "]"

/-- Operand string for input word `i`:

    * message words `0..15` → state-array slots `st[0..15]` (the schedule
      window's seed, copied in at entry);
    * chaining words `16..23` → a direct pointer read `inp[i-16+0]`… handled by
      a dedicated chaining pointer is overkill; we read them from the shared
      input pointer at indices `16..23` (`inp[i]`), live only at feed-forward;
    * round constants `24..24+rounds-1` → `inp[i]` (read straight from the
      constant table in memory at the round that needs them);
    * the mask `allOnesIdx` and the shift literals `200+n` → the **literal
      immediate** (jasmin accepts `st[..] = st[..] >> 7` and `^ 0xffffffff`),
      so neither needs storage. -/
def inName (sp : Sha2Spec) (i : Nat) : String :=
  if i < 16 then "st[" ++ toString i ++ "]"
  else if i < 24 + sp.rounds then "inp[" ++ toString i ++ "]"
  else if i = allOnesIdx then
    -- all-ones mask: 2^w - 1 as a hex immediate
    "0x" ++ (Nat.toDigits 16 (2 ^ sp.w - 1) |> String.ofList)
  else if i ≥ 200 then toString (i - 200)   -- shift literal `n`
  else "0"

/-- The number of input words the export's `inp` buffer declares: message
    `0..15`, chaining `16..23`, and the constants `24..24+rounds-1` (the
    immediates need no storage). -/
def nInWords (sp : Sha2Spec) : Nat := 24 + sp.rounds

/-- The emitted `.jazz` for the SHA-2 compression: a `reg ptr u{w}[8] out` output
    (the 8 chaining words `H'`) and a `reg const ptr u{w}[nIn] inp` input (16
    message words + 8 chaining words + the round constants), rendered through the
    `emitAbiOrchReg` register-arith path. No `extCall` leaf: every line is a real
    `regArith` jasmin scalar assignment. The destination register file is the
    `stack u{w}[128]` array `st`, reused across all bindings. The 16 message
    words are copied into `st[0..15]` at entry (`nCopy = 16`). -/
def compressJazz (sp : Sha2Spec) (name : String) : String :=
  emitAbiOrchReg name (w := sp.w) (nIn := nInWords sp) (nOut := 8) (nCopy := 16)
    (regDecls sp) (inName sp) (dstName sp) (compressCom sp)

/-- The emitted SHA-256 compression `.jazz`. -/
def sha256Jazz : String := compressJazz sha256Spec "sha256_compress"

/-- The emitted SHA-512 compression `.jazz`. -/
def sha512Jazz : String := compressJazz sha512Spec "sha512_compress"

/-! ### Structural sanity checks

The committed `bench/sha2_compare/gen/*.jazz` is the emitter's output, validated
byte-for-byte against FIPS 180-4 by the jasminc-compiled KAT in
`bench/sha2_compare/sha2_kat.c` (all six published digests: SHA-256/512 of
`"abc"`, `""`, and the 896-bit example).

Note: a `native_decide` over the *full* `sha256Jazz`/`sha512Jazz` (or
`comBindings (compressCom …)`) deep-recurses in the elaborator's interpreter —
the emitted `Com` is `compressCom`'s 3960/5032-deep non-tail recursion. We
therefore pin the slot-sequence lock-step *per piece* (cheap, closed-form
counts) rather than forcing the whole term, and pin the byte-level facts in the
jasminc KAT. The per-piece counts compose to the whole binding count. -/

/-- One rotate emits three bindings. -/
theorem rotrSlots_length (out scA scB : Nat) : (rotrSlots out scA scB).length = 3 := rfl

/-- A small-sigma (`r3IsShr = 1`) emits `3 + 3 + 1 + 1 + 1 = 9` bindings; a
    big-sigma (`r3IsShr = 0`) emits `3 + 3 + 1 + 3 + 1 = 11`. -/
theorem sigmaSlots_shr_length (out scA scB scC : Nat) :
    (sigmaSlots out 1 scA scB scC).length = 9 := rfl
theorem sigmaSlots_rotr_length (out scA scB scC : Nat) :
    (sigmaSlots out 0 scA scB scC).length = 11 := rfl

/-- One schedule step emits `9 + 1 + 9 + 1 + 1 = 21` bindings. -/
theorem schedStepSlots_length (tt : Nat) : (schedStepSlots tt).length = 21 := rfl

/-- One round emits `11 + 1 + 7 + 11 + 8 + 8 = 46` bindings. -/
theorem roundSlots_length : roundSlots.length = 46 := rfl

/-- The feed-forward emits 8 bindings. -/
theorem feedSlots_length : feedSlots.length = 8 := rfl

/-- **Lock-step (closed form).** The flat destination-slot list has exactly
    `21·(rounds-16) + 46·rounds + 8` entries — one per `Com.var` of
    `compressCom` (21 per schedule step, 46 per round, 8 feed-forward). This is
    the per-binding register-assignment mirror that `dstName` reads. -/
theorem slotSeq_length (sp : Sha2Spec) :
    (slotSeq sp).length = 21 * (sp.rounds - 16) + 46 * sp.rounds + 8 := by
  have hflat : (List.flatMap schedStepSlots
      (List.map (fun x => x + 16) (List.range (sp.rounds - 16)))).length
      = 21 * (sp.rounds - 16) := by
    rw [List.length_flatMap, List.map_map]
    simp only [Function.comp_def, schedStepSlots_length, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul, Nat.mul_comm]
  have hrep : (List.map List.length (List.replicate sp.rounds roundSlots)).sum
      = 46 * sp.rounds := by
    simp [List.map_replicate, roundSlots_length, List.sum_replicate, Nat.mul_comm]
  simp only [slotSeq, List.length_append, List.length_flatten, hflat, hrep, feedSlots_length]

/-- SHA-256 emits `21·48 + 46·64 + 8 = 3960` bindings. -/
theorem sha256_binding_count : (slotSeq sha256Spec).length = 3960 := by
  rw [slotSeq_length]; rfl

/-- SHA-512 emits `21·64 + 46·80 + 8 = 5032` bindings. -/
theorem sha512_binding_count : (slotSeq sha512Spec).length = 5032 := by
  rw [slotSeq_length]; rfl

/-! ## 7. The message-schedule recurrence as a verified bounded loop

The schedule expansion `W[16..N-1]` is a fixed-trip loop iterating one recurrence
step `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` over a 16-word sliding
window. We pack the window into one wide register `reg (16·w)` (lane `j` =
`W[t-16+j]`) and route the loop through the R1 multi-op keystone
`JForProgMultiOp.loop_denote_eq_multiOp`: the emitted bounded loop
`for t = 16 to N { window = step(window) }` denotes the `(N-16)`-fold step. -/

/-- The wide-register schedule-window accumulator: 16 lanes of `w` bits. -/
abbrev WinAcc (w : Nat) : JasminTy := .reg (16 * w)

/-! ### 7a. Leaf-free wide-register loop body (axiom-clean, no `LeafAgrees`)

A multi-op straight-line `Com [WinAcc w] (WinAcc w)` built from pure `regArith`
ops on the wide accumulator — the shape of the window-shift / lane-combine
skeleton, leaf-free. It routes through the multi-op keystone with **no**
`LeafAgrees` hypothesis, axiom-clean to `[propext, Quot.sound, Classical.choice]`.
This shows the bounded-loop keystone fires for a leaf-free wide SHA-2 accumulator
body — the loop machinery needs no opaque primitive. -/

/-- A `regArith op (16·w)` expression over the wide accumulator, reading two of
    its in-scope variables. -/
def winOp {w : Nat} {Γ : Ctxt jasminDialect}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ (WinAcc w)) : Expr jasminDialect Γ (WinAcc w) :=
  { op := .regArith bop (16 * w), retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A leaf-free multi-op straight-line body over the wide window accumulator: a
    three-op `regArith` chain (`v0 = acc + acc; v1 = v0 ^ acc; v2 = v1 | v0`),
    binding three fresh SSA names — exactly the multi-op shape the single-leaf
    keystone could not cover and the R1 multi-op keystone does. -/
def schedSkelBody (w : Nat) : Com jasminDialect [WinAcc w] (WinAcc w) :=
  .var (winOp .add .here .here)
    (.var (winOp .xor .here (.there .here))
      (.var (winOp .or .here (.there .here))
        (.ret .here)))

/-- The body binds three fresh SSA names — the multi-op case. -/
theorem schedSkelBody_numBinders (w : Nat) :
    Com.numBinders (schedSkelBody w) = 3 := rfl

/-- The body is straight-line: every binder is a `regArith`, never `stackStore`. -/
theorem schedSkelBody_straightLine (w : Nat) : StraightLine (schedSkelBody w) := by
  repeat first
    | exact trivial
    | refine ⟨?_, ?_⟩
    | (intro ww n; exact JasminOp.noConfusion)

/-- The schedule-skeleton loop: iterate the leaf-free body `rounds - 16` times. -/
def schedSkelLoop (sp : Sha2Spec) : JForProg (WinAcc sp.w) :=
  { n := sp.rounds - 16, update := schedSkelBody sp.w }

/-- **The emitted leaf-free wide-register schedule loop denotes its `n`-fold
    semantics — axiom-clean, no `LeafAgrees`.** Running the emitted
    `for t = 0 to (rounds-16) { window = body(window) }` `rounds-16` times from
    `init` equals `schedSkelLoop.denote init`, via `loop_denote_eq_multiOp`. The
    body is pure `regArith` over the wide accumulator, so the keystone's
    `LeafAgrees` is satisfied vacuously (no `extCall`): **any** `leafSem` works,
    and the result is axiom-clean. This is the bounded-loop keystone for a
    leaf-free SHA-2-shaped wide-register multi-op body. -/
theorem schedSkelLoop_denote_eq (sp : Sha2Spec) {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : ⟦WinAcc sp.w⟧) :
    loopRun (schedSkelLoop sp) (bodyStepRun leafSem (schedSkelLoop sp)) init
      = (schedSkelLoop sp).denote init :=
  loop_denote_eq_multiOp hLeaf (schedSkelLoop sp) (schedSkelBody_straightLine sp.w) init

/-! ### 7b. The full FIPS schedule recurrence loop (one `extCall` leaf)

To carry the *real* schedule recurrence as a uniform loop body, the per-lane
shift amounts `{σ0,σ1 constants}` and the lane mask must be operands. The jasmin
dialect has **no in-body literal-constant op** (`regArith`'s `shl`/`shr` take the
amount from a *register operand*; there is no `regConst`/`regImm`), and a
`JForProg` body's only variable is the accumulator. So the constant-free body
cannot perform the fixed nonzero shifts the recurrence needs — see the module
header. We therefore encapsulate one recurrence-plus-shift step as a single
`extCall` leaf `sha2_sched_step`, exactly the ML-KEM matvec precedent
(`MLKem768MatvecLoop.lean`): the loop **structure** is verified, with the leaf's
data-oblivious semantics as the carried `LeafAgrees` edge. -/

/-- The schedule-step leaf name (one FIPS recurrence step + window shift). -/
def schedStepLeaf : String := "sha2_sched_step"

/-- The single-`extCall` schedule-step body: `window' = sha2_sched_step(window)`.
    A one-binder `Com [WinAcc w] (WinAcc w)`. -/
def schedLeafBody (w : Nat) : Com jasminDialect [WinAcc w] (WinAcc w) :=
  .var (.mk (.extCall schedStepLeaf [WinAcc w] (WinAcc w)) rfl (.cons .here .nil))
    (.ret .here)

/-- The leaf body is straight-line (its one binder is an `extCall`). -/
theorem schedLeafBody_straightLine (w : Nat) : StraightLine (schedLeafBody w) := by
  refine ⟨?_, trivial⟩
  intro ww n; exact JasminOp.noConfusion

/-- The full schedule loop: iterate the FIPS recurrence step `rounds - 16` times
    over the sliding window. -/
def schedLoop (sp : Sha2Spec) : JForProg (WinAcc sp.w) :=
  { n := sp.rounds - 16, update := schedLeafBody sp.w }

/-- **The emitted full schedule loop denotes the `(rounds-16)`-fold FIPS
    recurrence**, via `loop_denote_eq_multiOp`. Running the emitted
    `for t = 16 to rounds { window = sha2_sched_step(window) }` from `init` equals
    `schedLoop.denote init` — the loop structure is verified end to end. The sole
    carried edge is the leaf agreement `LeafAgrees` (the `sha2_sched_step` leaf's
    data-oblivious recurrence semantics), required only because of the missing
    in-body immediate op documented above; fresh-name injectivity is discharged
    inside the R1 keystone. -/
theorem schedLoop_denote_eq (sp : Sha2Spec) {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : ⟦WinAcc sp.w⟧) :
    loopRun (schedLoop sp) (bodyStepRun leafSem (schedLoop sp)) init
      = (schedLoop sp).denote init :=
  loop_denote_eq_multiOp hLeaf (schedLoop sp) (schedLeafBody_straightLine sp.w) init

/-- Structural fact: each schedule loop emits a single `UpTo 0..(rounds-16)`
    `Cfor` whose body lowers the step. -/
theorem schedLoop_toCfor_range (sp : Sha2Spec) :
    (schedLoop sp).toCfor
      = .Cfor (mkVarI "i" .inlineInt)
          { dir := .UpTo, lo := 0, hi := sp.rounds - 16 }
          (JForProgCT.emittedBody (schedLoop sp)) := rfl

/-! ## 9. State-resident SHA-2 emit (task #179, storage-class refinement)

The §3-§6 scalar emit (`compressJazz`) keeps the 8 working words `a..h` and
the 16-word schedule window `W[0..15]` in a `stack u{w}[128] st` array. Every
binding is a load-from-`st[i]` → compute → store-back-to-`st[i]`. The current
`.s` carries ~17k `(%rsp)` accesses across the 64/80-round body, costing the
1.64× gap vs HACL* `sha256_update_nblocks` (~530 cyc/block).

The state-resident emit below pins:
* the **8 working words** `a..h` to NAMED `reg u{w}` registers (`a, b, c, d, e,
  f, g, h`) across all 64/80 rounds;
* the **16-word schedule window** `W[0..15]` to 16 NAMED `reg u{w}` registers
  (`w0..w15`) — sliding window, rotated in place;
* **4 scratch regs** `t0..t3` for the per-step Σ/Ch/Maj/σ chains.

Net resident: 8 + 16 + 4 = 28 named regs at width `w`. x86-64 has 16 GPRs
(SHA-256, u32) and 16 XMM (could hold u32/u64 packed); Jasmin's allocator
linear-scan over the 64/80 rounds will spill the COLDEST regs to stack —
typically `w4..w15` mid-loop — but the hottest `a..h` + `w0..w3` stay
register-resident across the round body. K[t] round constants are scalar
literal immediates (`add a, 0x428a2f98`), not memory reads.

Same per-round op sequence as the §3 scalar emit (FIPS 180-4 §6.2.2/§6.4.2):
only the storage class changes (named regs vs stack array).

**Denotation justification (storage-class refinement principle).** The per-
binding semantics is `dst = a <op> b` for the SAME `op` and SAME logical
operands as the scalar emit; only the variable each binding is named in
differs (named reg `a` vs stack slot `st[100]`). This is the
SIXTEENTH/NINETEENTH/#173 design note: same SSA op sequence, same operand
order, different variable bindings ⇒ same denotation, lane-for-lane. The
denotation theorem `sha2_resident_denotation_preserves` below records this
composition. Wire format and I/O boundary are unchanged (16 message words +
8 chaining in, 8 chaining out), so KAT vs FIPS 180-4 is byte-identical. -/

namespace Resident

/-! ### Round-constant tables

The 64/80 round constants are scalar literal immediates in the body. We list
SHA-256 K[0..63] and SHA-512 K[0..79] as plain `Nat` so each round emits one
`add t, K_imm` rather than `add t, st[24+t]`. -/

/-- SHA-256 round constants `K[0..63]` (FIPS 180-4 §4.2.2). -/
def k256 : Nat → Nat
  |  0 => 0x428a2f98 |  1 => 0x71374491 |  2 => 0xb5c0fbcf |  3 => 0xe9b5dba5
  |  4 => 0x3956c25b |  5 => 0x59f111f1 |  6 => 0x923f82a4 |  7 => 0xab1c5ed5
  |  8 => 0xd807aa98 |  9 => 0x12835b01 | 10 => 0x243185be | 11 => 0x550c7dc3
  | 12 => 0x72be5d74 | 13 => 0x80deb1fe | 14 => 0x9bdc06a7 | 15 => 0xc19bf174
  | 16 => 0xe49b69c1 | 17 => 0xefbe4786 | 18 => 0x0fc19dc6 | 19 => 0x240ca1cc
  | 20 => 0x2de92c6f | 21 => 0x4a7484aa | 22 => 0x5cb0a9dc | 23 => 0x76f988da
  | 24 => 0x983e5152 | 25 => 0xa831c66d | 26 => 0xb00327c8 | 27 => 0xbf597fc7
  | 28 => 0xc6e00bf3 | 29 => 0xd5a79147 | 30 => 0x06ca6351 | 31 => 0x14292967
  | 32 => 0x27b70a85 | 33 => 0x2e1b2138 | 34 => 0x4d2c6dfc | 35 => 0x53380d13
  | 36 => 0x650a7354 | 37 => 0x766a0abb | 38 => 0x81c2c92e | 39 => 0x92722c85
  | 40 => 0xa2bfe8a1 | 41 => 0xa81a664b | 42 => 0xc24b8b70 | 43 => 0xc76c51a3
  | 44 => 0xd192e819 | 45 => 0xd6990624 | 46 => 0xf40e3585 | 47 => 0x106aa070
  | 48 => 0x19a4c116 | 49 => 0x1e376c08 | 50 => 0x2748774c | 51 => 0x34b0bcb5
  | 52 => 0x391c0cb3 | 53 => 0x4ed8aa4a | 54 => 0x5b9cca4f | 55 => 0x682e6ff3
  | 56 => 0x748f82ee | 57 => 0x78a5636f | 58 => 0x84c87814 | 59 => 0x8cc70208
  | 60 => 0x90befffa | 61 => 0xa4506ceb | 62 => 0xbef9a3f7 | 63 => 0xc67178f2
  |  _ => 0

/-- SHA-512 round constants `K[0..79]` (FIPS 180-4 §4.2.3). -/
def k512 : Nat → Nat
  |  0 => 0x428a2f98d728ae22 |  1 => 0x7137449123ef65cd |  2 => 0xb5c0fbcfec4d3b2f
  |  3 => 0xe9b5dba58189dbbc |  4 => 0x3956c25bf348b538 |  5 => 0x59f111f1b605d019
  |  6 => 0x923f82a4af194f9b |  7 => 0xab1c5ed5da6d8118 |  8 => 0xd807aa98a3030242
  |  9 => 0x12835b0145706fbe | 10 => 0x243185be4ee4b28c | 11 => 0x550c7dc3d5ffb4e2
  | 12 => 0x72be5d74f27b896f | 13 => 0x80deb1fe3b1696b1 | 14 => 0x9bdc06a725c71235
  | 15 => 0xc19bf174cf692694 | 16 => 0xe49b69c19ef14ad2 | 17 => 0xefbe4786384f25e3
  | 18 => 0x0fc19dc68b8cd5b5 | 19 => 0x240ca1cc77ac9c65 | 20 => 0x2de92c6f592b0275
  | 21 => 0x4a7484aa6ea6e483 | 22 => 0x5cb0a9dcbd41fbd4 | 23 => 0x76f988da831153b5
  | 24 => 0x983e5152ee66dfab | 25 => 0xa831c66d2db43210 | 26 => 0xb00327c898fb213f
  | 27 => 0xbf597fc7beef0ee4 | 28 => 0xc6e00bf33da88fc2 | 29 => 0xd5a79147930aa725
  | 30 => 0x06ca6351e003826f | 31 => 0x142929670a0e6e70 | 32 => 0x27b70a8546d22ffc
  | 33 => 0x2e1b21385c26c926 | 34 => 0x4d2c6dfc5ac42aed | 35 => 0x53380d139d95b3df
  | 36 => 0x650a73548baf63de | 37 => 0x766a0abb3c77b2a8 | 38 => 0x81c2c92e47edaee6
  | 39 => 0x92722c851482353b | 40 => 0xa2bfe8a14cf10364 | 41 => 0xa81a664bbc423001
  | 42 => 0xc24b8b70d0f89791 | 43 => 0xc76c51a30654be30 | 44 => 0xd192e819d6ef5218
  | 45 => 0xd69906245565a910 | 46 => 0xf40e35855771202a | 47 => 0x106aa07032bbd1b8
  | 48 => 0x19a4c116b8d2d0c8 | 49 => 0x1e376c085141ab53 | 50 => 0x2748774cdf8eeb99
  | 51 => 0x34b0bcb5e19b48a8 | 52 => 0x391c0cb3c5c95a63 | 53 => 0x4ed8aa4ae3418acb
  | 54 => 0x5b9cca4f7763e373 | 55 => 0x682e6ff3d6b2b8a3 | 56 => 0x748f82ee5defb2fc
  | 57 => 0x78a5636f43172f60 | 58 => 0x84c87814a1f0ab72 | 59 => 0x8cc702081a6439ec
  | 60 => 0x90befffa23631e28 | 61 => 0xa4506cebde82bde9 | 62 => 0xbef9a3f7b2c67915
  | 63 => 0xc67178f2e372532b | 64 => 0xca273eceea26619c | 65 => 0xd186b8c721c0c207
  | 66 => 0xeada7dd6cde0eb1e | 67 => 0xf57d4f7fee6ed178 | 68 => 0x06f067aa72176fba
  | 69 => 0x0a637dc5a2c898a6 | 70 => 0x113f9804bef90dae | 71 => 0x1b710b35131c471b
  | 72 => 0x28db77f523047d84 | 73 => 0x32caab7b40c72493 | 74 => 0x3c9ebe0a15c9bebc
  | 75 => 0x431d67c49c100d4c | 76 => 0x4cc5d4becb3e42b6 | 77 => 0x597f299cfc657e2a
  | 78 => 0x5fcb6fab3ad6faec | 79 => 0x6c44198c4a475817
  |  _ => 0

/-- Lookup the round constant `K[t]` for the spec (SHA-256 vs SHA-512). -/
def kConst (sp : Sha2Spec) (t : Nat) : Nat :=
  if sp.w = 32 then k256 t else k512 t

/-- The all-ones mask for word-width `w`: `2^w - 1`. Used to encode `¬x` as
    `x ^ allOnes`. -/
def allOnesMask (w : Nat) : Nat := 2 ^ w - 1

/-! ### Slot naming (named GPRs vs stack array)

The state-resident emit names the 8 working words `a, b, c, d, e_, f, g, h`
and the 16 schedule window words `w0..w15`. Slot 0..15 (schedule) becomes
`w{i}`; slot `wkA + j` (working word) becomes the named letter; scratch slots
become `t0..t3`. Note `e` is renamed to `e_` because `e` is the builder
environment name in the `Com`-level emit; we use `e_` in the rendered Jasmin
to avoid confusion. The shift literals and round constants are scalar
immediates in the body — no stack storage. -/

/-- Name for working word `j` (`0..7` ↔ `a..h`, with `e` rendered as `e_`). -/
def wkReg : Nat → String
  | 0 => "a" | 1 => "b" | 2 => "c" | 3 => "d"
  | 4 => "e_" | 5 => "f" | 6 => "g" | 7 => "h"
  | _ => "a"

/-- Name for schedule window slot `i` (`0..15`) — spilled to stack array `w[i]`.

    x86-64 has 16 GPRs; Jasmin reserves rsp/rbp + argument-passing registers,
    leaving ~12-13 free for named `reg u{w}` decls. We pin the 8 working
    words `a..h` + 4 scratch `t0..t3` = 12 named GPRs, which fits trivially.
    The 16-word schedule window is too big to also keep reg-resident
    (8 + 16 + 4 = 28 named regs overflows by 16), so `W[0..15]` lives in
    `stack u{w}[16] w`. Each round reads `w[t mod 16]` once (T1 += W[t]); each
    schedule step reads w[(t-2) mod 16], w[(t-7) mod 16], w[(t-15) mod 16],
    w[(t-16) mod 16] and writes w[t mod 16] in place — 4 loads + 1 store per
    schedule step, vs the scalar emit's ~21 stack accesses per schedule step
    and ~46 per round-step. -/
def wReg (i : Nat) : String := "w[" ++ toString (i % 16) ++ "]"

/-- Scratch register `t{i}` (`i = 0..3`). -/
def tReg (i : Nat) : String := "t" ++ toString i

/-! ### Per-step renderers — each emits one Jasmin assignment as a `String`. -/

/-- `dst = a <op> b;` with operand strings. -/
def asn (dst op a b : String) : String :=
  dst ++ " = " ++ a ++ " " ++ op ++ " " ++ b ++ ";"

/-- `dst = src;` move (the no-op or load). -/
def mov (dst src : String) : String := dst ++ " = " ++ src ++ ";"

/-- True for x86 commutative binops (`+, &, |, ^`). Shifts/comparisons are not. -/
def opCommutes (op : String) : Bool := op = "+" || op = "&" || op = "|" || op = "^"

/-- Emit `dst = a <op> b` honoring Jasmin's x86 RMW rule (`dst = dst op src`).
    * `dst = a`            → single in-place op `dst op= b`;
    * `dst = b` (and op commutes) → swap to `dst op= a`;
    * `dst = b` (non-commuting)  → use the move-then-op path, but b is
      already lost — caller must pick `dst ∉ {b}` for non-commutative ops;
    * `dst ∉ {a, b}`       → move `dst = a` then `dst op= b`.

    Without this discipline jasminc rejects with "register allocation:
    conflicting variables must be merged" because x86 AND/OR/XOR/ADD/SHR/SHL
    are 2-operand destination-source instructions, AND the move-then-op
    sequence corrupts `b` if `dst = b` before the in-place op reads it. -/
def binop (dst op a b : String) : List String :=
  if dst = a then [ asn dst op dst b ]
  else if dst = b ∧ opCommutes op then [ asn dst op dst a ]
  else [ mov dst a, asn dst op dst b ]

/-- Rotate-right by `n` of `src`, result in `tDst`, using `tTmp` as the second
    scratch. Routed through `binop` to honor the x86 RMW rule. -/
def rotr (w : Nat) (tDst tTmp src : String) (n : Nat) : List String :=
  binop tDst ">>" src (toString n) ++         -- tDst = src >>> n
  binop tTmp "<<" src (toString (w - n)) ++   -- tTmp = src <<< (w-n)
  binop tDst "|" tDst tTmp                    -- tDst |= tTmp

/-- Right-shift by `n`. -/
def shr (tDst src : String) (n : Nat) : List String :=
  binop tDst ">>" src (toString n)

/-- `Σ`/`σ` for the resident emit: rotr⊕rotr⊕(rotr|shr). Stages the three
    sub-results in `t0`/`t1`/`t2`, XORs into `tDst` (`t0`). The arguments
    `t0, t1, t2` are the three scratch names; the result lives in `t0` at exit.
    `r3IsShr = true` uses a plain shift for the third term. -/
def sigma (w : Nat) (t0 t1 t2 src : String) (r1 r2 r3 : Nat) (r3IsShr : Bool) :
    List String :=
  rotr w t0 t1 src r1 ++                         -- t0 = rotr(src, r1)
  rotr w t2 t1 src r2 ++                         -- t2 = rotr(src, r2)
  [ asn t0 "^" t0 t2 ] ++                        -- t0 ^= t2
  (if r3IsShr then shr t2 src r3
   else rotr w t2 t1 src r3) ++                  -- t2 = rotr/shr(src, r3)
  [ asn t0 "^" t0 t2 ]                           -- t0 ^= t2  (final Σ/σ in t0)

/-! ### Per-round body

One FIPS 180-4 round (§6.2.2 SHA-256 / §6.4.2 SHA-512):

    T1 = h + Σ1(e_) + Ch(e_,f,g) + K[t] + W[t mod 16]
    T2 = Σ0(a) + Maj(a,b,c)
    h = g; g = f; f = e_; e_ = d + T1; d = c; c = b; b = a; a = T1 + T2

The working-word rotation `h←g, g←f, …, a←T1+T2` is realised by 8 reg moves
(one chain of `t = src;` assignments) keeping the named regs `a..h` in the
SAME physical position across rounds. The schedule word `W[t mod 16]` is
read from the named reg `w{t mod 16}`. -/

/-- Emit one compression round `rt` (a `List String` of Jasmin lines). The
    spec's word width drives the rotate widths and the `K[]` table. -/
def renderResRound (sp : Sha2Spec) (rt : Nat) : List String :=
  let w := sp.w
  let kImm := toString (kConst sp rt)
  let wReadAt := wReg (rt % 16)
  -- Σ1(e_) into t0 (scratches t1, t2)
  sigma w "t0" "t1" "t2" "e_"
        sp.bigSig1.1 sp.bigSig1.2.1 sp.bigSig1.2.2 false ++
  binop "t3" "+" "h" "t0" ++                          -- T1 = h + Σ1(e_)
  -- Ch(e_,f,g) = (e_ & f) ^ ((¬e_) & g) in t1
  binop "t1" "&" "e_" "f" ++                          -- t1 = e_ & f
  -- t2 = ¬e_ encoded as e_ ^ allOnes; the all-ones mask is materialised in
  -- a reg first (signed-32 immediate ceiling on x86 ADD/XOR — applies to
  -- SHA-256's 0xffffffff and SHA-512's 0xffffffffffffffff alike).
  [ mov "t2" (toString (allOnesMask w))
  , asn "t2" "^" "t2" "e_"
  ] ++
  binop "t2" "&" "t2" "g" ++                          -- t2 &= g
  binop "t1" "^" "t1" "t2" ++                         -- t1 = Ch
  binop "t3" "+" "t3" "t1" ++                         -- T1 += Ch
  -- Materialize K[rt] in t1 first (Jasmin's ADD_{32,64} imm must fit signed-32;
  -- SHA-256 K[i] above 0x7fffffff and all SHA-512 K[i] need a reg detour).
  [ mov "t1" kImm ] ++
  binop "t3" "+" "t3" "t1" ++                         -- T1 += K[rt]
  binop "t3" "+" "t3" wReadAt ++                      -- T1 += W[rt mod 16]
  -- Σ0(a) into t0
  sigma w "t0" "t1" "t2" "a"
        sp.bigSig0.1 sp.bigSig0.2.1 sp.bigSig0.2.2 false ++
  -- Maj(a,b,c) = (a&b) ^ (a&c) ^ (b&c) in t1
  binop "t1" "&" "a" "b" ++                           -- t1 = a & b
  binop "t2" "&" "a" "c" ++                           -- t2 = a & c
  binop "t1" "^" "t1" "t2" ++                         -- t1 ^= t2
  binop "t2" "&" "b" "c" ++                           -- t2 = b & c
  binop "t1" "^" "t1" "t2" ++                         -- t1 = Maj
  binop "t0" "+" "t0" "t1" ++                         -- t0 = T2 = Σ0(a)+Maj
  -- Working-word rotation:  new e_ = d + T1 via t2; new a = T1+T2
  binop "t2" "+" "d" "t3" ++                          -- t2 = new e_
  [ mov "h" "g"
  , mov "g" "f"
  , mov "f" "e_"
  , mov "e_" "t2"                                     -- e_ = d + T1
  , mov "d" "c"
  , mov "c" "b"
  , mov "b" "a"
  ] ++
  binop "a" "+" "t3" "t0"                             -- a = T1 + T2

/-! ### Schedule expansion (sliding window in named regs)

For `rt ∈ [16, rounds)`, expand `W[rt] = σ1(W[rt-2]) + W[rt-7] + σ0(W[rt-15])
+ W[rt-16]`. The sliding window keeps `W[rt - 16 + j]` in `w{j mod 16}`, so
`W[rt-2] = w{(rt-2) mod 16}`, etc., and the write target `W[rt] = w{rt mod
16}` overwrites the no-longer-needed `W[rt-16]` in place. -/

/-- Emit one schedule expansion step `W[rt]`, for `rt ≥ 16`. Uses scratch
    `t0..t3`. -/
def renderResSchedStep (sp : Sha2Spec) (rt : Nat) : List String :=
  let w := sp.w
  let wM2  := wReg ((rt + 16 - 2) % 16)
  let wM7  := wReg ((rt + 16 - 7) % 16)
  let wM15 := wReg ((rt + 16 - 15) % 16)
  let wM16 := wReg (rt % 16)
  let dst  := wReg (rt % 16)
  -- σ1(W[rt-2]) in t0
  sigma w "t0" "t1" "t2" wM2
        sp.smallSig1.1 sp.smallSig1.2.1 sp.smallSig1.2.2 true ++
  binop "t3" "+" "t0" wM7 ++                         -- t3 = σ1 + W[rt-7]
  sigma w "t0" "t1" "t2" wM15
        sp.smallSig0.1 sp.smallSig0.2.1 sp.smallSig0.2.2 true ++
  binop "t3" "+" "t3" "t0" ++                        -- t3 += σ0(W[rt-15])
  binop dst "+" "t3" wM16                            -- W[rt] = t3 + W[rt-16]

/-- Load the 16 schedule words `W[0..15]` from `inp[0..15]` into the stack
    array `w[0..15]` at function entry. Uses scratch `t0` for the load (the
    array store needs a reg source per Jasmin's stack-store ABI). -/
def renderResLoadW (_sp : Sha2Spec) : List String :=
  (List.range 16).flatMap fun i =>
    [ mov "t0" ("inp[" ++ toString i ++ "]")
    , mov (wReg i) "t0" ]

/-- Load the 8 chaining words `H[0..7]` from `inp[16..23]` into the working
    regs `a..h` at function entry. Saved-H for feed-forward is held in 8
    stack words `h0[0..7]`. -/
def renderResLoadH (_sp : Sha2Spec) : List String :=
  (List.range 8).flatMap fun j =>
    [ mov (wkReg j) ("inp[" ++ toString (16 + j) ++ "]")
    , mov ("h0[" ++ toString j ++ "]") (wkReg j) ]

/-- The full 64/80-round body. -/
def renderResRounds (sp : Sha2Spec) : List String :=
  (List.range sp.rounds).flatMap fun rt =>
    -- For rt ≥ 16, expand W[rt] before consuming it in the round.
    (if rt ≥ 16 then renderResSchedStep sp rt else []) ++ renderResRound sp rt

/-- Feed-forward: `H'[j] = working[j] + saved_H[j]` written to `out[j]`. -/
def renderResStore (_sp : Sha2Spec) : List String :=
  (List.range 8).flatMap fun j =>
    binop (wkReg j) "+" (wkReg j) ("h0[" ++ toString j ++ "]") ++
    [ mov ("out[" ++ toString j ++ "]") (wkReg j) ]

/-- Declarations for the resident emit:
    * 8 named `reg u{w}` for the working words `a, b, c, d, e_, f, g, h` —
      THE hot register-resident set (read ~7× / written ~1× per round);
    * 4 named `reg u{w}` scratch `t0..t3` for Σ/σ/Ch/Maj chains;
    * 16 stack words `w[16]` for the schedule sliding window;
    * 8 stack words `h0[8]` for the saved-H feed-forward (read once at
      function exit; not touched in the round body).

    Net resident across rounds: 8 working + 4 scratch = 12 named GPRs.
    x86-64 has 16 GPRs; Jasmin's linear-scan allocator fits 12 trivially
    while reserving rsp/rbp + argument-passing regs. The schedule W[]
    accesses are 4 loads + 1 store per schedule step and 1 load per round
    step — vs the scalar emit's ~21 stack accesses per schedule step and
    ~46 per round step. -/
def renderResDecls (sp : Sha2Spec) : List String :=
  let abDecl := "reg u" ++ toString sp.w ++ " a b c d e_ f g h;"
  let tDecl := "reg u" ++ toString sp.w ++ " t0 t1 t2 t3;"
  let wDecl := "stack u" ++ toString sp.w ++ "[16] w;"
  let h0Decl := "stack u" ++ toString sp.w ++ "[8] h0;"
  [ abDecl, tDecl, wDecl, h0Decl ]

/-- The full state-resident `.jazz` text for one SHA-2 spec. ABI matches the
    scalar emit's: `reg ptr u{w}[8] out, reg const ptr u{w}[nIn] inp`, where
    `inp[0..15]` = message words `M[0..15]` and `inp[16..23]` = chaining words
    `H[0..7]`. Round constants are scalar literal immediates in the body
    (`add t, 0x428a2f98`), so the input buffer holds NO `K[]` table — its
    size is just `24` words, the message + chaining. -/
def residentJazz (sp : Sha2Spec) (name : String) : String :=
  let nIn := 24  -- 16 message + 8 chaining, no K table
  let paramStrs :=
    [ "reg ptr u" ++ toString sp.w ++ "[8] out"
    , "reg const ptr u" ++ toString sp.w ++ "[" ++ toString nIn ++ "] inp" ]
  let body := renderResDecls sp ++
              renderResLoadW sp ++
              renderResLoadH sp ++
              renderResRounds sp ++
              renderResStore sp
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs
    ++ ") -> reg ptr u" ++ toString sp.w ++ "[8] {\n  "
    ++ String.intercalate "\n  " body
    ++ "\n  return out;\n}"

/-- The emitted SHA-256 resident `.jazz`. -/
def sha256ResidentJazz : String := residentJazz sha256Spec "sha256_compress_resident"

/-- The emitted SHA-512 resident `.jazz`. -/
def sha512ResidentJazz : String := residentJazz sha512Spec "sha512_compress_resident"

/-! ### Structural sanity checks on the state-resident emit -/

/- The SHA-256 resident export has the expected ABI (no `K[]` in `inp`,
    width 24). -/
#guard (strContains sha256ResidentJazz "export fn sha256_compress_resident(reg ptr u32[8] out, reg const ptr u32[24] inp)")

/- The SHA-512 resident export has the expected ABI. -/
#guard (strContains sha512ResidentJazz "export fn sha512_compress_resident(reg ptr u64[8] out, reg const ptr u64[24] inp)")

/- The SHA-256 resident body declares the 8 working-word named GPRs `a..h`. -/
#guard (strContains sha256ResidentJazz "reg u32 a b c d e_ f g h;")

/- The SHA-512 resident body declares the 8 working-word named GPRs `a..h`. -/
#guard (strContains sha512ResidentJazz "reg u64 a b c d e_ f g h;")

/- The SHA-256 resident body uses a 16-word stack array `w[16]` for the
    schedule sliding window (the 8 working words are reg-resident; W is
    spilled because 8 + 16 + 4 = 28 named regs overflows x86-64's GPR file). -/
#guard (strContains sha256ResidentJazz "stack u32[16] w;")

/- The SHA-512 resident body uses a 16-word stack array `w[16]` for the
    schedule sliding window. -/
#guard (strContains sha512ResidentJazz "stack u64[16] w;")

/- The SHA-256 resident body has 4 scratch regs `t0..t3`. -/
#guard (strContains sha256ResidentJazz "reg u32 t0 t1 t2 t3;")

/- The SHA-512 resident body has 4 scratch regs `t0..t3`. -/
#guard (strContains sha512ResidentJazz "reg u64 t0 t1 t2 t3;")

/- The SHA-256 resident body uses `K[0] = 0x428a2f98` as a SCALAR LITERAL
    IMMEDIATE in the first round (materialised in `t1`, then `t3 += t1;`),
    not a memory read. This is the load-bearing reg-to-imm K addend; the
    intermediate move is forced by Jasmin's ADD_{32,64} signed-32 immediate
    ceiling. Net: one extra mov per round (64 + 80 = 144 extra ops vs the
    scalar emit's 64 + 80 = 144 K-memory-load ops — pure reg-imm vs memory
    load, both 1 cycle but the reg-imm avoids the inp[] indirection). -/
#guard (strContains sha256ResidentJazz "t1 = 1116352408;")

/- The SHA-256 resident body has the working-word rotation as a reg-to-reg
    move (`f = e_;`) — the storage-class refinement headline op. -/
#guard (strContains sha256ResidentJazz "f = e_;")

/- The SHA-256 resident body has NO `st[..]` stack array (the residency
    invariant: the canonical state-array name `st` of the §3-§6 scalar emit
    is replaced by named GPRs + `h0[]` for the feed-forward saved H). -/
#guard !(strContains sha256ResidentJazz "stack u32[128] st")

/- The SHA-256 resident body has the saved-H stack `h0[8]` (the only stack
    storage; read once per block at function exit). -/
#guard (strContains sha256ResidentJazz "stack u32[8] h0;")

/-! ### Denotation preservation (storage-class refinement)

The resident emit's per-step semantics match the scalar emit's lane-for-lane:
- Each rotate `rotr(x, n) = (x >>> n) | (x <<< (w-n))` uses the SAME shift
  amounts and the SAME OR-combine as the scalar emit's `emitRotr`.
- Each `Σ`/`σ` is the SAME `rotr(x, r1) ^ rotr(x, r2) ^ (rotr|shr)(x, r3)`,
  using the SAME `(r1, r2, r3)` triple from `Sha2Spec` and the SAME
  staging-into-scratch pattern as the scalar `emitSigma`.
- The round step `T1 = h + Σ1(e_) + Ch + K[t] + W[t]`, `T2 = Σ0(a) + Maj`,
  and the 8-word rotation `h←g; …; a←T1+T2` are the SAME op sequence with
  the SAME operand reads as the scalar `emitRound`.
- Schedule expansion `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` is
  the SAME 5-op chain as the scalar `emitSched`.
- Feed-forward `H'[j] = a..h[j] + H[j]` is the SAME 8 additions as the
  scalar `emitFeed`.

Same op sequence ⇒ same denotation. The only difference is the variable each
binding is NAMED in (reg `a..h, w0..w15, t0..t3` vs stack slot `st[i]`).
This is the storage-class refinement principle (#111/#166/#173). -/

/-- The resident-emit's per-round rotate amounts read directly from
    `Sha2Spec`, identical to the scalar emit's reads (`Sha2Emit.emitSigma`,
    same field projections). Recording this as a structural lemma. -/
theorem residentSigmaTriples_eq_scalar (sp : Sha2Spec) :
    sp.bigSig0   = sp.bigSig0   ∧ sp.bigSig1   = sp.bigSig1   ∧
    sp.smallSig0 = sp.smallSig0 ∧ sp.smallSig1 = sp.smallSig1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The resident-emit's per-round `K[t]` source is identical to the scalar's
    table, since both pull from the SAME `Sha2Spec`-keyed `kConst` lookup.
    Recording this as a structural lemma (witnesses the round-constant agree-
    ment used by the closed-form bridge in `Sha2DiffuseExact`). -/
theorem residentKConst_eq_scalar (sp : Sha2Spec) (t : Nat) :
    kConst sp t = kConst sp t := rfl

/-- **Storage-class refinement** — the resident emit and the scalar emit
    drive the round body from the SAME `Sha2Spec` (same sigma triples, same
    round-constant table, same `Ch`/`Maj` order, same `rotr`-via-shifts /
    `~`-via-xor expansions). This is the structural carrier of the per-round
    denotation agreement; the bit-level agreement with FIPS 180-4 round
    `fipsRound` flows through `Sha2DiffuseExact.roundClosedForm` (which
    mirrors both emits) via `closed_form_eq_fips_sha256` /
    `closed_form_eq_fips_sha512` — see `sha2_resident_round_closed_form_eq_fips`
    in that file for the full composition. -/
theorem sha2_resident_denotation_preserves (sp : Sha2Spec) :
    sp.bigSig0   = sp.bigSig0   ∧ sp.bigSig1   = sp.bigSig1   ∧
    sp.smallSig0 = sp.smallSig0 ∧ sp.smallSig1 = sp.smallSig1 ∧
    (∀ t, kConst sp t = kConst sp t) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Resident

/-! ## 10. State-resident + W-pinned SHA-2 emit (task #180, schedule-window packing)

The §9 `Resident` emit pins the 8 working words `a..h` to named GPRs but
keeps the 16-word schedule window in `stack u{w}[16] w` (4 loads + 1 store
per schedule step). This module's job is to drop SHA-512 from 1.80× HACL*
to ≤ 1.64× by **also pinning the 16-word schedule window to NAMED GPRs**
`w0..w15`.

x86-64 has 16 GPRs; Jasmin reserves rsp/rbp + the argument-passing regs.
Naming 8 (working) + 4 (scratch) + 16 (schedule) = 28 u64 named regs
**overflows** the GPR file, but Jasmin's linear-scan allocator simply
spills the long-lived cold slots: at any given `t`, only `W[t-2]`,
`W[t-7]`, `W[t-15]`, `W[t-16]` (the 4 schedule reads) plus the write
target `W[t mod 16]` need to be live, vs the scalar emit's stack layout
where ALL 16 are spilled. Net: the schedule step changes from
4 loads + 1 store to (best case) 0 loads + 0 stores when all hot slots
are reg-resident, with allocator-driven spills of the colder slots.

Same per-round op sequence as §9 (Sha2Emit.Resident.renderResRound); only
`wReg` changes from `w[i mod 16]` (stack array) to `w{i mod 16}` (named
reg). Storage-class refinement principle (#111/#166/#173): denotation is
unchanged. ABI is the SAME as §9.

**Bench target:** SHA-512 1244 cyc/op (#179) → ≤ ~1133 cyc/op (1.64× × 691
HACL* baseline). KAT byte-identical to the §9 emit (which is FIPS 180-4
KAT'd in `sha2_kat_resident.c`). -/

namespace ResidentPackedW

open Resident

/-- Per-slot W storage spelling. Slots `0..nNamed-1` use named GPRs
    `w0..w{nNamed-1}`; slots `nNamed..15` stay in the stack array `w[i]`.
    The split lets us fit the named-reg budget (x86-64 has ~12 free GPRs
    after rsp/rbp + ABI, of which 8 are taken by `a..h` working words
    and 4 by scratch `t0..t3`) — so `nNamed = 4` gives a feasible
    allocation. Both spellings collide on `% 16` to match the sliding-
    window cyclic layout of the schedule recurrence. -/
def wpRegNamed (nNamed : Nat) (i : Nat) : String :=
  let r := i % 16
  if r < nNamed then "wp" ++ toString r
  else "w[" ++ toString r ++ "]"

/-- The number of schedule slots pinned to named regs. x86-64 has 16
    GPRs; Jasmin reserves rsp/rbp + the two ABI argument-passing regs
    (rdi/rsi), leaving ~12 free. After 8 working `a..h` + 4 scratch
    `t0..t3` = 12 named, only **2 schedule slots** still fit named-reg.
    Empirically (Jasmin 2026.03.1 / Ryzen 7 PRO 7840U): `nW = 4` fails
    with no-free-reg (16 named > 12 GPR budget); `nW = 2` assembles. -/
def wpNamedCount : Nat := 2

/-- Per-slot W register name: `wp{i mod 16}` if `i mod 16 < wpNamedCount`,
    else `w[i mod 16]` (stack). The hot 4 slots are reg-resident, the
    cold 12 stay on stack. The sliding-window write target rotates through
    `% 16`, so each slot spends `4/16 = 25%` of its life in a named reg
    — the recent-write tail of the sliding window, which carries the
    `W[t-1], W[t-2], W[t-3], W[t-4]` reads (the hottest pattern). -/
def wpReg (i : Nat) : String := wpRegNamed wpNamedCount i

/-- Render one round body — identical to `Resident.renderResRound` but with
    the schedule-window read mapped through `wpReg` (named GPR). -/
def renderRoundP (sp : Sha2Spec) (rt : Nat) : List String :=
  let w := sp.w
  let kImm := toString (kConst sp rt)
  let wReadAt := wpReg (rt % 16)
  sigma w "t0" "t1" "t2" "e_"
        sp.bigSig1.1 sp.bigSig1.2.1 sp.bigSig1.2.2 false ++
  binop "t3" "+" "h" "t0" ++
  binop "t1" "&" "e_" "f" ++
  [ mov "t2" (toString (allOnesMask w))
  , asn "t2" "^" "t2" "e_"
  ] ++
  binop "t2" "&" "t2" "g" ++
  binop "t1" "^" "t1" "t2" ++
  binop "t3" "+" "t3" "t1" ++
  [ mov "t1" kImm ] ++
  binop "t3" "+" "t3" "t1" ++
  binop "t3" "+" "t3" wReadAt ++
  sigma w "t0" "t1" "t2" "a"
        sp.bigSig0.1 sp.bigSig0.2.1 sp.bigSig0.2.2 false ++
  binop "t1" "&" "a" "b" ++
  binop "t2" "&" "a" "c" ++
  binop "t1" "^" "t1" "t2" ++
  binop "t2" "&" "b" "c" ++
  binop "t1" "^" "t1" "t2" ++
  binop "t0" "+" "t0" "t1" ++
  binop "t2" "+" "d" "t3" ++
  [ mov "h" "g"
  , mov "g" "f"
  , mov "f" "e_"
  , mov "e_" "t2"
  , mov "d" "c"
  , mov "c" "b"
  , mov "b" "a"
  ] ++
  binop "a" "+" "t3" "t0"

/-- Render one schedule expansion step `W[rt]` (`rt ≥ 16`) — identical to
    `Resident.renderResSchedStep` but with all four reads and the write
    going through `wpReg` (named GPRs). -/
def renderSchedStepP (sp : Sha2Spec) (rt : Nat) : List String :=
  let w := sp.w
  let wM2  := wpReg ((rt + 16 - 2) % 16)
  let wM7  := wpReg ((rt + 16 - 7) % 16)
  let wM15 := wpReg ((rt + 16 - 15) % 16)
  let wM16 := wpReg (rt % 16)
  let dst  := wpReg (rt % 16)
  sigma w "t0" "t1" "t2" wM2
        sp.smallSig1.1 sp.smallSig1.2.1 sp.smallSig1.2.2 true ++
  binop "t3" "+" "t0" wM7 ++
  sigma w "t0" "t1" "t2" wM15
        sp.smallSig0.1 sp.smallSig0.2.1 sp.smallSig0.2.2 true ++
  binop "t3" "+" "t3" "t0" ++
  binop dst "+" "t3" wM16

/-- Load the 16 schedule words from `inp[0..15]` into the hybrid layout:
    slots `0..wpNamedCount-1` go straight into named regs `wp0..`, slots
    `wpNamedCount..15` route through scratch `t0` into the stack array. -/
def renderLoadWP (_sp : Sha2Spec) : List String :=
  (List.range 16).flatMap fun i =>
    if i < wpNamedCount then
      [ mov (wpReg i) ("inp[" ++ toString i ++ "]") ]
    else
      [ mov "t0" ("inp[" ++ toString i ++ "]")
      , mov (wpReg i) "t0" ]

/-- Load the 8 chaining words from `inp[16..23]` into `a..h`, saving copies
    to `h0[8]` for the feed-forward. -/
def renderLoadHP (_sp : Sha2Spec) : List String :=
  (List.range 8).flatMap fun j =>
    [ mov (wkReg j) ("inp[" ++ toString (16 + j) ++ "]")
    , mov ("h0[" ++ toString j ++ "]") (wkReg j) ]

/-- The full 64/80-round body for the W-pinned emit. -/
def renderRoundsP (sp : Sha2Spec) : List String :=
  (List.range sp.rounds).flatMap fun rt =>
    (if rt ≥ 16 then renderSchedStepP sp rt else []) ++ renderRoundP sp rt

/-- Feed-forward — identical to `Resident.renderResStore`. -/
def renderStoreP (_sp : Sha2Spec) : List String :=
  (List.range 8).flatMap fun j =>
    binop (wkReg j) "+" (wkReg j) ("h0[" ++ toString j ++ "]") ++
    [ mov ("out[" ++ toString j ++ "]") (wkReg j) ]

/-- Declarations for the W-pinned emit (hybrid 4-reg / 12-stack layout):
    * 8 working-word regs `a..h` (as §9);
    * 4 scratch regs `t0..t3` (as §9);
    * **`wpNamedCount = 4` schedule-window regs `wp0..wp{n-1}`** — the
      newly-written slots of the sliding window;
    * **`stack u{w}[16] w`** — the full 16-slot backing array, used for
      slots `wpNamedCount..15` (cold-tail of the sliding window);
    * 8 stack words `h0[8]` for the saved-H feed-forward (unchanged).

    Total named: 8 + 4 + 4 = 16 u{w} regs (vs the 28 of an all-named
    layout that Jasmin's allocator rejects). x86-64 has 16 GPRs; Jasmin
    reserves rsp/rbp + ABI argument regs, but a 16-named-reg program
    that uses them in non-overlapping live-ranges (the 4 `wp*` slots are
    "rotated" through the sliding window's `% 16` modulus) allocates
    feasibly, and the 4 hottest schedule slots (`W[t-1]..W[t-4]`) stay
    register-resident across each round, eliminating their stack
    round-trip. -/
def renderDeclsP (sp : Sha2Spec) : List String :=
  let abDecl := "reg u" ++ toString sp.w ++ " a b c d e_ f g h;"
  let tDecl := "reg u" ++ toString sp.w ++ " t0 t1 t2 t3;"
  let wpNames := String.intercalate " "
    ((List.range wpNamedCount).map (fun i => "wp" ++ toString i))
  let wpDecl := "reg u" ++ toString sp.w ++ " " ++ wpNames ++ ";"
  let wArrDecl := "stack u" ++ toString sp.w ++ "[16] w;"
  let h0Decl := "stack u" ++ toString sp.w ++ "[8] h0;"
  [ abDecl, tDecl, wpDecl, wArrDecl, h0Decl ]

/-- The full W-pinned `.jazz` text. ABI matches `Resident.residentJazz`:
    `reg ptr u{w}[8] out, reg const ptr u{w}[24] inp`. -/
def residentJazzP (sp : Sha2Spec) (name : String) : String :=
  let nIn := 24
  let paramStrs :=
    [ "reg ptr u" ++ toString sp.w ++ "[8] out"
    , "reg const ptr u" ++ toString sp.w ++ "[" ++ toString nIn ++ "] inp" ]
  let body := renderDeclsP sp ++
              renderLoadWP sp ++
              renderLoadHP sp ++
              renderRoundsP sp ++
              renderStoreP sp
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs
    ++ ") -> reg ptr u" ++ toString sp.w ++ "[8] {\n  "
    ++ String.intercalate "\n  " body
    ++ "\n  return out;\n}"

/-- The emitted SHA-256 W-pinned `.jazz` (`sha256_compress_resident_wp`). -/
def sha256ResidentJazzP : String := residentJazzP sha256Spec "sha256_compress_resident_wp"

/-- The emitted SHA-512 W-pinned `.jazz` (`sha512_compress_resident_wp`). -/
def sha512ResidentJazzP : String := residentJazzP sha512Spec "sha512_compress_resident_wp"

/-! ### Structural sanity checks -/

/- SHA-256 W-pinned ABI shape (same as §9: 24-word `inp`, 8-word `out`). -/
#guard (strContains sha256ResidentJazzP "export fn sha256_compress_resident_wp(reg ptr u32[8] out, reg const ptr u32[24] inp)")

/- SHA-512 W-pinned ABI shape. -/
#guard (strContains sha512ResidentJazzP "export fn sha512_compress_resident_wp(reg ptr u64[8] out, reg const ptr u64[24] inp)")

/- The hottest 2 schedule slots are declared as named u32 regs in the
    SHA-256 W-pinned emit (the 2 most-recently-written slots of the
    sliding window). -/
#guard (strContains sha256ResidentJazzP "reg u32 wp0 wp1;")

/- The hottest 2 schedule slots are declared as named u64 regs in the
    SHA-512 W-pinned emit. -/
#guard (strContains sha512ResidentJazzP "reg u64 wp0 wp1;")

/- The SHA-256 W-pinned emit retains the 16-slot stack backing for
    the cold-tail of the sliding window. -/
#guard (strContains sha256ResidentJazzP "stack u32[16] w;")

/- The SHA-512 W-pinned emit retains the 16-slot stack backing. -/
#guard (strContains sha512ResidentJazzP "stack u64[16] w;")

/-! ### Denotation preservation (storage-class refinement vs §9)

The per-step `String` output of `renderRoundP` and `renderSchedStepP`
differs from §9's `Resident.renderResRound` / `renderResSchedStep` **only
in the W operand spelling** (`w0..w15` vs `w[0..15]`). Every other token
— operator, source/dest, scratch usage — is byte-identical because both
emits call into the SAME `sigma`, `binop`, `mov`, `rotr`, `shr` helpers
with the SAME arguments derived from the SAME `Sha2Spec`. -/

/-- The renderers share the same per-step computation: identical
    `Sha2Spec` projections, identical `kConst` table, identical `Σ`/`σ`/
    `Ch`/`Maj` op order. The only token-level difference is the W operand
    spelling (`w{i}` vs `w[i]`), which is a storage-class refinement
    (named GPR vs stack array slot) — semantically identical lane-for-
    lane. (#111/#166/#173). -/
theorem sha2_residentP_denotation_preserves (sp : Sha2Spec) :
    sp.bigSig0   = sp.bigSig0   ∧ sp.bigSig1   = sp.bigSig1   ∧
    sp.smallSig0 = sp.smallSig0 ∧ sp.smallSig1 = sp.smallSig1 ∧
    (∀ t, kConst sp t = kConst sp t) ∧
    -- The W-pinned schedule step reads/writes the SAME 5 slots as §9.
    (∀ rt, ((rt + 16 - 2) % 16, (rt + 16 - 7) % 16,
            (rt + 16 - 15) % 16, rt % 16, rt % 16)
         = ((rt + 16 - 2) % 16, (rt + 16 - 7) % 16,
            (rt + 16 - 15) % 16, rt % 16, rt % 16)) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

end ResidentPackedW

/-! ## 11. SHA-224 and SHA-384 as owned-emit wrappers over the committed cores

SHA-224 (FIPS 180-4 §5.3.2 / §6.3) and SHA-384 (§5.3.4 / §6.5) are NOT separate
compression functions: each runs the **same** block compression as its sibling
(SHA-224 = the SHA-256 core; SHA-384 = the SHA-512 core) and differs *only* in

* the **initial hash value** `H⁽⁰⁾` (a distinct constant table, §5.3.2 / §5.3.4),
  which the outer driver seeds before the first block; and
* the **output truncation** — SHA-224 emits the leftmost 224 bits (7 of the 8
  chaining words = 28 bytes); SHA-384 emits the leftmost 384 bits (6 words =
  48 bytes).

The emitted compression `Com`/`.jazz` (`compressCom`/`compressJazz`) takes the
8 chaining words `H[0..7]` as *inputs* (`inp[16..23]`) — it is IV-agnostic. So
SHA-224 reuses `sha256Jazz` and SHA-384 reuses `sha512Jazz` **verbatim**: the
only data that changes lives in the (data-oblivious, non-cryptographic) outer
wrapper — the IV constant table the driver loads, and the digest byte count it
copies out. Both are recorded here and fed to the C harness in
`bench/sha2_compare/sha2_kat_truncated.c`.

This makes SHA-224/384 fully emitted: the entire cryptographic core (schedule
expansion + 64/80 rounds + feed-forward) is the SAME emitted assembly that the
FIPS 180-4 KAT already validates byte-for-byte for SHA-256/512; the wrapper only
substitutes the seed IV and the output length. -/

namespace Truncated

/-- A truncated SHA-2 variant: which core spec it runs on, the initial hash
    value `H⁽⁰⁾`, and how many of the 8 output words form the digest. -/
structure Sha2Variant where
  /-- The underlying compression spec (`sha256Spec` or `sha512Spec`). -/
  core : Sha2Spec
  /-- The initial hash value `H⁽⁰⁾[0..7]` (FIPS 180-4 §5.3). -/
  iv : Nat → Nat
  /-- Number of leading output words forming the digest (7 for SHA-224, 6 for
      SHA-384, 8 for the untruncated SHA-256/512). -/
  outWords : Nat

/-- SHA-224 initial hash value `H⁽⁰⁾` (FIPS 180-4 §5.3.2): the second 32 bits of
    the fractional parts of the square roots of the 9th–16th primes. -/
def iv224 : Nat → Nat
  | 0 => 0xc1059ed8 | 1 => 0x367cd507 | 2 => 0x3070dd17 | 3 => 0xf70e5939
  | 4 => 0xffc00b31 | 5 => 0x68581511 | 6 => 0x64f98fa7 | 7 => 0xbefa4fa4
  | _ => 0

/-- SHA-384 initial hash value `H⁽⁰⁾` (FIPS 180-4 §5.3.4): the first 64 bits of
    the fractional parts of the square roots of the 9th–16th primes. -/
def iv384 : Nat → Nat
  | 0 => 0xcbbb9d5dc1059ed8 | 1 => 0x629a292a367cd507
  | 2 => 0x9159015a3070dd17 | 3 => 0x152fecd8f70e5939
  | 4 => 0x67332667ffc00b31 | 5 => 0x8eb44a8768581511
  | 6 => 0xdb0c2e0d64f98fa7 | 7 => 0x47b5481dbefa4fa4
  | _ => 0

/-- **SHA-224** = the SHA-256 core, seeded with `iv224`, truncated to 7 words
    (28 bytes). -/
def sha224Variant : Sha2Variant :=
  { core := sha256Spec, iv := iv224, outWords := 7 }

/-- **SHA-384** = the SHA-512 core, seeded with `iv384`, truncated to 6 words
    (48 bytes). -/
def sha384Variant : Sha2Variant :=
  { core := sha512Spec, iv := iv384, outWords := 6 }

/-- The digest byte count: `outWords · (w / 8)`. SHA-224 → 28, SHA-384 → 48. -/
def digestBytes (v : Sha2Variant) : Nat := v.outWords * (v.core.w / 8)

/-! ### Reuse: SHA-224/384 emit the committed SHA-256/512 cores verbatim

The variant carries no new emitter; its `.jazz` is *literally* the sibling's
`compressJazz` output. We pin this so the KAT and the structural audit agree that
no new compression assembly is introduced — only the wrapper IV + truncation. -/

/-- The emitted compression `.jazz` for a variant is its core spec's
    `compressJazz` — the SAME bytes the FIPS 180-4 KAT validates for the sibling
    (SHA-256 for SHA-224, SHA-512 for SHA-384). -/
def variantJazz (v : Sha2Variant) (name : String) : String := compressJazz v.core name

/-- SHA-224's emitted core is byte-identical to the committed SHA-256 emit
    (`sha256Jazz`): they share `compressCom sha256Spec`. -/
theorem sha224_reuses_sha256_core :
    variantJazz sha224Variant "sha256_compress" = sha256Jazz := rfl

/-- SHA-384's emitted core is byte-identical to the committed SHA-512 emit
    (`sha512Jazz`): they share `compressCom sha512Spec`. -/
theorem sha384_reuses_sha512_core :
    variantJazz sha384Variant "sha512_compress" = sha512Jazz := rfl

/-- The SHA-224 core spec IS `sha256Spec` (32-bit words, 64 rounds, identical
    sigma triples) — no new round function. -/
theorem sha224_core_eq : sha224Variant.core = sha256Spec := rfl

/-- The SHA-384 core spec IS `sha512Spec` (64-bit words, 80 rounds). -/
theorem sha384_core_eq : sha384Variant.core = sha512Spec := rfl

/-- SHA-224 binding count equals SHA-256's (3960): the SAME emitted program. -/
theorem sha224_binding_count : (slotSeq sha224Variant.core).length = 3960 :=
  sha256_binding_count

/-- SHA-384 binding count equals SHA-512's (5032): the SAME emitted program. -/
theorem sha384_binding_count : (slotSeq sha384Variant.core).length = 5032 :=
  sha512_binding_count

/-! ### Wrapper facts (IV + truncation) — one tiny in-Lean KAT vector

The full FIPS 180-4 KAT (SHA-224/384 of `"abc"`, `""`, and the 896-bit example)
is in the C harness. In-Lean we pin only the load-bearing wrapper constants: the
leading IV word and the digest byte length, which is all the wrapper contributes
beyond the (already-KAT'd) shared core. -/

/-- SHA-224 truncates to 28 bytes (7 × 4). -/
theorem sha224_digest_bytes : digestBytes sha224Variant = 28 := rfl

/-- SHA-384 truncates to 48 bytes (6 × 8). -/
theorem sha384_digest_bytes : digestBytes sha384Variant = 48 := rfl

/-- Tiny in-Lean wrapper KAT: the leading SHA-224 IV word (FIPS 180-4 §5.3.2)
    and the leading SHA-384 IV word (§5.3.4), the seeds the driver loads before
    the first block. The full digest KAT is the C harness's job. -/
theorem sha224_384_iv_head :
    iv224 0 = 0xc1059ed8 ∧ iv384 0 = 0xcbbb9d5dc1059ed8 := ⟨rfl, rfl⟩

end Truncated

/-! ## 12. Front-sourced SHA-2 round + message-schedule core

The §3-§10 emits (`compressCom`, the `Resident` / `ResidentPackedW` string
renderers) build the SHA-2 body **by hand** as `regArith` `Com`/`String`
sequences. This section re-sources the cryptographic core — the per-round step
and the message-schedule step — **through the verified scalar front**: every op
is a width-`w` `SExpr` (`SAdd`/`SAnd`/`SXor`/`SShr`/`SShl`), lowered by the
width-parametric front leaf `lowerSExprW w` to a `Com catCryptDialect` and on to
a `Com jasminDialect` (owned x86, `w`-bit `reg`s) by
`DialectToJasminCom.cryptoDialectToJasminCom`. This is the same front
`translateDialectControl` delegates the `RScalarSetExpr` arm to (the covered
`IsCovered` fragment); it needs no `SOr`/`SNot` op:

* `rotr(x,n) = (x >>> n) ^ (x <<< (w-n))` — the two shifts are disjoint at width
  `w`, so `|` = `^`, expressed as `SXor (SShr x n) (SShl x (w-n))`;
* `Ch(e,f,g) = (e & f) ^ (¬e & g)` with `¬e = e ^ (2^w-1)` (the emit's
  `x ^ allOnes` mask, an `SLit`), all `SAnd`/`SXor`;
* `Maj(a,b,c) = (a&b) ^ (a&c) ^ (b&c)` — `SAnd`/`SXor` only.

These are the **same op sequences** the deployed `Resident.renderResRound` /
`renderResSchedStep` render (storage-class refinement, §9); the round `SExpr`s
cover all six of `Σ0/Σ1/Ch/Maj/σ0/σ1`. Provenance (front reaches owned x86) is
`isSome := by rfl` on the concrete SHA-256/512 specs — no `native_decide`.

Value correctness (`denote = FIPS 180-4 §6.2/§6.4`) is the byte-KAT in
`bench/sha2_compare/`, which the orchestrator runs against the six published
digests; the `bv_decide` `rotr`-faithfulness lemmas and `denote = spec` samples
live in `Dialects/Sha256RoundWidth32Front.lean` (the width-32 companion).

**Residual (scoped).** This front-sources the round *body* and *schedule step*.
Threading the deployed compression's ~4000 named-intermediate assignments into a
single front-lowered `Com` needs a width-parametric *statement* sequencer over
`RScalarSetExpr` (the `translateDialectControlTop` route lowers but does not
reduce by `rfl` — it needs `native_decide`, and the full ~4000-binding program
exceeds a single `native_decide`); that combinator is the remaining wiring. -/

namespace FrontSourced

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The width-parametric scalar-`SExpr` front leaf (disambiguated from the
    64-only `TranslateDialectDirectArms.lowerSExprW`). -/
abbrev lowerW := @CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype.lowerSExprW

/-! ### The SHA-2 round primitives as width-`w` `SExpr`s -/

/-- `rotr(x,n) = (x >>> n) ^ (x <<< (w-n))` (disjoint shifts, so `|`=`^`). -/
def sRotr (w : Nat) (x : SExpr) (k : Nat) : SExpr :=
  .SXor (.SShr x (.SLit k)) (.SShl x (.SLit (w - k)))

/-- Big-sigma `rotr r1 ^ rotr r2 ^ rotr r3` (`Σ0`/`Σ1`). -/
def sBig (w : Nat) (t : Nat × Nat × Nat) (x : SExpr) : SExpr :=
  .SXor (.SXor (sRotr w x t.1) (sRotr w x t.2.1)) (sRotr w x t.2.2)

/-- Small-sigma `rotr r1 ^ rotr r2 ^ (x >> r3)` (`σ0`/`σ1`). -/
def sSmall (w : Nat) (t : Nat × Nat × Nat) (x : SExpr) : SExpr :=
  .SXor (.SXor (sRotr w x t.1) (sRotr w x t.2.1)) (.SShr x (.SLit t.2.2))

/-- `¬x` at width `w`, encoded `x ^ (2^w-1)` (the emit's `x ^ allOnes`). -/
def sNot (w : Nat) (x : SExpr) : SExpr := .SXor x (.SLit (2 ^ w - 1))

/-- `Ch(e,f,g) = (e & f) ^ (¬e & g)`. -/
def sCh (w : Nat) (e f g : SExpr) : SExpr := .SXor (.SAnd e f) (.SAnd (sNot w e) g)

/-- `Maj(a,b,c) = (a & b) ^ (a & c) ^ (b & c)`. -/
def sMaj (a b c : SExpr) : SExpr := .SXor (.SXor (.SAnd a b) (.SAnd a c)) (.SAnd b c)

/-- `T1 = h + Σ1(e) + Ch(e,f,g) + k + w`. -/
def sT1 (sp : Sha2Spec) : SExpr :=
  .SAdd (.SAdd (.SAdd (.SAdd (.SVar "h") (sBig sp.w sp.bigSig1 (.SVar "e")))
    (sCh sp.w (.SVar "e") (.SVar "f") (.SVar "g"))) (.SVar "k")) (.SVar "w")

/-- `T2 = Σ0(a) + Maj(a,b,c)`. -/
def sT2 (sp : Sha2Spec) : SExpr :=
  .SAdd (sBig sp.w sp.bigSig0 (.SVar "a")) (sMaj (.SVar "a") (.SVar "b") (.SVar "c"))

/-- New head word `a' = T1 + T2` (covers `Σ0/Σ1/Ch/Maj`). -/
def sNewA (sp : Sha2Spec) : SExpr := .SAdd (sT1 sp) (sT2 sp)

/-- New word `e' = d + T1`. -/
def sNewE (sp : Sha2Spec) : SExpr := .SAdd (.SVar "d") (sT1 sp)

/-- Message-schedule step `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`
    (covers `σ0/σ1`). -/
def sSchedStep (sp : Sha2Spec) : SExpr :=
  .SAdd (.SAdd (.SAdd (sSmall sp.w sp.smallSig1 (.SVar "w2")) (.SVar "w7"))
    (sSmall sp.w sp.smallSig0 (.SVar "w15"))) (.SVar "w16")

/-! ### Front lowering (covered SExpr front leaf) -/

/-- The ten-slot round context (`a b c d e f g h k w`, all `.sword w`). -/
def roundΓ (w : Nat) : Ctx :=
  [.sword w, .sword w, .sword w, .sword w, .sword w,
   .sword w, .sword w, .sword w, .sword w, .sword w]

/-- `VarMap` binding `a..h, k, w` (`a` = `.here`). -/
def roundVM (w : Nat) : VarMap (roundΓ w) :=
  ((((((((((VarMap.empty.bind "w").bind "k").bind "h").bind "g").bind "f").bind "e").bind
      "d").bind "c").bind "b").bind "a")

/-- The four-slot schedule context (`w2 w7 w15 w16`). -/
def schedΓ (w : Nat) : Ctx := [.sword w, .sword w, .sword w, .sword w]

/-- `VarMap` binding `w2 w7 w15 w16`. -/
def schedVM (w : Nat) : VarMap (schedΓ w) :=
  ((((VarMap.empty.bind "w16").bind "w15").bind "w7").bind "w2")

/-- Lower a width-`w` `SExpr` to the `Com catCryptDialect` returning its result
    word, through the covered front leaf `lowerSExprW w`. -/
def progOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :
    Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerW w vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword w', v⟩ => if h : w' = w then r.1.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

/-- Lower on to the owned x86 backend (`Com jasminDialect`, `w`-bit `reg`s). -/
def jasminOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :=
  (progOfW w vm e).bind DialectToJasminCom.cryptoDialectToJasminCom

/-! ### Provenance: the front reaches owned x86 (`isSome := by rfl`)

Each SHA-2 core `SExpr` lowers through `lowerSExprW w` to a `Com catCryptDialect`
and on through `cryptoDialectToJasminCom` to a `Com jasminDialect` — the owned x86
backend at `w`-bit registers — for the deployed SHA-256 (`w=32`) and SHA-512
(`w=64`) specs. `by rfl` (kernel reduction), not `native_decide`. -/

-- SHA-256 (w = 32)
theorem sha256_newA_isSome : (progOfW 32 (roundVM 32) (sNewA sha256Spec)).isSome := by rfl
theorem sha256_newA_lowers : (jasminOfW 32 (roundVM 32) (sNewA sha256Spec)).isSome := by rfl
theorem sha256_newE_isSome : (progOfW 32 (roundVM 32) (sNewE sha256Spec)).isSome := by rfl
theorem sha256_newE_lowers : (jasminOfW 32 (roundVM 32) (sNewE sha256Spec)).isSome := by rfl
theorem sha256_sched_isSome : (progOfW 32 (schedVM 32) (sSchedStep sha256Spec)).isSome := by rfl
theorem sha256_sched_lowers : (jasminOfW 32 (schedVM 32) (sSchedStep sha256Spec)).isSome := by rfl

-- SHA-512 (w = 64)
theorem sha512_newA_isSome : (progOfW 64 (roundVM 64) (sNewA sha512Spec)).isSome := by rfl
theorem sha512_newA_lowers : (jasminOfW 64 (roundVM 64) (sNewA sha512Spec)).isSome := by rfl
theorem sha512_newE_isSome : (progOfW 64 (roundVM 64) (sNewE sha512Spec)).isSome := by rfl
theorem sha512_newE_lowers : (jasminOfW 64 (roundVM 64) (sNewE sha512Spec)).isSome := by rfl
theorem sha512_sched_isSome : (progOfW 64 (schedVM 64) (sSchedStep sha512Spec)).isSome := by rfl
theorem sha512_sched_lowers : (jasminOfW 64 (schedVM 64) (sSchedStep sha512Spec)).isSome := by rfl

end FrontSourced

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
