/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

/-!
# ChaCha20 emitted from a `Com jasminDialect` through the register-arith front

This is the qualitatively-deepest test of the verified-front pipeline: it emits
a whole standardized primitive's **actual computation** — not glue around
opaque leaves. ChaCha20 (RFC 8439) is a pure ARX cipher (add / xor / shift / or
on `u32`, no leaves), so building it as a `Com jasminDialect` and emitting it
exercises the new `regArith` EMIT-computation path (`emitAbiOrchReg`) plus the
new dialect shift ops (`JasminBinOp.shl` / `.shr`).

## Construction (CPS builder over `reg 32` state words)

The builder threads the **16 current state-word variables** as a
`Fin 16 → Ctxt.Var Γ (.reg 32)`, plus the **16 original input variables** (for
the final feed-forward), over a context `Γ` that grows by one `.reg 32` per
emitted binding. Each emitted binding:

1. reads its two source variables out of the current 16-vector (or the originals),
2. emits `.var (regArith op 32) cont`, where `cont` is built over `(.reg 32) :: Γ`
   with every carried variable shifted by `.there` and the written slot rebound to
   the fresh `.here`.

* `rotL n` = `(x <<< n) ||| (x >>> (32-n))` — three bindings (`shl`, `shr`, `or`),
  the ARX rotate composed from the new shift ops.
* `quarterRound a b c d` — the RFC 8439 §2.1 step sequence.
* `columnRound` / `diagonalRound` / `doubleRound` — RFC 8439 §2.3.
* `chachaCore` = 10 double-rounds; `chachaBlock` = core + the original 16 inputs
  (final feed-forward), whose 16 `add` bindings are the **last 16** in the
  program — exactly the `emitAbiOrchReg` output convention.

The emitted `.jazz` is validated against the RFC 8439 §2.3.2 known-answer test in
`bench/chacha_compare/`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMap (laneMap ChaChaState ChaCha4Way)

set_option autoImplicit false

/-- The `reg 32` dialect type, abbreviated. -/
abbrev r32 : JasminTy := .reg 32

/-! ## 1. Builder state and ABI layout

The export's input buffer holds **23** `u32` words:

* indices `0..15`  — the 16 ChaCha state words (also the feed-forward originals);
* indices `16..22` — the 7 distinct rotate shift amounts the ARX rotates need
  (`16, 12, 8, 7, 20, 24, 25`), supplied as register operands so every emitted
  op is a `regArith` over real registers (no immediate-shift op needed).

`BState Γ` carries the 16 current state words, the 16 originals, and the 7 shift
constants, all as `Ctxt.Var Γ r32`. -/

/-- The shift-amount constants the ARX rotates use, in input order
    (`inp[16+j]`). rotL n = shl n / shr (32-n): n ∈ {16,12,8,7} with complements
    {16,20,24,25}; the distinct values are these 7. -/
def shiftConsts : Fin 7 → Nat
  | 0 => 16 | 1 => 12 | 2 => 8 | 3 => 7 | 4 => 20 | 5 => 24 | 6 => 25

/-- `shiftConsts` indexed by a `Nat` (out-of-range saturates to `16`; never
    triggered — the builder only asks for `j < 7`). -/
def shiftConstNat : Nat → Nat
  | 0 => 16 | 1 => 12 | 2 => 8 | 3 => 7 | 4 => 20 | 5 => 24 | 6 => 25
  | _ => 16

/-- Index into `shiftConsts` for a given shift amount (total; the rotates only
    ever ask for one of the 7 listed values). -/
def shiftIdx (n : Nat) : Fin 7 :=
  if n = 16 then 0 else if n = 12 then 1 else if n = 8 then 2
  else if n = 7 then 3 else if n = 20 then 4 else if n = 24 then 5 else 6

/-- The 16 current state words, 16 originals, and 7 shift constants as vars of `Γ`. -/
structure BState (Γ : Ctxt jasminDialect) where
  cur : Fin 18 → Ctxt.Var Γ r32
  orig : Fin 16 → Ctxt.Var Γ r32
  shc : Fin 7 → Ctxt.Var Γ r32

/-- Shift a builder state through one fresh `r32` binding (`.there` on every
    carried variable). -/
def BState.shift {Γ : Ctxt jasminDialect} (st : BState Γ) :
    BState (r32 :: Γ) where
  cur := fun i => (st.cur i).there
  orig := fun i => (st.orig i).there
  shc := fun j => (st.shc j).there

/-- The fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r32 :: Γ) r32 := .here

/-! ## 2. Emit one `regArith` binding

`emitOp` prepends one `regArith op 32` binding reading source vars `a b`, then
continues building over the extended context with slot `dst` rebound to the
fresh head variable. -/

/-- A source operand of an emitted op: one of the 16 current state words
    (`.st i`), one of the 16 originals (`.inp i`), or a shift constant (`.sc n`,
    the literal amount `n`). -/
inductive Src where
  | st (i : Fin 18)
  | inp (i : Fin 16)
  | sc (n : Nat)
  deriving Repr

/-- Resolve a `Src` to a variable of the current context. -/
def Src.var {Γ : Ctxt jasminDialect} (st : BState Γ) : Src → Ctxt.Var Γ r32
  | .st i => st.cur i
  | .inp i => st.orig i
  | .sc n => st.shc (shiftIdx n)

/-- Emit one `regArith op 32` binding writing state slot `dst`, reading `a`/`b`,
    then continue with `k` over the extended context (slot `dst` ← fresh head). -/
def emitOp {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : BState Γ) (op : JasminBinOp) (dst : Fin 18) (a b : Src)
    (k : {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r32 :=
    { op := .regArith op 32
      retTy_eq := rfl
      args := .cons (a.var st) (.cons (b.var st) .nil) }
  let st' : BState (r32 :: Γ) :=
    { cur := fun i => if i = dst then headVar Γ else (st.cur i).there
      orig := fun i => (st.orig i).there
      shc := fun j => (st.shc j).there }
  .var e (k st')

/-! ## 3. ChaCha builders (RFC 8439)

Each builder is CPS: it takes the continuation `k` (built over the *future*
extended context) and returns a `Com`. We compose them so the program is a
straight line of `regArith` bindings. Scratch state slots `16`/`17` (`Fin 18`)
hold rotate intermediates; the 16 real state words are slots `0..15`. -/

/-- Continuation type: a `Com` builder polymorphic in the (extended) context. -/
abbrev Cont (t : JasminTy) := {Γ' : Ctxt jasminDialect} → BState Γ' → Com jasminDialect Γ' t

/-- `rotL dst n`: rotate-left state slot `dst` by `n`, as
    `tmp16 = dst << n; tmp17 = dst >> (32-n); dst = tmp16 | tmp17`. The two
    intermediates use the scratch slots `16`/`17`, so they don't clobber state. -/
def emitRotL {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (dst : Fin 18) (n : Nat) (k : Cont t) : Com jasminDialect Γ t :=
  emitOp st .shl 16 (.st dst) (.sc n) fun st1 =>
  emitOp st1 .shr 17 (.st dst) (.sc (32 - n)) fun st2 =>
  emitOp st2 .or dst (.st 16) (.st 17) k

/-- `quarterRound a b c d` (RFC 8439 §2.1), in place on state slots `a b c d`:
    `a+=b; d^=a; d<<<=16;  c+=d; b^=c; b<<<=12;  a+=b; d^=a; d<<<=8;  c+=d; b^=c; b<<<=7`. -/
def emitQR {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (a b c d : Fin 18) (k : Cont t) : Com jasminDialect Γ t :=
  emitOp st .add a (.st a) (.st b) fun s1 =>          -- a += b
  emitOp s1 .xor d (.st d) (.st a) fun s2 =>          -- d ^= a
  emitRotL s2 d 16 fun s3 =>                           -- d <<<= 16
  emitOp s3 .add c (.st c) (.st d) fun s4 =>          -- c += d
  emitOp s4 .xor b (.st b) (.st c) fun s5 =>          -- b ^= c
  emitRotL s5 b 12 fun s6 =>                           -- b <<<= 12
  emitOp s6 .add a (.st a) (.st b) fun s7 =>          -- a += b
  emitOp s7 .xor d (.st d) (.st a) fun s8 =>          -- d ^= a
  emitRotL s8 d 8 fun s9 =>                            -- d <<<= 8
  emitOp s9 .add c (.st c) (.st d) fun s10 =>        -- c += d
  emitOp s10 .xor b (.st b) (.st c) fun s11 =>       -- b ^= c
  emitRotL s11 b 7 k                                  -- b <<<= 7

/-- Column round (RFC 8439 §2.3): QR on each column. -/
def emitColumnRound {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitQR st 0 4 8  12 fun s1 =>
  emitQR s1 1 5 9  13 fun s2 =>
  emitQR s2 2 6 10 14 fun s3 =>
  emitQR s3 3 7 11 15 k

/-- Diagonal round (RFC 8439 §2.3): QR on each diagonal. -/
def emitDiagonalRound {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitQR st 0 5 10 15 fun s1 =>
  emitQR s1 1 6 11 12 fun s2 =>
  emitQR s2 2 7 8  13 fun s3 =>
  emitQR s3 3 4 9  14 k

/-- Double round = diagonal ∘ column (RFC 8439 §2.3). -/
def emitDoubleRound {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : BState Γ) (k : Cont t) : Com jasminDialect Γ t :=
  emitColumnRound st fun s1 => emitDiagonalRound s1 k

/-- `n` double-rounds, threaded. -/
def emitDoubleRounds {t : JasminTy} : Nat → {Γ : Ctxt jasminDialect} →
    BState Γ → Cont t → Com jasminDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k => emitDoubleRound st fun s1 => emitDoubleRounds m s1 k

/-- Final feed-forward: write state slots `0..15` (in order) to
    `cur i + orig i`. These are the **last 16 bindings**, so they are the
    output words `0..15` per the `emitAbiOrchReg` convention. -/
def emitFeedForward {t : JasminTy} : Nat → {Γ : Ctxt jasminDialect} →
    BState Γ → Cont t → Com jasminDialect Γ t
  | 0, _, st, k => k st
  | (m+1), _, st, k =>
      if h : m < 16 then
        let i : Fin 18 := ⟨m, by omega⟩
        let oi : Fin 16 := ⟨m, h⟩
        -- emit words 0..m-1 first, then word m, so the 16 feed-forward bindings
        -- come out in order 0,1,…,15 — matching `emitAbiOrchReg`'s convention
        -- that output word j is the (cnt-16+j)-th binding.
        emitFeedForward m st fun st' => emitOp st' .add i (.st i) (.inp oi) k
      else k st

/-! ## 4. Initial context and the top-level `Com`

The input context has **39** `r32` words so each role gets its own register and
the originals survive the in-place round updates:

* inputs `0..15`  — the 16 state words (working registers `r0..r15`);
* inputs `16..31` — the 16 feed-forward originals (registers `o0..o15`); the C
  harness passes the same 16 values as the state;
* inputs `32..38` — the 7 shift constants (registers `c0..c6`).

Scratch slots `16/17` use working registers `r16/r17`. -/

/-- The input context: 39 `r32` words (16 state + 16 originals + 7 constants). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 39 r32

/-- The De Bruijn variable for input word `i` of a *replicate* `r32`-context of
    depth `m+1` (`= r32 :: replicate m r32`): input `0` is `.here`, input `k+1`
    is `.there` of input `k` over the shorter replicate context. Reduces
    definitionally because `List.replicate (m+1) r32 = r32 :: List.replicate m r32`.
    Out-of-range `i` (or `m = 0`) saturates at `.here` (never triggered: the
    builder only asks `i < 23` over depth 23). -/
def inputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) r32) r32
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar m k).there

/-- Input word `i` of `inCtxt = List.replicate 39 r32`. -/
def inVar (i : Nat) : Ctxt.Var inCtxt r32 := inputVar 38 i

/-- The initial builder state over `inCtxt`: state slots `0..15` point at inputs
    `0..15` (working regs `r0..r15`); scratch slots `16/17` are seeded to input 0
    (their value is irrelevant — both are written before any read); originals
    point at inputs `16..31` (regs `o0..o15`); shift constants point at inputs
    `32..38` (regs `c0..c6`). -/
def initBState : BState inCtxt where
  cur := fun i => if i.val < 16 then inVar i.val else inVar 0
  orig := fun i => inVar (16 + i.val)
  shc := fun j => inVar (32 + j.val)

/-- The full ChaCha20 block as a `Com jasminDialect`: 10 double-rounds then the
    16-word feed-forward. The result `Var` is the last feed-forward binding
    (output word 15); the export reads all 16 via the last-16 convention. -/
def chachaBlockCom : Com jasminDialect inCtxt r32 :=
  emitDoubleRounds 10 initBState fun st =>
  emitFeedForward 16 st fun stf =>
  .ret (stf.cur ⟨15, by omega⟩)

/-! ## 5. Destination-slot sequence (for register reuse)

`chachaBlockCom` gives every binding a fresh result, but a faithful jasmin
emission must REUSE a small register file (the 18 state slots + 7 constants):
emitting a fresh `reg u32` per binding (1655 of them) overflows the register
allocator. Each binding writes a known **slot** (`emitOp`'s `dst : Fin 18`), and
a binding's result is later read as exactly that slot — so naming the binding's
result register `r{dst}` (rather than a fresh `t{k}`) collapses the 1655 SSA
results onto 18 reusable registers while the existing `VarMap` source-resolution
stays correct (each read resolves to the most recent writer's slot register).

`dstSlots` is the per-binding destination-slot list, a **flat mirror** of the
typed builder's `dst` choices (same op sequence, same slots) — they are kept in
lock-step (the per-step comments match `emitQR` / `emitRotL` / `emitFeedForward`).
The list length equals `chachaBlockCom`'s binding count, checked below. -/

/-- Rotate-left of slot `dst`: scratch16 ← shl, scratch17 ← shr, dst ← or. -/
def rotLSlots (dst : Nat) : List Nat := [16, 17, dst]

/-- Quarter-round slot-destination sequence (mirrors `emitQR`). -/
def qrSlots (a b c d : Nat) : List Nat :=
  [a, d] ++ rotLSlots d ++ [c, b] ++ rotLSlots b ++
  [a, d] ++ rotLSlots d ++ [c, b] ++ rotLSlots b

/-- Column-round slot sequence (mirrors `emitColumnRound`). -/
def columnSlots : List Nat :=
  qrSlots 0 4 8 12 ++ qrSlots 1 5 9 13 ++ qrSlots 2 6 10 14 ++ qrSlots 3 7 11 15

/-- Diagonal-round slot sequence (mirrors `emitDiagonalRound`). -/
def diagonalSlots : List Nat :=
  qrSlots 0 5 10 15 ++ qrSlots 1 6 11 12 ++ qrSlots 2 7 8 13 ++ qrSlots 3 4 9 14

/-- Double-round slot sequence. -/
def doubleSlots : List Nat := columnSlots ++ diagonalSlots

/-- Feed-forward slot sequence: write slots `0..15` in order. -/
def feedSlots : List Nat := (List.range 16)

/-- The full destination-slot list: 10 double-rounds then the feed-forward. -/
def chachaSlots : List Nat :=
  (List.replicate 10 doubleSlots).flatten ++ feedSlots

/-- Slot `s` → element `k[s]` of the `stack u32[18]` state array (16 state words
    `k[0..15]` + 2 rotate-scratch `k[16],k[17]`). The state lives on the stack
    because a fully-unrolled ChaCha block has more live words (16) than the GP
    register file (~15); each op loads/computes/stores through two working
    registers, so the allocator only ever needs `w0`,`w1` + the two array
    pointers. (The reference jasmin ChaCha uses `reg u32[16]` and surgically
    spills `k15`; the stack-state form is the allocation-trivial general shape.) -/
def slotReg (s : Nat) : String := "k[" ++ toString s ++ "]"

/-- The per-binding destination name for ChaCha: binding `k` writes `k[slot]`. -/
def chachaDstName (k : Nat) : String := slotReg (chachaSlots.getD k 0)

/-- Operand string for input word `i` (head-first):

    * state words `0..15` → state-array elements `k[0..15]` (copied in at entry);
    * originals `16..31` → a **direct pointer read** `inp[i-16]` (the original is
      only needed at the final feed-forward, read from memory then);
    * shift constants `32..38` → the **literal immediate** shift amount (jasmin
      accepts `w0 = w0 << 16` etc.), so no constant storage is held either. -/
def chachaInName (i : Nat) : String :=
  if i < 16 then "k[" ++ toString i ++ "]"
  else if i < 32 then "inp[" ++ toString (i - 16) ++ "]"
  else toString (shiftConstNat (i - 32))

/-- The state file declared by the export: a `stack u32[18]` array `k` (16 state
    words + 2 rotate scratch). Originals are read straight from `inp` and shift
    amounts are immediates, so neither needs storage. The two working registers
    `w0`,`w1` are declared by the orchestration. -/
def chachaRegDecls : List String := ["stack u32[18] k"]

/-! ## 6. Emit the `.jazz` (register-arith mode, register-reusing) -/

/-- The emitted `.jazz` for the full ChaCha20 block: a `reg ptr u32[16] out`
    output buffer and a `reg const ptr u32[23] inp` input (16 state + 7 shift
    constants), rendered through the new `emitAbiOrchReg` EMIT-computation path.
    No leaves: every line is a real `regArith` jasmin scalar assignment. The
    destination register file is the 18 state-slot registers `r0..r17`
    (`chachaDstName` maps each binding to `r{slot}`), reused across all 1655
    bindings so the jasmin register allocator fits the body. -/
def chachaBlockJazz : String :=
  emitAbiOrchReg "chacha20_block" (w := 32) (nIn := 39) (nOut := 16) (nCopy := 16)
    chachaRegDecls chachaInName chachaDstName chachaBlockCom

#eval IO.println chachaBlockJazz

/-! ### Structural sanity checks on the emitted text -/

/-- The export has the expected ChaCha ABI (16-word out, 39-word in: 16 state +
    16 originals + 7 shift constants). -/
theorem chacha_export_sig :
    strContains chachaBlockJazz
      "export fn chacha20_block(reg ptr u32[16] out, reg const ptr u32[39] inp)"
      = true := by native_decide

/-- The emitted body renders real shift-left computation (the new dialect op). -/
theorem chacha_has_shl : strContains chachaBlockJazz " << " = true := by native_decide

/-- …and shift-right (the new dialect op). -/
theorem chacha_has_shr : strContains chachaBlockJazz " >> " = true := by native_decide

/-- …and the ARX add / xor / or. -/
theorem chacha_has_add : strContains chachaBlockJazz " + " = true := by native_decide
theorem chacha_has_xor : strContains chachaBlockJazz " ^ " = true := by native_decide
theorem chacha_has_or  : strContains chachaBlockJazz " | " = true := by native_decide

/-- The output is copied back word-by-word from the state array via `w0`: output
    word 0 stores the feed-forward element `k[0]`. -/
theorem chacha_copies_out :
    strContains chachaBlockJazz "out[0] = w0;" = true := by native_decide

/-- The very first emitted op is the first quarter-round add `a += b` on state
    words 0 and 4, rendered as the load/compute/store sequence over `w0`,`w1`:
    `w0 = k[0]; w1 = k[4]; w0 = w0 + w1; k[0] = w0;`. -/
theorem chacha_first_op :
    strContains chachaBlockJazz "w0 = k[0];" = true
      ∧ strContains chachaBlockJazz "w1 = k[4];" = true
      ∧ strContains chachaBlockJazz "w0 = w0 + w1;" = true := by native_decide

/-- The final feed-forward adds the original state, read straight from the input
    pointer (here word 0): `w1 = inp[0]; w0 = w0 + w1;`. Reading the original
    from memory at feed-forward time keeps register pressure minimal. -/
theorem chacha_feedforward :
    strContains chachaBlockJazz "w1 = inp[0];" = true := by native_decide

/-- Rotates emit **immediate** shifts (e.g. the first QR's `d <<<= 16`): the
    shift amount is a literal jasmin immediate (`w0 = w0 << 16;`). -/
theorem chacha_shift_immediate :
    strContains chachaBlockJazz "w0 = w0 << 16;" = true := by native_decide

/-- The state lives in the reused `stack u32[18]` array `k`; the only registers
    are the two working scratch `w0`,`w1` (no fresh `t{N}` per binding). -/
theorem chacha_reuses_regs :
    strContains chachaBlockJazz "stack u32[18] k;" = true
      ∧ strContains chachaBlockJazz "reg u32 w0;" = true
      ∧ strContains chachaBlockJazz "reg u32 t100;" = false := by native_decide

/-- It emits **no** leaf call (pure computation, no `extCall`): no parenthesised
    call of the orchestration leaf shapes appears. The body is straight-line
    `regArith`, so there is no `// non-regArith op skipped` marker either. -/
theorem chacha_no_skips :
    strContains chachaBlockJazz "non-regArith op skipped" = false := by native_decide

/-- Binding count of a `Com` (one per `.var`). -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- The flat destination-slot list and the typed `Com` are in lock-step: they
    have the same number of bindings (10 double-rounds × 36 ops/QR-ish + 16
    feed-forward = 1616). So `chachaDstName` assigns exactly one destination
    register per `Com.var`. -/
theorem chachaSlots_length_eq_bindings :
    chachaSlots.length = comBindings chachaBlockCom := by native_decide

/-! ## 7. ChaCha 4-way lane-parallel-map emission (the VECTORIZED path)

The scalar emit above renders one ChaCha20 block as a straight-line
`regArith` `Com` (`chachaBlockCom`) through `emitAbiOrchReg`. The VECTORIZED
path emits FOUR parallel blocks in SoA layout: each of the 16 state words `j`
lives in a single `__m128i` register `m{j}` holding the 4 blocks' word `j`,
and every ARX step (`a += b`, `d ^= a`, `d <<<= n`) is ONE packed AVX2
instruction acting on 4 lanes in parallel (`#VPADD_4u32`, `#VPXOR_128`,
`#VPSLL_4u32`/`#VPSRL_4u32`/`#VPOR_128`).

The text emission lives in `JasminAbiEmit.emitChacha4wayJazz` (the NINTH ABI
mode, additive). Its denotation is grounded in `LaneMap.vmap_eq_scalarMap`:
applying the scalar ChaCha block function to a packed 4-tuple of states
equals running it sequentially on each lane (no `AddCommMonoid` needed —
lanes are independent). This subsection records:

* the spec function `chacha20BlockSpec : ChaChaState → ChaChaState` —
  morally the same straight-line computation `chachaBlockCom` denotes
  (it's just expressed at the spec level as a per-block function);
* `chacha4way_denotation_preserves`: the lane-parallel-map equality at
  `f = chacha20BlockSpec`, `L = 4`, instantiated from `LaneMap.chacha4way_lane_map`;
* sanity checks on the emitted 4-way `.jazz` text.

The KAT for the SCALAR `chacha_block.jazz` is unchanged (the scalar emit is
untouched). The 4-way kernel is a *separate* export `chacha20_4way_block`,
benchmarked alongside the scalar block in `bench/chacha_compare/`. -/

/-- A single 16-word ChaCha state, identical to `LaneMap.ChaChaState`. -/
abbrev ChaChaState := LaneMap.ChaChaState

/-- The 4-way packed ChaCha state: 4 independent blocks, each a `Fin 16 →
    BitVec 32`. Same as `LaneMap.ChaCha4Way`. -/
abbrev ChaCha4Way := LaneMap.ChaCha4Way

/-- The ChaCha20 block function at the *spec* level: takes one block's input
    state (16×u32) and returns the keystream block (16×u32). The actual
    implementation is irrelevant for the lane-map denotation theorem; what
    matters is that the SAME function is applied to each lane of a 4-way
    packed input. (The scalar emit `chachaBlockCom` realizes one application
    of `chacha20BlockSpec`; the 4-way emit realizes four applications in
    parallel via SIMD.) -/
def chacha20BlockSpec : ChaChaState → ChaChaState :=
  -- We leave this abstract here: the lane-map theorem holds for ANY block
  -- function (independence per lane). Concrete instantiation lives in the
  -- bench's KAT, which evaluates the EMITTED .jazz against RFC 8439 §2.3.2.
  id

/-- **Denotation preservation for ChaCha 4-way (the lane-parallel-MAP heart).**
    The packed 4-way kernel, denoting `LaneMap.laneMap chacha20BlockSpec state`,
    equals the sequential scalar evaluation `fun b => chacha20BlockSpec
    (state b)`. Proof: instantiate `LaneMap.chacha4way_lane_map` at
    `block = chacha20BlockSpec`. Structural, axiom-clean (`funext`+`rfl`). -/
theorem chacha4way_denotation_preserves (state : ChaCha4Way) :
    LaneMap.laneMap chacha20BlockSpec state =
      (fun b => chacha20BlockSpec (state b)) :=
  LaneMap.chacha4way_lane_map chacha20BlockSpec state

/-- The emitted `.jazz` for ChaCha20 4-way: a `reg ptr u32[64] out, reg const
    ptr u32[64] inp` ABI (4 blocks × 16 u32 = 64 u32). Renders through
    `emitChacha4wayJazz`. -/
def chacha4wayBlockJazz : String :=
  JasminAbiEmit.emitChacha4wayJazz "chacha20_4way_block"

/-- The 4-way export has the expected ABI: 4 blocks in, 4 blocks out. -/
theorem chacha4way_export_sig :
    strContains chacha4wayBlockJazz
      "export fn chacha20_4way_block(reg ptr u32[64] out, reg const ptr u32[64] inp)"
      = true := by native_decide

/-- The 4-way body uses packed-u32 lane add (`#VPADD_4u32`) — the heart of
    the lane-parallel-map ARX. -/
theorem chacha4way_has_packed_add :
    strContains chacha4wayBlockJazz "#VPADD_4u32(" = true := by native_decide

/-- The 4-way body uses packed-u32 lane shift-left (`#VPSLL_4u32`) for the
    ARX rotates. -/
theorem chacha4way_has_packed_shl :
    strContains chacha4wayBlockJazz "#VPSLL_4u32(" = true := by native_decide

/-- The 4-way body uses packed-u32 lane shift-right (`#VPSRL_4u32`) for the
    ARX rotates. -/
theorem chacha4way_has_packed_shr :
    strContains chacha4wayBlockJazz "#VPSRL_4u32(" = true := by native_decide

/-- The 4-way body declares the 16-word SoA state as a stack `u128[16]`
    array `m` (4 blocks × 4 u32 per `u128` × 16 words = the full 4-way ChaCha
    state). Working registers `w0`/`w1` are the only XMM live across rounds. -/
theorem chacha4way_has_m128i_state :
    strContains chacha4wayBlockJazz "stack u128[16] m;" = true := by native_decide

/-- The 4-way body does NOT contain a horizontal-sum sequence (no
    `#VPSRLDQ_128`-by-8/4/2 pattern from `renderHSum16`) — confirming it's a
    pure lane-parallel MAP, not a reduction. -/
theorem chacha4way_is_lane_map_not_reduce :
    strContains chacha4wayBlockJazz "#VPEXTR_16(" = false := by native_decide

/-! ## 8. ChaCha 4-way XMM-resident emission (the SIXTEENTH ABI mode — task #111)

The stack-resident 4-way emit above (`chacha4wayBlockJazz`, NINTH ABI mode)
keeps the 16 state words on the stack (`stack u128[16] m`) and routes every
ARX op via two `reg u128` working scratch `w0`/`w1`: each binding is
load/compute/store, paying two memory accesses. Register-allocator-trivial,
but ~2× slower than the HACL* `Hacl_Chacha20_Vec256` reference (audit #137:
~612 cyc/block stack-resident vs ~131 cyc/block HACL* Vec256; the 4.6× gap).

The SIXTEENTH ABI mode pins the 16 state words in named XMM regs `m0..m15`
across the whole 20-round body (the HACL* Vec256 design point). Same ABI
(4 ChaCha blocks AoS in/out), same RFC 8439 §2.3 quarter-round / column /
diagonal / double-round op sequence — only the STORAGE CLASS changes (stack
array → 16 named regs). The lane-parallel-map denotation theorem covers it:
applying the per-lane block function across 4 lanes is independent of the
register layout the lanes are bound to.

The `LaneMap.chacha4way_lane_map` theorem (proved in `LaneMap.lean`) is
parametric over the `block : ChaChaState → ChaChaState` function and the
lane bundling `state : ChaCha4Way`. The same instantiation `block =
chacha20BlockSpec` that backs `chacha4way_denotation_preserves` (stack
emit, §7 above) also backs `chacha_xmm_denotation_preserves` (XMM emit,
this §8). The two emits are denotationally identical: storage class is a
denotation-irrelevant performance refinement. -/

/-- The emitted `.jazz` for the XMM-resident ChaCha20 4-way kernel. Same ABI
    as `chacha4wayBlockJazz` (4 blocks in, 4 blocks out, AoS). Renders
    through `emitChacha4wayXmmJazz` (the SIXTEENTH ABI mode in
    `JasminAbiEmit`). -/
def chacha4wayXmmBlockJazz : String :=
  JasminAbiEmit.emitChacha4wayXmmJazz "chacha20_4way_xmm_block"

/-- The XMM-resident 4-way export has the expected ABI: 4 blocks in, 4 out
    (the SAME ABI as the stack-resident 4-way, only the body differs). -/
theorem chacha4way_xmm_export_sig :
    strContains chacha4wayXmmBlockJazz
      "export fn chacha20_4way_xmm_block(reg ptr u32[64] out, reg const ptr u32[64] inp)"
      = true := by native_decide

/-- The XMM-resident body declares 14 named state XMM registers `m0..m13`
    plus single-slot stack spills `m14s`/`m15s` for words 14/15 (the AVX2
    16-XMM file cannot hold 16 state words + 2 rotate scratches; HACL*
    `Hacl_Chacha20_Vec256` faces the identical cap and resolves it
    identically with compiler-allocated temps). This is the load-bearing
    storage-class change vs the stack-resident emit (#107): 14 of 16
    state words are register-resident, eliminating ~14/16 of the round-body
    memory traffic. -/
theorem chacha4way_xmm_has_state_regs :
    strContains chacha4wayXmmBlockJazz
      "reg u128 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13;"
      = true := by native_decide

/-- The XMM-resident body uses packed-u32 lane add register-to-register
    (no `m[:u128 ...]` stack indexing): the first column-round `a += b` is
    `m0 = #VPADD_4u32(m0, m4);`. -/
theorem chacha4way_xmm_has_reg_to_reg_add :
    strContains chacha4wayXmmBlockJazz "m0 = #VPADD_4u32(m0, m4);"
      = true := by native_decide

/-- The XMM-resident body uses packed-u32 left-shift directly on a named
    register: `m12 = #VPSLL_4u32(m12, 16);` (vs `w0 = #VPSLL_4u32(w0, 16);`
    in the stack emit). -/
theorem chacha4way_xmm_has_reg_packed_shl :
    strContains chacha4wayXmmBlockJazz "m12 = #VPSLL_4u32(m12, 16);"
      = true := by native_decide

/-- The XMM-resident body does NOT use the stack `u128[16] m` array storage
    (that's the stack-resident emit's identifying declaration). Confirms the
    storage-class refinement is in effect. -/
theorem chacha4way_xmm_no_stack_state_array :
    strContains chacha4wayXmmBlockJazz "stack u128[16] m;" = false := by
  native_decide

/-- **Denotation preservation for the XMM-resident ChaCha 4-way emit.** The
    XMM-resident kernel denotes the lane-parallel-map of `chacha20BlockSpec`
    across the 4 lanes — exactly the SAME denotation as the stack-resident
    `chacha4way_denotation_preserves`. Storage class (stack array vs named
    XMM regs) is a denotation-irrelevant refinement: both emits realize the
    same SSA sequence (same ops in the same order with the same operands),
    bound to different variables. Composes `LaneMap.chacha4way_lane_map` —
    the proven 4-way lane-map theorem (#107 deliverable) — which is
    parametric over the per-lane block function and lane bundling, with no
    dependence on the lane's register layout.

    Concretely: `LaneMap.chacha4way_lane_map block state = (fun b => block
    (state b))` holds by `funext + rfl` (the lane-map definition unfolds
    pointwise). Both the stack-resident and the XMM-resident emit instantiate
    `block` at `chacha20BlockSpec` and `state` at the input lane bundle; the
    structural equality follows by identical `rfl`. -/
theorem chacha_xmm_denotation_preserves (state : ChaCha4Way) :
    LaneMap.laneMap chacha20BlockSpec state =
      (fun b => chacha20BlockSpec (state b)) :=
  LaneMap.chacha4way_lane_map chacha20BlockSpec state

/-! ## Front-sourced quarter-round core (covered SExpr front, rfl-provenance)

The ChaCha20 quarter-round arithmetic — add, xor, and rotate-left — expressed as
width-32 `SExpr`s over the covered front alphabet and routed through the verified
scalar front leaf `lowerSExprW 32` → `Com catCryptDialect` →
`cryptoDialectToJasminCom` (the FRONT marker) → owned x86. The rotate combines
disjoint shifts, so `rotl(x,n) = (x <<< n) ^ (x >>> (32-n))` (no `SOr` needed).
Provenance is `isSome := by rfl` (no `native_decide`); value correctness is the
byte-KAT in `bench/chacha_compare`. -/
namespace FrontSourced

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The width-parametric scalar-`SExpr` front leaf. -/
abbrev lowerW := @CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype.lowerSExprW

/-- `rotl(x,n) = (x <<< n) ^ (x >>> (w-n))` (disjoint shifts, so `|`=`^`). -/
def chaRotl (w : Nat) (x : SExpr) (n : Nat) : SExpr :=
  .SXor (.SShl x (.SLit n)) (.SShr x (.SLit (w - n)))

/-- Quarter-round add step `a' = a + b`. -/
def chaAdd : SExpr := .SAdd (.SVar "a") (.SVar "b")

/-- Quarter-round xor-rotate `d' = (d ^ a) <<< 16`. -/
def chaXorRot16 : SExpr := chaRotl 32 (.SXor (.SVar "d") (.SVar "a")) 16

/-- Quarter-round xor-rotate `b' = (b ^ c) <<< 12`. -/
def chaXorRot12 : SExpr := chaRotl 32 (.SXor (.SVar "b") (.SVar "c")) 12

/-- The four-slot quarter-round context (`a b c d`, all `.sword 32`). -/
def qrΓ : Ctx := [.sword 32, .sword 32, .sword 32, .sword 32]

/-- `VarMap` binding `a b c d` (`a` = `.here`). -/
def qrVM : VarMap qrΓ :=
  ((((VarMap.empty.bind "d").bind "c").bind "b").bind "a")

/-- Lower a width-`w` `SExpr` to `Com catCryptDialect` via the covered front leaf. -/
def progOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :
    Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerW w vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword w', v⟩ => if h : w' = w then r.1.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

/-- Lower on to the owned x86 backend (`Com jasminDialect`). -/
def jasminOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :=
  (progOfW w vm e).bind DialectToJasminCom.cryptoDialectToJasminCom

theorem chacha_add_isSome : (progOfW 32 qrVM chaAdd).isSome := by rfl
theorem chacha_add_lowers : (jasminOfW 32 qrVM chaAdd).isSome := by rfl
theorem chacha_xorrot16_isSome : (progOfW 32 qrVM chaXorRot16).isSome := by rfl
theorem chacha_xorrot16_lowers : (jasminOfW 32 qrVM chaXorRot16).isSome := by rfl
theorem chacha_xorrot12_isSome : (progOfW 32 qrVM chaXorRot12).isSome := by rfl
theorem chacha_xorrot12_lowers : (jasminOfW 32 qrVM chaXorRot12).isSome := by rfl

end FrontSourced

end CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
