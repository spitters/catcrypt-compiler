/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Plonky3 Fibonacci-AIR trace generation emitted as a callable owned leaf (x86)

GAP 1 of the Plonky3 "fully-emit" effort: the AIR / trace-generation FRONT.
`Plonky3AirEmit.lean` already MODELS the trace recurrence (`fibTrace`) and KATs
its column-1 values (`kat_fibonacci_trace_values`), and emits the
constraint-sweep `airJazz`. But the TRACE GENERATION recurrence itself — the
`bbAdd` chain `trace[0]=(0,1)`, `trace[i]=(prev.b, prev.a+prev.b)` — was modeled
and KAT'd, NOT emitted as a callable leaf. The prover front therefore relied on
hand-written Rust/C glue to produce the trace before handing it to the (emitted)
constraint evaluator.

This file closes that: it emits `fib_trace_gen_rc` as a `Com jasminDialect` leaf
through the verified register-arith emit path (`JasminAbiEmit.emitAbiOrchReg`,
the same path the BabyBear NTT layer uses, `Plonky3NttLayerEmit`). The body is a
fixed-height unroll of the BabyBear `bbAdd` recurrence — pure field arithmetic,
NO opaque leaf, NO hardware `%`.

## The recurrence as a `Com`

`fibTrace` (from `Plonky3AirEmit`) is: row 0 = `(0, 1)`; row `i` =
`(prev.b, bbAdd prev.a prev.b)`. So column 0 of row `i` is `prev.b` and column 1
is `bbAdd prev.a prev.b`. The leaf carries the running pair `(a, b)` in two
working slots; each step emits

  nb = bbAdd a b      (one BabyBear add: `s = a + b; csub by P`)
  na = b              (copy)
  (a, b) := (na, nb)

and writes the produced row `(a, b)` to the output. The single field op per step
is `bbAdd`, whose branchless conditional subtract is the SAME csub idiom the NTT
butterfly uses: `s = (a+b) - P; m = s >> 63; m = 0 - m; m = m & P; out = s + m`
(inputs `a, b < P`, so `a + b < 2P` — one csub canonicalises).

## ABI

`export fn fib_trace_gen_rc(reg ptr u64[20] out, reg const ptr u64[5] inp)`:
the 5 input words are `[a0, b0, P, 0, 63]` (seed `(a0, b0) = (0, 1)` and the
csub constants `P`, `0`, and the shift amount `63`). Only `a0, b0` are copied
into registers; `P, 0, 63` resolve to their immediates. The 20 output words are
the height-10 trace `[a0, b0, a1, b1, …, a9, b9]` — exactly the rows of
`fibTrace 10`, whose column-1 values are pinned by `kat_fibonacci_trace_values`.

## Reference / KAT

Ground truth is `Plonky3AirEmit.fibTrace 10` (column 1 = the first ten Fibonacci
numbers, `kat_fibonacci_trace_values`). The C KAT
(`fib_trace_gen_kat.c`) reproduces the same `bbAdd` recurrence and byte-matches
the emitted leaf's full 20-word output against it; the ARM sibling
(`../SSProve-lean/bench/arm_compare/plonky3_air_a64_emit.lean`) emits the same recurrence as an
A64 `BOp` block and KATs it under qemu.

Invoke: `lake env lean bench/plonky3_compare/fib_trace_gen_emit.lean`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FibTraceGenEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Constant indices into the `con` field: `0 ↦ P`, `1 ↦ 0`, `2 ↦ 63`. -/
def cP : Fin 3 := ⟨0, by omega⟩
def cZero : Fin 3 := ⟨1, by omega⟩
def cSh63 : Fin 3 := ⟨2, by omega⟩

/-- Fresh head variable of an extended context. -/
def headVar (Γ : Ctxt jasminDialect) : Ctxt.Var (r64 :: Γ) r64 := .here

/-! ## 1. The height-10 trace `Com`

`fibTrace 10` = rows `r0 .. r9` with `r0 = (0,1)` and
`r_{i+1} = (r_i.b, bbAdd r_i.a r_i.b)`. We need to WRITE every row to the output
in order. Output word layout is `[a0,b0, a1,b1, …, a9,b9]` (20 words). The
emit convention (`emitAbiOrchReg`) takes the OUTPUT words as the LAST `nOut`
bindings' destination slots, in order. So after running all the steps we append a
finalize block that re-materialises each row's `(a, b)` in order as the last 20
bindings.

To do that without recomputing, we keep every produced row alive in its own pair
of slots — but that needs 20 slots. Simpler and lock-step with the spec: emit the
steps writing into 10 (a,b) slot-pairs directly. We special-case the builder to
use 20 row slots + 2 scratch. -/

/-- A wide state holding all `2*10 = 20` row words plus 2 scratch + 2 const. -/
structure WState (Γ : Ctxt jasminDialect) where
  row : Fin 20 → Ctxt.Var Γ r64   -- a0,b0,a1,b1,…,a9,b9
  scr : Fin 2 → Ctxt.Var Γ r64    -- x, q
  con : Fin 3 → Ctxt.Var Γ r64    -- P, 0, 63

inductive WSrc where
  | rw (i : Fin 20)
  | sc (i : Fin 2)
  | cn (j : Fin 3)
  | sh63
  deriving Repr

def WSrc.var {Γ : Ctxt jasminDialect} (st : WState Γ) : WSrc → Ctxt.Var Γ r64
  | .rw i => st.row i
  | .sc i => st.scr i
  | .cn j => st.con j
  | .sh63 => st.con cSh63

/-- One `regArith` binding into a row slot. -/
def emitRow {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : WState Γ) (op : JasminBinOp) (dst : Fin 20) (a b : WSrc)
    (k : {Γ' : Ctxt jasminDialect} → WState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64, retTy_eq := rfl
      args := .cons (a.var st) (.cons (b.var st) .nil) }
  let st' : WState (r64 :: Γ) :=
    { row := fun i => if i = dst then headVar Γ else (st.row i).there
      scr := fun i => (st.scr i).there
      con := fun j => (st.con j).there }
  .var e (k st')

/-- One `regArith` binding into a scratch slot. -/
def emitScr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : WState Γ) (op : JasminBinOp) (dst : Fin 2) (a b : WSrc)
    (k : {Γ' : Ctxt jasminDialect} → WState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64, retTy_eq := rfl
      args := .cons (a.var st) (.cons (b.var st) .nil) }
  let st' : WState (r64 :: Γ) :=
    { row := fun i => (st.row i).there
      scr := fun i => if i = dst then headVar Γ else (st.scr i).there
      con := fun j => (st.con j).there }
  .var e (k st')

abbrev WCont (t : JasminTy) :=
  {Γ' : Ctxt jasminDialect} → WState Γ' → Com jasminDialect Γ' t

/-- Emit row `i+1` from row `i`: `a_{i+1} = b_i`, `b_{i+1} = bbAdd a_i b_i`.
    Row `i` occupies slots `2i` (a) and `2i+1` (b); row `i+1` is `2i+2`, `2i+3`.
    Writes `b_{i+1}` (the bbAdd) FIRST into scratch, then commits both rows. -/
def emitNextRow {t : JasminTy} {Γ : Ctxt jasminDialect}
    (i : Fin 9) (st : WState Γ) (k : WCont t) : Com jasminDialect Γ t :=
  let ai : Fin 20 := ⟨2 * i.val, by omega⟩
  let bi : Fin 20 := ⟨2 * i.val + 1, by omega⟩
  let aN : Fin 20 := ⟨2 * i.val + 2, by omega⟩
  let bN : Fin 20 := ⟨2 * i.val + 3, by omega⟩
  let x : Fin 2 := ⟨0, by omega⟩
  let q : Fin 2 := ⟨1, by omega⟩
  -- bbAdd a_i b_i into scratch q:
  emitScr st  .add x (.rw ai) (.rw bi) fun s1 =>   -- x = a_i + b_i
  emitScr s1  .sub x (.sc x) (.cn cP) fun s2 =>    -- x = x - P
  emitScr s2  .shr q (.sc x) .sh63 fun s3 =>       -- q = x >> 63
  emitScr s3  .sub q (.cn cZero) (.sc q) fun s4 => -- q = 0 - q
  emitScr s4  .and q (.sc q) (.cn cP) fun s5 =>    -- q = q & P
  emitScr s5  .add q (.sc x) (.sc q) fun s6 =>     -- q = bbReduce(a+b) = b_{i+1}
  -- commit: a_{i+1} = b_i ; b_{i+1} = q
  emitRow s6  .add aN (.rw bi) (.cn cZero) fun s7 =>
  emitRow s7  .add bN (.sc q) (.cn cZero) k

/-! ## 5. Initial context and top-level `Com`

Input context: 4 `r64` words `[a0, b0, P, 0]`. Row slots `0` (a0) and `1` (b0)
are seeded from inputs `0, 1`; the constants `P, 0` from inputs `2, 3`; row
slots `2..19` are seeded to input 0 (written before read). The shift amount `63`
is an immediate (declared input word `4` in `inName`, resolved to its literal). -/

/-- Input context: 5 `r64` words `[a0, b0, P, 0, 63]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate 5 r64

/-- De Bruijn variable for input word `i` of a context of `m+1` words. -/
def inputVar : (m : Nat) → Nat → @Ctxt.Var jasminDialect (List.replicate (m+1) r64) r64
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inputVar m k).there

def inVar (i : Nat) : Ctxt.Var inCtxt r64 := inputVar 4 i

/-- Initial wide state: a0←inp0, b0←inp1, all other rows←inp0; scratch←inp0;
    const P←inp2, 0←inp3, 63←inp4. -/
def initWState : WState inCtxt where
  row := fun i => if i.val = 0 then inVar 0 else if i.val = 1 then inVar 1 else inVar 0
  scr := fun _ => inVar 0
  con := fun j => inVar (2 + j.val)

/-- Finalize: re-emit the 20 row words in order as the last 20 bindings (each an
    `add row 0`), so `emitAbiOrchReg`'s last-`nOut` convention copies them to the
    output buffer `[a0,b0,…,a9,b9]`. The final binding returns. -/
def finalize {Γ : Ctxt jasminDialect} (st : WState Γ) : Com jasminDialect Γ r64 :=
  emitRow st .add ⟨0, by omega⟩ (.rw ⟨0, by omega⟩) (.cn cZero) fun s0 =>
  emitRow s0 .add ⟨1, by omega⟩ (.rw ⟨1, by omega⟩) (.cn cZero) fun s1 =>
  emitRow s1 .add ⟨2, by omega⟩ (.rw ⟨2, by omega⟩) (.cn cZero) fun s2 =>
  emitRow s2 .add ⟨3, by omega⟩ (.rw ⟨3, by omega⟩) (.cn cZero) fun s3 =>
  emitRow s3 .add ⟨4, by omega⟩ (.rw ⟨4, by omega⟩) (.cn cZero) fun s4 =>
  emitRow s4 .add ⟨5, by omega⟩ (.rw ⟨5, by omega⟩) (.cn cZero) fun s5 =>
  emitRow s5 .add ⟨6, by omega⟩ (.rw ⟨6, by omega⟩) (.cn cZero) fun s6 =>
  emitRow s6 .add ⟨7, by omega⟩ (.rw ⟨7, by omega⟩) (.cn cZero) fun s7 =>
  emitRow s7 .add ⟨8, by omega⟩ (.rw ⟨8, by omega⟩) (.cn cZero) fun s8 =>
  emitRow s8 .add ⟨9, by omega⟩ (.rw ⟨9, by omega⟩) (.cn cZero) fun s9 =>
  emitRow s9 .add ⟨10, by omega⟩ (.rw ⟨10, by omega⟩) (.cn cZero) fun s10 =>
  emitRow s10 .add ⟨11, by omega⟩ (.rw ⟨11, by omega⟩) (.cn cZero) fun s11 =>
  emitRow s11 .add ⟨12, by omega⟩ (.rw ⟨12, by omega⟩) (.cn cZero) fun s12 =>
  emitRow s12 .add ⟨13, by omega⟩ (.rw ⟨13, by omega⟩) (.cn cZero) fun s13 =>
  emitRow s13 .add ⟨14, by omega⟩ (.rw ⟨14, by omega⟩) (.cn cZero) fun s14 =>
  emitRow s14 .add ⟨15, by omega⟩ (.rw ⟨15, by omega⟩) (.cn cZero) fun s15 =>
  emitRow s15 .add ⟨16, by omega⟩ (.rw ⟨16, by omega⟩) (.cn cZero) fun s16 =>
  emitRow s16 .add ⟨17, by omega⟩ (.rw ⟨17, by omega⟩) (.cn cZero) fun s17 =>
  emitRow s17 .add ⟨18, by omega⟩ (.rw ⟨18, by omega⟩) (.cn cZero) fun s18 =>
  emitRow s18 .add ⟨19, by omega⟩ (.rw ⟨19, by omega⟩) (.cn cZero) fun s19 =>
  .ret (s19.row ⟨19, by omega⟩)

/-- The full height-10 trace `Com`: nine `emitNextRow` steps then `finalize`. -/
def traceCom : Com jasminDialect inCtxt r64 :=
  emitNextRow ⟨0, by omega⟩ initWState fun s1 =>
  emitNextRow ⟨1, by omega⟩ s1 fun s2 =>
  emitNextRow ⟨2, by omega⟩ s2 fun s3 =>
  emitNextRow ⟨3, by omega⟩ s3 fun s4 =>
  emitNextRow ⟨4, by omega⟩ s4 fun s5 =>
  emitNextRow ⟨5, by omega⟩ s5 fun s6 =>
  emitNextRow ⟨6, by omega⟩ s6 fun s7 =>
  emitNextRow ⟨7, by omega⟩ s7 fun s8 =>
  emitNextRow ⟨8, by omega⟩ s8 finalize

/-! ## 6. Destination-slot list / register file (lock-step with `traceCom`)

Each `emitNextRow` writes 8 bindings: scratch `x,x,q,q,q,q` then rows `aN,bN`.
After nine steps (72 bindings) the finalize writes 20. The slot→register map:
row slot `s` → `r{s}`; scratch `x`→`r20`, `q`→`r21`. -/

/-- The destination-row slots for `emitNextRow i` (the 8 writes). Scratch slots
    are 20 (`x`) and 21 (`q`); row slots are `2i+2` (aN) and `2i+3` (bN). -/
def nextRowSlots (i : Nat) : List Nat :=
  [20, 20, 21, 21, 21, 21] ++ [2 * i + 2, 2 * i + 3]

/-- The full destination-slot list: nine steps then 20 finalize copies. -/
def traceSlots : List Nat :=
  ((List.range 9).flatMap nextRowSlots) ++ (List.range 20)

/-- Slot `s` → its operand name. The 20 row slots `0..19` live in the spill-safe
    `stack u64[20] s` array (`s[slot]`); the two scratch slots `20, 21` are the
    registers `r0, r1`. Keeping the 20 rows in a stack array (not 20 live
    registers) is what lets jasminc's register allocator close — only `r0`, `r1`
    and the emit's `w0`/`w1` scratch are ever simultaneously live. -/
def slotReg (s : Nat) : String :=
  if s < 20 then "s[" ++ toString s ++ "]" else "r" ++ toString (s - 20)

def traceDstName (k : Nat) : String := slotReg (traceSlots.getD k 0)

/-- Operand string for input word `i`:
    * inputs `0, 1` (`a0`, `b0`) → stack slots `s[0]`, `s[1]` (copied in);
    * input `2` (`P`) → the literal `2013265921`;
    * input `3` (`0`) → the literal `0`;
    * input `4` (`63`, the shift) → the literal `63`.

    The shift amount `63` is referenced by the `.sh63` operand, which resolves
    (via `WSrc.var`) to the `con cSh63` variable; its declared input slot is
    mapped to the immediate `63` here. The constants `P`, `0`, `63` are declared
    input words `2, 3, 4` and resolve to their literals — the NTT-layer
    convention. -/
def traceInName (i : Nat) : String :=
  if i = 0 then "s[0]"
  else if i = 1 then "s[1]"
  else if i = 2 then "2013265921"
  else if i = 3 then "0"
  else "63"  -- input word 4: the shift amount, an immediate

/-- The state file: one `stack u64[20]` row array plus the two scratch
    registers `r0`, `r1`. -/
def traceRegDecls : List String :=
  ["stack u64[20] s", "reg u64 r0", "reg u64 r1"]

/-! ## 7. Emit the `.jazz`

`nCopy = 2`: the seed `(a0, b0)` is copied into `s[0], s[1]`; the constants
`P, 0, 63` are immediates. -/

/-- Number of declared inputs: `[a0, b0, P, 0, 63]`. The constants `P, 0, 63` are
    real declared input words (so the body's `con` operands resolve to their
    immediate strings), exactly the NTT-layer convention. -/
def nInputs : Nat := 5

def traceJazz : String :=
  emitAbiOrchReg "fib_trace_gen_rc" (w := 64) (nIn := nInputs) (nOut := 20)
    (nCopy := 2) traceRegDecls traceInName traceDstName traceCom

/-! ## 8. Structural sanity checks -/

/-- The export has the trace-gen ABI (20-word out, 4-word in). -/
theorem trace_export_sig :
    strContains traceJazz
      "export fn fib_trace_gen_rc(reg ptr u64[20] out, reg const ptr u64[5] inp)"
      = true := by native_decide

/-- The BabyBear prime appears as an immediate (the csub constant). -/
theorem trace_has_prime :
    strContains traceJazz "2013265921" = true := by native_decide

/-- No opaque leaf — every binding is a regArith. -/
theorem trace_no_skips :
    strContains traceJazz "non-regArith op skipped" = false := by native_decide

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- Slot list and typed `Com` are lock-step: 9 steps × 8 + 20 finalize = 92. -/
theorem traceSlots_length_eq_bindings :
    traceSlots.length = comBindings traceCom := by native_decide

/-- Every binding of `traceCom` is a `regArith` op (by-construction
    `leaf.denote = spec`). -/
def allRegArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body =>
    (match e.op with | .regArith _ _ => true | _ => false) && allRegArith body

theorem trace_is_regarith_only : allRegArith traceCom = true := by native_decide

/-! ## 9. The AIR transition-constraint evaluator as a callable leaf

`Plonky3AirEmit.evalTransition` over a single row pair `(cur, next)` is the two
Fibonacci-AIR transition constraints:

  c0 = bbSub next.a cur.b                 (`FIB_NEXT_A`)
  c1 = bbSub next.b (bbAdd cur.a cur.b)   (`FIB_NEXT_B`)

both `0` exactly when the row pair is consistent with the AIR (the soundness
witness `kat_fib_trace_satisfies_air` checks). We emit it as a callable leaf
`fib_air_transition_rc` through the SAME regArith path. `bbSub a b` is the
branchless `a + P - b` followed by one csub (inputs `a, b < P` ⇒ `a+P-b ∈
[1, 2P)`); `bbAdd` is the csub from the trace-gen body above.

State slots: `0..3` = the row pair `(ca, cb, na, nb)`; `4` = `c0`, `5` = `c1`
(the two outputs, emitted LAST); `6` = `x`, `7` = `q` scratch. Inputs
`[ca, cb, na, nb, P, 0, 63]` (7 words); the four row words copied in, the three
constants immediates. -/

structure CState (Γ : Ctxt jasminDialect) where
  slot : Fin 8 → Ctxt.Var Γ r64    -- ca,cb,na,nb,c0,c1,x,q
  con  : Fin 3 → Ctxt.Var Γ r64    -- P, 0, 63

inductive CSrc where
  | sl (i : Fin 8)
  | cn (j : Fin 3)
  | sh63
  deriving Repr

def CSrc.var {Γ : Ctxt jasminDialect} (st : CState Γ) : CSrc → Ctxt.Var Γ r64
  | .sl i => st.slot i
  | .cn j => st.con j
  | .sh63 => st.con cSh63

def emitC {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : CState Γ) (op : JasminBinOp) (dst : Fin 8) (a b : CSrc)
    (k : {Γ' : Ctxt jasminDialect} → CState Γ' → Com jasminDialect Γ' t) :
    Com jasminDialect Γ t :=
  let e : Expr jasminDialect Γ r64 :=
    { op := .regArith op 64, retTy_eq := rfl
      args := .cons (a.var st) (.cons (b.var st) .nil) }
  let st' : CState (r64 :: Γ) :=
    { slot := fun i => if i = dst then headVar Γ else (st.slot i).there
      con := fun j => (st.con j).there }
  .var e (k st')

abbrev CCont (t : JasminTy) := {Γ' : Ctxt jasminDialect} → CState Γ' → Com jasminDialect Γ' t

/-- Input context for the constraint leaf: 7 `r64` words `[ca,cb,na,nb,P,0,63]`. -/
abbrev inCtxtC : Ctxt jasminDialect := List.replicate 7 r64

def inVarC : (m : Nat) → Nat → @Ctxt.Var jasminDialect (List.replicate (m+1) r64) r64
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (inVarC m k).there

def cInVar (i : Nat) : Ctxt.Var inCtxtC r64 := inVarC 6 i

/-- Initial constraint state: row words `ca,cb,na,nb` ← inputs `0..3`; output
    slots `c0,c1` and scratch `x,q` ← input 0 (written before read); constants
    `P,0,63` ← inputs `4,5,6`. -/
def initCState : CState inCtxtC where
  slot := fun i => if i.val < 4 then cInVar i.val else cInVar 0
  con  := fun j => cInVar (4 + j.val)

/-- `bbSub a b` into slot `dst`, via scratch `x` (slot 6) and `q` (slot 7):
    `x = a + P; x = x - b; t = x - P; q = t>>63; q = 0-q; q = q&P; dst = t + q`.
    We fold `t` into `x` (one slot). -/
def emitBbSub {t : JasminTy} {Γ : Ctxt jasminDialect}
    (st : CState Γ) (dst : Fin 8) (a b : CSrc) (k : CCont t) : Com jasminDialect Γ t :=
  let x : Fin 8 := ⟨6, by omega⟩
  let q : Fin 8 := ⟨7, by omega⟩
  emitC st  .add x a (.cn cP) fun s1 =>      -- x = a + P
  emitC s1  .sub x (.sl x) b fun s2 =>       -- x = x - b  (= a + P - b ∈ [1,2P))
  emitC s2  .sub x (.sl x) (.cn cP) fun s3 =>-- x = x - P
  emitC s3  .shr q (.sl x) .sh63 fun s4 =>   -- q = x >> 63
  emitC s4  .sub q (.cn cZero) (.sl q) fun s5 =>-- q = 0 - q
  emitC s5  .and q (.sl q) (.cn cP) fun s6 =>-- q = q & P
  emitC s6  .add dst (.sl x) (.sl q) k       -- dst = x + q = bbSub a b

/-- The constraint-eval `Com`: `c0 = bbSub na cb`, then `sum = bbAdd ca cb`
    (into scratch slot 6, the csub) followed by `c1 = bbSub nb sum`. The two
    outputs `c0` (slot 4) and `c1` (slot 5) are the last two bindings. -/
def transCom : Com jasminDialect inCtxtC r64 :=
  let ca : Fin 8 := ⟨0, by omega⟩; let cb : Fin 8 := ⟨1, by omega⟩
  let na : Fin 8 := ⟨2, by omega⟩; let nb : Fin 8 := ⟨3, by omega⟩
  let c0 : Fin 8 := ⟨4, by omega⟩; let c1 : Fin 8 := ⟨5, by omega⟩
  let x  : Fin 8 := ⟨6, by omega⟩; let q : Fin 8 := ⟨7, by omega⟩
  -- c0 = bbSub na cb. (After this, slot `na` is free — reuse it for the sum.)
  emitBbSub initCState c0 (.sl na) (.sl cb) fun s1 =>
  -- sum = bbAdd ca cb (csub) into slot `na` (slot 2), NOT the bbSub scratch x:
  emitC s1  .add na (.sl ca) (.sl cb) fun s2 =>
  emitC s2  .sub na (.sl na) (.cn cP) fun s3 =>
  emitC s3  .shr q (.sl na) .sh63 fun s4 =>
  emitC s4  .sub q (.cn cZero) (.sl q) fun s5 =>
  emitC s5  .and q (.sl q) (.cn cP) fun s6 =>
  emitC s6  .add na (.sl na) (.sl q) fun s7 =>  -- na = bbAdd ca cb
  -- c1 = bbSub nb (bbAdd ca cb). The sum lives in slot `na`, disjoint from the
  -- bbSub scratch `x`/`q`, so no clobber.
  emitBbSub s7 c1 (.sl nb) (.sl na) fun s8 =>
  -- finalize: re-emit c0, c1 in order as the last two bindings
  emitC s8 .add c0 (.sl c0) (.cn cZero) fun s9 =>
  emitC s9 .add c1 (.sl c1) (.cn cZero) fun s10 =>
  .ret (s10.slot c1)

/-- Destination slots per binding (lock-step with `transCom`). `bbSub` writes 7
    (x,x,x,q,q,q,dst); `bbAdd` writes 6 (x,x,q,q,q,x). c0=4, c1=5; x=6, q=7. -/
def transSlots : List Nat :=
  [6,6,6,7,7,7,4] ++              -- c0 = bbSub na cb
  [2,2,7,7,7,2] ++                -- na = bbAdd ca cb  (sum in slot 2)
  [6,6,6,7,7,7,5] ++              -- c1 = bbSub nb (sum in slot 2)
  [4, 5]                          -- finalize c0, c1

def cSlotReg (s : Nat) : String := "r" ++ toString s
def transDstName (k : Nat) : String := cSlotReg (transSlots.getD k 0)

/-- Input word name: `0..3` → `r0..r3` (copied in); `4,5,6` → `P, 0, 63`. -/
def transInName (i : Nat) : String :=
  if i = 0 then "r0" else if i = 1 then "r1"
  else if i = 2 then "r2" else if i = 3 then "r3"
  else if i = 4 then "2013265921" else if i = 5 then "0" else "63"

/-- State file: working registers `r0..r7`. Only ~4 live at once, so this fits. -/
def transRegDecls : List String := (List.range 8).map (fun s => "reg u64 r" ++ toString s)

def transJazz : String :=
  emitAbiOrchReg "fib_air_transition_rc" (w := 64) (nIn := 7) (nOut := 2)
    (nCopy := 4) transRegDecls transInName transDstName transCom

/-- The constraint leaf exports the expected ABI (2-word out, 7-word in). -/
theorem trans_export_sig :
    strContains transJazz
      "export fn fib_air_transition_rc(reg ptr u64[2] out, reg const ptr u64[7] inp)"
      = true := by native_decide

/-- Lock-step: 7 + 6 + 7 + 2 = 22 bindings. -/
theorem transSlots_length_eq_bindings :
    transSlots.length = comBindings transCom := by native_decide

theorem trans_is_regarith_only : allRegArith transCom = true := by native_decide

/-! ## 10. Emit driver -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/fib_trace_gen.jazz" traceJazz
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/fib_air_transition.jazz" transJazz
  IO.println "wrote gen_com/fib_trace_gen.jazz (Fibonacci-AIR trace gen, height 10, EMIT-computation leaf)"
  IO.println "wrote gen_com/fib_air_transition.jazz (Fibonacci-AIR transition eval over a row pair)"
  IO.println s!"  traceCom bindings = {comBindings traceCom}; transCom bindings = {comBindings transCom}"

#eval main

end CatCrypt.Crypto.SecureCompilation.VIR.FibTraceGenEmit
