/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockMemrefEmit

/-!
# The whole ChaCha20 block with the FULL pointer ABI: BOTH input and output via memrefs

[`Chacha20BlockMemrefEmit.lean`](Chacha20BlockMemrefEmit.lean) writes all sixteen
output words to a caller-provided **output** memref, but still passes the sixteen
input state words (and their sixteen feed-forward originals) as **register
arguments**: the context is `List.replicate 32 T64 ++ [.memref 16]`, i.e. 32 `reg
u32`/`reg u64` parameters plus one out-pointer. On the x86-64 SysV ABI a function
gets only **six** integer-register arguments, so jasminc rejects that signature
(`"too many parameters"` in register allocation): 32 reg words do not fit.

This file closes that residual by reading the input state **from an input memref
pointer** instead of register arguments. The whole block now lives in a context of
**just two memref pointers**:

```
chacha20_block(out : .memref 16, in : .memref 16)
```

The sixteen state words are read from `in` at indices `0..15` via the
seam-covered runtime-index load `memrefGetDyn` (which lowers to jasmin
`stackLoad`), the ten double-rounds + feed-forward run exactly as in the
output-memref version (the 64-carried masked ops, all seam-covered), and the
sixteen results are written to `out` at indices `0..15` via `memrefSetDyn`
(lowering to jasmin `stackStore`). Two pointer arguments fit the 6-register ABI,
so jasminc compiles the emitted `export fn chacha20_block(reg ptr …, reg ptr …)`.

## The feed-forward source

`chachaBlock s i = (chachaCore s) i + s i` (RFC 8439 §2.3): the feed-forward adds
the **original input state** `s`. Here `s` IS the `in` memref, so both the working
state and the feed-forward originals are the sixteen `in` reads — we read `in`
once into sixteen `T64` SSA words and seed BOTH `cur` and `orig` of the builder
state from them. No second set of inputs is needed.

## What is delivered

* `inCtxtFull : Ctxt catCryptDialect := [.memref 16, .memref 16]` — the two-pointer
  context `(out, in)`. Exactly two memref args; NO 32 reg-word args.
* `emitReads64` — read sixteen `in` words via `memrefGetDyn` at indices `0..15`,
  seeding the builder state's `cur` and `orig` from them.
* `chacha20BlockFullMemrefCom : Com catCryptDialect inCtxtFull (.memref 16)` — the
  whole block: read `in`, ten 64-carried double-rounds, 16-word feed-forward, then
  sixteen `memrefSetDyn` stores into `out`.
* `chacha20BlockFullMemrefCom_readback` — reading `out` cell `i` back via
  `memGetDyn` returns `(chachaBlock s i).setWidth 64` (the multi-output read API),
  reusing the committed abstract spec `chacha20BlockMemrefSpec`.
* `emitReads64_denote_reduces` / `emitQR64_denote_reduces` — the per-layer
  `denote`-peel reductions.
* `chacha20BlockFullMemrefJasmin` — lowered all the way to `Com jasminDialect`
  (the input reads via `stackLoad`, the output stores via `stackStore`).
* `chacha20BlockFullMemrefJazz` / `emit` — the whole-function `.s` text, symbol
  `chacha20_block`, to `bench/chacha_compare/gen_com/chacha20_block_full.s`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefJazzEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.ChaCha20Block
open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockMemrefEmit

/-! ## 1. The two-pointer context and the memref vars

`inCtxtFull` holds JUST the two memref pointers: the output memref `out`
(slot 0) and the input memref `in` (slot 1). There are NO register-word inputs —
the sixteen state words are read from `in` at runtime. This is the whole point:
the `export fn` signature has exactly two pointer arguments, satisfying the
x86-64 SysV 6-register limit that the 32-reg-arg version blew. -/

/-- The 64-bit machine-word dialect type (re-exported for local use). -/
abbrev T64 : CryptoTy := .sword 64

/-- The whole-block context: just the two memref pointers `(out, in)`. -/
abbrev inCtxtFull : Ctxt catCryptDialect := [.memref 16, .memref 16]

/-- The output memref var of `inCtxtFull` (slot 0). -/
def outVarFull : Ctxt.Var inCtxtFull (.memref 16) := .here

/-- The input memref var of `inCtxtFull` (slot 1). -/
def inVarFull : Ctxt.Var inCtxtFull (.memref 16) := .there .here

/-! ## 2. Reading the sixteen input words from the `in` memref

`emitReadsFrom seed m` emits, for `j = m-1 … 0`, the binding
`wj := memrefGetDyn in (bvConst 64 j)`, threading a TOTAL word map
`words : Fin 16 → Ctxt.Var Γ T64`. The map is seeded with a real `T64` var
(`seed`) so it stays total; every one of the sixteen slots is overwritten by its
own read before the builder is seeded (the seed only fills positions not yet
read, which at the `m = 0` leaf is none). The `in`/`out` memref vars and the word
map all `.there`-shift by two binders per read (the `idx` const + the load). -/

/-- Emit the `in`-reads for indices `m-1 … 0`, threading the input memref var
    `inV`, the output memref var `outV`, and a total word map `words`. At the
    leaf, seed BOTH `cur` and `orig` of the builder state from `words` (the
    feed-forward originals ARE the input state) and pass `out := outV`. -/
def emitReadsFrom {t : CryptoTy} : (m : Nat) → {Γ : Ctxt catCryptDialect} →
    Ctxt.Var Γ (.memref 16) → Ctxt.Var Γ (.memref 16) →
    (Fin 16 → Ctxt.Var Γ T64) →
    ({Γ' : Ctxt catCryptDialect} → BState64 Γ' → Com catCryptDialect Γ' t) →
    Com catCryptDialect Γ t
  | 0, _, _, outV, words, k =>
      k (Γ' := _) { cur := words, orig := words, out := outV }
  | (m+1), _, inV, outV, words, k =>
      if h : m < 16 then
        -- idx := bvConst 64 m
        .var (show Expr catCryptDialect _ T64 from
              { op := .bvConst 64 (BitVec.ofNat 64 m), retTy_eq := rfl, args := .nil }) <|
        -- wm := memrefGetDyn in idx        (in shifted by one, idx = .here)
        .var (show Expr catCryptDialect _ T64 from
              { op := .memrefGetDyn 16, retTy_eq := rfl,
                args := .cons inV.there (.cons .here .nil) })
          (emitReadsFrom m (Γ := T64 :: T64 :: _)
            (inV.there.there) (outV.there.there)
            (fun i => if i = ⟨m, h⟩ then .here else (words i).there.there)
            k)
      else
        k (Γ' := _) { cur := words, orig := words, out := outV }

/-- Bootstrap the reads: emit read `w15` first (giving a real `T64` head var to
    seed the total word map), then read `w14 … w0` via `emitReadsFrom`. We seed the
    map with that first head var at every slot; each true read overwrites its own
    slot, so at the leaf all sixteen slots hold their own `in`-word. -/
def emitReads64 {t : CryptoTy}
    (inV outV : Ctxt.Var inCtxtFull (.memref 16))
    (k : {Γ' : Ctxt catCryptDialect} → BState64 Γ' → Com catCryptDialect Γ' t) :
    Com catCryptDialect inCtxtFull t :=
  -- idx15 := bvConst 64 15
  .var (show Expr catCryptDialect _ T64 from
        { op := .bvConst 64 (BitVec.ofNat 64 15), retTy_eq := rfl, args := .nil }) <|
  -- w15 := memrefGetDyn in idx15
  .var (show Expr catCryptDialect _ T64 from
        { op := .memrefGetDyn 16, retTy_eq := rfl,
          args := .cons inV.there (.cons .here .nil) })
    (emitReadsFrom 15 (Γ := T64 :: T64 :: inCtxtFull)
      (inV.there.there) (outV.there.there)
      (fun i => if i = (15 : Fin 16) then .here else .here)
      k)

/-! ## 3. The whole-block full-memref `Com`

Read the sixteen `in` words, run the committed ten double-rounds + feed-forward +
sixteen output stores (`emitDoubleRounds64` / `emitFeedForward64` / `emitStores64`
from `Chacha20BlockMemrefEmit`), and return the output memref. The ONLY change
from `chacha20BlockMemrefCom` is the front matter: instead of seeding `cur`/`orig`
from 32 register-arg vars, we seed them from the sixteen `in`-reads. -/

/-- **The whole ChaCha20 block as a SINGLE straight-line `Com catCryptDialect`
    over a two-pointer context `(out, in)`.** Reads sixteen `in` words via
    `memrefGetDyn`, runs ten 64-carried double-rounds, the 16-word feed-forward
    (adding the original `in` state), then sixteen `memrefSetDyn` stores into
    `out`; the result is the final `.memref 16`. The context is JUST the two
    memref pointers — no 32 reg-word args — so the emitted `export fn` fits the
    x86-64 6-register ABI. -/
def chacha20BlockFullMemrefCom : Com catCryptDialect inCtxtFull (.memref 16) :=
  emitReads64 inVarFull outVarFull fun st =>
  emitDoubleRounds64 10 st fun st1 =>
  emitFeedForward64 16 st1 fun stf =>
  emitStores64 16 stf fun stS =>
  .ret stS.out

/-! ## 4. The abstract output-memref spec and the multi-output readback

We reuse the committed abstract spec `chacha20BlockMemrefSpec` (the caller buffer
with the sixteen `chachaBlock` output words `setWidth 64` written at `0..15`) and
its readback lemma `chacha20BlockMemrefSpec_readback`. The whole 64-byte keystream
block is recoverable cell by cell from the `out` memref. -/

/-- Reading cell `i` of the output memref returns the `i`-th block output word
    `(chachaBlock s i).setWidth 64` — the whole keystream block is recoverable
    cell by cell, independent of the buffer's prior contents. Re-exports the
    committed `chacha20BlockMemrefSpec_readback`. -/
theorem chacha20BlockFullMemrefCom_readback (s : ChaChaState) (m : Fin 16 → BitVec 64)
    (i : Fin 16) :
    memGetDyn (chacha20BlockMemrefSpec s m) i.val = (chachaBlock s i).setWidth 64 :=
  chacha20BlockMemrefSpec_readback s m i

/-! ## 5. Per-layer denote-peel reductions

Each emitted layer's `denote` is its continuation evaluated at the chained-extend
valuation (every `.var` peel is `rfl` via the `@[simp] lookup_*_extend` lemmas).
The `memrefGetDyn` reads, the masked quarter-rounds, and the feed-forward all peel
the same definitional way. -/

variable {Γ : Ctxt catCryptDialect} {t : CryptoTy}

/-- One `.var` binder's `denote` is its body's `denote` at the valuation extended
    by the bound expression's value. -/
theorem denote_var_peel {u s : CryptoTy}
    (e : Expr catCryptDialect Γ u) (body : Com catCryptDialect (u :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (Com.var e body).denote V = body.denote (V.extend (e.denote V)) := rfl

/-- **Per-read denote reduction, by induction on the read counter.** For every
    `m`, the `denote` of the `in`-reads for indices `m-1 … 0` is the continuation
    evaluated at some valuation: there is a post-builder `st'` and post-valuation
    `V'` with `(emitReadsFrom m inV outV words k).denote V = (k st').denote V'`.
    Each induction step peels the level's two `.var` binders with `denote_var_peel`
    and appeals to the induction hypothesis, so no reduction is deeper than one
    binder. -/
theorem emitReadsFrom_denote_reduces (m : Nat) :
    ∀ {Γ : Ctxt catCryptDialect} (inV outV : Ctxt.Var Γ (.memref 16))
      (words : Fin 16 → Ctxt.Var Γ T64)
      (k : {Γ' : Ctxt catCryptDialect} → BState64 Γ' → Com catCryptDialect Γ' t)
      (V : Ctxt.Valuation Γ),
      ∃ (Γ' : Ctxt catCryptDialect) (st' : BState64 Γ') (V' : Ctxt.Valuation Γ'),
        (emitReadsFrom m inV outV words k).denote V = (k st').denote V' := by
  induction m with
  | zero => intro Γ inV outV words k V; exact ⟨_, _, V, rfl⟩
  | succ m ih =>
      intro Γ inV outV words k V
      by_cases h : m < 16
      · simp only [emitReadsFrom, dif_pos h, denote_var_peel]
        exact ih _ _ _ _ _
      · simp only [emitReadsFrom, dif_neg h]
        exact ⟨_, _, V, rfl⟩

/-- **Per-read-block denote reduction.** The sixteen `in`-reads' `denote` is the
    continuation evaluated at the chained-extend valuation: there is a post-builder
    `st'` and post-valuation `V'` with `(emitReads64 inV outV k).denote V =
    (k st').denote V'`. The bootstrap read's two `.var` binders peel with
    `denote_var_peel`; the remaining fifteen are `emitReadsFrom_denote_reduces`. -/
theorem emitReads64_denote_reduces
    (inV outV : Ctxt.Var inCtxtFull (.memref 16))
    (k : {Γ' : Ctxt catCryptDialect} → BState64 Γ' → Com catCryptDialect Γ' t)
    (V : Ctxt.Valuation inCtxtFull) :
    ∃ (Γ' : Ctxt catCryptDialect) (st' : BState64 Γ') (V' : Ctxt.Valuation Γ'),
      (emitReads64 inV outV k).denote V = (k st').denote V' := by
  simp only [emitReads64, denote_var_peel]
  exact emitReadsFrom_denote_reduces 15 _ _ _ _ _

/-- **Per-quarter-round denote reduction** (re-exported for the full-memref
    program; identical to the output-memref version, the QR builders are shared). -/
theorem emitQR64_denote_reduces (st : BState64 Γ) (a b c d : Fin 16) (k : Cont64 t)
    (V : Ctxt.Valuation Γ) :
    ∃ (Γ' : Ctxt catCryptDialect) (st' : BState64 Γ') (V' : Ctxt.Valuation Γ'),
      (emitQR64 st a b c d k).denote V = (k st').denote V' :=
  ⟨_, _, _, rfl⟩

/-! ## 6. Lowering through the seam and emit

The whole-block full-memref `Com` uses only seam-covered ops (`bvConst`, `bvAdd`,
`bvXor`, `bvAnd`, `bvOr`, `bvShiftL`, `bvShiftR`, `memrefGetDyn`, `memrefSetDyn`),
so `cryptoDialectToJasminCom` lowers it: the sixteen `memrefGetDyn` reads lower to
jasmin `stackLoad`, the sixteen `memrefSetDyn` stores to `stackStore`. The context
is just two memrefs, so the lowered jasmin `Com` has two pointer parameters. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-- The seam lowers the whole-block full-memref program. -/
theorem chacha20BlockFullMemref_jasmin_isSome :
    (cryptoDialectToJasminCom chacha20BlockFullMemrefCom).isSome := by native_decide

/-- The lowered jasmin `Com` for the whole ChaCha20 block with the full pointer
    ABI (input via `stackLoad`, output via `stackStore`, two pointer params). -/
def chacha20BlockFullMemrefJasmin :
    Com jasminDialect (mapCtx inCtxtFull) (mapTy (.memref 16)) :=
  (cryptoDialectToJasminCom chacha20BlockFullMemrefCom).get
    chacha20BlockFullMemref_jasmin_isSome

/-- **The export-fn signature witness.** The lowered jasmin program's parameter
    context is EXACTLY the two pointer-array memrefs `[stackArr 64 16, stackArr 64
    16]` — i.e. two `reg ptr u64[16]` arguments `(out, in)` and ZERO `reg u32`
    word arguments. The 32-reg-arg version's context was `List.replicate 32 T64 ++
    [.memref 16]` (33 params, 32 of them scalar words) which blows the x86-64 SysV
    6-register limit; this two-pointer context fits it, so jasminc compiles the
    emitted `export fn`. -/
theorem chacha20BlockFullMemref_param_ctx :
    mapCtx inCtxtFull = [JasminTy.stackArr 64 16, JasminTy.stackArr 64 16] := rfl

/-- The lowered jasmin program has exactly two parameters (the two memref
    pointers) — none are scalar register words. -/
theorem chacha20BlockFullMemref_param_count :
    (mapCtx inCtxtFull).length = 2 := rfl

/-- The whole-function `.jazz`/`.s` text of the whole ChaCha20 block with the
    full pointer ABI, symbol `chacha20_block`. The `export fn` takes exactly two
    pointer arguments `(out, in)` — fits the x86-64 6-register ABI. -/
def chacha20BlockFullMemrefJazz : String :=
  JasminPrint.emitJazz "chacha20_block" chacha20BlockFullMemrefJasmin

/-- **The public emit action.** Write the whole-block full-memref `.s` (from one
    `Com catCryptDialect` lowered through the seam) to the bench gen-from-Com
    directory, under the symbol `chacha20_block`. Both input and output flow
    through memref pointers, so the emitted `export fn` has only two pointer
    arguments — jasminc compiles it (the 32-reg-arg version did not). The
    orchestrator assembles + perf-compares against HACL* (`bench/chacha_compare`). -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/chacha_compare/gen_com"
  IO.FS.writeFile "bench/chacha_compare/gen_com/chacha20_block_full.s"
    chacha20BlockFullMemrefJazz
  IO.println "CatCrypt whole-block FULL-memref emit OK : bench/chacha_compare/gen_com/chacha20_block_full.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefJazzEmit
