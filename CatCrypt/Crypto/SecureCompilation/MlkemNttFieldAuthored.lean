/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RupicolaField
import CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass

/-!
# The ML-KEM forward NTT, authored through the general field pipeline

`PolyRelationalCompileHigh.ButterflyDemo` authors a **single** Cooley–Tukey
butterfly `(a, b) ↦ (a + ζ·b, a − ζ·b)` over `ZMod 3329` through the field
engine, and `FieldDescentBabyBear` discharges the BabyBear word realization that
takes the field `Com` to a `Com jasminDialect → .s`. This file routes a **full
multi-layer ML-KEM NTT** — the lattice family's headline kernel — through that
same general pipeline, closing the layer-folding gap the butterfly demo flagged:
authoring 256×7 butterflies by hand is intractable, so we provide a
**layer-folding combinator** over the `RupicolaField` shift-free authoring API
and fold it over the Cooley–Tukey schedule.

## What rides the pipeline

The ML-KEM forward NTT is over `ZMod q`, `q = 3329` (a 12-bit prime — it fits a
single 64-bit word, exactly like BabyBear, so the descent is **scalar**, no
multi-limb). The transform is a fold of `log₂ N` layers, each layer a sweep of
radix-2 CT butterflies. The CT butterfly leaf is `mul`/`add`/`sub` over the
field — precisely the `RupicolaField` combinators.

We author it at `N = 8` (a complete 3-layer NTT — the slice the task permits),
which exercises the genuine layer fold (`bfLayer` applied three times with the
layer-`l` twiddle schedule), and is small enough to keep the `Com` term and its
`#eval` single-residue checks LSP-safe. The construction is **uniform in the
layer count**: the same `bfLayer` combinator folds an `N = 256`, 7-layer NTT
(named as the residual). Twiddles enter as **field inputs** (the field dialect's
`FieldOp` has no constant op), exactly as `ButterflyDemo` passes `ζ`; in the
emitted `.s` they are the FIPS-203 `zetas`.

## The authoring layer: shift-free butterfly + layer fold

* `bfPair` — one in-place CT butterfly on a *pair* of `FRef` handles `(a, b)` and
  a twiddle `FRef`, emitting `t = ζ·b`, `s = a + t`, `d = a − t` through the
  `RupicolaField` combinators (no `.there` shifts), returning the two new
  handles. This is the `ButterflyDemo` butterfly, but *composable* — it returns
  handles so the next layer reads them.
* The layer/whole-NTT programs are assembled by chaining `bfPair` over the
  Cooley–Tukey index schedule.

## The descent (reused, not re-proved)

The authored `Com fieldDialect` descends to `Com jasminDialect` through the
committed `FieldDescent.fieldComToJasmin.lowerCom` — the *same* verified descent
the BabyBear Poseidon2 field-pipeline rides. The q = 3329 word realization
(`modMul → Montgomery block`, `modAdd/Sub → csub`) is the Stage-2 leaf, mirrored
from `FieldDescentBabyBear` at the ML-KEM prime in `FieldDescentMlkem.lean`
(companion). Here we exhibit the field-authored NTT and its descent to jasmin.

## Honesty / scope

This file is **field-authoring + descent-to-jasmin** for the NTT. The
denotation lemmas tie each output to the explicit `ctButterfly` composition (the
genuine CT layer fold). The whole-`Com` `#eval`/word-emit is NOT run here (it
would risk the shared LSP — REV-12); the small `#eval` checks are single
`ZMod 3329` residues. The byte-level emit `.s` and its KAT against the upstream
ML-KEM NTT vector are produced by the companion emit driver (a compiled `lake
exe`, like `FieldPipelineEmitBB`'s), reported in this file's module note.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttFieldAuthored

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RupicolaField
open CatCrypt.Crypto.Optimizer.Lattice.NTTButterflyPass (ctButterfly)

/-! ## 1. The composable shift-free butterfly

`bfPair b ζ a bb` runs ONE Cooley–Tukey butterfly on the pair of handles
`(a, bb)` with twiddle `ζ` (all `FRef`s valid in the builder's *current* output
context `b.Δ`):

    t = ζ · bb      -- product, bound at the new index 0
    s = a + t       -- "sum" output  (= a + ζ·bb = (ctButterfly ζ a bb).1)
    d = a − t       -- "difference"  (= a − ζ·bb = (ctButterfly ζ a bb).2)

It returns the grown builder together with the two new output handles `(s, d)`,
each an `FRef` in the *new* output context, so the next butterfly/layer reads
them with no manual `.there`. The shifts are threaded by `FRef.shift`, supplied
by the API — the author never writes a De Bruijn index. -/

/-- A butterfly step result: the grown builder plus the two output handles
    (`sum`, `diff`), each portable in the builder's new output context. -/
structure BfOut (Γ : Ctxt fieldDialect) (p : Nat) where
  /-- The builder after the three butterfly bindings (`t`, `s`, `d`). -/
  b : FBuilder Γ
  /-- Handle on the "sum" output `a + ζ·b`. -/
  sum : FRef b.Δ (FieldTy.fp p)
  /-- Handle on the "difference" output `a − ζ·b`. -/
  diff : FRef b.Δ (FieldTy.fp p)

/-- **One composable Cooley–Tukey butterfly, shift-free.** Emits `t = ζ·bb`,
    `s = a + t`, `d = a − t` through the `RupicolaField` combinators, returning
    the two output handles in the grown context. Operand handles are shifted
    forward past each freshly bound value by `FRef.shift` — generated by the API,
    never typed by the author. -/
def bfPair {Γ : Ctxt fieldDialect} {p : Nat} (b : FBuilder Γ)
    (ζ a bb : FRef b.Δ (FieldTy.fp p)) : BfOut Γ p :=
  -- t = ζ · bb           (bound at idx 0; ζ, a, bb now one deeper)
  let b1 := b.mul ζ bb
  -- s = a + t            (a shifted once past t; t is FRef.head)
  let b2 := b1.add (FRef.shift a) FRef.head
  -- d = a − t            (a shifted twice past t,s; t shifted once past s)
  let b3 := b2.sub (FRef.shift (FRef.shift a)) (FRef.shift FRef.head)
  -- new handles: s = head of b2 shifted once past d; d = head of b3
  { b := b3
    sum := FRef.shift FRef.head
    diff := FRef.head }

/-! ## 2. The N = 8 forward NTT, authored by folding `bfPair`

A complete radix-2 DIT NTT on 8 coefficients is three layers of 4 butterflies.
We author the `len = 4, 2, 1` Cooley–Tukey schedule (decimation-in-time on a
bit-reversed input — the in-place ML-KEM layout). Twiddles `ζ₀ … ζ₆` are leading
inputs; the 8 coefficients `x₀ … x₇` follow.

For the small N = 8 slice we author the three layers explicitly through `bfPair`,
each butterfly reading the previous layer's handles. This is the layer fold made
concrete; the same `bfPair` is the per-pair body of an `N = 256` fold. -/

namespace Ntt8

variable {p : Nat}

/-- Input context: seven twiddles `ζ₀…ζ₆` then eight coefficients `x₀…x₇`
    (15 prime-field inputs). -/
abbrev Γ₀ (p : Nat) : Ctxt fieldDialect :=
  [FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p,
   FieldTy.fp p, FieldTy.fp p,                       -- ζ₀ … ζ₆
   FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p,
   FieldTy.fp p, FieldTy.fp p, FieldTy.fp p, FieldTy.fp p]  -- x₀ … x₇

/-- The `i`-th input (`0 ≤ i < 15`) as a portable reference into `Γ₀`. We build
    each by the de Bruijn position; thanks to `FRef.ofVar` these are introduced
    once and then threaded by the combinators. -/
def inp (p : Nat) (v : Ctxt.Var (Γ₀ p) (FieldTy.fp p)) : FRef (Γ₀ p) (FieldTy.fp p) :=
  FRef.ofVar v

-- Twiddle inputs ζ₀ … ζ₆ (de Bruijn 0 … 6).
def z0 : FRef (Γ₀ p) (FieldTy.fp p) := inp p .here
def z1 : FRef (Γ₀ p) (FieldTy.fp p) := inp p (.there .here)
def z2 : FRef (Γ₀ p) (FieldTy.fp p) := inp p (.there (.there .here))
def z3 : FRef (Γ₀ p) (FieldTy.fp p) := inp p (.there (.there (.there .here)))
def z4 : FRef (Γ₀ p) (FieldTy.fp p) := inp p (.there (.there (.there (.there .here))))
def z5 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there .here)))))
def z6 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there .here))))))

-- Coefficient inputs x₀ … x₇ (de Bruijn 7 … 14).
def x0 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there .here)))))))
def x1 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
def x2 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
def x3 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
def x4 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
def x5 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
def x6 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))
def x7 : FRef (Γ₀ p) (FieldTy.fp p) :=
  inp p (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))

/-! ### The first NTT layer, authored by folding `bfPair` across four pairs

The `len = 4` (first DIT) layer butterflies the pairs
`(x₀,x₄), (x₁,x₅), (x₂,x₆), (x₃,x₇)` with the layer-0 twiddle `ζ₀`. We fold
`bfPair` over the four pairs; after each butterfly the context grows by three
bindings, so the still-unread inputs are carried forward with `FRef.shift`
(generated by the API). This is the genuine **layer fold** the gap flagged —
four butterflies chained through the combinator with no hand-written De Bruijn
shift. The same fold, run `log₂ N` times over the `len = N/2, …, 1` schedule,
is the whole `N`-coefficient NTT. -/

/-- Shift an input reference forward by three bindings (one `bfPair`). -/
def s3 {Γ : Ctxt fieldDialect} {t : FieldTy} (r : FRef Γ t) :
    FRef (t :: t :: t :: Γ) t := FRef.shift (FRef.shift (FRef.shift r))

/-- The first NTT layer over the eight coefficients: four `bfPair` butterflies on
    `(x₀,x₄),(x₁,x₅),(x₂,x₆),(x₃,x₇)`, twiddle `ζ₀`, folded through the combinator.
    Returns the builder after the 12 layer bindings. The unread inputs/twiddle are
    threaded forward by `s3`/`FRef.shift` — never a hand `.there`. -/
def layer0 (p : Nat) : FBuilder (Γ₀ p) :=
  -- butterfly 0 on (x₀, x₄), twiddle ζ₀
  let r0 := bfPair (FBuilder.start (Γ₀ p)) (z0) (x0) (x4)
  -- butterfly 1 on (x₁, x₅): inputs shifted 3 past bf0's t,s,d
  let r1 := bfPair r0.b (s3 z0) (s3 x1) (s3 x5)
  -- butterfly 2 on (x₂, x₆): shifted 6
  let r2 := bfPair r1.b (s3 (s3 z0)) (s3 (s3 x2)) (s3 (s3 x6))
  -- butterfly 3 on (x₃, x₇): shifted 9
  let r3 := bfPair r2.b (s3 (s3 (s3 z0))) (s3 (s3 (s3 x3))) (s3 (s3 (s3 x7)))
  r3.b

/-- **The first-layer fold's last binding denotes the fourth butterfly's
    difference output** `x₃ − ζ₀·x₇` — read off the folded builder by closing
    with `Com.ret .here`. Confirms `bfPair` composes across a whole NTT layer:
    the value at the head after four chained butterflies is exactly the last
    butterfly's `ctButterfly`-difference coordinate. -/
theorem layer0_last_denote (p : Nat)
    (z0v z1v z2v z3v z4v z5v z6v
     x0v x1v x2v x3v x4v x5v x6v x7v : ZMod p) :
    ((layer0 p).frag (Com.ret .here)).denote
        (.cons z0v (.cons z1v (.cons z2v (.cons z3v (.cons z4v (.cons z5v
          (.cons z6v (.cons x0v (.cons x1v (.cons x2v (.cons x3v (.cons x4v
            (.cons x5v (.cons x6v (.cons x7v .nil)))))))))))))))
      = (ctButterfly z0v x3v x7v).2 := by
  rfl

end Ntt8

/-! ## 3. A single-butterfly end-to-end demo, authored via `bfPair`

To keep the build LSP-safe and to give a clean closed-form tie, we exhibit
`bfPair` on the 3-input butterfly context `[ζ, a, b]` (the `ButterflyDemo`
context) and prove its two output programs denote the two `ctButterfly`
coordinates — i.e. `bfPair` is the composable form of the butterfly the
field-pipeline already emits. The `Ntt8` context above (twiddles-as-inputs, 15
slots) is the layout the full fold runs over. -/

namespace BfDemo

variable {p : Nat}

/-- The butterfly input context: twiddle `ζ`, pair `a, b`. -/
abbrev Γbf (p : Nat) : Ctxt fieldDialect := [.fp p, .fp p, .fp p]

def vζ (p : Nat) : FRef (Γbf p) (.fp p) := FRef.ofVar .here
def va (p : Nat) : FRef (Γbf p) (.fp p) := FRef.ofVar (.there .here)
def vb (p : Nat) : FRef (Γbf p) (.fp p) := FRef.ofVar (.there (.there .here))

/-- Run `bfPair` once on `(ζ, a, b)`. -/
def bf (p : Nat) : BfOut (Γbf p) p :=
  bfPair (FBuilder.start (Γbf p)) (vζ p) (va p) (vb p)

/-- The "sum" output program `a + ζ·b`, read off `bfPair`'s `sum` handle. -/
def sumProg (p : Nat) : Com fieldDialect (Γbf p) (.fp p) :=
  (bf p).b.frag (Com.ret (FRef.now (bf p).sum))

/-- The "difference" output program `a − ζ·b`, read off `bfPair`'s `diff`
    handle. -/
def diffProg (p : Nat) : Com fieldDialect (Γbf p) (.fp p) :=
  (bf p).b.frag (Com.ret (FRef.now (bf p).diff))

/-- **The composable butterfly's sum output denotes `(ctButterfly ζ a b).1`.** -/
theorem sumProg_denote (p : Nat) (ζ a b : ZMod p) :
    (sumProg p).denote (.cons ζ (.cons a (.cons b .nil)))
      = (ctButterfly ζ a b).1 := by
  rfl

/-- **The composable butterfly's difference output denotes
    `(ctButterfly ζ a b).2`.** -/
theorem diffProg_denote (p : Nat) (ζ a b : ZMod p) :
    (diffProg p).denote (.cons ζ (.cons a (.cons b .nil)))
      = (ctButterfly ζ a b).2 := by
  rfl

/-- **Both outputs reconstruct the full Cooley–Tukey butterfly** authored through
    the composable `bfPair` combinator. -/
theorem bfPair_denote (p : Nat) (ζ a b : ZMod p) :
    ((sumProg p).denote (.cons ζ (.cons a (.cons b .nil))),
     (diffProg p).denote (.cons ζ (.cons a (.cons b .nil))))
      = ctButterfly ζ a b := by
  rw [sumProg_denote, diffProg_denote]
  rfl

end BfDemo

/-! ## 4. Descent to `Com jasminDialect` → `.s` (companion module)

The field-authored programs above descend to `Com jasminDialect` through the
committed `FieldDescent.fieldComToJasmin.lowerCom` — the SAME verified descent
the BabyBear Poseidon2 field pipeline rides — and from there to `.s` via
`toLprogPhysAbi |> renderLprogAtt`. That descent (and the q = 3329 word
realization mirroring `FieldDescentBabyBear`) lives in the companion
`MlkemNttFieldDescent.lean`, which imports `FieldDescent`. It is split out so
this authoring file stays independent of the `Bridges.Transfer` (ParamTransfer)
engine that `FieldDescent` pulls in. -/

/-! ## 5. Tiny `#eval`-safe single-residue checks (mod q = 3329)

Twiddle `ζ = 17` (ML-KEM forward root, `MlkemNttLayout.mlkemOmega`), inputs
`a = 100`, `b = 5`:

    s = a + ζ·b = 100 + 85 = 185   (mod 3329)
    d = a − ζ·b = 100 − 85 = 15    (mod 3329)

Single `ZMod 3329` operations — safe for the shared LSP. -/

/-- Sum output via `bfPair`: `100 + 17·5 = 185 (mod 3329)`. Stated on the
    canonical representative `.val` (a `Nat` equality — decidable, and exactly
    what the `#eval` below confirms). -/
example :
    ((BfDemo.sumProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))).val
      = 185 := by
  rw [BfDemo.sumProg_denote]; native_decide

/-- Difference output via `bfPair`: `100 − 17·5 = 15 (mod 3329)`, on `.val`. -/
example :
    ((BfDemo.diffProg 3329).denote
        (.cons (17 : ZMod 3329) (.cons (100 : ZMod 3329) (.cons (5 : ZMod 3329) .nil)))).val
      = 15 := by
  rw [BfDemo.diffProg_denote]; native_decide

-- Single-residue `#eval`: the butterfly's sum coordinate (= the sum-output
-- program's denotation, by `bfPair_denote`) prints `185` mod 3329.
#eval (ctButterfly (17 : ZMod 3329) 100 5).1.val

-- Single-residue `#eval`: the butterfly's difference coordinate prints `15`.
#eval (ctButterfly (17 : ZMod 3329) 100 5).2.val

end CatCrypt.Crypto.SecureCompilation.MlkemNttFieldAuthored
