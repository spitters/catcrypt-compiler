/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# LowCT surface DSL

A small surface syntax for writing `LowCT` programs without directly
manipulating the `.RSeq` / `.RLetZero` / `.RCall` constructors. The
desugaring target is pure `LowCT` — no runtime overhead — so every
verified pass over `LowCT` consumes DSL-produced programs unchanged.

## Building blocks

A `Frag` is a program *prefix*: a function `LowCT → LowCT` that, given
the "tail" of the program, prepends its statements. Frags compose via
`++` (function composition) with identity `.RSkip`.

- `frag_let x t`    — emits `RLetZero x t body`
- `frag_letU64 x`   — emits `RLetU64Zero x body`
- `frag_scalar x n` — emits `RSeq (RScalarSet x n) body`
- `frag_call f d a` — emits `RSeq (RCall f d a) body`
- `frag_ifNz x t e` — emits `RSeq (RIfNz x t e) body`
- `frag_limb l i v` — emits `RSeq (RLimbStore l i v) body`

## Surface syntax

```lean
open CatCrypt.Crypto.Jasmin.LowCTDSL in
def x25519_body : LowCT :=
  rustcmd| do
    rc_let "a" TFp
    rc_let "b" TFp
    rc_let "c" TFp
    rc_call "fp_add" (loc "c" TFp) [loc "a" TFp, loc "b" TFp]
```

This is intentionally *close* to the underlying `Frag` API —
the point is ergonomics + discoverability, not a novel grammar. Using
`do` lets users chain helpers, bind fresh names, and still benefit from
Lean's goto-definition on each helper.
-/

namespace CatCrypt.Crypto.Jasmin.LowCTDSL

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. `Frag`: program-prefix combinator -/

/-- A LowCT program prefix: given the body it should precede, returns
    the combined program. Compose with `++`; identity is `Frag.nil`. -/
structure Frag where
  apply : LowCT → LowCT

namespace Frag

/-- Empty prefix — identity under composition. -/
def nil : Frag := ⟨id⟩

/-- Sequential composition (`a ++ b` runs `a` then `b`). -/
def append (a b : Frag) : Frag := ⟨a.apply ∘ b.apply⟩

instance : Append Frag := ⟨append⟩
instance : EmptyCollection Frag := ⟨nil⟩

/-- Finalize a frag into a complete LowCT by attaching `.RSkip`. -/
def compile (f : Frag) : LowCT := f.apply .RSkip

end Frag

/-! ## 2. Smart constructors for common statements -/

/-- `let <name> : <t> := 0` — fresh tower binding. -/
def frag_let (name : String) (t : TowerType) : Frag :=
  ⟨fun body => .RLetZero name t body⟩

/-- `let <name> : u64 := 0` — fresh scalar binding. -/
def frag_letU64 (name : String) : Frag :=
  ⟨fun body => .RLetU64Zero name body⟩

/-- `<name> := n` — reassign scalar to a literal. -/
def frag_scalar (name : String) (n : Nat) : Frag :=
  ⟨fun body => .RSeq (.RScalarSet name n) body⟩

/-- `f(&mut dest, &args…)` — non-clone leaf call. -/
def frag_call (f : String) (dest : Located) (args : List Located) : Frag :=
  ⟨fun body => .RSeq (.RCall f dest args) body⟩

/-- `f(&mut dest1, &mut dest2, &args…)` — 2-destination leaf call,
    used for cswap-shaped operations that mutate two field elements
    in a single call. -/
def frag_callSwap (f : String) (dest1 dest2 : Located) (args : List Located) : Frag :=
  ⟨fun body => .RSeq (.RCallSwap f dest1 dest2 args) body⟩

/-- `let clone = oldDest.clone(); f(&mut newDest, &args…)`. -/
def frag_cloneCall (clone : String) (t : TowerType) (oldDest : Located)
    (f : String) (newDest : Located) (args : List Located) : Frag :=
  ⟨fun body => .RSeq (.RCloneCall clone t oldDest f newDest args) body⟩

/-- `if <name> != 0 then <then> else <else>`. -/
def frag_ifNz (name : String) (thenBr elseBr : LowCT) : Frag :=
  ⟨fun body => .RSeq (.RIfNz name thenBr elseBr) body⟩

/-- `while <name> != 0 do <body>`. -/
def frag_whileNz (name : String) (loopBody : LowCT) : Frag :=
  ⟨fun body => .RSeq (.RWhileNz name loopBody) body⟩

/-- `for <name> in 0..n do <body>`: bounded for-loop with `n` iterations.
    The scalar variable `name` takes values `0, 1, …, n-1`. Authored to mirror
    Bedrock2's bounded `for`; the Hoare rule for `RFor` gives `0 ≤ name < n`
    as a free invariant. -/
def frag_for (name : String) (n : Nat) (loopBody : LowCT) : Frag :=
  ⟨fun body => .RSeq (.RFor name n loopBody) body⟩

/-- `<loc>.limbs[idx] := v`. -/
def frag_limb (loc : Located) (idx : Nat) (v : BitVec 64) : Frag :=
  ⟨fun body => .RSeq (.RLimbStore loc idx v) body⟩

/-! ## 3. `Located` helpers

Most leaf calls take a dest whose source and destination tower types
agree (e.g. `fp_add` writes an `Fp` from two `Fp`s). -/

/-- Standard located: `locSrc = t` (and `locDst` is the same via the
    `Located.locDst := locSrc` abbrev). -/
def loc (name : String) (t : TowerType) : Located :=
  { locVar := name, locSrc := t }

/-! ## 4. `Rcm`: a state monad over `Frag`

Users write a `do` block whose statements append to an accumulator.
`rustcmd|` finalizes the accumulator into a `LowCT`. -/

/-- Builder monad: wraps a `StateM Frag Unit` so `do`-notation chains
    statements. -/
abbrev Rcm := StateM Frag

namespace Rcm

/-- Execute a builder and return the compiled LowCT. -/
def run (m : Rcm Unit) : LowCT :=
  (StateT.run m Frag.nil).2.compile

/-- Append a fragment to the current program. -/
def emit (f : Frag) : Rcm Unit := modify (· ++ f)

/-! ### 4a. Statement helpers -/

/-- `let <name> : <t> := 0` inside an `Rcm` block. -/
def rc_let (name : String) (t : TowerType) : Rcm Unit :=
  emit (frag_let name t)

/-- `let <name> : u64 := 0`. -/
def rc_letU64 (name : String) : Rcm Unit :=
  emit (frag_letU64 name)

/-- `<name> := n` (scalar assignment). -/
def rc_set (name : String) (n : Nat) : Rcm Unit :=
  emit (frag_scalar name n)

/-- Leaf call `f(&mut dest, &args…)`. -/
def rc_call (f : String) (dest : Located) (args : List Located) : Rcm Unit :=
  emit (frag_call f dest args)

/-- 2-destination leaf call `f(&mut dest1, &mut dest2, &args…)` —
    cswap-shaped operations.  Use when both `dest1` and `dest2` need
    to be mutated by the same call (e.g., constant-time conditional
    swap).  The two destinations must be distinct (borrowOk). -/
def rc_call_swap (f : String) (dest1 dest2 : Located) (args : List Located) : Rcm Unit :=
  emit (frag_callSwap f dest1 dest2 args)

/-- `let clone = oldDest.clone(); f(&mut newDest, &args…)`. -/
def rc_cloneCall (clone : String) (t : TowerType) (oldDest : Located)
    (f : String) (newDest : Located) (args : List Located) : Rcm Unit :=
  emit (frag_cloneCall clone t oldDest f newDest args)

/-- Conditional. The `then`/`else` bodies are sub-`Rcm` blocks. -/
def rc_ifNz (name : String) (thenBr elseBr : Rcm Unit) : Rcm Unit :=
  emit (frag_ifNz name (Rcm.run thenBr) (Rcm.run elseBr))

/-- Conditional without else. -/
def rc_ifNzSimple (name : String) (thenBr : Rcm Unit) : Rcm Unit :=
  emit (frag_ifNz name (Rcm.run thenBr) .RSkip)

/-- Loop. The body is a sub-`Rcm` block. -/
def rc_whileNz (name : String) (body : Rcm Unit) : Rcm Unit :=
  emit (frag_whileNz name (Rcm.run body))

/-- Limb store. -/
def rc_limb (l : Located) (idx : Nat) (v : BitVec 64) : Rcm Unit :=
  emit (frag_limb l idx v)

end Rcm

/-! ## 5. Surface syntax: `rustcmd| do …` -/

/-- `rustcmd| <term>` elaborates `<term>` (typically an `Rcm Unit` `do`-block)
    and compiles it down to a `LowCT`.

    Example:
    ```
    open Rcm in
    #check (rustcmd| do
      rc_let "a" TowerType.TFp
      rc_call "fp_add" (loc "a" TowerType.TFp) []) : LowCT
    ``` -/
syntax "rustcmd| " term : term

macro_rules
  | `(rustcmd| $t:term) => `(Rcm.run $t)

/-! ## 6. Smoke tests -/

open Rcm TowerType

/-- Two-let fragment. -/
example : LowCT := rustcmd| do
  rc_let "a" TFp
  rc_let "b" TFp

/-- A leaf call. -/
example : LowCT := rustcmd| do
  rc_let "a" TFp
  rc_let "b" TFp
  rc_let "c" TFp
  rc_call "fp_add" (loc "c" TFp) [loc "a" TFp, loc "b" TFp]

/-- Scalar + conditional. -/
example : LowCT := rustcmd| do
  rc_letU64 "bit"
  rc_set "bit" 1
  rc_let "x" TFp
  rc_ifNzSimple "bit" do
    rc_call "fp_sub" (loc "x" TFp) [loc "x" TFp, loc "x" TFp]

/-- X25519-ish half-step (sugar-free baseline). -/
example : LowCT := rustcmd| do
  rc_let "x2" TFp
  rc_let "z2" TFp
  rc_let "A" TFp
  rc_let "B" TFp
  rc_call "fp_add" (loc "A" TFp) [loc "x2" TFp, loc "z2" TFp]
  rc_call "fp_sub" (loc "B" TFp) [loc "x2" TFp, loc "z2" TFp]

/-! ## 7. Unrolled loops via Lean's native `for`

`Rcm = StateM Frag` is a `Monad`, so Lean's `for x in xs do …`
`do`-notation works inside `rustcmd| do { … }`. Each loop iteration
runs the body and appends its fragment to the accumulator, giving
fully-unrolled straight-line `LowCT` as output. This is the
readable-source story: write loops in Lean, get unrolled LowCT.

Helper conventions:
- **Variable names per iteration**: use `s!"x_{i}"` (string interpolation)
  to get distinct bindings, or reuse a fixed name if SSA shadowing is
  the intent (each `rc_let name t` just emits a new `RLetZero`). -/

/-- Unroll: 4 fresh Fp let-bindings (`x_0`…`x_3`). -/
example : LowCT := rustcmd| do
  for i in List.range 4 do
    rc_let s!"x_{i}" TFp

/-- Unroll: 8-round straight-line "compress step" shape,
    where each round reads from the current accumulator and
    writes a fresh result. This is the shape that SHA-512's
    80 rounds would take. -/
example : LowCT := rustcmd| do
  rc_let "acc" TFp
  for i in List.range 8 do
    rc_call "round_step" (loc s!"acc_{i+1}" TFp) [loc (if i = 0 then "acc" else s!"acc_{i}") TFp]

/-- Unroll: an X25519-style ladder, 255 iterations of (cswap; step; cswap).
    Full size expansion — readable source, fully-unrolled output. -/
example : LowCT := rustcmd| do
  rc_let "x2" TFp
  rc_let "z2" TFp
  rc_let "x3" TFp
  rc_let "z3" TFp
  rc_letU64 "swap"
  for _i in List.range 255 do
    rc_call "cswap" (loc "x2" TFp) [loc "x3" TFp]
    rc_call "cswap" (loc "z2" TFp) [loc "z3" TFp]
    rc_call "ladder_step" (loc "x2" TFp)
      [loc "z2" TFp, loc "x3" TFp, loc "z3" TFp]
    rc_call "cswap" (loc "x2" TFp) [loc "x3" TFp]
    rc_call "cswap" (loc "z2" TFp) [loc "z3" TFp]

/-- Nested unroll: SHA-512 message-schedule shape.
    16-word block expanded to 80 schedule words via a straight-line recurrence. -/
example : LowCT := rustcmd| do
  rc_let "block" TFp  -- placeholder: real SHA uses TU64 + limb stores
  for t in List.range (80 - 16) do
    let i := t + 16
    rc_call "sched_step"
      (loc s!"w_{i}" TFp)
      [loc s!"w_{i-2}" TFp, loc s!"w_{i-7}" TFp,
       loc s!"w_{i-15}" TFp, loc s!"w_{i-16}" TFp]

/-! ### Size-check smoke tests

Each test verifies the unroll produces the expected number of AST nodes. -/

/-- Counts the total number of LowCT constructor applications (a
    rough "unrolled LoC" metric).

    Migrated to `LowCT.fold` (#350): every leaf node contributes `1`,
    every recursive node contributes `1 +` the sum of its children's sizes.
    `seqLike a b = 1 + a + b` covers the two-child constructors
    (`RSeq`/`RIfNz`/`RFnDef`) and `wrap1 c = 1 + c` the one-child ones
    (`RLetZero`/`RLetU64Zero`/`RWhileNz`/`RFor`/`RBlock`).  A new leaf
    constructor needs no edit here — it falls through to `leaf _ => 1`. -/
def rcSize : LowCT → Nat :=
  LowCT.fold (leaf := fun _ => 1) (seqLike := fun a b => 1 + a + b)
    (wrap1 := fun c => 1 + c)

-- 4 nested `RLetZero` + final `RSkip` = 5 AST nodes. Confirms unrolling
-- fires at compile time (not at runtime).
example : rcSize (rustcmd| do
    for i in List.range 4 do
      rc_let s!"x_{i}" TFp) = 5 := by native_decide

-- 16 iters × `RSeq (RCall _) _` + final `RSkip` = 33 AST nodes.
example : rcSize (rustcmd| do
    for _i in List.range 16 do
      rc_call "step" (loc "a" TFp) [loc "b" TFp]) = 33 := by native_decide

end CatCrypt.Crypto.Jasmin.LowCTDSL
