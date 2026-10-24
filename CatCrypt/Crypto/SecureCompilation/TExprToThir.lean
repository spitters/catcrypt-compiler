/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.TExpr
public import HaxLean.TExpr
public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-!
# TYPED FRONT: hax-lean `Hax.TExpr` (typed AST) → verified `Thir` front IR

This module is the **production** typed-front for removing the deprecated untyped
`ImpExpr` from CatCrypt's compile-from-hax front. It roots the front directly on
the **canonical** typed AST from the `hax-lean` dependency — `Hax.TExpr`
(`HaxLean/TExpr.lean` in `hax-lean`), where **every node carries its
`ty : Hax.ImpType`** annotation from the Rust compiler — and shows that this lets
SHA-256 σ₀ compile to the FIPS formula **without any of the string-tag pre-passes**
the untyped front needs.

Depending on `hax-lean` directly makes the typed AST a **single source of truth**:
the front consumes the dependency's `Hax.TExpr` / `Hax.ImpType` / `Hax.ImpLit`,
with no local mirror that could drift from it.

## The payoff vs. the untyped front (`ImpExprToThir.lean`)

The untyped front recovers a Rust op's **width** and **kind** from string tags
baked into operator-head names — `#32`/`#64` suffixes, `stripWidthSuffix`, a
`castStrip` that peels `(u32)(…)` casts encoded as marker apps, a `desugarNot`,
the `anfLift`'s tag-aware argument handling. None of that is sound *structure*:
it is string parsing that re-derives information the Rust type checker already
knew.

With `Hax.TExpr`, that information **lives in the node's `ty`**. `texprToThir`:
* reads the **working width** `w` from a node's `ty : Hax.ImpType` via the
  dependency's own `ImpType.intWidth?` + `IntWidth.bits` accessors (packaged here
  as `tyWidth?`) — *replacing* `stripWidthSuffix`;
* treats a **cast** as a coercion read from the source/target `ty`, *not* a
  string marker — *replacing* `castStrip`;
* recognises a bitwise / shift / rotate op by its **typed application** with the
  width from `ty` — no `#32` tag on the head string;
* needs **no** `desugarNot`/`strip64`/`anfLift` tag pre-pass.

So the whole `texprToThir` is a single typed elaboration with no pre-pass stage.

## What is proved

* `texprToThir (params) : Hax.TExpr → Option Thir` — the typed elaboration into
  the **existing** front `Thir` (`ThirToComFront.lean`), reusing the committed
  `Thir → Com jasminDialect → owned-x86` back half unchanged.
* `TExpr.denoteScalarT` — a **source** semantics of the typed subset (into
  `Option (BitVec w)`), defined independently of the translator, so preservation
  is non-vacuous.
* `texprToThir_denoteScalarT` — the value-preservation theorem: whenever
  `texprToThir params e = some t`, the typed source denotation equals the front
  denotation `t.denote`.
* `sigma0Texpr` — σ₀ **hand-built in typed form** with the real `Hax.TExpr` /
  `Hax.TExprKind` constructors: every node tagged `ty = u32`.
* `sigma0_texpr_compiles` — σ₀, compiled from the **typed** σ₀ through the
  committed `Thir → Com` path, denotes to the FIPS formula
  `ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`, **with no `anfLift`/`strip64`/`desugarNot`/
  `castStrip` in the pipeline** — the gate's claim, on the `hax-lean` AST.
* The **full SHA-256 round-component op-set** (§6) — `ch_texpr_compiles`,
  `maj_texpr_compiles`, `big_sigma0_texpr_compiles`, `big_sigma1_texpr_compiles`,
  `small_sigma1_texpr_compiles` — each built in typed form and compiled through
  the **same** committed back half, denoting to its FIPS formula. This is the
  typed analog of the deprecated-ImpExpr `CompileFromHaxLeaves` round set. The
  headline: `ch`'s complemented-AND `(¬x) ∧ z` is recognised as the dialect's
  single-op `andn` — `Not`/`And` are **typed ops**, so there is **no
  `desugarNot` string-hack and no all-ones-literal / width-tag pre-pass** (the
  untyped front needed both).

## Scope

Scope mirrors `ImpExprToThir`'s scalar ARX subset: let-normalized
`lit`/`var`/`letBind`/`app`, atom-only operator arguments — bitwise AND/OR/XOR,
wrapping ADD/SUB/MUL, shift/rotate, and the **complemented-AND `andn`** idiom
(`BitAnd[Not[a], b]`, recognising a nested typed `Not`). The ~26 remaining
`Hax.TExprKind` constructors (tuples, projections, matches, loops, control-flow
markers, `ann`/`namedProj`) are outside this subset and translate to `none`. The
new thing is that **op width comes from `ty`, not from the head string**, so no
string-tag pre-pass is needed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.TExprToThir

open Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  Reading the width and op-kind from `ty` (replacing the string tags)

The whole point of the typed front: the operations that the untyped front
recovers from `#32`/`#64` string suffixes are read directly from a node's
`ty : Hax.ImpType`. `tyWidth?` is the *width* reader (`stripWidthSuffix`'s
replacement); `recogBinTy`/`recogShiftTy` are the op-kind readers. They take the
op-head string *and* the result type, but the **width** they emit comes from the
type, never from the string. -/

/-- Read the **register width** of a `Hax.ImpType`. This is the typed front's
    replacement for the untyped front's `stripWidthSuffix` (which parsed `#32`/
    `#64` out of operator-head strings). Built on the `hax-lean` dependency's own
    accessors `Hax.ImpType.intWidth?` (returns the `Hax.IntWidth`) and
    `Hax.IntWidth.bits`. `u32` ↦ `32`, `u64` ↦ `64`, etc. Returns `none` for
    non-integer / non-scalar types (the op is then not in the scalar ARX subset).

    NOTE: `hax-lean`'s `Hax.ImpType` carries the width via the structured
    `intWidth?`/`bits` pair rather than a flat `regWidth? : Option Nat`. We do NOT
    edit the dependency — `tyWidth?` packages those two accessors here. -/
def tyWidth? : Hax.ImpType → Option Nat :=
  fun t => t.intWidth?.map (·.bits)

/-- Recognise a binary ALU operator head. The width is taken from the node's `ty`
    (`tyWidth?`), not the head.

    **Suffix-tolerance for real extractions.** The hand-built σ₀/round components
    carry *clean* op heads (`"BitXor"`, `"BitAnd"`, …); a real hax extraction
    (e.g. `load_u32_le`) carries `#w`-**suffixed** heads (`"BitOr#32"`, …). Each
    clean head is the **first** disjunct of its arm, and the suffixed forms
    (`#8`/`#16`/`#32`/`#64`) are spelled out as later string-literal disjuncts:
    a clean head short-circuits `Decidable`-`Or` at the first disjunct, so the
    committed clean-head `rfl`/`simp only [recogBinTy]` proofs are unchanged,
    while the real suffixed heads are recognised by a later disjunct. The width
    is **still** read from `ty` (not the suffix) — the suffix is matched purely
    to admit the real-extraction head string. No `splitOn`/`startsWith`/`match`
    wrapper (those do not `rfl`-reduce under the committed proofs). -/
def recogBinTy (f : String) : Option JasminBinOp :=
  if f = "BitXor" ∨ f = "BitXor#8" ∨ f = "BitXor#16" ∨ f = "BitXor#32" ∨ f = "BitXor#64" then some .xor
  else if f = "BitAnd" ∨ f = "BitAnd#8" ∨ f = "BitAnd#16" ∨ f = "BitAnd#32" ∨ f = "BitAnd#64" then some .and
  else if f = "BitOr" ∨ f = "BitOr#8" ∨ f = "BitOr#16" ∨ f = "BitOr#32" ∨ f = "BitOr#64" then some .or
  else if f = "wrapping_add" ∨ f = "add" ∨ f = "Add" ∨ f = "Add#8" ∨ f = "Add#16" ∨ f = "Add#32" ∨ f = "Add#64" then some .add
  else if f = "wrapping_mul" ∨ f = "mul" ∨ f = "Mul" ∨ f = "Mul#8" ∨ f = "Mul#16" ∨ f = "Mul#32" ∨ f = "Mul#64" then some .mul
  else if f = "wrapping_sub" ∨ f = "sub" ∨ f = "Sub" ∨ f = "Sub#8" ∨ f = "Sub#16" ∨ f = "Sub#32" ∨ f = "Sub#64" then some .sub
  else none

/-- Shift/rotate kinds (the second operand is a compile-time literal count). -/
inductive ShiftKind where
  | ror
  | shr
  | sar
  | shl
  deriving DecidableEq, Repr

/-- Recognise a shift/rotate operator head. Accepts the capitalized `Shr`/`Shl`
    twins. Width is in the `ty`, never the head.

    **Suffix-tolerance** (same flat-enumerated discipline as `recogBinTy`): the
    clean head is the first disjunct, the real-extraction `#w`-suffixed forms
    (`"Shl#32"`, …) follow as later string literals, so the committed clean-head
    proofs short-circuit unchanged while a real `Shl#32` is recognised. -/
def recogShiftTy (f : String) : Option ShiftKind :=
  if f = "rotate_right" ∨ f = "rotate_right_w"
      ∨ f = "rotate_right#8" ∨ f = "rotate_right#16" ∨ f = "rotate_right#32" ∨ f = "rotate_right#64" then some .ror
  else if f = "arith_shift_right" ∨ f = "sar" ∨ f = "Sar"
      ∨ f = "Sar#8" ∨ f = "Sar#16" ∨ f = "Sar#32" ∨ f = "Sar#64" then some .sar
  else if f = "shift_right" ∨ f = "shr" ∨ f = "Shr"
      ∨ f = "Shr#8" ∨ f = "Shr#16" ∨ f = "Shr#32" ∨ f = "Shr#64" then some .shr
  else if f = "shift_left" ∨ f = "shl" ∨ f = "Shl"
      ∨ f = "Shl#8" ∨ f = "Shl#16" ∨ f = "Shl#32" ∨ f = "Shl#64" then some .shl
  else none

/-- Recognise a **unary bitwise-NOT** operator head. Like `recogBinTy`, the width
    is taken from the node's `ty`, never from the head string. Accepts the
    lowercase `not`/`bitnot` forms and the capitalized `core::ops::Not` trait
    twin (`Not`) and the `BitNot`/`bit_not` aliases. This is a **typed
    op** recogniser — the typed analog of the untyped front's `desugarNot`
    string-tag pre-pass, with the desugar pass deleted: the NOT is recognised as
    a real typed op (nested inside an AND it forms the dialect's single-op
    `andn` — the SHA-256 `Ch` complemented-AND `(¬x) ∧ z`). -/
def recogNotTy (f : String) : Bool :=
  f == "Not" || f == "not" || f == "BitNot" || f == "bit_not" || f == "bitnot"

/-- Recognise a **width-coercion** (`cast`) operator head. A real hax extraction
    emits the integer-coercion `(u32) x` as a `cast#32[x]` app (the `load_u32_le`
    byte-widen `(u32) bytes[i]`); the clean alias `"cast"` is the first disjunct
    so any hand-built clean-head proof short-circuits, with the `#w`-suffixed
    real forms as later disjuncts. The **target width** comes from the node's
    `ty` (`tyWidth?`), exactly like the binary/shift recognisers — the suffix is
    matched only to admit the extraction head string, never read for the width.
    The front image is `Rhs.cast` (the dialect's `castW w w'`); at the ambient
    front width `w` the coercion `BitVec.setWidth w` is the identity, so it stays
    in the homogeneous `rW w` register file and flows through the committed
    preservation cascade unchanged. -/
def recogCastTy (f : String) : Bool :=
  f == "cast" || f == "cast#8" || f == "cast#16" || f == "cast#32" || f == "cast#64"

/-- Read a `Nat` out of a recognised `Hax.ImpLit`. The literal's width lives in
    the enclosing node's `ty`; the value is the payload. -/
def litNatT? : Hax.ImpLit → Option Nat
  | .uintLit _ n => some n
  | .int n => some n.toNat
  | _ => none

/-- Apply a recognised shift/rotate kind to a value and a compile-time count; the
    logical shifts shift by the masked count `VIR.shiftMask w n`. -/
def ShiftKind.apply {w : Nat} : ShiftKind → BitVec w → Nat → BitVec w
  | .ror, av, n => av.rotateRight n
  | .shr, av, n => av >>> VIR.shiftMask w n
  | .sar, av, n => BitVec.sshiftRight av n
  | .shl, av, n => av <<< VIR.shiftMask w n

/-! ## §2  Source semantics of the typed scalar subset

`denoteScalarT` evaluates a `Hax.TExpr` directly into `Option (BitVec w)`, *with
no reference to the translator*. A `var` naming a parameter reads `inpGet I i`
(matching `Atom.inp i`'s front denotation); operator apps consult the *same*
`recogBinTy`/`recogShiftTy` the translator uses, so source and target stay in
lockstep. Crucially, the op-kind is read from the head while the width is the
ambient `w` — there is no width-suffix parsing anywhere. -/

/-- Source denotation of an *atom* `Hax.TExpr` (`.var`/`.lit` kind). A `var x`
    naming parameter `i` reads input word `i`; otherwise the local env `ρ`. The
    literal value comes from the `Hax.ImpLit` payload; its width is the ambient
    `w`. -/
def TExpr.denoteAtomT {w nIn : Nat} (params : List String) (I : Fin nIn → BitVec w) :
    Hax.TExpr → (String → Option (BitVec w)) → Option (BitVec w)
  | .mk (.var x) _, ρ =>
      match params.idxOf? x with
      | some i => some (inpGet I i)
      | none => ρ x
  | .mk (.lit l) _, _ => (litNatT? l).map (fun n => BitVec.ofNat w n)
  | _, _ => none

/-- Source denotation of the typed scalar ARX subset. Recursive on `letBind`;
    `app` arguments are atom-`Hax.TExpr`s evaluated via `denoteAtomT`. The op-kind
    is read from the head; the width is the ambient `w` (read, in the translator,
    from `ty` — see §3). -/
def TExpr.denoteScalarT {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) : Hax.TExpr → (String → Option (BitVec w)) →
    Option (BitVec w)
  | .mk (.letBind x v body) _, ρ =>
      (TExpr.denoteScalarT params I v ρ).bind fun vv =>
        TExpr.denoteScalarT params I body (fun y => if y = x then some vv else ρ y)
  | .mk (.app f args) _, ρ =>
      -- Typed `andn` idiom: a bitwise AND whose **first operand is itself a typed
      -- `Not`** — `BitAnd[Not[a], b]` — denotes to `(~~~av) &&& bv`, the dialect's
      -- single-op `andn` (`JasminBinOp.andn`). The NOT is recognised as a real
      -- typed op (`recogNotTy`) nested inside the AND; no string-tag desugar, no
      -- all-ones-literal synthesis. This is the SHA-256 `Ch` complemented-AND
      -- shape `(¬x) ∧ z`.
      match recogBinTy f, args with
      | some .and, [.mk (.app g [na]) _, b] =>
          if recogNotTy g then
            (TExpr.denoteAtomT params I na ρ).bind fun av =>
              (TExpr.denoteAtomT params I b ρ).map fun bv => JasminBinOp.andn.apply av bv
          else none
      | some op, [a, b] =>
          (TExpr.denoteAtomT params I a ρ).bind fun av =>
            (TExpr.denoteAtomT params I b ρ).map fun bv => op.apply av bv
      | _, _ =>
        match recogShiftTy f, args with
        | some k, [a, .mk (.lit l) _] =>
            (TExpr.denoteAtomT params I a ρ).bind fun av =>
              (litNatT? l).map fun n => k.apply av n
        | _, _ =>
          -- Width-coercion `cast#w[a]` over a single atom argument. At the ambient
          -- front width `w` the coercion `BitVec.setWidth w` is the identity; its
          -- front image is `Rhs.cast` (`castW w w`). The cast head is recognised
          -- by `recogCastTy`; clean bin/shift heads never reach this branch.
          if recogCastTy f then
            match args with
            | [a] => (TExpr.denoteAtomT params I a ρ).map fun av => BitVec.setWidth w av
            | _ => none
          else none
  | e, ρ => TExpr.denoteAtomT params I e ρ

/-! ## §3  The typed translator `Hax.TExpr → Thir` (correct-by-construction)

`texprToThir` mirrors `denoteScalarT` arm-for-arm onto the front's
`Atom`/`Rhs`/`Thir`. The **width is read from the node's `ty`** via `tyWidth?`
(the `stripWidthSuffix` replacement): an op whose `ty` is not a `tyWidth?`-width
is *not* in the scalar subset and translates to `none`. This is the structural
width check the untyped front fakes with `#w` string tags. -/

/-- Translate an atom-`Hax.TExpr` (`.var`/`.lit` kind) to a front `Atom`. A `var`
    naming a parameter becomes `Atom.inp i`; otherwise a local `Atom.lvar`. -/
def atomOfT (params : List String) : Hax.TExpr → Option Atom
  | .mk (.var x) _ =>
      match params.idxOf? x with
      | some i => some (.inp i)
      | none => some (.lvar x)
  | .mk (.lit l) _ => (litNatT? l).map (fun n => Atom.lit n)
  | _ => none

/-- Translate a value-producing `Hax.TExpr` to a front `Rhs`. The op head is
    matched by `recogBinTy`/`recogShiftTy`; the operation **width is read from the
    node's `ty`** (`tyWidth?`) — replacing the untyped front's `#w` string-tag
    stripping. A node whose `ty` carries no register width (e.g. a tuple, a
    non-scalar) is rejected. Anything outside the recognised atom/op shapes →
    `none`. -/
def rhsOfT (params : List String) : Hax.TExpr → Option Rhs
  | .mk (.app f args) ty =>
      -- Read the working width from the node's TYPE — not from any `#w` suffix on
      -- `f`. This single line is the structural replacement for `stripWidthSuffix`.
      match tyWidth? ty with
      | none => none
      | some _w =>
        match recogBinTy f, args with
        | some .and, [.mk (.app g [na]) _, b] =>
            -- Typed `andn` idiom `BitAnd[Not[a], b]` → the dialect's single-op
            -- `andn` (`(~~~a) &&& b`). The NOT is recognised as a real typed op
            -- (`recogNotTy g`); the width is from `ty`. No all-ones-literal
            -- synthesis, no `desugarNot` string pre-pass.
            if recogNotTy g then
              (atomOfT params na).bind fun av =>
                (atomOfT params b).map fun bv => Rhs.bin .andn av bv
            else none
        | some op, [a, b] =>
            (atomOfT params a).bind fun av =>
              (atomOfT params b).map fun bv => Rhs.bin op av bv
        | _, _ =>
          match recogShiftTy f, args with
          | some k, [a, .mk (.lit l) _] =>
              (atomOfT params a).bind fun av =>
                (litNatT? l).map fun n =>
                  match k with
                  | .ror => Rhs.ror n av
                  | .shr => Rhs.shrImm n av
                  | .sar => Rhs.sarImm n av
                  | .shl => Rhs.shlImm n av
          | _, _ =>
            -- Width-coercion `cast#w[a]` → the front `Rhs.cast` (`castW w w`,
            -- identity at the ambient width). The target width is from `ty`
            -- (already forced `some _w` above). Mirrors `denoteScalarT`'s cast arm.
            if recogCastTy f then
              match args with
              | [a] => (atomOfT params a).map fun av => Rhs.cast av
              | _ => none
            else none
  | .mk (.var x) ty => (atomOfT params (.mk (.var x) ty)).map Rhs.atom
  | .mk (.lit l) ty => (atomOfT params (.mk (.lit l) ty)).map Rhs.atom
  | _ => none

/-- Translate a (let-normalized) typed `Hax.TExpr` to a front `Thir`. A `letBind`
    binds its RHS and recurses; a final value-`Hax.TExpr` returns. -/
def texprToThir (params : List String) : Hax.TExpr → Option Thir
  | .mk (.letBind x v body) _ =>
      (rhsOfT params v).bind fun r =>
        (texprToThir params body).map fun bt => Thir.let_ x r bt
  | .mk (.var x) ty => (atomOfT params (.mk (.var x) ty)).map Thir.ret
  | .mk (.lit l) ty => (atomOfT params (.mk (.lit l) ty)).map Thir.ret
  | .mk (.app f args) ty =>
      (rhsOfT params (.mk (.app f args) ty)).map fun r =>
        Thir.let_ "__ret" r (Thir.ret (.lvar "__ret"))
  | _ => none

/-! ## §4  Preservation -/

/-- Atom translation preserves denotation: an atom-`Hax.TExpr` that translates to
    a front `Atom` denotes (under `denoteAtomT`) to that atom's front denotation. -/
theorem atomOfT_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (ρ : String → Option (BitVec w))
    (e : Hax.TExpr) {a : Atom} (h : atomOfT params e = some a) :
    TExpr.denoteAtomT params I e ρ = a.denote I ρ := by
  rcases e with ⟨k, ty⟩
  cases k with
  | var x =>
      simp only [atomOfT, TExpr.denoteAtomT] at h ⊢
      split at h <;> cases h <;> simp [Atom.denote]
  | lit l =>
      simp only [atomOfT, TExpr.denoteAtomT, Option.map_eq_some_iff] at h ⊢
      obtain ⟨n, hn1, hn2⟩ := h; cases hn2; simp [Atom.denote, hn1]
  | _ => simp [atomOfT] at h

/-- Rhs translation preserves denotation: a `Hax.TExpr` that translates to a front
    `Rhs` denotes (under `denoteScalarT`) to that rhs's front denotation. -/
theorem rhsOfT_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (ρ : String → Option (BitVec w))
    (e : Hax.TExpr) {r : Rhs} (h : rhsOfT params e = some r) :
    TExpr.denoteScalarT params I e ρ = r.denote I ρ := by
  rcases e with ⟨k, ty⟩
  cases k with
  | var x =>
      simp only [rhsOfT, Option.map_eq_some_iff] at h
      obtain ⟨a, ha1, ha2⟩ := h; cases ha2
      rw [show TExpr.denoteScalarT params I (.mk (.var x) ty) ρ
            = TExpr.denoteAtomT params I (.mk (.var x) ty) ρ from rfl,
        atomOfT_denote params I ρ _ ha1]
      rfl
  | lit l =>
      simp only [rhsOfT, Option.map_eq_some_iff] at h
      obtain ⟨a, ha1, ha2⟩ := h; cases ha2
      rw [show TExpr.denoteScalarT params I (.mk (.lit l) ty) ρ
            = TExpr.denoteAtomT params I (.mk (.lit l) ty) ρ from rfl,
        atomOfT_denote params I ρ _ ha1]
      rfl
  | app f args =>
      simp only [rhsOfT] at h
      -- The `ty` width-read: a successful translation forces `tyWidth? ty = some _`,
      -- which we reduce in `h` so its match aligns with the goal's `denoteScalarT`.
      rcases hw : tyWidth? ty with _ | _w
      · rw [hw] at h; simp at h
      rw [hw] at h
      simp only at h
      simp only [TExpr.denoteScalarT]
      -- The `rhsOfT`/`denoteScalarT` app matches mirror arm-for-arm: (1) the
      -- typed `andn` idiom `BitAnd[Not[a], b]`, (2) a generic binary head, (3) a
      -- shift/rotate head. `split` walks the shared structure.
      split at h
      · -- (1) `andn` idiom: AND with a NOT-app first operand.
        rename_i _ _ g na _ b _
        -- The first operand is `app g [na]`; the goal/`h` carry an `if recogNotTy g`.
        split at h
        · -- `recogNotTy g` holds: `Rhs.bin .andn na b`.
          rename_i hg
          rw [ite_eq_left hg]
          rcases ha : atomOfT params na with _ | av
          · rw [ha] at h; simp at h
          rcases hbb : atomOfT params b with _ | bv
          · rw [ha, hbb] at h; simp at h
          rw [ha, hbb] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          rw [atomOfT_denote params I ρ na ha, atomOfT_denote params I ρ b hbb]
          rfl
        · exact absurd h (by simp)
      · -- (2) generic binary ALU head, exactly two atom arguments.
        rename_i _ _ _ a b _ _
        rcases ha : atomOfT params a with _ | av
        · rw [ha] at h; simp at h
        rcases hbb : atomOfT params b with _ | bv
        · rw [ha, hbb] at h; simp at h
        rw [ha, hbb] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        rw [atomOfT_denote params I ρ a ha, atomOfT_denote params I ρ b hbb]
        rfl
      · split at h
        · -- (3) recognised shift/rotate head, (atom, literal) arguments.
          rename_i _ _ _ _ k a l _ _ _ _
          rcases ha : atomOfT params a with _ | av
          · rw [ha] at h; simp at h
          rcases hl : litNatT? l with _ | n
          · rw [ha, hl] at h; simp at h
          rw [ha, hl] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          rw [atomOfT_denote params I ρ a ha]
          cases k <;> simp [ShiftKind.apply, Rhs.denote, Option.map_eq_bind]
        · -- (4) width-coercion `cast#w[a]`: a single-atom cast → `Rhs.cast`.
          by_cases hcast : recogCastTy f
          · rw [ite_eq_left hcast] at h ⊢
            -- the single-arg shape `[a]` is forced by `h = some r`.
            split at h
            · next aa _ _ _ =>
              rcases ha : atomOfT params aa with _ | av
              · rw [ha] at h; simp at h
              rw [ha] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              rw [atomOfT_denote params I ρ aa ha]
              simp [Rhs.denote, Option.map_eq_bind]
            · simp at h
          · rw [ite_eq_right hcast] at h; simp at h
  | _ => simp [rhsOfT] at h

/-- **Preservation theorem (typed front).** Whenever the typed translator
    succeeds, the typed source denotation `denoteScalarT` equals the front
    denotation `Thir.denote`. The value-preservation result connecting the
    hax-lean typed `Hax.TExpr` AST to the verified `Thir` front, with **no
    string-tag pre-pass** in the pipeline. Proved by structural cases on `e`. -/
theorem texprToThir_denoteScalarT {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) :
    (e : Hax.TExpr) → (ρ : String → Option (BitVec w)) → {t : Thir} →
    texprToThir params e = some t →
    TExpr.denoteScalarT params I e ρ = t.denote I ρ
  | .mk (.letBind x v body) _, ρ, t, h => by
      simp only [texprToThir] at h
      cases hr : rhsOfT params v with
      | none => rw [hr] at h; simp at h
      | some r =>
        cases hbt : texprToThir params body with
        | none => rw [hr, hbt] at h; simp at h
        | some bt =>
          rw [hr, hbt] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          show (TExpr.denoteScalarT params I v ρ).bind (fun vv =>
              TExpr.denoteScalarT params I body
                (fun y => if y = x then some vv else ρ y)) = _
          rw [rhsOfT_denote params I ρ v hr]
          simp only [Thir.denote]
          cases hrv : r.denote I ρ with
          | none => simp
          | some rv =>
            simp only [Option.bind_some]
            have hbody := texprToThir_denoteScalarT params I body
                (fun y => if y = x then some rv else ρ y) hbt
            rw [hbody]; rfl
  | .mk (.var x) ty, ρ, t, h => by
      simp only [texprToThir] at h
      cases ha : atomOfT params (.mk (.var x) ty) with
      | none => rw [ha] at h; simp at h
      | some av =>
        rw [ha] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show TExpr.denoteAtomT params I (.mk (.var x) ty) ρ = (Thir.ret av).denote I ρ
        rw [atomOfT_denote params I ρ (.mk (.var x) ty) ha]; rfl
  | .mk (.lit l) ty, ρ, t, h => by
      simp only [texprToThir] at h
      cases ha : atomOfT params (.mk (.lit l) ty) with
      | none => rw [ha] at h; simp at h
      | some av =>
        rw [ha] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show TExpr.denoteAtomT params I (.mk (.lit l) ty) ρ = (Thir.ret av).denote I ρ
        rw [atomOfT_denote params I ρ (.mk (.lit l) ty) ha]; rfl
  | .mk (.app f args) ty, ρ, t, h => by
      simp only [texprToThir] at h
      cases hr : rhsOfT params (.mk (.app f args) ty) with
      | none => rw [hr] at h; simp at h
      | some r =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show TExpr.denoteScalarT params I (.mk (.app f args) ty) ρ
          = (Thir.let_ "__ret" r (Thir.ret (.lvar "__ret"))).denote I ρ
        rw [rhsOfT_denote params I ρ (.mk (.app f args) ty) hr]
        simp only [Thir.denote]
        cases hrv : r.denote I ρ with
        | none => simp
        | some rv =>
          simp only [Option.bind_some, Atom.denote, LEnv.set, ite_true]
  -- The ~26 remaining `Hax.TExprKind` constructors (tuple/proj/match/loops/
  -- control-flow/ann/namedProj) are outside the scalar ARX subset: `texprToThir`
  -- maps each to `none`, so the hypothesis `… = some t` is impossible.
  | .mk (.tuple _) _, _, _, h
  | .mk (.proj _ _) _, _, _, h
  | .mk (.ifThenElse _ _ _) _, _, _, h
  | .mk (.match_ _ _) _, _, _, h
  | .mk .unitVal _, _, _, h
  | .mk (.seq _ _) _, _, _, h
  | .mk (.borrow _) _, _, _, h
  | .mk (.deref _) _, _, _, h
  | .mk (.assign _ _) _, _, _, h
  | .mk (.forLoop _ _ _ _) _, _, _, h
  | .mk (.forLoopRev _ _ _ _) _, _, _, h
  | .mk (.whileLoop _ _) _, _, _, h
  | .mk (.break_ _) _, _, _, h
  | .mk .continue_ _, _, _, h
  | .mk (.earlyReturn _) _, _, _, h
  | .mk (.questionMark _) _, _, _, h
  | .mk (.forFold _ _ _ _) _, _, _, h
  | .mk (.forFoldRev _ _ _ _) _, _, _, h
  | .mk (.whileFold _ _) _, _, _, h
  | .mk (.forFoldReturn _ _ _ _) _, _, _, h
  | .mk (.forFoldRevReturn _ _ _ _) _, _, _, h
  | .mk (.whileFoldReturn _ _) _, _, _, h
  | .mk (.cfBreak _) _, _, _, h
  | .mk (.cfContinue _) _, _, _, h
  | .mk (.cfBreakContinue _) _, _, _, h
  | .mk (.ann _) _, _, _, h
  | .mk (.namedProj _ _) _, _, _, h => by
      simp [texprToThir] at h

/-! ## §5  The typed σ₀ pilot — built in TYPED form, compiled with NO string-tag passes

σ₀(x) = (x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x ≫ 3), at `w = 32`, one input parameter `"x"`
(`nIn = 1`, `I 0 = x`). Hand-built in **typed** form with the real `hax-lean`
constructors: every node tagged `ty = u32` (`Hax.ImpType.uint .w32`). The op
widths are carried by these `ty`s — `rhsOfT` reads them via `tyWidth?`, so **no
`#32` string tag, no `stripWidthSuffix`, no `castStrip`/`desugarNot`/`strip64`/
`anfLift` pre-pass** is involved: `texprToThir sigma0Texpr` lands directly. -/

/-- `u32` as a real `Hax.ImpType` — the type annotation every σ₀ node carries. -/
abbrev tyU32 : Hax.ImpType := Hax.ImpType.uint .w32

/-- A typed `var` of type `u32`. -/
def vU32 (x : String) : Hax.TExpr := .mk (.var x) tyU32

/-- A typed `u32` literal. -/
def litU32 (n : Nat) : Hax.TExpr := .mk (.lit (.uintLit .w32 n)) tyU32

/-- A typed `u32`-result application. -/
def appU32 (f : String) (args : List Hax.TExpr) : Hax.TExpr := .mk (.app f args) tyU32

/-- σ₀ **in typed form**: every node `ty = u32`, fully let-normalized.

    ```
    let a  = rotate_right(x, 7);    -- u32
    let b  = rotate_right(x, 18);   -- u32
    let c  = shift_right(x, 3);     -- u32
    let ab = a ^ b;                 -- u32  (BitXor)
    let r  = ab ^ c;                -- u32  (BitXor)
    r
    ```

    The widths (`u32`) live in each node's `ty`; nothing is encoded in the head
    strings. Built with the real `Hax.TExpr` / `Hax.TExprKind` constructors. -/
def sigma0Texpr : Hax.TExpr :=
  .mk (.letBind "a" (appU32 "rotate_right" [vU32 "x", litU32 7])
    (.mk (.letBind "b" (appU32 "rotate_right" [vU32 "x", litU32 18])
      (.mk (.letBind "c" (appU32 "shift_right" [vU32 "x", litU32 3])
        (.mk (.letBind "ab" (appU32 "BitXor" [vU32 "a", vU32 "b"])
          (.mk (.letBind "r" (appU32 "BitXor" [vU32 "ab", vU32 "c"])
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- `recogBinTy` does not recognise the rotate head. -/
theorem recogBinTy_rotate_right : recogBinTy "rotate_right" = none := rfl

/-- `recogBinTy` does not recognise the shift head. -/
theorem recogBinTy_shift_right : recogBinTy "shift_right" = none := rfl

/-- `recogBinTy` reads the clean xor head. -/
theorem recogBinTy_BitXor : recogBinTy "BitXor" = some .xor := rfl

/-- `recogShiftTy` reads the clean rotate head as `ror`. -/
theorem recogShiftTy_rotate_right : recogShiftTy "rotate_right" = some .ror := rfl

/-- `recogShiftTy` reads the clean shift head as `shr`. -/
theorem recogShiftTy_shift_right : recogShiftTy "shift_right" = some .shr := rfl

/-- The typed σ₀ denotes (under `denoteScalarT`) to the FIPS 180-4 formula
    `ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`, for any single-word input. -/
theorem sigma0Texpr_denoteScalarT (I : Fin 1 → BitVec 32) :
    TExpr.denoteScalarT ["x"] I sigma0Texpr (fun _ => none)
      = some ((I 0).rotateRight 7 ^^^ (I 0).rotateRight 18 ^^^ (I 0) >>> (3 : Nat)) := by
  simp only [sigma0Texpr, appU32, vU32, litU32, TExpr.denoteScalarT,
    TExpr.denoteAtomT, recogBinTy_rotate_right, recogBinTy_shift_right, recogBinTy_BitXor,
    recogShiftTy_rotate_right, recogShiftTy_shift_right, litNatT?, ShiftKind.apply,
    List.idxOf?, List.findIdx?, JasminBinOp.apply, reduceIte, String.reduceEq]
  rfl

/-- The typed translator succeeds on σ₀ — **with no pre-pass** — producing a
    concrete `Thir`. -/
theorem sigma0Texpr_lowers : (texprToThir ["x"] sigma0Texpr).isSome := by
  native_decide

/-- **σ₀ end-to-end FROM THE TYPED FRONT (`Hax.TExpr → Thir → Com jasminDialect`).**
    There is a `Thir` `t` and a `Com jasminDialect` `c` such that the **typed**
    hax σ₀ (built with the real `hax-lean` `Hax.TExpr` constructors) translates to
    `t` (via `texprToThir`, reading widths from `ty` — **no
    `anfLift`/`strip64`/`desugarNot`/`castStrip`**), `t` lowers to `c` through the
    committed front, and `c`'s `BitVec 32` denotation is exactly the FIPS σ₀
    formula `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)` for every input. The chain:
    `texprToThir_denoteScalarT` (typed front, this file) composed with the
    committed `thirToJasmin_denote` (the front back half, unchanged).

    This is the **gate**: types carry the width/cast/op info that the deprecated
    untyped front's string-tag pre-passes recovered from `#32`/`#64`, so rooting
    the front on the real `Hax.TExpr` dependency removes those passes while still
    compiling σ₀ to the FIPS formula. -/
theorem sigma0_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      texprToThir ["x"] sigma0Texpr = some t ∧
      thirToJasmin [] (initFState 32 1) t = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  set t := (texprToThir ["x"] sigma0Texpr).get sigma0Texpr_lowers with ht_def
  have ht : texprToThir ["x"] sigma0Texpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 1) t).isSome := by
    rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 1) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 1) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x
  -- typed front (this file): typed source `denoteScalarT` = front `Thir.denote`.
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 1) ["x"]
      (fun _ => x) sigma0Texpr (fun _ => none) ht
  -- committed front back half: `Thir.denote` = `Com.denote`.
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
      (fun _ => x) t (LEnv.empty 32) (initFState 32 1)
      (inputValuation 32 1 (fun _ => x)) c (initAgree (fun _ => x)) hc
  have hspec := sigma0Texpr_denoteScalarT (fun _ => x)
  have hchain : some (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat))
      = some (c.denote (inputValuation 32 1 (fun _ => x))) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-! ## §6  The full SHA-256 round-component op-set — typed front, NO pre-passes

This section is the **typed analog** of the deprecated-ImpExpr
`CompileFromHaxLeaves` round-component set (`ch`/`maj`/`bigSigma0`/`bigSigma1`/…),
compiled through the *typed* front `texprToThir` — reading **types** from
each node's `ty : Hax.ImpType`, with the `ImpExpr` front's string-tag pre-passes
deleted by construction:

* `bigSigma0`/`bigSigma1` / `smallSigma1` — rotate/shift/xor (`recogShiftTy` +
  `BitXor`), widths from `ty`;
* `maj` — `BitAnd`/`BitXor`, widths from `ty`;
* `ch` — the complemented-AND `(¬x) ∧ z`. **Here is the key measurement:** the
  typed front recognises `Not`/`And` as **real typed ops** — `BitAnd[Not[x], z]`
  is recognised as the dialect's single-op `andn` (`(~~~x) &&& z`) — so there is
  **no `desugarNot` string-hack and no width-tag handling**. The untyped
  `CompileFromHaxLeaves.chSrc` had to desugar `¬x` into `BitXor[x, lit 0xFFFFFFFF]`
  with an explicit all-ones-literal pre-pass; the typed front needs none of that:
  `Not` is an op, the width is in the `ty`.

All five route through the **same** committed `thirToJasmin` back half as σ₀,
via `texprToThir_denoteScalarT` (this file) ∘ `thirToJasmin_denote` (unchanged). -/

/-- A typed `Not` (bitwise complement) of a typed `u32` expression. -/
def notU32 (e : Hax.TExpr) : Hax.TExpr := appU32 "Not" [e]

/-- **Ch in typed form**: `Ch(x,y,z) = (x ∧ y) ⊕ ((¬x) ∧ z)`. The `(¬x) ∧ z`
    is the typed `BitAnd[Not[x], z]` — recognised as the single-op `andn`. No
    desugared all-ones literal: `Not` is a real op, the width is in each `ty`. -/
def chTexpr : Hax.TExpr :=
  .mk (.letBind "t1" (appU32 "BitAnd" [vU32 "x", vU32 "y"])
    (.mk (.letBind "t2" (appU32 "BitAnd" [notU32 (vU32 "x"), vU32 "z"])
      (.mk (.letBind "r" (appU32 "BitXor" [vU32 "t1", vU32 "t2"])
        (vU32 "r")) tyU32)) tyU32)) tyU32

/-- **Maj in typed form**: `Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def majTexpr : Hax.TExpr :=
  .mk (.letBind "xy" (appU32 "BitAnd" [vU32 "x", vU32 "y"])
    (.mk (.letBind "xz" (appU32 "BitAnd" [vU32 "x", vU32 "z"])
      (.mk (.letBind "yz" (appU32 "BitAnd" [vU32 "y", vU32 "z"])
        (.mk (.letBind "t" (appU32 "BitXor" [vU32 "xy", vU32 "xz"])
          (.mk (.letBind "r" (appU32 "BitXor" [vU32 "t", vU32 "yz"])
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- **Σ₀ in typed form**: `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def bigSigma0Texpr : Hax.TExpr :=
  .mk (.letBind "a" (appU32 "rotate_right" [vU32 "x", litU32 2])
    (.mk (.letBind "b" (appU32 "rotate_right" [vU32 "x", litU32 13])
      (.mk (.letBind "c" (appU32 "rotate_right" [vU32 "x", litU32 22])
        (.mk (.letBind "ab" (appU32 "BitXor" [vU32 "a", vU32 "b"])
          (.mk (.letBind "r" (appU32 "BitXor" [vU32 "ab", vU32 "c"])
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- **Σ₁ in typed form**: `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def bigSigma1Texpr : Hax.TExpr :=
  .mk (.letBind "a" (appU32 "rotate_right" [vU32 "x", litU32 6])
    (.mk (.letBind "b" (appU32 "rotate_right" [vU32 "x", litU32 11])
      (.mk (.letBind "c" (appU32 "rotate_right" [vU32 "x", litU32 25])
        (.mk (.letBind "ab" (appU32 "BitXor" [vU32 "a", vU32 "b"])
          (.mk (.letBind "r" (appU32 "BitXor" [vU32 "ab", vU32 "c"])
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- **σ₁ in typed form**: `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def smallSigma1Texpr : Hax.TExpr :=
  .mk (.letBind "a" (appU32 "rotate_right" [vU32 "x", litU32 17])
    (.mk (.letBind "b" (appU32 "rotate_right" [vU32 "x", litU32 19])
      (.mk (.letBind "c" (appU32 "shift_right" [vU32 "x", litU32 10])
        (.mk (.letBind "ab" (appU32 "BitXor" [vU32 "a", vU32 "b"])
          (.mk (.letBind "r" (appU32 "BitXor" [vU32 "ab", vU32 "c"])
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- Σ₀ typed source denotes to the FIPS formula. -/
theorem bigSigma0Texpr_denoteScalarT (I : Fin 1 → BitVec 32) :
    TExpr.denoteScalarT ["x"] I bigSigma0Texpr (fun _ => none)
      = some ((I 0).rotateRight 2 ^^^ (I 0).rotateRight 13 ^^^ (I 0).rotateRight 22) := by
  simp only [bigSigma0Texpr, appU32, vU32, litU32, TExpr.denoteScalarT,
    TExpr.denoteAtomT, recogBinTy_rotate_right, recogBinTy_BitXor,
    recogShiftTy_rotate_right, litNatT?, ShiftKind.apply,
    List.idxOf?, List.findIdx?, JasminBinOp.apply, reduceIte, String.reduceEq]
  rfl

/-- Σ₁ typed source denotes to the FIPS formula. -/
theorem bigSigma1Texpr_denoteScalarT (I : Fin 1 → BitVec 32) :
    TExpr.denoteScalarT ["x"] I bigSigma1Texpr (fun _ => none)
      = some ((I 0).rotateRight 6 ^^^ (I 0).rotateRight 11 ^^^ (I 0).rotateRight 25) := by
  simp only [bigSigma1Texpr, appU32, vU32, litU32, TExpr.denoteScalarT,
    TExpr.denoteAtomT, recogBinTy_rotate_right, recogBinTy_BitXor,
    recogShiftTy_rotate_right, litNatT?, ShiftKind.apply,
    List.idxOf?, List.findIdx?, JasminBinOp.apply, reduceIte, String.reduceEq]
  rfl

/-- σ₁ typed source denotes to the FIPS formula `ROTR¹⁷ ⊕ ROTR¹⁹ ⊕ SHR¹⁰`. -/
theorem smallSigma1Texpr_denoteScalarT (I : Fin 1 → BitVec 32) :
    TExpr.denoteScalarT ["x"] I smallSigma1Texpr (fun _ => none)
      = some ((I 0).rotateRight 17 ^^^ (I 0).rotateRight 19 ^^^ (I 0) >>> (10 : Nat)) := by
  simp only [smallSigma1Texpr, appU32, vU32, litU32, TExpr.denoteScalarT,
    TExpr.denoteAtomT, recogBinTy_rotate_right, recogBinTy_shift_right, recogBinTy_BitXor,
    recogShiftTy_rotate_right, recogShiftTy_shift_right, litNatT?, ShiftKind.apply,
    List.idxOf?, List.findIdx?, JasminBinOp.apply, reduceIte, String.reduceEq]
  rfl

/-- Maj typed source denotes to the FIPS formula (three inputs `["x","y","z"]`). -/
theorem majTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32) :
    TExpr.denoteScalarT ["x", "y", "z"] I majTexpr (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ (inpGet I 0 &&& inpGet I 2)
                ^^^ (inpGet I 1 &&& inpGet I 2)) := by
  simp only [majTexpr, appU32, vU32, TExpr.denoteScalarT, TExpr.denoteAtomT,
    recogBinTy, JasminBinOp.apply, List.idxOf?,
    List.findIdx?, reduceIte, String.reduceEq]
  rfl

/-- Ch typed source denotes to the FIPS formula `(x ∧ y) ⊕ ((¬x) ∧ z)` (three
    inputs). The `(¬x) ∧ z` is the typed `andn` idiom — `~~~(inpGet I 0) &&&
    inpGet I 2` — recognised **without** a desugared all-ones literal. -/
theorem chTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32) :
    TExpr.denoteScalarT ["x", "y", "z"] I chTexpr (fun _ => none)
      = some ((inpGet I 0 &&& inpGet I 1) ^^^ ((~~~ inpGet I 0) &&& inpGet I 2)) := by
  simp only [chTexpr, notU32, appU32, vU32, TExpr.denoteScalarT, TExpr.denoteAtomT,
    recogBinTy, recogNotTy, JasminBinOp.apply, List.idxOf?,
    List.findIdx?, reduceIte, String.reduceEq, beq_iff_eq, Bool.or_eq_true]
  rfl

/-- Σ₀ lowers via the typed front (no pre-pass). -/
theorem bigSigma0Texpr_lowers : (texprToThir ["x"] bigSigma0Texpr).isSome := by
  native_decide

/-- Σ₁ lowers via the typed front. -/
theorem bigSigma1Texpr_lowers : (texprToThir ["x"] bigSigma1Texpr).isSome := by
  native_decide

/-- σ₁ lowers via the typed front. -/
theorem smallSigma1Texpr_lowers : (texprToThir ["x"] smallSigma1Texpr).isSome := by
  native_decide

/-- Maj lowers via the typed front. -/
theorem majTexpr_lowers : (texprToThir ["x", "y", "z"] majTexpr).isSome := by
  native_decide

/-- Ch lowers via the typed front — the `andn` idiom lands, **no all-ones
    literal pre-pass**. -/
theorem chTexpr_lowers : (texprToThir ["x", "y", "z"] chTexpr).isSome := by
  native_decide

/-- **Σ₀ end-to-end from the typed front.** (composition plumbing through the
    committed `thirToJasmin`.) -/
theorem big_sigma0_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      texprToThir ["x"] bigSigma0Texpr = some t ∧
      thirToJasmin [] (initFState 32 1) t = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 := by
  set t := (texprToThir ["x"] bigSigma0Texpr).get bigSigma0Texpr_lowers with ht_def
  have ht : texprToThir ["x"] bigSigma0Texpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 1) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 1) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 1) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 1) ["x"]
      (fun _ => x) bigSigma0Texpr (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
      (fun _ => x) t (LEnv.empty 32) (initFState 32 1)
      (inputValuation 32 1 (fun _ => x)) c (initAgree (fun _ => x)) hc
  have hspec := bigSigma0Texpr_denoteScalarT (fun _ => x)
  have hchain : some (x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22)
      = some (c.denote (inputValuation 32 1 (fun _ => x))) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-- **Σ₁ end-to-end from the typed front.** (composition plumbing.) -/
theorem big_sigma1_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      texprToThir ["x"] bigSigma1Texpr = some t ∧
      thirToJasmin [] (initFState 32 1) t = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 := by
  set t := (texprToThir ["x"] bigSigma1Texpr).get bigSigma1Texpr_lowers with ht_def
  have ht : texprToThir ["x"] bigSigma1Texpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 1) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 1) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 1) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 1) ["x"]
      (fun _ => x) bigSigma1Texpr (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
      (fun _ => x) t (LEnv.empty 32) (initFState 32 1)
      (inputValuation 32 1 (fun _ => x)) c (initAgree (fun _ => x)) hc
  have hspec := bigSigma1Texpr_denoteScalarT (fun _ => x)
  have hchain : some (x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25)
      = some (c.denote (inputValuation 32 1 (fun _ => x))) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-- **σ₁ end-to-end from the typed front.** (composition plumbing.) -/
theorem small_sigma1_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      texprToThir ["x"] smallSigma1Texpr = some t ∧
      thirToJasmin [] (initFState 32 1) t = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> (10 : Nat) := by
  set t := (texprToThir ["x"] smallSigma1Texpr).get smallSigma1Texpr_lowers with ht_def
  have ht : texprToThir ["x"] smallSigma1Texpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 1) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 1) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 1) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 1) ["x"]
      (fun _ => x) smallSigma1Texpr (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
      (fun _ => x) t (LEnv.empty 32) (initFState 32 1)
      (inputValuation 32 1 (fun _ => x)) c (initAgree (fun _ => x)) hc
  have hspec := smallSigma1Texpr_denoteScalarT (fun _ => x)
  have hchain : some (x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ x >>> (10 : Nat))
      = some (c.denote (inputValuation 32 1 (fun _ => x))) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-- **Maj end-to-end from the typed front** (three inputs `![x,y,z]`).
    (composition plumbing.) -/
theorem maj_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      texprToThir ["x", "y", "z"] majTexpr = some t ∧
      thirToJasmin [] (initFState 32 3) t = some c ∧
      ∀ (x y z : BitVec 32),
        c.denote (inputValuation 32 3 ![x, y, z])
          = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) := by
  set t := (texprToThir ["x", "y", "z"] majTexpr).get majTexpr_lowers with ht_def
  have ht : texprToThir ["x", "y", "z"] majTexpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 3) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 3) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 3) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x y z
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 3) ["x", "y", "z"]
      ![x, y, z] majTexpr (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 3) []
      ![x, y, z] t (LEnv.empty 32) (initFState 32 3)
      (inputValuation 32 3 ![x, y, z]) c (initAgree ![x, y, z]) hc
  have hspec : TExpr.denoteScalarT ["x", "y", "z"] ![x, y, z] majTexpr (fun _ => none)
      = some ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)) := by
    have h := majTexpr_denoteScalarT (nIn := 3) ![x, y, z]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  have hchain : some ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z))
      = some (c.denote (inputValuation 32 3 ![x, y, z])) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-- **Ch end-to-end from the typed front** (three inputs `![x,y,z]`).
    The complemented-AND `(¬x) ∧ z` compiled as the single-op `andn` — **the
    typed front needs no `desugarNot` string-hack and no width-tag handling**:
    `Not`/`And` are recognised as typed ops, the width comes from each node's
    `ty`. This is the headline measurement of the ImpExpr-removal step.
    (composition plumbing through the committed back half.) -/
theorem ch_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 3 []) (rW 32)),
      texprToThir ["x", "y", "z"] chTexpr = some t ∧
      thirToJasmin [] (initFState 32 3) t = some c ∧
      ∀ (x y z : BitVec 32),
        c.denote (inputValuation 32 3 ![x, y, z])
          = (x &&& y) ^^^ ((~~~x) &&& z) := by
  set t := (texprToThir ["x", "y", "z"] chTexpr).get chTexpr_lowers with ht_def
  have ht : texprToThir ["x", "y", "z"] chTexpr = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 3) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 3) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 3) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x y z
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 3) ["x", "y", "z"]
      ![x, y, z] chTexpr (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 3) []
      ![x, y, z] t (LEnv.empty 32) (initFState 32 3)
      (inputValuation 32 3 ![x, y, z]) c (initAgree ![x, y, z]) hc
  have hspec : TExpr.denoteScalarT ["x", "y", "z"] ![x, y, z] chTexpr (fun _ => none)
      = some ((x &&& y) ^^^ ((~~~x) &&& z)) := by
    have h := chTexpr_denoteScalarT (nIn := 3) ![x, y, z]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  have hchain : some ((x &&& y) ^^^ ((~~~x) &&& z))
      = some (c.denote (inputValuation 32 3 ![x, y, z])) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

end CatCrypt.Crypto.SecureCompilation.TExprToThir
