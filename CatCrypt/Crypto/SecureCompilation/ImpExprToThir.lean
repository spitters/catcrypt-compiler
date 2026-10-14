/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import HaxLean.AST
public import HaxLean.AST
public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-!
# C2: hax `ImpExpr` extraction AST → verified `Thir` front IR

This module is the **C2** step of the verified-compiler plan: it connects the
hax extraction AST (`Hax.ImpExpr`, the imperative-expression image of
the Rust source) to the verified `Thir` front IR
(`CatCrypt.Crypto.SecureCompilation.ThirToComFront.Thir`), **value-preservingly**,
and exercises the connection end-to-end on the SHA-256 message-schedule leaf σ₀.

## What it adds over `ThirToComFront`

`ThirToComFront.lean` lowers a hand-written `Thir` all the way to a
`Com jasminDialect` (emitted owned-x86) with the universal preservation theorem
`thirToJasmin_denote`. This module supplies the *top* of the chain: a verified
translator from the `ImpExpr` the hax pipeline actually produces into that
`Thir`, with the preservation theorem and the σ₀
demo that threads `ImpExpr → Thir → Com` in one statement.

## The supported subset (v1 — scalar, let-normalized ARX)

The translator is **correct-by-construction**: it handles only the let-normalized
scalar ARX subset and returns `none` on everything else, so whatever it *does*
translate is provably value-preserving. Concretely it accepts:

* `ImpExpr.lit (.uintLit _ n | .int n)` — a fixed-width / integer literal.
* `ImpExpr.var x` — a parameter (→ `Atom.inp i`) or a let-bound local
  (→ `Atom.lvar x`).
* `ImpExpr.letBind x v body` — with `v` a flat operator application (or atom)
  whose arguments are already atoms (the ANF / charon-shaped restriction).
* `ImpExpr.app f args` — recognised operator heads (see `recogBin`,
  `recogShift`); arguments must be atoms (`.var`/`.lit`) **or** an indexed array
  read `index[w, k]` (see `indexAtom?`). A general nested-app argument still makes
  the whole translation `none` (the ANF restriction).
* `ImpExpr.app "index" [.var w, .lit k]` — an **indexed read of the array
  parameter** `w` (when `w ∈ params`), recognised as the input atom `Atom.inp k`
  (denoting to `inpGet I k`). This is the leaf that lets real (non let-flattened)
  hax bodies — which read scalars out of an array param via `index` nested inside
  arith apps — translate. Under this array-param convention the bare `var w`
  itself is *not* an atom (it is the whole array); inputs are touched only through
  `index`.

Operator heads come in both the lowercase `wrapping_*`/`add`/`shr` forms and the
**capitalized** `core::ops`-trait forms (`Add`/`Mul`/`Sub`/`Shr`/`Shl`) real hax
extractions emit; the capitalized twins denote identically (see `recogBin`,
`recogShift`).

Every other `ImpExpr` constructor (`tuple`, `proj`, `ifThenElse`, `match_`,
loops, control-flow, refs, …) translates to `none`. Coverage is intentionally
narrow; correctness is total.

## Recognised operator heads

| head string(s)                       | target `Rhs` / op                |
|--------------------------------------|----------------------------------|
| `BitXor`                             | `Rhs.bin .xor`                   |
| `BitAnd`                             | `Rhs.bin .and`                   |
| `BitOr`                              | `Rhs.bin .or`                    |
| `wrapping_add` / `add`               | `Rhs.bin .add`                   |
| `wrapping_mul` / `mul`               | `Rhs.bin .mul`                   |
| `wrapping_sub` / `sub`               | `Rhs.bin .sub`                   |
| `rotate_right` / `rotate_right_w`    | `Rhs.ror n` (2nd arg literal `n`)|
| `shift_right` / `shr`                | `Rhs.shrImm n` (2nd arg literal) |
| `shift_left` / `shl`                 | `Rhs.shlImm n` (2nd arg literal) |

## What is proved

* `ImpExpr.denoteScalar` — a **source** semantics for the subset, evaluating an
  `ImpExpr` into `Option (BitVec w)` *independently of the translator*. This is
  what makes the preservation theorem non-vacuous: it relates two separately
  defined denotations. (App arguments are evaluated through `denoteAtomExpr`,
  the same atom-only leaf the translator's `atomOf` consumes — the ANF
  discipline.)
* `impExprToThir_denoteScalar` — the preservation theorem: whenever
  `impExprToThir params e = some t`, the source denotation `e.denoteScalar`
  equals the front denotation `t.denote`. Proved by structural induction on `e`.
* `sigma0Src_to_jasmin` — the σ₀ end-to-end demo: `ImpExpr → Thir → Com`, with
  the concrete `(x ror 7) ^^^ (x ror 18) ^^^ (x >>> 3)` `BitVec 32` formula on
  the right, threading `impExprToThir_denoteScalar` then the front's
  `thirToJasmin_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ImpExprToThir

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §1  Operator-head recognisers

A binary ALU head maps to a `JasminBinOp`; a shift/rotate head maps to a tag we
resolve against a literal count. Both `denoteScalar` and the translator consult
*these same* recognisers, so the source and target stay in lockstep. -/

/-- Recognise a binary ALU operator head. Besides the lowercase `wrapping_*`/`add`
    forms, this also accepts the **capitalized** operator-trait heads
    (`Add`/`Mul`/`Sub`, and `BitXor`/`BitAnd`/`BitOr`) that real hax extractions
    emit via the `core::ops` trait convention. The capitalized twins denote
    *identically* to their lowercase counterparts. -/
def recogBin (f : String) : Option JasminBinOp :=
  if f = "BitXor" then some .xor
  else if f = "BitAnd" then some .and
  else if f = "BitOr" then some .or
  else if f = "wrapping_add" ∨ f = "add" ∨ f = "Add" then some .add
  else if f = "wrapping_mul" ∨ f = "mul" ∨ f = "Mul" then some .mul
  else if f = "wrapping_sub" ∨ f = "sub" ∨ f = "Sub" then some .sub
  else none

/-- Shift/rotate kinds (the second operand is a compile-time literal count). -/
inductive ShiftKind where
  | ror
  | shr
  | sar
  | shl
  deriving DecidableEq, Repr

/-- Recognise a shift/rotate operator head. Also accepts the **capitalized**
    operator-trait heads (`Shr`/`Shl`) real hax extractions emit, denoting
    identically to their lowercase `shr`/`shl` twins. -/
def recogShift (f : String) : Option ShiftKind :=
  if f = "rotate_right" ∨ f = "rotate_right_w" then some .ror
  else if f = "arith_shift_right" ∨ f = "sar" ∨ f = "Sar" then some .sar
  else if f = "shift_right" ∨ f = "shr" ∨ f = "Shr" then some .shr
  else if f = "shift_left" ∨ f = "shl" ∨ f = "Shl" then some .shl
  else none

/-- Recognise a **unary bitwise-NOT** operator head (`Not`/`BitNot`, one operand).
    Bitwise complement at the working width `w` is `~~~x = x ^^^ allOnes w`
    (`BitVec.xor_allOnes`), so a recognised `Not[x]` denotes to `~~~xv`. This is a
    `Bool` recogniser (NOT is nullary in its tag — there is no per-head data, unlike
    `recogBin`/`recogShift`); both `denoteScalar` and `denoteAtomExpr` consult it so
    source and target stay aligned on the complement. -/
def recogNot (f : String) : Bool :=
  f = "Not" ∨ f = "BitNot"

/-- Read a `Nat` out of a recognised literal (`uintLit`/`int`); `none` otherwise. -/
def litNat? : ImpLit → Option Nat
  | .uintLit _ n => some n
  | .int n => some n.toNat
  | _ => none

/-- Recognise an **indexed read of the input array**: `index[(.var P), (.lit k)]`
    where `P` is one of the function's array parameters and `k` is a literal `Nat`.

    Array-param convention: a scalar body whose Rust source is a function over an
    array parameter `P` reads its scalar inputs via `P[k]` (the `core::ops::Index`
    projection). We model that element read as input word `k` — i.e. the same
    `inpGet I k` a bare scalar parameter would denote to. The bare `var P` itself is
    *not* an atom (it is the whole array), so the only way to touch the input under
    this convention is through `index`. This makes real (non let-flattened) hax
    bodies like `arith(index[w,0], index[w,1])` translatable: each `index` arg is an
    atom (`Atom.inp k`), so the surrounding op recogniser sees atom arguments. -/
def indexAtom? (params : List String) : ImpExpr → Option Nat
  | .app "index" [(.var P), (.lit l)] => if P ∈ params then litNat? l else none
  | _ => none

/-- Apply a recognised shift/rotate kind to a value and a compile-time count; the
    logical shifts shift by the masked count `VIR.shiftMask w n`. -/
def ShiftKind.apply {w : Nat} : ShiftKind → BitVec w → Nat → BitVec w
  | .ror, av, n => av.rotateRight n
  | .shr, av, n => av >>> VIR.shiftMask w n
  | .sar, av, n => BitVec.sshiftRight av n
  | .shl, av, n => av <<< VIR.shiftMask w n

/-! ## §2  Source semantics of the scalar subset

`denoteScalar` evaluates an `ImpExpr` directly into `Option (BitVec w)`, with
**no reference to the translator**. A parameter `var` reads `inpGet I i` (exactly
matching `Atom.inp i`'s front denotation), so the param-to-input alignment is
baked into the source semantics — the var case of preservation then closes
definitionally. App arguments are evaluated through `denoteAtomExpr` (atoms
only), mirroring the ANF restriction the translator enforces. -/

/-- Source denotation of an *atom* expression (`.var`/`.lit`). A `var x` naming
    parameter `i` reads input word `i`; otherwise the local env `ρ`. -/
def denoteAtomExpr {w nIn : Nat} (params : List String) (I : Fin nIn → BitVec w) :
    ImpExpr → (String → Option (BitVec w)) → Option (BitVec w)
  | .var x, ρ =>
      match params.idxOf? x with
      | some i => some (inpGet I i)
      | none => ρ x
  | .lit l, _ => (litNat? l).map (fun n => BitVec.ofNat w n)
  | .app f args, ρ =>
      -- Unary bitwise-NOT of a nested atom-expr: `Not[a]` denotes to `~~~av`.
      if recogNot f then
        match args with
        | [a] => (denoteAtomExpr params I a ρ).map (· ^^^ BitVec.allOnes w)
        | _ => none
      else
        -- Indexed read of an array parameter: `P[k]` denotes to input word `k`.
        (indexAtom? params (.app f args)).map (fun k => inpGet I k)
  | _, _ => none

/-- Source denotation of the scalar ARX subset. Recursive on `letBind`; `app`
    arguments are atom-expressions evaluated via `denoteAtomExpr`. -/
def ImpExpr.denoteScalar {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) : ImpExpr → (String → Option (BitVec w)) →
    Option (BitVec w)
  | .letBind x v body, ρ =>
      (ImpExpr.denoteScalar params I v ρ).bind fun vv =>
        ImpExpr.denoteScalar params I body (fun y => if y = x then some vv else ρ y)
  | .app f args, ρ =>
      match recogBin f, args with
      | some op, [a, b] =>
          (denoteAtomExpr params I a ρ).bind fun av =>
            (denoteAtomExpr params I b ρ).map fun bv => op.apply av bv
      | _, _ =>
        match recogShift f, args with
        | some k, [a, .lit l] =>
            (denoteAtomExpr params I a ρ).bind fun av =>
              (litNat? l).map fun n => k.apply av n
        | _, _ =>
          -- Unary bitwise-NOT (`Not`/`BitNot`): complement at width `w`.
          -- `~~~av = av ^^^ allOnes w` (`BitVec.xor_allOnes`).
          if recogNot f then
            match args with
            | [a] => (denoteAtomExpr params I a ρ).map (· ^^^ BitVec.allOnes w)
            | _ => none
          else none
  | e, ρ => denoteAtomExpr params I e ρ

/-! ## §3  The translator `ImpExpr → Thir` (correct-by-construction)

The translator mirrors `denoteScalar` arm-for-arm onto the front's `Atom`/`Rhs`/
`Thir`. App arguments must already be atoms (`.var`/`.lit`); a nested-app argument
yields `none` (the v1 ANF restriction). -/

/-- Translate an atom-expression (`.var`/`.lit`) to a front `Atom`. A `var` that
    names a parameter becomes `Atom.inp i`; otherwise a local `Atom.lvar`. -/
def atomOf (params : List String) : ImpExpr → Option Atom
  | .var x =>
      match params.idxOf? x with
      | some i => some (.inp i)
      | none => some (.lvar x)
  | .lit l => (litNat? l).map (fun n => Atom.lit n)
  | .app f args =>
      -- Indexed read of an array parameter `P[k]` becomes the input atom `inp k`.
      (indexAtom? params (.app f args)).map Atom.inp
  | _ => none

/-- Translate a value-producing expression to a front `Rhs`. A bare atom-expr is
    `Rhs.atom`; a recognised application of atoms is the matching binary/shift
    `Rhs`. Anything else (nested-app argument, unknown head, wrong arity) → `none`. -/
def rhsOf (params : List String) : ImpExpr → Option Rhs
  | .app f args =>
      match recogBin f, args with
      | some op, [a, b] =>
          (atomOf params a).bind fun av =>
            (atomOf params b).map fun bv => Rhs.bin op av bv
      | _, _ =>
        match recogShift f, args with
        | some k, [a, .lit l] =>
            (atomOf params a).bind fun av =>
              (litNat? l).map fun n =>
                match k with
                | .ror => Rhs.ror n av
                | .shr => Rhs.shrImm n av
                | .sar => Rhs.sarImm n av
                | .shl => Rhs.shlImm n av
        | _, _ => none
  | .var x => (atomOf params (.var x)).map Rhs.atom
  | .lit l => (atomOf params (.lit l)).map Rhs.atom
  | _ => none

/-- Translate a (let-normalized) `ImpExpr` to a front `Thir`. A `letBind` binds
    its RHS and recurses; a final value-expr returns. -/
def impExprToThir (params : List String) : ImpExpr → Option Thir
  | .letBind x v body =>
      (rhsOf params v).bind fun r =>
        (impExprToThir params body).map fun bt => Thir.let_ x r bt
  | .var x => (atomOf params (.var x)).map Thir.ret
  | .lit l => (atomOf params (.lit l)).map Thir.ret
  | .app f args =>
      (rhsOf params (.app f args)).map fun r =>
        Thir.let_ "__ret" r (Thir.ret (.lvar "__ret"))
  | _ => none

/-! ## §4  Preservation

The inductive helpers show atom / rhs translation preserves the source
denotation; the main theorem threads them through `letBind`. -/

/-- An `indexAtom?` success forces the app head to be `"index"` (so the new
    `recogNot` guard in `denoteAtomExpr`'s `.app` arm is `false`), hence the atom
    read denotes to the input word `inpGet I n`. Bridges the new NOT-guarded
    `denoteAtomExpr` back to the unchanged `indexAtom?` map. -/
theorem denoteAtomExpr_app_index {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (ρ : String → Option (BitVec w))
    {f : String} {args : List ImpExpr} {n : Nat}
    (hn1 : indexAtom? params (ImpExpr.app f args) = some n) :
    denoteAtomExpr params I (ImpExpr.app f args) ρ = some (inpGet I n) := by
  unfold indexAtom? at hn1
  split at hn1
  · rename_i _ _ _ heq
    rw [heq]
    simp only [denoteAtomExpr, recogNot, String.reduceEq, or_self, decide_false,
      Bool.false_eq_true, reduceIte, indexAtom?, hn1, Option.map_some]
  · exact absurd hn1 (by simp)

/-- Atom translation preserves denotation: an atom-expression that translates to a
    front `Atom` denotes (under `denoteAtomExpr`) to that atom's front denotation. -/
theorem atomOf_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (ρ : String → Option (BitVec w))
    (e : ImpExpr) {a : Atom} (h : atomOf params e = some a) :
    denoteAtomExpr params I e ρ = a.denote I ρ := by
  rcases e <;> simp only [atomOf, denoteAtomExpr, Option.map_eq_some_iff] at h ⊢ <;>
    first
      | (-- `.app` (indexed read): route through `denoteAtomExpr_app_index`, which
         -- discharges the new `recogNot` guard.
         obtain ⟨n, hn1, hn2⟩ := h; cases hn2
         rw [denoteAtomExpr_app_index params I ρ hn1]; simp [Atom.denote])
      | (-- `.lit`: literal atom maps to `Atom.lit`.
         obtain ⟨n, hn1, hn2⟩ := h; cases hn2; simp [Atom.denote, hn1])
      | (split at h <;> cases h <;> simp [Atom.denote])
      | exact absurd h (by simp)

/-- Rhs translation preserves denotation: an expression that translates to a front
    `Rhs` denotes (under `denoteScalar`) to that rhs's front denotation. -/
theorem rhsOf_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (ρ : String → Option (BitVec w))
    (e : ImpExpr) {r : Rhs} (h : rhsOf params e = some r) :
    ImpExpr.denoteScalar params I e ρ = r.denote I ρ := by
  -- The atom (`var`/`lit`) and impossible (`none`) cases close uniformly; only
  -- the `app` case needs the operator-dispatch reasoning, handled below.
  rcases e with _ | x | _ | ⟨f, args⟩ <;>
    simp only [rhsOf, Option.map_eq_some_iff] at h ⊢ <;>
    try first
      | (obtain ⟨a, ha1, ha2⟩ := h; cases ha2
         rw [show ImpExpr.denoteScalar params I _ ρ = denoteAtomExpr params I _ ρ
              from rfl, atomOf_denote params I ρ _ ha1]; rfl)
      | exact absurd h (by simp)
  -- The remaining goal is the `app f args` case.
  simp only [ImpExpr.denoteScalar]
  split at h
  · -- recognised binary ALU head, exactly two atom arguments
    rename_i _ _ _ a b _
    rcases ha : atomOf params a with _ | av
    · rw [ha] at h; simp at h
    rcases hbb : atomOf params b with _ | bv
    · rw [ha, hbb] at h; simp at h
    rw [ha, hbb] at h
    simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
    subst h
    rw [atomOf_denote params I ρ a ha, atomOf_denote params I ρ b hbb]
    rfl
  · -- not a binary head: try the shift/rotate dispatch
    split at h
    · -- recognised shift/rotate head, (atom, literal) arguments
      rename_i _ _ _ _ k a l _ _
      rcases ha : atomOf params a with _ | av
      · rw [ha] at h; simp at h
      rcases hl : litNat? l with _ | n
      · rw [ha, hl] at h; simp at h
      rw [ha, hl] at h
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
      subst h
      rw [atomOf_denote params I ρ a ha]
      cases k <;> simp [ShiftKind.apply, Rhs.denote, Option.map_eq_bind]
    · -- neither head recognised: translation was `none`
      exact absurd h (by simp)

/-- **Preservation theorem.** Whenever the translator succeeds, the source
    denotation `denoteScalar` equals the front denotation `Thir.denote`. The
    value-preservation result connecting the hax `ImpExpr` AST to the
    verified `Thir` front. Proved by structural induction on `e`. -/
theorem impExprToThir_denoteScalar {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) :
    (e : ImpExpr) → (ρ : String → Option (BitVec w)) → {t : Thir} →
    impExprToThir params e = some t →
    ImpExpr.denoteScalar params I e ρ = t.denote I ρ
  | .letBind x v body, ρ, t, h => by
      simp only [impExprToThir] at h
      cases hr : rhsOf params v with
      | none => rw [hr] at h; simp at h
      | some r =>
        cases hbt : impExprToThir params body with
        | none => rw [hr, hbt] at h; simp at h
        | some bt =>
          rw [hr, hbt] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          show (ImpExpr.denoteScalar params I v ρ).bind (fun vv =>
              ImpExpr.denoteScalar params I body
                (fun y => if y = x then some vv else ρ y)) = _
          rw [rhsOf_denote params I ρ v hr]
          simp only [Thir.denote]
          cases hrv : r.denote I ρ with
          | none => simp
          | some rv =>
            simp only [Option.bind_some]
            have hbody := impExprToThir_denoteScalar params I body
                (fun y => if y = x then some rv else ρ y) hbt
            rw [hbody]
            rfl
  | .var x, ρ, t, h => by
      simp only [impExprToThir] at h
      cases ha : atomOf params (.var x) with
      | none => rw [ha] at h; simp at h
      | some av =>
        rw [ha] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show denoteAtomExpr params I (.var x) ρ = (Thir.ret av).denote I ρ
        rw [atomOf_denote params I ρ (.var x) ha]
        rfl
  | .lit l, ρ, t, h => by
      simp only [impExprToThir] at h
      cases ha : atomOf params (.lit l) with
      | none => rw [ha] at h; simp at h
      | some av =>
        rw [ha] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show denoteAtomExpr params I (.lit l) ρ = (Thir.ret av).denote I ρ
        rw [atomOf_denote params I ρ (.lit l) ha]
        rfl
  | .app f args, ρ, t, h => by
      simp only [impExprToThir] at h
      cases hr : rhsOf params (.app f args) with
      | none => rw [hr] at h; simp at h
      | some r =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        show ImpExpr.denoteScalar params I (.app f args) ρ
          = (Thir.let_ "__ret" r (Thir.ret (.lvar "__ret"))).denote I ρ
        rw [rhsOf_denote params I ρ (.app f args) hr]
        simp only [Thir.denote]
        cases hrv : r.denote I ρ with
        | none => simp
        | some rv =>
          simp only [Option.bind_some, Atom.denote, LEnv.set, if_true]
  | .tuple _, _, _, h => by simp [impExprToThir] at h
  | .proj _ _, _, _, h => by simp [impExprToThir] at h
  | .ifThenElse _ _ _, _, _, h => by simp [impExprToThir] at h
  | .match_ _ _, _, _, h => by simp [impExprToThir] at h
  | .unitVal, _, _, h => by simp [impExprToThir] at h
  | .seq _ _, _, _, h => by simp [impExprToThir] at h
  | .borrow _, _, _, h => by simp [impExprToThir] at h
  | .deref _, _, _, h => by simp [impExprToThir] at h
  | .assign _ _, _, _, h => by simp [impExprToThir] at h
  | .forLoop _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .forLoopRev _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .whileLoop _ _, _, _, h => by simp [impExprToThir] at h
  | .break_ _, _, _, h => by simp [impExprToThir] at h
  | .continue_, _, _, h => by simp [impExprToThir] at h
  | .earlyReturn _, _, _, h => by simp [impExprToThir] at h
  | .questionMark _, _, _, h => by simp [impExprToThir] at h
  | .forFold _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .forFoldRev _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .whileFold _ _, _, _, h => by simp [impExprToThir] at h
  | .forFoldReturn _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .forFoldRevReturn _ _ _ _, _, _, h => by simp [impExprToThir] at h
  | .whileFoldReturn _ _, _, _, h => by simp [impExprToThir] at h
  | .cfBreak _, _, _, h => by simp [impExprToThir] at h
  | .cfContinue _, _, _, h => by simp [impExprToThir] at h
  | .cfBreakContinue _, _, _, h => by simp [impExprToThir] at h
  | .typeAscription _ _, _, _, h => by simp [impExprToThir] at h

/-! ## §5  The σ₀ end-to-end demo (`ImpExpr → Thir → Com`)

SHA-256 message-schedule σ₀(x) = (x ror 7) ⊕ (x ror 18) ⊕ (x >> 3), at `w = 32`,
one input parameter `"x"` (`nIn = 1`, `I 0 = x`). The source `ImpExpr` is in
fully let-normalized form (each op its own `letBind` with atom arguments), as the
hax pipeline produces after ANF. -/

/-- The σ₀ source as a hax `ImpExpr`, fully let-normalized, parameter `"x"`. -/
def sigma0Src : ImpExpr :=
  .letBind "a" (.app "rotate_right" [.var "x", .lit (.uintLit .w32 7)])
    (.letBind "b" (.app "rotate_right" [.var "x", .lit (.int 18)])
      (.letBind "c" (.app "shift_right" [.var "x", .lit (.int 3)])
        (.letBind "ab" (.app "BitXor" [.var "a", .var "b"])
          (.letBind "r" (.app "BitXor" [.var "ab", .var "c"])
            (.var "r")))))

/-- The σ₀ source `ImpExpr` denotes (under `denoteScalar`) to the FIPS 180-4
    formula `ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`, for any single-word input. -/
theorem sigma0Src_denoteScalar (I : Fin 1 → BitVec 32) :
    ImpExpr.denoteScalar ["x"] I sigma0Src (fun _ => none)
      = some ((I 0).rotateRight 7 ^^^ (I 0).rotateRight 18 ^^^ (I 0) >>> (3 : Nat)) := by
  simp only [sigma0Src, ImpExpr.denoteScalar, denoteAtomExpr, recogBin, recogShift,
    litNat?, ShiftKind.apply, List.idxOf?, List.findIdx?, JasminBinOp.apply,
    reduceIte, String.reduceEq]
  rfl

/-- The translator succeeds on σ₀, producing a concrete `Thir`. -/
theorem sigma0Src_lowers : (impExprToThir ["x"] sigma0Src).isSome := by
  native_decide

/-- **σ₀ end-to-end (`ImpExpr → Thir → Com jasminDialect`).** There is a `Thir`
    `t` and a `Com jasminDialect` `c` such that the hax `ImpExpr` σ₀ translates to
    `t`, `t` lowers to `c`, and `c`'s `BitVec 32` denotation is exactly the FIPS
    σ₀ formula `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)` for every input. The chain:
    `impExprToThir_denoteScalar` (C2, this file) composed with the front's
    `thirToJasmin_denote` (C1). -/
theorem sigma0Src_to_jasmin :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 1 []) (rW 32)),
      impExprToThir ["x"] sigma0Src = some t ∧
      thirToJasmin [] (initFState 32 1) t = some c ∧
      ∀ (x : BitVec 32),
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  -- The concrete translator output and its concrete lowering (both computed).
  set t := (impExprToThir ["x"] sigma0Src).get sigma0Src_lowers with ht_def
  have ht : impExprToThir ["x"] sigma0Src = some t := (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 1) t).isSome := by
    rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 1) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 1) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro x
  -- C2 (this file) : source `denoteScalar` = front `Thir.denote`.
  have hsrc := impExprToThir_denoteScalar (w := 32) (nIn := 1) ["x"]
      (fun _ => x) sigma0Src (fun _ => none) ht
  -- C1 (the front) : `Thir.denote` = `Com.denote`.
  have hfront := thirToJasmin_denote (w := 32) (nIn := 1) []
      (fun _ => x) t (LEnv.empty 32) (initFState 32 1)
      (inputValuation 32 1 (fun _ => x)) c (initAgree (fun _ => x)) hc
  -- The source value is the FIPS σ₀ formula (`(fun _ => x) 0 = x` already
  -- reduced inside `sigma0Src_denoteScalar`).
  have hspec := sigma0Src_denoteScalar (fun _ => x)
  -- `LEnv.empty 32 = fun _ => none` definitionally, so all `ρ`s line up; chain
  -- the three equalities and peel the outer `some`.
  have hchain : some (x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat))
      = some (c.denote (inputValuation 32 1 (fun _ => x))) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-! ## §6  Indexed-read demo (`index[w, k]` as nested arith arguments)

The σ₀ demo above is fully *let-flattened* with bare scalar parameters. Real hax
extractions instead emit scalar bodies over an **array parameter** `w`, reading
elements via `index[w, k]` *nested inside* arithmetic applications — the exact
shape the §3 v1 ANF restriction rejected. This demo exercises the extension:
a body containing `index[w, k]` as a nested argument both translates and is
value-preserving.

Convention: one array parameter `["w"]`; element `w[k]` denotes to input word `k`
(`inpGet I k`). The body
`let a = (w[0] ror 7); let b = (w[0] ^ w[1]); let r = (a ^ b); r`
has a nested `index` inside the `rotate_right` app (the `a` binder) *and* two
nested `index`es inside the `BitXor` app (the `b` binder). -/

/-- A realistic scalar body over an **array parameter** `"w"`: it reads its inputs
    via `index[w, k]` nested inside arithmetic applications (not let-flattened to
    bare scalar params). Computes `(w[0] ror 7) ⊕ (w[0] ⊕ w[1])`. -/
def sigma0ArrSrc : ImpExpr :=
  .letBind "a"
      (.app "rotate_right" [.app "index" [.var "w", .lit (.int 0)], .lit (.uintLit .w32 7)])
    (.letBind "b"
        (.app "BitXor"
          [ .app "index" [.var "w", .lit (.int 0)]
          , .app "index" [.var "w", .lit (.int 1)] ])
      (.letBind "r" (.app "BitXor" [.var "a", .var "b"])
        (.var "r")))

/-- The indexed-read body denotes (under `denoteScalar`, with array parameter
    `"w"`) to `ROTR⁷(w[0]) ⊕ (w[0] ⊕ w[1])`, where `w[k] = inpGet I k`. The
    nested `index` arguments are resolved through `denoteAtomExpr`'s new array-read
    case. -/
theorem sigma0ArrSrc_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ImpExpr.denoteScalar ["w"] I sigma0ArrSrc (fun _ => none)
      = some ((inpGet I 0).rotateRight 7 ^^^ (inpGet I 0 ^^^ inpGet I 1)) := by
  simp only [sigma0ArrSrc, ImpExpr.denoteScalar, denoteAtomExpr, indexAtom?,
    recogBin, recogShift, litNat?, ShiftKind.apply, JasminBinOp.apply,
    List.mem_cons, List.not_mem_nil, reduceIte, String.reduceEq, Int.toNat]
  rfl

/-- The translator succeeds on the indexed-read body, producing a concrete `Thir`
    (the nested `index` arguments become `Atom.inp` atoms). -/
theorem sigma0ArrSrc_lowers : (impExprToThir ["w"] sigma0ArrSrc).isSome := by
  native_decide

/-- **Indexed-read body translates and is value-preserving.** There is a `Thir`
    `t` such that the hax `ImpExpr` body with nested `index[w, k]` reads translates
    to `t`, and `t`'s front denotation is exactly `ROTR⁷(w[0]) ⊕ (w[0] ⊕ w[1])`
    for every input vector. Demonstrates coverage past the §3 let-normalized
    restriction: the body is *not* flattened — `index` reads appear nested inside
    arithmetic applications. Threads `impExprToThir_denoteScalar` (C2, this file).-/
theorem sigma0Arr_compiles {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ∃ (t : Thir),
      impExprToThir ["w"] sigma0ArrSrc = some t ∧
      ImpExpr.denoteScalar ["w"] I sigma0ArrSrc (fun _ => none) = t.denote I (fun _ => none) ∧
      ImpExpr.denoteScalar ["w"] I sigma0ArrSrc (fun _ => none)
        = some ((inpGet I 0).rotateRight 7 ^^^ (inpGet I 0 ^^^ inpGet I 1)) := by
  set t := (impExprToThir ["w"] sigma0ArrSrc).get sigma0ArrSrc_lowers with ht_def
  have ht : impExprToThir ["w"] sigma0ArrSrc = some t := (Option.some_get _).symm
  refine ⟨t, ht, ?_, sigma0ArrSrc_denoteScalar I⟩
  -- C2 (this file): source `denoteScalar` = front `Thir.denote`.
  exact impExprToThir_denoteScalar (w := 32) (nIn := nIn) ["w"] I
      sigma0ArrSrc (fun _ => none) ht

/-! ## §7  Bounded `forFold` loops → source-level unrolling (whole-function piece)

This section connects `ImpExpr.forFold` with **literal bounds** to the front's
source-level unrolling discipline (the `dotN`/`dotTail` pilot of
`ThirToComFront` §6), giving the first *whole-function* (not just scalar-leaf)
coverage past the straight-line scalar leaves: a bounded **reduction** loop is
unrolled into a flat `ImpExpr` let-chain (which the existing §3 `impExprToThir`
already consumes) and proved value-preserving against a `List.foldl`
source semantics.

### The supported `forFold` shape (precise restriction)

We support the **Horner-style multi-op accumulator step** — the canonical
two-op reduction loop (a `mul` then an `add` per iteration):

```text
acc := acc * x + c[i]      for i = 0 .. N-1        (Horner polynomial eval)
```

i.e. `forFold "i" (lit 0) (lit N) body` carrying a single scalar accumulator
`acc`, where `x` is a fixed input word (`Atom.inp xIdx`) and `c[i]` is the array
read `index[arr, i]` resolving to input word `cBase + i`. Each iteration is two
ops with one fresh temporary (`hMul i = acc * x`, then `acc = hMul i + c[i]`),
exactly `dotTail`'s shape. The literal index substitution turns `index[arr, i]`
into the input atom `Atom.inp (cBase + i)`, so no loop-index register is needed.

This is a **fixed two-op body shape** (deliberately, so the unrolling induction
closes cleanly — see the task's "restrict to a FIXED small multi-op shape"
fallback). It already beats the single-`Rhs` straight-line limitation: the per
iteration step is two chained ALU ops with a carried accumulator. We do
**not** yet support: non-literal bounds, multiple accumulators, an *arbitrary*
let-chain body, or control-flow/loops inside the body. Scope: a bounded
Horner/MAC reduction, not arbitrary whole-function loops.

`hornerStepFn` is the per-iteration `BitVec w` step; `hornerFold` is the
`List.range`-`foldl` source meaning; `hornerUnroll` is the flat unrolled
`ImpExpr` the front compiles; `hornerUnroll_denoteScalar` is the preservation
theorem tying them. -/

/-- Per-step accumulator name (the carried reduction value). -/
def accH : String := "acc"

/-- Per-iteration fresh product temporary `h0, h1, …` (mirrors `dotTail`'s
    `prodN i`), keeping each iteration's temporary from clobbering the next. -/
def mulH (i : Nat) : String := "h" ++ toString i

/-- The per-iteration `BitVec w` reduction step of Horner evaluation:
    `acc ↦ acc * x + c[i]`, where `x = inpGet I xIdx` and `c[i] = inpGet I
    (cBase + i)`. This is the independent (translator-free) arithmetic meaning. -/
def hornerStepFn {w nIn : Nat} (I : Fin nIn → BitVec w) (xIdx cBase : Nat)
    (acc : BitVec w) (i : Nat) : BitVec w :=
  acc * inpGet I xIdx + inpGet I (cBase + i)

/-- The `List.foldl` source meaning of the bounded Horner loop: starting
    from `init` (the program seeds `init = 0`), iterate the multiply-add step
    `acc ↦ acc * x + c[i]` over `i = 0 .. N-1`. With `init = 0` this is the
    standard Horner evaluation `c₀·xᴺ⁻¹ + c₁·xᴺ⁻² + … + c_{N-1}`
    (`(((0·x + c₀)·x + c₁)·x + …)·x + c_{N-1}`). Defined with no reference to the
    translator: this is what preservation certifies. -/
def hornerFold {w nIn : Nat} (I : Fin nIn → BitVec w) (xIdx cBase : Nat)
    (N : Nat) (init : BitVec w) : BitVec w :=
  (List.range N).foldl (fun acc j => hornerStepFn I xIdx cBase acc j) init

/-- The fully-unrolled flat `ImpExpr` for the bounded Horner loop, body-first:
    for iterations `j = 0 .. count-1` at source index `i`, emit
    `let h_i = acc * x; let acc = h_i + c[i]; …`, then return `acc`. `x` reads
    `index[arr, lit xLit]` and `c[i]` reads `index[arr, lit i]` (both resolve via
    `indexAtom?` to input atoms). The accumulator `acc` is reused; each `h_i` is
    fresh. Mirrors `dotTail`. -/
def hornerUnroll (arr : String) (xLit : Nat) : (count i : Nat) → ImpExpr
  | 0, _ => .var accH
  | c + 1, i =>
      .letBind (mulH i)
        (.app "wrapping_mul" [.var accH, .app "index" [.var arr, .lit (.int xLit)]])
        (.letBind accH
          (.app "wrapping_add"
            [.var (mulH i), .app "index" [.var arr, .lit (.int i)]])
          (hornerUnroll arr xLit c (i + 1)))

/-- Build the whole compiled Horner reduction: seed `acc = 0` (a literal,
    materialised into a register by the front's `regConst`), then run the
    unrolled multiply-add tail for `i = 0 .. N-1`. Single array parameter `arr`;
    the multiplier `x` is input word `xLit`. This is the flat `ImpExpr` the
    front's `impExprToThir` (§3) consumes directly (the `lit 0` seed is an
    `Rhs.atom`, every step a recognised `wrapping_mul`/`wrapping_add`). -/
def hornerProgram (arr : String) (xLit N : Nat) : ImpExpr :=
  .letBind accH (.lit (.int 0))
    (hornerUnroll arr xLit N 0)

/-! ### §7.1  The unrolling-preservation theorem

`hornerUnroll_denoteScalar` proves the unrolled flat `ImpExpr` denotes (under the
independent §2 `denoteScalar`) exactly to the `List.foldl` source
meaning, by induction on the iteration count. The carried accumulator survives
because `acc` is rebound each step and the fresh `h_i` temporaries are dead
across iterations. -/

/-- `denoteScalar` of the bare accumulator `var accH` (array parameter `arr` with
    `arr ≠ accH`, so `accH` is a *local* not a param) reads the env at `accH`. -/
theorem idxOf_arr_none {arr nm : String} (h : arr ≠ nm) :
    List.idxOf? nm [arr] = none := by
  simp only [List.idxOf?, List.findIdx?, List.findIdx?.go]
  rw [if_neg]
  simp only [beq_iff_eq]
  exact h

theorem denoteScalar_varAcc {w nIn : Nat} (I : Fin nIn → BitVec w) (arr : String)
    (harr : arr ≠ accH) (ρ : String → Option (BitVec w)) :
    ImpExpr.denoteScalar [arr] I (.var accH) ρ = ρ accH := by
  simp only [ImpExpr.denoteScalar, denoteAtomExpr, idxOf_arr_none harr]

/-- An `index[arr, lit k]` read denotes to input word `k` under any env (it
    never touches the local env — `indexAtom?` resolves it to `Atom.inp k`). -/
theorem denoteAtomExpr_indexLit {w nIn : Nat} (I : Fin nIn → BitVec w)
    (arr : String) (k : Nat) (ρ : String → Option (BitVec w)) :
    denoteAtomExpr [arr] I (.app "index" [.var arr, .lit (.int k)]) ρ
      = some (inpGet I k) := by
  simp only [denoteAtomExpr, recogNot, String.reduceEq, or_self, decide_false,
    Bool.false_eq_true, reduceIte, indexAtom?, List.mem_cons, List.not_mem_nil,
    or_false, litNat?, Int.toNat, Option.map_some]

/-- The unrolled Horner tail denotes (under `denoteScalar`, array parameter `arr`
    with `arr ≠ accH`) exactly to the `foldl` over `hornerStepFn` starting from
    index `i`, for **any** env `ρ` whose accumulator slot `ρ accH = some a0`
    (the body reads only `accH` freely; the `h_i` temporaries are bound locally
    and the `index` reads are inputs). The `xLit` literal resolves to input word
    `xLit` (the multiplier `x`), `index[arr, lit i]` to input word `i` (`c[i]`).
    Generalizing over `ρ` is what makes the inductive step's env line up without
    a function-extensionality clash on the dead temporary names. Proved by
    induction on `count`. -/
theorem hornerUnroll_denoteScalar {w nIn : Nat} (I : Fin nIn → BitVec w)
    (arr : String) (xLit : Nat) (harr : arr ≠ accH) (harrH : ∀ j, arr ≠ mulH j) :
    (count i : Nat) → (a0 : BitVec w) → (ρ : String → Option (BitVec w)) →
    ρ accH = some a0 →
    ImpExpr.denoteScalar [arr] I (hornerUnroll arr xLit count i) ρ
      = some ((List.range count).foldl
          (fun acc j => hornerStepFn I xLit 0 acc (i + j)) a0)
  | 0, i, a0, ρ, hρ => by
      simp only [hornerUnroll, List.range_zero, List.foldl_nil]
      rw [denoteScalar_varAcc I arr harr, hρ]
  | c + 1, i, a0, ρ, hρ => by
      -- read facts for the two operands of each op:
      have hacc : denoteAtomExpr [arr] I (.var accH) ρ = some a0 := by
        simp only [denoteAtomExpr, idxOf_arr_none harr, hρ]
      have hmul : denoteAtomExpr [arr] I (.var (mulH i))
          (fun y => if y = mulH i then some (a0 * inpGet I xLit) else ρ y)
          = some (a0 * inpGet I xLit) := by
        simp only [denoteAtomExpr, idxOf_arr_none (harrH i), if_true]
      -- reduce the two-let chain to the tail under its env.
      simp only [hornerUnroll, ImpExpr.denoteScalar, recogBin, String.reduceEq,
        or_self, reduceIte, true_or, JasminBinOp.apply, hacc,
        denoteAtomExpr_indexLit, Option.bind_some, Option.map_some, hmul]
      -- IH on the tail: env at this point has `accH ↦ hornerStepFn … a0 i`.
      rw [hornerUnroll_denoteScalar I arr xLit harr harrH c (i + 1)
        (hornerStepFn I xLit 0 a0 i)
        (fun y => if y = accH then some (a0 * inpGet I xLit + inpGet I i)
                  else if y = mulH i then some (a0 * inpGet I xLit) else ρ y)
        (by simp only [if_true, hornerStepFn, Nat.zero_add])]
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      rw [show (fun acc (j : Nat) => hornerStepFn I xLit 0 acc (i + 1 + j))
            = (fun acc (j : Nat) => hornerStepFn I xLit 0 acc (i + (j + 1)))
          from by funext acc j; congr 1; omega]
      simp only [hornerStepFn, Nat.add_zero]

/-- **Bounded Horner reduction is value-preserving.** The whole-program
    `hornerProgram` denotes (under `denoteScalar`) exactly to the
    `hornerFold` source meaning seeded at `0`. Combines the seed `let acc = 0`
    with the unrolled-tail induction `hornerUnroll_denoteScalar`. -/
theorem hornerProgram_denoteScalar {w nIn : Nat} (I : Fin nIn → BitVec w)
    (arr : String) (xLit N : Nat) (harr : arr ≠ accH) (harrH : ∀ j, arr ≠ mulH j) :
    ImpExpr.denoteScalar [arr] I (hornerProgram arr xLit N) (fun _ => none)
      = some (hornerFold I xLit 0 N 0) := by
  -- Seed: `acc = 0` (literal); then run the `N`-iteration tail from i=0.
  have hseed :
      ImpExpr.denoteScalar [arr] I (hornerProgram arr xLit N) (fun _ => none)
        = ImpExpr.denoteScalar [arr] I (hornerUnroll arr xLit N 0)
            (fun y => if y = accH then some 0 else none) := by
    simp only [hornerProgram, ImpExpr.denoteScalar, denoteAtomExpr, litNat?,
      Int.toNat, Option.map_some, BitVec.ofNat_eq_ofNat, Option.bind_some]
  -- The unrolled tail folds `i = 0 + j = j`, exactly `hornerFold`'s meaning.
  rw [hseed, hornerUnroll_denoteScalar I arr xLit harr harrH N 0 0
    (fun y => if y = accH then some 0 else none) (by simp only [if_true])]
  simp only [hornerFold, Nat.zero_add]

/-! ## §8  Bounded array-write recurrences → per-element SSA unrolling

This section is the **array-write** companion to §7: the second whole-function
coverage piece. The insight is that with **literal indices** (which bounded-loop
unrolling produces), an array *accumulator* — the canonical example is SHA-256's
message schedule `W[t]` — SSA's into per-element locals with **no memory model**:
`index[arr, lit k]` reads either an input word (if `k` was not yet written) or a
written local, and a write `W[i] := …` binds a fresh local and updates the
element→source map. So an array recurrence compiles to the same flat scalar
let-chain §3 already consumes.

### The supported recurrence shape (precise restriction)

We support a **bounded read-read-write array recurrence** of the canonical
message-schedule shape, fixed to the two-read one-add body (Fibonacci-style):

```text
W[i] = W[i-1] + W[i-2]      for i = base .. N-1
```

with `W[0..base-1]` **seeded from the input array** (`index[arr, lit k]` for
`k < base` resolves to input word `k`), each step writing a fresh local
`wName i`, and the program returning the **single** element `W[N-1]`. This is
the SHA-256 message-schedule SHAPE: a per-element array accumulator whose step
reads earlier elements at literal offsets. Reads of `W[j]` resolve to the local
`wName j` when `j ≥ base` (already written) and to the input atom
`index[arr, lit j]` when `j < base` (a seed).

This is a **fixed two-read one-op body** (deliberately, so the array-SSA
induction closes cleanly — the task's "fix the step to a concrete small shape"
floor). The general machinery (`arrFold` array state, `wReadExpr` read
resolution, `arrRecUnroll` the unrolled let-chain, `arrRecUnroll_denoteScalar`
the array-SSA preservation theorem with its env↔array-state invariant) is what
generalises; only the per-step body is pinned. We do **not** here emit the full
SHA-256 σ-schedule (`W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]`): that
needs the wider body and the rotate/shift reads; the read-read-write recurrence
is the floor demonstrated. Scope: a bounded
`W[i] = W[i-1] + W[i-2]` array recurrence, not an arbitrary array body.

`arrStepFn`/`arrFold` are the `Function.update` source semantics on an
array state `Nat → BitVec w`; `wReadExpr`/`arrRecUnroll` are the flat unrolled
`ImpExpr` the front compiles; `arrRecUnroll_denoteScalar` is the preservation
theorem tying them via the per-element-SSA env invariant. -/

/-- Per-element fresh local name for the SSA'd array slot `W[i]`. We use a
    **unary** encoding (`"W" ++ "I"^i`) rather than `toString i`, because its
    injectivity (`wName_inj`) is elementary (`List.replicate` length) — the
    fresh-name disequality the array-SSA invariant needs across distinct
    written elements. Any injective `Nat → String` would do; the names are
    internal SSA temporaries, not a front-emission contract. -/
def wName (i : Nat) : String := "W" ++ String.ofList (List.replicate i 'I')

/-- The per-step `BitVec w` recurrence on the array state: the
    message-schedule read-read-write body `W[i] := W[i-1] + W[i-2]`. Independent
    of the translator — this is the arithmetic meaning. -/
def arrStepFn {w : Nat} (W : Nat → BitVec w) (i : Nat) : BitVec w :=
  W (i - 1) + W (i - 2)

/-- The **array-state** source meaning of the bounded recurrence:
    starting from `seed` (the input words for the `< base` slots), perform
    `count` writes `W[base + j] := arrStepFn W (base + j)` for `j = 0 .. count-1`,
    each via `Function.update`. Returns the final array state `Nat → BitVec w`.
    No reference to the translator: this is what preservation certifies. -/
def arrFold {w : Nat} (seed : Nat → BitVec w) (base : Nat) :
    (count : Nat) → (Nat → BitVec w)
  | 0 => seed
  | c + 1 => Function.update (arrFold seed base c) (base + c)
      (arrStepFn (arrFold seed base c) (base + c))

/-- The `ImpExpr` read of array element `W[j]`: a **local** `var (wName j)` when
    `j ≥ base` (already written), else the input read `index[arr, lit j]` (a
    seed, resolving via `indexAtom?` to input atom `j`). This is the
    element→source resolution that the literal-index discipline makes static. -/
def wReadExpr (arr : String) (base j : Nat) : ImpExpr :=
  if base ≤ j then .var (wName j) else .app "index" [.var arr, .lit (.int j)]

/-- The fully-unrolled flat `ImpExpr` for the bounded array recurrence,
    body-first: for `count` writes at source indices `i, i+1, …`, emit
    `let wName i = wReadExpr (i-1) + wReadExpr (i-2); …`, then return
    `var (wName (i-1))` (the last element written before `i`). Each element is a
    fresh local; reads resolve to earlier locals or input seeds. This is the flat
    let-chain the §3 `impExprToThir` consumes directly (every step a recognised
    `wrapping_add` of two atom reads). Mirrors §7's `hornerUnroll`, but with
    per-element fresh names (no reused accumulator). -/
def arrRecUnroll (arr : String) (base : Nat) : (count i : Nat) → ImpExpr
  | 0, i => .var (wName (i - 1))
  | c + 1, i =>
      .letBind (wName i)
        (.app "wrapping_add" [wReadExpr arr base (i - 1), wReadExpr arr base (i - 2)])
        (arrRecUnroll arr base c (i + 1))

/-- Build the whole compiled array recurrence: run the unrolled write-chain for
    `i = base .. N-1` (that is `N - base` writes from index `base`), returning the
    final element `W[N-1]`. Single array parameter `arr`; the first `base` slots
    are input seeds. Flat `ImpExpr` the front's `impExprToThir` (§3) consumes. -/
def arrRecProgram (arr : String) (base N : Nat) : ImpExpr :=
  arrRecUnroll arr base (N - base) base

/-! ### §8.1  The per-element-SSA preservation theorem

`arrRecUnroll_denoteScalar` proves the unrolled flat `ImpExpr` denotes (under the
independent §2 `denoteScalar`) exactly to the `arrFold` array-state
source meaning, by induction on the write count. The invariant ties each env
local `wName j` to the array state at `j` for every already-written slot — the
array-SSA invariant. Fresh-element disjointness (`wName_inj`) keeps a write at
`i` from clobbering the earlier locals. -/

/-- The unary per-element names are injective: `wName i = wName j → i = j`. The
    fresh-name disequality the array-SSA invariant needs (distinct written
    elements are distinct locals). Elementary via `List.replicate` length. -/
theorem wName_inj {i j : Nat} (h : i ≠ j) : wName i ≠ wName j := by
  unfold wName
  intro hc
  apply_fun (·.toList) at hc
  rw [String.toList_append, String.toList_append] at hc
  rw [show "W".toList = ['W'] from rfl, String.toList_ofList, String.toList_ofList] at hc
  have hc2 : List.replicate i 'I' = List.replicate j 'I' := (List.cons_inj_right 'W').mp hc
  apply h
  have := congrArg List.length hc2
  simpa [List.length_replicate] using this

/-- A bare-element local `var (wName k)` (array parameter `arr` with
    `arr ≠ wName k`, so `wName k` is local not a param) reads the env at it. -/
theorem arrFold_succ_stable {w : Nat} (seed : Nat → BitVec w) (base count j : Nat)
    (h : j ≠ base + count) :
    arrFold seed base (count + 1) j = arrFold seed base count j := by
  simp only [arrFold, Function.update_apply, if_neg h]

/-- The array state at slot `j` is **stable** once `j` has been written/seeded:
    extending the fold to any `count' ≥ count` leaves index `j` unchanged when
    `j < base + count` (later writes hit only `base + c ≥ j`). The monotonicity
    that lets earlier-element locals survive subsequent writes. -/
theorem arrFold_stable {w : Nat} (seed : Nat → BitVec w) (base count j : Nat)
    (hj : j < base + count) :
    (count' : Nat) → count ≤ count' →
    arrFold seed base count' j = arrFold seed base count j := by
  intro count' hle
  induction count' with
  | zero =>
      have : count = 0 := by omega
      subst this; rfl
  | succ c ih =>
      rcases Nat.lt_or_ge count (c + 1) with hlt | hge
      · rw [arrFold_succ_stable seed base c j (by omega)]; exact ih (by omega)
      · have : count = c + 1 := by omega
        subst this; rfl

/-- The array state below `base` is always the seed (writes never touch
    `j < base`). The seed-slot read fact: `index[arr, lit j]` for `j < base`
    resolves to `inpGet I j = arrFold (inpGet I) base count j`. -/
theorem arrFold_seed_below {w : Nat} (seed : Nat → BitVec w) (base j : Nat)
    (hj : j < base) :
    (count : Nat) → arrFold seed base count j = seed j := by
  intro count
  induction count with
  | zero => rfl
  | succ c ih =>
      simp only [arrFold, Function.update_apply, if_neg (by omega : j ≠ base + c)]; exact ih

/-- A `W[j]` read for `j < base + cnt` denotes (under `denoteScalar`'s atom layer)
    to the array state at `j`: when `j ≥ base` it is the local `wName j`, read off
    the env via the array-SSA invariant `hρ`; when `j < base` it is the input
    seed `index[arr, lit j] = inpGet I j = arrFold … j`. Array parameter `arr`
    distinct from every element name (`harr`). -/
theorem wReadExpr_denote {w nIn : Nat} (I : Fin nIn → BitVec w) (arr : String)
    (base : Nat) (harr : ∀ k, arr ≠ wName k) (j : Nat) (cnt : Nat)
    (hj : j < base + cnt) (ρ : String → Option (BitVec w))
    (hρ : ∀ k, base ≤ k → k < base + cnt →
        ρ (wName k) = some (arrFold (inpGet I) base cnt k)) :
    denoteAtomExpr [arr] I (wReadExpr arr base j) ρ
      = some (arrFold (inpGet I) base cnt j) := by
  unfold wReadExpr
  by_cases hb : base ≤ j
  · simp only [hb, if_true]
    rw [denoteAtomExpr]
    simp only [idxOf_arr_none (harr j)]
    exact hρ j hb hj
  · simp only [hb, if_false]
    have hb' : j < base := by omega
    rw [denoteAtomExpr_indexLit I arr j ρ, arrFold_seed_below (inpGet I) base j hb' cnt]

/-- Writing slot `i` (the `(i - base)`-th write) yields the step value: the array
    state after `i - base + 1` writes equals the step body at `i` over the
    state after `i - base` writes. The key one-step computation tying the bound
    let value to `arrFold`. -/
theorem arrFold_write {w : Nat} (seed : Nat → BitVec w) (base i : Nat)
    (hbi : base ≤ i) :
    arrFold seed base (i - base + 1) i = arrStepFn (arrFold seed base (i - base)) i := by
  conv_lhs => rw [arrFold]
  rw [show base + (i - base) = i from by omega]
  simp only [Function.update_apply, if_true]

/-- **Array-write recurrence is value-preserving (per-element SSA).** The unrolled
    flat let-chain `arrRecUnroll` denotes (under `denoteScalar`, array parameter
    `arr` distinct from every element name) exactly to the `arrFold`
    array-state meaning. Proved by induction on the write `count`, generalized
    over the env `ρ`, under the **array-SSA invariant** `hρ`: every already-written
    local `wName k` (`base ≤ k < i`) equals the array state at `k`. The fresh
    write at `i` extends the invariant (earlier locals survive by `arrFold_stable`,
    the new local is the step value by `arrFold_write`). `hb2 : 2 ≤ base` keeps
    the two reads `W[i-1]`, `W[i-2]` in range; `hret` guarantees the returned
    slot `i - 1` is itself in range (covered for `count = 0`). This is the array
    analogue of §7's `hornerUnroll_denoteScalar`. -/
theorem arrRecUnroll_denoteScalar {w nIn : Nat} (I : Fin nIn → BitVec w)
    (arr : String) (base : Nat) (harr : ∀ k, arr ≠ wName k) (hb2 : 2 ≤ base) :
    (count i : Nat) → base ≤ i →
    (ρ : String → Option (BitVec w)) →
    (∀ k, base ≤ k → k < i → ρ (wName k) = some (arrFold (inpGet I) base (i - base) k)) →
    base ≤ i - 1 ∨ 0 < count →
    ImpExpr.denoteScalar [arr] I (arrRecUnroll arr base count i) ρ
      = some (arrFold (inpGet I) base (i - base + count) (i + count - 1))
  | 0, i, hi, ρ, hρ, hret => by
      simp only [arrRecUnroll]
      rcases hret with hr | hr
      · rw [show ImpExpr.denoteScalar [arr] I (.var (wName (i - 1))) ρ = ρ (wName (i - 1)) from by
              simp only [ImpExpr.denoteScalar, denoteAtomExpr, idxOf_arr_none (harr (i - 1))]]
        rw [hρ (i - 1) hr (by omega)]
        rw [show i - base + 0 = i - base from rfl, show i + 0 - 1 = i - 1 from by omega]
      · omega
  | c + 1, i, hi, ρ, hρ, hret => by
      have hipos : 0 < i := by omega
      have hbi : base + (i - base) = i := by omega
      have hr1 := wReadExpr_denote I arr base harr (i - 1) (i - base) (by rw [hbi]; omega) ρ
        (by intro k hk1 hk2; rw [hbi] at hk2; exact hρ k hk1 hk2)
      have hr2 := wReadExpr_denote I arr base harr (i - 2) (i - base) (by rw [hbi]; omega) ρ
        (by intro k hk1 hk2; rw [hbi] at hk2; exact hρ k hk1 hk2)
      have hval : arrFold (inpGet I) base (i - base) (i - 1)
            + arrFold (inpGet I) base (i - base) (i - 2)
          = arrFold (inpGet I) base (i - base + 1) i := by
        rw [arrFold_write (inpGet I) base i hi]; rfl
      simp only [arrRecUnroll, ImpExpr.denoteScalar, recogBin, String.reduceEq, or_self,
        reduceIte, true_or, hr1, hr2, Option.bind_some, Option.map_some]
      rw [show JasminBinOp.add.apply
            (arrFold (inpGet I) base (i - base) (i - 1)) (arrFold (inpGet I) base (i - base) (i - 2))
            = arrFold (inpGet I) base (i - base + 1) i from hval]
      have hnew : ∀ k, base ≤ k → k < i + 1 →
          (fun y => if y = wName i then some (arrFold (inpGet I) base (i - base + 1) i) else ρ y)
              (wName k)
            = some (arrFold (inpGet I) base ((i + 1) - base) k) := by
        intro k hk1 hk2
        by_cases hki : k = i
        · rw [show (fun y => if y = wName i then some (arrFold (inpGet I) base (i - base + 1) i)
                  else ρ y) (wName k)
                = some (arrFold (inpGet I) base (i - base + 1) i) from by rw [hki]; simp]
          rw [show (i + 1) - base = i - base + 1 from by omega, hki]
        · have hklt : k < i := by omega
          rw [show (fun y => if y = wName i then some (arrFold (inpGet I) base (i - base + 1) i)
                  else ρ y) (wName k)
                = ρ (wName k) from by simp only [if_neg (wName_inj hki)]]
          rw [hρ k hk1 hklt]
          have hcc : i - base ≤ (i + 1) - base := by omega
          have hjlt : k < base + (i - base) := by rw [hbi]; exact hklt
          rw [arrFold_stable (inpGet I) base (i - base) k hjlt ((i + 1) - base) hcc]
      rw [arrRecUnroll_denoteScalar I arr base harr hb2 c (i + 1) (by omega)
          (fun y => if y = wName i then some (arrFold (inpGet I) base (i - base + 1) i) else ρ y)
          hnew (by left; omega)]
      have e1 : (i + 1) - base + c = i - base + (c + 1) := by omega
      have e2 : (i + 1) + c - 1 = i + (c + 1) - 1 := by omega
      rw [e1, e2]

/-- **Bounded array recurrence is value-preserving.** The whole-program
    `arrRecProgram` denotes (under `denoteScalar`, the empty env) to the
    `arrFold` array-state meaning: the final element `W[N-1]` of the recurrence
    seeded from the input array. Specialises `arrRecUnroll_denoteScalar` at the
    initial state (no locals yet; the invariant holds vacuously since `i = base`
    means no `base ≤ k < base`). Requires `base ≤ N` (`hbN`) and `base < N`
    (`hlt`) so at least one write happens and the returned slot is in range. -/
theorem arrRecProgram_denoteScalar {w nIn : Nat} (I : Fin nIn → BitVec w)
    (arr : String) (base N : Nat) (harr : ∀ k, arr ≠ wName k) (hb2 : 2 ≤ base)
    (hlt : base < N) :
    ImpExpr.denoteScalar [arr] I (arrRecProgram arr base N) (fun _ => none)
      = some (arrFold (inpGet I) base (N - base) (N - 1)) := by
  rw [arrRecProgram,
    arrRecUnroll_denoteScalar I arr base harr hb2 (N - base) base (le_refl base)
      (fun _ => none)
      (by intro k hk1 hk2; omega)
      (by right; omega)]
  rw [show base - base + (N - base) = N - base from by omega,
    show base + (N - base) - 1 = N - 1 from by omega]

/-! ## §9  The SHA-256 message-schedule σ recurrence (multi-op step body)

This section is **the convergence demo**: it combines the two whole-function
pieces — §7's bounded-loop unrolling and §8's array-write per-element SSA — with a
multi-op σ step body, giving the **SHA-256 message-schedule
recurrence** (FIPS 180-4), value-preserving from hax `ImpExpr` through the front.

### The recurrence (FIPS 180-4 §6.2.2)

For `i = 16 .. N-1`:
```text
W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]      (mod 2³², wrapping)
σ₀(x) = (x ⋙ 7)  ⊕ (x ⋙ 18) ⊕ (x >> 3)
σ₁(x) = (x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x >> 10)
```
with `W[0..15]` the input message words. This is §8's **array-write recurrence**
(per-element SSA on `wName i`) but with §8's fixed two-read `W[i-1]+W[i-2]` body
replaced by the full four-read σ body, whose σ₀/σ₁ are themselves the
rotate/shift/xor combos §5/§7 already prove. No new dialect op, no hardware leaf —
this is pure front machinery, the array-SSA (§8) + multi-op σ (ror/shr/xor + adds)
convergence.

`sigmaGen`/`schedStepFn`/`schedFold` are the translator-free `BitVec 32`
source semantics; `sigBlock`/`schedStepBody`/`schedUnroll` are the flat unrolled
`ImpExpr` the front compiles; `schedUnroll_denoteScalar` is the preservation
theorem, the §8 array-SSA induction re-run with the wider σ step.

We fix `w = 32` (the SHA-256 word width — σ₀/σ₁ are width-specific) and the input
array parameter name `"w"`. The σ-block scratch locals (`sa`/`sb`/`sc`) and the
per-step temporaries (`s1`/`s0`/`t1`/`t2`) all start with `s`/`t`, hence are
disjoint from every `wName k = "W" ++ "I"^k` (which starts with `'W'`) — the
fresh-name disjointness the array-SSA invariant needs. -/

/-- The generic SHA-256 small-σ shape `x ⋙ rot1 ⊕ x ⋙ rot2 ⊕ x >> sh`. With
    `(7, 18, 3)` this is FIPS σ₀; with `(17, 19, 10)` it is σ₁. The translator-free
    `BitVec 32` meaning the σ-block let-chain reproduces. -/
def sigmaGen (rot1 rot2 sh : Nat) (x : BitVec 32) : BitVec 32 :=
  x.rotateRight rot1 ^^^ x.rotateRight rot2 ^^^ x >>> sh

/-- FIPS 180-4 σ₀: `(x ⋙ 7) ⊕ (x ⋙ 18) ⊕ (x >> 3)`. -/
def sigma0Fn (x : BitVec 32) : BitVec 32 := sigmaGen 7 18 3 x

/-- FIPS 180-4 σ₁: `(x ⋙ 17) ⊕ (x ⋙ 19) ⊕ (x >> 10)`. -/
def sigma1Fn (x : BitVec 32) : BitVec 32 := sigmaGen 17 19 10 x

/-- The per-step `BitVec 32` schedule recurrence (FIPS 180-4 §6.2.2):
    `W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]`. The wrapping adds are
    `BitVec` `+`. Independent of the translator — the arithmetic meaning the
    preservation theorem certifies. The §9 analogue of §8's `arrStepFn`. -/
def schedStepFn (W : Nat → BitVec 32) (i : Nat) : BitVec 32 :=
  sigma1Fn (W (i - 2)) + W (i - 7) + sigma0Fn (W (i - 15)) + W (i - 16)

/-- The **array-state** source meaning of the bounded σ schedule: starting
    from `seed` (the input message words for `< 16` slots), perform `count` writes
    `W[16 + j] := schedStepFn W (16 + j)` for `j = 0 .. count-1`, each via
    `Function.update`. The §9 analogue of §8's `arrFold` with the σ step. -/
def schedFold (seed : Nat → BitVec 32) : (count : Nat) → (Nat → BitVec 32)
  | 0 => seed
  | c + 1 => Function.update (schedFold seed c) (16 + c)
      (schedStepFn (schedFold seed c) (16 + c))

/-- A σ-block let-chain over an atom-expr read `r`: bind the rotate/shift parts to
    scratch locals `sa`/`sb`/`sc`, xor them, and bind the σ result to `nout`, then
    run `cont`. `r` is read three times (as a nested atom argument of the
    `rotate_right`/`shift_right` apps — exactly the `index`/`var` read shape
    `denoteAtomExpr` resolves). With `(7,18,3)`/`(17,19,10)` this emits σ₀/σ₁. -/
def sigBlock (rot1 rot2 sh : Nat) (nout : String) (r cont : ImpExpr) : ImpExpr :=
  .letBind "sa" (.app "rotate_right" [r, .lit (.int rot1)])
   (.letBind "sb" (.app "rotate_right" [r, .lit (.int rot2)])
    (.letBind "sc" (.app "shift_right" [r, .lit (.int sh)])
     (.letBind "sa" (.app "BitXor" [.var "sa", .var "sb"])
      (.letBind nout (.app "BitXor" [.var "sa", .var "sc"]) cont))))

/-- **σ-block is value-preserving.** Under `denoteScalar` (array parameter `"w"`),
    the σ-block over a read `r` denoting to `v` (stably across the scratch
    extensions — `hr`) runs `cont` in the env extended with `nout := sigmaGen v`
    (plus the dead scratch slots). The σ analogue of §8's `wReadExpr_denote`,
    discharging the rotate/shift/xor reductions the front recognises. -/
theorem sigBlock_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (rot1 rot2 sh : Nat) (nout : String)
    (r : ImpExpr) (v : BitVec 32)
    (hr : ∀ ρ', (∀ y, y ≠ "sa" → y ≠ "sb" → ρ' y = ρ y) →
        denoteAtomExpr ["w"] I r ρ' = some v)
    (hsh : sh < 32) (cont : ImpExpr) :
    ImpExpr.denoteScalar ["w"] I (sigBlock rot1 rot2 sh nout r cont) ρ
      = ImpExpr.denoteScalar ["w"] I cont
          (fun y => if y = nout then some (sigmaGen rot1 rot2 sh v)
                    else if y = "sa" then some (v.rotateRight rot1 ^^^ v.rotateRight rot2)
                    else if y = "sc" then some (v >>> sh)
                    else if y = "sb" then some (v.rotateRight rot2) else ρ y) := by
  have e0 := hr ρ (fun _ _ _ => rfl)
  have e1 := hr (fun y => if y = "sa" then some (v.rotateRight rot1) else ρ y)
    (fun y h _ => by simp [if_neg h])
  have e2 := hr (fun y => if y = "sb" then some (v.rotateRight rot2)
                          else if y = "sa" then some (v.rotateRight rot1) else ρ y)
    (fun y h1 h2 => by simp [if_neg h1, if_neg h2])
  have hsa : denoteAtomExpr ["w"] I (ImpExpr.var "sa") = fun ρ' => ρ' "sa" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("w":String) ≠ "sa" by decide)]
  have hsb : denoteAtomExpr ["w"] I (ImpExpr.var "sb") = fun ρ' => ρ' "sb" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("w":String) ≠ "sb" by decide)]
  have hsc : denoteAtomExpr ["w"] I (ImpExpr.var "sc") = fun ρ' => ρ' "sc" := by
    funext ρ'; simp only [denoteAtomExpr, idxOf_arr_none (show ("w":String) ≠ "sc" by decide)]
  simp only [sigBlock, ImpExpr.denoteScalar, recogBin, recogShift,
    litNat?, ShiftKind.apply, JasminBinOp.apply, reduceIte,
    String.reduceEq, Int.toNat, or_self, or_false,
    e0, e1, e2, hsa, hsb, hsc, Option.bind_some, Option.map_some, sigmaGen, if_true,
    VIR.shiftMask_of_lt hsh]
  congr 1
  funext y
  by_cases h : y = "sa" <;> simp [h]

/-- Every per-element name `wName k = "W" ++ "I"^k` starts with `'W'`, so it is
    distinct from any scratch/temporary name that does not. The fresh-name
    disjointness the array-SSA invariant needs against the σ-block scratch. -/
theorem wName_ne_of_head {k : Nat} {s : String} (hs : s.toList.head? ≠ some 'W') :
    wName k ≠ s := by
  intro hc
  apply hs
  rw [← hc]
  have h : (wName k).toList = 'W' :: (String.ofList (List.replicate k 'I')).toList := by
    simp only [wName, String.toList_append, show "W".toList = ['W'] from rfl,
      List.cons_append, List.nil_append]
  rw [h, List.head?_cons]

/-- The σ-schedule **step body** for index `i` (FIPS 180-4 §6.2.2): compute
    `σ₁(W[i-2])` into `s1`, `σ₀(W[i-15])` into `s0` (each a `sigBlock`), then the
    three wrapping adds `t1 = s1 + W[i-7]`, `t2 = t1 + s0`,
    `wName i = t2 + W[i-16]`, finally running `cont`. Each `W[j]` read is the §8
    `wReadExpr` (local `wName j` for `j ≥ 16`, input seed `index[w, lit j]` for
    `j < 16`). This is §8's per-element step, widened from `W[i-1]+W[i-2]` to the
    real four-read σ body. -/
def schedStepBody (i : Nat) (cont : ImpExpr) : ImpExpr :=
  sigBlock 17 19 10 "s1" (wReadExpr "w" 16 (i - 2))
   (sigBlock 7 18 3 "s0" (wReadExpr "w" 16 (i - 15))
    (.letBind "t1" (.app "wrapping_add" [.var "s1", wReadExpr "w" 16 (i - 7)])
     (.letBind "t2" (.app "wrapping_add" [.var "t1", .var "s0"])
      (.letBind (wName i)
        (.app "wrapping_add" [.var "t2", wReadExpr "w" 16 (i - 16)]) cont))))

/-- The fully-unrolled flat `ImpExpr` for the bounded σ schedule, body-first: for
    `count` writes at source indices `i, i+1, …`, emit `schedStepBody i (…)`, then
    return `var (wName (i-1))` (the last element written before `i`). The §9
    analogue of §8's `arrRecUnroll` with the σ step body. -/
def schedUnroll : (count i : Nat) → ImpExpr
  | 0, i => .var (wName (i - 1))
  | c + 1, i => schedStepBody i (schedUnroll c (i + 1))

/-- Build the whole compiled σ schedule: run the unrolled write-chain for
    `i = 16 .. N-1` (that is `N - 16` writes from index `16`), returning the final
    element `W[N-1]`. Single array parameter `"w"`; the first 16 slots are input
    message words. Flat `ImpExpr` the front's `impExprToThir` (§3) consumes. -/
def schedProgram (N : Nat) : ImpExpr :=
  schedUnroll (N - 16) 16

/-! ### §9.1  The σ-schedule preservation theorem

`schedUnroll_denoteScalar` is the §8 array-SSA induction re-run with the σ step
body. The `schedFold` stability lemmas (`schedFold_*`) mirror §8's `arrFold_*`
exactly (the recurrence's only change is the step function, not the array-SSA
bookkeeping). `wReadExpr_denoteSched` is the §8 `wReadExpr_denote` over `schedFold`;
`schedStep_denote` is the per-step lemma threading `sigBlock_denote` twice plus
the three adds. -/

/-- `schedFold` is stable at any slot `j` not touched by the `(count)`-th write. -/
theorem schedFold_succ_stable (seed : Nat → BitVec 32) (count j : Nat)
    (h : j ≠ 16 + count) :
    schedFold seed (count + 1) j = schedFold seed count j := by
  simp only [schedFold, Function.update_apply, if_neg h]

/-- `schedFold` at slot `j` is stable once `j < 16 + count` (later writes hit only
    `16 + c ≥ j`). The §9 analogue of §8's `arrFold_stable`. -/
theorem schedFold_stable (seed : Nat → BitVec 32) (count j : Nat)
    (hj : j < 16 + count) :
    (count' : Nat) → count ≤ count' → schedFold seed count' j = schedFold seed count j := by
  intro count' hle
  induction count' with
  | zero => have : count = 0 := by omega
            subst this; rfl
  | succ c ih =>
      rcases Nat.lt_or_ge count (c + 1) with hlt | hge
      · rw [schedFold_succ_stable seed c j (by omega)]; exact ih (by omega)
      · have : count = c + 1 := by omega
        subst this; rfl

/-- `schedFold` below `16` is always the seed (writes never touch `j < 16`). The
    §9 analogue of §8's `arrFold_seed_below`. -/
theorem schedFold_seed_below (seed : Nat → BitVec 32) (j : Nat) (hj : j < 16) :
    (count : Nat) → schedFold seed count j = seed j := by
  intro count
  induction count with
  | zero => rfl
  | succ c ih =>
      simp only [schedFold, Function.update_apply, if_neg (by omega : j ≠ 16 + c)]; exact ih

/-- Writing slot `i` (the `(i - 16)`-th write) yields the step value. The §9
    analogue of §8's `arrFold_write`. -/
theorem schedFold_write (seed : Nat → BitVec 32) (i : Nat) (hi : 16 ≤ i) :
    schedFold seed (i - 16 + 1) i = schedStepFn (schedFold seed (i - 16)) i := by
  conv_lhs => rw [schedFold]
  rw [show 16 + (i - 16) = i from by omega]
  simp only [Function.update_apply, if_true]

/-- A `W[j]` read (`wReadExpr "w" 16 j`) for `j < 16 + cnt` denotes to the
    `schedFold` array state at `j`, under any env whose `wName` slots satisfy the
    array-SSA invariant `hρ`. The §9 (`schedFold`) analogue of §8's
    `wReadExpr_denote`. -/
theorem wReadExpr_denoteSched {nIn : Nat} (I : Fin nIn → BitVec 32) (j cnt : Nat)
    (hj : j < 16 + cnt) (ρ : String → Option (BitVec 32))
    (hρ : ∀ k, 16 ≤ k → k < 16 + cnt → ρ (wName k) = some (schedFold (inpGet I) cnt k)) :
    denoteAtomExpr ["w"] I (wReadExpr "w" 16 j) ρ
      = some (schedFold (inpGet I) cnt j) := by
  unfold wReadExpr
  by_cases hb : 16 ≤ j
  · simp only [hb, if_true]
    rw [denoteAtomExpr]
    simp only [idxOf_arr_none (show ("w":String) ≠ wName j from (wName_ne_of_head
      (by decide)).symm)]
    exact hρ j hb hj
  · simp only [hb, if_false]
    have hb' : j < 16 := by omega
    rw [denoteAtomExpr_indexLit I "w" j ρ, schedFold_seed_below (inpGet I) j hb' cnt]

/-- A `W[j]` read is stable under env-extension at the σ-block scratch names
    `sa`/`sb` (they are not `wName` slots): if `ρ'` agrees with `ρ` off `{sa, sb}`
    then the read under `ρ'` matches the `schedFold` state, for `j < 16 + cnt`. The
    σ-block `hr` precondition, instantiated for `wReadExpr` reads. -/
theorem wReadExpr_denoteSched_scratch {nIn : Nat} (I : Fin nIn → BitVec 32)
    (j cnt : Nat) (hj : j < 16 + cnt) (ρ ρ' : String → Option (BitVec 32))
    (hagree : ∀ y, y ≠ "sa" → y ≠ "sb" → ρ' y = ρ y)
    (hρ : ∀ k, 16 ≤ k → k < 16 + cnt → ρ (wName k) = some (schedFold (inpGet I) cnt k)) :
    denoteAtomExpr ["w"] I (wReadExpr "w" 16 j) ρ' = some (schedFold (inpGet I) cnt j) := by
  apply wReadExpr_denoteSched I j cnt hj ρ'
  intro k hk1 hk2
  rw [hagree (wName k) (wName_ne_of_head (by decide)) (wName_ne_of_head (by decide))]
  exact hρ k hk1 hk2

/-- **The σ-schedule step is value-preserving.** Under the array-SSA invariant `hρ`
    (`cnt = i - 16`, every written `wName k` equal to the `schedFold` state), the
    step body for `i` denotes (via the two `sigBlock_denote` applications and the
    three adds) to `cont` run in the env extended at `wName i` with the
    step value `schedFold (inpGet I) (cnt + 1) i = schedStepFn …`, plus dead
    σ-scratch/temporary slots. The per-step computation the recurrence iterates. -/
theorem schedStep_denote {nIn : Nat} (I : Fin nIn → BitVec 32) (i : Nat)
    (hi : 16 ≤ i) (ρ : String → Option (BitVec 32)) (cont : ImpExpr)
    (hρ : ∀ k, 16 ≤ k → k < i → ρ (wName k) = some (schedFold (inpGet I) (i - 16) k)) :
    ImpExpr.denoteScalar ["w"] I (schedStepBody i cont) ρ
      = ImpExpr.denoteScalar ["w"] I cont
          (fun y => if y = wName i then some (schedFold (inpGet I) (i - 16 + 1) i)
                    else (fun y' => if y' = "s1" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)))
                          else if y' = "sa" then some ((schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 7 ^^^ (schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 18)
                          else if y' = "sc" then some ((schedFold (inpGet I) (i - 16) (i - 15)) >>> (3:Nat))
                          else if y' = "sb" then some ((schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 18)
                          else if y' = "s0" then some (sigma0Fn (schedFold (inpGet I) (i - 16) (i - 15)))
                          else if y' = "t1" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)) + schedFold (inpGet I) (i - 16) (i - 7))
                          else if y' = "t2" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)) + schedFold (inpGet I) (i - 16) (i - 7) + sigma0Fn (schedFold (inpGet I) (i - 16) (i - 15)))
                          else ρ y') y) := by
  set cnt := i - 16 with hcnt
  -- read facts (each `W[j]` is in range `< 16 + cnt = i`)
  have hib : 16 + cnt = i := by omega
  have hρ' : ∀ k, 16 ≤ k → k < 16 + cnt → ρ (wName k) = some (schedFold (inpGet I) cnt k) := by
    intro k hk1 hk2; exact hρ k hk1 (by omega)
  -- abbreviations for the two σ read values
  set v1 := schedFold (inpGet I) cnt (i - 2) with hv1
  set v0 := schedFold (inpGet I) cnt (i - 15) with hv0
  -- σ₁ block over W[i-2]
  rw [schedStepBody, sigBlock_denote I ρ 17 19 10 "s1"
      (wReadExpr "w" 16 (i - 2)) v1
      (fun ρ' hag => wReadExpr_denoteSched_scratch I (i - 2) cnt (by omega) ρ ρ' hag hρ')
      (by decide)]
  -- the σ₁-extended env (base for the σ₀ block) agrees with ρ on every `wName` slot.
  set ρ1 : String → Option (BitVec 32) :=
    (fun y => if y = "s1" then some (sigmaGen 17 19 10 v1)
              else if y = "sa" then some (v1.rotateRight 17 ^^^ v1.rotateRight 19)
              else if y = "sc" then some (v1 >>> (10:Nat))
              else if y = "sb" then some (v1.rotateRight 19) else ρ y) with hρ1def
  have hρ1 : ∀ k, 16 ≤ k → k < 16 + cnt → ρ1 (wName k) = some (schedFold (inpGet I) cnt k) := by
    intro k hk1 hk2
    rw [hρ1def]
    simp only [if_neg (wName_ne_of_head (by decide) : wName k ≠ "s1"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sa"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sc"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sb")]
    exact hρ' k hk1 hk2
  -- σ₀ block over W[i-15]
  rw [sigBlock_denote I ρ1 7 18 3 "s0"
      (wReadExpr "w" 16 (i - 15)) v0
      (fun ρ' hag => wReadExpr_denoteSched_scratch I (i - 15) cnt (by omega) ρ1 ρ' hag hρ1)
      (by decide)]
  -- the σ₀-extended env (base for the three adds): name it and record its `wName`
  -- invariant, the `s1`/`s0` lookups, and the two remaining `W[j]` reads.
  set ρ2 : String → Option (BitVec 32) :=
    (fun y => if y = "s0" then some (sigmaGen 7 18 3 v0)
              else if y = "sa" then some (v0.rotateRight 7 ^^^ v0.rotateRight 18)
              else if y = "sc" then some (v0 >>> (3:Nat))
              else if y = "sb" then some (v0.rotateRight 18) else ρ1 y) with hρ2def
  -- `s1`/`s0` lookups
  have hs1 : ρ2 "s1" = some (sigma1Fn v1) := by
    simp only [hρ2def, hρ1def, sigma1Fn, String.reduceEq, reduceIte]
  have hs0 : ρ2 "s0" = some (sigma0Fn v0) := by
    simp only [hρ2def, sigma0Fn, String.reduceEq, reduceIte]
  -- the two remaining `W[j]` reads (i-7, i-16) under ρ2 (its `wName` slots = ρ's)
  have hρ2 : ∀ k, 16 ≤ k → k < 16 + cnt → ρ2 (wName k) = some (schedFold (inpGet I) cnt k) := by
    intro k hk1 hk2
    rw [hρ2def]
    simp only [if_neg (wName_ne_of_head (by decide) : wName k ≠ "s0"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sa"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sc"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "sb")]
    exact hρ1 k hk1 hk2
  have hr7 := wReadExpr_denoteSched I (i - 7) cnt (by omega) ρ2 hρ2
  -- reduce the three wrapping adds binding t1, t2, wName i
  simp only [ImpExpr.denoteScalar, recogBin, String.reduceEq, or_self, reduceIte,
    true_or, JasminBinOp.apply, denoteAtomExpr,
    idxOf_arr_none (show ("w":String) ≠ "s1" by decide),
    idxOf_arr_none (show ("w":String) ≠ "s0" by decide),
    idxOf_arr_none (show ("w":String) ≠ "t1" by decide),
    idxOf_arr_none (show ("w":String) ≠ "t2" by decide),
    hs1, hs0, hr7, Option.bind_some, Option.map_some, if_true]
  -- the final `W[i-16]` read (env extended at dead `t1`/`t2`) matches `ρ2`'s read.
  have hr16' : denoteAtomExpr ["w"] I (wReadExpr "w" 16 (i - 16))
      (fun y => if y = "t2" then some (sigma1Fn v1 + schedFold (inpGet I) cnt (i - 7) + sigma0Fn v0)
                else if y = "t1" then some (sigma1Fn v1 + schedFold (inpGet I) cnt (i - 7)) else ρ2 y)
      = some (schedFold (inpGet I) cnt (i - 16)) := by
    apply wReadExpr_denoteSched I (i - 16) cnt (by omega)
    intro k hk1 hk2
    simp only [if_neg (wName_ne_of_head (by decide) : wName k ≠ "t2"),
      if_neg (wName_ne_of_head (by decide) : wName k ≠ "t1")]
    exact hρ2 k hk1 hk2
  rw [hr16']
  -- the bound step value is `schedStepFn` = `schedFold (cnt+1) i`.
  have hstep : sigma1Fn v1 + schedFold (inpGet I) cnt (i - 7) + sigma0Fn v0
        + schedFold (inpGet I) cnt (i - 16)
      = schedFold (inpGet I) (cnt + 1) i := by
    rw [show cnt + 1 = i - 16 + 1 from by omega, schedFold_write (inpGet I) i hi]
    simp only [schedStepFn, hv1, hv0, hcnt]
  rw [Option.map_some, Option.bind_some, hstep]
  -- reconcile the two `cont` envs: `wName i` is matched first; the dead temporaries
  -- (`s1`/`sa`/…/`t2`) agree pointwise, all distinct from `wName i`.
  congr 1
  funext y
  by_cases hy : y = wName i
  · simp only [hy, if_true]
  · simp only [if_neg hy, hρ2def, hρ1def, sigma1Fn, sigma0Fn]
    by_cases h1 : y = "s1"
    · simp [h1]
    by_cases ha : y = "sa"
    · simp [ha]
    by_cases hc : y = "sc"
    · simp [hc]
    by_cases hb : y = "sb"
    · simp [hb]
    by_cases h0 : y = "s0"
    · simp [h0]
    by_cases ht1 : y = "t1"
    · simp [ht1]
    by_cases ht2 : y = "t2"
    · simp [ht2]
    · simp [h1, ha, hc, hb, h0, ht1, ht2]

/-- **The σ schedule recurrence is value-preserving (per-element SSA).** The
    unrolled flat let-chain `schedUnroll` denotes (under `denoteScalar`, array
    parameter `"w"`) exactly to the `schedFold` array-state meaning. Proved
    by induction on the write `count`, generalized over the env `ρ`, under the
    array-SSA invariant `hρ`: every already-written `wName k` (`16 ≤ k < i`) equals
    the array state at `k`. The fresh σ step at `i` extends the invariant (earlier
    locals survive — they are distinct names, and the σ-block scratch is disjoint
    from every `wName` slot; the new local is the step value by `schedStep_denote`).
    `hb16 : 16 ≤ i` keeps the four reads `W[i-2]`, `W[i-7]`, `W[i-15]`, `W[i-16]` in
    range. The §9 (multi-op σ body) analogue of §8's `arrRecUnroll_denoteScalar`. -/
theorem schedUnroll_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) :
    (count i : Nat) → 16 ≤ i →
    (ρ : String → Option (BitVec 32)) →
    (∀ k, 16 ≤ k → k < i → ρ (wName k) = some (schedFold (inpGet I) (i - 16) k)) →
    16 ≤ i - 1 ∨ 0 < count →
    ImpExpr.denoteScalar ["w"] I (schedUnroll count i) ρ
      = some (schedFold (inpGet I) (i - 16 + count) (i + count - 1))
  | 0, i, hi, ρ, hρ, hret => by
      simp only [schedUnroll]
      rcases hret with hr | hr
      · rw [show ImpExpr.denoteScalar ["w"] I (.var (wName (i - 1))) ρ = ρ (wName (i - 1)) from by
              simp only [ImpExpr.denoteScalar, denoteAtomExpr,
                idxOf_arr_none (show ("w":String) ≠ wName (i - 1) from
                  (wName_ne_of_head (by decide)).symm)]]
        rw [hρ (i - 1) hr (by omega)]
        rw [show i - 16 + 0 = i - 16 from rfl, show i + 0 - 1 = i - 1 from by omega]
      · omega
  | c + 1, i, hi, ρ, hρ, _ => by
      simp only [schedUnroll]
      rw [schedStep_denote I i hi ρ (schedUnroll c (i + 1)) hρ]
      -- the new env extends the invariant to `i + 1` (write at `i` is the step
      -- value; earlier `wName k` survive, the σ-temps are disjoint from `wName`).
      have hnew : ∀ k, 16 ≤ k → k < i + 1 →
          (fun y => if y = wName i then some (schedFold (inpGet I) (i - 16 + 1) i)
                    else (fun y' => if y' = "s1" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)))
                          else if y' = "sa" then some ((schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 7 ^^^ (schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 18)
                          else if y' = "sc" then some ((schedFold (inpGet I) (i - 16) (i - 15)) >>> (3:Nat))
                          else if y' = "sb" then some ((schedFold (inpGet I) (i - 16) (i - 15)).rotateRight 18)
                          else if y' = "s0" then some (sigma0Fn (schedFold (inpGet I) (i - 16) (i - 15)))
                          else if y' = "t1" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)) + schedFold (inpGet I) (i - 16) (i - 7))
                          else if y' = "t2" then some (sigma1Fn (schedFold (inpGet I) (i - 16) (i - 2)) + schedFold (inpGet I) (i - 16) (i - 7) + sigma0Fn (schedFold (inpGet I) (i - 16) (i - 15)))
                          else ρ y') y) (wName k)
            = some (schedFold (inpGet I) ((i + 1) - 16) k) := by
        intro k hk1 hk2
        by_cases hki : k = i
        · subst hki
          rw [show (fun y => if y = wName k then some (schedFold (inpGet I) (k - 16 + 1) k) else _)
                  (wName k) = some (schedFold (inpGet I) (k - 16 + 1) k) from by simp]
          rw [show (k + 1) - 16 = k - 16 + 1 from by omega]
        · have hklt : k < i := by omega
          simp only [if_neg (wName_inj (by omega : k ≠ i)),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "s1"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "sa"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "sc"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "sb"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "s0"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "t1"),
            if_neg (wName_ne_of_head (by decide) : wName k ≠ "t2")]
          rw [hρ k hk1 hklt]
          have hcc : i - 16 ≤ (i + 1) - 16 := by omega
          rw [schedFold_stable (inpGet I) (i - 16) k (by omega) ((i + 1) - 16) hcc]
      rw [schedUnroll_denoteScalar I c (i + 1) (by omega) _ hnew (by left; omega)]
      rw [show (i + 1) - 16 + c = i - 16 + (c + 1) from by omega,
        show (i + 1) + c - 1 = i + (c + 1) - 1 from by omega]

/-- **The bounded σ schedule is value-preserving.** The whole-program
    `schedProgram N` denotes (under `denoteScalar`, the empty env) to the
    `schedFold` array-state meaning: the final element `W[N-1]` of the FIPS 180-4
    message-schedule recurrence seeded from the 16 input words. Specialises
    `schedUnroll_denoteScalar` at the initial state (no locals yet; the invariant
    holds vacuously since `i = 16` means no `16 ≤ k < 16`). Requires `16 < N`
    (`hlt`) so at least one write happens and the returned slot is in range. The §9
    analogue of §8's `arrRecProgram_denoteScalar`. -/
theorem schedProgram_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 32) (N : Nat)
    (hlt : 16 < N) :
    ImpExpr.denoteScalar ["w"] I (schedProgram N) (fun _ => none)
      = some (schedFold (inpGet I) (N - 16) (N - 1)) := by
  rw [schedProgram,
    schedUnroll_denoteScalar I (N - 16) 16 (le_refl 16) (fun _ => none)
      (by intro k hk1 hk2; omega)
      (by right; omega)]
  rw [show 16 - 16 + (N - 16) = N - 16 from by omega,
    show 16 + (N - 16) - 1 = N - 1 from by omega]

/-! ## §10  Verbatim extraction: width-suffixed heads + ANF-lift pre-pass

§3–§9 consume `ImpExpr`s that are already let-normalized with bare operator
heads and atom arguments. A **verbatim** hax extraction (taken as-is from the
`*_impExpr` literals in `…/Extraction/Sha256_haxpipe.lean`) differs in two ways
the §3 translator rejects:

* **Width-suffixed heads.** Operator heads carry a `#<width>` tag:
  `BitXor#32`, `rotate_right#32`, `Shr#32`, `wrapping_add#32`, … (the
  `core::ops`-trait twins with the working width pinned). `recogBin`/`recogShift`
  only know the bare heads.
* **Nested-app arguments.** Args are general subexpressions, e.g.
  `BitXor#32[ BitXor#32[ rotate_right#32[x,7], rotate_right#32[x,18] ], Shr#32[x,3] ]`
  — a `BitXor#32[…]` (a non-atom) sits where §3 requires an atom.

This section closes both, **additively** (no §1–§9 decl is changed). The fix is a
single source-to-source normalization `anfLift : ImpExpr → ImpExpr` run *before*
`impExprToThir`, which (a) rewrites each head through `stripWidthSuffix` to its
bare form and (b) flattens every nested-app argument into a fresh `letBind`.
Its output lands in exactly the §3 let-normalized atom-arg subset, so the
unchanged §3 translator and its preservation theorem apply verbatim. The
recognizers are therefore left untouched (avoiding any churn to the §5–§9
`simp`-reductions that pin the bare heads); width-tagged heads are handled
*equivalently* because `anfLift` has already mapped them to bare form by the time
a recognizer sees them.

### Supported shape

`anfLift` is scoped to the **nested scalar-ARX fragment** the σ-family leaves
inhabit: `letBind`, `var`, `lit`, and `app f args` where `f` is a width-tagged or
bare ALU/shift/rotate head and each arg is itself in the fragment (an atom, an
`index[…]` read, or a nested ALU/shift/rotate app). Index reads (`app "index" …`)
are left inline (they are already atoms via `indexAtom?`). Everything else is
returned unchanged. It is driven by a `Nat` fuel bound (100, ample for the σ
leaves); on the fixed closed extraction literals it reduces by `rfl`.

This already unlocks the whole SHA-256 ARX σ-family verbatim — `small_sigma0`,
`small_sigma1`, `big_sigma0`, `big_sigma1`, and `maj` (`BitAnd`/`BitXor`) all
`anfLift`-compile. It does **not** cover a `Not[·]` operand as a hoisted RHS
(`ch`): that is the orthogonal `rhsOf`-has-no-NOT-`Rhs` limitation, not an
`anfLift` gap. -/

/-- Drop an unsigned width tag from an ALU/shift/rotate head, mapping the
    capitalized shift twins `Shr`/`Shl`/`Sar` to the lowercase `shr`/`shl`/`sar`
    the recognizers consume.

    The tagged forms covered are the bare-width `#8`/`#16`/`#32`/`#64`/`#size`
    and the explicitly-unsigned `#u8`/`#u16`/`#u32`/`#u64`/`#usize` twins of each
    ALU/shift/rotate head. Three classes pass through unchanged: bare heads,
    heads carrying a signed tag (`isSignedHead`), and `cast` heads of any tag.
    The recognizers key on bare unsigned heads, so leaving a signed or `cast`
    head tagged is what makes the front reject it rather than read it as its
    unsigned same-width twin — the front has a single register width `w`, at
    which `Rhs.cast` is `BitVec.zeroExtend w`, the identity, so a `cast#w'` with
    `w' ≠ w` has no sound bare image.

    The table is a literal-`if` chain over full head names, with no `String`
    decomposition or concatenation. `String.endsWith`, `String.dropRight` and
    `String.splitOn` have unexposed bodies in a module and do not reduce at all,
    so the downstream recognizer pins — which reduce this rewrite by `rfl` and by
    `simp [String.reduceEq]` — would not close over them; `String.append` on
    literals reduces, at about a millisecond per application. A decomposition on
    `#` would also mangle the non-width `#` heads a hax extraction emits, such as
    `struct_update#Xof#0#3`. The width-32 forms are tested first because a kernel
    `String`-literal comparison costs a few milliseconds. -/
def stripWidthSuffix (f : String) : String :=
  if f = "Shr#32" then "shr"
  else if f = "Shr#16" then "shr"
  else if f = "Shl#32" then "shl"
  else if f = "BitXor#32" then "BitXor"
  else if f = "BitAnd#32" then "BitAnd"
  else if f = "BitOr#32" then "BitOr"
  else if f = "Not#32" then "Not"
  else if f = "rotate_right#32" then "rotate_right"
  else if f = "wrapping_add#32" then "wrapping_add"
  else if f = "wrapping_mul#32" then "wrapping_mul"
  else if f = "wrapping_sub#32" then "wrapping_sub"
  else if f = "Shr#64" ∨ f = "Shr#8" ∨ f = "Shr#size" ∨ f = "Shr#u32" ∨
     f = "Shr#u64" ∨ f = "Shr#u16" ∨ f = "Shr#u8" ∨ f = "Shr#usize" then "shr"
  else if f = "Shl#64" ∨ f = "Shl#16" ∨ f = "Shl#8" ∨ f = "Shl#size" ∨ f = "Shl#u32" ∨
     f = "Shl#u64" ∨ f = "Shl#u16" ∨ f = "Shl#u8" ∨ f = "Shl#usize" then "shl"
  else if f = "BitXor#64" ∨ f = "BitXor#16" ∨ f = "BitXor#8" ∨ f = "BitXor#size" ∨
     f = "BitXor#u32" ∨ f = "BitXor#u64" ∨ f = "BitXor#u16" ∨ f = "BitXor#u8" ∨
     f = "BitXor#usize" then "BitXor"
  else if f = "BitAnd#64" ∨ f = "BitAnd#16" ∨ f = "BitAnd#8" ∨ f = "BitAnd#size" ∨
     f = "BitAnd#u32" ∨ f = "BitAnd#u64" ∨ f = "BitAnd#u16" ∨ f = "BitAnd#u8" ∨
     f = "BitAnd#usize" then "BitAnd"
  else if f = "BitOr#64" ∨ f = "BitOr#16" ∨ f = "BitOr#8" ∨ f = "BitOr#size" ∨
     f = "BitOr#u32" ∨ f = "BitOr#u64" ∨ f = "BitOr#u16" ∨ f = "BitOr#u8" ∨
     f = "BitOr#usize" then "BitOr"
  else if f = "rotate_right#64" ∨ f = "rotate_right#16" ∨ f = "rotate_right#8" ∨
     f = "rotate_right#size" ∨ f = "rotate_right#u32" ∨ f = "rotate_right#u64" ∨
     f = "rotate_right#u16" ∨ f = "rotate_right#u8" ∨ f = "rotate_right#usize" then
    "rotate_right"
  else if f = "rotate_left#32" ∨ f = "rotate_left#64" ∨ f = "rotate_left#16" ∨
     f = "rotate_left#8" ∨ f = "rotate_left#size" ∨ f = "rotate_left#u32" ∨
     f = "rotate_left#u64" ∨ f = "rotate_left#u16" ∨ f = "rotate_left#u8" ∨
     f = "rotate_left#usize" then "rotate_left"
  else if f = "wrapping_add#64" ∨ f = "wrapping_add#16" ∨ f = "wrapping_add#8" ∨
     f = "wrapping_add#size" ∨ f = "wrapping_add#u32" ∨ f = "wrapping_add#u64" ∨
     f = "wrapping_add#u16" ∨ f = "wrapping_add#u8" ∨ f = "wrapping_add#usize" then
    "wrapping_add"
  else if f = "wrapping_mul#64" ∨ f = "wrapping_mul#16" ∨ f = "wrapping_mul#8" ∨
     f = "wrapping_mul#size" ∨ f = "wrapping_mul#u32" ∨ f = "wrapping_mul#u64" ∨
     f = "wrapping_mul#u16" ∨ f = "wrapping_mul#u8" ∨ f = "wrapping_mul#usize" then
    "wrapping_mul"
  else if f = "wrapping_sub#64" ∨ f = "wrapping_sub#16" ∨ f = "wrapping_sub#8" ∨
     f = "wrapping_sub#size" ∨ f = "wrapping_sub#u32" ∨ f = "wrapping_sub#u64" ∨
     f = "wrapping_sub#u16" ∨ f = "wrapping_sub#u8" ∨ f = "wrapping_sub#usize" then
    "wrapping_sub"
  else if f = "Not#64" ∨ f = "Not#16" ∨ f = "Not#8" ∨ f = "Not#size" ∨
     f = "Not#u32" ∨ f = "Not#u64" ∨ f = "Not#u16" ∨ f = "Not#u8" ∨
     f = "Not#usize" then "Not"
  else if f = "BitNot#32" ∨ f = "BitNot#64" ∨ f = "BitNot#16" ∨ f = "BitNot#8" ∨
     f = "BitNot#size" ∨ f = "BitNot#u32" ∨ f = "BitNot#u64" ∨ f = "BitNot#u16" ∨
     f = "BitNot#u8" ∨ f = "BitNot#usize" then "BitNot"
  else if f = "Sar#32" ∨ f = "Sar#64" ∨ f = "Sar#16" ∨ f = "Sar#8" ∨ f = "Sar#size" ∨
     f = "Sar#u32" ∨ f = "Sar#u64" ∨ f = "Sar#u16" ∨ f = "Sar#u8" ∨
     f = "Sar#usize" then "sar"
  else f

/-- Whether an operator head carries a **signed** width tag (`#i8`/`#i16`/`#i32`/
    `#i64`/`#isize`), or is a `cast` head of any tag. `stripWidthSuffix` leaves
    both classes tagged, so the recognizers reject them; this predicate names the
    rejection reason. A signed operation's meaning is not its unsigned twin's at
    the front's single unsigned register width, and a `cast#w'` is the identity
    only when `w'` is that width. -/
def isSignedHead (f : String) : Bool :=
  f = "Shr#i8" ∨ f = "Shr#i16" ∨ f = "Shr#i32" ∨ f = "Shr#i64" ∨ f = "Shr#isize" ∨
  f = "Shl#i8" ∨ f = "Shl#i16" ∨ f = "Shl#i32" ∨ f = "Shl#i64" ∨ f = "Shl#isize" ∨
  f = "Sar#i8" ∨ f = "Sar#i16" ∨ f = "Sar#i32" ∨ f = "Sar#i64" ∨ f = "Sar#isize" ∨
  f = "BitXor#i8" ∨ f = "BitXor#i16" ∨ f = "BitXor#i32" ∨ f = "BitXor#i64" ∨
  f = "BitAnd#i8" ∨ f = "BitAnd#i16" ∨ f = "BitAnd#i32" ∨ f = "BitAnd#i64" ∨
  f = "BitOr#i8" ∨ f = "BitOr#i16" ∨ f = "BitOr#i32" ∨ f = "BitOr#i64" ∨
  f = "Rem#i8" ∨ f = "Rem#i16" ∨ f = "Rem#i32" ∨ f = "Rem#i64" ∨
  f = "Div#i8" ∨ f = "Div#i16" ∨ f = "Div#i32" ∨ f = "Div#i64" ∨
  f = "wrapping_add#i8" ∨ f = "wrapping_add#i16" ∨ f = "wrapping_add#i32" ∨
  f = "wrapping_add#i64" ∨
  f = "wrapping_mul#i8" ∨ f = "wrapping_mul#i16" ∨ f = "wrapping_mul#i32" ∨
  f = "wrapping_mul#i64" ∨
  f = "wrapping_sub#i8" ∨ f = "wrapping_sub#i16" ∨ f = "wrapping_sub#i32" ∨
  f = "wrapping_sub#i64" ∨
  f = "cast#8" ∨ f = "cast#16" ∨ f = "cast#32" ∨ f = "cast#64" ∨
  f = "cast#u8" ∨ f = "cast#u16" ∨ f = "cast#u32" ∨ f = "cast#u64" ∨
  f = "cast#i8" ∨ f = "cast#i16" ∨ f = "cast#i32" ∨ f = "cast#i64" ∨
  f = "cast#size" ∨ f = "cast#usize" ∨ f = "cast#isize"

/-! Static checks on the two head tables: the width-64 unsigned heads reach their
bare form, and the `cast` and signed-tagged heads do not. A head that stops being
stripped turns a compiling front into a rejecting one with no other local
signal. -/

example : stripWidthSuffix "Shr#64" = "shr" := rfl
example : stripWidthSuffix "Shl#64" = "shl" := rfl
example : stripWidthSuffix "BitAnd#64" = "BitAnd" := rfl
example : stripWidthSuffix "wrapping_add#64" = "wrapping_add" := rfl
example : stripWidthSuffix "cast#64" = "cast#64" := rfl
example : stripWidthSuffix "Shr#i32" = "Shr#i32" := rfl
example : isSignedHead "Rem#i64" = true := rfl
example : isSignedHead "cast#i32" = true := rfl
example : isSignedHead "Shr#32" = false := rfl

/-- Fresh hoisting-temporary name `_anf<n>`. Disjoint from real source names (no
    real binder starts with `_anf`) and from the σ-block scratch (`s`/`t`/`W…`). -/
def anfName (n : Nat) : String := "_anf" ++ toString n

/-! ANF-normalize an `ImpExpr` (fuel-bounded): `anfVal` head-normalizes via
`stripWidthSuffix` and hoists nested-app arguments into fresh `letBind`s,
returning `(next counter, a wrapper prepending the hoisted lets, the value-expr
with atom arguments)`. `anfArgs` walks the argument list, leaving atoms and
`index[…]` reads inline and hoisting every other arg through a fresh `_anf<n>`
binder. -/
mutual
/-- Head-normalize + hoist nested-app args of a single value-expr (see the
    section note). -/
def anfVal : Nat → Nat → ImpExpr → (Nat × (ImpExpr → ImpExpr) × ImpExpr)
  | 0, n, e => (n, id, e)
  | _ + 1, n, .var x => (n, id, .var x)
  | _ + 1, n, .lit l => (n, id, .lit l)
  | fuel + 1, n, .app f args =>
      match anfArgs fuel n args with
      | (n', wrap, args') => (n', wrap, .app (stripWidthSuffix f) args')
  | _ + 1, n, e => (n, id, e)
/-- ANF a list of arguments: atoms and `index[…]` reads stay inline; every other
    arg is recursively `anfVal`-normalized and hoisted to a fresh `_anf<n>`. -/
def anfArgs : Nat → Nat → List ImpExpr → (Nat × (ImpExpr → ImpExpr) × List ImpExpr)
  | _, n, [] => (n, id, [])
  | fuel, n, (.var x) :: rest =>
      match anfArgs fuel n rest with
      | (n1, w1, r1) => (n1, w1, (.var x) :: r1)
  | fuel, n, (.lit l) :: rest =>
      match anfArgs fuel n rest with
      | (n1, w1, r1) => (n1, w1, (.lit l) :: r1)
  | fuel, n, (.app "index" ia) :: rest =>
      match anfArgs fuel n rest with
      | (n1, w1, r1) => (n1, w1, (.app "index" ia) :: r1)
  | fuel, n, a :: rest =>
      match anfArgs fuel n rest with
      | (n1, w1, r1) =>
        match anfVal fuel n1 a with
        | (n2, wA, aVal) =>
          (n2 + 1, fun body => wA (.letBind (anfName n2) aVal (w1 body)),
           (.var (anfName n2)) :: r1)
end

/-- The verbatim-extraction pre-pass: head-normalize + flatten nested args into a
    let-chain. A `letBind` is structural (its leading `let x = x` self-binding and
    the body both recurse); a value `app` is ANF-lifted via `anfVal` (fuel `100`)
    and its hoisted lets prepended; everything else passes through. The output is
    in the §3 let-normalized atom-arg subset, so `impExprToThir`/`compileFromHax`
    consume it directly. -/
def anfLift : ImpExpr → ImpExpr
  | .letBind x v body => .letBind x (anfLift v) (anfLift body)
  | .app f args =>
      match anfVal 100 0 (.app f args) with
      | (_, wrap, v) => wrap v
  | e => e

/-! ## §11  Function-call inlining pre-pass (whole-function verbatim front)

§10's `anfLift` consumes a *single* function body whose operator heads are all
recognised ALU/shift/rotate primitives. A real whole-function hax extraction —
e.g. `sha256_compress` — instead **calls helper functions**: its schedule loop
contains `small_sigma1(index[w, Sub[i,2]])`, `small_sigma0(index[w, Sub[i,15]])`,
its round loop `big_sigma0(a)`, `ch(e,f,g)`, `maj(a,b,c)`. The §3 translator (and
§10's `anfLift`) treat such a call head `small_sigma0` as an *unknown operator*
(`recogBin`/`recogShift`/`stripWidthSuffix` leave it alone) and so reject the body.

This section adds the missing **call-handling pre-pass**: a source-to-source
`callInline` that, given a registry of callee definitions (`params, body`),
replaces each recognised call `app f args` by the callee `body` with its formal
`params` substituted by the (themselves inlined) actual `args`. Run *before*
`anfLift`/`impExprToThir`, it turns a body that *calls* `small_sigma0` into one
that *contains* `small_sigma0`'s verbatim extracted body inline — which §10 then
ANF-lifts and §3 compiles. This is the machinery whole-function verbatim
compress needs (inline `small_sigma0`/`small_sigma1`/`big_sigma0`/`big_sigma1`/
`ch`/`maj`, then compose with the §7/§8/§9 unrollers).

The substitution `substVars` is **shadowing-respecting** (it does not substitute a
free `var` under a `letBind` that rebinds the same name) — adequate for our
ANF/let-normalized callee bodies, whose formal parameters are distinct names. Full
α-renaming hygiene is not needed for the bounded demo. `callInline` is fuel-bounded
like §10's `anfLift`. The preservation statement is callee-specific (the
inlined `#32`-tagged body has no `denoteScalar` of its own until `anfLift`), so it
is proved in the demo file `CompileFromHaxCall.lean`; here we supply the computable
defs plus the cleanly-general structural equations the demo's `rfl`-reduction uses. -/

/-- A callee registry: a function name maps to its `(formal params, body)`
    definition, or `none` if it is not an inlinable call (a recognised ALU/shift
    primitive, or unknown). -/
abbrev CallRegistry := String → Option (List String × ImpExpr)

/-- Build the parameter→argument substitution for a call: formal `params` paired
    positionally with actual `args`, looked up by name. (A later/shadowing binder
    of the same formal name is handled by `substVars`'s `letBind` arm, not here.) -/
def mkSubst (params : List String) (args : List ImpExpr) : String → Option ImpExpr :=
  fun y =>
    match (params.zip args).find? (fun p => p.1 == y) with
    | some (_, e) => some e
    | none => none

/-! Capture-avoiding-enough substitution of free `var`s by `ImpExpr`s. A `var x`
with `σ x = some e` becomes `e`; a `letBind x …` that rebinds `x` drops `x` from
`σ` in its body (respecting shadowing); `app`/`seq` recurse structurally; every
other constructor passes through (the bounded scalar/let-normalized fragment
never reaches them). -/
mutual
/-- Substitute free `var`s by `ImpExpr`s (shadowing-respecting; see section note). -/
def substVars (σ : String → Option ImpExpr) : ImpExpr → ImpExpr
  | .var x => match σ x with | some e => e | none => .var x
  | .lit l => .lit l
  | .letBind x v body =>
      .letBind x (substVars σ v) (substVars (fun y => if y = x then none else σ y) body)
  | .app f args => .app f (substVarsList σ args)
  | .seq e1 e2 => .seq (substVars σ e1) (substVars σ e2)
  | e => e
/-- Map `substVars` over an argument list. -/
def substVarsList (σ : String → Option ImpExpr) : List ImpExpr → List ImpExpr
  | [] => []
  | a :: rest => substVars σ a :: substVarsList σ rest
end

/-! The call-inlining pre-pass (fuel-bounded). Walks the body; at a call
`app f args` with `reg f = some (params, body)` and matching arity, replaces it by
`body` with each formal `params[i]` substituted by the (recursively inlined)
actual `args[i]`. Recognised ALU/shift heads (`reg f = none`) and every other
constructor recurse/pass through unchanged, so the output is still in the nested
scalar-ARX fragment §10's `anfLift` consumes. -/
mutual
/-- The call-inlining pre-pass (fuel-bounded; see section note). -/
def callInline (reg : CallRegistry) : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | _ + 1, .var x => .var x
  | _ + 1, .lit l => .lit l
  | fuel + 1, .letBind x v body =>
      .letBind x (callInline reg (fuel + 1) v) (callInline reg (fuel + 1) body)
  | fuel + 1, .app f args =>
      let args' := callInlineList reg fuel args
      match reg f with
      | some (params, body) =>
          if args'.length = params.length then
            substVars (mkSubst params args') body
          else .app f args'
      | none => .app f args'
  | fuel + 1, .seq e1 e2 =>
      .seq (callInline reg (fuel + 1) e1) (callInline reg (fuel + 1) e2)
  | _ + 1, e => e
/-- Inline calls inside each element of an argument list. -/
def callInlineList (reg : CallRegistry) : Nat → List ImpExpr → List ImpExpr
  | _, [] => []
  | fuel, a :: rest => callInline reg (fuel + 1) a :: callInlineList reg fuel rest
end

/-! ### §11.1  Structural equations

These are the cleanly-general `rfl`/`simp` equations the demo's `rfl`-reduction
and any future inlining proof consume. The substantive value-preservation is the
callee-specific demo theorem (see `CompileFromHaxCall.lean`): the inlined
`#32`-tagged callee body has no `denoteScalar` of its own until `anfLift`, so a
general `denoteScalar (callInline reg e) = denoteScalar e` is *false* here (just as
§10 has no general `denoteScalar (anfLift e) = denoteScalar e`). -/

/-- `substVars` hits a substituted variable. -/
theorem substVars_var_hit (σ : String → Option ImpExpr) (x : String) (e : ImpExpr)
    (h : σ x = some e) : substVars σ (.var x) = e := by
  simp only [substVars, h]

/-- `substVars` leaves an unsubstituted variable unchanged. -/
theorem substVars_var_miss (σ : String → Option ImpExpr) (x : String)
    (h : σ x = none) : substVars σ (.var x) = .var x := by
  simp only [substVars, h]

/-- `callInline` recurses structurally through `letBind`. -/
theorem callInline_letBind (reg : CallRegistry) (fuel : Nat) (x : String)
    (v body : ImpExpr) :
    callInline reg (fuel + 1) (.letBind x v body)
      = .letBind x (callInline reg (fuel + 1) v) (callInline reg (fuel + 1) body) := rfl

/-- `callInline` at a non-call head (`reg f = none`) just inlines the arguments. -/
theorem callInline_app_miss (reg : CallRegistry) (fuel : Nat) (f : String)
    (args : List ImpExpr) (h : reg f = none) :
    callInline reg (fuel + 1) (.app f args) = .app f (callInlineList reg fuel args) := by
  simp only [callInline, h]

/-- `callInline` at a recognised call (`reg f = some (params, body)`, arity matches)
    replaces it by the substituted callee body. -/
theorem callInline_app_hit (reg : CallRegistry) (fuel : Nat) (f : String)
    (args : List ImpExpr) (params : List String) (body : ImpExpr)
    (h : reg f = some (params, body))
    (hlen : (callInlineList reg fuel args).length = params.length) :
    callInline reg (fuel + 1) (.app f args)
      = substVars (mkSubst params (callInlineList reg fuel args)) body := by
  simp only [callInline, h, hlen, if_true]

/-! ## §12  Let-flatten normalization (no `letBind` as a `letBind`'s RHS)

§11's `callInline` inlines a callee body into the *RHS of a `let`*: a caller
`let r = small_sigma0(x); …` becomes
`let r = (let x = x; …σ₀-body…); …`. The §3 `rhsOf` rejects this — a `letBind`
is not a flat `Rhs`. (This is the exact non-tail-position gap the call-inline
demo documented: "Inlining the latter would land the callee's let-chain as the
RHS of `let r = …`, which the §3 `rhsOf` rejects".) Whole-function verbatim
compress needs it because calls sit in let-RHS / `array_update`-arg positions.

`letFlatten` is the source-to-source pre-pass that closes this, **additively**
(no §1–§11 decl is changed). It re-associates nested `letBind`s via the
monad/let-association law

```text
let r = (let a = e1; e2); body   ↦   let a = e1; (let r = e2; body)
```

applied repeatedly until no `letBind` appears as another `letBind`'s RHS,
recursing into all subterms (`body`, `app` args, `seq`). It is fuel-bounded
(100, ample for the σ leaves) like §10/§11. Run it *after* `anfLift` (so the
nested `app`-arg lets `anfLift` introduces are themselves hoisted out of any
enclosing let-RHS), and the output lands in the §3 flat let-normalized atom-arg
subset that `impExprToThir`/`compileFromHax` consume directly.

### Hygiene assumption

The hoisting law is value-preserving only when the hoisted inner binder `a` is
**not free in `body`** — otherwise pulling `let a = e1` outward over `body`
would capture a free `a` there. For our ANF/fresh-name pipeline this always
holds: the hoisted binders are the callee's distinct formal params and
`anfLift`'s fresh `_anf<n>` temporaries, which never recur in the *enclosing*
caller `body`. The general single-step preservation `letFlatten_swap_denote`
carries that freshness as an explicit env-coincidence-at-`a` hypothesis (the
cleanly-true general fact). A fully general `letFlatten_denoteScalar` over a
syntactic `WellScoped`/free-var predicate would need a `denoteScalar`
coincidence lemma plus freshness-preservation through the recursion; that is
heavier than the bounded deliverable, so the *whole-pass* preservation is
proved demo-specifically by the `rfl`-reduction in `CompileFromHaxLetFlatten.lean`
(exactly as §10/§11's `anfLift`/`callInline` have no general
`denoteScalar`-preservation either — their preservation statement is the
σ-family-specific `denoteScalar` of the normal form). -/

/-- The let-flatten pre-pass: re-associate nested `letBind`s so that no `letBind`
    appears as another `letBind`'s RHS. A `letBind x v body` first flattens `v`;
    if `v` flattens to a `letBind a e1 e2`, the law
    `let x = (let a = e1; e2); body ↦ let a = e1; let x = e2; body` hoists it out
    (and re-flattens, since `e1` may itself be a `letBind`); otherwise the flat
    `v'` stays in place. `app` args and `seq` recurse; `var`/`lit`/everything else
    pass through. Fuel-bounded (`100` on the σ leaves; reduces by `rfl` on the
    fixed closed pipeline). -/
def letFlatten : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | fuel + 1, .letBind x v body =>
      match letFlatten fuel v with
      | .letBind a e1 e2 =>
          letFlatten fuel (.letBind a e1 (.letBind x e2 (letFlatten fuel body)))
      | v' => .letBind x v' (letFlatten fuel body)
  | fuel + 1, .app f args => .app f (args.map (letFlatten fuel))
  | fuel + 1, .seq e1 e2 => .seq (letFlatten fuel e1) (letFlatten fuel e2)
  | _ + 1, e => e

/-! ### §12.1  Structural equations

The cleanly-general `rfl`/`simp` unfold equations a `letFlatten`-reduction
consumes. (`letFlatten`'s `letBind` arm dispatches on `letFlatten fuel v`, so
its unfold is conditioned on that value — see `letFlatten_letBind_letBind` and
`letFlatten_letBind_flat`.) -/

/-- `letFlatten` passes a `var` through unchanged. -/
theorem letFlatten_var (fuel : Nat) (x : String) :
    letFlatten (fuel + 1) (.var x) = .var x := rfl

/-- `letFlatten` passes a `lit` through unchanged. -/
theorem letFlatten_lit (fuel : Nat) (l : ImpLit) :
    letFlatten (fuel + 1) (.lit l) = .lit l := rfl

/-- `letFlatten` recurses into every `app` argument. -/
theorem letFlatten_app (fuel : Nat) (f : String) (args : List ImpExpr) :
    letFlatten (fuel + 1) (.app f args) = .app f (args.map (letFlatten fuel)) := rfl

/-- `letFlatten` recurses structurally through `seq`. -/
theorem letFlatten_seq (fuel : Nat) (e1 e2 : ImpExpr) :
    letFlatten (fuel + 1) (.seq e1 e2)
      = .seq (letFlatten fuel e1) (letFlatten fuel e2) := rfl

/-- **The key rewrite step.** When the flattened RHS is itself a `letBind a e1 e2`,
    `letFlatten` hoists it out via the let-association law (and re-flattens). -/
theorem letFlatten_letBind_letBind (fuel : Nat) (x a : String)
    (v e1 e2 body : ImpExpr) (hv : letFlatten fuel v = .letBind a e1 e2) :
    letFlatten (fuel + 1) (.letBind x v body)
      = letFlatten fuel (.letBind a e1 (.letBind x e2 (letFlatten fuel body))) := by
  simp only [letFlatten, hv]

/-! ### §12.2  Preservation of the key rewrite step

`letFlatten_swap_denote` is the general preservation fact:
the single hoisting rewrite `let r = (let a = e1; e2); body ↦
let a = e1; let r = e2; body` denotes identically, **under the freshness
side-condition** that `body`'s denotation does not depend on the hoisted slot
`a` (`hfresh` — env-coincidence at `a`). This is a true general equation on the
well-scoped fragment, proved directly by `denoteScalar`-reduction: both sides
evaluate `e1 → a`, then `e2 → r` (under the `a`-extended env), and finally
`body` — the LHS without `a` in scope, the RHS with `a = av`; `hfresh` reconciles
the two `body` envs. Unlike §10/§11's `anfLift`/`callInline` (which have *no*
general `denoteScalar`-preservation — they map non-denoting `#32`-tagged forms
into denoting ones), this rewrite is a real monad-law equation. -/

/-- **Let-flatten rewrite preservation (general, with freshness side-condition).**
    The single hoisting step `let r = (let a = e1; e2); body ↦
    let a = e1; let r = e2; body` is value-preserving whenever `body`'s denotation
    is invariant to the slot bound at `a` (the hygiene condition — `a ∉ freeVars
    body`, expressed as env-coincidence at `a`). Proved by `denoteScalar`-reduction:
    both sides bind `e1 → a` and `e2 → r` identically; `hfresh` reconciles the final
    `body` env (LHS: `a` out of scope; RHS: `a = av`). -/
theorem letFlatten_swap_denote {w nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec w) (r a : String) (e1 e2 body : ImpExpr)
    (ρ : String → Option (BitVec w))
    (hfresh : ∀ (ρ' : String → Option (BitVec w)) (va rv : BitVec w),
        ImpExpr.denoteScalar params I body
            (fun y => if y = r then some rv else if y = a then some va else ρ' y)
          = ImpExpr.denoteScalar params I body
            (fun y => if y = r then some rv else ρ' y)) :
    ImpExpr.denoteScalar params I (.letBind r (.letBind a e1 e2) body) ρ
      = ImpExpr.denoteScalar params I (.letBind a e1 (.letBind r e2 body)) ρ := by
  simp only [ImpExpr.denoteScalar]
  cases he1 : ImpExpr.denoteScalar params I e1 ρ with
  | none => simp [Option.bind]
  | some av =>
    simp only [Option.bind_some]
    cases he2 : ImpExpr.denoteScalar params I e2
        (fun y => if y = a then some av else ρ y) with
    | none => simp [Option.bind]
    | some rv =>
      simp only [Option.bind_some]
      rw [hfresh ρ av rv]

end CatCrypt.Crypto.SecureCompilation.ImpExprToThir
