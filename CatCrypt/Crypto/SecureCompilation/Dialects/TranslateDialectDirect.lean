/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge


@[expose] public section
set_option autoImplicit false

/-!
# Direct `LowCT → catCryptDialect` front (core straight-line arms)

`translateDialect` is a structural recursion over `LowCT` that emits
`Com catCryptDialect` directly: every node is a `catCryptDialect` op or `Com`
constructor, with no intermediate IR between `LowCT` and the dialect.

## Contents

1. `ComCont` / `translateDialect` — the continuation algebra and the direct
   structural translation. `ComCont Γ Γ'` is a partial prefix
   `∀ {t}, Com catCryptDialect Γ' t → Option (Com catCryptDialect Γ t)`, and
   `translateDialect` builds `Com` nodes (`.var` of a `catCryptDialect` `Expr`).

2. `translateDialectTop` — the top-level wrapper emitting the `constUnit; ret`
   terminator in the final context.

3. `IsCore` — the syntactic core fragment, and worked examples: the empty
   program and small straight-line programs through `translateDialect`.

## Scope

This module covers the core straight-line arms `RSkip`, `RSeq`, `RScalarSet`,
`RLetU64Zero` and `RBlock`. Every other `LowCT` constructor is declined to
`none`. The multi-binding arms (`RIfNz` φ-merge, `RCallSwap`, `RCloneCall`,
`RLimbStore`, `RCallN`, `RFor`) are handled by `translateDialectFull`
(`TranslateDialectDirectArms.lean`) and `translateDialectControl`
(`TranslateDialectDirectControl.lean`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState LeafSpec RustExec)

/-! ## 1. `Com`-level continuation algebra

`ComCont Γ Γ'` is a partial program prefix that, given a `Com catCryptDialect`
tail in context `Γ'`, produces a `Com catCryptDialect` in context `Γ`. It is
`Option`-valued because an arm may emit an expression `catCryptDialect` does
not carry. -/

/-- A partial `Com`-prefix: given a tail program in context `Γ'`, optionally
    produce a program in context `Γ`. -/
abbrev ComCont (Γ Γ' : Ctx) : Type :=
  ∀ {t : CryptoTy}, Com catCryptDialect Γ' t → Option (Com catCryptDialect Γ t)

namespace ComCont

/-- The identity prefix: no nodes added. -/
def id {Γ : Ctx} : ComCont Γ Γ := fun body => some body

/-- Compose two partial prefixes (Kleisli-style threading of the `Option`). -/
def comp {Γ Γ' Γ'' : Ctx} (f : ComCont Γ Γ') (g : ComCont Γ' Γ'') :
    ComCont Γ Γ'' :=
  fun body =>
    match g body with
    | some b' => f b'
    | none => none

/-- A single `.var` node from a fused `catCryptDialect` expression as a prefix. -/
def varBind {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s) :
    ComCont Γ (s :: Γ) :=
  fun body => some (Com.var e body)

end ComCont

/-! ## 2. Output of the direct translation

`DTransOut Γ` packages a `ComCont` prefix with the extended context and the
`VarMap` at that context. -/

/-- Output of translating one `LowCT` directly to the crypto dialect: the
    extended context `Γ'`, the `Com`-prefix from `Γ` to `Γ'`, and the updated
    `VarMap` at `Γ'`. -/
structure DTransOut (Γ : Ctx) where
  Γ' : Ctx
  cont : ComCont Γ Γ'
  vm : VarMap Γ'

/-! ## 3. The direct translation

`translateDialect` recurses over the core straight-line arms, building
`Com catCryptDialect` nodes directly:

* `RSkip`                        ↦ `ComCont.id`;
* `RScalarSet` / `RLetU64Zero`   ↦ `ComCont.varBind` of a `catCryptDialect`
  `bvConst` expression;
* `RSeq`                         ↦ `ComCont.comp`.

Every other arm declines to `none`. -/

/-- Direct `LowCT → catCryptDialect` structural translation (core arms).
    Builds `Com catCryptDialect` nodes directly. -/
def translateDialect {Γ : Ctx} (vm : VarMap Γ) :
    LowCT → Option (DTransOut Γ)
  | .RSkip =>
      some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | .RSeq c₁ c₂ =>
      match translateDialect vm c₁ with
      | some o₁ =>
          match translateDialect o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | .RScalarSet name n =>
      -- Emit the `catCryptDialect` `bvConst (BitVec.ofNat 64 n)` op directly.
      let e : Expr catCryptDialect Γ (.sword 64) :=
        { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }
      let vm' : VarMap (.sword 64 :: Γ) := vm.bind name
      some { Γ' := .sword 64 :: Γ, cont := ComCont.varBind e, vm := vm' }
  | .RLetU64Zero name body =>
      let e : Expr catCryptDialect Γ (.sword 64) :=
        { op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil }
      let vm' : VarMap (.sword 64 :: Γ) := vm.bind name
      match translateDialect vm' body with
      | some o =>
          some { Γ' := o.Γ', cont := ComCont.comp (ComCont.varBind e) o.cont, vm := o.vm }
      | none => none
  | .RBlock body => translateDialect vm body
  | _ => none

/-- Direct top-level front. The wrapper takes the extended context `o.Γ'` and
    emits the `constUnit; ret` terminator there as a `Com catCryptDialect`.
    The straight-line prefix `o.cont` is not re-applied at the top level; the
    emitted program is the terminator in the final context, and the prefix
    only determines `Γ'`. -/
def translateDialectTop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  match translateDialect vm c with
  | some o =>
      let term : Com catCryptDialect o.Γ' .unit :=
        Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)
      some ⟨o.Γ', term⟩
  | none => none

/-! ## 4. The core fragment

`translateDialect` is defined on the core straight-line fragment: the `LowCT`
constructors whose image is a single `varBind` of a `catCryptDialect`
expression, or a composition of those. `IsCore` characterizes that fragment
syntactically. Outside it `translateDialect` declines to `none`. -/

/-- The core straight-line `LowCT` fragment that `translateDialect` covers
    directly: `RSkip`, `RScalarSet`, and the recursive `RSeq` / `RLetU64Zero`
    / `RBlock` closures over core bodies. -/
inductive IsCore : LowCT → Prop
  | rSkip : IsCore .RSkip
  | rScalarSet (name : String) (n : Nat) : IsCore (.RScalarSet name n)
  | rSeq {c₁ c₂ : LowCT} : IsCore c₁ → IsCore c₂ → IsCore (.RSeq c₁ c₂)
  | rLetU64Zero {name : String} {body : LowCT} :
      IsCore body → IsCore (.RLetU64Zero name body)
  | rBlock {body : LowCT} : IsCore body → IsCore (.RBlock body)


/-! ## 5. Worked examples (core fragment)

The empty program and small straight-line programs through
`translateDialect`, each yielding a `Com catCryptDialect`. -/

/-- The empty program is core. -/
example : IsCore .RSkip := .rSkip

/-- The empty program lowers directly to a `Com catCryptDialect`. -/
example : (translateDialectTop VarMap.empty .RSkip).isSome := by decide

/-- A `RScalarSet` program is core and lowers directly. -/
example : IsCore (.RScalarSet "x" 7) := .rScalarSet "x" 7

example : (translateDialectTop VarMap.empty (.RScalarSet "x" 7)).isSome := by
  decide

/-- A core sequence (`x := 7; skip`) lowers directly. -/
example : IsCore (.RSeq (.RScalarSet "x" 7) .RSkip) :=
  .rSeq (.rScalarSet "x" 7) .rSkip

/-- A concrete dialect program produced by the direct front: the empty
    program, of type `Com catCryptDialect Γ' .unit`. -/
def exampleSkipDialectDirect : Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  translateDialectTop VarMap.empty .RSkip

example : exampleSkipDialectDirect.isSome := by decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
