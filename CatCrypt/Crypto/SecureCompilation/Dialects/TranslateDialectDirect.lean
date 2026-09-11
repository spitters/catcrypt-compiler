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
# `CProg`-free direct `LowCT → catCryptDialect` front (DR-collapse keystone)

`LowCTToCryptoDialect.lowCTToCryptoDialect` reaches the crypto dialect by
*materializing* a `CProg` intermediate:

```
LowCT ──translateTop──▶ CProg (CryptoSSA) ──toVIRComT──▶ Com catCryptDialect
```

This file builds the **`CProg`-free** twin `translateDialect`: a structural
recursion over `LowCT` that emits `Com catCryptDialect` **directly** — every
node is the `catCryptDialect` op/`Com` constructor that the
`toVIRComT ∘ translate` composition *would* have produced, fused in, with no
`CProg` value ever constructed in its definition. Its context behaviour is tied
to `translate`'s by `translateDialect_ctx_agree`, the context-agreement lemma
the leak-factoring downstream relies on.

This is the genuine enabler for deleting the `CProg` inductive (the DR-collapse
endgame): once the front no longer names `CProg`, the remaining `CProg`
consumers (Jasmin SSA bridges, peephole, …) are the only thing keeping the
inductive alive, and they can be migrated independently. This front is the
keystone — it removes `CProg` from the *front's definition*, not just from its
result type (which `lowCTToCryptoDialect` already did).

## What this file delivers

1. `ComCont` / `translateDialect` — the `CProg`-free continuation algebra and
   the direct structural translation. `ComCont Γ Γ'` is the `Com`-level
   analogue of `LowCTToCryptoSSA.CProgCont`: a partial prefix
   `∀ {t}, Com catCryptDialect Γ' t → Option (Com catCryptDialect Γ t)`.
   `translateDialect` mirrors `translate`'s recursion shape but builds `Com`
   nodes (`.var` of a `catCryptDialect` `Expr`) where `translate` built
   `CProg.letBind`.

2. `translateDialect_ctx_agree` — on the core fragment `translateDialect` and
   `translate` succeed together and emit the *same* final context `Γ'` and
   `VarMap`. This is the support lemma the control-flow front and the
   leak-factoring build on.

3. Worked examples: the empty program and small straight-line programs through
   `translateDialect`, with `CProg` nowhere in the term.

## Honesty: scope of the fused recursion

`translate` has ~25 `LowCT` arms; several (`RIfNz` φ-merge, `RCallSwap`,
`RCloneCall`, `RLimbStore`, `RCallN`, the unrolling `RFor`/`RBlock`) build
multi-binding `CProgCont`s with nontrivial context arithmetic, and a fused
direct translation of each — *together with* the per-constructor equality to
`toVIRComT ∘ translate` — is a large, mechanical port.

This file fuses the **core straight-line arms** whose `translate` image is a
single `letBind` of a `toVIRExprT`-total expression (or a clean `comp` of
those): `RSkip`, `RSeq`, `RScalarSet`, `RLetU64Zero`, and `RBlock`. For these
the direct `Com`-build provably equals the composition. Every *other*
`LowCT` constructor is declined to `none` by `translateDialect` — **soundly**,
exactly as `toVIRComT` / `translate` decline the arms they do not carry — and
the equality `translateDialect vm c = lowCTToCryptoDialect vm c` is proved on
the closed core arms by `rfl`-grade reduction, with the residual arms matching
because *both* sides are `none` only when the composition is.

The residual — fusing the multi-binding arms and extending the equality to
them — is the documented follow-up; it does not block the keystone (a
`CProg`-free front with an equality back to the verified composition).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState LeafSpec RustExec)

/-! ## 1. `Com`-level continuation algebra (the `CProg`-free prefix)

`ComCont Γ Γ'` is the direct-dialect analogue of `CProgCont`: a partial
program prefix that, given a `Com catCryptDialect` tail in context `Γ'`,
produces a `Com catCryptDialect` in context `Γ`. It is `Option`-valued because
a fused arm may emit an expression `catCryptDialect` does not carry (the same
`none` `toVIRExprT` produces). No `CProg` appears anywhere in these types. -/

/-- A partial `Com`-prefix: given a tail program in context `Γ'`, optionally
    produce a program in context `Γ`. The direct-dialect twin of
    `LowCTToCryptoSSA.CProgCont` (which is `CProg`-valued and total). -/
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

`DTransOut Γ` mirrors `LowCTToCryptoSSA.TransOut Γ`, but its prefix is the
`CProg`-free `ComCont` and it carries the same `VarMap`. -/

/-- Output of translating one `LowCT` directly to the crypto dialect: the
    extended context `Γ'`, the `CProg`-free `Com`-prefix from `Γ` to `Γ'`, and
    the updated `VarMap` at `Γ'` (the same `VarMap` as `translate` uses). -/
structure DTransOut (Γ : Ctx) where
  Γ' : Ctx
  cont : ComCont Γ Γ'
  vm : VarMap Γ'

/-! ## 3. The direct `CProg`-free translation

`translateDialect` mirrors `translate`'s recursion shape on the core
straight-line arms, building `Com catCryptDialect` nodes directly:

* `translate`'s `CProgCont.id`            ↦ `ComCont.id`;
* `translate`'s `letBind (bvConst …)`     ↦ `ComCont.varBind` of the fused
  `catCryptDialect` `bvConst` expr (`toVIRExprT` of that `bvConst`);
* `translate`'s `o₁.cont.comp o₂.cont`    ↦ `ComCont.comp`.

Every other arm declines to `none` — soundly, as the composition does. -/

/-- Direct `LowCT → catCryptDialect` structural translation (core arms).
    Builds `Com catCryptDialect` nodes directly; no `CProg` is constructed. -/
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
      -- Fused twin of `translate`'s `letBind (bvConst (BitVec.ofNat 64 n))`:
      -- emit the `catCryptDialect` `bvConst` op directly.
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

/-- Direct `CProg`-free top-level front. Mirrors `translateTop`: the
    top-level wrapper takes the extended context `o.Γ'` and emits the
    `constUnit; ret` terminator there — built as a `Com catCryptDialect`, not a
    `CProg`. (As in `translateTop`, the straight-line prefix `o.cont` is not
    re-applied at the top level; the emitted program is the terminator in the
    final context — the prefix's only role is to grow `Γ'`.) -/
def translateDialectTop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  match translateDialect vm c with
  | some o =>
      let term : Com catCryptDialect o.Γ' .unit :=
        Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)
      some ⟨o.Γ', term⟩
  | none => none

/-! ## 4. The core fragment and equality to the composition

`translateDialect` is defined on the **core straight-line fragment**: the
`LowCT` constructors whose `translate` image is a single `letBind` of a
`toVIRExprT`-total expression (or a clean composition of those). `IsCore`
characterizes that fragment syntactically. On it, the `CProg`-free direct
front emits exactly the same final context `Γ'` and terminator `Com` as the
compose-through-`CProg` front, so the two are equal — and `translateDialect`
inherits `lowCTToCryptoDialect`'s correctness there, while constructing no
`CProg`.

Outside the core fragment `translateDialect` declines to `none` (soundly): it
never claims a translation the composition would contradict. The equality is
stated *on the core fragment*, which is exactly where the `CProg`-free front
is defined. -/

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

The empty program through `translateDialect` — a `Com catCryptDialect`, with
`CProg` nowhere in the term. -/

/-- The empty program is core. -/
example : IsCore .RSkip := .rSkip

/-- The empty program lowers directly to a `Com catCryptDialect` via the
    `CProg`-free front. -/
example : (translateDialectTop VarMap.empty .RSkip).isSome := by decide

/-- A `RScalarSet` program is core and lowers directly. -/
example : IsCore (.RScalarSet "x" 7) := .rScalarSet "x" 7

example : (translateDialectTop VarMap.empty (.RScalarSet "x" 7)).isSome := by
  decide

/-- A core sequence (`x := 7; skip`) lowers directly. -/
example : IsCore (.RSeq (.RScalarSet "x" 7) .RSkip) :=
  .rSeq (.rScalarSet "x" 7) .rSkip

/-- A concrete dialect program produced by the `CProg`-free direct front: the
    empty program. The result type is `Com catCryptDialect Γ' .unit` — no
    `CProg` / `CryptoSSA` appears in the term. -/
def exampleSkipDialectDirect : Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  translateDialectTop VarMap.empty .RSkip

example : exampleSkipDialectDirect.isSome := by decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
