/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSTotalCtl

/-!
# A hax contract discharged from the ascent

For a Rust function `f` carrying `#[hax_lib::requires(φ)]` and `#[hax_lib::ensures(|r| ψ)]`,
the Lean printer of hax emits, beside `f`, a declaration `f.spec` of the structure `Spec`
of the module `Hax.Rust_primitives.Spec` of the hax-lib Lean proof library:

```
structure Spec {α}
    (requires : RustM Prop)
    (ensures : α → RustM Prop)
    (f : RustM α) where
  pureRequires : {p : Prop // ⦃ ⌜ True ⌝ ⦄ requires ⦃ ⇓r => ⌜ r = p ⌝ ⦄}
  pureEnsures : {p : α → Prop // pureRequires.val → ∀ a, ⦃ ⌜ True ⌝ ⦄ ensures a ⦃ ⇓r => ⌜ r = p a ⌝ ⦄}
  contract : ⦃ ⌜ pureRequires.val ⌝ ⦄ f ⦃ ⇓r => ⌜ pureEnsures.val r ⌝ ⦄
```

with the default proofs `by constructor; mvcgen <;> try grind` of the two pure fields and
`by mvcgen[f] <;> try grind` of `contract`. The hax-lib proof library is not a dependency of
this workspace, and its `RustM` is `ExceptT Error Option`, while the reading `toRustMS`
returns in `Aeneas.Std.RustM`, the monad `HaxLean/HaxBackendPrelude.lean` names `RustM`.
`Spec` below restates the upstream structure field by field over `Aeneas.Std.RustM`.

`keyEqRun` is the reading of the haxpipe literal `keyEqLit` from two Aeneas byte arrays,
and `keyEqRun.spec` is its contract in the printed form: the precondition `32 ≤ n`, the
postcondition that the returned value encodes `keyEq` of the two arrays. The pure fields
are closed by `mvcgen` as in the printed default. The `contract` field is the total triple
`keyEqLit_triple` of `ToRustMSTotalCtl`, which comes from the function correspondence
`keyEq_fnCorres` through `fnCorres_toRustMS_triple_of_kindOf`; no verification condition
is generated over the body of the reading.

## Main definitions

* `Spec`, `keyEqRun`, `keyEqRun.spec`

## Main results

* `triple_of_pure_imp`, `keyEqRun_contract`
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Hax.RustSemantics.ContractDemo

open Aeneas.Std Aeneas.Std.WP Std.Do
open Hax.Ascent Hax.Ascent.Demo

/-- The contract of a function as the hax Lean printer emits it: the structure `Spec` of
    the module `Hax.Rust_primitives.Spec` of the hax-lib Lean proof library, with the
    same fields, over `Aeneas.Std.RustM`. `requires` and `ensures` are the monadic clauses of the
    attributes; `pureRequires` and `pureEnsures` are their pure readings, and `contract`
    is the triple of `f` between them. -/
structure Spec {α : Type} («requires» : RustM Prop) («ensures» : α → RustM Prop) (f : RustM α)
    where
  /-- The proposition the precondition clause returns. -/
  pureRequires : {p : Prop // ⦃⌜True⌝⦄ «requires» ⦃⇓ r => ⌜r = p⌝⦄}
  /-- The predicate the postcondition clause returns, under the precondition. -/
  pureEnsures :
    {p : α → Prop // pureRequires.val → ∀ a, ⦃⌜True⌝⦄ «ensures» a ⦃⇓ r => ⌜r = p a⌝⦄}
  /-- The contract: from the precondition, `f` returns a value satisfying the
      postcondition. -/
  contract : ⦃⌜pureRequires.val⌝⦄ f ⦃⇓ r => ⌜pureEnsures.val r⌝⦄

/-- A triple with a pure precondition `p` from the triple with the precondition `True`
    under the hypothesis `p`. -/
theorem triple_of_pure_imp {α : Type} {x : RustM α} {p : Prop} {Q : PostCond α _}
    (h : p → ⦃⌜True⌝⦄ x ⦃Q⦄) : ⦃⌜p⌝⦄ x ⦃Q⦄ :=
  SPred.pure_elim' fun hp => h hp

/-- The reading of `keyEqLit` from two Aeneas byte arrays, as the function the contract
    is about. -/
def keyEqRun {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) : RustM (AVal × AEnv) :=
  toRustMS keyEqApp keyEqLit (keyEqEnvA x y)

/-- The contract of `keyEqRun` from the ascent: under `32 ≤ n` the returned value encodes
    `keyEq` of the two arrays, from `keyEqLit_triple`. -/
theorem keyEqRun_contract {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) :
    ⦃⌜32 ≤ n.val⌝⦄ keyEqRun x y
    ⦃⇓ r => ⌜r.1.toValue = HaxEnc.enc (keyEq (keyArr x) (keyArr y))⌝⦄ :=
  triple_of_pure_imp fun hn => keyEqLit_triple x y hn

/-- **The printed contract of `keyEqRun`.** The `Spec` declaration the hax Lean printer
    emits for `#[requires(32 <= n)]` and `#[ensures(|r| r == key_eq(x, y))]`; the pure
    fields by `mvcgen`, the `contract` field by `keyEqRun_contract`. -/
def keyEqRun.spec {n : Usize} (x y : Aeneas.Std.Array (UScalar .U8) n) :
    Spec («requires» := do pure (32 ≤ n.val))
      («ensures» := fun r => do pure (r.1.toValue = HaxEnc.enc (keyEq (keyArr x) (keyArr y))))
      (keyEqRun x y) where
  pureRequires := ⟨32 ≤ n.val, by mvcgen⟩
  pureEnsures := ⟨fun r => r.1.toValue = HaxEnc.enc (keyEq (keyArr x) (keyArr y)),
    fun _ _ => by mvcgen⟩
  contract := keyEqRun_contract x y

end CatCrypt.Hax.RustSemantics.ContractDemo
