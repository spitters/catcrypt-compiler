/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms


@[expose] public section
set_option autoImplicit false

/-!
# Control-flow arms of the direct front (`RIfNz`, `RFor`, `RWhileNz`)

`TranslateDialectDirectArms.translateDialectFull` lowers the core straight-line
arms plus the leaf-call multi-binding arms to a `Com catCryptDialect` recursion
on `IsCovered`. This module adds the control-flow arms, building
`Com catCryptDialect` nodes through `ComCont`:

* **`RFor x N body`** — the bounded inline unroll. `loopRForD` is a
  `Nat`-recursion that, per iteration `i ∈ [0..N)`, emits one
  `ComCont.varBind` of `bvConst (BitVec.ofNat 64 i)` then threads the body
  translation through the growing `VarMap` (same shape as
  `TranslateDialectDirectArms.loopCallNDestsD`).

* **`RIfNz name thenBr elseBr`** — the φ-merge. Both branches are translated in
  the entry context and merged by final-context shape: cases (A) (both
  non-extending) and (B) (one extends) pass through one branch's `⟨Γ', vm⟩`;
  case (C′) — both branches a `RScalarSet` on the *same* name — composes six
  `ComCont.varBind`s (`thenV; elseV; zero; cond_eq; cond_bit; merged`); case
  (C-otherwise) re-translates `elseBr` from the post-then `VarMap`.

* **`RWhileNz name body`** — the data-dependent loop, gated on the guard being
  a bound scalar and on the body front-compiling, emitting a context-invariant
  region.

* **`RLetU64Zero name body`** and **`RLetZero name tt body`** — the binders,
  handled as in `translateDialectFull` (a `bvConst 64 0` binding, and the dead
  zero-init elision) with the body translated by this front, so a binder over
  a control form is accepted.

Every other arm delegates to `translateDialectFull`.

## Covered fragment

`IsCoveredCtl` is the covered arms of `TranslateDialectDirectArms.IsCovered`
plus `RFor` over covered bodies, `RIfNz` over covered branches, `RWhileNz`
over a covered body and `RLetU64Zero` over a covered body. On `IsCovered`,
`translateDialectControl` coincides with `translateDialectFull`
(`translateDialectControl_eq_full_of_covered`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState LeafSpec RustExec Located TowerType)

/-! ## 1. The `RFor` unroll (`loopRForD`)

`loopRForD` is a `Nat`-recursion: per iteration it emits one `ComCont.varBind`
of `bvConst (BitVec.ofNat 64 i)` then threads the direct body translator. It
has the shape of `loopCallNDestsD` (whose recursion is over the destination
list); here the recursion is over `Nat`. -/

/-- The `RFor` unroll: a left-to-right `Nat`-fold of one
    `bvConst (BitVec.ofNat 64 i)` binding plus the direct body translation per
    iteration, building `ComCont` prefixes. The body translator
    `translateBody` is passed in, so this def can be used before
    `translateDialectControl` is in scope. -/
def loopRForD {Γ : Ctx}
    (translateBody : ∀ {Γ'' : Ctx}, VarMap Γ'' → Option (DTransOut Γ''))
    (vm : VarMap Γ) (x : String) :
    Nat → Option (DTransOut Γ)
  | 0 => some { Γ' := Γ, cont := ComCont.id, vm := vm }
  | n + 1 =>
      match loopRForD translateBody vm x n with
      | none => none
      | some oPre =>
          let vmAfterSet : VarMap (.sword 64 :: oPre.Γ') := oPre.vm.bind x
          let eSet : Expr catCryptDialect oPre.Γ' (.sword 64) :=
            { op := .bvConst 64 (BitVec.ofNat 64 n), retTy_eq := rfl, args := .nil }
          match translateBody vmAfterSet with
          | none => none
          | some oBody =>
              some { Γ' := oBody.Γ'
                     cont := ComCont.comp oPre.cont
                       (ComCont.comp (ComCont.varBind eSet) oBody.cont)
                     vm := oBody.vm }

/-! ## 2. The fused control-flow front `translateDialectControl`

Lowers `RSeq`, `RFor`, `RIfNz`, `RWhileNz`, `RLetU64Zero` and `RLetZero`; every
other arm delegates to `translateDialectFull`. The `RIfNz` φ-merge builds its six expressions inline
as a chain of `ComCont.varBind`s. -/

/-- Direct `LowCT → catCryptDialect` translation extended to the control-flow
    arms. Every prefix is a `ComCont`. -/
def translateDialectControl {Γ : Ctx} (vm : VarMap Γ) :
    LowCT → Option (DTransOut Γ)
  | .RFor x N body =>
      loopRForD (translateBody := fun vm' => translateDialectControl vm' body) vm x N
  | .RIfNz name thenBr elseBr =>
      match vm.lookup name with
      | some ⟨.sword w, condVar⟩ =>
          match translateDialectControl vm thenBr, translateDialectControl vm elseBr with
          | some o₁, some o₂ =>
              if _h₁ : o₁.Γ' = Γ then
                if _h₂ : o₂.Γ' = Γ then
                  some { Γ' := o₁.Γ', cont := o₁.cont, vm := o₁.vm }
                else
                  some { Γ' := o₂.Γ', cont := o₂.cont, vm := o₂.vm }
              else
                if _h₂ : o₂.Γ' = Γ then
                  some { Γ' := o₁.Γ', cont := o₁.cont, vm := o₁.vm }
                else
                  match asSingleScalarSet thenBr, asSingleScalarSet elseBr with
                  | some thenSet, some elseSet =>
                      if thenSet.name = elseSet.name then
                        -- (C′) φ-merge: build the six merge expressions.
                        let Γ₁ : Ctx := .sword 64 :: Γ
                        let Γ₂ : Ctx := .sword 64 :: Γ₁
                        let Γ₃ : Ctx := .sword w :: Γ₂
                        let Γ₄ : Ctx := .bit :: Γ₃
                        let Γ₅ : Ctx := .bit :: Γ₄
                        let Γ₆ : Ctx := .sword 64 :: Γ₅
                        let eThen : Expr catCryptDialect Γ (.sword 64) :=
                          { op := .bvConst 64 (BitVec.ofNat 64 thenSet.val),
                            retTy_eq := rfl, args := .nil }
                        let eElse : Expr catCryptDialect Γ₁ (.sword 64) :=
                          { op := .bvConst 64 (BitVec.ofNat 64 elseSet.val),
                            retTy_eq := rfl, args := .nil }
                        let eZero : Expr catCryptDialect Γ₂ (.sword w) :=
                          { op := .bvConst w (BitVec.ofNat w 0), retTy_eq := rfl, args := .nil }
                        let condVar' : CVar Γ₃ (.sword w) :=
                          .there (.there (.there condVar))
                        let zeroHere : CVar Γ₃ (.sword w) := .here
                        let eEq : Expr catCryptDialect Γ₃ .bit :=
                          { op := .bvEq w, retTy_eq := rfl,
                            args := .cons (toVIRVar condVar') (.cons (toVIRVar zeroHere) .nil) }
                        let condEqHere : CVar Γ₄ .bit := .here
                        let eNot : Expr catCryptDialect Γ₄ .bit :=
                          { op := .not, retTy_eq := rfl,
                            args := .cons (toVIRVar condEqHere) .nil }
                        let condBitHere : CVar Γ₅ .bit := .here
                        let thenV : CVar Γ₅ (.sword 64) :=
                          .there (.there (.there (.there .here)))
                        let elseV : CVar Γ₅ (.sword 64) :=
                          .there (.there (.there .here))
                        let eIte : Expr catCryptDialect Γ₅ (.sword 64) :=
                          { op := .ite (.sword 64), retTy_eq := rfl,
                            args := .cons (toVIRVar condBitHere)
                              (.cons (toVIRVar thenV) (.cons (toVIRVar elseV) .nil)) }
                        let pre : ComCont Γ Γ₆ :=
                          ComCont.comp (ComCont.varBind eThen)
                            (ComCont.comp (ComCont.varBind eElse)
                              (ComCont.comp (ComCont.varBind eZero)
                                (ComCont.comp (ComCont.varBind eEq)
                                  (ComCont.comp (ComCont.varBind eNot)
                                    (ComCont.varBind eIte)))))
                        let vm'' : VarMap Γ₆ :=
                          (((((vm.weaken (t := .sword 64)).weaken
                              (t := .sword 64)).weaken
                              (t := .sword w)).weaken
                              (t := .bit)).weaken
                              (t := .bit)).bind (t := .sword 64) thenSet.name
                        some { Γ' := Γ₆, cont := pre, vm := vm'' }
                      else
                        match translateDialectControl o₁.vm elseBr with
                        | some o₂' =>
                            some { Γ' := o₂'.Γ',
                                   cont := ComCont.comp o₁.cont o₂'.cont,
                                   vm := o₂'.vm }
                        | none => none
                  | _, _ =>
                      match translateDialectControl o₁.vm elseBr with
                      | some o₂' =>
                          some { Γ' := o₂'.Γ',
                                 cont := ComCont.comp o₁.cont o₂'.cont,
                                 vm := o₂'.vm }
                      | none => none
          | _, _ => none
      | _ => none
  | .RWhileNz name body =>
      -- A data-dependent unbounded `while (name != 0)` is accepted by the front's
      -- **context-plumbing** arm: gate on the guard `name` being a bound scalar
      -- (mirroring `RIfNz`'s `some ⟨.sword w, _⟩` lookup) and on the loop `body`
      -- front-compiling (recursively, via this same `translateDialectControl`).  The
      -- body's own `Γ'`/`vm` are **loop-local** (the trip is unknown at entry and the
      -- body may rebind the counter), so we discard them and return the
      -- context-invariant `DTransOut` (`Γ' = Γ`, `cont = ComCont.id`, `vm` unchanged)
      -- — the loop-region invariant.  The `catCryptDialect` `Com` substrate has no
      -- label/branch node, so `cont = ComCont.id` is a placeholder: the actual
      -- run-time back-edge is emitted downstream at the `Lprog`/`Lcmd` level by
      -- `TranslateDialectDataWhile.rolledWhileNz` (guard-driven `whileLinstrRM`) /
      -- `X86Backend.LprogControlFlow.whileLcmd`, which front-compiles this same
      -- `body` through `translateDialectControl`.  The front arm's sole job is the
      -- context plumbing (gate + invariant) that lets the straight-line front
      -- *accept* an `RWhileNz` node and hand the body to the loop emitter.
      match vm.lookup name with
      | some ⟨.sword _, _⟩ =>
          (translateDialectControl vm body).map
            (fun _ => { Γ' := Γ, cont := ComCont.id, vm := vm })
      | _ => none
  | .RSeq c₁ c₂ =>
      -- **Control-level `RSeq` sequencing.** Recurse into `translateDialectControl`
      -- on BOTH children (composing the two prefixes with `ComCont.comp`), rather
      -- than delegating to the straight-line `translateDialectFull` (whose `RSeq`
      -- arm recurses through `translateDialectFull`, which declines `RFor`/`RIfNz`).
      -- This closes the front under sequencing of control blocks, so a multi-phase
      -- kernel (`ladder; invert; encode`, `absorb; squeeze`, MAYO phases) descends
      -- through the canonical front. Mirrors `translateDialectControlV`'s `RSeq`
      -- arm. On a straight-line `RSeq` it agrees with the old delegation by
      -- `translateDialectControl_eq_full_of_covered` on each child.
      match translateDialectControl vm c₁ with
      | some o₁ =>
          match translateDialectControl o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | .RLetU64Zero name body =>
      -- The `RLetU64Zero` arm of `translateDialectFull`, with the body
      -- translated by this control front, so a binder whose body contains a
      -- control form is accepted.
      let e : Expr catCryptDialect Γ (.sword 64) :=
        { op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil }
      let vm' : VarMap (.sword 64 :: Γ) := vm.bind name
      match translateDialectControl vm' body with
      | some o =>
          some { Γ' := o.Γ', cont := ComCont.comp (ComCont.varBind e) o.cont, vm := o.vm }
      | none => none
  -- The dead zero-init elision of `translateDialectFull`'s `RLetZero` arm, with
  -- the body translated by this control front.
  | .RLetZero _name _tt body => translateDialectControl vm body
  | c => translateDialectFull vm c

/-- `translateDialectControl` on `RSeq`: the two children translated in sequence,
    prefixes composed. -/
theorem translateDialectControl_rSeq {Γ : Ctx} (vm : VarMap Γ) (c₁ c₂ : LowCT) :
    translateDialectControl vm (.RSeq c₁ c₂) =
      match translateDialectControl vm c₁ with
      | some o₁ =>
          match translateDialectControl o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none :=
  rfl

/-- `translateDialectControl` on a `RLetZero` binder is its translation of the
    body. -/
theorem translateDialectControl_rLetZero {Γ : Ctx} (vm : VarMap Γ) (name : String)
    (tt : TowerType) (body : LowCT) :
    translateDialectControl vm (.RLetZero name tt body) = translateDialectControl vm body :=
  rfl

/-- `translateDialectControl` on a `RLetU64Zero` binder: a `bvConst 64 0`
    binding of `name` composed before the body's translation. -/
theorem translateDialectControl_rLetU64Zero {Γ : Ctx} (vm : VarMap Γ) (name : String)
    (body : LowCT) :
    translateDialectControl vm (.RLetU64Zero name body) =
      match translateDialectControl (vm.bind (t := .sword 64) name) body with
      | some o =>
          some { Γ' := o.Γ'
                 cont := ComCont.comp
                   (ComCont.varBind
                     ({ op := .bvConst 64 (0 : BitVec 64), retTy_eq := rfl, args := .nil } :
                       Expr catCryptDialect Γ (.sword 64)))
                   o.cont
                 vm := o.vm }
      | none => none :=
  rfl

/-- Direct top-level front over the control-extended arm set.
    Mirrors `translateDialectFullTop`: emits the `constUnit; ret` terminator at
    the final context `o.Γ'`. -/
def translateDialectControlTop {Γ : Ctx} (vm : VarMap Γ) (c : LowCT) :
    Option (Σ Γ' : Ctx, Com catCryptDialect Γ' .unit) :=
  match translateDialectControl vm c with
  | some o =>
      let term : Com catCryptDialect o.Γ' .unit :=
        Com.var { op := .constUnit, retTy_eq := rfl, args := .nil } (.ret .here)
      some ⟨o.Γ', term⟩
  | none => none

/-! ## 3. The control-extended covered fragment -/

/-- The control-extended covered `LowCT` fragment: the leaf-call covered arms
    (`TranslateDialectDirectArms.IsCovered`) plus `RFor` over covered bodies,
    `RIfNz` over covered branches, and the data-dependent `RWhileNz` over a
    covered body. -/
inductive IsCoveredCtl : LowCT → Prop
  | ofCovered {c : LowCT} : IsCovered c → IsCoveredCtl c
  | rFor {x : String} {N : Nat} {body : LowCT} :
      IsCoveredCtl body → IsCoveredCtl (.RFor x N body)
  | rIfNz {name : String} {thenBr elseBr : LowCT} :
      IsCoveredCtl thenBr → IsCoveredCtl elseBr →
      IsCoveredCtl (.RIfNz name thenBr elseBr)
  | rWhileNz {name : String} {body : LowCT} :
      IsCoveredCtl body → IsCoveredCtl (.RWhileNz name body)
  | rLetU64Zero {name : String} {body : LowCT} :
      IsCoveredCtl body → IsCoveredCtl (.RLetU64Zero name body)

/-- On the leaf-call covered fragment, `translateDialectControl` coincides with
    `translateDialectFull`: the `RSeq` and `RLetU64Zero` arms agree by the
    child translations, every other arm delegates there. -/
theorem translateDialectControl_eq_full_of_covered {Γ : Ctx} (vm : VarMap Γ)
    {c : LowCT} (hc : IsCovered c) :
    translateDialectControl vm c = translateDialectFull vm c := by
  induction hc generalizing Γ with
  | rLetU64Zero _ ih =>
      simp only [translateDialectControl, translateDialectFull]
      split
      · next o heq => rw [ih] at heq; simp only [heq]
      · next heq => rw [ih] at heq; simp only [heq]
  | rSeq _ _ ih1 ih2 =>
      -- `translateDialectControl`'s `RSeq` arm recurses into itself; on a
      -- straight-line (`IsCovered`) `RSeq` it still agrees with
      -- `translateDialectFull` by the two child IHs (the `transCtlSeq` fold).
      simp only [translateDialectControl, translateDialectFull]
      split
      · next o₁ heq1 =>
          rw [ih1 vm] at heq1
          split
          · next o₂ heq2 => rw [ih2 o₁.vm] at heq2; simp only [heq1, heq2]
          · next heq2 => rw [ih2 o₁.vm] at heq2; simp only [heq1, heq2]
      · next heq1 => rw [ih1 vm] at heq1; simp only [heq1]
  | _ => rfl

/-! ### The `RWhileNz` front arm invariant

The data-dependent-while arm (§2) gates on the guard being a bound scalar and on
the loop body front-compiling (recursively), then emits the **context-invariant**
`DTransOut` — the loop-region invariant. The two facts the downstream
context-agreement / coverage extension reduces to. -/

/-- **The `RWhileNz` arm accepts the loop iff its body front-compiles** (on a
    bound-scalar guard). Mirrors `RIfNz`'s guard lookup: the arm succeeds precisely
    when the body does, at the unchanged entry context. -/
theorem translateDialectControl_rWhileNz_isSome_of_body {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (body : LowCT) (w : Nat) (v : CVar Γ (.sword w))
    (hlk : vm.lookup name = some ⟨.sword w, v⟩)
    (hbody : (translateDialectControl vm body).isSome) :
    (translateDialectControl vm (.RWhileNz name body)).isSome := by
  unfold translateDialectControl
  rw [hlk]
  cases h : translateDialectControl vm body with
  | none => rw [h] at hbody; simp at hbody
  | some o => rfl

/-- **The accepted loop is context-invariant** (`Γ' = Γ`): the loop body's
    bindings are loop-scoped and do not escape into the outer straight-line
    context. This is the loop-region invariant the arm preserves. -/
theorem translateDialectControl_rWhileNz_ctx_invariant {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (body : LowCT) (o : DTransOut Γ)
    (h : translateDialectControl vm (.RWhileNz name body) = some o) :
    o.Γ' = Γ := by
  unfold translateDialectControl at h
  split at h
  · cases hb : translateDialectControl vm body with
    | none => rw [hb] at h; simp at h
    | some o' =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rfl
  · simp at h


/-! ## 4. Worked examples -/

/-- A bounded loop over a covered body is control-covered and lowers via
    `loopRForD`. -/
example (x : String) (N : Nat) :
    IsCoveredCtl (.RFor x N .RSkip) := .rFor (.ofCovered .rSkip)

/-- An `RIfNz` over covered branches is control-covered. -/
example (name : String) :
    IsCoveredCtl (.RIfNz name .RSkip .RSkip) :=
  .rIfNz (.ofCovered .rSkip) (.ofCovered .rSkip)

/-- A bounded loop *sequenced* with further work — `RSeq (RFor …) …`, the
    top-level shape of a multi-phase kernel (X25519 `ladder; invert; encode`,
    sponge `absorb; squeeze`, MAYO phases) — descends through the front: the
    `RSeq` arm recurses into `translateDialectControl` on both children. -/
example :
    (translateDialectControl (Γ := []) VarMap.empty
      (.RSeq (.RFor "i" 4 .RSkip) .RSkip)).isSome := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
