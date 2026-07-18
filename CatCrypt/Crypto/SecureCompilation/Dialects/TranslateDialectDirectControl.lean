/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms

set_option autoImplicit false

/-!
# Control-flow arms of the `CProg`-free direct front (`RIfNz` + `RFor`)

`TranslateDialectDirectArms.translateDialectFull` fuses the core straight-line
arms plus the leaf-call multi-binding arms into a `CProg`-free
`Com catCryptDialect` recursion, with context agreement to `translate` on
`IsCovered`. The two arms it still declined were the *intricate* control-flow
ones:

* **`RFor x N body`** — the bounded inline unroll. `translate` lowers it via
  `loopRFor`, a pure `Nat`-recursion that, per iteration `i ∈ [0..N)`, emits one
  `letBind (bvConst (BitVec.ofNat 64 i))` then threads `translate vm body`
  through the growing `VarMap`.

* **`RIfNz name thenBr elseBr`** — the φ-merge. `translate` translates both
  branches in the entry context and merges by final-context shape: cases (A)
  (both non-extending) and (B) (one extends) pass through one branch's
  `⟨Γ', vm⟩`; case (C′) — both branches a `RScalarSet` on the *same* name —
  materialises a six-binding `CExpr.ite` chain (`thenV; elseV; zero; cond_eq;
  cond_bit; merged`); case (C-otherwise) re-translates `elseBr` from the
  post-then `VarMap`.

This file fuses **both** arms `CProg`-free, mirroring `translate`'s exact
control flow but building `Com catCryptDialect` nodes through `ComCont`:

* `loopRForD` — the `Nat`-recursion twin of `loopRFor` (same shape as
  `TranslateDialectDirectArms.loopCallNDestsD`, but the per-iteration body
  translator is `translateDialectFull vm' body`).
* the `RIfNz` arm builds the **same** final `Γ'`/`VarMap` as `translate` in
  every case; the (C′) φ-merge composes six `ComCont.varBind`s — the
  `toVIRExprT`-images of the six `CExpr`s `translate` emits — so no `CProg.ite`
  chain is named.

## Context agreement (`translateDialectControl_ctx_agree`)

Exactly as for the leaf-call arms, `translateTop` discards the prefix and emits
the `constUnit; ret` terminator at the final context, so the load-bearing fact
is **context agreement**: `translateDialectControl` and `translate` succeed
together and emit the *same* `⟨Γ', vm⟩`. We prove it on the extended fragment
`IsCoveredCtl` (the covered arms of `TranslateDialectDirectArms.IsCovered` plus
`RFor` over covered bodies and `RIfNz` over covered branches), reusing the
`loopCallNDestsD_ctx_agree` fold pattern for `RFor` (`loopRForD_ctx_agree`) and a
case split mirroring `translate`'s (A)/(B)/(C′)/(C-otherwise) for `RIfNz`.

## Coverage

With `RIfNz` and `RFor` fused, the `CProg`-free front now covers the full
**non-`while`** `LowCT` (the core + leaf-call + control arms); only `RWhileNz`
(unbounded loops, a genuine `CProg.cwhile` region) and the not-yet-in-dialect
ops (`RAsmOp`, `bvAdd64`/`bvAdc`, dynamic memref, sampling) remain declined.
This completes the coverage half of the `CProg`-deletion keystone (DR collapse)
for everything but unbounded `while`.
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

/-! ## 1. Fused dialect `RFor` twin (`loopRForD`)

`loopRForD` is the `Nat`-recursion twin of `loopRFor`: per iteration it emits one
`ComCont.varBind` of the fused `bvConst (BitVec.ofNat 64 i)` then threads the
direct body translator. Mirrors `loopCallNDestsD` (whose recursion was over the
destination list); here the recursion is over `Nat`, and the body translator is
the dialect front `translateDialectFull`. -/

/-- Dialect twin of `loopRFor`: a left-to-right `Nat`-fold of one
    `bvConst (BitVec.ofNat 64 i)` binding plus the direct body translation per
    iteration, building `ComCont` prefixes. `CProg`-free. The body translator
    `translateBody` is passed in (as in `loopRFor`), so this def can be used
    before `translateDialectControl` is in scope. -/
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

Mirrors `translate`'s control flow on `RFor`/`RIfNz`; every other arm delegates
to `translateDialectFull`. The `RIfNz` φ-merge builds the six fused expressions
(`toVIRExprT`-images of `translate`'s six `CExpr`s) inline as a chain of
`ComCont.varBind`s — no `CProg.ite` is named. -/

/-- Direct `LowCT → catCryptDialect` translation extended to the control-flow
    arms `RFor` and `RIfNz`. `CProg`-free: every prefix is a `ComCont`. -/
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
                        -- (C′) φ-merge: build the six fused expressions —
                        -- the `toVIRExprT`-images of `translate`'s six `CExpr`s.
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
  | c => translateDialectFull vm c

/-- Direct `CProg`-free top-level front over the control-extended arm set.
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

/-! ## 3. The control-extended covered fragment and context agreement -/

/-- The control-extended covered `LowCT` fragment: the leaf-call covered arms
    (`TranslateDialectDirectArms.IsCovered`) plus `RFor` over covered bodies and
    `RIfNz` over covered branches. -/
inductive IsCoveredCtl : LowCT → Prop
  | ofCovered {c : LowCT} : IsCovered c → IsCoveredCtl c
  | rFor {x : String} {N : Nat} {body : LowCT} :
      IsCoveredCtl body → IsCoveredCtl (.RFor x N body)
  | rIfNz {name : String} {thenBr elseBr : LowCT} :
      IsCoveredCtl thenBr → IsCoveredCtl elseBr →
      IsCoveredCtl (.RIfNz name thenBr elseBr)

/-- On the leaf-call covered fragment, `translateDialectControl` coincides with
    `translateDialectFull` (it delegates there for every non-`RFor`/`RIfNz`
    arm). -/
theorem translateDialectControl_eq_full_of_covered {Γ : Ctx} (vm : VarMap Γ)
    {c : LowCT} (hc : IsCovered c) :
    translateDialectControl vm c = translateDialectFull vm c := by
  induction hc generalizing Γ with
  | rSeq _ _ ih1 ih2 =>
      -- `translateDialectControl`'s `RSeq` arm now recurses into itself; on a
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

/-- A bounded loop over a covered body is control-covered and lowers `CProg`-free
    via `loopRForD`. -/
example (x : String) (N : Nat) :
    IsCoveredCtl (.RFor x N .RSkip) := .rFor (.ofCovered .rSkip)

/-- An `RIfNz` over covered branches is control-covered. -/
example (name : String) :
    IsCoveredCtl (.RIfNz name .RSkip .RSkip) :=
  .rIfNz (.ofCovered .rSkip) (.ofCovered .rSkip)

/-- **The RSeq-over-control wall is gone.** A bounded loop *sequenced* with
    further work — `RSeq (RFor …) …`, the top-level shape of a multi-phase kernel
    (X25519 `ladder; invert; encode`, sponge `absorb; squeeze`, MAYO phases) —
    now descends through the canonical front. The old `RSeq` arm delegated both
    children to the straight-line `translateDialectFull`, whose `| _ => none`
    declined the `RFor` child, so this returned `none`. It is now `isSome`. -/
example :
    (translateDialectControl (Γ := []) VarMap.empty
      (.RSeq (.RFor "i" 4 .RSkip) .RSkip)).isSome := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
