/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring


@[expose] public section
set_option autoImplicit false

/-!
# `RFnDef` / `RFnCall` arms for the dialect front

`LowCT.RFnDef name params returns body cont` declares a helper function and
`LowCT.RFnCall f dests args` invokes one. This file supplies the two front
combinators that lower them into `Com catCryptDialect`, together with their
context, leakage and denotation obligations.

## Main definitions

* `fnCallD`: lowers `RFnCall` to one `extCall` binding per destination.
* `fnDefD`: type-checks an `RFnDef` body and emits the translation of `cont`.
* `translateDialectFnCall`: the front dispatcher over the two constructors.

## Main results

* `fnCallD_eq_loopCallNDestsD`: `fnCallD` is the `RCallN` fold at `fnLeafName f`.
* `fnDefD_eq_cont` / `fnDefD_eq_none`: `fnDefD` emits `cont` on success, rejects
  a body the front declines.
* `fnCallD_leakFactors` / `fnDefD_leakFactors`: leak-factoring obligations.
* `translateDialectFnCall_RFnDef` / `translateDialectFnCall_RFnCall`: the
  dispatcher agrees with each arm.

## The call is an opaque leaf

`Com d` cannot carry a call node: `VIR.Dialect` fixes `Op : Type` before `Com d`
exists, so no op can mention a program. `ComL` inherits that shape — its six loop
nodes are the loop layer, and it has no inter-procedural region node either. What
both layers do carry is the `extCall name argTys retTy` **op**, whose denotation
is an opaque oracle and which `DialectToJasminCom.cryptoDialectToJasminCom` maps
to the jasmin `extCall` that the backend lowers to a linked call.

`RFnCall f dests args` therefore lowers exactly as `RCallN` does: one
`extCall` binding per destination, through `loopCallNDestsD`, under the leaf name
`fnLeafName f`. The two constructors carry the same operand shape (`dests`,
`args`) and the same borrow-checker contract, and `loopCallNDestsD` is parametric
in the leaf name, so every companion result proved for the `RCallN` fold —
denotation, leak factoring, no-alias preservation, interpreter extension —
applies to `RFnCall` by instantiation rather than by a parallel proof.

Whole-program reasoning across the call boundary is recovered one layer down, by
`VIR.ComInlineCall.inlineLcall_denote`: for a statically known non-recursive
callee `Com` satisfying `CalleeConsistent` with the leaf name, the inlined
call-free program denotes identically to the program with the call. That is a
discharged hypothesis per call site, not an assumption about the oracle.

## The definition binds, it does not run

`LowCT.RustExec` gives `RFnDef name params returns body cont` the rule
"run `cont`" — the body is not executed at the definition site — and
`LowCT.toJasminProg.extractFnDefs` matches it, lifting the body to a sibling
`FunDecl` and leaving `cont` as the residual. `fnDefD` follows both: it
type-checks the body against a `VarMap` seeded with the formals (`bindFormals`)
and, when the body front-compiles, emits the translation of `cont` alone. A
definition whose body the front declines is rejected rather than ignored. This
mirrors the `RWhileNz` arm of `TranslateDialectDirectControl.translateDialectControl`,
which likewise gates on a sub-program compiling and emits a context-invariant
output.

## Scope

`translateDialectFnCall` is a harness: it carries the two new arms plus an `RSeq`
arm, enough to exhibit a helper definition followed by two calls to it, and
delegates every other arm to `translateDialectControl`. Once the two arms
are in `translateDialectControl`'s own match, a definition nested under any arm
of the front is reached and this harness is subsumed.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectFnCall

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectLeakFactoring
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located)

/-! ## 1. The helper leaf name -/

/-- The name a helper `f` is passed to the destination fold under. The fold
    applies `callNLeafName` per output, so the emitted `extCall` op for output
    `i` names `"callN:fn:" ++ f ++ "#" ++ toString i` — disjoint from the
    `"callN:" ++ g ++ "#" ++ toString i` of a primitive leaf `g`, so a leaf
    oracle can tell a user-defined helper from a primitive. -/
def fnLeafName (f : String) : String := "fn:" ++ f

/-! ## 2. The `RFnCall` arm -/

/-- Lower `RFnCall f dests args`: one `extCall (fnLeafName f)` binding per
    destination, through the `RCallN` destination fold. -/
def fnCallD {Γ : Ctx} (f : String) (args : List Located) (vm : VarMap Γ)
    (dests : List Located) : Option (DTransOut Γ) :=
  loopCallNDestsD (fnLeafName f) args vm dests

/-- `fnCallD` is the `RCallN` destination fold at the helper leaf name. Every
    companion result proved for `loopCallNDestsD` at an arbitrary leaf name
    transports along this equation. -/
theorem fnCallD_eq_loopCallNDestsD {Γ : Ctx} (f : String) (args : List Located)
    (vm : VarMap Γ) (dests : List Located) :
    fnCallD f args vm dests = loopCallNDestsD (fnLeafName f) args vm dests := rfl

/-! ## 3. The `RFnDef` arm -/

/-- Seed a `VarMap` with a list of `Located` formals, each bound at its encoded
    type. Used to type-check a helper body against its parameters and returns. -/
def bindFormals {Γ : Ctx} (vm : VarMap Γ) : List Located → (Δ : Ctx) × VarMap Δ
  | [] => Sigma.mk Γ vm
  | l :: rest =>
      let r := bindFormals vm rest
      Sigma.mk (encodeTy l.locDst :: r.1) (r.2.bind l.locVar)

/-- Lower `RFnDef name params returns body cont`: front-compile `body` against a
    `VarMap` seeded with `params ++ returns`, and on success emit the translation
    of `cont`. The body contributes no prefix at the definition site, matching
    the residual of `LowCT.extractFnDefs`. `RustExec` has no rule for `RFnDef`,
    so this is the dialect-side shape a future rule would mirror rather than a
    lowering of an existing one. -/
def fnDefD {Γ : Ctx}
    (translateBody : ∀ {Δ : Ctx}, VarMap Δ → LowCT → Option (DTransOut Δ))
    (vm : VarMap Γ) (params returns : List Located) (body cont : LowCT) :
    Option (DTransOut Γ) :=
  match translateBody (bindFormals vm (params ++ returns)).2 body with
  | some _ => translateBody vm cont
  | none => none

/-- A definition whose body front-compiles emits exactly the continuation's
    translation. -/
theorem fnDefD_eq_cont {Γ : Ctx}
    (translateBody : ∀ {Δ : Ctx}, VarMap Δ → LowCT → Option (DTransOut Δ))
    (vm : VarMap Γ) (params returns : List Located) (body cont : LowCT)
    {ob : DTransOut (bindFormals vm (params ++ returns)).1}
    (hbody : translateBody (bindFormals vm (params ++ returns)).2 body = some ob) :
    fnDefD translateBody vm params returns body cont = translateBody vm cont := by
  simp only [fnDefD, hbody]

/-- A definition whose body the front declines is declined. -/
theorem fnDefD_eq_none {Γ : Ctx}
    (translateBody : ∀ {Δ : Ctx}, VarMap Δ → LowCT → Option (DTransOut Δ))
    (vm : VarMap Γ) (params returns : List Located) (body cont : LowCT)
    (hbody : translateBody (bindFormals vm (params ++ returns)).2 body = none) :
    fnDefD translateBody vm params returns body cont = none := by
  simp only [fnDefD, hbody]

/-- Whatever the front emits for a `RFnDef` is what it emits for the
    continuation: the definition site contributes no context, no prefix and no
    `VarMap` change of its own. -/
theorem fnDefD_mem_cont {Γ : Ctx}
    (translateBody : ∀ {Δ : Ctx}, VarMap Δ → LowCT → Option (DTransOut Δ))
    (vm : VarMap Γ) (params returns : List Located) (body cont : LowCT)
    {o : DTransOut Γ}
    (h : fnDefD translateBody vm params returns body cont = some o) :
    translateBody vm cont = some o := by
  unfold fnDefD at h
  split at h
  · exact h
  · simp at h

/-! ## 4. Leakage

`ComCont.LeakFactors f k` records that the prefix `f` prepends exactly `k` leak
events, independently of any valuation — the front-side constant-prefix
statement. A call boundary is where a leakage argument usually breaks because
the callee's trace joins the caller's; under the opaque-leaf lowering it does
not, because the callee contributes no prefix at all: the call site emits one
event per destination and the definition site emits none. -/

/-- The `RFnCall` prefix leak-factors: it prepends a fixed number of leak
    events, independent of any valuation. Instantiation of the `RCallN`
    destination-fold result at the helper leaf name. -/
theorem fnCallD_leakFactors {Γ : Ctx} (f : String) (args : List Located)
    (vm : VarMap Γ) (dests : List Located) {o : DTransOut Γ}
    (h : fnCallD f args vm dests = some o) :
    ∃ k : Nat, ComCont.LeakFactors o.cont k :=
  loopCallNDestsD_leakFactors (fnLeafName f) args vm dests h

/-- The `RFnDef` prefix leak-factors exactly as its continuation does: a helper
    definition emits no leak event of its own. -/
theorem fnDefD_leakFactors {Γ : Ctx}
    (translateBody : ∀ {Δ : Ctx}, VarMap Δ → LowCT → Option (DTransOut Δ))
    (vm : VarMap Γ) (params returns : List Located) (body cont : LowCT)
    {o : DTransOut Γ} {k : Nat}
    (h : fnDefD translateBody vm params returns body cont = some o)
    (hcont : ∀ o' : DTransOut Γ, translateBody vm cont = some o' →
      ComCont.LeakFactors o'.cont k) :
    ComCont.LeakFactors o.cont k :=
  hcont o (fnDefD_mem_cont translateBody vm params returns body cont h)

/-! ## 5. The harness front -/

/-- The dialect front carrying the two helper arms plus an `RSeq` arm; every
    other arm delegates to `translateDialectControl`. -/
def translateDialectFnCall {Γ : Ctx} (vm : VarMap Γ) :
    LowCT → Option (DTransOut Γ)
  | .RFnCall f dests args => fnCallD f args vm dests
  | .RFnDef _ params returns body cont =>
      match translateDialectFnCall (bindFormals vm (params ++ returns)).2 body with
      | some _ => translateDialectFnCall vm cont
      | none => none
  | .RSeq c₁ c₂ =>
      match translateDialectFnCall vm c₁ with
      | some o₁ =>
          match translateDialectFnCall o₁.vm c₂ with
          | some o₂ =>
              some { Γ' := o₂.Γ', cont := ComCont.comp o₁.cont o₂.cont, vm := o₂.vm }
          | none => none
      | none => none
  | c => translateDialectControl vm c

/-- The harness front's `RFnDef` arm is `fnDefD` at the harness translator. -/
theorem translateDialectFnCall_RFnDef {Γ : Ctx} (vm : VarMap Γ)
    (name : String) (params returns : List Located) (body cont : LowCT) :
    translateDialectFnCall vm (.RFnDef name params returns body cont)
      = fnDefD (fun {_Δ} vm' c => translateDialectFnCall vm' c) vm params returns body cont := by
  simp only [translateDialectFnCall, fnDefD]

/-- The harness front's `RFnCall` arm is `fnCallD`. -/
theorem translateDialectFnCall_RFnCall {Γ : Ctx} (vm : VarMap Γ)
    (f : String) (dests args : List Located) :
    translateDialectFnCall vm (.RFnCall f dests args) = fnCallD f args vm dests := by
  simp only [translateDialectFnCall]

/-! ## 6. A two-function worked example

`demoFnProg` declares one helper and calls it twice; `demoInlined` is the same
program with the helper body substituted at both call sites. Both front-compile,
and both emit the same output context — one fresh slot per destination — so the
call boundary costs no context and the inlining is context-neutral. -/

/-- A `u64` slot with the given name. -/
def u64Slot (n : String) : Located := { locVar := n, locSrc := .TU64 }

/-- Entry `VarMap` binding the three top-level `u64` slots `a`, `b`, `c`. -/
def demoEntry : (Δ : Ctx) × VarMap Δ :=
  bindFormals (Γ := []) VarMap.empty [u64Slot "a", u64Slot "b", u64Slot "c"]

/-- A helper `dbl(x) -> y` defined as `y := u64_add(x, x)`, called twice:
    `b := dbl(a)` then `c := dbl(b)`. -/
def demoFnProg : LowCT :=
  .RFnDef "dbl" [u64Slot "x"] [u64Slot "y"]
    (.RCallN "u64_add" [u64Slot "y"] [u64Slot "x", u64Slot "x"])
    (.RSeq (.RFnCall "dbl" [u64Slot "b"] [u64Slot "a"])
           (.RFnCall "dbl" [u64Slot "c"] [u64Slot "b"]))

/-- `demoFnProg` with the helper body substituted at both call sites. -/
def demoInlined : LowCT :=
  .RSeq (.RCallN "u64_add" [u64Slot "b"] [u64Slot "a", u64Slot "a"])
        (.RCallN "u64_add" [u64Slot "c"] [u64Slot "b", u64Slot "b"])

/-! The two-function program front-compiles. -/
#guard (translateDialectFnCall demoEntry.2 demoFnProg).isSome

/-! The hand-inlined equivalent front-compiles. -/
#guard (translateDialectFnCall demoEntry.2 demoInlined).isSome

/-! Both emit the same output context: one fresh slot per destination, with the
definition site contributing none. -/
#guard (translateDialectFnCall demoEntry.2 demoFnProg).map (·.Γ')
     = (translateDialectFnCall demoEntry.2 demoInlined).map (·.Γ')

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectFnCall
