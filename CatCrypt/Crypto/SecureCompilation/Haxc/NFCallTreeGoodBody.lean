/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule

/-!
# The calls of the bodies of the functions of a module, from the typing of the front

A body `crateOp` returns for a call of a function of a module is the program `impToNF` makes of
the body of the function at the call typing `crateSigOf` of the prepared callees over the call
typing `linkSig` of the linked functions, which is the call typing of the module. Every
operation of the body is therefore typed by the front (`frontOp`), as the operations of the
source program of the entry are. A call of a linked function then satisfies `GoodCall` as in
`NFCallTreeGoodCall.goodCall_of_op`. A call of a function of the module has a body in the
library when the argument types are the parameter types and the function has a body at its own
signature: the first holds at a call without an argument of type `int` of a function without a
parameter of type `int` (`argTysFit_eq`), the second is a shape condition on each function.

## Main results

* `opsNB_crateBody`: the operations of a body `crateBody` returns are typed by the front.
* `crateOp_isSome_of_op`: a typed call of a function of the module without an argument of type
  `int` has a body in the library.
* `goodCallB`: `GoodCall` at every operation of every body `crateOp` returns for a call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax (HaxModule ModFn find?_prep)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf entryCtx whileCarryOkB)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody crateLib crateCallOp)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (frontOp opsNB)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule (OpOk GoodCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall (IntArgFree opsNB_hasOp
  argTysFit_eq goodCall_of_op)

/-- **The operations of a body `crateBody` returns are typed by the front**: every operation
    satisfies `frontOp` at the call typing `crateSigOf fs base`, every exit-flag loop carries a
    tuple of types of `whileCarryOkB`, and the body has no `call` node. -/
theorem opsNB_crateBody {fs : List CrateFn} {c : CrateFn} {as : List NfTy} {r : NfTy}
    {base : String → List NfTy → Option NfTy} {b : NFProg nfDialect as [r]}
    (hb : crateBody fs c as r base = some b) :
    opsNB (frontOp (crateSigOf fs base)) b (fun cs => cs.all whileCarryOkB) = true := by
  unfold crateBody at hb
  split at hb
  · obtain ⟨o, ho, hb⟩ := Option.bind_eq_some_iff.mp hb
    split at hb
    · rename_i h
      obtain ⟨h1, h2⟩ := h
      subst h1 h2
      cases hb
      exact FrontComplete.impToNF_prog_frontOpLoop _ _ _ _ o ho
    · cases hb
  · cases hb

/-- **A typed call of a function of the module without an argument of type `int` has a body
    in the library**, when no function of the module has a parameter of type `int` and each
    has a body at its own parameter types and result type. -/
theorem crateOp_isSome_of_op {m : HaxModule}
    (hpar : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true) :
    ∀ o : NfOp, frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf) o = true →
      OpOk IntArgFree o → crateCallOp (m.prepared nfBody) o = true →
        ((crateLib (m.prepared nfBody) m.linkSig).op o).isSome = true := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
    intro hS hI hC
    simp only [frontOp, decide_eq_true_eq] at hS
    simp only [OpOk, IntArgFree] at hI
    simp only [crateCallOp, HaxModule.prepared, find?_prep, Option.isSome_map] at hC
    obtain ⟨fn, hf⟩ := Option.isSome_iff_exists.mp hC
    have hmem := List.mem_of_find?_eq_some hf
    unfold crateSigOf at hS
    rw [List.find?_append, HaxModule.prepared, find?_prep, hf] at hS
    simp only [Option.map_some, Option.some_or] at hS
    split at hS
    · rename_i hfit
      have hpar' : ∀ p ∈ (fn.prep nfBody).params.map (·.2), p ≠ .int := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hpar fn hmem q hq
      have has := argTysFit_eq hfit hpar' hI
      have hr : (fn.prep nfBody).res = r := Option.some.inj hS
      subst has hr
      simp only [crateLib, crateOp, HaxModule.prepared, find?_prep, hf, Option.map_some,
        Option.bind_some]
      exact hbody fn hmem
    · cases hS
  | _ => intro _ _ hC; simp [crateCallOp] at hC

/-- **`GoodCall` at every operation of every body of a call of a function of a module.** When
    the linked functions pass `linkSigOk`, no function of `m` has a parameter of type `int`,
    each function of `m` has a body at its own signature, and no call of a body has an argument
    of type `int`, every operation of a body `crateOp` returns for a call satisfies
    `GoodCall m`. This is the premise `hgood` of
    `NFCallTreeR3Handlers.r3FA_of_shape_linkedHandlers`. -/
theorem goodCallB {m : HaxModule} (hsig : ∀ l ∈ m.linked, linkSigOk l = true)
    (hpar : ∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int)
    (hbody : ∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true)
    (hintB : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk IntArgFree o) :
    ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk (GoodCall m) o := by
  intro g as r b hb o ho
  have hops : opsNB (frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf)) b
      (fun cs => cs.all whileCarryOkB) = true := by
    obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.mp hb
    have h := opsNB_crateBody hc
    rwa [← HaxModule.sigOf_eq_linkSig, HaxModule.sigOf] at h
  exact goodCall_of_op hsig o (opsNB_hasOp b hops o ho)
    (crateOp_isSome_of_op hpar hbody o (opsNB_hasOp b hops o ho) (hintB g as r b hb o ho))
    (hintB g as r b hb o ho)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodBody
