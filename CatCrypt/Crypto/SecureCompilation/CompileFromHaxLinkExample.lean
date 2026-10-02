/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-!
# Linking a front-lowered outer with the front-compiled SHA-256 σ₀ kernel

The outer program is the front lowering (`ThirToComFront.thirToJasmin`) of the
THIR term `let r = sha256_sigma0(inp[0]); ret r`, written directly in Lean. Its
single right-hand side is an `extCall` boundary named `"sha256_sigma0"`.

The leaf is `ThirToComFront.sigma0Com`, the front lowering of the SHA-256 σ₀
THIR `sigma0Thir`. Linking inlines that kernel at the call boundary with
`ComInlineCall.inlineCalls`, which yields a call-free `Com jasminDialect`.

## Main results

* `outerSigma0Thir_lowers`, `sigma0Thir_lowers` — both front lowerings succeed.
* `sigma0Com_denote` — the front-compiled σ₀ kernel denotes the FIPS 180-4
  formula `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)` for every input word `x`, from the
  front's value preservation `sigma0_FrontValueAgrees` and `sigma0Thir_denote`.
* `linkedExample_correct` — the linked program `linkedSigma0Com` denotes the
  same formula for every input word `x`. The proof rewrites with the inlining law
  `ComInlineCall.inlineCalls_denote_eq_denoteSubst`, which carries no hypothesis
  on the external-call semantics `jasminExtSem`, and closes with
  `sigma0Com_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## §1  The outer: a front-lowered `Com` with one `extCall` -/

/-- The external-call name of the σ₀ leaf. -/
def sigma0Name : String := "sha256_sigma0"

/-- The outer THIR: `let r = sha256_sigma0(inp[0]); ret r`. One single-argument
    external call to the σ₀ leaf, returning its result. -/
def outerSigma0Thir : Thir :=
  .let_ "r" (.call sigma0Name [.inp 0]) (.ret (.lvar "r"))

/-- The outer lowers (the front returns `some`) at width 32 with `nIn = 1`. -/
theorem outerSigma0Thir_lowers :
    (thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) outerSigma0Thir).isSome := by
  simp only [outerSigma0Thir, thirToJasmin, rhsExpr, atomsToVarHV, Atom.toVar,
    initFState, FState.push, inputVarRep, Option.map_some, if_true]
  rfl

/-- The outer `Com` (the front's output) at width 32. -/
noncomputable def outerSigma0Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  (thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) outerSigma0Thir).get
    outerSigma0Thir_lowers

/-! ## §2  The leaf: the front-compiled σ₀ kernel -/

/-- The front lowering of the σ₀ THIR succeeds. -/
theorem sigma0Thir_lowers :
    (thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) sigma0Thir).isSome := by
  simp only [sigma0Thir, thirToJasmin, rhsExpr, Atom.toVar, initFState, FState.push,
    inputVarRep, if_true]
  rfl

/-- The front-compiled σ₀ kernel denotes the FIPS 180-4 σ₀ formula on every input
    word. -/
theorem sigma0Com_denote (x : BitVec 32) :
    (sigma0Com ()).denote (inputValuation 32 1 (fun _ => x)) = sigma0Spec x := by
  have hc : thirToJasmin (w := 32) (nIn := 1) [] (initFState 32 1) sigma0Thir
      = some (sigma0Com ()) := by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp sigma0Thir_lowers
    simp only [sigma0Com, hc, Option.getD_some]
  have h := sigma0_FrontValueAgrees (fun _ => x) (sigma0Com ()) hc
  rw [sigma0Thir_denote] at h
  exact (Option.some.inj h).symm

/-! ## §3  Linking by inlining -/

/-- The σ₀ kernel as a callee body over its one `rW 32` formal. -/
noncomputable def sigma0Callee : ComInlineCall.FunBodyN :=
  { argTys := ctxtSigma0, retTy := rW 32, body := sigma0Com () }

/-- The registry that maps `"sha256_sigma0"` to the σ₀ kernel and no other name. -/
noncomputable def sigma0Funcs : ComInlineCall.FuncRegistryN :=
  fun nm => if nm = sigma0Name then some sigma0Callee else none

/-- The linked program: the outer with the σ₀ kernel inlined at its call. -/
noncomputable def linkedSigma0Com : Com jasminDialect (frontCtxt 32 1 []) (rW 32) :=
  ComInlineCall.inlineCalls sigma0Funcs outerSigma0Com

/-- **The linked program denotes SHA-256 σ₀.** For every input word `x`, the
    call-free program obtained by inlining the front-compiled σ₀ kernel into the
    front-lowered outer denotes `(x ror 7) ⊕ (x ror 18) ⊕ (x >> 3)`. -/
theorem linkedExample_correct (x : BitVec 32) :
    linkedSigma0Com.denote (inputValuation 32 1 (fun _ => x))
      = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  refine (ComInlineCall.inlineCalls_denote_eq_denoteSubst sigma0Funcs outerSigma0Com
    (inputValuation 32 1 (fun _ => x))).trans ?_
  have key : ComInlineCall.denoteSubst sigma0Funcs outerSigma0Com
      (inputValuation 32 1 (fun _ => x))
      = (fun v : BitVec 32 => v ||| v)
          ((sigma0Com ()).denote (inputValuation 32 1 (fun _ => x))) := by
    with_unfolding_all rfl
  exact key.trans (BitVec.or_self.trans (sigma0Com_denote x))

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxLinkExample
