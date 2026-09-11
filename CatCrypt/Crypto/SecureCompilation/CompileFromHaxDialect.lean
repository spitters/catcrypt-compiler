/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

/-!
# C6 dialect-routing: compile the THIR front *through* `thirDialect` (#616)

`ThirToComFront.lean` lowers the THIR-ANF surface **directly** to
`Com jasminDialect` (`thirToJasmin`). That skips the MLIR `thirDialect`
intermediate entirely, so any optimizer that runs at the `Com thirDialect`
level (the RD2 thir-level rewrites) never sees the compiled output.

This module adds the *routed* front: a second front lowering `thirToThirCom`
that targets `Com thirDialect` (the SAME `Ctxt`/`Var`/`HVector` type the direct
front uses — `thirDialect.Ty := JasminTy`, so `Ctxt thirDialect = Ctxt
jasminDialect` definitionally), followed by the generic, verified lowering
`lowerThir : Com thirDialect Γ t → Com jasminDialect Γ t`
(`ThirDialect.lean`). The composite

    Thir  --thirToThirCom-->  Com thirDialect  --lowerThir-->  Com jasminDialect

is `thirToJasminViaThir`. Routing through `thirDialect` lets compiled output
inherit the thirDialect-level optimizer before it ever reaches jasmin.

## What is proved

* `rhsExprThir` / `thirToThirCom` — the `thirDialect` analogues of `rhsExpr` /
  `thirToJasmin`, op-for-op (each `Rhs` arm builds the matching `ThirOp`).
* `thirToThirCom_denote` — preservation against the THIR big-step semantics
  (`Thir.denote`), the strong-induction mirror of `thirToJasmin_denote`.
* `thirToJasminViaThir_denote` — the routed composite preserves denotation,
  by composing `thirToThirCom_denote` with `lowerThir_denote`. Since
  `lowerThir c` denotes equal to `c` on the *same* valuation type, the routed
  composite's value is identical to the THIR meaning.
* `sigma0ViaThir_*` — the SHA-256 σ₀ leaf, routed end-to-end through the
  thirDialect and checked against the FIPS `sigma0Spec`.

## Variable transport

The front's `FState`/`Atom.toVar`/`atomsToVarHV` resolve atoms to
`@Ctxt.Var jasminDialect`. The `thirDialect` `Expr`s want `@Ctxt.Var
thirDialect` over the *same* context. The `Var` constructors (`here`/`there`)
don't mention the dialect's op set, so transport is structural: `vTinv` is the
jasmin→thir inverse of `ThirDialect.vT`, and `vTinv_lookup` preserves lookup
(the `Valuation` type is dialect-free).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
open CatCrypt.Crypto.SecureCompilation.ThirToComFront

/-! ## §1  jasmin → thir variable transport (the inverse of `vT`) -/

/-- Transport a jasmin-dialect variable to the THIR dialect (same `Ctxt`/`Ty`).
    The structural inverse of `ThirDialect.vT`. -/
def vTinv {Γ : Ctxt jasminDialect} {t : JasminTy} :
    @Ctxt.Var jasminDialect Γ t → @Ctxt.Var thirDialect Γ t
  | .here => .here
  | .there v => .there (vTinv v)

/-- Transport an HVector of jasmin-dialect variables to the THIR dialect. -/
def argsTinv {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} →
    HVector (fun ty => @Ctxt.Var jasminDialect Γ ty) tys →
    HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (vTinv v) (argsTinv rest)

/-- Transport preserves variable lookup (the valuation type is dialect-free). -/
theorem vTinv_lookup {Γ : Ctxt jasminDialect} {t : JasminTy} :
    (v : @Ctxt.Var jasminDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (vTinv v).lookup V = v.lookup V
  | .here, .cons _ _ => rfl
  | .there v, .cons _ V => by
      show (vTinv v).lookup V = v.lookup V
      exact vTinv_lookup v V

/-- Transport commutes with argument lookup. -/
theorem argsTinv_lookupArgs {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} →
    (args : HVector (fun ty => @Ctxt.Var jasminDialect Γ ty) tys) →
    (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (argsTinv args) V = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((vTinv v).lookup V) (Expr.lookupArgs (argsTinv rest) V)
        = HVector.cons (v.lookup V) (Expr.lookupArgs rest V)
      rw [vTinv_lookup v V, argsTinv_lookupArgs rest V]

/-! ## §2  `rhsExprThir`: lower a `Rhs` to a single `thirDialect` `Expr`

The `thirDialect` analogue of the front's `rhsExpr`. Each `Rhs` arm builds the
matching `ThirOp` (`.bin op → thBin`, `.ror n → thRor`, …) over the *same*
context, transporting the resolved jasmin variables to the THIR dialect via
`vTinv`. The atom-resolver (`Atom.toVar`/`atomsToVarHV`) is dialect-agnostic
(it works at the jasmin level), so we reuse it and transport its results. -/

/-- Lower a `Rhs` to the single `thirDialect` `Expr` it binds at the head of the
    context — the op-for-op mirror of `rhsExpr` (`.bin op a b → thBin op`,
    `.ror n a → thRor n`, `.shrImm n → thShrImm n`, `.shlImm n → thShlImm n`,
    `.add/.mul → thBin .add/.mul`, `.mulHi → thMulHi`, `.cast → thCast`,
    `.call → thExtCall`, `.atom → thConst`/`thBin .or` copy). -/
def rhsExprThir {w nIn : Nat} {locals : List String} (st : FState w nIn locals) :
    Rhs → Option (Expr thirDialect (frontCtxt w nIn locals) (rW w))
  | .atom (.lit n) =>
      some (Expr.mk (.thConst w n) rfl .nil)
  | .atom a =>
      (a.toVar st).map fun v =>
        Expr.mk (.thBin .or w) rfl (argsTinv (.cons v (.cons v .nil)))
  | .add a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some (Expr.mk (.thBin .add w) rfl
            (argsTinv (.cons va (.cons vb .nil))))
      | _, _ => none
  | .mul a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some (Expr.mk (.thBin .mul w) rfl
            (argsTinv (.cons va (.cons vb .nil))))
      | _, _ => none
  | .mulHi a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some (Expr.mk (.thMulHi w) rfl
            (argsTinv (.cons va (.cons vb .nil))))
      | _, _ => none
  | .bin op a b =>
      match a.toVar st, b.toVar st with
      | some va, some vb =>
          some (Expr.mk (.thBin op w) rfl
            (argsTinv (.cons va (.cons vb .nil))))
      | _, _ => none
  | .ror n a =>
      (a.toVar st).map fun va =>
        Expr.mk (.thRor w n) rfl (argsTinv (.cons va .nil))
  | .shrImm n a =>
      (a.toVar st).map fun va =>
        Expr.mk (.thShrImm w n) rfl (argsTinv (.cons va .nil))
  | .sarImm n a =>
      (a.toVar st).map fun va =>
        Expr.mk (.thSarImm w n) rfl (argsTinv (.cons va .nil))
  | .shlImm n a =>
      (a.toVar st).map fun va =>
        Expr.mk (.thShlImm w n) rfl (argsTinv (.cons va .nil))
  | .cast a =>
      (a.toVar st).map fun va =>
        Expr.mk (.thCast w w) rfl (argsTinv (.cons va .nil))
  | .call name args =>
      (atomsToVarHV st args).map fun vs =>
        Expr.mk (.thExtCall name (callArgTys w args.length) (rW w)) rfl
          (argsTinv vs)

/-! ## §3  `thirToThirCom`: lower a `Thir` to a `Com thirDialect`

Exact mirror of `thirToJasmin`: the same recursion (`.ret`, `.let_` push,
`.forUp` compile-time unrolling), with `rhsExprThir` in place of `rhsExpr`. -/

/-- Lower a THIR statement to a `Com thirDialect` against a scope state — the
    routed front's first stage. Same recursion as `thirToJasmin`:

    * `ret a` → bind `a`'s `Expr` then `ret here`.
    * `let_ x r body` → bind `r`'s `Expr`, lower `body` in the pushed scope.
    * `forUp` → compile-time unrolling into nested `let_`s. -/
def thirToThirCom {w nIn : Nat} (locals : List String) (st : FState w nIn locals) :
    Thir → Option (Com thirDialect (frontCtxt w nIn locals) (rW w))
  | .ret a =>
      (rhsExprThir st (.atom a)).map fun e => .var e (.ret .here)
  | .let_ x r body =>
      match rhsExprThir st r, thirToThirCom (x :: locals) (st.push x) body with
      | some e, some bc => some (.var e bc)
      | _, _ => none
  | .forUp acc init n body =>
      thirToThirCom locals st (Thir.unrollFor acc init n body)
  termination_by t => thirMeasure t
  decreasing_by
    · simp [thirMeasure]
    · simp [thirMeasure, thirMeasure_unrollFor]

/-! ## §4  Preservation of `rhsExprThir`

The `thirDialect` analogue of `rhsExpr_denote`: the single `Expr` produced for
a `Rhs` denotes to the same `BitVec w` as the THIR `Rhs`. Each arm reduces to
its jasmin counterpart's reasoning after `vTinv_lookup`/`argsTinv_lookupArgs`,
since the `thirDialect` op denotation matches the THIR `Rhs.denote`. -/

/-- `rhsExprThir` preservation: the routed `thirDialect` `Expr` denotes to the
    same value as the THIR `Rhs`. -/
theorem rhsExprThir_denote {w nIn : Nat} {locals : List String}
    {I : Fin nIn → BitVec w} {ρ : LEnv w} {st : FState w nIn locals}
    {V : Ctxt.Valuation (frontCtxt w nIn locals)} (h : Agree locals I ρ st V)
    (r : Rhs) {e : Expr thirDialect (frontCtxt w nIn locals) (rW w)}
    (he : rhsExprThir st r = some e) :
    r.denote I ρ = some (e.denote V) := by
  cases r with
  | atom a =>
      cases a with
      | lit n =>
          simp only [rhsExprThir, Option.some.injEq] at he
          subst he
          simp only [Rhs.denote, Atom.denote, Expr.denote, DialectDenote.denote]
      | lvar x =>
          rcases hv : (Atom.lvar x).toVar st with _ | v
          · simp [rhsExprThir, hv] at he
          · simp only [rhsExprThir, hv, Option.map_some, Option.some.injEq] at he
            subst he
            have hd := Atom.toVar_denote h (.lvar x) hv
            simp only [Rhs.denote]
            rw [hd]
            simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
            show some (v.lookup V)
                = some (JasminBinOp.or.apply (v.lookup V) (v.lookup V))
            simp [JasminBinOp.apply, BitVec.or_self]
      | inp i =>
          rcases hv : (Atom.inp i).toVar st with _ | v
          · simp [rhsExprThir, hv] at he
          · simp only [rhsExprThir, hv, Option.map_some, Option.some.injEq] at he
            subst he
            have hd := Atom.toVar_denote h (.inp i) hv
            simp only [Rhs.denote]
            rw [hd]
            simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
            show some (v.lookup V)
                = some (JasminBinOp.or.apply (v.lookup V) (v.lookup V))
            simp [JasminBinOp.apply, BitVec.or_self]
  | add a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExprThir, hva, hvb] at he
      · simp only [rhsExprThir, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | mul a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExprThir, hva, hvb] at he
      · simp only [rhsExprThir, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | mulHi a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExprThir, hva, hvb] at he
      · simp only [rhsExprThir, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | bin op a b =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      rcases hvb : b.toVar st with _ | vb
      · simp [rhsExprThir, hva, hvb] at he
      · simp only [rhsExprThir, hva, hvb, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Atom.toVar_denote h b hvb,
          Option.bind_some, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | ror n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      · simp only [rhsExprThir, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | shrImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      · simp only [rhsExprThir, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | sarImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      · simp only [rhsExprThir, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | shlImm n a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      · simp only [rhsExprThir, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | cast a =>
      rcases hva : a.toVar st with _ | va
      · simp [rhsExprThir, hva] at he
      · simp only [rhsExprThir, hva, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [Atom.toVar_denote h a hva, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]
        rfl
  | call name args =>
      rcases hvs : atomsToVarHV st args with _ | vs
      · simp [rhsExprThir, hvs] at he
      · simp only [rhsExprThir, hvs, Option.map_some, Option.some.injEq] at he
        subst he
        simp only [Rhs.denote]
        rw [atomsHV_lookupArgs h args hvs, Option.map_some]
        simp only [Expr.denote, DialectDenote.denote, argsTinv_lookupArgs]

/-! ## §5  Preservation of `thirToThirCom`

The strong-induction mirror of `thirToJasmin_denote`, on the unrolling measure
`thirMeasure`. The only difference from the jasmin proof is `rhsExprThir_denote`
in place of `rhsExpr_denote`; the loop-unrolling lemmas (`unrollFor_denote`)
are dialect-free (they live at the THIR-`denote` level). -/

/-- **Routed preservation (front stage).** When `Agree` holds and the routed
    lowering succeeds, the THIR denotation equals the `Com thirDialect`'s
    denotation. The `thirDialect` mirror of `thirToJasmin_denote`. -/
theorem thirToThirCom_denote {w nIn : Nat} (locals : List String)
    (I : Fin nIn → BitVec w) (t : Thir) (ρ : LEnv w) (st : FState w nIn locals)
    (V : Ctxt.Valuation (frontCtxt w nIn locals))
    (c : Com thirDialect (frontCtxt w nIn locals) (rW w))
    (hAg : Agree locals I ρ st V) (hc : thirToThirCom locals st t = some c) :
    t.denote I ρ = some (c.denote V) := by
  induction hmeas : thirMeasure t using Nat.strongRecOn
    generalizing locals ρ st V c t with
  | ind m ih =>
    cases t with
    | ret a =>
        simp only [thirToThirCom] at hc
        rcases he : rhsExprThir st (.atom a) with _ | e <;> rw [he] at hc
        · simp at hc
        · simp only [Option.map_some, Option.some.injEq] at hc
          subst hc
          have hr := rhsExprThir_denote hAg (.atom a) he
          simp only [Thir.denote]
          rw [show a.denote I ρ = (Rhs.atom a).denote I ρ from rfl, hr]
          simp only [Com.denote]
          rfl
    | let_ x r body =>
        simp only [thirToThirCom] at hc
        rcases he : rhsExprThir st r with _ | e <;> rw [he] at hc
        · simp at hc
        rcases hbc : thirToThirCom (x :: locals) (st.push x) body with _ | bc <;>
          rw [hbc] at hc
        · simp at hc
        · simp only [Option.some.injEq] at hc
          subst hc
          simp only [Thir.denote, Com.denote]
          rw [rhsExprThir_denote hAg r he, Option.bind_some]
          exact ih (thirMeasure body) (by subst hmeas; simp [thirMeasure])
            (x :: locals) body (ρ.set x (e.denote V)) (st.push x)
            (V.extend (e.denote V)) bc (hAg.push x (e.denote V)) hbc rfl
    | forUp acc init n body =>
        simp only [thirToThirCom] at hc
        rw [← unrollFor_denote]
        have hlt : thirMeasure (Thir.unrollFor acc init n body) < m := by
          subst hmeas; rw [thirMeasure_unrollFor]; simp [thirMeasure]
        exact ih (thirMeasure (Thir.unrollFor acc init n body)) hlt
          locals (Thir.unrollFor acc init n body) ρ st V c hAg hc rfl

/-! ## §6  The routing composite and its preservation

`thirToJasminViaThir = thirToThirCom` then `lowerThir`. Because `lowerThir c`
denotes equal to `c` on the *same* valuation type (`lowerThir_denote`), the
routed composite has exactly the THIR meaning — the routed jasmin `Com` agrees
with the THIR, the same statement `thirToJasmin_denote` gives for the direct
front. The difference is purely the path: the routed `Com thirDialect`
intermediate is exposed to the thirDialect-level optimizer. -/

/-- The routed front: lower the THIR through `thirDialect`, then run the generic
    verified `lowerThir` to land in `Com jasminDialect`. -/
def thirToJasminViaThir {w nIn : Nat} (locals : List String)
    (st : FState w nIn locals) (t : Thir) :
    Option (Com jasminDialect (frontCtxt w nIn locals) (rW w)) :=
  (thirToThirCom locals st t).map lowerThir

/-- **Routed preservation (composite).** When `Agree` holds and the routed
    lowering succeeds, the THIR denotation equals the lowered
    `Com jasminDialect`'s denotation — proved by composing `thirToThirCom_denote`
    (front stage) with `lowerThir_denote` (the generic lowering soundness). -/
theorem thirToJasminViaThir_denote {w nIn : Nat} (locals : List String)
    (I : Fin nIn → BitVec w) (t : Thir) (ρ : LEnv w) (st : FState w nIn locals)
    (V : Ctxt.Valuation (frontCtxt w nIn locals))
    (c : Com jasminDialect (frontCtxt w nIn locals) (rW w))
    (hAg : Agree locals I ρ st V)
    (hc : thirToJasminViaThir locals st t = some c) :
    t.denote I ρ = some (c.denote V) := by
  simp only [thirToJasminViaThir] at hc
  rcases hcc : thirToThirCom locals st t with _ | cc <;> rw [hcc] at hc
  · simp at hc
  · simp only [Option.map_some, Option.some.injEq] at hc
    subst hc
    rw [lowerThir_denote cc V]
    exact thirToThirCom_denote locals I t ρ st V cc hAg hcc

/-! ## §7  σ₀ DEMO: SHA-256 `small_sigma0`, routed end-to-end

The same σ₀ THIR the direct front compiles (`ThirToComFront.sigma0Thir`), now
routed through `thirDialect`. We reuse the front's `sigma0Thir`, `sigma0Spec`,
`inputValuation`, and `initAgree`. The lowering succeeds, and the routed jasmin
`Com` denotes the FIPS σ₀ reference for every input word. -/

/-- The routed lowering of σ₀ succeeds (`some`). -/
theorem sigma0ViaThir_lowers :
    (thirToJasminViaThir [] (initFState 32 1) sigma0Thir).isSome := by
  native_decide

/-- **Routed σ₀ connecting theorem.** There is a routed jasmin `Com` for σ₀ whose
    denotation, on every input word `x = I 0`, is exactly the FIPS 180-4
    `sigma0Spec x = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. The `= some c` part is the
    routed lowering succeeding; the value part composes
    `thirToJasminViaThir_denote` with the THIR-level `sigma0Thir_denote`. -/
theorem sigma0ViaThir_FrontValueAgrees :
    ∃ c : Com jasminDialect (frontCtxt 32 1 []) (rW 32),
      thirToJasminViaThir [] (initFState 32 1) sigma0Thir = some c ∧
      ∀ x : BitVec 32,
        c.denote (inputValuation 32 1 (fun _ => x))
          = x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ x >>> (3 : Nat) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp sigma0ViaThir_lowers
  refine ⟨c, hc, fun x => ?_⟩
  have hcong : sigma0Thir.denote (fun _ => x) (LEnv.empty 32)
      = some (c.denote (inputValuation 32 1 (fun _ => x))) :=
    thirToJasminViaThir_denote [] (fun _ => x) sigma0Thir (LEnv.empty 32)
      (initFState 32 1) (inputValuation 32 1 (fun _ => x)) c
      (initAgree (fun _ => x)) hc
  have hspec := sigma0Thir_denote (fun _ => x)
  rw [hcong] at hspec
  have : some (c.denote (inputValuation 32 1 (fun _ => x)))
      = some (sigma0Spec ((fun _ => x) 0)) := hspec
  have := Option.some.inj this
  simp only [sigma0Spec] at this
  rw [this]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxDialect
