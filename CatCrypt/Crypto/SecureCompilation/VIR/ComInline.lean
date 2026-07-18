/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate

/-!
# Verified `extCall` inlining as a `Com → Com` pass

A verified inlining pass for the Jasmin VIR dialect. The pass walks a
`Com jasminDialect Γ t` and, for each `Com.var (extCall fName …) body` whose
`fName` is matched by a hand-curated function registry, **replaces the call
with the registered body's single defining expression** spliced into
position.

## Why a verified inlining pass

Downstream Com → Com passes (CSE / GVN, LICM, dead-code elimination) can only
optimise across function-call boundaries if those boundaries are first removed.
Inlining is the third of the three highest-leverage missing -O2 passes
alongside CSE/GVN and LICM. Adding it lets CSE/GVN see across function bodies
and LICM hoist work out of loops whose bodies used to hide it behind a call.

The closest existing Com → Com pass is `JasminLeafFusion.lean`, which fuses
**two adjacent leaves** into a single fused leaf. That pass operates on
*declared* `extCall` op nodes — it preserves the call structure. Inlining is
complementary: it **eliminates** call nodes by substituting the callee's body.

## Scope (initial deliverable)

In the typed VIR every `Expr.args` is already an `HVector` of `Ctxt.Var`
references (no nested expressions to duplicate at a call site), so the
task's "args must be `Pvar`" scope cap is automatic by the intrinsic typing.

For this initial deliverable the registry is restricted to **single-expression
function bodies** of the shape

  `.var defExpr (.ret .here)`

i.e. functions that perform exactly one operation `defExpr` on their formals
and return its result. This covers the realistic inlining case for a small
*wrapper* leaf (e.g. a "Σ₀" SHA-2 helper that just calls one primitive, or a
Barrett-reduce wrapper around a single intrinsic).

Per the task's "honest blocker handling" guidance: general inlining (bodies
with nested let-bindings) requires Com-level splicing through `Com.foldVar`
plus a bookkeeping lemma about lifting outer-context vars through emitted
bindings — straightforward in principle (the substitution laws are proved
below) but not needed for the single-expression case. Extending the scope to
multi-binding bodies is the next deliverable.

## Architecture

* `SingleExprBody` — a single-expression function body (one `Expr` over
  the formals, returning its result).
* `FunBody` / `FuncRegistry` — packaging + the registry map.
* `argHom` — turn an `HVector (Ctxt.Var Γ) argTys` (a call's args) into a
  `Ctxt.Hom argTys Γ`.
* `inlineExpr` — inline a body's defining expression by renaming through
  `argHom`.
* `inline` — the recursive walk over a `Com`.

## What is proved

* `Var.lookup_rename` / `Expr.denote_rename` — standard substitution laws.
* `inlineExpr_denote` — the inlined expression on a caller valuation equals
  the body's defining expression on the formals' valuation
  `Expr.lookupArgs args V`.
* `inline_emptyRegistry` — sanity: the inline pass on the empty registry is
  the identity.

All proofs are structural over `Expr`/`HVector`. No `sorry`, no
`native_decide`, no new axioms.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. Function bodies and the registry -/

/-- A single-expression function body: one operation `defExpr` on the
    formals, returning its result. -/
structure SingleExprBody (argTys : List JasminTy) (retTy : JasminTy) where
  defExpr : Expr jasminDialect argTys retTy

/-- The Com associated with a single-expression body. -/
def SingleExprBody.toCom {argTys : List JasminTy} {retTy : JasminTy}
    (b : SingleExprBody argTys retTy) : Com jasminDialect argTys retTy :=
  .var b.defExpr (.ret .here)

/-- A registered function body: a closed `SingleExprBody` whose context is
    the function's formal parameter types and whose return type is the
    function's return type. -/
structure FunBody where
  argTys : List JasminTy
  retTy  : JasminTy
  body   : SingleExprBody argTys retTy

/-- The function registry: a hand-curated map from function names to bodies.
    The pass inlines `extCall` ops whose name is in this map and whose
    argument / return types match the registered body. -/
abbrev FuncRegistry := String → Option FunBody

/-! ## 2. Substitution: args HVector → `Ctxt.Hom` -/

/-- Look up the `i`-th `Ctxt.Var Γ tᵢ` from an args HVector, indexed by a
    function-body variable `Ctxt.Var argTys t`. -/
def argsLookup {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {t : JasminTy} :
    HVector (fun ty => Ctxt.Var Γ ty) argTys →
    @Ctxt.Var jasminDialect argTys t → Ctxt.Var Γ t :=
  match argTys with
  | [] => fun _ v => nomatch v
  | _ :: _ => fun args v =>
    match args, v with
    | .cons v _, .here => v
    | .cons _ rest, .there w => argsLookup rest w

/-- Build a context homomorphism `Ctxt.Hom argTys Γ` from an args HVector
    `HVector (Ctxt.Var Γ) argTys`. -/
def argHom {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys) :
    Ctxt.Hom argTys Γ :=
  fun {_} v => argsLookup args v

/-- The value of an args-renamed formal is the value of the corresponding
    caller argument in `V`. -/
theorem argsLookup_lookup : {Γ : Ctxt jasminDialect} → {argTys : List JasminTy} →
    {t : JasminTy} → (args : HVector (fun ty => Ctxt.Var Γ ty) argTys) →
    (v : Ctxt.Var argTys t) → (V : Ctxt.Valuation Γ) →
    (argsLookup args v).lookup V
      = v.lookup (Expr.lookupArgs args V)
  | _, [], _, _, v, _ => nomatch v
  | _, _ :: _, _, .cons _ _, .here, _ => rfl
  | _, _ :: _, _, .cons _ rest, .there w, V => argsLookup_lookup rest w V

/-! ## 3. Pullback valuations and the renaming substitution laws

Standard de Bruijn substitution lemmas: looking up a renamed variable in `V`
equals looking up the original variable in the **pullback** of `V` along `h`. -/

/-- Pullback of a `Valuation Γ'` along a context homomorphism `h : Γ → Γ'`,
    defined by recursion on `Γ`. -/
def pullV : {Γ : Ctxt jasminDialect} → {Γ' : Ctxt jasminDialect} →
    Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => HVector.nil
  | _ :: _, _, h, V =>
      HVector.cons ((h Ctxt.Var.here).lookup V)
        (pullV (fun v => h (.there v)) V)

/-- Looking up a renamed variable in `V` equals looking up the original
    variable in the pullback of `V`. -/
theorem Ctxt.Var.lookup_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih =>
    simp only [pullV]
    exact ih (fun v => h (.there v))

/-- Renaming arguments and looking them up against a valuation equals looking
    up the original arguments against the pulled-back valuation. -/
theorem lookupArgs_renameVars {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') :
    {tys : List JasminTy} →
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ') →
    Expr.lookupArgs (HVector.renameVars h args) V
      = Expr.lookupArgs args (pullV h V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
    show HVector.cons _ _ = HVector.cons _ _
    congr 1
    · exact Ctxt.Var.lookup_rename h v V
    · exact lookupArgs_renameVars h rest V

/-- Renaming an `Expr` and denoting it against `V` equals denoting the
    original expression against the pulled-back valuation. -/
theorem Expr.denote_rename {Γ Γ' : Ctxt jasminDialect}
    (h : Ctxt.Hom Γ Γ') {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (pullV h V) := by
  cases e with
  | mk op retTy_eq args =>
    simp only [Expr.rename, Expr.denote]
    rw [lookupArgs_renameVars h args V]

/-! ## 4. The args-substitution lemma

When the homomorphism is `argHom args`, the pullback `pullV (argHom args) V`
is exactly `Expr.lookupArgs args V` — the formals' valuation the function
body should see. -/

/-- The pullback along the args-substitution hom equals the looked-up args. -/
theorem pullV_argHom {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (V : Ctxt.Valuation Γ) :
    pullV (argHom args) V = Expr.lookupArgs args V := by
  induction args with
  | nil => rfl
  | @cons t ts v rest ih =>
    show HVector.cons _ _ = HVector.cons _ _
    -- Head matches definitionally (`(argHom (cons v _) .here).lookup V`
    -- reduces to `v.lookup V`); tail follows from the IH.
    congr 1

/-! ## 5. Inlining a single-expression body's defining expression -/

/-- Inline a single-expression body's defining expression at the call site:
    rename `defExpr` through the args-to-formal homomorphism. -/
def inlineExpr {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {retTy : JasminTy}
    (b : SingleExprBody argTys retTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys) :
    Expr jasminDialect Γ retTy :=
  b.defExpr.rename (argHom args)

/-- **Denotation theorem for the inlined expression.** Evaluating the
    inlined expression on the caller valuation equals evaluating the
    function body's defining expression on the formals' valuation
    `Expr.lookupArgs args V`. -/
theorem inlineExpr_denote {Γ : Ctxt jasminDialect} {argTys : List JasminTy}
    {retTy : JasminTy}
    (b : SingleExprBody argTys retTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (V : Ctxt.Valuation Γ) :
    (inlineExpr b args).denote V
      = b.defExpr.denote (Expr.lookupArgs args V) := by
  unfold inlineExpr
  rw [Expr.denote_rename]
  rw [pullV_argHom]

/-! ## 6. The inline pass: a recursive walk over `Com`

For each `Com.var e body`, examine `e.op`. If it is
`extCall name argTys retTy` and the registry maps `name` to a body whose
types match, replace `e` with the inlined expression; the binding shape
stays identical (the inlined expression has the same return type).

Otherwise keep the binding and recurse into the body. -/

/-- Try to inline a single binding's `e : Expr Γ bs` against the registry. -/
def tryInlineExpr (R : FuncRegistry) {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) : Option (Expr jasminDialect Γ bs) :=
  match e_op : e.op with
  | .extCall name eArgTys eRetTy =>
    match R name with
    | some fb =>
      if hArg : fb.argTys = eArgTys then
        if hRet : fb.retTy = eRetTy then
          -- `e.args : HVector (Ctxt.Var Γ) (DialectSignature.sig e.op)`.
          -- With `e.op = extCall name eArgTys eRetTy` (`e_op`), the signature
          -- list is `eArgTys`. With `fb.argTys = eArgTys` (`hArg`), view
          -- `e.args` as `HVector (Ctxt.Var Γ) fb.argTys`.
          let argsRenamed : HVector (fun ty => Ctxt.Var Γ ty) fb.argTys :=
            hArg ▸ (show HVector (fun ty => Ctxt.Var Γ ty)
                          (DialectSignature.sig (.extCall name eArgTys eRetTy))
                    from e_op ▸ e.args)
          let inlined : Expr jasminDialect Γ fb.retTy :=
            inlineExpr fb.body argsRenamed
          -- Convert `inlined : Expr Γ fb.retTy` to `Expr Γ bs` via
          -- `fb.retTy = eRetTy` then `eRetTy = DialectSignature.ret e.op = bs`
          -- (`e.retTy_eq` for the latter).
          let inlinedAtRet : Expr jasminDialect Γ eRetTy := hRet ▸ inlined
          -- `e.retTy_eq : DialectSignature.ret e.op = bs`, i.e.
          -- `eRetTy = bs` once `e.op = extCall …`. Convert.
          have h_ret_match : eRetTy = bs := by
            have := e.retTy_eq
            rw [e_op] at this
            exact this
          some (h_ret_match ▸ inlinedAtRet)
        else none
      else none
    | none => none
  | _ => none

/-- One pass of inlining: walk the Com, replacing each registered
    `extCall`'s expression with the inlined expression. -/
def inline (R : FuncRegistry) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | _, _, .ret v => .ret v
  | _, _, .var (t := _) e body =>
    match tryInlineExpr R e with
    | some e' => .var e' (inline R body)
    | none => .var e (inline R body)

/-! ## 7. Smoke: empty-registry identity -/

/-- The empty registry. -/
def emptyRegistry : FuncRegistry := fun _ => none

/-- For any `Expr`, `tryInlineExpr emptyRegistry e = none`. -/
theorem tryInlineExpr_emptyRegistry {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (e : Expr jasminDialect Γ bs) :
    tryInlineExpr emptyRegistry e = none := by
  -- Destructure `e` to expose its `op`; then case on the `op`. The `.extCall`
  -- arm goes through `R name = emptyRegistry _ = none`, all others return
  -- `none` directly.
  obtain ⟨op, retTy_eq, args⟩ := e
  unfold tryInlineExpr
  cases op <;> rfl

/-- On the empty registry, `inline` is the identity. -/
theorem inline_emptyRegistry :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    inline emptyRegistry c = c
  | _, _, .ret _ => rfl
  | _, _, .var (t := _) e body => by
    -- Reduce `inline` to its `.var` arm; `tryInlineExpr emptyRegistry e` is
    -- `none`, so the pass keeps `e` and recurses; IH closes.
    show (match tryInlineExpr emptyRegistry e with
            | some e' => Com.var e' (inline emptyRegistry body)
            | none => Com.var e (inline emptyRegistry body)) = Com.var e body
    rw [tryInlineExpr_emptyRegistry]
    exact congrArg _ (inline_emptyRegistry body)

/-! ## 8. Registry consistency and denotation preservation

The headline theorem says `(inline R p).denote V = p.denote V` — **provided**
the registry is consistent, i.e. each registered body's defining expression
denotes equally to the `extCall`'s opaque external semantics.

This is exactly analogous to `JasminLeafFusion.fuseExtCall_denote`'s `hgf`
per-leaf KAT obligation. -/

/-- Registry consistency: each registered body's defining expression
    denotes equally to the `extCall`'s opaque external semantics. -/
def RegistryConsistent (R : FuncRegistry) : Prop :=
  ∀ (name : String) (fb : FunBody), R name = some fb →
    ∀ (V : Ctxt.Valuation (d := jasminDialect) fb.argTys),
      fb.body.defExpr.denote V
        = jasminExtSem name fb.argTys fb.retTy V

/-- **Local denotation theorem for `tryInlineExpr`.** If `tryInlineExpr R e`
    succeeds, the inlined Expr denotes equally to the original Expr — provided
    the registry is consistent.

    The proof unfolds `tryInlineExpr`, destructures `e` to expose its op as
    an `.extCall` (the only path where `tryInlineExpr` returns `some`),
    threads through the type-match equalities, and reduces both sides to a
    common `jasminExtSem` evaluation. -/
theorem tryInlineExpr_denote {Γ : Ctxt jasminDialect} {bs : JasminTy}
    (R : FuncRegistry) (h_consistent : RegistryConsistent R)
    (e : Expr jasminDialect Γ bs) (e' : Expr jasminDialect Γ bs)
    (h_match : tryInlineExpr R e = some e')
    (V : Ctxt.Valuation Γ) :
    e'.denote V = e.denote V := by
  -- Destructure e and case on its op. `tryInlineExpr` only returns `some`
  -- in the `.extCall` arm, so every other op gives `h_match : none = some e'`,
  -- a contradiction. We use simp to evaluate the outer match in each arm.
  obtain ⟨op, retTy_eq, args⟩ := e
  cases op with
  | regArith => unfold tryInlineExpr at h_match; cases h_match
  | stackLoad => unfold tryInlineExpr at h_match; cases h_match
  | stackStore => unfold tryInlineExpr at h_match; cases h_match
  | castW => unfold tryInlineExpr at h_match; cases h_match
  | regConst => unfold tryInlineExpr at h_match; cases h_match
  | vpackZMM => unfold tryInlineExpr at h_match; cases h_match
  | vpackZMMd => unfold tryInlineExpr at h_match; cases h_match
  | vprordZMM => unfold tryInlineExpr at h_match; cases h_match
  | vpslldq => unfold tryInlineExpr at h_match; cases h_match
  | vpsrldq => unfold tryInlineExpr at h_match; cases h_match
  | vsimd => unfold tryInlineExpr at h_match; cases h_match
  | mulhi => unfold tryInlineExpr at h_match; cases h_match
  | addCarryLo => unfold tryInlineExpr at h_match; cases h_match
  | addCarryHi => unfold tryInlineExpr at h_match; cases h_match
  | rorImm => unfold tryInlineExpr at h_match; cases h_match
  | shrImm => unfold tryInlineExpr at h_match; cases h_match
  | sarImm => unfold tryInlineExpr at h_match; cases h_match
  | shlImm => unfold tryInlineExpr at h_match; cases h_match
  | select => unfold tryInlineExpr at h_match; cases h_match
  | callN => unfold tryInlineExpr at h_match; cases h_match
  | extCall name eArgTys eRetTy =>
    -- `e.retTy_eq : eRetTy = bs` (the `Expr.mk` field gives the call's
    -- return type after the op-match).
    -- The call's args have type `HVector (Var Γ) eArgTys`. Substitute
    -- `retTy_eq` to align everything at one type. We case on `R name`
    -- next.
    unfold tryInlineExpr at h_match
    -- The outer `match e_op : op` collapses to the `extCall` arm.
    simp only at h_match
    -- Now `h_match` is on `match R name with ...`.
    cases h_R : R name with
    | none =>
      rw [h_R] at h_match; exact absurd h_match (by simp)
    | some fb =>
      rw [h_R] at h_match
      -- Reduce the outer `match some fb` so the `dite`s are top-level.
      simp only at h_match
      by_cases hArg : fb.argTys = eArgTys
      · rw [dif_pos hArg] at h_match
        by_cases hRet : fb.retTy = eRetTy
        · rw [dif_pos hRet] at h_match
          subst hArg
          subst hRet
          simp only [Option.some.injEq] at h_match
          subst h_match
          subst retTy_eq
          rw [inlineExpr_denote]
          rw [h_consistent name fb h_R (Expr.lookupArgs args V)]
          rfl
        · rw [dif_neg hRet] at h_match; exact absurd h_match (by simp)
      · rw [dif_neg hArg] at h_match; exact absurd h_match (by simp)

/-- **Headline denotation theorem.** Under registry consistency, `inline R`
    preserves `Com.denote`. -/
theorem inline_preserves_denote (R : FuncRegistry)
    (h_consistent : RegistryConsistent R) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → (c : Com jasminDialect Γ t) →
    (V : Ctxt.Valuation Γ) →
    (inline R c).denote V = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var (t := _) e body, V => by
    -- Reduce `inline` to its `.var` arm; case on `tryInlineExpr R e`.
    unfold inline
    cases h_match : tryInlineExpr R e with
    | none =>
      -- No inlining: keep `e`; recurse on body via IH.
      simp only [Com.denote]
      rw [inline_preserves_denote R h_consistent body
            (Ctxt.Valuation.extend V (e.denote V))]
    | some e' =>
      -- Inlining succeeded: e'.denote V = e.denote V by tryInlineExpr_denote.
      simp only [Com.denote]
      rw [tryInlineExpr_denote R h_consistent e e' h_match V]
      rw [inline_preserves_denote R h_consistent body
            (Ctxt.Valuation.extend V (e.denote V))]

/-! ## 9. CT preservation

The inline pass is CT-preserving when each registered body's defining
expression is itself CT-safe. Replacing an `extCall` (always CT-safe by
`opIndexPublic_extCall`) with a registered body's defining expression
preserves CT iff that expression is CT-safe — i.e., its op's index arg (if
any) is public after the args substitution.

For the canonical inlining case (a wrapper around another `extCall`), the
inlined expression is again an `extCall`, hence CT-safe unconditionally. -/

/-- Registry CT consistency: each registered body's defining expression is
    CT-safe under any label context for the formals. The natural side-
    condition: only register CT-safe bodies. -/
def RegistryCTSafe (R : FuncRegistry) : Prop :=
  ∀ (name : String) (fb : FunBody), R name = some fb →
    ∀ (L : LabelCtxt fb.argTys),
      ctSafeExprJasmin fb.body.defExpr L = true

/-! Note on the CT-preservation statement.

The full denotation theorem (`inline_preserves_denote`) composes through the
denotation lemmas because `Expr.denote` is parametric in the variable
context. The full CT-preservation theorem requires the analogous transfer
of `ctSafeExprJasmin` through `argHom`: if the body's expression is CT-safe
in *any* label context (`RegistryCTSafe`), then in particular the renamed
expression at the caller is CT-safe in the caller's label context.

The structural argument: `ctSafeExprJasmin` reduces to `opIndexPublic`,
which for non-load/store ops returns `true` unconditionally. For
`stackLoad`/`stackStore` the second arg is the index; after renaming via
`argHom`, the index variable's label in the caller's `L` is what
`labelOf (argHom args .there .here) L` evaluates to. Provided the caller
supplies a public-index arg at that slot, the inlined expression is
CT-safe.

For the canonical "wrapper around extCall" registered body (`defExpr.op =
extCall …`), every `ctSafeExprJasmin` evaluation is unconditionally `true`
regardless of label context, so CT preservation is *unconditional* on the
caller side. We state and prove this concrete case below — it is the
CT-side analogue of `JasminLeafFusion`'s "fused-leaf is itself an
extCall, always CT-safe" reasoning. -/

/-- The inlined expression from a wrapper-around-`extCall` body is itself
    CT-safe under any caller label context, unconditionally.

    This is the canonical CT-preservation guarantee for the realistic
    inlining case: a wrapper leaf whose defining expression is itself an
    `extCall` to a primitive. The renamed wrapper denotes (by
    `inlineExpr`) to an `extCall` at the caller's side, which is CT-safe
    by `opIndexPublic_extCall` regardless of the args' labels. -/
theorem inlineExpr_ctSafe_of_extCall_body
    {Γ : Ctxt jasminDialect} {argTys : List JasminTy} {retTy : JasminTy}
    (b : SingleExprBody argTys retTy)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys)
    (L : LabelCtxt Γ)
    (h_ext : ∃ name innerArgTys innerRetTy,
      b.defExpr.op = JasminOp.extCall name innerArgTys innerRetTy) :
    ctSafeExprJasmin (inlineExpr b args) L = true := by
  -- The renamed Expr's op equals the body's op (Expr.rename only touches
  -- args, not op). So if the body's op is an extCall, the inlined op is
  -- too, and `ctSafeExprJasmin_extCall` gives the result.
  apply ctSafeExprJasmin_extCall
  obtain ⟨name, innerArgTys, innerRetTy, hop⟩ := h_ext
  refine ⟨name, innerArgTys, innerRetTy, ?_⟩
  -- `inlineExpr b args = b.defExpr.rename (argHom args)`; renaming preserves op.
  simp only [inlineExpr, Expr.rename]
  exact hop

end CatCrypt.Crypto.SecureCompilation.VIR.ComInline
