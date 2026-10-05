/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgModule
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses

/-!
# Inlining of calls in `NFProg`

A library `InlineLib d` gives, for an operation of the dialect `d`, a body over the argument
types of the operation returning its result, and, for a symbol at a signature `as → rs`, a body
over `as` returning `rs`. `NFProg.inline?` replaces each let-binding of an operation and each
`call` node the library has a body for by that body, with the argument variables substituted
for its parameters, followed by the continuation reading the body's results.

The splice is `NFProg.seq? k b ρ θ`: the body `b` over `Δ`, its variables renamed into `Γ` by
`ρ`, followed by the continuation `k` over `rs ++ Γ₀`, whose variables of `Γ₀` are renamed into
`Γ` by `θ`. The regions of the body are renamed by `NFProg.rename?`; the spine of the body is
traversed, and the continuation is renamed once, at the return of the body, by the renaming
`PRen.appendVars` that reads the returned variables for `rs`.

A library is sound at a fuel (`InlineLib.Sound`) when every successful run of an operation or of
a callee of the call environment is a run of its body with the same result. Inlining under a
sound library keeps every successful run (`NFProg.denote_inline?`), at the dialect's call
environment and at an explicit one (`NFProg.denoteAt_inline?`). `NFProg.inlineIter` repeats the
pass, so that the calls of an inlined body are inlined by the next round; `inlineStep` is the
repetition as a chain step and `inlineCert` its certificate.

`crateLib fs` is the library of the functions `fs` of a crate over `nfDialect`: a leaf call
`NfOp.call f as r` of a function of `fs` has the body `impToNF` produces from the function's
body over its parameters, when the parameter types are `as` and the result type is `r`.

## Main definitions

* `PRen.ofArgs`, `PRen.appendVars`, `PRen.shift`, `PRen.id` — the renamings of a body's
  parameters to argument variables, of a continuation's results to returned variables, under
  further bindings, and the identity.
* `NFProg.seq?` — a body renamed into a context, followed by a continuation.
* `InlineLib`, `InlineLib.Sound` — inlining libraries and their soundness.
* `NFProg.inlineVar`, `NFProg.inline?`, `NFProg.inlineIter` — inlining at one binding, in a
  program, and repeated.
* `NFProgPasses.inlineStep`, `NFProgPasses.inlineCert` — the repeated inlining as a chain step
  and its certificate.
* `NFInline.crateBody`, `NFInline.crateOp`, `NFInline.crateLib` — the bodies of the functions
  of a crate, at a leaf call and at a named leaf call.

## Main results

* `PRen.agrees_ofArgs`, `PRen.agrees_appendVars`, `PRen.agrees_shift`, `PRen.agrees_id` — the
  renamings relate the valuations they are built for.
* `NFProg.denote_seq?` — the splice denotes the body followed by the continuation.
* `NFProg.denote_inline?`, `NFProg.denoteAt_inline?` — inlining under a sound library keeps
  every successful run.
* `NFProg.denote_inlineIter` — so does the repeated inlining.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## 1. The renamings of a splice -/

namespace PRen

variable {d : Dialect}

/-- The renaming of the context `as` to the variables `args` of `Γ`, position by position. -/
def ofArgs {Γ : Ctxt d} : {as : List d.Ty} → HVector (fun t => Var Γ t) as → PRen as Γ
  | [], .nil, _, v => nomatch v
  | _ :: _, .cons w _, _, .here => some w
  | _ :: _, .cons _ ws, _, .there v => ofArgs ws v

/-- The renaming of `rs ++ Γ₀` to `Γ`: the variables of `rs` to the variables `ws`, position by
    position, and the variables of `Γ₀` by `θ`. -/
def appendVars {Γ₀ Γ : Ctxt d} (θ : PRen Γ₀ Γ) : {rs : List d.Ty} →
    HVector (fun t => Var Γ t) rs → PRen (rs ++ Γ₀) Γ
  | [], .nil, _, v => θ v
  | _ :: _, .cons w _, _, .here => some w
  | _ :: _, .cons _ ws, _, .there v => appendVars θ ws v

/-- The renaming `θ` followed by the shift under the bindings `cs`. -/
def shift {Γ₀ Γ : Ctxt d} (cs : List d.Ty) (θ : PRen Γ₀ Γ) : PRen Γ₀ (cs ++ Γ) :=
  fun v => (θ v).map (Var.shiftApp cs)

/-- The identity renaming. -/
def id {Γ : Ctxt d} : PRen Γ Γ := fun v => some v

variable [TyDenote d.Ty]

/-- The renaming to the arguments `args` relates their values to the valuation. -/
theorem agrees_ofArgs {Γ : Ctxt d} (W : Valuation Γ) : {as : List d.Ty} →
    (args : HVector (fun t => Var Γ t) as) → Agrees (ofArgs args) (Expr.lookupArgs args W) W
  | [], .nil => fun v => nomatch v
  | _ :: _, .cons w ws => by
      intro v v' hv
      cases v with
      | here =>
          simp only [ofArgs, Option.some.injEq] at hv
          subst hv
          rfl
      | there v => exact agrees_ofArgs W ws v v' hv

/-- The renaming to the returned variables `ws` relates their values, followed by a valuation
    `θ` relates, to the valuation. -/
theorem agrees_appendVars {Γ₀ Γ : Ctxt d} {θ : PRen Γ₀ Γ} {V₀ : Valuation Γ₀}
    {W : Valuation Γ} (h : Agrees θ V₀ W) : {rs : List d.Ty} →
    (ws : HVector (fun t => Var Γ t) rs) →
    Agrees (appendVars θ ws) (hvAppend (Expr.lookupArgs ws W) V₀) W
  | [], .nil => h
  | _ :: _, .cons w ws => by
      intro v v' hv
      cases v with
      | here =>
          simp only [appendVars, Option.some.injEq] at hv
          subst hv
          rfl
      | there v => exact agrees_appendVars h ws v v' hv

/-- The shifted renaming relates the valuation to the valuation extended by a tuple. -/
theorem agrees_shift {Γ₀ Γ : Ctxt d} {θ : PRen Γ₀ Γ} {V₀ : Valuation Γ₀} {W : Valuation Γ}
    (h : Agrees θ V₀ W) (cs : List d.Ty) (A : Valuation cs) :
    Agrees (shift cs θ) V₀ (hvAppend A W) := by
  intro t v v' hv
  simp only [shift, Option.map_eq_some_iff] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [Var.lookup_shiftApp]
  exact h v w hw

/-- The identity renaming relates a valuation to itself. -/
theorem agrees_id {Γ : Ctxt d} (V : Valuation Γ) : Agrees (id (Γ := Γ)) V V := by
  intro t v v' hv
  simp only [id, Option.some.injEq] at hv
  subst hv
  rfl

end PRen

/-! ## 2. The splice of a body and a continuation -/

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

namespace NFProg

/-- **The splice** of the body `b` over `Δ`, renamed into `Γ` by `ρ`, and the continuation `k`
    over `rs ++ Γ₀`, whose variables of `Γ₀` are renamed into `Γ` by `θ`: the spine of `b` with
    its regions renamed, and at each return of `b` the continuation reading the returned
    variables. `none` when a renaming drops a variable the program reads. -/
def seq? {Γ₀ : Ctxt d} {rs ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) :
    {Δ Γ : Ctxt d} → NFProg d Δ rs → PRen Δ Γ → PRen Γ₀ Γ → Option (NFProg d Γ ts)
  | _, _, .ret vs, ρ, θ => (PRen.vars? ρ vs).bind fun ws => rename? (PRen.appendVars θ ws) k
  | _, _, .var (t := t) e b, ρ, θ =>
      (Expr.rename? ρ e).bind fun e' =>
        (seq? k b (PRen.lift ρ) (PRen.shift [t] θ)).map (.var e')
  | _, _, .forLoop (cs := cs) count inits body b, ρ, θ =>
      (ρ count).bind fun c' => (PRen.vars? ρ inits).bind fun i' =>
        (rename? (PRen.liftApp cs (PRen.lift ρ)) body).bind fun body' =>
          (seq? k b (PRen.liftApp cs ρ) (PRen.shift cs θ)).map fun b' =>
            .forLoop c' i' body' b'
  | _, _, .ifThenElse (rs := rs') cond thn els b, ρ, θ =>
      (ρ cond).bind fun c' => (rename? ρ thn).bind fun t' => (rename? ρ els).bind fun e' =>
        (seq? k b (PRen.liftApp rs' ρ) (PRen.shift rs' θ)).map fun b' =>
          .ifThenElse c' t' e' b'
  | _, _, .whileLoop (cs := cs) inits body b, ρ, θ =>
      (PRen.vars? ρ inits).bind fun i' => (rename? (PRen.liftApp cs ρ) body).bind fun body' =>
        (seq? k b (PRen.liftApp cs ρ) (PRen.shift cs θ)).map fun b' => .whileLoop i' body' b'
  | _, _, .call (rs := rs') f args b, ρ, θ =>
      (PRen.vars? ρ args).bind fun a' =>
        (seq? k b (PRen.liftApp rs' ρ) (PRen.shift rs' θ)).map fun b' => .call f a' b'

variable [DialectDenoteM d Option] [CallDenote d]

/-- **The splice denotes the body followed by the continuation.** When `ρ` relates `U` to `W`
    and `θ` relates `V₀` to `W`, the splice denotes at `W` the run of `b` at `U` followed by
    the run of `k` at its results and `V₀`. -/
theorem denote_seq? {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts} {U : Valuation Δ}
      {V₀ : Valuation Γ₀} {W : Valuation Γ}, seq? k b ρ θ = some q →
      PRen.Agrees ρ U W → PRen.Agrees θ V₀ W → ∀ fuel,
      q.denote fuel W = b.denote fuel U >>= fun r => k.denote fuel (hvAppend r V₀) := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff] at hq
      obtain ⟨ws, hws, hq⟩ := hq
      rw [denote_rename? k hq (PRen.agrees_appendVars hθ ws) fuel,
        PRen.lookupArgs_vars? hρ vs hws]
      rfl
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he, b', hb, rfl⟩ := hq
      simp only [denote, Expr.denoteM_rename? hρ e he, bind_assoc]
      congr 1
      funext x
      exact ih k hb (PRen.agrees_lift hρ x) (PRen.agrees_shift hθ _ (.cons x .nil)) fuel
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨c', hc, i', hi, body', hbody', b', hb, rfl⟩ := hq
      simp only [denote, hρ count c' hc, PRen.lookupArgs_vars? hρ inits hi, bind_assoc]
      have hfold : (fun acc i => body'.denote fuel
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
          (fun acc i => body.denote fuel
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) U))) := by
        funext acc i
        exact denote_rename? body hbody' (PRen.agrees_liftApp (PRen.agrees_lift hρ _) _ acc) fuel
      rw [hfold]
      congr 1
      funext acc
      exact ih k hb (PRen.agrees_liftApp hρ _ acc) (PRen.agrees_shift hθ _ acc) fuel
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨c', hc, t', ht, e', he, b', hb, rfl⟩ := hq
      simp only [denote, hρ cond c' hc, denote_rename? thn ht hρ fuel,
        denote_rename? els he hρ fuel, bind_assoc]
      congr 1
      funext r
      exact ih k hb (PRen.agrees_liftApp hρ _ r) (PRen.agrees_shift hθ _ r) fuel
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨i', hi, body', hbody', b', hb, rfl⟩ := hq
      simp only [denote, PRen.lookupArgs_vars? hρ inits hi, bind_assoc]
      have hstep : (fun acc => body'.denote fuel (hvAppend acc W)) =
          (fun acc => body.denote fuel (hvAppend acc U)) := by
        funext acc
        exact denote_rename? body hbody' (PRen.agrees_liftApp hρ _ acc) fuel
      rw [hstep]
      congr 1
      funext acc
      exact ih k hb (PRen.agrees_liftApp hρ _ acc) (PRen.agrees_shift hθ _ acc) fuel
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W hq hρ hθ fuel
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨a', ha, b', hb, rfl⟩ := hq
      simp only [denote, PRen.lookupArgs_vars? hρ args ha, bind_assoc]
      congr 1
      funext r
      exact ih k hb (PRen.agrees_liftApp hρ _ r) (PRen.agrees_shift hθ _ r) fuel

end NFProg

/-! ## 3. Inlining libraries and the pass -/

/-- **An inlining library** of the dialect `d`: for an operation, a body over its argument
    types returning its result; for a symbol at the signature `as → rs`, a body over `as`
    returning `rs`. `none` keeps the operation or the call. -/
structure InlineLib (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] where
  /-- The body of an operation. -/
  op : (o : d.Op) → Option (NFProg d (DialectSignature.sig o) [DialectSignature.ret o])
  /-- The body of the symbol `f` at the signature `as → rs`. -/
  call : (f : String) → (as rs : List d.Ty) → Option (NFProg d as rs)

/-- **A library is sound at the fuel `fuel`**: every successful run of an operation, and of a
    callee of the call environment `CallDenote.env`, the library has a body for, is a run of
    the body at `fuel` with the same result. -/
structure InlineLib.Sound [DialectDenoteM d Option] [CallDenote d] (L : InlineLib d)
    (fuel : Nat) : Prop where
  /-- The body of an operation runs as the operation. -/
  op : ∀ (o : d.Op) b, L.op o = some b → ∀ x y,
    DialectDenoteM.denoteM (M := Option) o x = some y → b.denote fuel x = some (.cons y .nil)
  /-- The body of a symbol runs as its callee. -/
  call : ∀ f as rs b, L.call f as rs = some b → ∀ x y,
    (CallDenote.env (d := d)).call f as rs x = some y → b.denote fuel x = some y

namespace NFProg

/-- The inlining at the let-binding of the expression `e` before the continuation `k`: the
    body of the operation of `e` with the arguments of `e` substituted, followed by `k`, when
    the library has a body for it; the binding otherwise. -/
def inlineVar (L : InlineLib d) {Γ : Ctxt d} {ts : List d.Ty} :
    {t : d.Ty} → Expr d Γ t → NFProg d (t :: Γ) ts → Option (NFProg d Γ ts)
  | _, ⟨o, rfl, args⟩, k =>
      match L.op o with
      | some b => seq? k b (PRen.ofArgs args) PRen.id
      | none => some (.var ⟨o, rfl, args⟩ k)

/-- **Inlining.** Each let-binding of an operation and each `call` node the library `L` has a
    body for is replaced by the body with the arguments substituted, followed by the
    continuation; the pass descends into every region and continuation, and leaves the
    inlined bodies as they are. -/
def inline? (L : InlineLib d) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Option (NFProg d Γ ts)
  | _, _, .ret vs => some (.ret vs)
  | _, _, .var e k => (inline? L k).bind fun k' => inlineVar L e k'
  | _, _, .forLoop count inits body k =>
      (inline? L body).bind fun b' => (inline? L k).map fun k' => .forLoop count inits b' k'
  | _, _, .ifThenElse cond thn els k =>
      (inline? L thn).bind fun t' => (inline? L els).bind fun e' =>
        (inline? L k).map fun k' => .ifThenElse cond t' e' k'
  | _, _, .whileLoop inits body k =>
      (inline? L body).bind fun b' => (inline? L k).map fun k' => .whileLoop inits b' k'
  | _, _, .call (as := as) (rs := rs) f args k =>
      (inline? L k).bind fun k' =>
        match L.call f as rs with
        | some b => seq? k' b (PRen.ofArgs args) PRen.id
        | none => some (.call f args k')

/-- **Repeated inlining**: `n` rounds of `inline?`, each on the result of the previous one,
    stopping at a refusal with the program of the last round. -/
def inlineIter (L : InlineLib d) {Γ : Ctxt d} {ts : List d.Ty} :
    Nat → NFProg d Γ ts → NFProg d Γ ts
  | 0, p => p
  | n + 1, p =>
      match inline? L p with
      | some q => inlineIter L n q
      | none => p

variable [DialectDenoteM d Option] [CallDenote d]

/-- **Inlining keeps every successful run** under a library sound at the fuel `fuel`. -/
theorem denote_inline? {L : InlineLib d} {fuel : Nat} (hL : L.Sound fuel) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts} {V : Valuation Γ} {out : Valuation ts}, inline? L p = some p' →
      p.denote fuel V = some out → p'.denote fuel V = some out := by
  induction p with
  | ret vs =>
      intro p' V out hq hp
      cases hq
      exact hp
  | var e k ih =>
      intro p' V out hq hp
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
      obtain ⟨x, hx, hk⟩ := hp
      have hk'' := ih hk' hk
      obtain ⟨o, rfl, args⟩ := e
      simp only [inlineVar] at hq
      split at hq
      · rename_i b hb
        rw [denote_seq? b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V) fuel,
          hL.op o b hb _ x hx]
        exact hk''
      · cases hq
        simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exact ⟨x, hx, hk''⟩
  | forLoop count inits body k ihb ihk =>
      intro p' V out hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨acc, hacc, hk⟩ := hp
      refine ⟨acc, ?_, ihk hk' hk⟩
      obtain ⟨acc', hacc', rfl⟩ := foldlM_rel_fwd (R := Eq) _
        (fun i _ a a' c hr hc => ⟨c, by
          subst hr
          exact ihb hb' hc, rfl⟩)
        _ _ acc rfl hacc
      exact hacc'
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' V out hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨r, hr, hk⟩ := hp
      refine ⟨r, ?_, ihk hk' hk⟩
      split at hr
      · rw [if_pos ‹_›]
        exact iht ht' hr
      · rw [if_neg ‹_›]
        exact ihe he' hr
  | whileLoop inits body k ihb ihk =>
      intro p' V out hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨acc, hacc, hk⟩ := hp
      refine ⟨acc, ?_, ihk hk' hk⟩
      obtain ⟨acc', hacc', rfl⟩ := whileIter_rel_fwd (R := Eq)
        (fun a a' r hr hc => ⟨r, by
          subst hr
          exact ihb hb' hc, rfl, rfl⟩)
        _ _ _ acc rfl hacc
      exact hacc'
  | call f args k ih =>
      intro p' V out hq hp
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
      obtain ⟨r, hr, hk⟩ := hp
      have hk'' := ih hk' hk
      split at hq
      · rename_i b hb
        rw [denote_seq? b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V) fuel,
          hL.call f _ _ b hb _ r hr]
        exact hk''
      · cases hq
        simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exact ⟨r, hr, hk''⟩

/-- **Repeated inlining keeps every successful run** under a library sound at the fuel
    `fuel`. -/
theorem denote_inlineIter {L : InlineLib d} {fuel : Nat} (hL : L.Sound fuel) {Γ : Ctxt d}
    {ts : List d.Ty} :
    ∀ (n : Nat) (p : NFProg d Γ ts) {V : Valuation Γ} {out : Valuation ts},
      p.denote fuel V = some out → (p.inlineIter L n).denote fuel V = some out
  | 0, _, _, _, hp => hp
  | n + 1, p, V, out, hp => by
      simp only [inlineIter]
      split
      · rename_i q hq
        exact denote_inlineIter hL n q (denote_inline? hL p hq hp)
      · exact hp

omit [CallDenote d] in
/-- **Inlining keeps every successful run at the call environment `E`** under a library sound
    at `E` and the fuel `fuel`. -/
theorem denoteAt_inline? (E : CallEnv d) {L : InlineLib d} {fuel : Nat}
    (hL : @InlineLib.Sound d _ _ _ _ _ ⟨E⟩ L fuel) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) {p' : NFProg d Γ ts} {V : Valuation Γ} {out : Valuation ts}
    (hq : inline? L p = some p') (hp : p.denoteAt E fuel V = some out) :
    p'.denoteAt E fuel V = some out :=
  @denote_inline? d _ _ _ _ _ ⟨E⟩ L fuel hL Γ ts p p' V out hq hp

end NFProg

/-! ## 4. The chain step -/

namespace NFProgPasses

/-- `n` rounds of inlining at the library `L` as a chain step. -/
def inlineStep (L : InlineLib d) (n : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.Step (NFProg d Γ ts) (NFProg d Γ ts) :=
  ⟨"inline", fun p => some (p.inlineIter L n)⟩

/-- The certificate of repeated inlining at a library sound at the fuel `fuel`: the inlined
    program keeps every successful run, from `NFProg.denote_inlineIter`. -/
def inlineCert [DialectDenoteM d Option] [CallDenote d] {L : InlineLib d} {fuel : Nat}
    (hL : L.Sound fuel) (n : Nat) (Γ : Ctxt d) (ts : List d.Ty) :
    PassChain.StepCert (inlineStep L n Γ ts).run (nfSem fuel d Γ ts) (nfSem fuel d Γ ts) :=
  PassChain.StepCert.ofRefines _ fun p q _ _ hf hd => by
    cases hf
    exact NFProg.denote_inlineIter hL n p hd

end NFProgPasses

end CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 5. The functions of a crate as an inlining library -/

namespace CatCrypt.Crypto.Hax.NFInline

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf hax64SigOf impToNF entryEnv entryCtx)

/-- The body of the function `c` of the crate `fs` at the argument types `as` and the result
    type `r`: the program `impToNF` produces from its body over its parameters, at the call
    typing `crateSigOf fs hax64SigOf`, when the parameter types are `as` and the result type is
    `r`. -/
def crateBody (fs : List CrateFn) (c : CrateFn) (as : List NfTy) (r : NfTy) :
    Option (NFProg nfDialect as [r]) :=
  (impToNF (crateSigOf fs hax64SigOf) none (entryEnv c.params) c.body).bind fun o =>
    if h : entryCtx c.params = as ∧ o.t = r then
      some (cast (congrArg₂ (NFProg nfDialect) h.1 (congrArg (fun x => [x]) h.2)) o.prog)
    else none

/-- The body of an operation in the library of the functions `fs`: a leaf call
    `NfOp.call f as r` of the first function of `fs` named `f` has the body `crateBody`, a
    named operation the body of the operation, and no other operation has a body. -/
def crateOp (fs : List CrateFn) : (o : NfOp) → Option (NFProg nfDialect o.sig [o.ret])
  | .call f as r => (fs.find? (·.name == f)).bind fun c => crateBody fs c as r
  | .named _ o => crateOp fs o
  | _ => none

/-- **The library of the functions `fs` of a crate**: the operations of `crateOp`; no `call`
    node has a body. -/
def crateLib (fs : List CrateFn) : InlineLib nfDialect where
  op := crateOp fs
  call _ _ _ := none

end CatCrypt.Crypto.Hax.NFInline
