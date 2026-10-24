/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.FrontOps
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgModule
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak

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

`crateLib fs base` is the library of the functions `fs` of a crate over `nfDialect`: a leaf
call `NfOp.call f as r` of a function of `fs` has the body `impToNF` produces from the
function's body over its parameters, at the call typing `crateSigOf fs base`, when the
parameter types are `as` and the result type is `r`. The typing `base` of the calls of other
names is `hax64SigOf` unless given; a typing that also types the calls of linked functions
lets the bodies call them.

The builtins with the crate, `ImpToNF.crateBi fs bi fuelC m`, answer a call of a function of
`fs` at the call depth `m + 1` by the run of its body at the depth `m`. The library is
therefore sound from the depth `m + 1` to the depth `m` (`InlineLib.SoundStep`,
`crateLib_soundStep`), under a typing `TypedCalls bi base` of the builtins `bi`: a round of
inlining lowers the depth by one. A round keeps the runs of a program each of whose calls of
a function of `fs` has a body in the library; `crateInlineOk fs n` checks this at each of `n`
rounds and checks that no call of a function of `fs` is left (`noCrateCall`), so that the
program after the rounds runs at `bi` (`denote_inlineIter_crate`).

## Main definitions

* `PRen.ofArgs`, `PRen.appendVars`, `PRen.shift`, `PRen.id` — the renamings of a body's
  parameters to argument variables, of a continuation's results to returned variables, under
  further bindings, and the identity.
* `NFProg.seq?` — a body renamed into a context, followed by a continuation.
* `InlineLib`, `InlineLib.Sound` — inlining libraries and their soundness.
* `InlineLib.LeakSound` — soundness of a library for the leakage run, with a list of events
  per symbol that does not depend on the arguments.
* `NFProg.inlineVar`, `NFProg.inline?`, `NFProg.inlineIter` — inlining at one binding, in a
  program, and repeated.
* `NFProgPasses.inlineStep`, `NFProgPasses.inlineCert` — the repeated inlining as a chain step
  and its certificate.
* `NFInline.crateBody`, `NFInline.crateOp`, `NFInline.crateLib` — the bodies of the functions
  of a crate, at a leaf call and at a named leaf call.
* `InlineLib.SoundStep` — soundness of a library from one denotation of the operations to
  another.
* `InlineLib.LeakSoundStep` — soundness of a library for the leakage run from one denotation
  and event function of the operations to another.
* `NFProg.allOps`, `NFProg.HasOp`, `NFProg.inlineIterOk` — a check on every operation of a
  program, the operations of a program, and the check of the rounds of inlining.
* `NFInline.crateCallOp`, `NFInline.noCrateCall`, `NFInline.crateInlineOk` — the calls of the
  functions of a crate, their absence from a program, and the check of the rounds of inlining
  at the library of the crate.

## Main results

* `PRen.agrees_ofArgs`, `PRen.agrees_appendVars`, `PRen.agrees_shift`, `PRen.agrees_id` — the
  renamings relate the valuations they are built for.
* `NFProg.denote_seq?` — the splice denotes the body followed by the continuation.
* `NFProg.denote_inline?`, `NFProg.denoteAt_inline?` — inlining under a sound library keeps
  every successful run.
* `NFProg.denote_inlineIter` — so does the repeated inlining.
* `NFProg.leakRunMC_ev_rename?`, `NFProg.leakRunMC_ev_seq?` — the leakage run of a renamed
  program and of a splice, under an event function of the operations; `leakRunMC_rename?`
  and `leakRunMC_seq?` are their instances at a leakage model.
* `NFProg.leakRunMC_inline?` — inlining under a library sound for the leakage run whose
  bodies of symbols emit no event keeps every successful leakage run.
* `NFProg.leakRunMC_inline?_step` — inlining keeps every successful leakage run from one
  denotation and event function of the operations to another (`InlineLib.LeakSoundStep`).
* `NFProg.leakRunMC_congr_ops` — the leakage run reads the denotation and the events of the
  operations of the program only.
* `NFProg.leakRunMC_inline?_prefix` — inlining under a library sound for the leakage run with
  a fixed list of events per symbol (`InlineLib.LeakSound`) maps two runs with equal events
  to two runs with equal events.
* `NFProg.allOps_iff`, `noCrateCall_iff` — the checks on the operations of a program accept
  the programs all of whose operations pass.
* `NFProg.denote_inline?_step`, `NFProg.denote_inlineIter_step` — inlining between two
  denotations of the operations, and along a family of them.
* `enc_inj` — the encoding of the values of a type is injective.
* `crateOp_sound`, `crateLib_soundStep` — a call of a function of the crate at the depth
  `m + 1` is a run of its body at the depth `m`.
* `denote_inlineIter_crate` — a run at the builtins with the crate is a run of the inlined
  program at the builtins without it, under `crateInlineOk`.
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
      · rw [ite_eq_left ‹_›]
        exact iht ht' hr
      · rw [ite_eq_right ‹_›]
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

/-! ## 3a. Inlining keeps the leakage run at a call environment -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel opLeak Expr.ctLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (forIterLeak whileIterLeak)

variable [DialectDenoteM d Option]

/-- **A library is sound for the leakage run at `E`** at the fuel `fuel` with the events `ev`
    of the symbols: the body of an operation runs, on every argument vector on which the
    operation succeeds, to its result and to the events of the operation, and the body of the
    symbol `f` at the signature `as → rs` runs, on every argument vector on which the callee
    of `E` succeeds, to its result and to the events `ev f as rs`, which do not depend on the
    arguments. The default `ev` is the empty list at every symbol. -/
structure InlineLib.LeakSound (M : LeakModel d) (E : CallEnv d) (L : InlineLib d)
    (fuel : Nat) (ev : String → List d.Ty → List d.Ty → List CTLeak := fun _ _ _ => []) :
    Prop where
  /-- The body of an operation runs as the operation, with its events. -/
  op : ∀ (o : d.Op) b, L.op o = some b → ∀ x y,
    DialectDenoteM.denoteM (M := Option) o x = some y →
    Dialects.NFLeak.NFProg.leakRunMC M E fuel b x = some (.cons y .nil, opLeak M o x)
  /-- The body of a symbol runs as its callee, with the events of the symbol. -/
  call : ∀ f as rs b, L.call f as rs = some b → ∀ x y, E.call f as rs x = some y →
    Dialects.NFLeak.NFProg.leakRunMC M E fuel b x = some (y, ev f as rs)

namespace NFProg

open Dialects.NFLeak.NFProg (leakRunMC)

open Dialects.NFLeak (OpEvents OpEvents.toExprEv)

omit [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- A renamed expression has the events of the source under an event function of the
    operations. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.OpEvents.toExprEv_rename?
    (ev : OpEvents d) {Γ Δ : Ctxt d} {t : d.Ty} {f : PRen Γ Δ} {V : Valuation Γ}
    {W : Valuation Δ} (h : PRen.Agrees f V W) (e : Expr d Γ t) {e' : Expr d Δ t}
    (he : Expr.rename? f e = some e') :
    ev.toExprEv.ev Δ t e' W = ev.toExprEv.ev Γ t e V := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at he
  obtain ⟨args, hargs, rfl⟩ := he
  show ev e.op (Expr.lookupArgs args W) = ev e.op (Expr.lookupArgs e.args V)
  rw [PRen.lookupArgs_vars? h e.args hargs]

/-- **A renamed program has the leakage run at `E` of the source**, under the events `ev` of
    the operations. -/
theorem leakRunMC_ev_rename? (ev : OpEvents d) (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts} {V : Valuation Γ}
      {W : Valuation Δ}, NFProg.rename? f p = some p' → PRen.Agrees f V W →
      leakRunMC ev.toExprEv E fuel p' W = leakRunMC ev.toExprEv E fuel p V := by
  induction p with
  | ret vs =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at hp
      obtain ⟨ws, hws, rfl⟩ := hp
      simp only [leakRunMC, PRen.lookupArgs_vars? h vs hws]
  | var e k ih =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨e', he, k', hk, rfl⟩ := hp
      simp only [leakRunMC, Expr.denoteM_rename? h e he, OpEvents.toExprEv_rename? ev h e he]
      congr 1
      funext x
      rw [ih hk (PRen.agrees_lift h x)]
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [leakRunMC, h count c' hc, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun i acc => leakRunMC ev.toExprEv E fuel b'
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
          (fun i acc => leakRunMC ev.toExprEv E fuel body
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) V))) := by
        funext i acc
        exact ihb hb (PRen.agrees_liftApp (PRen.agrees_lift h _) _ acc)
      rw [hbody]
      congr 1
      funext acc
      rw [ihk hk (PRen.agrees_liftApp h _ acc.1)]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨c', hc, t', ht, e', he, k', hk, rfl⟩ := hp
      simp only [leakRunMC, h cond c' hc, iht ht h, ihe he h]
      congr 1
      funext r
      rw [ihk hk (PRen.agrees_liftApp h _ r.1)]
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨i', hi, b', hb, k', hk, rfl⟩ := hp
      simp only [leakRunMC, PRen.lookupArgs_vars? h inits hi]
      have hbody : (fun acc => leakRunMC ev.toExprEv E fuel b' (hvAppend acc W)) =
          (fun acc => leakRunMC ev.toExprEv E fuel body (hvAppend acc V)) := by
        funext acc
        exact ihb hb (PRen.agrees_liftApp h _ acc)
      rw [hbody]
      congr 1
      funext acc
      rw [ihk hk (PRen.agrees_liftApp h _ acc.1)]
  | call fn args k ih =>
      intro Δ f p' V W hp h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a', ha, k', hk, rfl⟩ := hp
      simp only [leakRunMC, PRen.lookupArgs_vars? h args ha]
      congr 1
      funext r
      rw [ih hk (PRen.agrees_liftApp h _ r)]

/-- **The leakage run at `E` of a splice.** When `ρ` relates `U` to `W`, `θ` relates `V₀` to
    `W`, the body runs at `U` to `r` and the continuation at the results of `r` and `V₀` to
    `s`, the splice runs at `W` to the results of `s` and the events of `r` followed by those
    of `s`; under the events `ev` of the operations. -/
theorem leakRunMC_ev_seq? (ev : OpEvents d) (E : CallEnv d) (fuel : Nat) {Δ : Ctxt d}
    {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts} {U : Valuation Δ}
      {V₀ : Valuation Γ₀} {W : Valuation Γ} {r : Valuation rs × List CTLeak}
      {s : Valuation ts × List CTLeak}, seq? k b ρ θ = some q →
      PRen.Agrees ρ U W → PRen.Agrees θ V₀ W → leakRunMC ev.toExprEv E fuel b U = some r →
      leakRunMC ev.toExprEv E fuel k (hvAppend r.1 V₀) = some s →
      leakRunMC ev.toExprEv E fuel q W = some (s.1, r.2 ++ s.2) := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff] at hq
      obtain ⟨ws, hws, hq⟩ := hq
      simp only [leakRunMC, Option.some.injEq] at hr
      subst hr
      rw [leakRunMC_ev_rename? ev E fuel k hq (PRen.agrees_appendVars hθ ws),
        PRen.lookupArgs_vars? hρ vs hws]
      rw [hs, List.nil_append]
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨e', he, b', hb, rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨x, hx, u, hu, rfl⟩ := hr
      have h' := ih k hb (PRen.agrees_lift hρ x) (PRen.agrees_shift hθ _ (.cons x .nil)) hu hs
      simp only [leakRunMC, Expr.denoteM_rename? hρ e he, hx, Option.bind_some, h',
        Option.map_some, OpEvents.toExprEv_rename? ev hρ e he, List.append_assoc]
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨c', hc, i', hi, body', hbody', b', hb, rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      have hstep : (fun i acc => leakRunMC ev.toExprEv E fuel body'
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) W))) =
          (fun i acc => leakRunMC ev.toExprEv E fuel body
            (hvAppend acc (HVector.cons (HasWord64.ofNat (d := d) i) U))) := by
        funext i acc
        exact leakRunMC_ev_rename? ev E fuel body hbody'
          (PRen.agrees_liftApp (PRen.agrees_lift hρ _) _ acc)
      have h' := ih k hb (PRen.agrees_liftApp hρ _ a.1) (PRen.agrees_shift hθ _ a.1) hu hs
      simp only [leakRunMC, hρ count c' hc, PRen.lookupArgs_vars? hρ inits hi, hstep, ha,
        Option.bind_some, h', Option.map_some, List.cons_append, List.append_assoc]
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨c', hc, t', ht, e', he, b', hb, rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      have h' := ih k hb (PRen.agrees_liftApp hρ _ a.1) (PRen.agrees_shift hθ _ a.1) hu hs
      simp only [leakRunMC, hρ cond c' hc, leakRunMC_ev_rename? ev E fuel thn ht hρ,
        leakRunMC_ev_rename? ev E fuel els he hρ, ha, Option.bind_some, h', Option.map_some,
        List.cons_append, List.append_assoc]
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨i', hi, body', hbody', b', hb, rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨a, ha, u, hu, rfl⟩ := hr
      have hstep : (fun acc => leakRunMC ev.toExprEv E fuel body' (hvAppend acc W)) =
          (fun acc => leakRunMC ev.toExprEv E fuel body (hvAppend acc U)) := by
        funext acc
        exact leakRunMC_ev_rename? ev E fuel body hbody' (PRen.agrees_liftApp hρ _ acc)
      have h' := ih k hb (PRen.agrees_liftApp hρ _ a.1) (PRen.agrees_shift hθ _ a.1) hu hs
      simp only [leakRunMC, PRen.lookupArgs_vars? hρ inits hi, hstep, ha, Option.bind_some, h',
        Option.map_some, List.append_assoc]
  | call f args b ih =>
      intro Γ₀ ts k Γ ρ θ q U V₀ W r s hq hρ hθ hr hs
      simp only [seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨a', ha, b', hb, rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at hr
      obtain ⟨y, hy, hu⟩ := hr
      have h' := ih k hb (PRen.agrees_liftApp hρ _ y) (PRen.agrees_shift hθ _ y) hu hs
      simp only [leakRunMC, PRen.lookupArgs_vars? hρ args ha, hy, Option.bind_some, h']

/-- **A renamed program has the leakage run at `E` of the source.** -/
theorem leakRunMC_rename? (M : LeakModel d) (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts}
    {V : Valuation Γ} {W : Valuation Δ} (hp : NFProg.rename? f p = some p')
    (h : PRen.Agrees f V W) : leakRunMC M E fuel p' W = leakRunMC M E fuel p V :=
  leakRunMC_ev_rename? (opLeak M) E fuel p hp h

/-- **The leakage run at `E` of a splice.** When `ρ` relates `U` to `W`, `θ` relates `V₀` to
    `W`, the body runs at `U` to `r` and the continuation at the results of `r` and `V₀` to
    `s`, the splice runs at `W` to the results of `s` and the events of `r` followed by those
    of `s`. -/
theorem leakRunMC_seq? (M : LeakModel d) (E : CallEnv d) (fuel : Nat) {Δ : Ctxt d}
    {rs : List d.Ty} (b : NFProg d Δ rs) {Γ₀ : Ctxt d} {ts : List d.Ty}
    (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d} {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ}
    {q : NFProg d Γ ts} {U : Valuation Δ} {V₀ : Valuation Γ₀} {W : Valuation Γ}
    {r : Valuation rs × List CTLeak} {s : Valuation ts × List CTLeak}
    (hq : seq? k b ρ θ = some q) (hρ : PRen.Agrees ρ U W) (hθ : PRen.Agrees θ V₀ W)
    (hr : leakRunMC M E fuel b U = some r) (hs : leakRunMC M E fuel k (hvAppend r.1 V₀) = some s) :
    leakRunMC M E fuel q W = some (s.1, r.2 ++ s.2) :=
  leakRunMC_ev_seq? (opLeak M) E fuel b k hq hρ hθ hr hs

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- The iterations of a counted loop whose second step succeeds wherever the first does,
    with the same result, succeed with the same result. -/
theorem forIterLeak_mono {cs : List d.Ty}
    (a₁ a₂ : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (h : ∀ i X r, a₁ i X = some r → a₂ i X = some r) :
    ∀ (l : List Nat) (X : Valuation cs) (r : Valuation cs × List CTLeak),
      forIterLeak a₁ l X = some r → forIterLeak a₂ l X = some r
  | [], _, _, h₁ => h₁
  | i :: l, X, r, h₁ => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ ⊢
      obtain ⟨u, hu, q, hq, rfl⟩ := h₁
      exact ⟨u, h i X u hu, q, forIterLeak_mono a₁ a₂ h l _ q hq, rfl⟩

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- The iterations of an exit-flag loop whose second body succeeds wherever the first does,
    with the same result, succeed with the same result. -/
theorem whileIterLeak_mono {cs : List d.Ty}
    (a₁ a₂ : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (h : ∀ X r, a₁ X = some r → a₂ X = some r) :
    ∀ (n : Nat) (X : Valuation cs) (r : Valuation cs × List CTLeak),
      whileIterLeak a₁ n X = some r → whileIterLeak a₂ n X = some r
  | 0, _, _, h₁ => h₁
  | n + 1, X, r, h₁ => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ ⊢
      obtain ⟨u, hu, h₁⟩ := h₁
      refine ⟨u, h X u hu, ?_⟩
      split at h₁
      · rw [ite_eq_left ‹_›]
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h₁
        rw [whileIterLeak_mono a₁ a₂ h n _ q hq, Option.map_some]
      · rw [ite_eq_right ‹_›]
        exact h₁

/-- **Inlining keeps every successful leakage run at `E`** under a library sound for the
    leakage run at `E`: the inlined program runs to the same results and the same events. -/
theorem leakRunMC_inline? (M : LeakModel d) (E : CallEnv d) {L : InlineLib d} {fuel : Nat}
    (hL : L.LeakSound M E fuel) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts} {V : Valuation Γ} {r : Valuation ts × List CTLeak},
      inline? L p = some p' → leakRunMC M E fuel p V = some r →
      leakRunMC M E fuel p' V = some r := by
  induction p with
  | ret vs =>
      intro p' V r hq hp
      cases hq
      exact hp
  | var e k ih =>
      intro p' V r hq hp
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨x, hx, s, hs, rfl⟩ := hp
      have hs' := ih hk' hs
      obtain ⟨o, rfl, args⟩ := e
      simp only [inlineVar] at hq
      split at hq
      · rename_i b hb
        exact leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V args) (PRen.agrees_id V)
          (hL.op o b hb _ x hx) hs'
      · cases hq
        simp only [leakRunMC, hx, Option.bind_some, hs', Option.map_some]
  | forLoop count inits body k ihb ihk =>
      intro p' V r hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha, s, hs, rfl⟩ := hp
      have ha' := forIterLeak_mono _ _ (fun i X r h => ihb hb' h) _ _ a ha
      simp only [leakRunMC, ha', Option.bind_some, ihk hk' hs, Option.map_some]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' V r hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha, s, hs, rfl⟩ := hp
      have ha' : (if HasBoolBit.toBool (d := d) (cond.lookup V) then leakRunMC M E fuel t' V
          else leakRunMC M E fuel e' V) = some a := by
        split at ha
        · rw [ite_eq_left ‹_›]
          exact iht ht' ha
        · rw [ite_eq_right ‹_›]
          exact ihe he' ha
      simp only [leakRunMC, ha', Option.bind_some, ihk hk' hs, Option.map_some]
  | whileLoop inits body k ihb ihk =>
      intro p' V r hq hp
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha, s, hs, rfl⟩ := hp
      have ha' := whileIterLeak_mono _ _ (fun X r h => ihb hb' h) _ _ a ha
      simp only [leakRunMC, ha', Option.bind_some, ihk hk' hs, Option.map_some]
  | call f args k ih =>
      intro p' V r hq hp
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at hp
      obtain ⟨y, hy, hs⟩ := hp
      have hs' := ih hk' hs
      split at hq
      · rename_i b hb
        have h' := leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V args)
          (PRen.agrees_id V) (hL.call f _ _ b hb _ y hy) hs'
        rw [h', List.nil_append]
      · cases hq
        simp only [leakRunMC, hy, Option.bind_some, hs']

omit [DialectSignature d] [HasWord64 d] [HasBoolBit d] [DialectDenoteM d Option] in
/-- **The iterations of two counted loops whose single iterations split, split.** When every
    pair of iterations of the steps `f₁` and `f₂` is matched by iterations of `g₁` and `g₂`
    with the same accumulators and with events that are equal, together with the lists that
    follow them, whenever the source events extended by those lists are equal, the same holds
    for the iterations over a list of indices. -/
theorem forIterLeak_prefix {cs : List d.Ty}
    (f₁ f₂ g₁ g₂ : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (h : ∀ i X₁ X₂ u₁ u₂, f₁ i X₁ = some u₁ → f₂ i X₂ = some u₂ →
      ∃ m₁ m₂, g₁ i X₁ = some (u₁.1, m₁) ∧ g₂ i X₂ = some (u₂.1, m₂) ∧
        ∀ s₁ s₂ : List CTLeak, u₁.2 ++ s₁ = u₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂) :
    ∀ (l : List Nat) (X₁ X₂ : Valuation cs) (r₁ r₂ : Valuation cs × List CTLeak),
      forIterLeak f₁ l X₁ = some r₁ → forIterLeak f₂ l X₂ = some r₂ →
      ∃ m₁ m₂, forIterLeak g₁ l X₁ = some (r₁.1, m₁) ∧ forIterLeak g₂ l X₂ = some (r₂.1, m₂) ∧
        ∀ s₁ s₂ : List CTLeak, r₁.2 ++ s₁ = r₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂
  | [], X₁, X₂, r₁, r₂, h₁, h₂ => by
      simp only [forIterLeak, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨[], [], rfl, rfl, fun s₁ s₂ hs => ⟨rfl, by simpa using hs⟩⟩
  | i :: l, X₁, X₂, r₁, r₂, h₁, h₂ => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨u₁, hu₁, q₁, hq₁, rfl⟩ := h₁
      obtain ⟨u₂, hu₂, q₂, hq₂, rfl⟩ := h₂
      obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := h i X₁ X₂ u₁ u₂ hu₁ hu₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ :=
        forIterLeak_prefix f₁ f₂ g₁ g₂ h l u₁.1 u₂.1 q₁ q₂ hq₁ hq₂
      refine ⟨m₁ ++ n₁, m₂ ++ n₂, ?_, ?_, fun s₁ s₂ hs => ?_⟩
      · simp only [forIterLeak, hm₁, hn₁, Option.bind_some, Option.map_some]
      · simp only [forIterLeak, hm₂, hn₂, Option.bind_some, Option.map_some]
      · simp only [List.append_assoc] at hs
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨rfl, rfl⟩

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- The iterations of an exit-flag loop whose body succeeds wherever a first body does, with
    the same result and some events, succeed with the same result. -/
theorem whileIterLeak_exists {cs : List d.Ty}
    (f g : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (h : ∀ X u, f X = some u → ∃ m, g X = some (u.1, m)) :
    ∀ (n : Nat) (X : Valuation cs) (r : Valuation cs × List CTLeak),
      whileIterLeak f n X = some r → ∃ m, whileIterLeak g n X = some (r.1, m)
  | 0, _, _, h₁ => by simp [whileIterLeak] at h₁
  | n + 1, X, r, h₁ => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁
      obtain ⟨u, hu, h₁⟩ := h₁
      obtain ⟨m, hm⟩ := h X u hu
      by_cases hb : HasBoolBit.toBool (d := d) u.1.head = true
      · rw [ite_eq_left hb] at h₁
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨k, hk⟩ := whileIterLeak_exists f g h n _ q hq
        exact ⟨m ++ .branch true :: k, by
          simp only [whileIterLeak, hm, Option.bind_some, hb, ite_true, hk, Option.map_some]⟩
      · rw [ite_eq_right hb] at h₁
        cases h₁
        exact ⟨m ++ [.branch false], by
          simp only [whileIterLeak, hm, Option.bind_some, hb, Bool.false_eq_true, ite_false]⟩

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- **The iterations of two exit-flag loops whose single bodies split, split**: the analogue
    of `forIterLeak_prefix` for `whileIterLeak` at a common fuel, when each target body
    succeeds wherever its source body does. The flag a body returns is an event, so two runs
    whose events split take the same number of iterations. -/
theorem whileIterLeak_prefix {cs : List d.Ty}
    (f₁ f₂ g₁ g₂ : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs) × List CTLeak))
    (e₁ : ∀ X u, f₁ X = some u → ∃ m, g₁ X = some (u.1, m))
    (e₂ : ∀ X u, f₂ X = some u → ∃ m, g₂ X = some (u.1, m))
    (h : ∀ X₁ X₂ u₁ u₂, f₁ X₁ = some u₁ → f₂ X₂ = some u₂ →
      ∃ m₁ m₂, g₁ X₁ = some (u₁.1, m₁) ∧ g₂ X₂ = some (u₂.1, m₂) ∧
        ∀ s₁ s₂ : List CTLeak, u₁.2 ++ s₁ = u₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂) :
    ∀ (n : Nat) (X₁ X₂ : Valuation cs) (r₁ r₂ : Valuation cs × List CTLeak),
      whileIterLeak f₁ n X₁ = some r₁ → whileIterLeak f₂ n X₂ = some r₂ →
      ∃ m₁ m₂, whileIterLeak g₁ n X₁ = some (r₁.1, m₁) ∧
        whileIterLeak g₂ n X₂ = some (r₂.1, m₂) ∧
        ∀ s₁ s₂ : List CTLeak, r₁.2 ++ s₁ = r₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂
  | 0, _, _, _, _, h₁, _ => by simp [whileIterLeak] at h₁
  | n + 1, X₁, X₂, r₁, r₂, h₁, h₂ => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨u₁, hu₁, h₁⟩ := h₁
      obtain ⟨u₂, hu₂, h₂⟩ := h₂
      obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := h X₁ X₂ u₁ u₂ hu₁ hu₂
      by_cases hb₁ : HasBoolBit.toBool (d := d) u₁.1.head = true <;>
        by_cases hb₂ : HasBoolBit.toBool (d := d) u₂.1.head = true
      · rw [ite_eq_left hb₁] at h₁
        rw [ite_eq_left hb₂] at h₂
        obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ :=
          whileIterLeak_prefix f₁ f₂ g₁ g₂ e₁ e₂ h n _ _ q₁ q₂ hq₁ hq₂
        refine ⟨m₁ ++ .branch true :: k₁, m₂ ++ .branch true :: k₂, ?_, ?_,
          fun s₁ s₂ hs => ?_⟩
        · simp only [whileIterLeak, hm₁, Option.bind_some, hb₁, ite_true, hk₁, Option.map_some]
        · simp only [whileIterLeak, hm₂, Option.bind_some, hb₂, ite_true, hk₂, Option.map_some]
        · simp only [List.append_assoc, List.cons_append] at hs
          obtain ⟨rfl, hs⟩ := hm _ _ hs
          obtain ⟨rfl, rfl⟩ := hk _ _ (List.cons.inj hs).2
          exact ⟨rfl, rfl⟩
      · rw [ite_eq_left hb₁] at h₁
        rw [ite_eq_right hb₂] at h₂
        obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
        cases h₂
        obtain ⟨k₁, hk₁⟩ := whileIterLeak_exists f₁ g₁ e₁ n _ q₁ hq₁
        refine ⟨m₁ ++ .branch true :: k₁, m₂ ++ [.branch false], ?_, ?_, fun s₁ s₂ hs => ?_⟩
        · simp only [whileIterLeak, hm₁, Option.bind_some, hb₁, ite_true, hk₁, Option.map_some]
        · simp only [whileIterLeak, hm₂, Option.bind_some, hb₂, Bool.false_eq_true, ite_false]
        · simp only [List.append_assoc, List.cons_append, List.nil_append] at hs
          obtain ⟨-, hs⟩ := hm _ _ hs
          simp at hs
      · rw [ite_eq_right hb₁] at h₁
        rw [ite_eq_left hb₂] at h₂
        cases h₁
        obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨k₂, hk₂⟩ := whileIterLeak_exists f₂ g₂ e₂ n _ q₂ hq₂
        refine ⟨m₁ ++ [.branch false], m₂ ++ .branch true :: k₂, ?_, ?_, fun s₁ s₂ hs => ?_⟩
        · simp only [whileIterLeak, hm₁, Option.bind_some, hb₁, Bool.false_eq_true, ite_false]
        · simp only [whileIterLeak, hm₂, Option.bind_some, hb₂, ite_true, hk₂, Option.map_some]
        · simp only [List.append_assoc, List.cons_append, List.nil_append] at hs
          obtain ⟨-, hs⟩ := hm _ _ hs
          simp at hs
      · rw [ite_eq_right hb₁] at h₁
        rw [ite_eq_right hb₂] at h₂
        cases h₁
        cases h₂
        refine ⟨m₁ ++ [.branch false], m₂ ++ [.branch false], ?_, ?_, fun s₁ s₂ hs => ?_⟩
        · simp only [whileIterLeak, hm₁, Option.bind_some, hb₁, Bool.false_eq_true, ite_false]
        · simp only [whileIterLeak, hm₂, Option.bind_some, hb₂, Bool.false_eq_true, ite_false]
        · simp only [List.append_assoc, List.cons_append, List.nil_append] at hs
          obtain ⟨rfl, hs⟩ := hm _ _ hs
          exact ⟨rfl, (List.cons.inj hs).2⟩

/-- **Inlining maps two leakage runs at `E` whose events split to two runs whose events
    split**, under a library sound for the leakage run at `E` with the events `ev`: the
    inlined program runs from each valuation to the results of the source run, and when the
    events of the two source runs, each followed by a list, are equal, the events of the two
    inlined runs are equal and so are the two lists. Taking the empty lists, inlining maps
    equal events to equal events. A body of a symbol emits the events `ev f as rs` at every
    argument vector, an operation emits a number of events fixed by the operation
    (`Expr.ctLeak_length`), and a loop or a branch first emits its trip count or its
    condition, so equal events fix the path through the program. -/
theorem leakRunMC_inline?_prefix (M : LeakModel d) (E : CallEnv d) {L : InlineLib d}
    {fuel : Nat} {ev : String → List d.Ty → List d.Ty → List CTLeak}
    (hL : L.LeakSound M E fuel ev) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts} {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation ts × List CTLeak},
      inline? L p = some p' → leakRunMC M E fuel p V₁ = some r₁ →
      leakRunMC M E fuel p V₂ = some r₂ →
      ∃ l₁ l₂, leakRunMC M E fuel p' V₁ = some (r₁.1, l₁) ∧
        leakRunMC M E fuel p' V₂ = some (r₂.1, l₂) ∧
        ∀ s₁ s₂ : List CTLeak, r₁.2 ++ s₁ = r₂.2 ++ s₂ → l₁ = l₂ ∧ s₁ = s₂ := by
  induction p with
  | ret vs =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      cases hq
      simp only [leakRunMC, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨[], [], rfl, rfl, fun s₁ s₂ hs => ⟨rfl, by simpa using hs⟩⟩
  | var e k ih =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨x₁, hx₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨x₂, hx₂, u₂, hu₂, rfl⟩ := h₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl⟩ := ih hk' hu₁ hu₂
      have hrel : ∀ s₁ s₂ : List CTLeak,
          (Expr.ctLeak M e V₁ ++ u₁.2) ++ s₁ = (Expr.ctLeak M e V₂ ++ u₂.2) ++ s₂ →
            Expr.ctLeak M e V₁ ++ l₁ = Expr.ctLeak M e V₂ ++ l₂ ∧ s₁ = s₂ := by
        intro s₁ s₂ hs
        rw [List.append_assoc, List.append_assoc] at hs
        obtain ⟨he, hs⟩ := List.append_inj hs
          (by rw [Dialects.NFLeak.Expr.ctLeak_length, Dialects.NFLeak.Expr.ctLeak_length])
        obtain ⟨rfl, rfl⟩ := hl _ _ hs
        exact ⟨by rw [he], rfl⟩
      refine ⟨Expr.ctLeak M e V₁ ++ l₁, Expr.ctLeak M e V₂ ++ l₂, ?_, ?_, hrel⟩
      all_goals
        obtain ⟨o, rfl, args⟩ := e
        simp only [inlineVar] at hq
        split at hq
      · rename_i b hb
        exact leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V₁ args) (PRen.agrees_id V₁)
          (hL.op o b hb _ x₁ hx₁) hl₁
      · cases hq
        simp only [leakRunMC, hx₁, Option.bind_some, hl₁, Option.map_some]
      · rename_i b hb
        exact leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V₂ args) (PRen.agrees_id V₂)
          (hL.op o b hb _ x₂ hx₂) hl₂
      · cases hq
        simp only [leakRunMC, hx₂, Option.bind_some, hl₂, Option.map_some]
  | forLoop count inits body k ihb ihk =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hit := fun (W₁ W₂ : Valuation _) =>
        forIterLeak_prefix
          (fun i acc => leakRunMC M E fuel body (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₁)))
          (fun i acc => leakRunMC M E fuel body (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₂)))
          (fun i acc => leakRunMC M E fuel b' (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₁)))
          (fun i acc => leakRunMC M E fuel b' (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) W₂)))
          (fun i X₁ X₂ u₁ u₂ h₁ h₂ => ihb hb' h₁ h₂)
      obtain ⟨m₁, -, hm₁, -, -⟩ := hit V₁ V₁ _ _ _ a₁ a₁ ha₁ ha₁
      obtain ⟨m₂, -, hm₂, -, -⟩ := hit V₂ V₂ _ _ _ a₂ a₂ ha₂ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hk' hu₁ hu₂
      refine ⟨.trip (HasWord64.toNat (d := d) (count.lookup V₁)) :: (m₁ ++ n₁),
        .trip (HasWord64.toNat (d := d) (count.lookup V₂)) :: (m₂ ++ n₂), ?_, ?_,
        fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
          CTLeak.trip.injEq] at hs
        obtain ⟨hc, hs⟩ := hs
        rw [← hc] at ha₂
        obtain ⟨m₁', m₂', hm₁', hm₂', hm⟩ := hit V₁ V₂ _ _ _ a₁ a₂ ha₁ ha₂
        rw [hm₁, Option.some.injEq, Prod.mk.injEq] at hm₁'
        rw [hc, hm₂, Option.some.injEq, Prod.mk.injEq] at hm₂'
        obtain ⟨-, rfl⟩ := hm₁'
        obtain ⟨-, rfl⟩ := hm₂'
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨by rw [hc], rfl⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hbr : ∀ (W₁ W₂ : Valuation _) (c : Bool) (b₁ b₂ : Valuation _ × List CTLeak),
          (if c then leakRunMC M E fuel thn W₁ else leakRunMC M E fuel els W₁) = some b₁ →
          (if c then leakRunMC M E fuel thn W₂ else leakRunMC M E fuel els W₂) = some b₂ →
          ∃ m₁ m₂, (if c then leakRunMC M E fuel t' W₁ else leakRunMC M E fuel e' W₁) =
              some (b₁.1, m₁) ∧
            (if c then leakRunMC M E fuel t' W₂ else leakRunMC M E fuel e' W₂) =
              some (b₂.1, m₂) ∧
            ∀ s₁ s₂ : List CTLeak, b₁.2 ++ s₁ = b₂.2 ++ s₂ → m₁ = m₂ ∧ s₁ = s₂ := by
        intro W₁ W₂ c b₁ b₂ h₁ h₂
        cases c
        · simp only [Bool.false_eq_true, ite_false] at h₁ h₂ ⊢
          exact ihe he' h₁ h₂
        · simp only [ite_true] at h₁ h₂ ⊢
          exact iht ht' h₁ h₂
      obtain ⟨m₁, -, hm₁, -, -⟩ := hbr V₁ V₁ _ a₁ a₁ ha₁ ha₁
      obtain ⟨m₂, -, hm₂, -, -⟩ := hbr V₂ V₂ _ a₂ a₂ ha₂ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hk' hu₁ hu₂
      refine ⟨.branch (HasBoolBit.toBool (d := d) (cond.lookup V₁)) :: (m₁ ++ n₁),
        .branch (HasBoolBit.toBool (d := d) (cond.lookup V₂)) :: (m₂ ++ n₂), ?_, ?_,
        fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.cons_append, List.append_assoc, List.cons.injEq,
          CTLeak.branch.injEq] at hs
        obtain ⟨hc, hs⟩ := hs
        rw [← hc] at ha₂ hm₂
        obtain ⟨m₁', m₂', hm₁', hm₂', hm⟩ := hbr V₁ V₂ _ a₁ a₂ ha₁ ha₂
        rw [hm₁, Option.some.injEq, Prod.mk.injEq] at hm₁'
        rw [hm₂, Option.some.injEq, Prod.mk.injEq] at hm₂'
        obtain ⟨-, rfl⟩ := hm₁'
        obtain ⟨-, rfl⟩ := hm₂'
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨by rw [hc], rfl⟩
  | whileLoop inits body k ihb ihk =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, u₁, hu₁, rfl⟩ := h₁
      obtain ⟨a₂, ha₂, u₂, hu₂, rfl⟩ := h₂
      have hex : ∀ (W : Valuation _) X u, leakRunMC M E fuel body (hvAppend X W) = some u →
          ∃ m, leakRunMC M E fuel b' (hvAppend X W) = some (u.1, m) := fun W X u hu => by
        obtain ⟨m, -, hm, -, -⟩ := ihb hb' hu hu
        exact ⟨m, hm⟩
      obtain ⟨m₁, m₂, hm₁, hm₂, hm⟩ := whileIterLeak_prefix
        (fun acc => leakRunMC M E fuel body (hvAppend acc V₁))
        (fun acc => leakRunMC M E fuel body (hvAppend acc V₂))
        (fun acc => leakRunMC M E fuel b' (hvAppend acc V₁))
        (fun acc => leakRunMC M E fuel b' (hvAppend acc V₂))
        (hex V₁) (hex V₂) (fun X₁ X₂ u₁ u₂ h₁ h₂ => ihb hb' h₁ h₂) _ _ _ a₁ a₂ ha₁ ha₂
      obtain ⟨n₁, n₂, hn₁, hn₂, hn⟩ := ihk hk' hu₁ hu₂
      refine ⟨m₁ ++ n₁, m₂ ++ n₂, ?_, ?_, fun s₁ s₂ hs => ?_⟩
      · simp only [leakRunMC, hm₁, Option.bind_some, hn₁, Option.map_some]
      · simp only [leakRunMC, hm₂, Option.bind_some, hn₂, Option.map_some]
      · simp only [List.append_assoc] at hs
        obtain ⟨rfl, hs⟩ := hm _ _ hs
        obtain ⟨rfl, rfl⟩ := hn _ _ hs
        exact ⟨rfl, rfl⟩
  | call f args k ih =>
      intro p' V₁ V₂ r₁ r₂ hq h₁ h₂
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨y₁, hy₁, hu₁⟩ := h₁
      obtain ⟨y₂, hy₂, hu₂⟩ := h₂
      obtain ⟨l₁, l₂, hl₁, hl₂, hl⟩ := ih hk' hu₁ hu₂
      split at hq
      · rename_i b hb
        refine ⟨_ ++ l₁, _ ++ l₂, leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V₁ args)
          (PRen.agrees_id V₁) (hL.call f _ _ b hb _ y₁ hy₁) hl₁,
          leakRunMC_seq? M E fuel b k' hq (PRen.agrees_ofArgs V₂ args)
          (PRen.agrees_id V₂) (hL.call f _ _ b hb _ y₂ hy₂) hl₂, fun s₁ s₂ hs => ?_⟩
        obtain ⟨rfl, rfl⟩ := hl _ _ hs
        exact ⟨rfl, rfl⟩
      · cases hq
        exact ⟨l₁, l₂, by simp only [leakRunMC, hy₁, Option.bind_some, hl₁],
          by simp only [leakRunMC, hy₂, Option.bind_some, hl₂], hl⟩

end NFProg

end Leak

/-! ## 3b. Inlining between two denotations of the operations -/

/-- **A library is sound from the denotation `D₁` to the denotation `D₂`** of the operations,
    at the fuel `fuel` and for the kept operations `P`: a successful run at `D₁` of an
    operation the library has a body for is a run of the body at `D₂` with the same result; a
    successful run at `D₁` of an operation of `P` is a run at `D₂` with the same result; and a
    callee of the call environment the library has a body for runs as the body at `D₂`. -/
structure InlineLib.SoundStep [CallDenote d] (L : InlineLib d) (D₁ D₂ : DialectDenoteM d Option)
    (P : d.Op → Bool) (fuel : Nat) : Prop where
  /-- The body of an operation runs at `D₂` as the operation at `D₁`. -/
  op : ∀ (o : d.Op) b, L.op o = some b → ∀ x y, D₁.denoteM o x = some y →
    @NFProg.denote d _ _ _ _ D₂ _ fuel _ _ b x = some (.cons y .nil)
  /-- An operation of `P` runs at `D₂` as at `D₁`. -/
  keep : ∀ (o : d.Op), P o = true → ∀ x y, D₁.denoteM o x = some y → D₂.denoteM o x = some y
  /-- The body of a symbol runs at `D₂` as its callee. -/
  call : ∀ f as rs b, L.call f as rs = some b → ∀ x y,
    (CallDenote.env (d := d)).call f as rs x = some y →
      @NFProg.denote d _ _ _ _ D₂ _ fuel _ _ b x = some y

/-- A library sound at one denotation is sound from it to itself, for every kept
    operation. -/
theorem InlineLib.Sound.soundStep [D : DialectDenoteM d Option] [CallDenote d]
    {L : InlineLib d} {fuel : Nat} (hL : L.Sound fuel) (P : d.Op → Bool) :
    L.SoundStep D D P fuel :=
  ⟨hL.op, fun _ _ _ _ h => h, hL.call⟩

namespace NFProg

/-- Every operation of a let-binding of the program, in every region and continuation,
    satisfies `P`. -/
def allOps (P : d.Op → Bool) : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => P e.op && allOps P k
  | _, _, .forLoop _ _ body k => allOps P body && allOps P k
  | _, _, .ifThenElse _ thn els k => allOps P thn && allOps P els && allOps P k
  | _, _, .whileLoop _ body k => allOps P body && allOps P k
  | _, _, .call _ _ k => allOps P k

/-- `p.HasOp o`: a let-binding of the program `p`, in a region or a continuation, is of the
    operation `o`. -/
def HasOp : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → d.Op → Prop
  | _, _, .ret _, _ => False
  | _, _, .var e k, o => e.op = o ∨ k.HasOp o
  | _, _, .forLoop _ _ body k, o => body.HasOp o ∨ k.HasOp o
  | _, _, .ifThenElse _ thn els k, o => thn.HasOp o ∨ els.HasOp o ∨ k.HasOp o
  | _, _, .whileLoop _ body k, o => body.HasOp o ∨ k.HasOp o
  | _, _, .call _ _ k, o => k.HasOp o

/-- `allOps P` accepts the programs all of whose operations satisfy `P`. -/
theorem allOps_iff (P : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    p.allOps P = true ↔ ∀ o, p.HasOp o → P o = true := by
  induction p with
  | ret vs => simp [allOps, HasOp]
  | var e k ih =>
      simp only [allOps, HasOp, Bool.and_eq_true, ih]
      exact ⟨fun h o ho => ho.elim (fun he => he ▸ h.1) (h.2 o),
        fun h => ⟨h _ (Or.inl rfl), fun o ho => h o (Or.inr ho)⟩⟩
  | forLoop count inits body k ihb ihk =>
      simp only [allOps, HasOp, Bool.and_eq_true, ihb, ihk]
      exact ⟨fun h o ho => ho.elim (h.1 o) (h.2 o),
        fun h => ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [allOps, HasOp, Bool.and_eq_true, iht, ihe, ihk]
      exact ⟨fun h o ho => ho.elim (h.1.1 o) fun ho => ho.elim (h.1.2 o) (h.2 o),
        fun h => ⟨⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr (Or.inl ho))⟩,
          fun o ho => h o (Or.inr (Or.inr ho))⟩⟩
  | whileLoop inits body k ihb ihk =>
      simp only [allOps, HasOp, Bool.and_eq_true, ihb, ihk]
      exact ⟨fun h o ho => ho.elim (h.1 o) (h.2 o),
        fun h => ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩⟩
  | call f args k ih => simp only [allOps, HasOp, ih]

/-- **A program denotes the same at two denotations that agree on its operations.** -/
theorem denote_congr_ops [CallDenote d] (D₁ D₂ : DialectDenoteM d Option) (P : d.Op → Bool)
    (hP : ∀ o, P o = true → ∀ x, D₁.denoteM o x = D₂.denoteM o x) (fuel : Nat) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : p.allOps P = true) (V : Valuation Γ) :
    @denote d _ _ _ _ D₁ _ fuel _ _ p V = @denote d _ _ _ _ D₂ _ fuel _ _ p V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [allOps, Bool.and_eq_true] at hp
      obtain ⟨o, rfl, args⟩ := e
      simp only [denote]
      rw [show @Expr.denoteM d Option _ _ D₁ _ _ ⟨o, rfl, args⟩ V =
          @Expr.denoteM d Option _ _ D₂ _ _ ⟨o, rfl, args⟩ V from hP o hp.1 _]
      congr 1
      funext x
      exact ih hp.2 _
  | forLoop count inits body k ihb ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [denote, fun acc i => ihb hp.1 (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)),
        fun acc => ihk hp.2 (hvAppend acc V)]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [denote, iht hp.1.1, ihe hp.1.2, fun r => ihk hp.2 (hvAppend r V)]
  | whileLoop inits body k ihb ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [denote, fun acc => ihb hp.1 (hvAppend acc V), fun acc => ihk hp.2 (hvAppend acc V)]
  | call f args k ih =>
      simp only [allOps] at hp
      simp only [denote, fun r => ih hp (hvAppend r V)]

/-- **Inlining keeps every successful run, from the denotation `D₁` to the denotation `D₂`**,
    under a library sound from `D₁` to `D₂` for the kept operations `P`, on a program each of
    whose operations the library has a body for or is of `P`. -/
theorem denote_inline?_step [CallDenote d] {L : InlineLib d} {D₁ D₂ : DialectDenoteM d Option}
    {P : d.Op → Bool} {fuel : Nat} (hL : L.SoundStep D₁ D₂ P fuel) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts} {V : Valuation Γ} {out : Valuation ts},
      p.allOps (fun o => (L.op o).isSome || P o) = true → inline? L p = some p' →
      @denote d _ _ _ _ D₁ _ fuel _ _ p V = some out →
      @denote d _ _ _ _ D₂ _ fuel _ _ p' V = some out := by
  induction p with
  | ret vs =>
      intro p' V out _ hq hp
      cases hq
      exact hp
  | var e k ih =>
      intro p' V out ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
      obtain ⟨x, hx, hk⟩ := hp
      have hk'' := ih ha.2 hk' hk
      obtain ⟨o, rfl, args⟩ := e
      simp only [inlineVar] at hq
      split at hq
      · rename_i b hb
        rw [@denote_seq? d _ _ _ _ D₂ _ _ _ b _ _ k' _ _ _ _ _ _ _ hq (PRen.agrees_ofArgs V args)
          (PRen.agrees_id V) fuel, hL.op o b hb _ x hx]
        exact hk''
      · rename_i hb
        cases hq
        simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff]
        have hPo : P o = true := by
          have h := ha.1
          simp only [hb, Option.isSome_none, Bool.false_or] at h
          exact h
        exact ⟨x, hL.keep o hPo _ x hx, hk''⟩
  | forLoop count inits body k ihb ihk =>
      intro p' V out ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨acc, hacc, hk⟩ := hp
      refine ⟨acc, ?_, ihk ha.2 hk' hk⟩
      obtain ⟨acc', hacc', rfl⟩ := foldlM_rel_fwd (R := Eq) _
        (fun i _ a a' c hr hc => ⟨c, by
          subst hr
          exact ihb ha.1 hb' hc, rfl⟩)
        _ _ acc rfl hacc
      exact hacc'
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' V out ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨r, hr, hk⟩ := hp
      refine ⟨r, ?_, ihk ha.2 hk' hk⟩
      split at hr
      · rw [ite_eq_left ‹_›]
        exact iht ha.1.1 ht' hr
      · rw [ite_eq_right ‹_›]
        exact ihe ha.1.2 he' hr
  | whileLoop inits body k ihb ihk =>
      intro p' V out ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp ⊢
      obtain ⟨acc, hacc, hk⟩ := hp
      refine ⟨acc, ?_, ihk ha.2 hk' hk⟩
      obtain ⟨acc', hacc', rfl⟩ := whileIter_rel_fwd (R := Eq)
        (fun a a' r hr hc => ⟨r, by
          subst hr
          exact ihb ha.1 hb' hc, rfl, rfl⟩)
        _ _ _ acc rfl hacc
      exact hacc'
  | call f args k ih =>
      intro p' V out ha hq hp
      simp only [allOps] at ha
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
      obtain ⟨r, hr, hk⟩ := hp
      have hk'' := ih ha hk' hk
      split at hq
      · rename_i b hb
        rw [@denote_seq? d _ _ _ _ D₂ _ _ _ b _ _ k' _ _ _ _ _ _ _ hq (PRen.agrees_ofArgs V args)
          (PRen.agrees_id V) fuel, hL.call f _ _ b hb _ r hr]
        exact hk''
      · cases hq
        simp only [denote, Option.bind_eq_bind, Option.bind_eq_some_iff]
        exact ⟨r, hr, hk''⟩

end NFProg

section LeakStep

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (OpEvents OpEvents.toExprEv)
open Dialects.NFLeak.NFProg (leakRunMC)

/-- **A library is sound for the leakage run from the denotation `D₁` and the events `ev₁` to
    the denotation `D₂` and the events `ev₂`**, at the call environment `E`, the fuel `fuel`
    and for the kept operations `P`: the body of an operation runs at `D₂` and `ev₂`, on every
    argument vector on which the operation succeeds at `D₁`, to its result and to the events
    `ev₁` of the operation; an operation of `P` runs at `D₂` as at `D₁`, with the same events;
    and the body of a symbol runs at `D₂` and `ev₂` as its callee in `E`, with no event. -/
structure InlineLib.LeakSoundStep (L : InlineLib d) (D₁ D₂ : DialectDenoteM d Option)
    (ev₁ ev₂ : OpEvents d) (E : CallEnv d) (P : d.Op → Bool) (fuel : Nat) : Prop where
  /-- The body of an operation runs at `D₂` as the operation at `D₁`, with its events. -/
  op : ∀ (o : d.Op) b, L.op o = some b → ∀ x y, D₁.denoteM o x = some y →
    @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ b x = some (.cons y .nil, ev₁ o x)
  /-- An operation of `P` runs at `D₂` as at `D₁`, with the same events. -/
  keep : ∀ (o : d.Op), P o = true → ∀ x y, D₁.denoteM o x = some y →
    D₂.denoteM o x = some y ∧ ev₂ o x = ev₁ o x
  /-- The body of a symbol runs at `D₂` as its callee, with no event. -/
  call : ∀ f as rs b, L.call f as rs = some b → ∀ x y, E.call f as rs x = some y →
    @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ b x = some (y, [])

namespace NFProg

/-- **Inlining keeps every successful leakage run, from the denotation `D₁` and the events
    `ev₁` to the denotation `D₂` and the events `ev₂`**, under a library sound for the leakage
    run from the one to the other for the kept operations `P`, on a program each of whose
    operations the library has a body for or is of `P`: the inlined program runs to the same
    results and the same events. -/
theorem leakRunMC_inline?_step {L : InlineLib d} {D₁ D₂ : DialectDenoteM d Option}
    {ev₁ ev₂ : OpEvents d} {E : CallEnv d} {P : d.Op → Bool} {fuel : Nat}
    (hL : L.LeakSoundStep D₁ D₂ ev₁ ev₂ E P fuel) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts} {V : Valuation Γ} {r : Valuation ts × List CTLeak},
      p.allOps (fun o => (L.op o).isSome || P o) = true → inline? L p = some p' →
      @leakRunMC d _ _ _ _ D₁ ev₁.toExprEv E fuel _ _ p V = some r →
      @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ p' V = some r := by
  induction p with
  | ret vs =>
      intro p' V r _ hq hp
      cases hq
      exact hp
  | var e k ih =>
      intro p' V r ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨x, hx, s, hs, rfl⟩ := hp
      have hs' := ih ha.2 hk' hs
      obtain ⟨o, rfl, args⟩ := e
      simp only [inlineVar] at hq
      split at hq
      · rename_i b hb
        exact @leakRunMC_ev_seq? d _ _ _ _ D₂ ev₂ E fuel _ _ b _ _ k' _ _ _ _ _ _ _ _ _ hq
          (PRen.agrees_ofArgs V args) (PRen.agrees_id V) (hL.op o b hb _ x hx) hs'
      · rename_i hb
        cases hq
        have hPo : P o = true := by
          have h := ha.1
          simp only [hb, Option.isSome_none, Bool.false_or] at h
          exact h
        obtain ⟨hx', hev⟩ := hL.keep o hPo _ x hx
        simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff]
        refine ⟨x, hx', s, hs', ?_⟩
        show (s.1, ev₂ o (Expr.lookupArgs args V) ++ s.2) =
          (s.1, ev₁ o (Expr.lookupArgs args V) ++ s.2)
        rw [hev]
  | forLoop count inits body k ihb ihk =>
      intro p' V r ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha', s, hs, rfl⟩ := hp
      have ha'' := forIterLeak_mono _ _ (fun i X r h => ihb ha.1 hb' h) _ _ a ha'
      simp only [leakRunMC, ha'', Option.bind_some, ihk ha.2 hk' hs, Option.map_some]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' V r ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha', s, hs, rfl⟩ := hp
      have ha'' : (if HasBoolBit.toBool (d := d) (cond.lookup V) then
          @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ t' V
          else @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ e' V) = some a := by
        split at ha'
        · rw [ite_eq_left ‹_›]
          exact iht ha.1.1 ht' ha'
        · rw [ite_eq_right ‹_›]
          exact ihe ha.1.2 he' ha'
      simp only [leakRunMC, ha'', Option.bind_some, ihk ha.2 hk' hs, Option.map_some]
  | whileLoop inits body k ihb ihk =>
      intro p' V r ha hq hp
      simp only [allOps, Bool.and_eq_true] at ha
      simp only [inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨b', hb', k', hk', rfl⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
      obtain ⟨a, ha', s, hs, rfl⟩ := hp
      have ha'' := whileIterLeak_mono _ _ (fun X r h => ihb ha.1 hb' h) _ _ a ha'
      simp only [leakRunMC, ha'', Option.bind_some, ihk ha.2 hk' hs, Option.map_some]
  | call f args k ih =>
      intro p' V r ha hq hp
      simp only [allOps] at ha
      simp only [inline?, Option.bind_eq_some_iff] at hq
      obtain ⟨k', hk', hq⟩ := hq
      simp only [leakRunMC, Option.bind_eq_some_iff] at hp
      obtain ⟨y, hy, hs⟩ := hp
      have hs' := ih ha hk' hs
      split at hq
      · rename_i b hb
        have h' := @leakRunMC_ev_seq? d _ _ _ _ D₂ ev₂ E fuel _ _ b _ _ k' _ _ _ _ _ _ _ _ _ hq
          (PRen.agrees_ofArgs V args) (PRen.agrees_id V) (hL.call f _ _ b hb _ y hy) hs'
        rw [h', List.nil_append]
      · cases hq
        simp only [leakRunMC, hy, Option.bind_some, hs']

/-- **The leakage run reads the denotation and the events of the operations of the program
    only**: two denotations and two event functions that agree at every operation of `P`
    give the same leakage run of a program all of whose operations are of `P`. -/
theorem leakRunMC_congr_ops (D₁ D₂ : DialectDenoteM d Option) (ev₁ ev₂ : OpEvents d)
    (P : d.Op → Bool)
    (hP : ∀ o, P o = true → ∀ x, D₁.denoteM o x = D₂.denoteM o x ∧ ev₁ o x = ev₂ o x)
    (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.allOps P = true) (V : Valuation Γ) :
    @leakRunMC d _ _ _ _ D₁ ev₁.toExprEv E fuel _ _ p V =
      @leakRunMC d _ _ _ _ D₂ ev₂.toExprEv E fuel _ _ p V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [allOps, Bool.and_eq_true] at hp
      obtain ⟨o, rfl, args⟩ := e
      simp only [leakRunMC]
      rw [show @Expr.denoteM d Option _ _ D₁ _ _ ⟨o, rfl, args⟩ V =
          @Expr.denoteM d Option _ _ D₂ _ _ ⟨o, rfl, args⟩ V from (hP o hp.1 _).1]
      have hev : ev₁.toExprEv.ev _ _ (⟨o, rfl, args⟩ : Expr d _ _) V =
          ev₂.toExprEv.ev _ _ (⟨o, rfl, args⟩ : Expr d _ _) V := (hP o hp.1 _).2
      rw [hev]
      congr 1
      funext x
      rw [ih hp.2 _]
  | forLoop count inits body k ihb ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [leakRunMC,
        fun acc i => ihb hp.1 (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)),
        fun acc => ihk hp.2 (hvAppend acc V)]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [leakRunMC, iht hp.1.1, ihe hp.1.2, fun r => ihk hp.2 (hvAppend r V)]
  | whileLoop inits body k ihb ihk =>
      simp only [allOps, Bool.and_eq_true] at hp
      simp only [leakRunMC, fun acc => ihb hp.1 (hvAppend acc V),
        fun acc => ihk hp.2 (hvAppend acc V)]
  | call f args k ih =>
      simp only [allOps] at hp
      simp only [leakRunMC, fun r => ih hp (hvAppend r V)]

end NFProg

end LeakStep

namespace NFProg

/-- **The check of repeated inlining**: at each of the `n` rounds, every operation of the
    program of the round has a body in the library `L` or is of `P`, and the round does not
    refuse. -/
def inlineIterOk (L : InlineLib d) (P : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} :
    Nat → NFProg d Γ ts → Bool
  | 0, _ => true
  | n + 1, p =>
      p.allOps (fun o => (L.op o).isSome || P o) &&
        match inline? L p with
        | some q => inlineIterOk L P n q
        | none => false

/-- **Repeated inlining keeps every successful run, along a family of denotations.** Let the
    library be sound from the denotation `D (m + 1)` to the denotation `D m`, for every `m`.
    On a program accepted by `inlineIterOk L P n`, a successful run at `D n` is a run of the
    program after `n` rounds at `D 0` with the same result. -/
theorem denote_inlineIter_step [CallDenote d] {L : InlineLib d}
    (D : Nat → DialectDenoteM d Option) {P : d.Op → Bool} {fuel : Nat}
    (hL : ∀ m, L.SoundStep (D (m + 1)) (D m) P fuel) {Γ : Ctxt d} {ts : List d.Ty} :
    ∀ (n : Nat) (p : NFProg d Γ ts) {V : Valuation Γ} {out : Valuation ts},
      p.inlineIterOk L P n = true → @denote d _ _ _ _ (D n) _ fuel _ _ p V = some out →
      @denote d _ _ _ _ (D 0) _ fuel _ _ (p.inlineIter L n) V = some out
  | 0, _, _, _, _, hp => hp
  | n + 1, p, V, out, hok, hp => by
      simp only [inlineIterOk, Bool.and_eq_true] at hok
      obtain ⟨ha, hok⟩ := hok
      simp only [inlineIter]
      split at hok
      · rename_i q hq
        exact denote_inlineIter_step D hL n q hok (denote_inline?_step (hL n) p ha hq hp)
      · cases hok

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
    typing `crateSigOf fs base`, when the body has no `whileFold` (`ImpToNF.whileFoldFree`),
    the parameter types are `as` and the result type is `r`.
    The typing `base` of the calls of names of no function of `fs` is `hax64SigOf` unless
    given. -/
def crateBody (fs : List CrateFn) (c : CrateFn) (as : List NfTy) (r : NfTy)
    (base : String → List NfTy → Option NfTy := hax64SigOf) :
    Option (NFProg nfDialect as [r]) :=
  if ImpToNF.whileFoldFree c.body then
    (impToNF (crateSigOf fs base) none (entryEnv c.params) c.body).bind fun o =>
      if h : entryCtx c.params = as ∧ o.t = r then
        some (cast (congrArg₂ (NFProg nfDialect) h.1 (congrArg (fun x => [x]) h.2)) o.prog)
      else none
  else none

/-- The body of a function of the crate has no `whileFold` when `crateBody` returns one. -/
theorem whileFoldFree_of_crateBody {fs : List CrateFn} {c : CrateFn} {as : List NfTy}
    {r : NfTy} {base : String → List NfTy → Option NfTy} {b : NFProg nfDialect as [r]}
    (hb : crateBody fs c as r base = some b) : ImpToNF.whileFoldFree c.body = true := by
  by_contra hn
  simp [crateBody, hn] at hb

/-- The body of an operation in the library of the functions `fs` at the typing `base` of the
    other calls: a leaf call `NfOp.call f as r` of the first function of `fs` named `f` has the
    body `crateBody`, a named operation the body of the operation, and no other operation has a
    body. -/
def crateOp (fs : List CrateFn) : (o : NfOp) →
    (base : String → List NfTy → Option NfTy := hax64SigOf) →
      Option (NFProg nfDialect o.sig [o.ret])
  | .call f as r, base => (fs.find? (·.name == f)).bind fun c => crateBody fs c as r base
  | .named _ o, base => crateOp fs o base
  | _, _ => none

/-- **The library of the functions `fs` of a crate** at the typing `base` of the other calls:
    the operations of `crateOp`; no `call` node has a body. -/
def crateLib (fs : List CrateFn) (base : String → List NfTy → Option NfTy := hax64SigOf) :
    InlineLib nfDialect where
  op o := crateOp fs o base
  call _ _ _ := none

/-! ## 6. The library of a crate is sound along the call depth -/

open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll tailVals tableOf TypedCalls crateBi
  crateBi_of_find_none crateBi_typedCalls paramsEnv EnvRel NfEnv PDenP PDenP_plug_ret
  impToNF_sound dec_sound Out RepeatCalls crateBi_repeatCalls)
open _root_.Hax (Builtins Value Env denote')
open Ctxt (Var Valuation)

/-- The components `tailVals` reads off an encoding determine the encoding. -/
theorem tailVals_enc_inj : ∀ (t : NfTy) (x y : t.denote),
    tailVals (enc t x) = tailVals (enc t y) → enc t x = enc t y := by
  intro t x y h
  cases t <;> simp_all [enc, tailVals]

/-- **The encoding of the values of a type is injective.** -/
theorem enc_inj : ∀ (t : NfTy) (x y : t.denote), enc t x = enc t y → x = y
  | .bit, x, y, h => by simpa [enc] using h
  | .unit, _, _, _ => rfl
  | .word _, x, y, h => by
      simp only [enc, Value.int.injEq, Int.natCast_inj] at h
      exact BitVec.eq_of_toNat_eq h
  | .arr _ t, f, g, h => by
      simp only [enc, Value.array.injEq] at h
      funext i
      exact enc_inj t _ _ (congrFun (List.ofFn_injective h) i)
  | .pair a b, p, q, h => by
      simp only [enc, Value.tuple.injEq, List.cons.injEq, and_true] at h
      exact Prod.ext (enc_inj a _ _ h.1) (enc_inj b _ _ h.2)
  | .uint _, x, y, h => by
      simp only [enc, Value.uint.injEq, true_and] at h
      exact BitVec.eq_of_toNat_eq h
  | .sint _, x, y, h => by
      simp only [enc, Value.sint.injEq, true_and] at h
      exact BitVec.eq_of_toInt_eq h
  | .int, x, y, h => by simpa [enc] using h
  | .tnil, _, _, _ => rfl
  | .tcons a t, p, q, h => by
      simp only [enc, Value.tuple.injEq, List.cons.injEq] at h
      exact Prod.ext (enc_inj a _ _ h.1) (enc_inj t _ _ (tailVals_enc_inj t _ _ h.2))
  | .slice t, xs, ys, h => by
      simp only [enc, Value.array.injEq] at h
      exact List.map_injective_iff.mpr (fun a b => enc_inj t a b) h

/-- **The names of the parameters read their argument values.** The environment of names
    of the parameters `ps` is related to a valuation `V` of the parameters by the source
    environment `paramsEnv` binding the names of `ps` to the encodings of `V`. -/
theorem entryEnv_rel_paramsEnv : ∀ (ps : List (String × NfTy)) (V : Valuation (entryCtx ps)),
    EnvRel (entryEnv ps) (paramsEnv (ps.map (·.1)) (encAll (entryCtx ps) V)) V
  | [], .nil => by
      intro x t v hx
      simp [entryEnv, NfEnv.lookup] at hx
  | (x, t) :: ps, .cons y V => by
      intro x' t' v hx'
      change NfEnv.lookup ((x, ⟨t, Var.here⟩) ::
        NfEnv.mapV (fun v => Var.there v) (entryEnv ps)) x' = _ at hx'
      rw [ImpToNF.NfEnv.lookup_cons] at hx'
      show (if x' = x then some (enc t y) else
        paramsEnv (ps.map (·.1)) (encAll (entryCtx ps) V) x') = _
      split at hx'
      · rename_i hxx
        subst hxx
        cases hx'
        rw [ite_eq_left rfl]
        rfl
      · rename_i hxx
        rw [ite_eq_right fun h => hxx h.symm]
        exact EnvRel.mapV (entryEnv_rel_paramsEnv ps V) (fun v => Var.there v)
          (W := .cons y V) (fun _ _ => rfl) x' t' v hx'

/-- **An operation calls a function of the crate `fs`**: a leaf call `NfOp.call f as r`, under
    any number of names, of a name a function of `fs` has. -/
def crateCallOp (fs : List CrateFn) : NfOp → Bool
  | .call f _ _ => (fs.find? (·.name == f)).isSome
  | .named _ o => crateCallOp fs o
  | _ => false

/-- **No call of a function of the crate `fs` is in the program `p`**: no let-binding of `p`,
    in a region or a continuation, is of an operation of `crateCallOp fs`. -/
def noCrateCall (fs : List CrateFn) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Bool :=
  p.allOps fun o => !crateCallOp fs o

/-- `noCrateCall fs` accepts the programs none of whose operations calls a function of
    `fs`. -/
theorem noCrateCall_iff (fs : List CrateFn) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    noCrateCall fs p = true ↔ ∀ o, p.HasOp o → crateCallOp fs o = false := by
  simp only [noCrateCall, NFProg.allOps_iff, Bool.not_eq_true']

/-- A program accepted by `noCrateCall fs` has no leaf call of a name of `fs`. -/
theorem noCrateCall_call {fs : List CrateFn} {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p : NFProg nfDialect Γ ts} (h : noCrateCall fs p = true) {f : String} {as : List NfTy}
    {r : NfTy} (hp : p.HasOp (.call f as r)) : fs.find? (·.name == f) = none := by
  have := (noCrateCall_iff fs p).mp h _ hp
  simpa [crateCallOp] using this

/-- **An operation that calls no function of the crate denotes at the builtins with the crate
    as at the builtins `bi`**, at every call depth. -/
theorem nfDenoteOp_crateBi (fs : List CrateFn) (bi : Builtins) (fuelC m : Nat) :
    ∀ (o : NfOp), crateCallOp fs o = false → ∀ x,
      nfDenoteOp (tableOf (crateBi fs bi fuelC m)) o x = nfDenoteOp (tableOf bi) o x := by
  intro o
  induction o with
  | call f as r =>
      intro h x
      simp only [crateCallOp, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [nfDenoteOp, tableOf, crateBi_of_find_none fs bi fuelC m h]
  | named _ o ih =>
      intro h x
      exact ih h x
  | _ =>
      intro _ _
      rfl

/-- **A call of a function of the crate at depth `m + 1` is a run of its body at depth `m`.**
    Under a typing `base` of the builtins `bi`, `RepeatCalls bi` and no function of the crate
    named `repeat`, a successful run of an operation `crateOp fs`
    has a body for at the typing `base`, at the builtins with the crate to the call depth
    `m + 1`, is a run of the body at the builtins with the crate to the call depth `m`, at
    every fuel `tf`, with the same result. -/
theorem crateOp_sound (fs : List CrateFn) (bi : Builtins)
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC m tf : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o base = some b → ∀ x y,
      nfDenoteOp (tableOf (crateBi fs bi fuelC (m + 1))) o x = some y →
        PDenP (crateBi fs bi fuelC m) tf b x = some (.cons y .nil) := by
  intro o
  induction o with
  | call f as r =>
      intro b hb x y hy
      simp only [crateOp, Option.bind_eq_some_iff] at hb
      obtain ⟨c, hc, hb⟩ := hb
      have hwf := whileFoldFree_of_crateBody hb
      simp only [crateBody, hwf, ite_true, Option.bind_eq_some_iff] at hb
      obtain ⟨o', ho', hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        obtain ⟨rfl, rfl⟩ := hty
        simp only [nfDenoteOp, tableOf, crateBi, hc, Option.bind_eq_some_iff] at hy
        obtain ⟨v, hv, hd⟩ := hy
        split at hv
        · rename_i v' hrun
          split at hv
          · cases hv
            have hw : o'.prog.whileFree = true :=
              SecureCompilation.Haxc.FrontComplete.whileFree_of_opsNB _
                (SecureCompilation.Haxc.FrontComplete.impToNF_prog_frontOp _ c.body none _ o' ho'
                  hwf)
            obtain ⟨W, hprog, -, hvW⟩ := ImpToNF.Sound.all_of_whileFree (impToNF_sound
              (crateBi fs bi fuelC m) (crateSigOf fs base) (crateBi_typedCalls fs bi base hT fuelC m)
              (crateBi_repeatCalls fs bi hR hfR fuelC m) c.body none (entryEnv c.params) ho' fuelC)
              hw (entryEnv_rel_paramsEnv c.params x) (Prod.ext hrun rfl)
            have hy' : y = o'.res.lookup W :=
              enc_inj _ _ _ ((dec_sound _ _ _ hd).symm.trans hvW)
            subst hy'
            exact hprog tf
          · cases hv
        · cases hv
      · cases hb
  | named _ o ih =>
      intro b hb x y hy
      exact ih b hb x y hy
  | _ =>
      intro b hb
      cases hb

/-- **The library of a crate is sound from the call depth `m + 1` to the call depth `m`**,
    for the operations that call no function of the crate, under a typing `base` of the
    builtins `bi` with `RepeatCalls bi`, no function of the crate named `repeat`, and at
    every fuel `tf`. -/
theorem crateLib_soundStep (fs : List CrateFn) (bi : Builtins)
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC m tf : Nat) :
    (crateLib fs base).SoundStep (nfDenote (tableOf (crateBi fs bi fuelC (m + 1))))
      (nfDenote (tableOf (crateBi fs bi fuelC m))) (fun o => !crateCallOp fs o) tf where
  op := crateOp_sound fs bi hT hR hfR fuelC m tf
  keep o ho x y h := by
    simp only [Bool.not_eq_true'] at ho
    simp only [nfDenote_denoteM] at h ⊢
    rw [nfDenoteOp_crateBi fs bi fuelC m o ho]
    rwa [nfDenoteOp_crateBi fs bi fuelC (m + 1) o ho] at h
  call _ _ _ _ hb := by cases hb

/-- **The check of `n` rounds of inlining at the library of the crate `fs`** at the typing
    `base` of the other calls: at each round every call of a function of `fs` in the program of
    the round has a body in `crateLib fs base` and the round does not refuse, and no call of a
    function of `fs` is in the program after the `n` rounds. -/
def crateInlineOk (fs : List CrateFn) (n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (base : String → List NfTy → Option NfTy := hax64SigOf) :
    Bool :=
  p.inlineIterOk (crateLib fs base) (fun o => !crateCallOp fs o) n &&
    noCrateCall fs (p.inlineIter (crateLib fs base) n)

/-- A program accepted by `crateInlineOk fs n` has no call of a function of `fs` after the
    `n` rounds. -/
theorem crateInlineOk_noCrateCall {fs : List CrateFn} {n : Nat} {Γ : Ctxt nfDialect}
    {ts : List NfTy} {p : NFProg nfDialect Γ ts} {base : String → List NfTy → Option NfTy}
    (h : crateInlineOk fs n p base = true) :
    noCrateCall fs (p.inlineIter (crateLib fs base) n) = true :=
  (Bool.and_eq_true_iff.mp h).2

/-- **A program without calls of the crate denotes at the builtins with the crate as at the
    builtins `bi`**, at every call depth. -/
theorem PDenP_crateBi_of_noCrateCall (fs : List CrateFn) (bi : Builtins) (fuelC m tf : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : noCrateCall fs p = true) (V : Valuation Γ) :
    PDenP (crateBi fs bi fuelC m) tf p V = PDenP bi tf p V :=
  NFProg.denote_congr_ops (nfDenote (tableOf (crateBi fs bi fuelC m))) (nfDenote (tableOf bi))
    (fun o => !crateCallOp fs o)
    (fun o ho x => nfDenoteOp_crateBi fs bi fuelC m o (by simpa using ho) x) tf p hp V

/-- **Inlining at the library of a crate keeps every successful run, from the builtins with
    the crate to the builtins without it.** Under a typing `base` of the builtins `bi`,
    `RepeatCalls bi` and no function of the crate named `repeat`, on a
    program accepted by `crateInlineOk fs n` at `base`, a successful run at the builtins with
    the crate to the call depth `n` (the functions of `fs` run their bodies at the fuel
    `fuelC`) is a run of the program after `n` rounds of inlining at the builtins `bi`, with
    the same result. -/
theorem denote_inlineIter_crate (fs : List CrateFn) (bi : Builtins)
    {base : String → List NfTy → Option NfTy} (hT : TypedCalls bi base) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC tf n : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hok : crateInlineOk fs n p base = true) {V : Valuation Γ}
    {out : Valuation (d := nfDialect) ts}
    (hp : PDenP (crateBi fs bi fuelC n) tf p V = some out) :
    PDenP bi tf (p.inlineIter (crateLib fs base) n) V = some out := by
  obtain ⟨hit, hno⟩ := Bool.and_eq_true_iff.mp hok
  rw [← PDenP_crateBi_of_noCrateCall fs bi fuelC 0 tf _ hno V]
  exact NFProg.denote_inlineIter_step
    (fun m => nfDenote (tableOf (crateBi fs bi fuelC m)))
    (fun m => crateLib_soundStep fs bi hT hR hfR fuelC m tf) n p hit hp

end CatCrypt.Crypto.Hax.NFInline
