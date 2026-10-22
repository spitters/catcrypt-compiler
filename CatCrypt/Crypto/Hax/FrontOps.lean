/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.FrontDomain

/-!
# The operations of the front's output

The operations a program of the front `impToNF` contains, and the absence of exit-flag loops
and `call` nodes in it.

## Main definitions and results

* `NFToCatComplete.ilitOk` — the integer literals in `[0, 2^64)` at an integer, a `64`-bit
  word or an unsigned integer of at most `64` bits.
* `opsNB`, `preOps` — every operation of a program (of a prefix) satisfies a predicate, and
  the program has no exit-flag loop and no `call` node.
* `whileFree_of_opsNB` — a program of `opsNB P` has no exit-flag loop.
* `opsNB_rename?`, `opsNB_dce`, `opsNB_plug` — renaming, dead-binding elimination and
  plugging keep `opsNB`.
* `frontOp` — the operations of the front at a call typing.
* `impToNF_frontOp`, `impToNF_prog_frontOp` — every operation of the output of `impToNF S`
  satisfies `frontOp S`, and its program is a program of `opsNB (frontOp S)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCatComplete

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect

/-- The integer literals in `[0, 2^64)` at an integer, a `64`-bit word or an unsigned integer
    of at most `64` bits. -/
def ilitOk (t : NfTy) (v : Int) : Bool :=
  decide (0 ≤ v) && decide (v < 2 ^ 64) &&
    (ImpToNF.hax64NFWordTy t ||
      match t with
      | .uint W => decide (W.bits ≤ 64)
      | _ => false)

end CatCrypt.Crypto.Hax.NFToCatComplete

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open Ctxt (Var Valuation)

/-! ## 1. The operations of a program without exit-flag loops and calls -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- Every operation of a program, in every region and continuation, satisfies `P`, and the
    program has no exit-flag loop and no `call` node. -/
def opsNB (P : d.Op → Bool) : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => P e.op && opsNB P k
  | _, _, .forLoop _ _ body k => opsNB P body && opsNB P k
  | _, _, .ifThenElse _ thn els k => opsNB P thn && opsNB P els && opsNB P k
  | _, _, .whileLoop .. => false
  | _, _, .call .. => false

/-- `opsNB` is monotone in the predicate on the operations. -/
theorem opsNB_mono {P Q : d.Op → Bool} (h : ∀ o, P o = true → Q o = true) {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : opsNB P p = true) : opsNB Q p = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨h _ hp.1, ih hp.2⟩
  | forLoop _ _ body k ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht hp.1.1, ihe hp.1.2⟩, ihk hp.2⟩
  | whileLoop => simp [opsNB] at hp
  | call => simp [opsNB] at hp

/-- A program of `opsNB P` has no exit-flag loop. -/
theorem whileFree_of_opsNB {P : d.Op → Bool} {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : opsNB P p = true) : p.whileFree = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ih hp.2
  | forLoop _ _ body k ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.whileFree, Bool.and_eq_true]
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.whileFree, Bool.and_eq_true]
      exact ⟨⟨iht hp.1.1, ihe hp.1.2⟩, ihk hp.2⟩
  | whileLoop => simp [opsNB] at hp
  | call => simp [opsNB] at hp

omit [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- A renamed expression has the operation of the expression. -/
theorem op_rename? {Γ Δ : Ctxt d} {t : d.Ty} {f : PRen Γ Δ} {e : Expr d Γ t}
    {e' : Expr d Δ t} (h : Expr.rename? f e = some e') : e'.op = e.op := by
  simp only [Expr.rename?, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- Renaming keeps `opsNB`. -/
theorem opsNB_rename? {P : d.Op → Bool} {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} {f : PRen Γ Δ} {p' : NFProg d Δ ts}, NFProg.rename? f p = some p' →
      opsNB P p = true → opsNB P p' = true := by
  induction p with
  | ret vs =>
      intro Δ f p' h _
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
  | var e k ih =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, k', hk, rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨(op_rename? he).symm ▸ hp.1, ih hk hp.2⟩
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, b', hb, k', hk, rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hb hp.1, ihk hk hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h hp
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht ht hp.1.1, ihe he hp.1.2⟩, ihk hk hp.2⟩
  | whileLoop => intro _ _ _ _ hp; simp [opsNB] at hp
  | call => intro _ _ _ _ hp; simp [opsNB] at hp

/-- **Dead-binding elimination keeps `opsNB P`.** -/
theorem opsNB_dce {P : d.Op → Bool} {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : opsNB P p = true) : opsNB P (NFProg.dce p) = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.dce]
      split
      · rename_i k' hk'
        exact opsNB_rename? _ hk' (ih hp.2)
      · simp only [opsNB, Bool.and_eq_true]
        exact ⟨hp.1, ih hp.2⟩
  | forLoop _ _ body k ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.dce, opsNB, Bool.and_eq_true]
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.dce, opsNB, Bool.and_eq_true]
      exact ⟨⟨iht hp.1.1, ihe hp.1.2⟩, ihk hp.2⟩
  | whileLoop => simp [opsNB] at hp
  | call => simp [opsNB] at hp

/-- Every operation of a prefix, in every region and continuation, satisfies `P`, and its
    regions have no exit-flag loop and no `call` node. -/
def preOps (P : d.Op → Bool) : {Γ Δ : Ctxt d} → NFPre d Γ Δ → Bool
  | _, _, .nil => true
  | _, _, .var e p => P e.op && preOps P p
  | _, _, .forLoop _ _ body p => opsNB P body && preOps P p
  | _, _, .ifThenElse _ thn els p => opsNB P thn && opsNB P els && preOps P p
  | _, _, .whileLoop .. => false

/-- `preOps` of the concatenation of two prefixes. -/
theorem preOps_append (P : d.Op → Bool) {Γ Δ Θ : Ctxt d} (p : NFPre d Γ Δ)
    (q : NFPre d Δ Θ) : preOps P (p.append q) = (preOps P p && preOps P q) := by
  induction p with
  | nil => simp [NFPre.append, preOps]
  | var e p ih => simp [NFPre.append, preOps, ih, Bool.and_assoc]
  | forLoop _ _ body p ih => simp [NFPre.append, preOps, ih, Bool.and_assoc]
  | ifThenElse _ thn els p ih => simp [NFPre.append, preOps, ih, Bool.and_assoc]
  | whileLoop _ body p ih => simp [NFPre.append, preOps]

/-- `opsNB` of a prefix plugged with a program. -/
theorem opsNB_plug (P : d.Op → Bool) {Γ Δ : Ctxt d} {ts : List d.Ty} (p : NFPre d Γ Δ)
    (k : NFProg d Δ ts) : opsNB P (p.plug k) = (preOps P p && opsNB P k) := by
  induction p with
  | nil => simp [NFPre.plug, preOps]
  | var e p ih => simp [NFPre.plug, preOps, opsNB, ih, Bool.and_assoc]
  | forLoop _ _ body p ih => simp [NFPre.plug, preOps, opsNB, ih, Bool.and_assoc]
  | ifThenElse _ thn els p ih => simp [NFPre.plug, preOps, opsNB, ih, Bool.and_assoc]
  | whileLoop _ body p ih => simp [NFPre.plug, preOps, opsNB]

omit [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] in
/-- `opsNB` of a program cast along equal contexts and result types. -/
theorem opsNB_cast [TyDenote d.Ty] [HasWord64 d] [HasBoolBit d] (P : d.Op → Bool)
    {Γ Γ' : Ctxt d} {ts ts' : List d.Ty} (hΓ : Γ' = Γ) (hts : ts' = ts)
    (e : NFProg d Γ' ts' = NFProg d Γ ts) (q : NFProg d Γ' ts') :
    opsNB P (cast e q) = opsNB P q := by
  subst hΓ
  subst hts
  rfl

end Generic

/-! ## 2. The operations of the front -/

section Front

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open _root_.Hax (ImpExpr ImpLit Value Env Builtins denote')

/-- The types of the upper bound of a counted loop of the front: an unsigned integer and a
    word of at most `64` bits. -/
def tripBoundTy : NfTy → Bool
  | .uint _ => true
  | .word w => decide (w ≤ 64)
  | _ => false

/-- **The operations of the front at the call typing `S`**: a call `S` types, an integer
    literal of `NFToCatComplete.ilitOk`, a trip count at a type of `tripBoundTy`, the integer
    lower bound of a loop at a type of `loTyOk`, the subtraction of `64`-bit words, the
    constants, the loop counter, the tuple constructors `tnilV` and `tconsV`, the tuple
    projections `thead` and `ttail`, and the array
    `arrRepeat` of copies of a `64`-bit word. -/
def frontOp (S : String → List NfTy → Option NfTy) : NfOp → Bool
  | .named _ op => frontOp S op
  | .call f as r => decide (S f as = some r)
  | .ilit t v => CatCrypt.Crypto.Hax.NFToCatComplete.ilitOk t v
  | .trip t => tripBoundTy t
  | .boundInt t => loTyOk t
  | .bin o w => decide (o = .sub) && decide (w = 64)
  | .constBit _ | .constUnit | .ctr | .tnilV | .tconsV _ _ | .thead _ _ | .ttail _ _ => true
  | .arrRepeat _ t => decide (t = .word 64)
  | _ => false

variable (S : String → List NfTy → Option NfTy)

/-- The source name of a binding does not change `frontOp`. -/
theorem frontOp_mkEN {Γ : Ctxt nfDialect} (tgt : Option String) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) : frontOp S (mkEN tgt op args).op = frontOp S op := by
  cases tgt <;> rfl

/-- The prefix of `bind1N` satisfies `frontOp S` exactly when its operation does. -/
theorem preOps_bind1N {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) :
    preOps (frontOp S) (bind1N tgt σ op args).pre = frontOp S op := by
  simp [bind1N, preOps, frontOp_mkEN]

/-- The prefix of `bind1` satisfies `frontOp S` exactly when its operation does. -/
theorem preOps_bind1 {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) :
    preOps (frontOp S) (bind1 σ op args).pre = frontOp S op := by
  simp [bind1, preOps, mkE]

/-- The prefix of a literal binds a constant or an integer literal of `ilitOk`. -/
theorem litOut_frontOp {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (l : ImpLit)
    {o : Out Γ} (h : litOut tgt σ l = some o) : preOps (frontOp S) o.pre = true := by
  cases l with
  | bool b =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      simp [preOps_bind1N, frontOp]
  | unit =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      simp [preOps_bind1N, frontOp]
  | int n | uintLit W n | sintLit W n =>
      simp only [litOut, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hl, hs⟩ := h
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        rw [preOps_bind1N]
        exact CatCrypt.Crypto.Hax.FrontDomain.litInt_ilitWord hl
      · cases hs

/-- The prefix of an atom satisfies `frontOp S`. -/
theorem atomOut_frontOp {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (a : ImpExpr) {o : Out Γ}
    (h : atomOut σ a = some o) : preOps (frontOp S) o.pre = true := by
  cases a with
  | var x =>
      simp only [atomOut, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
  | lit l => exact litOut_frontOp S none σ l h
  | _ => simp [atomOut] at h

/-- The prefix of a list of atoms satisfies `frontOp S`. -/
theorem argsOut_frontOp (es : List ImpExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
      preOps (frontOp S) oa.pre = true := by
  induction es with
  | nil =>
      intro Γ σ oa h
      simp only [argsOut, Option.some.injEq] at h
      subst h
      rfl
  | cons e es ih =>
      intro Γ σ oa h
      simp only [argsOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      simp only [preOps_append, atomOut_frontOp S σ e ho, ih o.σ hos, Bool.and_self]

/-- The bindings of a tuple are tuple constructors. -/
theorem tupleOut_frontOp {Γ : Ctxt nfDialect} (tgt : Option String) (as : List NfTy)
    (vs : HVector (fun t => Var Γ t) as) :
    preOps (frontOp S) (tupleOut tgt as vs).snd.fst = true := by
  induction as generalizing tgt with
  | nil => cases vs; simp [tupleOut, preOps, frontOp_mkEN, frontOp]
  | cons a as ih =>
      cases vs with
      | cons v vs =>
          rw [tupleOut]
          simp [preOps_append, preOps, frontOp_mkEN, frontOp, ih]

/-- The bindings of a tuple projection are `ttail` and `thead` bindings. -/
theorem projOut_frontOp (tgt : Option String) (i : Nat) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (t : NfTy) (x : Var Γ t) {o : Out Γ},
      projOut tgt σ t x i = some o → preOps (frontOp S) o.pre = true := by
  induction i with
  | zero =>
      intro Γ σ t x o h
      cases t <;> simp only [projOut, Option.some.injEq, reduceCtorEq] at h
      subst h
      simp [preOps_bind1N, frontOp]
  | succ i ih =>
      intro Γ σ t x o h
      cases t <;> simp only [projOut, Option.map_eq_some_iff, reduceCtorEq] at h
      obtain ⟨o', ho', rfl⟩ := h
      simp [Out.comp, preOps_append, preOps_bind1, frontOp, ih _ _ _ ho']

/-- The counter binding of a loop body binds the loop counter and the subtraction of
    `64`-bit words. -/
theorem ctrOut_frontOp {Γ₃ : Ctxt nfDialect} (cs : List NfTy) (i : String)
    (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) :
    preOps (frontOp S) (ctrOut cs i σB loV rev).pre = true := by
  cases rev <;> simp [ctrOut, Out.comp, preOps_append, preOps_bind1N, preOps_bind1, frontOp]

/-- The counted loop of the front satisfies `frontOp S` when its prefix and the translation
    of its body do. -/
theorem loopOut_frontOp {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String)
    (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ))
    (hpre : preOps (frontOp S) pre₀ = true)
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (o : Out Δ), rec σ = some o →
      preOps (frontOp S) o.pre = true)
    {o : Out Γ} (h : loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits rec = some o) :
    preOps (frontOp S) o.pre = true := by
  simp only [loopOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ob, hob, rets, -, rfl⟩ := h
  simp [preOps_append, preOps, opsNB_plug, opsNB, hpre, ctrOut_frontOp, hrec _ _ hob,
    preOps_bind1N, frontOp]

/-- The conditional of the front satisfies `frontOp S` when its prefix and the translations
    of its arms do. -/
theorem condOut_frontOp {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc)
    (σc : NfEnv Γc) (cV : Var Γc NfTy.bit) (xs : List String) (cs : List NfTy)
    (recA recB : Option (Out Γc)) (hpre : preOps (frontOp S) pre₀ = true)
    (hA : ∀ oa, recA = some oa → preOps (frontOp S) oa.pre = true)
    (hB : ∀ ob, recB = some ob → preOps (frontOp S) ob.pre = true)
    {o : Out Γ} (h : condOut pre₀ σc cV xs cs recA recB = some o) :
    preOps (frontOp S) o.pre = true := by
  simp only [condOut, Option.bind_eq_some_iff] at h
  obtain ⟨oa, hoa, ob, hob, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ra, -, rb, -, h⟩ := h
    split at h <;> (subst h; simp [preOps_append, preOps, opsNB_plug, opsNB, hpre,
      hA oa hoa, hB ob hob, preOps_bind1N, frontOp])
  · cases h

/-- The binding of a lower bound `loOut` accepts satisfies `frontOp S`: an integer literal of
    `ilitOk` at the integer type, or `boundInt` at a type of `loTyOk`. -/
theorem loOut_frontOp {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (lo : ImpExpr)
    {e : Expr nfDialect Γ NfTy.int} (h : loOut σ lo = some e) :
    preOps (frontOp S) (loBind σ e).pre = true := by
  match lo, h with
  | .lit (.int n), h =>
      simp only [loOut] at h
      split at h
      · rename_i hn
        cases h
        have h1 : n < 2 ^ 64 := hn.2
        simp [loBind, preOps, mkE, frontOp, CatCrypt.Crypto.Hax.NFToCatComplete.ilitOk,
          hax64NFWordTy, hn.1]
        omega
      · cases h
  | .var x, h =>
      simp only [loOut, Option.bind_eq_some_iff] at h
      obtain ⟨p, -, h⟩ := h
      split at h
      · rename_i ht
        cases h
        simp [loBind, preOps, mkE, frontOp, ht]
      · cases h

/-- The upper bound of a counted loop accepted by `boundOk 0` or `litBoundOk 0` has a type of
    `tripBoundTy`. -/
theorem bound_frontOp {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {hi : ImpExpr}
    {oHi : Out Γ} (hHi : atomOut σ hi = some oHi) (hb : (boundOk 0 oHi.t || litBoundOk 0 hi) = true) :
    tripBoundTy oHi.t = true := by
  rcases Bool.or_eq_true_iff.mp hb with hb | hb
  · revert hb
    cases oHi.t <;> simp [boundOk, tripBoundTy]
  · match hi, hb, hHi with
    | .lit (.int n), hb, hHi =>
        simp only [litBoundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [atomOut, litOut, litInt, Option.bind_eq_some_iff] at hHi
        obtain ⟨⟨t, v⟩, hl, hs⟩ := hHi
        split at hl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          split at hs
          · simp only [Option.some.injEq] at hs
            subst hs
            rfl
          · cases hs
        · cases hl

/-- The prefix of `impArgsNF` satisfies `frontOp S` when the prefix of `impToNF` on each
    argument does. -/
theorem impArgsNF_frontOp (args : List ImpExpr)
    (ih : ∀ e ∈ args, ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : Out Γ),
      impToNF S tgt σ e = some o → preOps (frontOp S) o.pre = true) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (oa : ArgsOut Γ),
      impArgsNF S σ args = some oa → preOps (frontOp S) oa.pre = true := by
  induction args with
  | nil =>
      intro Γ σ oa h
      simp only [impArgsNF, Option.some.injEq] at h
      subst h
      rfl
  | cons e es ihes =>
      intro Γ σ oa h
      simp only [impArgsNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      simp only [preOps_append, ih e List.mem_cons_self none σ o ho,
        ihes (fun a ha => ih a (List.mem_cons_of_mem _ ha)) o.σ os hos, Bool.and_self]

/-- **The operations of the front's output**: every operation of a prefix `impToNF S`
    returns satisfies `frontOp S`, and its regions have no exit-flag loop and no `call`
    node. -/
theorem impToNF_frontOp (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : Out Γ),
      impToNF S tgt σ e = some o → preOps (frontOp S) o.pre = true := by
  induction e using ImpExpr.ind
  case lit l =>
    intro tgt Γ σ o h
    exact litOut_frontOp S tgt σ l h
  case var x =>
    intro tgt Γ σ o h
    exact atomOut_frontOp S σ (.var x) h
  case unitVal =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.some.injEq] at h
    subst h
    simp [preOps_bind1N, frontOp]
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    simp only [Out.comp, preOps_append, ihv _ _ _ hov, ihb _ _ _ hob, Bool.and_self]
  case seq a b iha ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    simp only [Out.comp, preOps_append, iha _ _ _ hoa, ihb _ _ _ hob, Bool.and_self]
  case assign x r ih =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨o', ho', rfl⟩ := h
    simp [Out.comp, preOps_append, ih _ _ _ ho', preOps_bind1N, frontOp]
  case typeAscription e s ih =>
    intro tgt Γ σ o h
    simp only [impToNF] at h
    exact ih _ _ _ h
  case app f args iha =>
    intro tgt Γ σ o h
    rcases impToNF_app_cases S tgt σ h with ⟨x, N, -, h⟩ | ⟨-, oa, hoa, r, hr, rfl⟩
    · simp only [repeatOut, Option.bind_eq_some_iff] at h
      obtain ⟨ox, hox, h⟩ := h
      split at h
      · cases h
        simp [Out.comp, preOps_append, atomOut_frontOp S _ _ hox, preOps_bind1N, frontOp]
      · cases h
    · simp [preOps_append, preOps, impArgsNF_frontOp S args iha _ _ hoa, frontOp_mkEN,
        frontOp, hr]
  case tuple es _ =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, rfl⟩ := h
    simp only [preOps_append, argsOut_frontOp S es σ hoa, tupleOut_frontOp, Bool.and_self]
  case proj e i ih =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oe, hoe, op, hop, rfl⟩ := h
    simp only [Out.comp, preOps_append, ih _ _ _ hoe, projOut_frontOp S tgt i _ _ _ hop,
      Bool.and_self]
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, hHi, h⟩ := h
    split at h
    · rename_i hb
      have ht := bound_frontOp hHi hb
      refine loopOut_frontOp S _ _ _ _ _ _ _ _ _ _ _ ?_
        (fun σB o' ho' => ihb _ σB o' ho') h
      simp only [preOps_append, preOps_bind1, atomOut_frontOp S _ _ hHi, loOut_frontOp S σ lo hLo,
        frontOp, ht, Bool.and_self]
    · cases h
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, hHi, h⟩ := h
    split at h
    · rename_i hb
      have ht := bound_frontOp hHi hb
      refine loopOut_frontOp S _ _ _ _ _ _ _ _ _ _ _ ?_
        (fun σB o' ho' => ihb _ σB o' ho') h
      simp only [preOps_append, preOps_bind1, atomOut_frontOp S _ _ hHi, loOut_frontOp S σ lo hLo,
        frontOp, ht, Bool.and_self]
      decide
    · cases h
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨oc, hoc, h⟩ := h
    split at h
    · exact condOut_frontOp S _ _ _ _ _ _ _ (ihc _ _ _ hoc) (fun oa ha => iha _ _ _ ha)
        (fun ob hb => ihb _ _ _ hb) h
    · cases h
  all_goals
    intro tgt Γ σ o h
    simp [impToNF] at h

/-- The program of an output of `impToNF S` is a program of `opsNB (frontOp S)`. -/
theorem impToNF_prog_frontOp (e : ImpExpr) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (o : Out Γ) (h : impToNF S tgt σ e = some o) :
    opsNB (frontOp S) o.prog = true := by
  simp [Out.prog, opsNB_plug, impToNF_frontOp S e tgt σ o h, opsNB]

/-- A prefix of `preOps P` denotes independently of the fuel. -/
theorem PDen_fuel_of_preOps (bi : Builtins) {P : NfOp → Bool} {Γ Δ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) (hp : preOps P p = true) (n m : Nat) :
    ∀ V : Valuation Γ, PDen bi n p V = PDen bi m p V := by
  let _ : DialectDenoteM nfDialect Option := nfDenote (tableOf bi)
  induction p with
  | nil => intro V; rfl
  | var e p ih =>
      intro V
      simp only [preOps, Bool.and_eq_true] at hp
      simp only [PDen, NFPre.denote, ih hp.2]
  | forLoop count inits body p ih =>
      intro V
      simp only [preOps, Bool.and_eq_true] at hp
      have hb := NFProg.denote_fuel_of_whileFree body (whileFree_of_opsNB body hp.1) n m
      simp only [PDen, NFPre.denote, ih hp.2, hb]
  | ifThenElse cond thn els p ih =>
      intro V
      simp only [preOps, Bool.and_eq_true] at hp
      have ht := NFProg.denote_fuel_of_whileFree thn (whileFree_of_opsNB thn hp.1.1) n m
      have he := NFProg.denote_fuel_of_whileFree els (whileFree_of_opsNB els hp.1.2) n m
      simp only [PDen, NFPre.denote, ih hp.2, ht, he]
  | whileLoop => simp [preOps] at hp

/-- **A sound output whose prefix is of `preOps P` is matched at every fuel**: a run of the
    source to a value gives one valuation `W` of the hole that the prefix reaches at every
    target fuel. -/
theorem Sound.all_of_preOps {bi : Builtins} {fuel : Nat} {e : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {o : Out Γ} (hs : Sound bi fuel e σ o) {P : NfOp → Bool}
    (hp : preOps P o.pre = true) {env : Env} {V : Valuation Γ} {v : Value} {env' : Env}
    (hrel : EnvRel σ env V) (hrun : (denote' bi fuel e).run env = (.val v, env')) :
    ∃ W, (∀ tf, PDen bi tf o.pre V = some W) ∧ EnvRel o.σ env' W ∧
      v = enc o.t (o.res.lookup W) := by
  obtain ⟨W, ⟨N, hN⟩, hrelW, hv⟩ := hs.ev hrel hrun
  exact ⟨W, fun tf => (PDen_fuel_of_preOps bi o.pre hp tf N V).trans (hN N le_rfl), hrelW, hv⟩

end Front

end CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete
