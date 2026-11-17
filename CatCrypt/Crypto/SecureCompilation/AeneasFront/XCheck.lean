/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Entry

/-!
# A checker that two entries translate a source to the same program

The hax front (`haxEntry`) and the Aeneas front (`aeneasEntry`) translate a Rust function to
programs of `NFProg nfDialect` over the parameters of a layout. This module decides, for two
such programs, that a canonical form of each is the same program, and proves that two
source runs from one entry state then return the same value.

## Main results

* `NFProg.stripNamed` removes the source names `NfOp.named` of the bound operations; it keeps
  the denotation (`denote_stripNamed`), as the chain step `stripNamedStep` with the
  certificate `stripNamedCert`.
* `canon` is the elimination of aborting branches, tuple flattening, dead-code elimination and
  `stripNamed`. A run of a program is a run of its canonical form at the same fuel
  (`canon_sim`).
* `NFProg.erase` maps a program to an untyped tree `XProg`: de Bruijn variables as their
  indices, with the types the indices do not determine. Erasure is injective on programs of
  one context and result list (`erase_inj`), so equality of erasures decides equality of
  programs; since the variables are de Bruijn indices, this is alpha-equivalence.
* `xcheckNF q₁ q₂`: the result types agree and the canonical forms have equal erasures.
* `NFEntry.agree`: two entries whose tables are a fixed table `B` at every fuel, whose
  translations of two sources pass `xcheckNF`, return the same value on two runs from one
  entry state. The parameter environment is determined by the entry state
  (`AbiLayout.envOf_unique`), the parameter valuation by the environment
  (`entryVals_unique`), and the program value by the valuation, at the larger of the two fuels
  (`NFProg.denoteAt_fuel_mono`).
* `xcheck σ m s` and `xcheck_sound`: the instance at the hax module `m` without linked functions
  and the Aeneas source `s`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals tableOf)
open CatCrypt.Crypto.Hax (hax64WExit HaxModule)
open _root_.Hax (Value Env Builtins)

deriving instance DecidableEq for NfOp

/-! ## Removal of source names -/

/-- The expression of the operation `op` on `args` with every source name `NfOp.named` around
    `op` removed. -/
def stripE {Γ : Ctxt nfDialect} {t : NfTy} : (op : NfOp) → NfOp.ret op = t →
    HVector (fun ty => Var Γ ty) (NfOp.sig op) → Expr nfDialect Γ t
  | .named _ op, h, args => stripE op h args
  | op, h, args => ⟨op, h, args⟩

/-- An expression with its source names removed denotes what it denotes. -/
theorem stripE_denoteM (T : NfLeafTable) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (op : NfOp) : ∀ {t : NfTy} (h : NfOp.ret op = t)
      (args : HVector (fun ty => Var Γ ty) (NfOp.sig op)),
      @Expr.denoteM nfDialect Option _ _ (nfDenote T) Γ t (stripE op h args) V =
        @Expr.denoteM nfDialect Option _ _ (nfDenote T) Γ t ⟨op, h, args⟩ V := by
  induction op with
  | named n op ih =>
      intro t h args
      rw [stripE, ih h args]
      subst h
      rfl
  | _ => intro t h args; rfl

namespace NFProg

/-- **The removal of source names**: every bound operation `NfOp.named n op` becomes `op`. -/
def stripNamed : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts →
    NFProg nfDialect Γ ts
  | _, _, .ret vs => .ret vs
  | _, _, .var e k => .var (stripE e.op e.retTy_eq e.args) (stripNamed k)
  | _, _, .forLoop count inits body k => .forLoop count inits (stripNamed body) (stripNamed k)
  | _, _, .ifThenElse c thn els k => .ifThenElse c (stripNamed thn) (stripNamed els) (stripNamed k)
  | _, _, .whileLoop inits body k => .whileLoop inits (stripNamed body) (stripNamed k)
  | _, _, .call f args k => .call f args (stripNamed k)

/-- **The removal of source names keeps the denotation**, at every leaf table and fuel. -/
theorem denote_stripNamed (T : NfLeafTable) (fuel : Nat) :
    ∀ {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) (V : Valuation Γ),
      @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts (stripNamed p) V =
        @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V
  | _, _, .ret _, _ => rfl
  | _, _, .var e k, V => by
      obtain ⟨op, h, args⟩ := e
      simp only [stripNamed, NFProg.denote, stripE_denoteM, denote_stripNamed T fuel k]
  | _, _, .forLoop count inits body k, V => by
      have hb := denote_stripNamed T fuel body
      have hk := denote_stripNamed T fuel k
      simp only [stripNamed, NFProg.denote, hb, hk]
  | _, _, .ifThenElse c thn els k, V => by
      have ht := denote_stripNamed T fuel thn
      have he := denote_stripNamed T fuel els
      have hk := denote_stripNamed T fuel k
      simp only [stripNamed, NFProg.denote, ht, he, hk]
  | _, _, .whileLoop inits body k, V => by
      have hb := denote_stripNamed T fuel body
      have hk := denote_stripNamed T fuel k
      simp only [stripNamed, NFProg.denote, hb, hk]
  | _, _, .call f args k, V => by
      have hk := denote_stripNamed T fuel k
      simp only [stripNamed, NFProg.denote, hk]

end NFProg

/-- The removal of source names as a chain step; it never refuses. -/
def stripNamedStep (Γ : Ctxt nfDialect) (ts : List NfTy) :
    Step (NFProg nfDialect Γ ts) (NFProg nfDialect Γ ts) :=
  ⟨"stripNamed", fun p => some (NFProg.stripNamed p)⟩

/-- The certificate of `stripNamedStep`, at equal inputs and outputs, at every table and fuel
    (`NFProg.denote_stripNamed`). -/
def stripNamedCert (bi : Builtins) (tf : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    StepCert (stripNamedStep Γ ts).run (nfSemB bi tf Γ ts) (nfSemB bi tf Γ ts) :=
  StepCert.ofDenoteEq _ fun p q hf => by
    cases hf
    funext V
    exact NFProg.denote_stripNamed (tableOf bi) tf p V

/-! ## The canonical form -/

/-- **The canonical form of a program**: the elimination of aborting branches
    (`NFProg.abortElim NfOp.isAbort`), tuple flattening (`flatSame`), dead-code elimination
    (`NFProg.dce`) and the removal of source names (`NFProg.stripNamed`). It refuses where
    `flatSame` refuses. -/
def canon {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    Option (NFProg nfDialect Γ ts) :=
  (flatSame (NFProg.abortElim NfOp.isAbort p)).map fun q => NFProg.stripNamed (NFProg.dce q)

/-- **Forward simulation of the canonical form**: a run of a program is a run of its canonical
    form, at the same table and fuel. -/
theorem canon_sim (bi : Builtins) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p c : NFProg nfDialect Γ ts} (h : canon p = some c) {k : Nat} {V : Valuation Γ}
    {r : Valuation (d := nfDialect) ts} (hp : PDenP bi k p V = some r) :
    PDenP bi k c V = some r := by
  let _ : DialectDenoteM nfDialect Option := nfDenote (tableOf bi)
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := NFProg.denote_abortElim NfOp.isAbort (nfDenote_isAbort (tableOf bi)) p k V r hp
  have h2 := (flatSame_denote (tableOf bi) k hq V).trans h1
  exact (NFProg.denote_stripNamed (tableOf bi) k _ V).trans (NFProg.denote_dce q h2)

/-- **Fuel monotonicity of programs** at a builtin table: a run at a fuel is a run at every
    larger fuel (`NFProg.denoteAt_fuel_mono`). -/
theorem pDenP_mono (bi : Builtins) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p : NFProg nfDialect Γ ts} {V : Valuation Γ} {r : Valuation (d := nfDialect) ts}
    {n m : Nat} (hnm : n ≤ m) (h : PDenP bi n p V = some r) : PDenP bi m p V = some r := by
  let _ : DialectDenoteM nfDialect Option := nfDenote (tableOf bi)
  exact NFProg.denoteAt_fuel_mono .empty hnm p V r h

/-! ## Erasure to untyped trees -/

/-- **Untyped programs**: the programs of `NFProg nfDialect` with each variable as its de Bruijn
    index, each operation as itself, and the types of loop carries, branch results and call
    signatures, which the indices do not determine. -/
inductive XProg where
  /-- Return the variables of the indices. -/
  | ret (vs : List Nat)
  /-- Bind an operation on the variables of the indices. -/
  | var (op : NfOp) (args : List Nat) (k : XProg)
  /-- A counted loop carrying the types `cs`. -/
  | forLoop (count : Nat) (cs : List NfTy) (inits : List Nat) (body k : XProg)
  /-- A branch with the result types `rs`. -/
  | ifThenElse (cond : Nat) (rs : List NfTy) (thn els k : XProg)
  /-- An exit-flag loop carrying the types `cs`. -/
  | whileLoop (cs : List NfTy) (inits : List Nat) (body k : XProg)
  /-- A call of `f` at the signature `as → rs`. -/
  | call (f : String) (as rs : List NfTy) (args : List Nat) (k : XProg)
  deriving DecidableEq

/-- The de Bruijn index of a variable. -/
def varIdx {Γ : Ctxt nfDialect} {t : NfTy} : Var Γ t → Nat
  | .here => 0
  | .there v => varIdx v + 1

/-- The de Bruijn indices of a vector of variables. -/
def varIdxs {Γ : Ctxt nfDialect} : {ts : List NfTy} → HVector (fun t => Var Γ t) ts → List Nat
  | [], .nil => []
  | _ :: _, .cons v vs => varIdx v :: varIdxs vs

/-- Two variables of one context with the same index have the same type and are equal. -/
theorem varIdx_inj {Γ : Ctxt nfDialect} {t : NfTy} (v : Var Γ t) :
    ∀ {t' : NfTy} (w : Var Γ t'), varIdx v = varIdx w → t = t' ∧ HEq v w := by
  induction v with
  | here => intro t' w h; cases w with
    | here => exact ⟨rfl, HEq.rfl⟩
    | there w => simp [varIdx] at h
  | there v ih => intro t' w h; cases w with
    | here => simp [varIdx] at h
    | there w =>
        obtain ⟨rfl, hvw⟩ := ih w (by simpa [varIdx] using h)
        exact ⟨rfl, by rw [eq_of_heq hvw]⟩

/-- Two vectors of variables of one context and one type list with the same indices are
    equal. -/
theorem varIdxs_inj {Γ : Ctxt nfDialect} :
    ∀ {ts : List NfTy} (a b : HVector (fun t => Var Γ t) ts), varIdxs a = varIdxs b → a = b
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v vs, .cons w ws, h => by
      change varIdx v :: varIdxs vs = varIdx w :: varIdxs ws at h
      rw [List.cons.injEq] at h
      rw [eq_of_heq (varIdx_inj v w h.1).2, varIdxs_inj vs ws h.2]

/-- **The erasure of a program** to an untyped tree. -/
def NFProg.erase : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → XProg
  | _, _, .ret vs => .ret (varIdxs vs)
  | _, _, .var e k => .var e.op (varIdxs e.args) (NFProg.erase k)
  | _, _, .forLoop (cs := cs) count inits body k =>
      .forLoop (varIdx count) cs (varIdxs inits) (NFProg.erase body) (NFProg.erase k)
  | _, _, .ifThenElse (rs := rs) c thn els k =>
      .ifThenElse (varIdx c) rs (NFProg.erase thn) (NFProg.erase els) (NFProg.erase k)
  | _, _, .whileLoop (cs := cs) inits body k =>
      .whileLoop cs (varIdxs inits) (NFProg.erase body) (NFProg.erase k)
  | _, _, .call (as := as) (rs := rs) f args k =>
      .call f as rs (varIdxs args) (NFProg.erase k)

/-- **Erasure is injective** on programs of one context and one result list. -/
theorem NFProg.erase_inj :
    ∀ {Γ : Ctxt nfDialect} {ts : List NfTy} (p q : NFProg nfDialect Γ ts),
      NFProg.erase p = NFProg.erase q → p = q := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro q h
      cases q with
      | ret ws =>
          simp only [NFProg.erase, XProg.ret.injEq] at h
          rw [varIdxs_inj vs ws h]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h
  | var e k ih =>
      intro q h
      cases q with
      | var e' k' =>
          obtain ⟨op, he, args⟩ := e
          obtain ⟨op', he', args'⟩ := e'
          simp only [NFProg.erase, XProg.var.injEq] at h
          obtain ⟨rfl, ha, hk⟩ := h
          subst he
          subst he'
          rw [varIdxs_inj args args' ha, ih k' hk]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h
  | forLoop c i b k ihb ihk =>
      intro q h
      cases q with
      | forLoop c' i' b' k' =>
          simp only [NFProg.erase, XProg.forLoop.injEq] at h
          obtain ⟨hc, rfl, hi, hb, hk⟩ := h
          rw [eq_of_heq (varIdx_inj c c' hc).2, varIdxs_inj i i' hi, ihb b' hb, ihk k' hk]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h
  | ifThenElse c thn els k iht ihe ihk =>
      intro q h
      cases q with
      | ifThenElse c' thn' els' k' =>
          simp only [NFProg.erase, XProg.ifThenElse.injEq] at h
          obtain ⟨hc, rfl, ht, he, hk⟩ := h
          rw [eq_of_heq (varIdx_inj c c' hc).2, iht thn' ht, ihe els' he, ihk k' hk]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h
  | whileLoop i b k ihb ihk =>
      intro q h
      cases q with
      | whileLoop i' b' k' =>
          simp only [NFProg.erase, XProg.whileLoop.injEq] at h
          obtain ⟨rfl, hi, hb, hk⟩ := h
          rw [varIdxs_inj i i' hi, ihb b' hb, ihk k' hk]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h
  | call f args k ih =>
      intro q h
      cases q with
      | call f' args' k' =>
          simp only [NFProg.erase, XProg.call.injEq] at h
          obtain ⟨rfl, rfl, rfl, ha, hk⟩ := h
          rw [varIdxs_inj args args' ha, ih k' hk]
      | _ => simp only [NFProg.erase, reduceCtorEq] at h

/-! ## The check -/

/-- **The check of two translations**: the result types are equal and the canonical forms of
    the programs have equal erasures. -/
def xcheckNF {Γ : Ctxt nfDialect} (q₁ q₂ : Σ t : NfTy, NFProg nfDialect Γ [t]) : Bool :=
  match canon q₁.2, canon q₂.2 with
  | some c₁, some c₂ => q₁.1 == q₂.1 && NFProg.erase c₁ == NFProg.erase c₂
  | _, _ => false

/-- **Soundness of the check on programs**: at programs that pass `xcheckNF`, two runs at one
    table and one valuation, at any fuels, return values with the same encoding. -/
theorem xcheckNF_sound {B : Builtins} {Γ : Ctxt nfDialect}
    {q₁ q₂ : Σ t : NfTy, NFProg nfDialect Γ [t]} (h : xcheckNF q₁ q₂ = true)
    {V : Valuation Γ} {k₁ k₂ : Nat} {y₁ : q₁.1.denote} {y₂ : q₂.1.denote}
    (h₁ : PDenP B k₁ q₁.2 V = some (HVector.cons y₁ .nil))
    (h₂ : PDenP B k₂ q₂.2 V = some (HVector.cons y₂ .nil)) :
    enc q₁.1 y₁ = enc q₂.1 y₂ := by
  obtain ⟨t₁, p₁⟩ := q₁
  obtain ⟨t₂, p₂⟩ := q₂
  dsimp only at h₁ h₂ y₁ y₂ ⊢
  simp only [xcheckNF] at h
  split at h
  · rename_i c₁ c₂ hc₁ hc₂
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, he⟩ := h
    have hc := NFProg.erase_inj c₁ c₂ he
    subst hc
    have m₁ := pDenP_mono B (le_max_left k₁ k₂) (canon_sim B hc₁ h₁)
    have m₂ := pDenP_mono B (le_max_right k₁ k₂) (canon_sim B hc₂ h₂)
    rw [m₁, Option.some.injEq, HVector.cons.injEq] at m₂
    rw [m₂.1]
  · exact absurd h Bool.false_ne_true

/-! ## Agreement of two entries -/

/-- **The parameter environment is determined by the entry state**: two environments that a
    layout reads off one entry state are equal. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout.envOf_unique
    {σ : AbiLayout} {sa : AState} {e₁ e₂ : Env}
    (h₁ : σ.EnvOf sa e₁) (h₂ : σ.EnvOf sa e₂) : e₁ = e₂ := by
  obtain ⟨hA₁, hC₁, hN₁⟩ := h₁
  obtain ⟨hA₂, hC₂, hN₂⟩ := h₂
  funext y
  by_cases hy : y ∈ σ.envNames
  · simp only [AbiLayout.envNames, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · rw [hA₁ a ha, hA₂ a ha]
    · rw [hC₁ c hc, hC₂ c hc]
  · have n₁ : e₁ y = none := Option.not_isSome_iff_eq_none.mp fun h => hy (hN₁ y h)
    have n₂ : e₂ y = none := Option.not_isSome_iff_eq_none.mp fun h => hy (hN₂ y h)
    rw [n₁, n₂]

/-- **The parameter valuation is determined by the environment**: two valuations whose
    encodings an environment holds at the parameters are equal (`enc_inj`). -/
theorem entryVals_unique {e : Env} :
    ∀ {ps : List (String × NfTy)} {V₁ V₂ : Valuation (entryCtx ps)},
      EntryVals e ps V₁ → EntryVals e ps V₂ → V₁ = V₂
  | [], .nil, .nil, _, _ => rfl
  | (_, t) :: _, .cons y₁ V₁, .cons y₂ V₂, h₁, h₂ => by
      obtain ⟨hy₁, h₁⟩ := h₁
      obtain ⟨hy₂, h₂⟩ := h₂
      have hy := CatCrypt.Crypto.Hax.NFInline.enc_inj t y₁ y₂
        (Option.some.inj (hy₁.symm.trans hy₂))
      rw [hy, entryVals_unique h₁ h₂]

/-- **Agreement of two entries.** Let the tables of the entries `E₁`, `E₂` at the sources `s₁`,
    `s₂` be the table `B` at every fuel, and let their translations under the layout `σ` pass
    `xcheckNF`. Then two runs of the sources from one entry state that satisfies `σ.Regions`
    return the same value. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.Haxc.NFEntry.agree (E₁ E₂ : NFEntry)
    {B : Builtins} {σ : AbiLayout} {s₁ : E₁.Src}
    {s₂ : E₂.Src} {q₁ q₂ : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    (hq₁ : E₁.toNF σ s₁ = some q₁) (hq₂ : E₂.toNF σ s₂ = some q₂)
    (hB₁ : ∀ k, E₁.bi s₁ k = B) (hB₂ : ∀ k, E₂.bi s₂ k = B) (hc : xcheckNF q₁ q₂ = true)
    {sa : AState} {v w : Value} (hR : σ.Regions sa) (hr₁ : E₁.Runs σ s₁ sa v)
    (hr₂ : E₂.Runs σ s₂ sa w) : v = w := by
  obtain ⟨k₁, -, e₁, V₁, y₁, -, -, -, he₁, hV₁, ⟨tf₁, -, hp₁⟩, hv⟩ :=
    E₁.sound σ s₁ q₁ hq₁ sa v hR hr₁
  obtain ⟨k₂, -, e₂, V₂, y₂, -, -, -, he₂, hV₂, ⟨tf₂, -, hp₂⟩, hw⟩ :=
    E₂.sound σ s₂ q₂ hq₂ sa w hR hr₂
  rw [hB₁] at hp₁
  rw [hB₂] at hp₂
  have he := AbiLayout.envOf_unique he₁ he₂
  subst he
  have hV := entryVals_unique hV₁ hV₂
  subst hV
  rw [hv, hw]
  exact xcheckNF_sound hc hp₁ hp₂

/-! ## The hax and Aeneas fronts -/

/-- **The cross-check of the hax and Aeneas fronts**: the module `m` has no linked function,
    both translations under the layout `σ` succeed, and their programs pass `xcheckNF`. -/
def xcheck (σ : AbiLayout) (m : HaxModule) (s : AeSrc) : Bool :=
  m.linked.isEmpty &&
    match haxToNF σ m, aeneasToNF σ s with
    | some q₁, some q₂ => xcheckNF q₁ q₂
    | _, _ => false

/-- **Soundness of the cross-check**: when `xcheck σ m s` holds, a run of the hax module `m`
    (`haxRunsW`) and a run of the Aeneas source `s` (`aeneasRuns`) from one entry state that
    satisfies `σ.Regions` return the same value. -/
theorem xcheck_sound {σ : AbiLayout} {m : HaxModule} {s : AeSrc} (h : xcheck σ m s = true)
    {sa : AState} {v w : Value} (hR : σ.Regions sa) (hH : haxRunsW σ m sa v)
    (hA : aeneasRuns σ s sa w) : v = w := by
  simp only [xcheck, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨hl, h⟩ := h
  split at h
  · rename_i q₁ q₂ hq₁ hq₂
    exact NFEntry.agree haxEntry aeneasEntry (B := hax64WExit) hq₁ hq₂
      (fun _ => HaxModule.linkTable_of_linked_nil hl _) (fun _ => rfl) h hR hH hA
  · exact absurd h Bool.false_ne_true

end CatCrypt.Crypto.SecureCompilation.AeneasFront
