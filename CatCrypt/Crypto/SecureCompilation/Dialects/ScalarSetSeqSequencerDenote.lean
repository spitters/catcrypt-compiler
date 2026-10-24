/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
import all CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
public import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.Optimizer.ComDCE

@[expose] public section
set_option autoImplicit false

/-!
# Denotation of the width-`w` statement sequencer

`ScalarSetSeqSequencer.seqProg w vm stmts r` lowers a statement list
`stmts : List (String × SExpr)` to a `Com catCryptDialect Γ (.sword w)` returning
the slot of `r`. This module gives the statement list its source semantics and
proves that the lowered program denotes it.

* `evalSExprW w β e` is the value of `e` at width `w` over the name environment
  `β : String → BitVec w`: wrapping `+ - *`, `&&& ^^^`, the logical shifts by
  the count `shiftMask w` of the count operand's value, and the arithmetic shift
  right by the count operand's value (the shift conventions of the dialect ops
  `bvShiftLV`/`bvShiftRV`/`bvShiftRA` the lowering emits).
* `stmtListEnv w β stmts` is the environment after executing `stmts` in order, each
  `(x, e)` setting `x` to `evalSExprW w β e`.
* `seqProg_denote`: when `seqProg w vm stmts r = some com` and the slots of `vm`
  hold the values of `β`, `com.denote V = stmtListEnv w β stmts r`.
* `seqProg_jasmin_denote`: the same value for the `jasminDialect` program
  `cryptoDialectToJasminCom com` on the transported valuation.

## Main results

* `evalSExprW`, `stmtListEnv`: the width-`w` value of an `SExpr` and the environment a
  statement list produces.
* `seqProg_denote`: the program `seqProg w` builds denotes the value the statement list
  gives the result name.
* `seqProg_jasmin_denote`, `seqProg_jasmin_exists_denote`: the same for the
  `jasminDialect` program `cryptoDialectToJasminCom` makes of it.

The side conditions are name hygiene and literal shift counts: source names
(variables, destinations, the result name) are not `tmpName` temporaries, and a
literal shift count `k` is a `w`-bit word (`k < 2 ^ w`), because the lowering
emits the immediate-count op with count `k` while `evalSExprW` shifts by the
count's `w`-bit value `(BitVec.ofNat w k).toNat`.

The proof is by induction over the builder: `lowerSExprW_denote` by induction on
the `SExpr`, `lowerScalarSetSeqW_denote` by induction on the statement list, each
step tracking a `ConsistentS` environment of the slots the `VarMap` names.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName seqOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. Source semantics -/

/-- The value of an `SExpr` at width `w` over the name environment `β`. The
    arithmetic and bitwise operators wrap at width `w`; `SShl`/`SShr` shift by
    `shiftMask w` of the count's value and `SAsr` shifts arithmetically by the
    count's value. The constructors the sequencer does not lower (`SLt`, `SMulS`,
    `SMulHiU`, `SMulHiS`, `SLimb`) have value `0`. -/
def evalSExprW (w : Nat) (β : String → BitVec w) : SExpr → BitVec w
  | .SVar x => β x
  | .SLit n => BitVec.ofNat w n
  | .SAdd a b => evalSExprW w β a + evalSExprW w β b
  | .SSub a b => evalSExprW w β a - evalSExprW w β b
  | .SMul a b => evalSExprW w β a * evalSExprW w β b
  | .SAnd a b => evalSExprW w β a &&& evalSExprW w β b
  | .SXor a b => evalSExprW w β a ^^^ evalSExprW w β b
  | .SShl a b => evalSExprW w β a <<< shiftMask w (evalSExprW w β b).toNat
  | .SShr a b => evalSExprW w β a >>> shiftMask w (evalSExprW w β b).toNat
  | .SAsr a b => BitVec.sshiftRight (evalSExprW w β a) (evalSExprW w β b).toNat
  | _ => 0

/-- The environment after executing the statements in order: `(x, e)` sets `x`
    to `evalSExprW w β e`, where `β` is the environment before the statement. -/
def stmtListEnv (w : Nat) (β : String → BitVec w) :
    List (String × SExpr) → String → BitVec w
  | [] => β
  | (x, e) :: rest => stmtListEnv w (fun n => if n = x then evalSExprW w β e else β n) rest

/-- Source hygiene of an `SExpr` at width `w`: its variables are not `tmpName`
    temporaries, and every literal shift count is below `2 ^ w`. -/
def SrcCleanW (w : Nat) : SExpr → Prop
  | .SVar x => ¬ isTmpName x
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b =>
      SrcCleanW w a ∧ SrcCleanW w b
  | .SShl a b | .SShr a b | .SAsr a b =>
      SrcCleanW w a ∧ SrcCleanW w b ∧ ∀ k, b = .SLit k → k < 2 ^ w
  | _ => True

/-- Source hygiene of a statement list: every destination is not a `tmpName`
    temporary and every right-hand side is `SrcCleanW`. -/
def StmtsClean (w : Nat) : List (String × SExpr) → Prop
  | [] => True
  | (x, e) :: rest => ¬ isTmpName x ∧ SrcCleanW w e ∧ StmtsClean w rest

/-- The environment after a concatenation is the environment after the second list, run
    from the environment after the first. -/
theorem stmtListEnv_append (w : Nat) (β : String → BitVec w)
    (l₁ l₂ : List (String × SExpr)) :
    stmtListEnv w β (l₁ ++ l₂) = stmtListEnv w (stmtListEnv w β l₁) l₂ := by
  induction l₁ generalizing β with
  | nil => rfl
  | cons p l ih => exact ih _

/-- A concatenation of hygienic statement lists is hygienic. -/
theorem stmtsClean_append (w : Nat) (l₁ l₂ : List (String × SExpr))
    (h₁ : StmtsClean w l₁) (h₂ : StmtsClean w l₂) : StmtsClean w (l₁ ++ l₂) := by
  induction l₁ with
  | nil => exact h₂
  | cons p l ih =>
    obtain ⟨x, e⟩ := p
    exact ⟨h₁.1, h₁.2.1, ih h₁.2.2⟩

/-! ## 2. Prefix denotation and environment agreement -/

/-- The prefix `f` sends every tail to a program whose denotation at `V` is the
    tail's denotation at `V'`. -/
def ContDenotes {Γ Γ' : Ctx} (f : ComCont Γ Γ')
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (V' : Ctxt.Valuation (d := catCryptDialect) Γ') : Prop :=
  ∀ {t : CryptoTy} (tail : Com catCryptDialect Γ' t),
    ∃ com, f tail = some com ∧ com.denote V = tail.denote V'

/-- The identity prefix denotes the identity on valuations. -/
theorem ContDenotes.id {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ContDenotes (ComCont.id (Γ := Γ)) V V :=
  fun tail => ⟨tail, rfl, rfl⟩

/-- Prefix denotations compose along `ComCont.comp`. -/
theorem ContDenotes.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {V₁ : Ctxt.Valuation (d := catCryptDialect) Γ'}
    {V₂ : Ctxt.Valuation (d := catCryptDialect) Γ''}
    (hf : ContDenotes f V V₁) (hg : ContDenotes g V₁ V₂) :
    ContDenotes (ComCont.comp f g) V V₂ := by
  intro t tail
  obtain ⟨b, hb, hbd⟩ := hg tail
  obtain ⟨c, hc, hcd⟩ := hf b
  refine ⟨c, ?_, hcd.trans hbd⟩
  show ComCont.comp f g tail = some c
  unfold ComCont.comp
  rw [hb]; exact hc

/-- Every non-temporary name the environment binds at `.sword w` holds its `β`
    value. -/
def SlotsAgreeAt (w : Nat) (env : SEnvScalar) (β : String → BitVec w) : Prop :=
  ∀ n, ¬ isTmpName n → ∀ x : BitVec w, env n = some ⟨.sword w, x⟩ → x = β n

/-- Agreement transfers along an environment change confined to temporaries. -/
theorem SlotsAgreeAt.of_onlyTmpBelow {w : Nat} {env env2 : SEnvScalar} {β : String → BitVec w}
    {cnt : Nat} (hag : SlotsAgreeAt w env β) (hotb : OnlyTmpBelow env env2 cnt) :
    SlotsAgreeAt w env2 β := by
  intro n hn x hx
  rw [hotb n (Or.inl hn)] at hx
  exact hag n hn x hx

/-- A slot found by `lookupUW` is read from a consistent environment at `.sword w`. -/
theorem consistentS_lookupUW {w : Nat} {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) (nm : String) {v : CVar Γ (.sword w)}
    (h : lookupUW w vm nm = some v) :
    env nm = some ⟨.sword w, (toVIRVar v).lookup V⟩ := by
  have hlk := hc nm
  simp only [lookupUW] at h
  split at h
  · next w' v' heq =>
      split at h
      · next hw =>
          subst hw
          simp only [Option.some.injEq] at h
          subst h
          rw [heq] at hlk
          exact hlk.symm
      · simp at h
  · simp at h

/-- The slot `lookupUW` finds holds the environment's value of the name. -/
theorem lookupUW_val {w : Nat} {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) {nm : String} {v : CVar Γ (.sword w)}
    (h : lookupUW w vm nm = some v) {x : BitVec w}
    (hx : env nm = some ⟨.sword w, x⟩) : (toVIRVar v).lookup V = x := by
  have h2 := (consistentS_lookupUW hc nm h).symm.trans hx
  simpa using h2

/-- Aliasing `dst` to `src` is consistent with binding `dst` to `src`'s value. -/
theorem consistentS_aliasBind {Γ : Ctx} {vm : VarMap Γ}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar}
    (hc : ConsistentS vm V env) (dst src : String) {t : CryptoTy} {x : ⟦t⟧}
    (hsrc : env src = some ⟨t, x⟩) :
    ConsistentS (aliasBind vm dst src) V (env.upd dst x) := by
  intro s
  by_cases hs : s = dst
  · subst hs
    simp only [aliasBind, SEnvScalar.upd, ↓reduceIte]
    rw [hc src, hsrc]
  · simp only [aliasBind, SEnvScalar.upd, ite_eq_right hs]
    exact hc s

/-! ## 3. The `SExpr` lowering -/

/-- The result of lowering one `SExpr` from `(V, env)` at counter `cnt`: the
    prefix `o.cont` denotes the passage from `V` to a valuation `V'` consistent
    with an environment `env2` that differs from `env` only on temporaries of index
    at least `cnt`, and the result name `nm` holds `x` in `env2`. -/
def LowerOK (w : Nat) {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env : SEnvScalar) (cnt : Nat) (o : DTransOut Γ) (nm : String) (cnt' : Nat)
    (x : BitVec w) : Prop :=
  ∃ (V' : Ctxt.Valuation (d := catCryptDialect) o.Γ') (env2 : SEnvScalar),
    cnt ≤ cnt' ∧ ConsistentS o.vm V' env2 ∧ ContDenotes o.cont V V' ∧
    OnlyTmpBelow env env2 cnt ∧ ResultOK nm cnt' ∧ env2 nm = some ⟨.sword w, x⟩

/-- One `pushVarBindW` of an expression with value `y`, binding `tmpName c`. -/
theorem pushVarBindW_step (w : Nat) {Γ : Ctx}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar} {cnt c : Nat}
    (o : DTransOut Γ) (V₁ : Ctxt.Valuation (d := catCryptDialect) o.Γ')
    (env1 : SEnvScalar) (hcont : ContDenotes o.cont V V₁)
    (hc : ConsistentS o.vm V₁ env1) (hotb : OnlyTmpBelow env env1 cnt) (hle : cnt ≤ c)
    (E : Expr catCryptDialect o.Γ' (.sword w)) (y : BitVec w) (hE : E.denote V₁ = y) :
    LowerOK w V env cnt (pushVarBindW w o E (tmpName c)) (tmpName c) (c + 1) y := by
  obtain ⟨hcons, hstep⟩ := scalar_step o.vm V₁ env1 hc (tmpName c) E
  refine ⟨V₁.extend (E.denote V₁), env1.upd (tmpName c) (E.denote V₁), by omega, hcons,
    ContDenotes.comp hcont (fun tail => hstep tail), ?_,
    Or.inr ⟨c, Nat.lt_succ_self _, rfl⟩, ?_⟩
  · intro s hs
    have hne : s ≠ tmpName c := by
      rcases hs with h1 | ⟨k, hk, rfl⟩
      · exact ne_tmpName_of_not_isTmp h1 c
      · exact tmpName_ne (by omega)
    simp only [SEnvScalar.upd, ite_eq_right hne]
    exact hotb s hs
  · simp [SEnvScalar.upd, hE]

/-- A binary node: both operands lowered, then one op over their result slots. -/
theorem lowerOK_bin (w : Nat) {β : String → BitVec w} {Γ : Ctx}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar} {cnt c1 c2 : Nat}
    {oa : DTransOut Γ} {na : String} {ob : DTransOut oa.Γ'} {nb : String}
    {xa xb : BitVec w} (hag : SlotsAgreeAt w env β)
    (hA : LowerOK w V env cnt oa na c1 xa)
    (hB : ∀ (V₁ : Ctxt.Valuation (d := catCryptDialect) oa.Γ') (env1 : SEnvScalar),
      ConsistentS oa.vm V₁ env1 → SlotsAgreeAt w env1 β → LowerOK w V₁ env1 c1 ob nb c2 xb)
    {va vb : CVar ob.Γ' (.sword w)}
    (hla : lookupUW w ob.vm na = some va) (hlb : lookupUW w ob.vm nb = some vb)
    (f : BitVec w → BitVec w → BitVec w) (E : Expr catCryptDialect ob.Γ' (.sword w))
    (hE : ∀ V₂, E.denote V₂ = f ((toVIRVar va).lookup V₂) ((toVIRVar vb).lookup V₂)) :
    LowerOK w V env cnt (pushVarBindW w (seqOut oa ob) E (tmpName c2)) (tmpName c2)
      (c2 + 1) (f xa xb) := by
  obtain ⟨V₁, env1, hleA, hcA, hcontA, hotbA, hrokA, hvalA⟩ := hA
  obtain ⟨V₂, env2, hleB, hcB, hcontB, hotbB, -, hvalB⟩ :=
    hB V₁ env1 hcA (hag.of_onlyTmpBelow hotbA)
  have hva : (toVIRVar va).lookup V₂ = xa :=
    lookupUW_val hcB hla (by rw [hotbB na hrokA]; exact hvalA)
  have hvb : (toVIRVar vb).lookup V₂ = xb := lookupUW_val hcB hlb hvalB
  exact pushVarBindW_step w (seqOut oa ob) V₂ env2 (ContDenotes.comp hcontA hcontB) hcB
    (onlyTmpBelow_trans hotbA hotbB hleA) (by omega) E (f xa xb)
    ((hE V₂).trans (by rw [hva, hvb]))

/-- A unary node: the operand lowered, then one op over its result slot. -/
theorem lowerOK_un (w : Nat) {Γ : Ctx}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ} {env : SEnvScalar} {cnt c1 : Nat}
    {oa : DTransOut Γ} {na : String} {xa : BitVec w}
    (hA : LowerOK w V env cnt oa na c1 xa)
    {va : CVar oa.Γ' (.sword w)} (hla : lookupUW w oa.vm na = some va)
    (f : BitVec w → BitVec w) (E : Expr catCryptDialect oa.Γ' (.sword w))
    (hE : ∀ V₁, E.denote V₁ = f ((toVIRVar va).lookup V₁)) :
    LowerOK w V env cnt (pushVarBindW w oa E (tmpName c1)) (tmpName c1) (c1 + 1) (f xa) := by
  obtain ⟨V₁, env1, hleA, hcA, hcontA, hotbA, -, hvalA⟩ := hA
  have hva : (toVIRVar va).lookup V₁ = xa := lookupUW_val hcA hla hvalA
  exact pushVarBindW_step w oa V₁ env1 hcontA hcA hotbA hleA E (f xa)
    ((hE V₁).trans (by rw [hva]))

/-- **Denotation of one lowered `SExpr`.** From a state consistent with `env`,
    where `env` agrees with `β` on non-temporary names, the prefix `lowerSExprW`
    emits for a `SrcCleanW` expression denotes a valuation in which its result
    name holds `evalSExprW w β e`. Induction on the `SExpr`. -/
theorem lowerSExprW_denote (w : Nat) (β : String → BitVec w) (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env : SEnvScalar) (cnt : Nat) (o : DTransOut Γ) (nm : String) (cnt' : Nat),
      ConsistentS vm V env → SlotsAgreeAt w env β → SrcCleanW w e →
      lowerSExprW w vm cnt e = some (o, nm, cnt') →
      LowerOK w V env cnt o nm cnt' (evalSExprW w β e) := by
  induction e with
  | SVar x =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      simp only [lowerSExprW] at h
      split at h
      · next v hv =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hx := consistentS_lookupUW hc x hv
          refine ⟨V, env, le_refl _, hc, ContDenotes.id V, onlyTmpBelow_refl env cnt,
            Or.inl hcl, ?_⟩
          rw [hx, hag x hcl _ hx]; rfl
      · simp at h
  | SLit n =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      simp only [lowerSExprW, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact pushVarBindW_step w ⟨Γ, ComCont.id, vm⟩ V env (ContDenotes.id V) hc
        (onlyTmpBelow_refl env cnt) (le_refl _) _ _ rfl
  | SAdd a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hra =>
        split at h
        · simp at h
        · next So hrb =>
          split at h
          · next va vb hla hlb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
              (fun V₁ env1 hc1 hag1 => ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
              hla hlb (· + ·) _ (fun _ => rfl)
          · simp at h
  | SSub a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hra =>
        split at h
        · simp at h
        · next So hrb =>
          split at h
          · next va vb hla hlb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
              (fun V₁ env1 hc1 hag1 => ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
              hla hlb (· - ·) _ (fun _ => rfl)
          · simp at h
  | SMul a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hra =>
        split at h
        · simp at h
        · next So hrb =>
          split at h
          · next va vb hla hlb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
              (fun V₁ env1 hc1 hag1 => ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
              hla hlb (· * ·) _ (fun _ => rfl)
          · simp at h
  | SAnd a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hra =>
        split at h
        · simp at h
        · next So hrb =>
          split at h
          · next va vb hla hlb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
              (fun V₁ env1 hc1 hag1 => ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
              hla hlb (· &&& ·) _ (fun _ => rfl)
          · simp at h
  | SXor a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hra =>
        split at h
        · simp at h
        · next So hrb =>
          split at h
          · next va vb hla hlb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
              (fun V₁ env1 hc1 hag1 => ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
              hla hlb (· ^^^ ·) _ (fun _ => rfl)
          · simp at h
  | SShl a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb, hlit⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · next k =>
        split at h
        · simp at h
        · next Ro hra =>
          split at h
          · next va hla =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hk : k < 2 ^ w := hlit k rfl
            have hval : evalSExprW w β (.SShl a (.SLit k))
                = evalSExprW w β a <<< shiftMask w k := by
              simp only [evalSExprW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
            rw [hval]
            exact lowerOK_un w (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra) hla
              (fun x => x <<< shiftMask w k) _ (fun _ => rfl)
          · simp at h
      · split at h
        · simp at h
        · next Ro hra =>
          split at h
          · simp at h
          · next So hrb =>
            split at h
            · next va vb hla hlb =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
                (fun V₁ env1 hc1 hag1 =>
                  ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
                hla hlb (fun x y => x <<< shiftMask w y.toNat) _ (fun _ => rfl)
            · simp at h
  | SShr a b iha ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, sb, hlit⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · next k =>
        split at h
        · simp at h
        · next Ro hra =>
          split at h
          · next va hla =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hk : k < 2 ^ w := hlit k rfl
            have hval : evalSExprW w β (.SShr a (.SLit k))
                = evalSExprW w β a >>> shiftMask w k := by
              simp only [evalSExprW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
            rw [hval]
            exact lowerOK_un w (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra) hla
              (fun x => x >>> shiftMask w k) _ (fun _ => rfl)
          · simp at h
      · split at h
        · simp at h
        · next Ro hra =>
          split at h
          · simp at h
          · next So hrb =>
            split at h
            · next va vb hla hlb =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact lowerOK_bin w hag (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra)
                (fun V₁ env1 hc1 hag1 =>
                  ihb Ro.1.vm V₁ env1 Ro.2.2 So.1 So.2.1 So.2.2 hc1 hag1 sb hrb)
                hla hlb (fun x y => x >>> shiftMask w y.toNat) _ (fun _ => rfl)
            · simp at h
  | SAsr a b iha _ihb =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      obtain ⟨sa, -, hlit⟩ := hcl
      simp only [lowerSExprW] at h
      split at h
      · next k =>
        split at h
        · simp at h
        · next Ro hra =>
          split at h
          · next va hla =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hk : k < 2 ^ w := hlit k rfl
            have hval : evalSExprW w β (.SAsr a (.SLit k))
                = BitVec.sshiftRight (evalSExprW w β a) k := by
              simp only [evalSExprW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
            rw [hval]
            exact lowerOK_un w (iha vm V env cnt Ro.1 Ro.2.1 Ro.2.2 hc hag sa hra) hla
              (fun x => BitVec.sshiftRight x k) _ (fun _ => rfl)
          · simp at h
      · simp at h
  | SLt a b _ _ | SMulS a b _ _ | SMulHiU a b _ _ | SMulHiS a b _ _ =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      simp [lowerSExprW] at h
  | SLimb v i =>
      intro Γ vm V env cnt o nm cnt' hc hag hcl h
      simp [lowerSExprW] at h

/-! ## 4. The statement sequence -/

/-- **Denotation of the lowered statement sequence.** From a state consistent
    with `env`, where `env` agrees with `β` on non-temporary names, the prefix
    `lowerScalarSetSeqW` emits for a `StmtsClean` statement list denotes a
    valuation consistent with an environment that agrees with `stmtListEnv w β stmts`
    on non-temporary names. Induction on the statement list. -/
theorem lowerScalarSetSeqW_denote (w : Nat) (stmts : List (String × SExpr)) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env : SEnvScalar) (β : String → BitVec w) (cnt : Nat) (out : DTransOut Γ)
      (cntf : Nat),
      ConsistentS vm V env → SlotsAgreeAt w env β → StmtsClean w stmts →
      lowerScalarSetSeqW w vm cnt stmts = some (out, cntf) →
      ∃ (V' : Ctxt.Valuation (d := catCryptDialect) out.Γ') (env' : SEnvScalar),
        ConsistentS out.vm V' env' ∧ ContDenotes out.cont V V' ∧
        SlotsAgreeAt w env' (stmtListEnv w β stmts) := by
  induction stmts with
  | nil =>
      intro Γ vm V env β cnt out cntf hc hag _ h
      simp only [lowerScalarSetSeqW, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨V, env, hc, ContDenotes.id V, hag⟩
  | cons s rest ih =>
      obtain ⟨dst, e⟩ := s
      intro Γ vm V env β cnt out cntf hc hag hcl h
      obtain ⟨hdst, he, hrest⟩ := hcl
      unfold lowerScalarSetSeqW at h
      split at h
      · simp at h
      · next r resName cnt' hl =>
        dsimp only [] at h
        split at h
        · simp at h
        · next tail cntf' ht =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨V₁, env1, -, hc1, hcont1, hotb1, -, hval1⟩ :=
            lowerSExprW_denote w β e vm V env cnt r resName cnt' hc hag he hl
          have hcA := consistentS_aliasBind hc1 dst resName hval1
          have hagA : SlotsAgreeAt w (env1.upd dst (t := .sword w) (evalSExprW w β e))
              (fun n => if n = dst then evalSExprW w β e else β n) := by
            intro n hn x hx
            by_cases hnd : n = dst
            · subst hnd
              simp only [SEnvScalar.upd] at hx
              simpa using hx.symm
            · simp only [SEnvScalar.upd, ite_eq_right hnd] at hx
              simp only [ite_eq_right hnd]
              exact (hag.of_onlyTmpBelow hotb1) n hn x hx
          obtain ⟨V', env', hc', hcont', hag'⟩ :=
            ih (aliasBind r.vm dst resName) V₁ _ _ cnt' tail cntf' hcA hagA hrest ht
          exact ⟨V', env', hc', ContDenotes.comp hcont1 hcont', hag'⟩

/-- **Denotation of the sequencer's program.** If `seqProg w vm stmts r` returns
    `com`, the `.sword w` slots `vm` binds to non-temporary names hold the values
    of `β`, the statements are `StmtsClean` and `r` is not a temporary, then `com`
    denotes the value of `r` in the environment the statement list produces. -/
theorem seqProg_denote (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (r : String)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (β : String → BitVec w)
    (hin : ∀ n (v : CVar Γ (.sword w)), ¬ isTmpName n →
      vm.lookup n = some ⟨.sword w, v⟩ → (toVIRVar v).lookup V = β n)
    (hcl : StmtsClean w stmts) (hr : ¬ isTmpName r)
    {com : Com catCryptDialect Γ (.sword w)} (hsp : seqProg w vm stmts r = some com) :
    com.denote V = stmtListEnv w β stmts r := by
  let env0 : SEnvScalar := fun s =>
    (vm.lookup s).map (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))
  have hc0 : ConsistentS vm V env0 := fun _ => rfl
  have hag0 : SlotsAgreeAt w env0 β := by
    intro n hn x hx
    simp only [env0] at hx
    cases hlk : vm.lookup n with
    | none => rw [hlk] at hx; simp at hx
    | some p =>
        obtain ⟨t, v⟩ := p
        rw [hlk] at hx
        simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hx
        obtain ⟨rfl, hxv⟩ := hx
        rw [← eq_of_heq hxv]
        exact hin n v hn hlk
  unfold seqProg at hsp
  split at hsp
  · next out cntf hlo =>
    obtain ⟨V', env', hc', hcont', hag'⟩ :=
      lowerScalarSetSeqW_denote w stmts vm V env0 β 0 out cntf hc0 hag0 hcl hlo
    split at hsp
    · next w' v hlr =>
      split at hsp
      · next hw =>
        subst hw
        obtain ⟨com', hcom', hden⟩ := hcont' (Com.ret (toVIRVar v))
        have hcc : com' = com := Option.some.inj (hcom'.symm.trans hsp)
        subst hcc
        rw [hden]
        have hx := hc' r
        rw [hlr] at hx
        exact hag' r hr _ hx.symm
      · simp at hsp
    · simp at hsp
  · simp at hsp

/-! ## 5. Composition with the jasmin lowering -/

/-- **Denotation of the jasmin program.** The `jasminDialect` program
    `cryptoDialectToJasminCom` produces from the sequencer's program denotes, on
    the transported valuation, the value of `r` in the environment the statement
    list produces. -/
theorem seqProg_jasmin_denote (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (r : String)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (β : String → BitVec w)
    (hin : ∀ n (v : CVar Γ (.sword w)), ¬ isTmpName n →
      vm.lookup n = some ⟨.sword w, v⟩ → (toVIRVar v).lookup V = β n)
    (hcl : StmtsClean w stmts) (hr : ¬ isTmpName r)
    {com : Com catCryptDialect Γ (.sword w)} (hsp : seqProg w vm stmts r = some com)
    {jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ)
      (CryptoToJasminCom.mapTy (.sword w))}
    (hj : DialectToJasminCom.cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (DialectToJasminComCorrect.ctMapValD V) = stmtListEnv w β stmts r := by
  rw [DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq' com V jcom hj,
    ← seqProg_denote w vm stmts r V β hin hcl hr hsp]
  rfl

/-- **The jasmin program exists and has the source value.** For a coverable
    statement list whose program resolves, the jasmin lowering of the sequencer's
    program succeeds and denotes the value of `r` in the environment the statement
    list produces. -/
theorem seqProg_jasmin_exists_denote (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (r : String)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (β : String → BitVec w)
    (hin : ∀ n (v : CVar Γ (.sword w)), ¬ isTmpName n →
      vm.lookup n = some ⟨.sword w, v⟩ → (toVIRVar v).lookup V = β n)
    (hcl : StmtsClean w stmts) (hr : ¬ isTmpName r) (hcov : SeqCovers w vm 0 stmts)
    {com : Com catCryptDialect Γ (.sword w)} (hsp : seqProg w vm stmts r = some com) :
    ∃ jcom, (seqProg w vm stmts r).bind DialectToJasminCom.cryptoDialectToJasminCom
        = some jcom ∧
      jcom.denote (DialectToJasminComCorrect.ctMapValD V) = stmtListEnv w β stmts r := by
  obtain ⟨jcom, hj⟩ := Option.isSome_iff_exists.mp
    (cryptoDialectToJasminCom_isSome com (seqProg_comJLowerable w vm stmts r hcov hsp))
  refine ⟨jcom, by rw [hsp]; exact hj, ?_⟩
  exact seqProg_jasmin_denote w vm stmts r V β hin hcl hr hsp hj

/-! ## 6. The bindings of the sequencer's program

`Optimizer.ComDCE.bindVals c V` lists the values of the bindings of `c` run from `V`,
in binding order. `nBindsS e` is the number of bindings `lowerSExprW` emits for `e`
and `stmtsBinds stmts` the number the sequencer emits for a statement list. The last
binding a statement `(x, e)` with `nBindsS e ≠ 0` emits holds the value of `e`, so
entry `stmtsBinds pre + nBindsS e - 1` of the binding list is the value of `x` after
the statements `pre` before it and the statement itself (`seqProg_bindVals`). The
jasmin lowering keeps the binding values (`cryptoDialectToJasminCom_bindVals`), which
gives the same entry for the `jasminDialect` program (`seqProg_jasmin_bindVals`). -/

/-- The number of bindings `lowerSExprW` emits for an expression: none for a variable,
    one for a literal and one per operator node; a shift by a literal binds no
    constant for the count. -/
def nBindsS : SExpr → Nat
  | .SVar _ => 0
  | .SLit _ => 1
  | .SAdd a b | .SSub a b | .SMul a b | .SAnd a b | .SXor a b =>
      nBindsS a + nBindsS b + 1
  | .SShl a b | .SShr a b =>
      match b with
      | .SLit _ => nBindsS a + 1
      | _ => nBindsS a + nBindsS b + 1
  | .SAsr a _ => nBindsS a + 1
  | _ => 0

/-- The number of bindings the sequencer emits for a statement list. -/
def stmtsBinds : List (String × SExpr) → Nat
  | [] => 0
  | (_, e) :: rest => nBindsS e + stmtsBinds rest

theorem stmtsBinds_append (l₁ l₂ : List (String × SExpr)) :
    stmtsBinds (l₁ ++ l₂) = stmtsBinds l₁ + stmtsBinds l₂ := by
  induction l₁ with
  | nil => simp [stmtsBinds]
  | cons p l ih =>
    obtain ⟨x, e⟩ := p
    simp only [List.cons_append, stmtsBinds, ih, Nat.add_assoc]

theorem nBindsS_shl_of_not_lit {a b : SExpr} (hb : ∀ k, b = .SLit k → False) :
    nBindsS (.SShl a b) = nBindsS a + nBindsS b + 1 := by
  cases b <;> first | rfl | exact absurd rfl (hb _)

theorem nBindsS_shr_of_not_lit {a b : SExpr} (hb : ∀ k, b = .SLit k → False) :
    nBindsS (.SShr a b) = nBindsS a + nBindsS b + 1 := by
  cases b <;> first | rfl | exact absurd rfl (hb _)

/-- The prefix `f` sends every tail to a program whose bindings run from `V` are `L`
    followed by the bindings of the tail run from `V'`. -/
def ContBinds {Γ Γ' : Ctx} (f : ComCont Γ Γ')
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (V' : Ctxt.Valuation (d := catCryptDialect) Γ') (L : List ((u : CryptoTy) × ⟦u⟧)) :
    Prop :=
  ∀ {t : CryptoTy} (tail : Com catCryptDialect Γ' t),
    ∃ com, f tail = some com ∧
      Optimizer.ComDCE.bindVals com V = L ++ Optimizer.ComDCE.bindVals tail V'

/-- The identity prefix emits no binding. -/
theorem ContBinds.id {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ContBinds (ComCont.id (Γ := Γ)) V V [] :=
  fun tail => ⟨tail, rfl, rfl⟩

/-- A `varBind` prefix emits one binding, the value of its expression. -/
theorem ContBinds.varBind {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ContBinds (ComCont.varBind e) V (V.extend (e.denote V)) [⟨s, e.denote V⟩] :=
  fun tail => ⟨Com.var e tail, rfl, rfl⟩

/-- The bindings of composed prefixes are concatenated. -/
theorem ContBinds.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {V₁ : Ctxt.Valuation (d := catCryptDialect) Γ'}
    {V₂ : Ctxt.Valuation (d := catCryptDialect) Γ''}
    {L₁ L₂ : List ((u : CryptoTy) × ⟦u⟧)}
    (hf : ContBinds f V V₁ L₁) (hg : ContBinds g V₁ V₂ L₂) :
    ContBinds (ComCont.comp f g) V V₂ (L₁ ++ L₂) := by
  intro t tail
  obtain ⟨b, hb, hbv⟩ := hg tail
  obtain ⟨c, hc, hcv⟩ := hf b
  refine ⟨c, ?_, by rw [hcv, hbv, List.append_assoc]⟩
  show ComCont.comp f g tail = some c
  unfold ComCont.comp
  rw [hb]; exact hc

/-- Two valuations of a context that agree on every variable are equal. -/
theorem valuation_eq_of_lookup : {Γ : Ctx} →
    (V₁ V₂ : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (∀ {t : CryptoTy} (v : Ctxt.Var (d := catCryptDialect) Γ t), v.lookup V₁ = v.lookup V₂) →
    V₁ = V₂
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x V₁, .cons y V₂, h => by
      have hx : x = y := h .here
      have hV : V₁ = V₂ := valuation_eq_of_lookup V₁ V₂ (fun v => h (.there v))
      subst hx hV
      rfl

/-- The valuation a prefix denotes from `V` is unique. -/
theorem ContDenotes.unique {Γ Γ' : Ctx} {f : ComCont Γ Γ'}
    {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {V₁ V₂ : Ctxt.Valuation (d := catCryptDialect) Γ'}
    (h₁ : ContDenotes f V V₁) (h₂ : ContDenotes f V V₂) : V₁ = V₂ := by
  refine valuation_eq_of_lookup V₁ V₂ (fun {t} v => ?_)
  obtain ⟨c₁, hc₁, hd₁⟩ := h₁ (Com.ret v)
  obtain ⟨c₂, hc₂, hd₂⟩ := h₂ (Com.ret v)
  rw [hc₁, Option.some.injEq] at hc₂
  subst hc₂
  exact hd₁.symm.trans hd₂

/-- The prefix `o.cont` run from `V` denotes a valuation `V'` and emits `n` bindings;
    when `n ≠ 0` the last of them is the value the result name `nm` holds in `V'`. -/
def BindsOK (w : Nat) {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (o : DTransOut Γ) (nm : String) (n : Nat) : Prop :=
  ∃ (V' : Ctxt.Valuation (d := catCryptDialect) o.Γ') (L : List ((u : CryptoTy) × ⟦u⟧)),
    ContDenotes o.cont V V' ∧ ContBinds o.cont V V' L ∧ L.length = n ∧
    (n ≠ 0 → ∃ v : CVar o.Γ' (.sword w), lookupUW w o.vm nm = some v ∧
      L.getLast? = some ⟨.sword w, (toVIRVar v).lookup V'⟩)

/-- The identity output emits no binding. -/
theorem BindsOK.idOut (w : Nat) {Γ : Ctx} (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (vm : VarMap Γ) (nm : String) : BindsOK w V ⟨Γ, ComCont.id, vm⟩ nm 0 :=
  ⟨V, [], ContDenotes.id V, ContBinds.id V, rfl, fun h => absurd rfl h⟩

/-- One `pushVarBindW` after a prefix of `n` bindings emits `n + 1` bindings, the last
    the value of the pushed expression, which the pushed name holds. -/
theorem BindsOK.push (w : Nat) {Γ : Ctx} {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {o : DTransOut Γ} {V₁ : Ctxt.Valuation (d := catCryptDialect) o.Γ'}
    {L : List ((u : CryptoTy) × ⟦u⟧)} {n : Nat}
    (hd : ContDenotes o.cont V V₁) (hb : ContBinds o.cont V V₁ L) (hlen : L.length = n)
    (E : Expr catCryptDialect o.Γ' (.sword w)) (nm : String) :
    BindsOK w V (pushVarBindW w o E nm) nm (n + 1) := by
  refine ⟨V₁.extend (E.denote V₁), L ++ [⟨.sword w, E.denote V₁⟩],
    ContDenotes.comp hd (fun tail => ⟨Com.var E tail, rfl, rfl⟩),
    ?_, by simp [hlen], fun _ => ⟨.here, ?_, ?_⟩⟩
  · exact ContBinds.comp hb (ContBinds.varBind E V₁)
  · simp [pushVarBindW, lookupUW, LowCTToCryptoSSA.VarMap.bind]
  · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    rfl

/-- A `pushVarBindW` after two outputs in sequence. -/
theorem BindsOK.seqPush (w : Nat) {Γ : Ctx} {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {oa : DTransOut Γ} {ob : DTransOut oa.Γ'} {na nb : String} {nA nB : Nat}
    (hA : BindsOK w V oa na nA)
    (hB : ∀ V₁ : Ctxt.Valuation (d := catCryptDialect) oa.Γ', BindsOK w V₁ ob nb nB)
    (E : Expr catCryptDialect ob.Γ' (.sword w)) (nm : String) :
    BindsOK w V (pushVarBindW w (seqOut oa ob) E nm) nm (nA + nB + 1) := by
  obtain ⟨V₁, L₁, hd1, hb1, hl1, -⟩ := hA
  obtain ⟨V₂, L₂, hd2, hb2, hl2, -⟩ := hB V₁
  exact BindsOK.push w (o := seqOut oa ob) (ContDenotes.comp hd1 hd2)
    (ContBinds.comp hb1 hb2) (by simp [hl1, hl2]) E nm

/-- A `pushVarBindW` after one output. -/
theorem BindsOK.push1 (w : Nat) {Γ : Ctx} {V : Ctxt.Valuation (d := catCryptDialect) Γ}
    {oa : DTransOut Γ} {na : String} {nA : Nat} (hA : BindsOK w V oa na nA)
    (E : Expr catCryptDialect oa.Γ' (.sword w)) (nm : String) :
    BindsOK w V (pushVarBindW w oa E nm) nm (nA + 1) := by
  obtain ⟨V₁, L₁, hd1, hb1, hl1, -⟩ := hA
  exact BindsOK.push w hd1 hb1 hl1 E nm

/-- **The bindings of one lowered `SExpr`.** The prefix `lowerSExprW` emits for `e`
    emits `nBindsS e` bindings, and when there is one, the last is the value its result
    name holds. Induction on the `SExpr`. -/
theorem lowerSExprW_binds (w : Nat) (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (o : DTransOut Γ) (nm : String) (cnt' : Nat),
      lowerSExprW w vm cnt e = some (o, nm, cnt') →
      ∀ V : Ctxt.Valuation (d := catCryptDialect) Γ, BindsOK w V o nm (nBindsS e) := by
  induction e with
  | SVar x =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact BindsOK.idOut w V vm x
      · simp at h
  | SLit n =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact BindsOK.push w (o := ⟨Γ, ComCont.id, vm⟩) (ContDenotes.id V) (ContBinds.id V)
        rfl _ _
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact BindsOK.seqPush w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V)
              (fun V₁ => ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb V₁) _ _
          · simp at h
  | SShl a b iha ihb =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW] at h
      split at h
      · split at h
        · simp at h
        · next Ro hla =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact BindsOK.push1 w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V) _ _
          · simp at h
      · rw [nBindsS_shl_of_not_lit (a := a) (b := b) (by assumption)]
        split at h
        · simp at h
        · next Ro hla =>
          split at h
          · simp at h
          · next So hlb =>
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, -⟩ := h
              exact BindsOK.seqPush w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V)
                (fun V₁ => ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb V₁) _ _
            · simp at h
  | SShr a b iha ihb =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW] at h
      split at h
      · split at h
        · simp at h
        · next Ro hla =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact BindsOK.push1 w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V) _ _
          · simp at h
      · rw [nBindsS_shr_of_not_lit (a := a) (b := b) (by assumption)]
        split at h
        · simp at h
        · next Ro hla =>
          split at h
          · simp at h
          · next So hlb =>
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, -⟩ := h
              exact BindsOK.seqPush w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V)
                (fun V₁ => ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb V₁) _ _
            · simp at h
  | SAsr a b iha _ =>
      intro Γ vm cnt o nm cnt' h V
      simp only [lowerSExprW] at h
      split at h
      · split at h
        · simp at h
        · next Ro hla =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            exact BindsOK.push1 w (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla V) _ _
          · simp at h
      · simp at h
  | SLt a b _ _ | SMulS a b _ _ | SMulHiU a b _ _ | SMulHiS a b _ _ =>
      intro Γ vm cnt o nm cnt' h V
      simp [lowerSExprW] at h
  | SLimb v i =>
      intro Γ vm cnt o nm cnt' h V
      simp [lowerSExprW] at h

/-- **The bindings of the lowered statement sequence.** Under the hypotheses of
    `lowerScalarSetSeqW_denote`, the prefix `lowerScalarSetSeqW` emits denotes a
    valuation `V'` and emits `stmtsBinds stmts` bindings `L`; for a statement `(x, e)`
    after the statements `pre` with `nBindsS e ≠ 0`, entry
    `stmtsBinds pre + nBindsS e - 1` of `L` is the value of `e` in the environment
    `pre` produces. Induction on the statement list. -/
theorem lowerScalarSetSeqW_binds (w : Nat) (stmts : List (String × SExpr)) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env : SEnvScalar) (β : String → BitVec w) (cnt : Nat) (out : DTransOut Γ)
      (cntf : Nat),
      ConsistentS vm V env → SlotsAgreeAt w env β → StmtsClean w stmts →
      lowerScalarSetSeqW w vm cnt stmts = some (out, cntf) →
      ∃ (V' : Ctxt.Valuation (d := catCryptDialect) out.Γ')
        (L : List ((u : CryptoTy) × ⟦u⟧)),
        ContDenotes out.cont V V' ∧ ContBinds out.cont V V' L ∧
        L.length = stmtsBinds stmts ∧
        ∀ (pre : List (String × SExpr)) (x : String) (e : SExpr)
          (suf : List (String × SExpr)),
          stmts = pre ++ (x, e) :: suf → nBindsS e ≠ 0 →
          L[stmtsBinds pre + nBindsS e - 1]?
            = some ⟨.sword w, evalSExprW w (stmtListEnv w β pre) e⟩ := by
  induction stmts with
  | nil =>
      intro Γ vm V env β cnt out cntf _ _ _ h
      simp only [lowerScalarSetSeqW, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨V, [], ContDenotes.id V, ContBinds.id V, rfl, fun pre x e suf hs _ => ?_⟩
      exact absurd hs.symm (by simp)
  | cons s rest ih =>
      obtain ⟨dst, e0⟩ := s
      intro Γ vm V env β cnt out cntf hc hag hcl h
      obtain ⟨_, he, hrest⟩ := hcl
      unfold lowerScalarSetSeqW at h
      split at h
      · simp at h
      · next r resName cnt' hl =>
        dsimp only [] at h
        split at h
        · simp at h
        · next tail cntf' ht =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨V₁, env1, -, hc1, hcont1, hotb1, -, hval1⟩ :=
            lowerSExprW_denote w β e0 vm V env cnt r resName cnt' hc hag he hl
          obtain ⟨V₁', L₁, hd1, hb1, hl1, hlast⟩ :=
            lowerSExprW_binds w e0 vm cnt r resName cnt' hl V
          obtain rfl : V₁' = V₁ := hd1.unique hcont1
          have hcA := consistentS_aliasBind hc1 dst resName hval1
          have hagA : SlotsAgreeAt w (env1.upd dst (t := .sword w) (evalSExprW w β e0))
              (fun n => if n = dst then evalSExprW w β e0 else β n) := by
            intro n hn x hx
            by_cases hnd : n = dst
            · subst hnd
              simp only [SEnvScalar.upd] at hx
              simpa using hx.symm
            · simp only [SEnvScalar.upd, ite_eq_right hnd] at hx
              simp only [ite_eq_right hnd]
              exact (hag.of_onlyTmpBelow hotb1) n hn x hx
          obtain ⟨V', L₂, hd2, hb2, hl2, hidx⟩ :=
            ih (aliasBind r.vm dst resName) V₁' _ _ cnt' tail cntf' hcA hagA hrest ht
          refine ⟨V', L₁ ++ L₂, ContDenotes.comp hd1 hd2, ContBinds.comp hb1 hb2,
            by simp [stmtsBinds, hl1, hl2], ?_⟩
          intro pre x e suf hs hne
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hs
            obtain ⟨⟨rfl, rfl⟩, -⟩ := hs
            obtain ⟨v, hv, hgl⟩ := hlast hne
            have hx : (toVIRVar v).lookup V₁' = evalSExprW w β e0 :=
              lookupUW_val hc1 hv hval1
            rw [List.getLast?_eq_getElem?, hl1] at hgl
            simp only [stmtsBinds, stmtListEnv, Nat.zero_add]
            rw [List.getElem?_append_left (by omega), hgl, hx]
          | cons p pre' =>
            simp only [List.cons_append, List.cons.injEq] at hs
            obtain ⟨rfl, hs'⟩ := hs
            have hi := hidx pre' x e suf hs' hne
            simp only [stmtsBinds, stmtListEnv]
            rw [List.getElem?_append_right (by omega), hl1,
              show nBindsS e0 + stmtsBinds pre' + nBindsS e - 1 - nBindsS e0
                = stmtsBinds pre' + nBindsS e - 1 by omega]
            exact hi

/-- **The bindings of the sequencer's program.** Under the hypotheses of
    `seqProg_denote` (without the hygiene of `r`), the program `seqProg w vm stmts r`
    has `stmtsBinds stmts` bindings, and for a statement `(x, e)` after the statements
    `pre` with `nBindsS e ≠ 0`, binding `stmtsBinds pre + nBindsS e - 1` is the value
    of `e` in the environment `pre` produces, the value of `x` after the statement. -/
theorem seqProg_bindVals (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (r : String)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (β : String → BitVec w)
    (hin : ∀ n (v : CVar Γ (.sword w)), ¬ isTmpName n →
      vm.lookup n = some ⟨.sword w, v⟩ → (toVIRVar v).lookup V = β n)
    (hcl : StmtsClean w stmts)
    {com : Com catCryptDialect Γ (.sword w)} (hsp : seqProg w vm stmts r = some com) :
    (Optimizer.ComDCE.bindVals com V).length = stmtsBinds stmts ∧
      ∀ (pre : List (String × SExpr)) (x : String) (e : SExpr)
        (suf : List (String × SExpr)),
        stmts = pre ++ (x, e) :: suf → nBindsS e ≠ 0 →
        (Optimizer.ComDCE.bindVals com V)[stmtsBinds pre + nBindsS e - 1]?
          = some ⟨.sword w, evalSExprW w (stmtListEnv w β pre) e⟩ := by
  let env0 : SEnvScalar := fun s =>
    (vm.lookup s).map (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))
  have hc0 : ConsistentS vm V env0 := fun _ => rfl
  have hag0 : SlotsAgreeAt w env0 β := by
    intro n hn x hx
    simp only [env0] at hx
    cases hlk : vm.lookup n with
    | none => rw [hlk] at hx; simp at hx
    | some p =>
        obtain ⟨t, v⟩ := p
        rw [hlk] at hx
        simp only [Option.map_some, Option.some.injEq, Sigma.mk.injEq] at hx
        obtain ⟨rfl, hxv⟩ := hx
        rw [← eq_of_heq hxv]
        exact hin n v hn hlk
  unfold seqProg at hsp
  split at hsp
  · next out cntf hlo =>
    obtain ⟨V', L, -, hb, hlen, hidx⟩ :=
      lowerScalarSetSeqW_binds w stmts vm V env0 β 0 out cntf hc0 hag0 hcl hlo
    split at hsp
    · next w' v hlr =>
      split at hsp
      · next hw =>
        subst hw
        obtain ⟨com', hcom', hbv⟩ := hb (Com.ret (toVIRVar v))
        have hcc : com' = com := Option.some.inj (hcom'.symm.trans hsp)
        subst hcc
        have hL : Optimizer.ComDCE.bindVals com' V = L := by
          rw [hbv]; simp [Optimizer.ComDCE.bindVals]
        rw [hL]
        exact ⟨hlen, hidx⟩
      · simp at hsp
    · simp at hsp
  · simp at hsp

/-- `cryptoDialectToJasminCom` keeps the binding values: the bindings of the lowered
    program run from the transported valuation are the bindings of the source program,
    each transported by `ctTransTy`. Induction on the `Com`. -/
theorem cryptoDialectToJasminCom_bindVals {Γ : Ctx} {t : CryptoTy} :
    (com : Com catCryptDialect Γ t) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ) (CryptoToJasminCom.mapTy t)) →
    DialectToJasminCom.cryptoDialectToJasminCom com = some jcom →
    Optimizer.ComDCE.bindVals jcom (DialectToJasminComCorrect.ctMapValD V)
      = (Optimizer.ComDCE.bindVals com V).map
          (fun p => ⟨CryptoToJasminCom.mapTy p.1, CryptoToJasminComCorrect.ctTransTy p.2⟩)
  | .ret v, V, jcom, hcom => by
      simp only [DialectToJasminCom.cryptoDialectToJasminCom, Option.some.injEq] at hcom
      subst hcom
      rfl
  | .var e body, V, jcom, hcom => by
      simp only [DialectToJasminCom.cryptoDialectToJasminCom] at hcom
      split at hcom
      · next e' he =>
          split at hcom
          · next body' hbody =>
              simp only [Option.some.injEq] at hcom
              subst hcom
              have hval := DialectToJasminComCorrect.dialectJasminLeafAgrees_holds e V e' he
              have ih := cryptoDialectToJasminCom_bindVals body (V.extend (e.denote V)) body'
                hbody
              simp only [Optimizer.ComDCE.bindVals, List.map_cons]
              rw [hval, ← DialectToJasminComCorrect.ctMapValD_extend V (e.denote V), ih]
          · exact absurd hcom (by simp)
      · exact absurd hcom (by simp)

/-- **The bindings of the jasmin program.** `seqProg_bindVals` for the `jasminDialect`
    program `cryptoDialectToJasminCom` makes of the sequencer's program, on the
    transported valuation: binding `stmtsBinds pre + nBindsS e - 1` is the register
    holding the value of `e` in the environment the statements `pre` produce. -/
theorem seqProg_jasmin_bindVals (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (r : String)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (β : String → BitVec w)
    (hin : ∀ n (v : CVar Γ (.sword w)), ¬ isTmpName n →
      vm.lookup n = some ⟨.sword w, v⟩ → (toVIRVar v).lookup V = β n)
    (hcl : StmtsClean w stmts)
    {com : Com catCryptDialect Γ (.sword w)} (hsp : seqProg w vm stmts r = some com)
    {jcom : Com jasminDialect (CryptoToJasminCom.mapCtx Γ)
      (CryptoToJasminCom.mapTy (.sword w))}
    (hj : DialectToJasminCom.cryptoDialectToJasminCom com = some jcom) :
    (Optimizer.ComDCE.bindVals jcom (DialectToJasminComCorrect.ctMapValD V)).length
        = stmtsBinds stmts ∧
      ∀ (pre : List (String × SExpr)) (x : String) (e : SExpr)
        (suf : List (String × SExpr)),
        stmts = pre ++ (x, e) :: suf → nBindsS e ≠ 0 →
        (Optimizer.ComDCE.bindVals jcom (DialectToJasminComCorrect.ctMapValD V))[
            stmtsBinds pre + nBindsS e - 1]?
          = some ⟨.reg w, evalSExprW w (stmtListEnv w β pre) e⟩ := by
  obtain ⟨hlen, hidx⟩ := seqProg_bindVals w vm stmts r V β hin hcl hsp
  rw [cryptoDialectToJasminCom_bindVals com V jcom hj]
  refine ⟨by rw [List.length_map, hlen], fun pre x e suf hs hne => ?_⟩
  rw [List.getElem?_map, hidx pre x e suf hs hne]
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
