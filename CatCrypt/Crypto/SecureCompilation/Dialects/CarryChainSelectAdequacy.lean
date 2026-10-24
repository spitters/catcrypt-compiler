/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect
public import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# Source semantics of the carry-chain-selected windows

`CarryChainSelect.translateDialectCarrySelect` flattens a `LowCT` body to a
command list, rewrites the five recognised `bSltu` carry/borrow windows to
`bvAddCarryLo`/`bvAddCarryHi` pairs, and falls through to
`translateDialectControl` on everything else.  Its per-rewrite value
obligations are `BitVec` identities (`CarryChainSelect.select_addStart_data`,
`select_addStart_carry`, …).

This module lifts those identities from `BitVec` to the `LowCT` scalar
operational semantics `TranslateDialectScalar.semScalar`: for each window shape
it computes the value the *plain* source commands leave in the window's data
and carry slots, and identifies it with the `addCarryWordC` / `carryOutBitC`
waist the selected emission binds.  A mid-chain window is stated against the
incoming carry bit, with the chain invariant — the source's carry word is the
widened bit — as an explicit hypothesis.

It also records where the selected front's `VarMap` differs from the plain
front's on the same body: the window's scratch slots are not bound, and a carry
slot is bound as a word only when some other step reads it as one.

## Main results

* `semScalar_flattenSeq` — `flattenSeq` preserves the scalar semantics, so a
  statement about the command list the selector walks is a statement about the
  `RSeq` spine it came from.
* `ltuWindow_sem` — the three-command `ltuCmds` window leaves `ltuIdiom` of its
  two operand values in its destination slot and every other non-temporary slot
  untouched.
* `addStartWindow_sem`, `addMidWindow_sem`, `addFinWindow_sem`,
  `subStartWindow_sem`, `subMidWindow_sem` — the five recognised windows: the
  data slot holds `addCarryWordC`, the carry slot holds the widened
  `carryOutBitC`, and a borrow slot holds its complement.
* `frontBinds` / `frontCaps` — whether a front's output `VarMap` binds a name,
  and whether it binds it at the accumulator type. The two fronts' answers on a
  body whose carry-out is read nowhere downstream, and whether the accumulator
  cap accepts each, are pinned with `#guard`, which declares no name.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The command-list semantics the selector walks -/

/-- Left-to-right `semScalar` of a command list — the semantics of the
    flattened spine `selectGo` consumes. -/
def semList : List LowCT → SEnvScalar → Option SEnvScalar
  | [], env => some env
  | c :: cs, env =>
      match semScalar c env with
      | some e => semList cs e
      | none => none

theorem semList_nil (env : SEnvScalar) : semList [] env = some env := rfl

theorem semList_cons (c : LowCT) (cs : List LowCT) (env : SEnvScalar) :
    semList (c :: cs) env = (semScalar c env).bind (semList cs) := by
  cases h : semScalar c env with
  | none => simp [semList, h]
  | some e => simp [semList, h]

theorem semList_single (c : LowCT) (env : SEnvScalar) :
    semList [c] env = semScalar c env := by
  rw [semList_cons]
  cases semScalar c env with
  | none => rfl
  | some e => rfl

/-- Peel the head command off a successful list run. -/
theorem semList_cons_eq {c : LowCT} {cs : List LowCT} {env env' : SEnvScalar}
    (h : semList (c :: cs) env = some env') :
    ∃ e, semScalar c env = some e ∧ semList cs e = some env' := by
  rw [semList_cons] at h
  cases hc : semScalar c env with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some e =>
      refine ⟨e, rfl, ?_⟩
      rw [hc] at h
      simpa using h

theorem semList_append (l₁ l₂ : List LowCT) (env : SEnvScalar) :
    semList (l₁ ++ l₂) env = (semList l₁ env).bind (semList l₂) := by
  induction l₁ generalizing env with
  | nil => simp [semList_nil]
  | cons c cs ih =>
      simp only [List.cons_append, semList_cons]
      cases semScalar c env with
      | none => rfl
      | some e => simpa using ih e

/-- **`flattenSeq` preserves the scalar semantics.** Dropping the `RSkip`s and
    re-associating the `RSeq` spine into a command list leaves the `semScalar`
    transformer unchanged. -/
theorem semScalar_flattenSeq (c : LowCT) (env : SEnvScalar) :
    semList (flattenSeq c) env = semScalar c env := by
  induction c generalizing env with
  | RSeq a b iha ihb =>
      simp only [flattenSeq, semList_append, semScalar, iha]
      cases semScalar a env with
      | none => rfl
      | some e => simpa using ihb e
  | _ => simp [flattenSeq, semList_nil, semList_single, semScalar]

/-! ## 2. Reading back one `RScalarSetExpr` -/

/-- The `SExpr` lowering mirror writes only fresh temporaries: every
    non-temporary slot keeps its value across `semLowerSExpr`. -/
theorem semLowerSExpr_off_tmp :
    ∀ (e : SExpr) (env env₂ : SEnvScalar) (cnt cnt' : Nat) (nm s : String),
      semLowerSExpr env cnt e = some (env₂, nm, cnt') → ¬ isTmpName s → env₂ s = env s := by
  intro e
  induction e with
  | SVar x =>
      intro env env₂ cnt cnt' nm s h _
      simp only [semLowerSExpr] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h; rfl
      · exact absurd h (by simp)
  | SLit n =>
      intro env env₂ cnt cnt' nm s h hs
      simp only [semLowerSExpr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp only [SEnvScalar.upd, ite_eq_right (ne_tmpName_of_not_isTmp hs cnt)]
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb
  | SMulHiU a b iha ihb =>
      intro env env₂ cnt cnt' nm s h hs
      simp only [semLowerSExpr] at h
      split at h
      · next e1 na c1 h1 =>
          split at h
          · next e2 nb c2 h2 =>
              simp only [binNode] at h
              split at h
              · next va vb _ _ =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, -, -⟩ := h
                  simp only [SEnvScalar.upd, ite_eq_right (ne_tmpName_of_not_isTmp hs c2)]
                  rw [ihb e1 e2 c1 c2 nb s h2 hs, iha env e1 cnt c1 na s h1 hs]
              · exact absurd h (by simp)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | SLt a b _ _ | SAsr a b _ _ | SMulS a b _ _ | SMulHiS a b _ _ =>
      intro env env₂ cnt cnt' nm s h _
      simp only [semLowerSExpr] at h
      exact absurd h (by simp)
  | SLimb v i =>
      intro env env₂ cnt cnt' nm s h _
      simp only [semLowerSExpr] at h
      exact absurd h (by simp)

/-- **One scalar assignment, read back.** `RScalarSetExpr x e` binds `x` to the
    closed-form word evaluator and leaves every other non-temporary slot
    alone. -/
theorem semScalar_setExpr_eq {x : String} {e : SExpr} {env env' : SEnvScalar}
    (h : semScalar (.RScalarSetExpr x e) env = some env') :
    env' x = some ⟨.sword 64, SExpr.evalBV (envReader env) e⟩ ∧
      ∀ s, ¬ isTmpName s → s ≠ x → env' s = env s := by
  simp only [semScalar] at h
  cases hlow : semLowerSExpr env 0 e with
  | none => rw [hlow] at h; exact absurd h (by simp)
  | some p =>
      obtain ⟨env₂, nm, k⟩ := p
      rw [hlow] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp [SEnvScalar.upd], ?_⟩
      intro s hs hne
      simp only [SEnvScalar.upd, ite_eq_right hne]
      exact semLowerSExpr_off_tmp e env env₂ 0 k nm s hlow hs

/-- The word reader after one scalar assignment, at the assigned slot. -/
theorem envReader_setExpr_at {x : String} {e : SExpr} {env env' : SEnvScalar}
    (h : semScalar (.RScalarSetExpr x e) env = some env') :
    envReader env' x = SExpr.evalBV (envReader env) e := by
  simp only [envReader, (semScalar_setExpr_eq h).1]

/-- The word reader after one scalar assignment, off the assigned slot. -/
theorem envReader_setExpr_off {x : String} {e : SExpr} {env env' : SEnvScalar}
    (h : semScalar (.RScalarSetExpr x e) env = some env') (s : String)
    (hs : ¬ isTmpName s) (hne : s ≠ x) : envReader env' s = envReader env s := by
  simp only [envReader, (semScalar_setExpr_eq h).2 s hs hne]

/-! ## 3. `SExpr` readers agreeing on the read variables -/

/-- The variables of a `srcClean` expression are source names. -/
theorem srcClean_vars_not_tmp :
    ∀ (e : SExpr), srcClean e → ∀ s, s ∈ sexprVars e → ¬ isTmpName s := by
  intro e
  induction e with
  | SVar x => intro hc s hs; simp [sexprVars] at hs; subst hs; exact hc
  | SLit n => intro _ s hs; simp [sexprVars] at hs
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro hc s hs
      simp only [sexprVars, List.mem_append] at hs
      rcases hs with hs | hs
      · exact iha hc.1 s hs
      · exact ihb hc.2 s hs
  | SLt a b _ _ => intro hc; simp only [srcClean] at hc
  | SAsr a b _ _ => intro hc; simp only [srcClean] at hc
  | SMulS a b _ _ => intro hc; simp only [srcClean] at hc
  | SMulHiS a b _ _ => intro hc; simp only [srcClean] at hc
  | SLimb v i => intro hc; simp only [srcClean] at hc

/-- `SExpr.evalBV` depends on its reader only at the variables it reads. -/
theorem evalBV_congr_vars (β₁ β₂ : String → BitVec 64) :
    ∀ (e : SExpr), (∀ s, s ∈ sexprVars e → β₁ s = β₂ s) →
      SExpr.evalBV β₁ e = SExpr.evalBV β₂ e := by
  intro e
  induction e with
  | SVar x => intro hβ; exact hβ x (by simp [sexprVars])
  | SLit n => intro _; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb
  | SMulHiS a b iha ihb =>
      intro hβ
      have ha : SExpr.evalBV β₁ a = SExpr.evalBV β₂ a :=
        iha (fun s hs => hβ s (by simp only [sexprVars, List.mem_append]; exact Or.inl hs))
      have hb : SExpr.evalBV β₁ b = SExpr.evalBV β₂ b :=
        ihb (fun s hs => hβ s (by simp only [sexprVars, List.mem_append]; exact Or.inr hs))
      simp only [SExpr.evalBV, ha, hb]
  | SLimb v i => intro _; rfl

/-! ## 4. The `ltuCmds` window at the source level -/

/-- The three-command `ltuCmds` window that `CarryChainSelect.matchLtu`
    recognises, over an explicit destination `dst` and the two scratch slots
    `q`, `r`. -/
def ltuWindow (dst q r : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr q (.SAnd (.SXor x (.SLit onesLit)) y),
    .RScalarSetExpr r (.SAnd (.SXor (.SXor x y) (.SLit onesLit)) (.SSub x y)),
    .RScalarSetExpr dst
      (.SShr (.SXor (.SXor (.SVar q) (.SVar r)) (.SAnd (.SVar q) (.SVar r)))
        (.SLit 63)) ]

/-- **The `ltuCmds` window's source value.** Under the freshness the matcher
    checks — the two scratch slots distinct from each other, from the
    destination, and from the operand variables — the window leaves `ltuIdiom`
    of the operand values in `dst` and every other non-temporary slot
    untouched. -/
theorem ltuWindow_sem {dst q r : String} {x y : SExpr} {env env' : SEnvScalar}
    (hqt : ¬ isTmpName q) (hrt : ¬ isTmpName r)
    (hxc : srcClean x) (hyc : srcClean y)
    (hqr : q ≠ r) (hdq : dst ≠ q) (hdr : dst ≠ r)
    (hqx : q ∉ sexprVars x) (hqy : q ∉ sexprVars y)
    (hrx : r ∉ sexprVars x) (hry : r ∉ sexprVars y)
    (h : semList (ltuWindow dst q r x y) env = some env') :
    env' dst = some ⟨.sword 64,
        ltuIdiom (SExpr.evalBV (envReader env) x) (SExpr.evalBV (envReader env) y)⟩ ∧
      ∀ s, ¬ isTmpName s → s ≠ dst → s ≠ q → s ≠ r → env' s = env s := by
  simp only [ltuWindow] at h
  obtain ⟨env₁, h1, h⟩ := semList_cons_eq h
  obtain ⟨env₂, h2, h⟩ := semList_cons_eq h
  obtain ⟨env₃, h3, h⟩ := semList_cons_eq h
  rw [semList_nil] at h
  have hE : env₃ = env' := Option.some.inj h
  subst hE
  obtain ⟨h1at, h1off⟩ := semScalar_setExpr_eq h1
  obtain ⟨h2at, h2off⟩ := semScalar_setExpr_eq h2
  obtain ⟨h3at, h3off⟩ := semScalar_setExpr_eq h3
  -- readers agree with the entry reader on the operand variables
  have hread1 : ∀ s, s ∈ sexprVars x ∨ s ∈ sexprVars y → envReader env₁ s = envReader env s := by
    intro s hs
    rcases hs with hs | hs
    · exact envReader_setExpr_off h1 s (srcClean_vars_not_tmp x hxc s hs)
        (fun he => hqx (he ▸ hs))
    · exact envReader_setExpr_off h1 s (srcClean_vars_not_tmp y hyc s hs)
        (fun he => hqy (he ▸ hs))
  have hxv1 : SExpr.evalBV (envReader env₁) x = SExpr.evalBV (envReader env) x :=
    evalBV_congr_vars _ _ x (fun s hs => hread1 s (Or.inl hs))
  have hyv1 : SExpr.evalBV (envReader env₁) y = SExpr.evalBV (envReader env) y :=
    evalBV_congr_vars _ _ y (fun s hs => hread1 s (Or.inr hs))
  -- the two scratch values
  have hqval : envReader env₂ q =
      (SExpr.evalBV (envReader env) x ^^^ BitVec.ofNat 64 onesLit) &&&
        SExpr.evalBV (envReader env) y := by
    rw [envReader_setExpr_off h2 q hqt hqr, envReader_setExpr_at h1]
    simp only [SExpr.evalBV]
  have hrval : envReader env₂ r =
      ((SExpr.evalBV (envReader env) x ^^^ SExpr.evalBV (envReader env) y) ^^^
          BitVec.ofNat 64 onesLit) &&&
        (SExpr.evalBV (envReader env) x - SExpr.evalBV (envReader env) y) := by
    rw [envReader_setExpr_at h2]
    simp only [SExpr.evalBV, hxv1, hyv1]
  have hval : SExpr.evalBV (envReader env₂)
      (SExpr.SShr (.SXor (.SXor (.SVar q) (.SVar r)) (.SAnd (.SVar q) (.SVar r)))
        (.SLit 63))
      = ltuIdiom (SExpr.evalBV (envReader env) x) (SExpr.evalBV (envReader env) y) := by
    simp only [SExpr.evalBV, hqval, hrval, ltuIdiom]
    norm_num
  refine ⟨by rw [h3at, hval], ?_⟩
  intro s hs hsd hsq hsr
  rw [h3off s hs hsd, h2off s hs hsr, h1off s hs hsq]

/-! ## 5. The chain-start and chain-final windows -/

/-- The `addStart` window `matchAddStart` recognises: the plain sum, then the
    `ltuCmds` carry test on the sum and the first operand. -/
def addStartWindow (s c q r : String) (x y : SExpr) : List LowCT :=
  .RScalarSetExpr s (.SAdd x y) :: ltuWindow c q r (.SVar s) x

/-- **The `addStart` window's source values.** The data slot holds
    `addCarryWordC x y 0` and the carry slot the widened `carryOutBitC x y 0` —
    exactly what the selected `bvAddCarryLo`/`bvAddCarryHi` pair binds. -/
theorem addStartWindow_sem {s c q r : String} {x y : SExpr} {env env' : SEnvScalar}
    (hst : ¬ isTmpName s) (hqt : ¬ isTmpName q) (hrt : ¬ isTmpName r)
    (hxc : srcClean x)
    (hqs : q ≠ s) (hrs : r ≠ s) (hqr : q ≠ r)
    (hcs : c ≠ s) (hcq : c ≠ q) (hcr : c ≠ r)
    (hsx : s ∉ sexprVars x) (hqx : q ∉ sexprVars x) (hrx : r ∉ sexprVars x)
    (h : semList (addStartWindow s c q r x y) env = some env') :
    env' s = some ⟨.sword 64,
        addCarryWordC (SExpr.evalBV (envReader env) x)
          (SExpr.evalBV (envReader env) y) 0#1⟩ ∧
      env' c = some ⟨.sword 64,
        BitVec.setWidth 64 (carryOutBitC (SExpr.evalBV (envReader env) x)
          (SExpr.evalBV (envReader env) y) 0#1)⟩ ∧
      ∀ n, ¬ isTmpName n → n ≠ s → n ≠ c → n ≠ q → n ≠ r → env' n = env n := by
  simp only [addStartWindow] at h
  obtain ⟨env₀, h0, hrest⟩ := semList_cons_eq h
  obtain ⟨h0at, h0off⟩ := semScalar_setExpr_eq h0
  have hxv : SExpr.evalBV (envReader env₀) x = SExpr.evalBV (envReader env) x :=
    evalBV_congr_vars _ _ x (fun n hn =>
      envReader_setExpr_off h0 n (srcClean_vars_not_tmp x hxc n hn) (fun he => hsx (he ▸ hn)))
  have hsval : envReader env₀ s
      = SExpr.evalBV (envReader env) x + SExpr.evalBV (envReader env) y := by
    rw [envReader_setExpr_at h0]; simp only [SExpr.evalBV]
  obtain ⟨hcat, hoff⟩ :=
    ltuWindow_sem (dst := c) (q := q) (r := r) (x := .SVar s) (y := x)
      hqt hrt hst hxc hqr hcq hcr
      (by simpa [sexprVars] using hqs) hqx (by simpa [sexprVars] using hrs) hrx hrest
  refine ⟨?_, ?_, ?_⟩
  · rw [hoff s hst (Ne.symm hcs) (Ne.symm hqs) (Ne.symm hrs), h0at]
    simp only [SExpr.evalBV, select_addStart_data]
  · rw [hcat]
    simp only [SExpr.evalBV, hsval, hxv, ← select_addStart_carry]
  · intro n hn hns hnc hnq hnr
    rw [hoff n hn hnc hnq hnr, h0off n hn hns]

/-- The `addFin` window `matchAddFin` recognises: the plain sum, then the
    carry-in add whose carry-out the architecture drops. -/
def addFinWindow (t s cp : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr t (.SAdd x y),
    .RScalarSetExpr s (.SAdd (.SVar t) (.SVar cp)) ]

/-- **The `addFin` window's source value.** With the chain invariant — the
    carry-in slot `cp` holds the widened bit `cin` — the data slot holds
    `addCarryWordC x y cin`. -/
theorem addFinWindow_sem {t s cp : String} {x y : SExpr} {env env' : SEnvScalar}
    {cin : BitVec 1}
    (hcpt : ¬ isTmpName cp) (htcp : t ≠ cp)
    (hcarry : envReader env cp = BitVec.setWidth 64 cin)
    (h : semList (addFinWindow t s cp x y) env = some env') :
    env' s = some ⟨.sword 64,
      addCarryWordC (SExpr.evalBV (envReader env) x)
        (SExpr.evalBV (envReader env) y) cin⟩ := by
  rw [addFinWindow] at h
  obtain ⟨env₀, h0, h⟩ := semList_cons_eq h
  obtain ⟨env₁, h1, h⟩ := semList_cons_eq h
  rw [semList_nil] at h
  have hE : env₁ = env' := Option.some.inj h
  subst hE
  obtain ⟨h0at, h0off⟩ := semScalar_setExpr_eq h0
  obtain ⟨h1at, _⟩ := semScalar_setExpr_eq h1
  have htval : envReader env₀ t
      = SExpr.evalBV (envReader env) x + SExpr.evalBV (envReader env) y := by
    rw [envReader_setExpr_at h0]; simp only [SExpr.evalBV]
  have hcpval : envReader env₀ cp = BitVec.setWidth 64 cin := by
    rw [envReader_setExpr_off h0 cp hcpt (Ne.symm htcp), hcarry]
  rw [h1at]
  simp only [SExpr.evalBV, htval, hcpval, select_addMid_data]

/-- The `subStart` window `matchSubStart` recognises: the plain difference,
    then the `ltuCmds` borrow test on the two operands. -/
def subStartWindow (e w q r : String) (x y : SExpr) : List LowCT :=
  .RScalarSetExpr e (.SSub x y) :: ltuWindow w q r x y

/-- **The `subStart` window's source values.** In the complement-add
    convention the data slot holds `addCarryWordC x (~y) 1` and the borrow slot
    the complement of the widened `carryOutBitC x (~y) 1`. -/
theorem subStartWindow_sem {e w q r : String} {x y : SExpr} {env env' : SEnvScalar}
    (het : ¬ isTmpName e) (hqt : ¬ isTmpName q) (hrt : ¬ isTmpName r)
    (hxc : srcClean x) (hyc : srcClean y)
    (hqr : q ≠ r) (hwq : w ≠ q) (hwr : w ≠ r)
    (hqe : q ≠ e) (hre : r ≠ e) (hwe : w ≠ e)
    (hex : e ∉ sexprVars x) (hey : e ∉ sexprVars y)
    (hqx : q ∉ sexprVars x) (hqy : q ∉ sexprVars y)
    (hrx : r ∉ sexprVars x) (hry : r ∉ sexprVars y)
    (h : semList (subStartWindow e w q r x y) env = some env') :
    env' e = some ⟨.sword 64,
        addCarryWordC (SExpr.evalBV (envReader env) x)
          (SExpr.evalBV (envReader env) y ^^^ BitVec.ofNat 64 onesLit) 1#1⟩ ∧
      env' w = some ⟨.sword 64,
        BitVec.setWidth 64 (carryOutBitC (SExpr.evalBV (envReader env) x)
          (SExpr.evalBV (envReader env) y ^^^ BitVec.ofNat 64 onesLit) 1#1) ^^^ 1#64⟩ ∧
      ∀ n, ¬ isTmpName n → n ≠ e → n ≠ w → n ≠ q → n ≠ r → env' n = env n := by
  simp only [subStartWindow] at h
  obtain ⟨env₀, h0, hrest⟩ := semList_cons_eq h
  obtain ⟨h0at, h0off⟩ := semScalar_setExpr_eq h0
  have hxv : SExpr.evalBV (envReader env₀) x = SExpr.evalBV (envReader env) x :=
    evalBV_congr_vars _ _ x (fun n hn =>
      envReader_setExpr_off h0 n (srcClean_vars_not_tmp x hxc n hn) (fun he => hex (he ▸ hn)))
  have hyv : SExpr.evalBV (envReader env₀) y = SExpr.evalBV (envReader env) y :=
    evalBV_congr_vars _ _ y (fun n hn =>
      envReader_setExpr_off h0 n (srcClean_vars_not_tmp y hyc n hn) (fun he => hey (he ▸ hn)))
  obtain ⟨hwat, hoff⟩ :=
    ltuWindow_sem (dst := w) (q := q) (r := r) (x := x) (y := y)
      hqt hrt hxc hyc hqr hwq hwr hqx hqy hrx hry hrest
  refine ⟨?_, ?_, ?_⟩
  · rw [hoff e het (Ne.symm hwe) (Ne.symm hqe) (Ne.symm hre), h0at]
    simp only [SExpr.evalBV, select_subStart_data]
  · rw [hwat]
    simp only [hxv, hyv, ← select_subStart_borrow]
  · intro n hn hne hnw hnq hnr
    rw [hoff n hn hnw hnq hnr, h0off n hn hne]

/-! ## 6. Slots the selection leaves unbound

The two fronts bind different name sets on the same body.  The window's two
scratch slots have no counterpart in the fused emission, and the carry word is
materialised only when `CarryChainSelect.needFun` finds a later step reading it
as a word — which the cap `frontLoopBodyCDC` applies afterwards cannot
request. -/

/-- A one-limb add-with-carry body: the `addStart` window and nothing else, so
    no later command reads the carry-out `c0` as a word. -/
def carryOnlyBody : LowCT :=
  .RSeq (.RScalarSetExpr "s0" (.SAdd (.SVar "a0") (.SVar "b0")))
    (.RSeq (.RScalarSetExpr "c0q"
        (.SAnd (.SXor (.SVar "s0") (.SLit onesLit)) (.SVar "a0")))
      (.RSeq (.RScalarSetExpr "c0r"
          (.SAnd (.SXor (.SXor (.SVar "s0") (.SVar "a0")) (.SLit onesLit))
            (.SSub (.SVar "s0") (.SVar "a0"))))
        (.RScalarSetExpr "c0"
          (.SShr (.SXor (.SXor (.SVar "c0q") (.SVar "c0r"))
              (.SAnd (.SVar "c0q") (.SVar "c0r")))
            (.SLit 63)))))

/-- The two-word entry context of `carryOnlyBody`. -/
def probeCtx : Ctx := [.sword 64, .sword 64]

/-- `a0` and `b0` at the two entry slots. -/
def probeVarMap : VarMap probeCtx :=
  (VarMap.empty.bind (t := .sword 64) "a0").bind (t := .sword 64) "b0"

/-- Whether a front's output `VarMap` binds `nm`. -/
def frontBinds (front : VarMap probeCtx → LowCT → Option (DTransOut probeCtx))
    (c : LowCT) (nm : String) : Bool :=
  match front probeVarMap c with
  | some r => (r.vm.lookup nm).isSome
  | none => false

/-- The accumulator cap that `TranslateDialectRolledLoop.frontLoopBodyCD` and
    `frontLoopBodyCDC` apply to a front's output: the accumulator name must be
    bound at the accumulator type. -/
def frontCaps (front : VarMap probeCtx → LowCT → Option (DTransOut probeCtx))
    (c : LowCT) (nm : String) : Bool :=
  match front probeVarMap c with
  | some r =>
      match r.vm.lookup nm with
      | some ⟨t, _⟩ => t == .sword 64
      | none => false
  | none => false

-- The plain front binds the window's data slot, both scratch slots and the
-- carry word.
#guard (frontBinds (fun vm c => translateDialectControl vm c) carryOnlyBody "s0",
    frontBinds (fun vm c => translateDialectControl vm c) carryOnlyBody "c0q",
    frontBinds (fun vm c => translateDialectControl vm c) carryOnlyBody "c0r",
    frontBinds (fun vm c => translateDialectControl vm c) carryOnlyBody "c0")
    == (true, true, true, true)

-- The selecting front binds the window's data slot and neither scratch slot.
#guard (frontBinds (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "s0",
    frontBinds (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "c0q",
    frontBinds (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "c0r")
    == (true, false, false)

-- With no later word read of the carry, the selecting front binds the carry bit
-- `c0#b` and not the carry word `c0`.
#guard (frontBinds (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "c0",
    frontBinds (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "c0#b")
    == (false, true)

-- The accumulator cap accepts `c0` on the plain front's output and rejects it on
-- the selecting front's: a loop body whose accumulator is the chain's carry-out
-- passes `frontLoopBodyCD` and not `frontLoopBodyCDC`.
#guard (frontCaps (fun vm c => translateDialectControl vm c) carryOnlyBody "c0",
    frontCaps (fun vm c => translateDialectCarrySelect vm c) carryOnlyBody "c0")
    == (true, false)

end CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
