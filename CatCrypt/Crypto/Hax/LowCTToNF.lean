/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# The lowering of `LowCT` to `NFProg nfDialect`

`lowCTToNF ps res c` translates a `LowCT` command `c` over the scalar heap to a one-result
program of `NFProg nfDialect` over the context `entryCtx ps` of the parameters `ps`; the
result is the value of the scalar name `res` at the end of `c`. The translation passes the
state: an environment of names `NfEnv` holds, for each scalar name, the variable of type
`word 64` with its current value, and an assignment binds a new variable.

The fragment is the scalar straight-line commands `RSkip`, `RAssert`, `RBlock`, `RSeq`,
`RLetU64Zero`, `RScalarSet`, `RScalarSetExpr`, and the counted loop `RFor` on a body in the
fragment. A counted loop is a `forLoop` carrying the names of the environment that its body
assigns (`assigned`); the body reads the counter in the trip index. Every other command is
`none`.

The scalar expressions translated are `SVar`, `SLit`, `SAdd`, `SSub`, `SMul`, `SShr`, `SShl`,
`SAnd`, `SXor`, `SMulS` and `SMulHiU`, each as the wrapping operation of `NfBinOp` at width
`64`; every other expression is `none`.

`RustExec` evaluates scalar expressions over unbounded naturals with a saturating
subtraction, and `nfDialect` over words of 64 bits with shifts that fail at an amount of at
least `64`. The simulation therefore assumes `RunInRange`: every expression a run evaluates
satisfies `SExpr.inRangeState` at the state it is evaluated in.

## Main definitions

* `stEnv` — the scalar heap of a `RustState` as a source environment of integer values.
* `StateVals` — the scalar heap holds, at each parameter, the value of its variable.
* `wordVar` — the variable of type `word 64` of a name.
* `seToNF` — the translation of scalar expressions.
* `assigned` — the scalar names a command may write.
* `RunInRange` — the in-range condition of a run.
* `cmdToNF` — the translation of commands, as a prefix and the environment at its hole.
* `lowCTToNF` — the translation of a command to a one-result program.

## Main results

* `seToNF_sound` — a translated expression denotes the word of its value.
* `rsScalar_of_not_assigned` — a run leaves the scalars outside `assigned` unchanged.
* `cmdToNF_sim` — a run of a command is matched by the denotation of its prefix.
* `lowCTToNF_sim` — a run of a command is matched by the denotation of its program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.LowCTToNF

open _root_.Hax (Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr RustState RustExec LeafSpec rsSetScalar
  rsSetTower callNUpdate_rsScalar sexprMulHiU sexprOfSignedInt64 sexprToSignedInt64)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. States and environments of names -/

/-- The scalar heap of `rs` as a source environment: every name reads the integer value of
    its scalar slot. -/
def stEnv (rs : RustState) : Env := fun x => some (.int (rs.rsScalar x))

/-- Writing a scalar slot extends the source environment at its name. -/
theorem stEnv_rsSetScalar (rs : RustState) (x : String) (n : Nat) :
    stEnv (rsSetScalar rs x n) = (stEnv rs).extend x (.int n) := by
  funext y
  by_cases h : y = x <;> simp [stEnv, rsSetScalar, Env.extend, h]

/-- The scalar heap of `rs` holds, at the name of each parameter of `ps`, the value of its
    variable in `V`: `EntryVals` at the source environment `stEnv rs`. -/
def StateVals (rs : RustState) (ps : List (String × NfTy)) (V : Valuation (entryCtx ps)) :
    Prop :=
  EntryVals (stEnv rs) ps V

/-- The current variable of the name `x` when its type is `word 64`. -/
def wordVar {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String) : Option (Var Γ (NfTy.word 64)) :=
  (σ.lookup x).bind fun p => if h : p.1 = NfTy.word 64 then some (h ▸ p.2) else none

/-- A variable `wordVar` returns is the current variable of its name. -/
theorem wordVar_lookup {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {x : String}
    {v : Var Γ (NfTy.word 64)} (h : wordVar σ x = some v) :
    σ.lookup x = some ⟨NfTy.word 64, v⟩ := by
  simp only [wordVar, Option.bind_eq_some_iff] at h
  obtain ⟨⟨t, u⟩, hl, h⟩ := h
  dsimp only at h
  split at h
  · rename_i ht
    subst ht
    cases h
    exact hl
  · cases h

/-- In a related state, the scalar slot of a name holds the value of its word variable. -/
theorem rsScalar_of_wordVar {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {rs : RustState}
    {V : Valuation Γ} (hrel : EnvRel σ (stEnv rs) V) {x : String} {v : Var Γ (NfTy.word 64)}
    (h : wordVar σ x = some v) : rs.rsScalar x = (v.lookup V).toNat := by
  have h1 := hrel x _ v (wordVar_lookup h)
  simpa [stEnv, enc] using h1

/-- A related state after a write of the scalar `x` is related to the environment of names
    with `x` bound to a word variable holding the written value. -/
theorem envRel_setWord {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {rs : RustState} {V : Valuation Γ}
    (hrel : EnvRel σ (stEnv rs) V) (x : String) (r : Var Γ (NfTy.word 64)) {n : Nat}
    (hn : (r.lookup V).toNat = n) :
    EnvRel ((x, ⟨NfTy.word 64, r⟩) :: σ) (stEnv (rsSetScalar rs x n)) V := by
  rw [stEnv_rsSetScalar, ← hn]
  exact hrel.cons x (NfTy.word 64) r

/-! ## 2. Scalar expressions -/

/-- The output of the translation of a scalar expression over `Γ`: a prefix to the context
    `Δ` and the variable of the value. -/
structure ExprOut (Γ : Ctxt nfDialect) where
  /-- The context at the hole. -/
  Δ : Ctxt nfDialect
  /-- The prefix. -/
  pre : NFPre nfDialect Γ Δ
  /-- The variable of the value. -/
  res : Var Δ (NfTy.word 64)

/-- The binary operation `o` at width `64` on the outputs of two operands: the second
    operand is translated from the environment of names at the hole of the first. -/
def binOut (o : NfBinOp) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (ra : Option (ExprOut Γ))
    (fb : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (ExprOut Δ)) : Option (ExprOut Γ) :=
  ra.bind fun oa => (fb (σ.mapV oa.pre.wk)).map fun ob =>
    ⟨NfTy.word 64 :: ob.Δ,
      oa.pre.append (ob.pre.append
        (.var (mkE (.bin o 64) (.cons (ob.pre.wk oa.res) (.cons ob.res .nil))) .nil)),
      .here⟩

/-- **The translation of scalar expressions**: a scalar variable is its word variable, a
    literal a word constant, and an arithmetic, shift or bitwise node the wrapping operation
    of `NfBinOp` at width `64` on its operands. `SLt`, `SAsr`, `SMulHiS` and `SLimb` are
    `none`. -/
def seToNF : SExpr → {Γ : Ctxt nfDialect} → NfEnv Γ → Option (ExprOut Γ)
  | .SVar x, Γ, σ => (wordVar σ x).map fun v => ⟨Γ, .nil, v⟩
  | .SLit n, Γ, _ =>
      some ⟨NfTy.word 64 :: Γ, .var (mkE (.const 64 (BitVec.ofNat 64 n)) .nil) .nil, .here⟩
  | .SAdd a b, _, σ => binOut .add σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SSub a b, _, σ => binOut .sub σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SMul a b, _, σ => binOut .mul σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SShr a b, _, σ => binOut .lshr σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SShl a b, _, σ => binOut .shl σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SAnd a b, _, σ => binOut .and σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SXor a b, _, σ => binOut .xor σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SMulS a b, _, σ => binOut .mul σ (seToNF a σ) (fun σ' => seToNF b σ')
  | .SMulHiU a b, _, σ => binOut .mulhi σ (seToNF a σ) (fun σ' => seToNF b σ')
  | _, _, _ => none

/-- A binary operation on two sound operands denotes the value of the operation. -/
theorem binOut_sound (bi : Builtins) (fuel : Nat) {o : NfBinOp} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {ra : Option (ExprOut Γ)}
    {fb : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (ExprOut Δ)} {out : ExprOut Γ}
    (h : binOut o σ ra fb = some out) {rs : RustState} {V : Valuation Γ}
    (hrel : EnvRel σ (stEnv rs) V) {x y z : BitVec 64}
    (ha : ∀ oa, ra = some oa → ∃ W, PDen bi fuel oa.pre V = some W ∧ oa.res.lookup W = x)
    (hb : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) (W : Valuation Δ) (ob : ExprOut Δ),
      EnvRel σ' (stEnv rs) W → fb σ' = some ob →
      ∃ W', PDen bi fuel ob.pre W = some W' ∧ ob.res.lookup W' = y)
    (hop : o.denote 64 x y = some z) :
    ∃ W, PDen bi fuel out.pre V = some W ∧ out.res.lookup W = z := by
  simp only [binOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
  obtain ⟨Wa, hWa, hxa⟩ := ha oa hoa
  have hrelA : EnvRel (σ.mapV oa.pre.wk) (stEnv rs) Wa :=
    hrel.mapV _ fun t u =>
      @NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fuel _ _ _ oa.pre u _ _ hWa
  obtain ⟨Wb, hWb, hyb⟩ := hb _ Wa ob hrelA hob
  have hwk : (ob.pre.wk oa.res).lookup Wb = x :=
    (@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fuel _ _ _ ob.pre oa.res
      _ _ hWb).trans hxa
  have hlast : PDen bi fuel (NFPre.var (mkE (.bin o 64)
      (.cons (ob.pre.wk oa.res) (.cons ob.res .nil))) .nil) Wb =
      some (Wb.extend (t := NfTy.word 64) z) := by
    refine (PDen_bind1 bi fuel ([] : NfEnv ob.Δ) (.bin o 64)
      (.cons (ob.pre.wk oa.res) (.cons ob.res .nil)) Wb).trans ?_
    show (o.denote 64 ((ob.pre.wk oa.res).lookup Wb) (ob.res.lookup Wb)).map _ = _
    rw [hwk, hyb, hop]
    rfl
  exact ⟨_, PDen_append_some bi fuel hWa (PDen_append_some bi fuel hWb hlast), rfl⟩

/-- **The translation of scalar expressions is sound.** In a state related to the valuation
    `V` in which `e` is in range, the prefix of `e` denotes a valuation in which its variable
    holds the word `e.evalStateBV rs`, the truncation of the value `e.evalState rs` that
    `RustExec` computes. -/
theorem seToNF_sound (bi : Builtins) (fuel : Nat) (e : SExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : ExprOut Γ), seToNF e σ = some o →
      ∀ (rs : RustState) (V : Valuation Γ), EnvRel σ (stEnv rs) V → e.inRangeState rs →
        ∃ W, PDen bi fuel o.pre V = some W ∧ o.res.lookup W = e.evalStateBV rs := by
  induction e with
  | SVar x =>
      intro Γ σ o h rs V hrel _
      simp only [seToNF, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      refine ⟨V, rfl, ?_⟩
      show v.lookup V = BitVec.ofNat 64 (rs.rsScalar x)
      rw [rsScalar_of_wordVar hrel hv]
      simp
  | SLit n =>
      intro Γ σ o h rs V _ _
      simp only [seToNF, Option.some.injEq] at h
      subst h
      exact ⟨_, PDen_bind1 bi fuel ([] : NfEnv Γ) (.const 64 (BitVec.ofNat 64 n)) .nil V, rfl⟩
  | SAdd a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2.1) rfl
  | SSub a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2.1) rfl
  | SMul a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2.1) rfl
  | SShr a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      have hlt : (b.evalStateBV rs).toNat < 64 := by
        rw [SExpr.toNat_evalStateBV_of_inRangeState rs b hr.2.1]
        exact hr.2.2
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2.1)
        (by simp [NfBinOp.denote, SExpr.evalStateBV, hlt])
  | SShl a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      have hlt : (b.evalStateBV rs).toNat < 64 := by
        rw [SExpr.toNat_evalStateBV_of_inRangeState rs b hr.2.1]
        exact hr.2.2.1
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2.1)
        (by simp [NfBinOp.denote, SExpr.evalStateBV, hlt])
  | SAnd a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2) rfl
  | SXor a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2) rfl
  | SMulS a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2)
        (by
          simp only [NfBinOp.denote, SExpr.evalStateBV, sexprOfSignedInt64, sexprToSignedInt64,
            BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofInt_mul, BitVec.ofInt_toInt])
  | SMulHiU a b iha ihb =>
      intro Γ σ o h rs V hrel hr
      simp only [seToNF] at h
      exact binOut_sound bi fuel h hrel (fun oa hoa => iha σ oa hoa rs V hrel hr.1)
        (fun σ' W ob hrel' hob => ihb σ' ob hob rs W hrel' hr.2)
        (by simp [NfBinOp.denote, SExpr.evalStateBV, sexprMulHiU, Nat.shiftRight_eq_div_pow,
          Nat.mod_eq_of_lt (BitVec.isLt _)])
  | _ =>
      intro Γ σ o h
      simp [seToNF] at h

/-! ## 3. Assigned names and the in-range condition -/

/-- The scalar names a command may write: the names of its scalar assignments and scalar
    bindings and the counters of its loops. -/
def assigned : LowCT → List String
  | .RSeq a b => assigned a ++ assigned b
  | .RLetZero _ _ b => assigned b
  | .RLetU64Zero x b => x :: assigned b
  | .RScalarSet x _ => [x]
  | .RScalarSetExpr x _ => [x]
  | .RIfNz _ a b => assigned a ++ assigned b
  | .RWhileNz _ b => assigned b
  | .RFor x _ b => x :: assigned b
  | .RForRuntime x _ b => x :: assigned b
  | .RBlock b => assigned b
  | _ => []

/-- **The frame of the scalar heap.** A run leaves every scalar slot outside `assigned`
    unchanged. -/
theorem rsScalar_of_not_assigned {N : Nat} {L : LeafSpec} {c : LowCT} {rs rs' : RustState}
    (h : RustExec N L c rs rs') :
    ∀ y, y ∉ assigned c → rs'.rsScalar y = rs.rsScalar y := by
  induction h with
  | seq _ _ _ _ _ _ _ ih1 ih2 =>
      intro y hy
      simp only [assigned, List.mem_append, not_or] at hy
      rw [ih2 y hy.2, ih1 y hy.1]
  | letZero _ _ _ _ _ _ ih =>
      intro y hy
      rw [ih y (by simpa only [assigned] using hy)]
      rfl
  | letU64Zero x _ _ _ _ ih =>
      intro y hy
      simp only [assigned, List.mem_cons, not_or] at hy
      rw [ih y hy.2]
      simp [rsSetScalar, hy.1]
  | scalarSet x _ _ =>
      intro y hy
      simp only [assigned, List.mem_singleton] at hy
      simp [rsSetScalar, hy]
  | scalarSetExpr x _ _ =>
      intro y hy
      simp only [assigned, List.mem_singleton] at hy
      simp [rsSetScalar, hy]
  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
      intro y hy
      simp only [assigned, List.mem_append, not_or] at hy
      exact ih y hy.1
  | ifFalse _ _ _ _ _ _ _ ih =>
      intro y hy
      simp only [assigned, List.mem_append, not_or] at hy
      exact ih y hy.2
  | whileTrue _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      intro y hy
      rw [ih2 y hy, ih1 y (by simpa only [assigned] using hy)]
  | forSucc x _ _ _ _ _ _ _ ih1 ih2 =>
      intro y hy
      simp only [assigned, List.mem_cons, not_or] at hy
      rw [ih2 y hy.2, ← ih1 y (by simp only [assigned, List.mem_cons, not_or]; exact hy)]
      simp [rsSetScalar, hy.1]
  | forRuntime _ _ _ _ _ _ ih =>
      intro y hy
      exact ih y (by simpa only [assigned] using hy)
  | cloneCall _ _ _ _ _ _ _ _ _ hc _ ih =>
      intro y _
      rw [ih y (by simp [assigned]), hc]
      rfl
  | callSwap _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      intro y _
      rw [ih2 y (by simp [assigned]), ih1 y (by simp [assigned])]
  | callN _ _ _ _ _ hargs _ _ =>
      intro y _
      rw [callNUpdate_rsScalar]
  | block _ _ _ _ ih =>
      intro y hy
      exact ih y (by simpa only [assigned] using hy)
  | _ =>
      intro y _
      rfl

/-- **The in-range condition of a run** of `c` from `rs`: every scalar expression the run
    assigns satisfies `SExpr.inRangeState` at the state it is evaluated in. On a sequence
    the second command is in range at every state the first runs to, and on a counted loop
    the body is in range at the state of every trip. -/
def RunInRange (N : Nat) (L : LeafSpec) : LowCT → RustState → Prop
  | .RSeq a b, rs => RunInRange N L a rs ∧ ∀ r1, RustExec N L a rs r1 → RunInRange N L b r1
  | .RLetU64Zero x b, rs => RunInRange N L b (rsSetScalar rs x 0)
  | .RBlock b, rs => RunInRange N L b rs
  | .RScalarSetExpr _ e, rs => e.inRangeState rs
  | .RFor x n b, rs => ∀ i, i < n → ∀ r1, RustExec N L (.RFor x i b) rs r1 →
      RunInRange N L b (rsSetScalar r1 x i)
  | _, _ => True

/-! ## 4. Commands -/

/-- The output of the translation of a command over `Γ`: a prefix to the context `Δ` and the
    environment of names at its hole. -/
structure CmdOut (Γ : Ctxt nfDialect) where
  /-- The context at the hole. -/
  Δ : Ctxt nfDialect
  /-- The prefix. -/
  pre : NFPre nfDialect Γ Δ
  /-- The environment of names at the hole. -/
  σ : NfEnv Δ

/-- The output `o₂` from the hole of `o`, composed after `o`. -/
def CmdOut.comp {Γ : Ctxt nfDialect} (o : CmdOut Γ) (o₂ : CmdOut o.Δ) : CmdOut Γ :=
  ⟨o₂.Δ, o.pre.append o₂.pre, o₂.σ⟩

/-- The carried entries of a loop: the current entry of each name of `σ` other than the
    counter `x` that is among the assigned names `as`. -/
def carriedEntries {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String) (as : List String) :
    List (String × (Σ t : NfTy, Var Γ t)) :=
  ((σ.map (·.1)).eraseDups.filter fun y => y != x && as.contains y).filterMap
    fun y => (σ.lookup y).map fun p => (y, p)

/-- Every carried entry is current. -/
theorem carriedEntries_lookup {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String)
    (as : List String) : ∀ p ∈ carriedEntries σ x as, σ.lookup p.1 = some p.2 := by
  intro p hp
  simp only [carriedEntries, List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨y, -, q, hq, rfl⟩ := hp
  exact hq

/-- A current name other than the counter that is not carried is not assigned. -/
theorem not_mem_of_not_carried {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String)
    (as : List String) {y : String} {q : Σ t : NfTy, Var Γ t} (hq : σ.lookup y = some q)
    (hyx : y ≠ x) (hy : y ∉ (carriedEntries σ x as).map (·.1)) : y ∉ as := by
  intro hmem
  apply hy
  have hσ : y ∈ σ.map (·.1) := by
    simp only [NfEnv.lookup, Option.map_eq_some_iff, List.find?_eq_some_iff_append] at hq
    obtain ⟨p, ⟨hp, as', bs, rfl, -⟩, -⟩ := hq
    simp only [beq_iff_eq] at hp
    simp [hp]
  simp only [carriedEntries, List.map_filterMap, List.mem_filterMap, List.mem_filter,
    List.mem_eraseDups, Option.map_map]
  refine ⟨y, ⟨hσ, ?_⟩, by simp [hq]⟩
  simp [hyx, hmem]

/-- The environment of names of the body of a loop on the counter `x` carrying the entries
    `W` of `σ₀`: the counter bound to the trip index, in front of the carried names bound
    to the carried tuple and the other names of `σ₀`. -/
def forBodyEnv {Γ₀ : Ctxt nfDialect} (σ₀ : NfEnv Γ₀) (x : String)
    (W : List (String × (Σ t : NfTy, Var Γ₀ t))) :
    NfEnv ((entriesVars W).1 ++ NfTy.word 64 :: Γ₀) :=
  (x, ⟨NfTy.word 64, Var.shiftApp (d := nfDialect) (Γ := NfTy.word 64 :: Γ₀)
      (entriesVars W).1 Var.here⟩) ::
    loopEnv σ₀ x (W.map (·.1)) (entriesVars W).1 (headVars (entriesVars W).1)
      fun v => Var.shiftApp (d := nfDialect) (entriesVars W).1 v.there

/-- The environment of names after a loop on the counter `x` carrying the entries `W` of
    `σ₀`: the carried names bound to the final tuple, in front of the names of `σ₀` other
    than the counter. -/
def forPostEnv {Γ₀ : Ctxt nfDialect} (σ₀ : NfEnv Γ₀) (x : String)
    (W : List (String × (Σ t : NfTy, Var Γ₀ t))) : NfEnv ((entriesVars W).1 ++ Γ₀) :=
  loopEnv σ₀ x (W.map (·.1)) (entriesVars W).1 (headVars (entriesVars W).1)
    fun v => Var.shiftApp (d := nfDialect) (entriesVars W).1 v

/-- **The counted loop.** The trip count `n`, below `2 ^ 64`, is bound to a word constant;
    the loop carries the entries of the names among `as`; its body is the translation `rec`
    from `forBodyEnv`, returning the current variables of the carried names. The counter is
    not a name of the environment after the loop. -/
def forOut {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String) (n : Nat) (as : List String)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (CmdOut Δ)) : Option (CmdOut Γ) :=
  if n < 2 ^ 64 then
    (rec (forBodyEnv (σ.mapV (Δ := NfTy.word 64 :: Γ) .there) x
        (carriedEntries (σ.mapV .there) x as))).bind fun ob =>
      (varsAt ob.σ ((carriedEntries (σ.mapV (Δ := NfTy.word 64 :: Γ) .there) x as).map (·.1))
          (entriesVars (carriedEntries (σ.mapV .there) x as)).1).map fun rets =>
        ⟨(entriesVars (carriedEntries (σ.mapV (Δ := NfTy.word 64 :: Γ) .there) x as)).1 ++
            NfTy.word 64 :: Γ,
          .var (mkE (.const 64 (BitVec.ofNat 64 n)) .nil)
            (.forLoop .here (entriesVars (carriedEntries (σ.mapV .there) x as)).2
              (ob.pre.plug (.ret rets)) .nil),
          forPostEnv (σ.mapV .there) x (carriedEntries (σ.mapV .there) x as)⟩
  else none

/-- **The translation of commands**: the prefix of a command of the fragment from the
    environment of names `σ`, and the environment of names at its hole. A scalar binding or
    assignment binds a word variable to its name; a counted loop is `forOut` on the names
    its body assigns. Every command outside the fragment is `none`. -/
def cmdToNF : LowCT → {Γ : Ctxt nfDialect} → NfEnv Γ → Option (CmdOut Γ)
  | .RSkip, Γ, σ => some ⟨Γ, .nil, σ⟩
  | .RAssert _, Γ, σ => some ⟨Γ, .nil, σ⟩
  | .RBlock b, _, σ => cmdToNF b σ
  | .RSeq a b, _, σ => (cmdToNF a σ).bind fun oa => (cmdToNF b oa.σ).map oa.comp
  | .RLetU64Zero x b, _, σ =>
      (cmdToNF b ((x, ⟨NfTy.word 64, .here⟩) :: σ.mapV .there)).map fun ob =>
        ⟨ob.Δ, .var (mkE (.const 64 0) .nil) ob.pre, ob.σ⟩
  | .RScalarSet x n, Γ, σ =>
      if n < 2 ^ 64 then
        some ⟨NfTy.word 64 :: Γ, .var (mkE (.const 64 (BitVec.ofNat 64 n)) .nil) .nil,
          (x, ⟨NfTy.word 64, .here⟩) :: σ.mapV .there⟩
      else none
  | .RScalarSetExpr x e, _, σ => (seToNF e σ).map fun o =>
      ⟨o.Δ, o.pre, (x, ⟨NfTy.word 64, o.res⟩) :: σ.mapV o.pre.wk⟩
  | .RFor x n body, _, σ => forOut σ x n (assigned body) (fun σ' => cmdToNF body σ')
  | _, _, _ => none

/-- **The trips of a counted loop.** Let the body be matched from every state related to
    `forBodyEnv`. Then a run of `m ≤ 2 ^ 64` trips whose body is in range at every trip is
    matched by the fold of the target body over the trip indices `0, …, m - 1`, to a tuple
    the carried names hold, with the other names of `σ₀` unchanged. -/
theorem forLoop_fold (bi : Builtins) (fuel : Nat) {N : Nat} {L : LeafSpec} {x : String}
    {body : LowCT} {Γ₀ : Ctxt nfDialect} {σ₀ : NfEnv Γ₀}
    {W : List (String × (Σ t : NfTy, Var Γ₀ t))}
    (hcur : ∀ p ∈ W, σ₀.lookup p.1 = some p.2)
    (hfr : ∀ y q, σ₀.lookup y = some q → y ≠ x → y ∉ W.map (·.1) → y ∉ assigned body)
    {ob : CmdOut ((entriesVars W).1 ++ NfTy.word 64 :: Γ₀)}
    {rets : HVector (fun t => Var ob.Δ t) (entriesVars W).1}
    (hrets : varsAt ob.σ (W.map (·.1)) (entriesVars W).1 = some rets)
    (hbody : ∀ (r r' : RustState)
      (U : Valuation (d := nfDialect) ((entriesVars W).1 ++ NfTy.word 64 :: Γ₀)),
      RustExec N L body r r' → EnvRel (forBodyEnv σ₀ x W) (stEnv r) U → RunInRange N L body r →
      ∃ U', PDen bi fuel ob.pre U = some U' ∧ EnvRel ob.σ (stEnv r') U')
    {rs : RustState} {V₀ : Valuation Γ₀} (hrel : EnvRel σ₀ (stEnv rs) V₀) :
    ∀ (m : Nat), m ≤ 2 ^ 64 → ∀ r, RustExec N L (.RFor x m body) rs r →
      (∀ i, i < m → ∀ r1, RustExec N L (.RFor x i body) rs r1 →
        RunInRange N L body (rsSetScalar r1 x i)) →
      ∃ acc, (List.range m).foldlM (fun a j => PDenP bi fuel (ob.pre.plug (.ret rets))
          (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V₀)))
          (Expr.lookupArgs (entriesVars W).2 V₀) = some acc ∧
        CarriedRel (stEnv r) (W.map (·.1)) (entriesVars W).1 acc ∧
        FrameRel σ₀ x (W.map (·.1)) (stEnv r) V₀ := by
  intro m
  induction m with
  | zero =>
      intro _ r hex _
      cases hex
      exact ⟨_, rfl, CarriedRel.of_entries hrel W hcur, fun y _ _ t v h => hrel y t v h⟩
  | succ k ih =>
      intro hk r hex hr
      cases hex with
      | forSucc _ _ _ _ r1 _ hin hb =>
        obtain ⟨acc, hfold, hc, hf⟩ := ih (by omega) r1 hin fun i hi => hr i (by omega)
        have hlen : (W.map (·.1)).length = (entriesVars W).1.length := by
          rw [List.length_map, entriesVars_length]
        have hentry : EnvRel (forBodyEnv σ₀ x W) (stEnv (rsSetScalar r1 x k))
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₀)) := by
          refine envRel_setWord (EnvRel.loopEnv σ₀ x _ _ hlen _ _ ?_ hf ?_) x _ ?_
          · rw [lookupArgs_headVars]
            exact hc
          · intro t v
            exact Var.lookup_shiftApp _ acc v.there _
          · rw [Var.lookup_shiftApp]
            show (BitVec.ofNat 64 k).toNat = k
            rw [BitVec.toNat_ofNat]
            omega
        obtain ⟨U', hU', hrel'⟩ := hbody _ r _ hb hentry (hr k (Nat.lt_succ_self k) r1 hin)
        refine ⟨Expr.lookupArgs rets U', ?_, CarriedRel.of_varsAt hrel' _ _ hrets, ?_⟩
        · rw [List.range_succ, List.foldlM_append, hfold]
          simp [PDenP_plug_ret bi fuel ob.pre rets _ hU']
        · intro y hy hyx t v hl
          have hna := hfr y _ hl hyx hy
          have hsc : r.rsScalar y = r1.rsScalar y := by
            rw [rsScalar_of_not_assigned hb y hna]
            simp [rsSetScalar, hyx]
          rw [← hf y hy hyx t v hl]
          simp [stEnv, hsc]

/-- **The counted loop is sound.** -/
theorem forOut_sound (bi : Builtins) (fuel : Nat) {N : Nat} {L : LeafSpec} {x : String}
    {n : Nat} {body : LowCT} {Γ : Ctxt nfDialect} {σ : NfEnv Γ}
    {rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (CmdOut Δ)} {o : CmdOut Γ}
    (h : forOut σ x n (assigned body) rec = some o)
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) (ob : CmdOut Δ), rec σ' = some ob →
      ∀ (r r' : RustState) (U : Valuation Δ), RustExec N L body r r' →
        EnvRel σ' (stEnv r) U → RunInRange N L body r →
        ∃ U', PDen bi fuel ob.pre U = some U' ∧ EnvRel ob.σ (stEnv r') U')
    {rs rs' : RustState} {V : Valuation Γ} (hex : RustExec N L (.RFor x n body) rs rs')
    (hrel : EnvRel σ (stEnv rs) V)
    (hr : ∀ i, i < n → ∀ r1, RustExec N L (.RFor x i body) rs r1 →
      RunInRange N L body (rsSetScalar r1 x i)) :
    ∃ W, PDen bi fuel o.pre V = some W ∧ EnvRel o.σ (stEnv rs') W := by
  unfold forOut at h
  split at h
  · rename_i hn
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ob, hob, rets, hrets, rfl⟩ := h
    have hrel₀ : EnvRel (σ.mapV (Δ := NfTy.word 64 :: Γ) .there) (stEnv rs)
        (V.extend (t := NfTy.word 64) (BitVec.ofNat 64 n)) :=
      hrel.mapV (fun v => Var.there v) fun _ _ => rfl
    obtain ⟨acc, hfold, hc, hf⟩ := forLoop_fold bi fuel
      (carriedEntries_lookup _ x _)
      (fun y q hl hyx hy => not_mem_of_not_carried _ x _ hl hyx hy) hrets
      (fun r r' U => hrec _ ob hob r r' U) hrel₀ n (Nat.le_of_lt hn) rs' hex hr
    refine ⟨hvAppend acc (V.extend (t := NfTy.word 64) (BitVec.ofNat 64 n)), ?_, ?_⟩
    · show PDen bi fuel (.forLoop .here _ _ .nil)
        (V.extend (t := NfTy.word 64) (BitVec.ofNat 64 n)) = _
      refine PDen_forLoop_some bi fuel n ?_ (by rw [← List.range_eq_range']; exact hfold) rfl
      show (BitVec.ofNat 64 n).toNat = n
      rw [BitVec.toNat_ofNat]
      omega
    · refine EnvRel.loopEnv _ x _ _ (by rw [List.length_map, entriesVars_length]) _ _ ?_ hf ?_
      · rw [lookupArgs_headVars]
        exact hc
      · intro t v
        exact Var.lookup_shiftApp _ acc v _
  · cases h

/-- **The translation of commands simulates `RustExec`.** If `cmdToNF c σ = some o`, a run
    of `c` from `rs` to `rs'` that is in range, from a state related to the valuation `V`,
    is matched at every fuel by the denotation of the prefix of `o` from `V`, to a
    valuation related to `rs'` by the environment of names of `o`. -/
theorem cmdToNF_sim (bi : Builtins) (fuel : Nat) {N : Nat} {L : LeafSpec} (c : LowCT) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : CmdOut Γ), cmdToNF c σ = some o →
      ∀ (rs rs' : RustState) (V : Valuation Γ), RustExec N L c rs rs' →
        EnvRel σ (stEnv rs) V → RunInRange N L c rs →
        ∃ W, PDen bi fuel o.pre V = some W ∧ EnvRel o.σ (stEnv rs') W := by
  induction c with
  | RSkip =>
      intro Γ σ o h rs rs' V hex hrel _
      simp only [cmdToNF, Option.some.injEq] at h
      subst h
      cases hex
      exact ⟨V, rfl, hrel⟩
  | RAssert l =>
      intro Γ σ o h rs rs' V hex hrel _
      simp only [cmdToNF, Option.some.injEq] at h
      subst h
      cases hex
      exact ⟨V, rfl, hrel⟩
  | RBlock b ih =>
      intro Γ σ o h rs rs' V hex hrel hr
      simp only [cmdToNF] at h
      cases hex with
      | block _ _ _ hb => exact ih σ o h rs rs' V hb hrel hr
  | RSeq a b iha ihb =>
      intro Γ σ o h rs rs' V hex hrel hr
      simp only [cmdToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
      cases hex with
      | seq _ _ _ r1 _ h1 h2 =>
        obtain ⟨W1, hW1, hrel1⟩ := iha σ oa hoa rs r1 V h1 hrel hr.1
        obtain ⟨W2, hW2, hrel2⟩ := ihb oa.σ ob hob r1 rs' W1 h2 hrel1 (hr.2 r1 h1)
        exact ⟨W2, PDen_append_some bi fuel hW1 hW2, hrel2⟩
  | RLetU64Zero x b ih =>
      intro Γ σ o h rs rs' V hex hrel hr
      simp only [cmdToNF, Option.map_eq_some_iff] at h
      obtain ⟨ob, hob, rfl⟩ := h
      cases hex with
      | letU64Zero _ _ _ _ hb =>
        have hrel' : EnvRel ((x, ⟨NfTy.word 64, Var.here⟩) :: σ.mapV .there)
            (stEnv (rsSetScalar rs x 0)) (V.extend (t := NfTy.word 64) (0 : BitVec 64)) :=
          envRel_setWord (hrel.mapV (fun v => Var.there v)
            (W := V.extend (t := NfTy.word 64) (0 : BitVec 64)) fun _ _ => rfl) x Var.here rfl
        obtain ⟨W, hW, hrelW⟩ := ih _ ob hob _ rs' _ hb hrel' hr
        exact ⟨W, hW, hrelW⟩
  | RScalarSet x n =>
      intro Γ σ o h rs rs' V hex hrel _
      simp only [cmdToNF] at h
      split at h
      · rename_i hn
        simp only [Option.some.injEq] at h
        subst h
        cases hex
        refine ⟨V.extend (t := NfTy.word 64) (BitVec.ofNat 64 n), rfl,
          envRel_setWord (hrel.mapV (fun v => Var.there v)
            (W := V.extend (t := NfTy.word 64) (BitVec.ofNat 64 n)) fun _ _ => rfl)
            x Var.here ?_⟩
        show (BitVec.ofNat 64 n).toNat = n
        rw [BitVec.toNat_ofNat]
        omega
      · cases h
  | RScalarSetExpr x e =>
      intro Γ σ o h rs rs' V hex hrel hr
      simp only [cmdToNF, Option.map_eq_some_iff] at h
      obtain ⟨oe, hoe, rfl⟩ := h
      cases hex
      obtain ⟨W, hW, hres⟩ := seToNF_sound bi fuel e σ oe hoe rs V hrel hr
      refine ⟨W, hW, envRel_setWord (hrel.mapV _ fun t u =>
        @NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ fuel _ _ _ oe.pre u _ _ hW)
        x _ ?_⟩
      rw [hres]
      exact SExpr.toNat_evalStateBV_of_inRangeState rs e hr
  | RFor x n body ih =>
      intro Γ σ o h rs rs' V hex hrel hr
      simp only [cmdToNF] at h
      exact forOut_sound bi fuel h (fun σ' ob hob r r' U hb hrelU hrU =>
        ih σ' ob hob r r' U hb hrelU hrU) hex hrel hr
  | _ =>
      intro Γ σ o h
      simp [cmdToNF] at h

/-! ## 5. The one-result program -/

/-- **The lowering of a command to a one-result program** over the parameters `ps`: the
    prefix of `cmdToNF` from the environment of names of the parameters, returning the word
    variable of the scalar name `res`. `none` when the command is outside the fragment or
    `res` is not a word name at the end. -/
def lowCTToNF (ps : List (String × NfTy)) (res : String) (c : LowCT) :
    Option (Σ t : NfTy, NFProg nfDialect (entryCtx ps) [t]) :=
  (cmdToNF c (entryEnv ps)).bind fun o => (wordVar o.σ res).map fun v =>
    ⟨NfTy.word 64, o.pre.plug (.ret (.cons v .nil))⟩

/-- **The lowering simulates `RustExec`.** If `lowCTToNF ps res c = some q`, a run of `c`
    from `rs` to `rs'` that is in range (`RunInRange`), from a state whose scalar heap
    holds the values of `V` at the parameters (`StateVals`), is matched at every fuel by the
    denotation of `q` from `V`, whose result encodes the scalar `res` of `rs'`. -/
theorem lowCTToNF_sim (bi : Builtins) (fuel : Nat) {N : Nat} {L : LeafSpec}
    {ps : List (String × NfTy)} {res : String} {c : LowCT}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx ps) [t]} (h : lowCTToNF ps res c = some q)
    {rs rs' : RustState} {V : Valuation (entryCtx ps)} (hex : RustExec N L c rs rs')
    (hrel : StateVals rs ps V) (hr : RunInRange N L c rs) :
    ∃ y : q.1.denote, PDenP bi fuel q.2 V = some (.cons y .nil) ∧
      enc q.1 y = .int (rs'.rsScalar res) := by
  simp only [lowCTToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ho, v, hv, rfl⟩ := h
  obtain ⟨W, hW, hrelW⟩ := cmdToNF_sim bi fuel c _ o ho rs rs' V hex (entryEnv_rel hrel) hr
  refine ⟨v.lookup W, PDenP_plug_ret bi fuel o.pre _ V hW, ?_⟩
  rw [rsScalar_of_wordVar hrelW hv]
  rfl

end CatCrypt.Crypto.Hax.LowCTToNF
