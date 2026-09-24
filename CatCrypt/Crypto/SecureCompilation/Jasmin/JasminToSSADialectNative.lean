/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminMonoSem
public import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect

/-!
# Native dialect-translator correctness

This file proves `translateMonoCmdD_denoteSP_native`: the
dialect-targeting Jasmin → SSA translator `translateMonoCmdD` denotes
(under the dialect's `SPComp` security interpretation `Com.denoteSP`) to
the Jasmin reference semantics `pureEvalMonoCmd`. It is proved **directly by
induction on the command**, computing `Com.denoteSP` through each translated
arm's dialect-op denotation.

`translateMonoCmdD` emits `Com catCryptDialect` ops directly from the
Jasmin AST (see `JasminToSSADialect.lean`), so this correctness proof is
likewise direct:

1. **Dialect-only.** The proof references only `translateMonoCmdD`,
   `Com.denoteSP`, and the per-op dialect denotation facts
   (`catCryptDenoteSP`, `toVIRVar_lookup`). The per-expression agreement
   (`translateMonoExprD_denoteSP`) is derived directly against the
   `catCryptDialect` op denotation.

2. **Sorry-free.** The `Copn` head is dispatched via the function's own
   equation compiler (`unfold translateMonoCmdD; split`), so the wildcard
   arms carry the negative shape information as `h_trans : none = some _`
   (immediately contradictory) — there is no `match`-compiler wildcard
   `sorry`. The two translated intrinsic shapes (`ADD_64` / `ADC_64`) — which
   `translateMonoCmdD` translates to a 3-`let` dialect chain over the carry
   ops `bvAdd64` / `bvAdc` (plus `fst` / `snd` destructuring) — are proved
   natively against `Com.denoteSP`. The proof is `sorryAx`-free (verified by
   `#print axioms` at the foot of the file — only `propext`,
   `Classical.choice`, `Quot.sound`).

## Coverage

The covered fragment is exactly the `some`-image of `translateMonoCmdD`:

* `[]` (return),
* `Cassgn (.Lvar x) … (.Pvar gv)` (copy / alias),
* `Cassgn (.Lvar x) … e` (op / const / shift / not — every
  `translateMonoExprD`-accepted expression head),
* the `ADD_64` / `ADC_64` `Copn` intrinsics (`bvAdd64` / `bvAdc` + `fst` /
  `snd` 3-`let` chain).

Every other `Copn` head and all control flow (`Cif` / `Cfor` / `Cwhile` /
`Ccall`) are declined to `none` by `translateMonoCmdD`, so the hypothesis
`translateMonoCmdD m retVar cmd = some dprog` rules them out. The main result is
that the full bignum ALU spine + carry intrinsics — everything the
`S2NBignumSSA` ports use — denotes to the Jasmin reference semantics on
`catCryptDialect`, with all goals closed.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.ToSSADialect

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.ToSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open scoped ENNReal

set_option autoImplicit false

noncomputable section

/-! ## Per-expression native agreement

Whenever `translateMonoExprD m e = some dexpr`, the dialect expression's
`SPComp` denotation is `SPComp.pure (pureEvalMonoExpr n env e)`, under the
simulation invariant `monoAgrees`. Proved **directly** on the dialect side: we
unfold `translateMonoExprD` per Jasmin-expression head to the concrete
`catCryptDialect` op it emits, then evaluate `Expr.denoteSP` through that op's
`catCryptDenoteSP` interpretation and the argument-lookup bridge
(`lookupArgs_one` / `lookupArgs_two`, `toVIRVar_lookup`). -/

/-- **Native per-expression correctness.** If `translateMonoExprD m e = some
    dexpr`, then `Expr.denoteSP dexpr (toVIRVal V) = SPComp.pure
    (pureEvalMonoExpr n env e)` under `monoAgrees m V env`. -/
theorem translateMonoExprD_denoteSP {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n)
    (h_agrees : monoAgrees m V env) (e : PExpr)
    (dexpr : Expr catCryptDialect Γ (.sword n))
    (h_trans : translateMonoExprD m e = some dexpr) :
    Expr.denoteSP dexpr (toVIRVal V) = SPComp.pure (pureEvalMonoExpr n env e) := by
  cases e with
  | Pconst z =>
    simp only [translateMonoExprD, Option.some.injEq] at h_trans
    subst h_trans
    simp only [Expr.denoteSP, catCryptDenoteSP, DialectDenote.denote, pureEvalMonoExpr]
  | Papp2 op e1 e2 =>
    cases e1 with
    | Pvar x =>
      cases e2 with
      | Pvar y =>
        -- two-variable operands: only the six ALU binops translate (via
        -- `translateBinOpD`); every other head (incl. the shift ops, which need
        -- a *constant* second operand) makes `translateBinOpD` decline → `none`.
        cases op with
        | Olxor ws | Oland ws | Olor ws | Oadd ws | Osub ws | Omul ws =>
          -- binary ALU op: `translateMonoExprD` emits the matching
          -- `catCryptDialect` two-operand op directly; evaluate it through
          -- `catCryptDenoteSP` and the two-argument lookup bridge.
          match h_mx : m x.gv.var, h_my : m y.gv.var with
          | some cvx, some cvy =>
            simp only [translateMonoExprD, h_mx, h_my,
              translateBinOpD, Option.some.injEq] at h_trans
            subst h_trans
            simp only [Expr.denoteSP, catCryptDenoteSP, DialectDenote.denote,
              pureEvalMonoExpr]
            rw [lookupArgs_two, h_agrees x.gv.var cvx h_mx, h_agrees y.gv.var cvy h_my]
            rfl
          | some _, none =>
            simp only [translateMonoExprD, h_mx, h_my] at h_trans
            exact absurd h_trans (by simp)
          | none, _ =>
            simp only [translateMonoExprD, h_mx] at h_trans
            exact absurd h_trans (by simp)
        | Olsl ws | Olsr ws =>
          -- shift ops with a *variable* second operand: `translateBinOpD`
          -- declines, so `translateMonoExprD` is `none`.
          all_goals (
            match h_mx : m x.gv.var, h_my : m y.gv.var with
            | some cvx, some cvy =>
              simp only [translateMonoExprD, h_mx, h_my, translateBinOpD] at h_trans
              exact absurd h_trans (by simp)
            | some _, none =>
              simp only [translateMonoExprD, h_mx, h_my] at h_trans
              exact absurd h_trans (by simp)
            | none, _ =>
              simp only [translateMonoExprD, h_mx] at h_trans
              exact absurd h_trans (by simp))
        | _ =>
          -- any other op with two variable operands: `translateBinOpD` declines.
          match h_mx : m x.gv.var, h_my : m y.gv.var with
          | some cvx, some cvy =>
            simp only [translateMonoExprD, h_mx, h_my, translateBinOpD] at h_trans
            exact absurd h_trans (by simp)
          | some _, none =>
            simp only [translateMonoExprD, h_mx, h_my] at h_trans
            exact absurd h_trans (by simp)
          | none, _ =>
            simp only [translateMonoExprD, h_mx] at h_trans
            exact absurd h_trans (by simp)
      | Pconst k =>
        -- a constant second operand: only the shift ops `Olsl` / `Olsr`
        -- translate (to `bvShiftL` / `bvShiftR`); every other head declines.
        cases op with
        | Olsl ws =>
          -- left shift by a constant: emits `bvShiftL`.
          match h_mx : m x.gv.var with
          | some cvx =>
            simp only [translateMonoExprD, h_mx, Option.some.injEq] at h_trans
            subst h_trans
            simp only [Expr.denoteSP, catCryptDenoteSP, DialectDenote.denote,
              pureEvalMonoExpr]
            rw [lookupArgs_one, h_agrees x.gv.var cvx h_mx]
            rfl
          | none =>
            simp only [translateMonoExprD, h_mx] at h_trans
            exact absurd h_trans (by simp)
        | Olsr ws =>
          -- right shift by a constant: emits `bvShiftR`.
          match h_mx : m x.gv.var with
          | some cvx =>
            simp only [translateMonoExprD, h_mx, Option.some.injEq] at h_trans
            subst h_trans
            simp only [Expr.denoteSP, catCryptDenoteSP, DialectDenote.denote,
              pureEvalMonoExpr]
            rw [lookupArgs_one, h_agrees x.gv.var cvx h_mx]
            rfl
          | none =>
            simp only [translateMonoExprD, h_mx] at h_trans
            exact absurd h_trans (by simp)
        | _ =>
          simp only [translateMonoExprD] at h_trans
          exact absurd h_trans (by simp)
      | _ =>
        simp only [translateMonoExprD] at h_trans
        exact absurd h_trans (by simp)
    | _ =>
      simp only [translateMonoExprD] at h_trans
      exact absurd h_trans (by simp)
  | Papp1 op arg =>
    cases op with
    | Olnot ws =>
      cases arg with
      | Pvar x =>
        -- bitwise not: emits `bvNot`.
        match h_mx : m x.gv.var with
        | some cvx =>
          simp only [translateMonoExprD, h_mx, Option.some.injEq] at h_trans
          subst h_trans
          simp only [Expr.denoteSP, catCryptDenoteSP, DialectDenote.denote,
            pureEvalMonoExpr]
          rw [lookupArgs_one, h_agrees x.gv.var cvx h_mx]
          rfl
        | none =>
          simp only [translateMonoExprD, h_mx] at h_trans
          exact absurd h_trans (by simp)
      | _ =>
        simp only [translateMonoExprD] at h_trans
        exact absurd h_trans (by simp)
    | _ =>
      simp only [translateMonoExprD] at h_trans
      exact absurd h_trans (by simp)
  | _ =>
    simp only [translateMonoExprD] at h_trans
    exact absurd h_trans (by simp)

/-- The valuation bridge `toVIRVal` commutes with extension: extending an
    `HVec` and then bridging equals bridging then extending the VIR valuation.
    Holds by `rfl` (`HVec.extend` / `toVIRVal` / `Ctxt.Valuation.extend` are all
    the matching `.cons`). The key lemma that aligns the IH's bridged-extended
    valuation with the `Com.denoteSP_var` bind continuation. -/
theorem toVIRVal_extend {Γ : Ctx} {n : Nat} (V : HVec Γ) (val : BitVec n) :
    toVIRVal (HVec.cons (t := .sword n) val V) = (toVIRVal V).extend val := rfl

/-! ## Native command correctness -/

/-- **Native dialect-translator correctness.** If the dialect translator
    succeeds (`translateMonoCmdD m retVar cmd = some dprog` — necessarily on
    the straight-line ALU fragment it covers), then the dialect program's
    `SPComp`-valued security denotation `Com.denoteSP` agrees with the Jasmin
    reference semantics `pureEvalMonoCmd`, under the simulation invariant
    `monoAgrees`.

    Proved **directly** by induction on `cmd`, computing `Com.denoteSP` through
    each translated arm. `translateMonoCmdD` declines every `Copn` head other
    than `ADD_64` / `ADC_64` to `none`, so the hypothesis rules those arms
    out. -/
theorem translateMonoCmdD_denoteSP_native {Γ : Ctx} {n : Nat}
    (m : MonoVarMap Γ n) (V : HVec Γ) (env : Var → BitVec n)
    (retVar : Var) (cmd : List InstrR)
    (dprog : Com catCryptDialect Γ (.sword n))
    (h_agrees : monoAgrees m V env)
    (h_trans : translateMonoCmdD m retVar cmd = some dprog) :
    Com.denoteSP dprog (toVIRVal V) = SPComp.pure (pureEvalMonoCmd n env retVar cmd) := by
  induction cmd generalizing Γ m V env dprog with
  | nil =>
    -- return: `Com.denoteSP (.ret (toVIRVar cv)) = pure ((toVIRVar cv).lookup …)`
    simp only [translateMonoCmdD] at h_trans
    split at h_trans
    · rename_i cv h_ret
      cases h_trans
      simp only [Com.denoteSP_ret, pureEvalMonoCmd]
      rw [toVIRVar_lookup]
      exact congrArg SPComp.pure (h_agrees retVar cv h_ret)
    · exact absurd h_trans (by simp)
  | cons instr rest ih =>
    cases instr with
    | Cassgn lv tag ty e =>
      cases lv with
      | Lvar x =>
        cases e with
        | Pvar gv =>
          -- copy / alias arm
          simp only [translateMonoCmdD] at h_trans
          split at h_trans
          · rename_i cv h_src
            have h_agrees' : monoAgrees
                (fun w => if w = x.var then some cv else m w) V
                (fun w => if w = x.var then env gv.gv.var else env w) := by
              intro w cv' h_lookup
              by_cases hw : w = x.var
              · subst hw; simp at h_lookup ⊢; cases h_lookup
                exact h_agrees gv.gv.var cv h_src
              · simp [hw] at h_lookup ⊢
                exact h_agrees w cv' h_lookup
            simp only [pureEvalMonoCmd, pureEvalMonoExpr]
            exact ih _ V _ _ h_agrees' h_trans
          · exact absurd h_trans (by simp)
        | _ =>
          -- op / const / shift / not arm
          simp only [translateMonoCmdD] at h_trans
          split at h_trans
          · rename_i dexpr h_expr
            split at h_trans
            · rename_i body h_body
              cases h_trans
              -- `Com.denoteSP (.var dexpr body) = bind (Expr.denoteSP dexpr …) …`.
              rw [Com.denoteSP_var]
              rw [translateMonoExprD_denoteSP m V env h_agrees _ dexpr h_expr]
              rw [SPComp.pure_bind]
              -- body: unfold only the command head (keep `pureEvalMonoExpr`
              -- folded so the new value matches `monoAgrees_extend`), realign
              -- the valuation via `toVIRVal_extend`, then recurse via IH.
              simp only [pureEvalMonoCmd]
              rw [← toVIRVal_extend V (pureEvalMonoExpr n env _)]
              exact ih (m.extend x.var) _ _ _
                (monoAgrees_extend h_agrees x.var _) h_body
            · exact absurd h_trans (by simp)
          · exact absurd h_trans (by simp)
      | Lnone _ _ | Lmem _ _ _ | Laset _ _ _ _ | Lasub _ _ _ _ _ =>
        simp [translateMonoCmdD] at h_trans
    | Copn lvs tag op es =>
      -- `translateMonoCmdD` translates the `ADD_64` / `ADC_64` intrinsic
      -- shapes to a 3-`let` dialect chain (`bvAdd64`/`bvAdc`; `fst`; `snd`)
      -- and declines every other `Copn` head to `none`. Drive the match via
      -- the function's own splitter so the wildcard arms carry the negative
      -- shape information (`h_trans : none = some _`, impossible); on the two
      -- intrinsic shapes, relate both sides through the body IH.
      unfold translateMonoCmdD at h_trans
      split at h_trans
      · exact absurd ‹(_ : List InstrR) = []› (by simp)
      · exact absurd ‹InstrR.Copn _ _ _ _ :: _ = InstrR.Cassgn _ _ _ _ :: _› (by simp)
      · exact absurd ‹InstrR.Copn _ _ _ _ :: _ = InstrR.Cassgn _ _ _ _ :: _› (by simp)
      · -- ADD_64 shape : `dprog` = bvAdd64 ; fst ; snd ; body.
        next heq =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
            lvs = _ ∧ tag = _ ∧ op = _ ∧ es = _ ∧ rest = _ := by
          simpa only [List.cons.injEq, InstrR.Copn.injEq, and_assoc] using heq
        rename_i _ _ _ cfv _ _ _ _ _ _ rv av bv
        clear heq
        cases hma : m av.gv.var with
        | none => simp only [hma] at h_trans; exact absurd h_trans (by simp)
        | some cva =>
        cases hmb : m bv.gv.var with
        | none => simp only [hma, hmb] at h_trans; exact absurd h_trans (by simp)
        | some cvb =>
        cases hbody : translateMonoCmdD (m.extend2 cfv.var rv.var) retVar rest with
        | none =>
          simp only [hma, hmb, hbody] at h_trans; exact absurd h_trans (by simp)
        | some body =>
          simp only [hma, hmb, hbody, Option.some.injEq] at h_trans
          subst h_trans
          simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP]
          rw [lookupArgs_two]
          simp only [SPComp.pure_bind, DialectDenote.denote]
          dsimp only [HVector.head, HVector.tail, Expr.lookupArgs]
          simp only []
          -- The 3-`let` chain's final valuation is, definitionally, the bridge
          -- of the `extend2` heap (`snd`, `fst`, `pair` pushed on `V`).
          show Com.denoteSP body (toVIRVal
              (HVec.cons (BitVec.adc (cva.lookup V) (cvb.lookup V) false).2
                (HVec.cons
                  (if (BitVec.adc (cva.lookup V) (cvb.lookup V) false).1 = true then 1 else 0)
                  (HVec.cons
                    ((if (BitVec.adc (cva.lookup V) (cvb.lookup V) false).1 = true then 1 else 0),
                      (BitVec.adc (cva.lookup V) (cvb.lookup V) false).2) V)))) = _
          -- Evaluate the body via the IH on the `extend2` heap, with the
          -- `extend2`-shaped env (`monoAgrees_extend2`). Both heap and env are
          -- threaded explicitly so the IH's conclusion lines up; the remaining
          -- RHS env mismatch (`boolToBVaux p.fst` vs `if p.fst then 1 else 0`)
          -- is a pointwise equality.
          rw [ih (m.extend2 cfv.var rv.var)
                (HVec.cons (BitVec.adc (cva.lookup V) (cvb.lookup V) false).2
                  (HVec.cons
                    (if (BitVec.adc (cva.lookup V) (cvb.lookup V) false).1 = true then 1 else 0)
                    (HVec.cons
                      ((if (BitVec.adc (cva.lookup V) (cvb.lookup V) false).1 = true then 1 else 0),
                        (BitVec.adc (cva.lookup V) (cvb.lookup V) false).2) V)))
                (fun w => if w = rv.var
                            then (BitVec.adc (cva.lookup V) (cvb.lookup V) false).2
                          else if w = cfv.var
                            then (if (BitVec.adc (cva.lookup V) (cvb.lookup V) false).1 = true
                                  then 1 else 0)
                          else env w)
                body
                (monoAgrees_extend2 h_agrees cfv.var rv.var _ _ _ rfl rfl) hbody]
          simp only [pureEvalMonoCmd]
          rw [show cva.lookup V = env av.gv.var from h_agrees av.gv.var cva hma,
              show cvb.lookup V = env bv.gv.var from h_agrees bv.gv.var cvb hmb]
          congr 2
          funext w
          by_cases h1 : w = rv.var
          · simp [h1]
          · simp only [h1, if_false]
            by_cases h2 : w = cfv.var
            · simp only [h2, if_true, boolToBVaux]
              split <;> simp_all
            · simp [h2]
      · -- ADC_64 shape : `dprog` = bvAdc ; fst ; snd ; body. Same shape as
        -- ADD_64 with a third (carry-in) operand `cinv`.
        next heq =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
            lvs = _ ∧ tag = _ ∧ op = _ ∧ es = _ ∧ rest = _ := by
          simpa only [List.cons.injEq, InstrR.Copn.injEq, and_assoc] using heq
        rename_i _ _ _ cfv _ _ _ _ _ _ rv av bv cinv
        clear heq
        cases hma : m av.gv.var with
        | none => simp only [hma] at h_trans; exact absurd h_trans (by simp)
        | some cva =>
        cases hmb : m bv.gv.var with
        | none => simp only [hma, hmb] at h_trans; exact absurd h_trans (by simp)
        | some cvb =>
        cases hmcin : m cinv.gv.var with
        | none =>
          simp only [hma, hmb, hmcin] at h_trans; exact absurd h_trans (by simp)
        | some cvcin =>
        cases hbody : translateMonoCmdD (m.extend2 cfv.var rv.var) retVar rest with
        | none =>
          simp only [hma, hmb, hmcin, hbody] at h_trans; exact absurd h_trans (by simp)
        | some body =>
          simp only [hma, hmb, hmcin, hbody, Option.some.injEq] at h_trans
          subst h_trans
          simp only [Com.denoteSP_var, Expr.denoteSP, catCryptDenoteSP]
          rw [lookupArgs_three]
          simp only [SPComp.pure_bind, DialectDenote.denote]
          dsimp only [HVector.head, HVector.tail, Expr.lookupArgs]
          simp only []
          show Com.denoteSP body (toVIRVal
              (HVec.cons
                  (BitVec.adc (cva.lookup V) (cvb.lookup V)
                    ((cvcin.lookup V).toNat ≠ 0)).2
                (HVec.cons
                  (if (BitVec.adc (cva.lookup V) (cvb.lookup V)
                        ((cvcin.lookup V).toNat ≠ 0)).1 = true then 1 else 0)
                  (HVec.cons
                    ((if (BitVec.adc (cva.lookup V) (cvb.lookup V)
                          ((cvcin.lookup V).toNat ≠ 0)).1 = true then 1 else 0),
                      (BitVec.adc (cva.lookup V) (cvb.lookup V)
                        ((cvcin.lookup V).toNat ≠ 0)).2) V)))) = _
          rw [ih (m.extend2 cfv.var rv.var)
                (HVec.cons
                    (BitVec.adc (cva.lookup V) (cvb.lookup V)
                      ((cvcin.lookup V).toNat ≠ 0)).2
                  (HVec.cons
                    (if (BitVec.adc (cva.lookup V) (cvb.lookup V)
                          ((cvcin.lookup V).toNat ≠ 0)).1 = true then 1 else 0)
                    (HVec.cons
                      ((if (BitVec.adc (cva.lookup V) (cvb.lookup V)
                            ((cvcin.lookup V).toNat ≠ 0)).1 = true then 1 else 0),
                        (BitVec.adc (cva.lookup V) (cvb.lookup V)
                          ((cvcin.lookup V).toNat ≠ 0)).2) V)))
                (fun w => if w = rv.var
                            then (BitVec.adc (cva.lookup V) (cvb.lookup V)
                              ((cvcin.lookup V).toNat ≠ 0)).2
                          else if w = cfv.var
                            then (if (BitVec.adc (cva.lookup V) (cvb.lookup V)
                                  ((cvcin.lookup V).toNat ≠ 0)).1 = true then 1 else 0)
                          else env w)
                body
                (monoAgrees_extend2 h_agrees cfv.var rv.var _ _ _ rfl rfl) hbody]
          simp only [pureEvalMonoCmd]
          rw [show cva.lookup V = env av.gv.var from h_agrees av.gv.var cva hma,
              show cvb.lookup V = env bv.gv.var from h_agrees bv.gv.var cvb hmb,
              show cvcin.lookup V = env cinv.gv.var from h_agrees cinv.gv.var cvcin hmcin]
          congr 2
          funext w
          by_cases h1 : w = rv.var
          · simp [h1]
          · simp only [h1, if_false]
            by_cases h2 : w = cfv.var
            · simp only [h2, if_true, boolToBVaux]
              split <;> simp_all
            · simp [h2]
      · exact absurd h_trans (by simp)
    | Cif _ _ _ | Cfor _ _ _ | Cwhile _ _ _ | Ccall _ _ _ _ =>
      simp [translateMonoCmdD] at h_trans

end

-- The native dialect-translator correctness depends only on the three standard
-- Lean axioms — no `sorryAx`. This is the point of the file: the dialect
-- reference semantics are established without routing through
-- `translateMonoCmd_correct` (which inherits the pre-existing `Copn`-wildcard
-- `sorry` in `translateMonoCmd_Copn_correct`). Reported axioms:
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms translateMonoCmdD_denoteSP_native

end CatCrypt.Crypto.Jasmin.ToSSADialect
