/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.Hax.HaxExitTypedCT

/-!
# The lowering of `NFProg nfDialect` to `LowCT`

`nfToLowCT A R p ρ` lowers a one-result program `p` of `NFProg nfDialect` to a `LowCT` command
under the placement `A` and the result placement `R`, from the reading `ρ` of its context.
The variables of `p` are held in source names: a binding named by `NfOp.named` in its name,
an unnamed call in a fresh temporary (`tmpName`), and a literal, a tuple and a trip count are
read without a slot (`RB`, as for the readback `nfToImp`).

A binding of a literal, a variable or a call on variables is lowered by the statement
lowering `letHeadT A` of the typed exit front, under the conditions of its exit fragment; a
scalar operation with a literal operand is an assignment of its scalar expression with the
literal as an immediate (`scalarOpHeadNF`). A counted loop whose body starts with a named
counter `i` is a `RForRuntime` over a reserved trip index (`nfRunName`) whose bound is the
trip count, with `i` set to the trip index plus `lo` at the head of each trip; its carried
values are held in the names of its initial atoms and written back at the end of the body.
The result, a variable, is stored by `resultStoreT A`.

The lowering makes three choices that a lowering of the exit front's output makes by passes.
It emits no exit frame: there is no exit flag, payload slot or flag test, since a program of
`NFProg` has no early exit. It emits no zero initialisation of a scalar slot: the first write
to each slot is its binding or the counter assignment. It binds no literal: a literal is read
as an immediate operand of the commands that use it.

## Main definitions

* `atomSE`, `scalarOpHeadNF` — the scalar expression of an atom, and the head of a scalar
  operation on atoms.
* `nfHead` — the head of one binding.
* `nfAssigns` — the write-back of the carried names of a loop body.
* `nfRunName` — the trip index of a loop.
* `LK`, `nfLow` — the continuation at a return, and the lowering with its fresh temporaries
  and the names it writes.
* `nfResult`, `nfToLowCT` — the store of the result, and the lowering of a one-result
  program.
* `RhsVal`, `LKSound`, `LowSound` — what a right-hand side states about its value, and the
  simulation statements of a continuation and of a program.

## Main results

* `headNF_scalarOp`, `nfHead_sound` — every head runs from a state agreeing with the
  environment to one agreeing with the extended environment, the exit flag unchanged.
* `rbBind_rhsVal` — an emitted binding states the encoding of the value of its operation.
* `nfAssigns_sound` — the write-back of the carried names runs.
* `nfRunName_reserved`, `nfRunName_ne_ret` — the trip index is a reserved name other than
  the exit flag.
* `nfLow_sound_aux` — the lowering simulates the denotation of `NFProg`, through an
  environment related to the valuation and agreeing with the state.
* `nfToLowCT_sim` — the lowering of a one-result program runs to a state whose result slot
  agrees with the encoding of the value of the program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToLowCT

open _root_.Hax (ImpExpr ImpLit Value Env Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr RustState RustExec LeafSpec rsSetScalar
  rsSetTower)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. The lowering -/

/-- The scalar expression of an atom under the placement `A`: a non-reserved variable held
    in the scalar heap, or an integer literal in `[0, 2^64)` as an immediate. -/
def atomSE (A : ExitTowers) : ImpExpr → Option SExpr
  | .var x => if exitReserved x = false ∧ A.lookup x = none then some (.SVar x) else none
  | .lit (.int k) => if 0 ≤ k ∧ k < 2 ^ 64 then some (.SLit k.toNat) else none
  | _ => none

/-- The scalar expression of a scalar operation `f` on two atoms bound to the non-reserved
    scalar name `n`, a literal atom an immediate operand. -/
def scalarOpHeadNF (A : ExitTowers) (n f : String) : List ImpExpr → Option SExpr
  | [a, b] =>
      if exitReserved n = false ∧ A.lookup n = none then
        (atomSE A a).bind fun x => (atomSE A b).bind fun y => scalarOpExprT f x y
      else none
  | _ => none

/-- The head of the binding of the name `n` to `rhs`: for a literal, a variable or a call on
    variables, the statement lowering `letHeadT A n rhs` of the typed exit front under the
    conditions of its exit fragment; for a scalar operation with a literal operand, the
    assignment of `scalarOpHeadNF`. -/
def nfHead (A : ExitTowers) (n : String) : ImpExpr → Option (LowCT → LowCT)
  | .lit l =>
      if exitLitOk l = true ∧ exitReserved n = false then letHeadT A n (.lit l) else none
  | .var s =>
      if exitReserved n = false ∧ exitReserved s = false ∧ A.lookup n = A.lookup s then
        letHeadT A n (.var s)
      else none
  | .app f args =>
      if exitReserved n = false ∧ exitArgsOk args = true then letHeadT A n (.app f args)
      else (scalarOpHeadNF A n f args).map fun se b => .RSeq (.RScalarSetExpr n se) b
  | _ => none

/-- The write-back of the values of the atoms `as` to the carried names `ns`, as one binding
    of each name to its atom by `nfHead`; a name whose atom is itself is left out. `none`
    when a later atom reads a name an earlier write-back writes. -/
def nfAssigns (A : ExitTowers) : List String → List ImpExpr → Option LowCT
  | [], [] => some .RSkip
  | n :: ns, a :: as =>
      if isVarOf n a then nfAssigns A ns as
      else if as.any (isVarOf n) then none
      else (nfHead A n a).bind fun h => (nfAssigns A ns as).map h
  | _, _ => none

/-- The trip index of the loop lowered with the fresh temporary `c`: a reserved loop slot. -/
def nfRunName (c : Nat) : String := "__exit_run" ++ toString c

/-- The continuation of the lowering at a return: from the reading of the context and the
    returned variables, the command ending the program and the next fresh temporary. -/
abbrev LK (ts : List NfTy) : Type :=
  ∀ {Δ : Ctxt nfDialect}, RBEnv Δ → HVector (fun t => Var Δ t) ts → Nat →
    Option (LowCT × Nat)

/-- **The lowering** of an `NFProg` program from the reading `ρ` of its context, with the
    fresh temporaries from `c` and the continuation `lk` at its return. Its value is the
    command, the next fresh temporary and the source names the command writes outside the
    continuation. A named binding is a head of its name, an unnamed call a head of a fresh
    temporary, and a literal, a unit, a tuple and a trip count are read without a slot. A
    counted loop whose count reads as a trip count and whose body starts with a named `ctr`
    on a non-reserved scalar name is a `RForRuntime` over the trip index `nfRunName c`, its
    carried values held in the names of its initial atoms and written back by `nfAssigns` at
    the end of the body; it is lowered only when it writes no name the reading of the context
    still reads. -/
def nfLow (A : ExitTowers) :
    {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → RBEnv Γ →
    Nat → LK ts → Option (LowCT × Nat × List String)
  | _, _, .ret vs, ρ, c, lk => (lk ρ vs c).map fun r => (r.1, r.2, [])
  | _, _, .var e k, ρ, c, lk =>
      (rbBind ρ c e.op e.args).bind fun b =>
        match b with
        | .emit n rhs tmp =>
            (nfHead A n rhs).bind fun h =>
              (nfLow A k (RBEnv.cons (.name n) (ρ.clobber [n]))
                (if tmp then c + 1 else c) lk).map fun r => (h r.1, r.2.1, n :: r.2.2)
        | .inline r => nfLow A k (RBEnv.cons r ρ) c lk
  | _, _, .forLoop (cs := cs) count inits body k, ρ, c, lk =>
      match body with
      | .var e rest =>
        (ctrOf? e.op e.args).bind fun ⟨i, a, b⟩ =>
          match ρ count with
          | .trip lo hi =>
            (atomSE A hi).bind fun hiSE =>
            (rbAtoms ρ inits).bind fun xs => (namesOf xs).bind fun cn =>
              if cn.Nodup ∧ exitReserved i = false ∧ A.lookup i = none then
                let ρΓ : RBEnv _ := RBEnv.clobber cn ρ
                let ρB : RBEnv (cs ++ NfTy.word 64 :: _) :=
                  RBEnv.appNames cs cn (RBEnv.cons .idx (RBEnv.dropIdx ρΓ))
                match ρB a, ρB b with
                | .lit (.int lo'), .idx =>
                    if lo' = lo ∧ 0 ≤ lo then
                      (nfLow A rest (RBEnv.cons (.name i) (ρB.clobber [i])) (c + 1)
                          (fun ρ' vs c' => (rbAtoms ρ' vs).bind fun as =>
                            (nfAssigns A cn as).map (·, c'))).bind fun bc =>
                        let wr := i :: bc.2.2
                        if (RBEnv.allNames ρΓ).all fun n => !wr.contains n then
                          let loopC : LowCT :=
                            .RForRuntime (nfRunName c) (.SSub hiSE (.SLit lo.toNat))
                              (.RSeq (.RScalarSetExpr i
                                (.SAdd (.SVar (nfRunName c)) (.SLit lo.toNat))) bc.1)
                          (nfLow A k (RBEnv.appNames cs cn ρΓ) bc.2.1 lk).map fun r =>
                            (.RSeq loopC r.1, r.2.1, wr ++ cn ++ r.2.2)
                        else none
                    else none
                | _, _ => none
              else none
          | _ => none
      | _ => none
  | _, _, .ifThenElse .., _, _, _ => none
  | _, _, .whileLoop .., _, _, _ => none
  | _, _, .call .., _, _, _ => none

/-- The store of the result of a program: a non-reserved variable `x` whose placement is the
    result placement `R`, stored by `resultStoreT A`. -/
def nfResult (A : ExitTowers) (R : ExitRes) : RB → Option LowCT
  | .name x =>
      if exitReserved x = false ∧ ExitRes.ofPlace (A.lookup x) = R then
        resultStoreT A (.var x)
      else none
  | _ => none

/-- **The lowering of a one-result program**: `nfLow` with the result variable stored by
    `nfResult`. -/
def nfToLowCT (A : ExitTowers) (R : ExitRes) {Γ : Ctxt nfDialect} {t : NfTy}
    (p : NFProg nfDialect Γ [t]) (ρ : RBEnv Γ) : Option LowCT :=
  (nfLow A p ρ 0 fun ρ' vs c => match vs with
    | .cons v .nil => (nfResult A R (ρ' v)).map (·, c)).map (·.1)

/-! ## 2. The heads -/

section Heads

variable {bi : Builtins} {N : Nat} {leafSpec : LeafSpec} {br : ValueTowerBridge}
  {A : ExitTowers}

/-- The scalar expression of an atom evaluates, in a state agreeing with the environment, to
    the decoding of the value the atom reads, a scalar value. -/
theorem atomSE_eval {env : Env} {rs : RustState} {a : ImpExpr} {x : SExpr} {v : Value}
    (hag : envAgreesT br A env rs) (ha : atomSE A a = some x) (hv : AtomEval env a v) :
    ScalarValN v ∧ valueToScalar v = some (x.evalState rs) := by
  cases a with
  | var y =>
      simp only [atomSE] at ha
      split at ha
      · rename_i hc
        cases ha
        exact envAgreesT_scalar hag hc.1 hc.2 hv
      · cases ha
  | lit l =>
      cases l with
      | int k =>
          simp only [atomSE] at ha
          split at ha
          · rename_i hk
            cases ha
            change Value.ofLit (.int k) = v at hv
            subst hv
            refine ⟨⟨hk.1, hk.2⟩, ?_⟩
            simp [valueToScalar, Value.ofLit, hk.1, SExpr.evalState]
          · cases ha
      | _ => simp [atomSE] at ha
  | _ => simp [atomSE] at ha

/-- **The head of a scalar operation on atoms.** -/
theorem headNF_scalarOp (hops : ScalarOpsSoundT bi) {env : Env} {rs : RustState}
    {n f : String} {args : List ImpExpr} {se : SExpr} {vals : List Value} {r : Value}
    (hso : scalarOpHeadNF A n f args = some se) (hF : AtomsEval env args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs) :
    HeadResT N leafSpec br A env rs n r (fun b => .RSeq (.RScalarSetExpr n se) b)
      (rs.rsScalar exitRetName) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;> try (simp [scalarOpHeadNF] at hso; done)
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | ⟨vc, vals⟩⟩⟩ <;> try exact hF.elim
  · exact hF.2.elim
  · obtain ⟨ha, hb, -⟩ := hF
    simp only [scalarOpHeadNF] at hso
    split at hso
    · rename_i hn
      obtain ⟨x, hx, hso⟩ := Option.bind_eq_some_iff.mp hso
      obtain ⟨y, hy, hso⟩ := Option.bind_eq_some_iff.mp hso
      obtain ⟨hsa, hda⟩ := atomSE_eval hag hx ha
      obtain ⟨hsb, hdb⟩ := atomSE_eval hag hy hb
      have hop : (scalarOpExprT f (.SVar "a") (.SVar "b")).isSome = true := by
        rw [scalarOpExprT_isSome_any f (.SVar "a") (.SVar "b") x y, hso]; rfl
      obtain ⟨hsr, hdr⟩ := hops f va vb r _ _ hop hsa hsb hda hdb hbi
      rw [← scalarOpExprT_evalState_any hso] at hdr
      exact ⟨_, envAgreesT_extend hn.1 hn.2 hsr hdr hag, ret_setScalar hn.1 _ rfl,
        fun bC rs' h => RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) h⟩
    · cases hso
  · exact hF.2.2.elim

/-- Variable atoms read the values the variables hold. -/
theorem atomsEval_forall₂ {env : Env} :
    ∀ {args : List ImpExpr} {vals : List Value}, exitArgsOk args = true →
      AtomsEval env args vals →
      List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals
  | [], [], _, _ => .nil
  | .var x :: args, v :: vals, hok, ⟨hv, hvs⟩ => by
      simp only [exitArgsOk, Bool.and_eq_true] at hok
      exact .cons ⟨x, rfl, hv⟩ (atomsEval_forall₂ hok.2 hvs)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | .lit _ :: _, _ :: _, hok, _ => by simp [exitArgsOk] at hok
  | .letBind .. :: _, _ :: _, hok, _ | .lam .. :: _, _ :: _, hok, _
  | .app .. :: _, _ :: _, hok, _ | .tuple .. :: _, _ :: _, hok, _
  | .proj .. :: _, _ :: _, hok, _ | .ifThenElse .. :: _, _ :: _, hok, _
  | .match_ .. :: _, _ :: _, hok, _ | .unitVal :: _, _ :: _, hok, _
  | .seq .. :: _, _ :: _, hok, _ | .borrow .. :: _, _ :: _, hok, _
  | .deref .. :: _, _ :: _, hok, _ | .assign .. :: _, _ :: _, hok, _
  | .forLoop .. :: _, _ :: _, hok, _ | .forLoopRev .. :: _, _ :: _, hok, _
  | .whileLoop .. :: _, _ :: _, hok, _ | .break_ .. :: _, _ :: _, hok, _
  | .continue_ :: _, _ :: _, hok, _ | .earlyReturn .. :: _, _ :: _, hok, _
  | .questionMark .. :: _, _ :: _, hok, _ | .forFold .. :: _, _ :: _, hok, _
  | .forFoldRev .. :: _, _ :: _, hok, _ | .whileFold .. :: _, _ :: _, hok, _
  | .forFoldReturn .. :: _, _ :: _, hok, _ | .forFoldRevReturn .. :: _, _ :: _, hok, _
  | .whileFoldReturn .. :: _, _ :: _, hok, _ | .cfBreak .. :: _, _ :: _, hok, _
  | .cfContinue .. :: _, _ :: _, hok, _ | .cfBreakContinue .. :: _, _ :: _, hok, _
  | .typeAscription .. :: _, _ :: _, hok, _ => by simp [exitArgsOk] at hok

/-- What a right-hand side of a binding states about its value `w`: a literal reads `w`, a
    variable holds `w`, and a call evaluates its atoms to values on which the builtin returns
    `w`. -/
def RhsVal (bi : Builtins) (env : Env) : ImpExpr → Value → Prop
  | .lit l, w => Value.ofLit l = w
  | .var s, w => env s = some w
  | .app f args, w => ∃ vals, AtomsEval env args vals ∧ bi f vals = some w
  | _, _ => True

/-- **The heads are sound.** A head of `nfHead` runs, from a state agreeing with the
    environment, to a state agreeing with the environment extended by the value of the
    binding, with the exit flag unchanged. -/
theorem nfHead_sound
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {n : String} {rhs : ImpExpr} {h : LowCT → LowCT} (hh : nfHead A n rhs = some h)
    {env : Env} {rs : RustState} {w : Value} (hw : RhsVal bi env rhs w)
    (hag : envAgreesT br A env rs) :
    HeadResT N leafSpec br A env rs n w h (rs.rsScalar exitRetName) := by
  cases rhs with
  | lit l =>
      simp only [nfHead] at hh
      split at hh
      · rename_i hc
        change Value.ofLit l = w at hw
        subst hw
        exact headResT_lit hL.marshal hc.1 hc.2 hh hag rfl
      · cases hh
  | var s =>
      simp only [nfHead] at hh
      split at hh
      · rename_i hc
        exact headResT_var hc.1 hc.2.1 hc.2.2 hw hh hag rfl
      · cases hh
  | app f args =>
      obtain ⟨vals, hvals, hbi⟩ := hw
      simp only [nfHead] at hh
      split at hh
      · rename_i hc
        exact headResT_app hL hh hc.1 hc.2 (atomsEval_forall₂ hc.2 hvals) hbi hag rfl
      · obtain ⟨se, hse, rfl⟩ := Option.map_eq_some_iff.mp hh
        exact headNF_scalarOp hL.ops hse hvals hbi hag
  | _ => simp [nfHead] at hh

/-- A right-hand side of the readback states the encoding of the value of its operation. -/
theorem rbRhs_rhsVal {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (hrel : RBRel ρ env V) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) {rhs : ImpExpr}
      {y : op.ret.denote}, rbRhs ρ op args = some rhs →
      nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some y →
      RhsVal bi env rhs (enc op.ret y)
  | .call f as r, args, rhs, y, h, hy => by
      change (rbAtoms ρ args).map (ImpExpr.app f) = some rhs at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨xs, hxs, rfl⟩ := h
      change (bi f (encAll as (Expr.lookupArgs args V))).bind (dec r) = some y at hy
      rw [Option.bind_eq_some_iff] at hy
      obtain ⟨w, hw, hdec⟩ := hy
      exact ⟨_, rbAtoms_eval hrel args hxs, by rw [hw, dec_sound r w y hdec]⟩
  | .ilit t v, _, rhs, y, h, hy => by
      change (litOfIlit t v).map ImpExpr.lit = some rhs at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨l, hl, rfl⟩ := h
      exact litOfIlit_ofLit hl hy
  | .constBit b, _, rhs, y, h, hy => by
      change some (ImpExpr.lit (.bool b)) = some rhs at h
      change some b = some y at hy
      simp only [Option.some.injEq] at h hy
      subst h hy
      rfl
  | .constUnit, _, rhs, y, h, hy => by
      change some (ImpExpr.lit .unit) = some rhs at h
      simp only [Option.some.injEq] at h
      subst h
      rfl
  | .tnilV, _, rhs, y, h, hy => by
      change some (ImpExpr.tuple []) = some rhs at h
      simp only [Option.some.injEq] at h
      subst h
      trivial
  | .tconsV h₀ t, .cons a (.cons b .nil), rhs, y, h, hy => by
      change (match (ρ a).atom?, ρ b with
        | some x, .tup as => some (ImpExpr.tuple (x :: as))
        | _, _ => none) = some rhs at h
      split at h
      · cases h; trivial
      · cases h
  | .const _ _, _, _, _, h, _ | .bin _ _, _, _, _, h, _ | .un _ _, _, _, _, h, _
  | .cast _ _, _, _, _, h, _ | .scast _ _, _, _, _, h, _ | .cmp _ _, _, _, _, h, _
  | .andB, _, _, _, h, _ | .orB, _, _, _, h, _ | .xorB, _, _, _, h, _
  | .eqB, _, _, _, h, _ | .notB, _, _, _, h, _ | .index _ _, _, _, _, h, _
  | .update _ _, _, _, _, h, _ | .arrLit _ _, _, _, _, h, _ | .arrRepeat _ _, _, _, _, h, _
  | .mkPair _ _, _, _, _, h, _ | .fst _ _, _, _, _, h, _ | .snd _ _, _, _, _, h, _
  | .ctr, _, _, _, h, _ | .trip _, _, _, _, h, _ | .thead _ _, _, _, _, h, _
  | .ttail _ _, _, _, _, h, _ | .named _ _, _, _, _, h, _ => by
      simp [rbRhs] at h

/-- An emitted binding of the readback states the encoding of the value of its operation. -/
theorem rbBind_rhsVal {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (hrel : RBRel ρ env V) (c : Nat) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    {n : String} {rhs : ImpExpr} {tmp : Bool} {y : op.ret.denote}
    (h : rbBind ρ c op args = some (.emit n rhs tmp))
    (hy : nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some y) :
    RhsVal bi env rhs (enc op.ret y) := by
  cases op with
  | named n' op' =>
      change (rbRhs ρ op' args).map (fun rhs => RBBind.emit n' rhs false) = some _ at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨rhs', hrhs, heq⟩ := h
      cases heq
      exact rbRhs_rhsVal hrel op' args hrhs hy
  | call f as r =>
      change (rbAtoms ρ args).map (fun xs => RBBind.emit (tmpName c) (.app f xs) true) =
        some _ at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨xs, hxs, heq⟩ := h
      cases heq
      exact rbRhs_rhsVal hrel (.call f as r) args
        (show (rbAtoms ρ args).map (ImpExpr.app f) = some (.app f xs) by rw [hxs]; rfl) hy
  | ilit t v =>
      change (litOfIlit t v).map (fun l => RBBind.inline (.lit l)) = some _ at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨l, -, heq⟩ := h
      cases heq
  | constBit b =>
      change some (RBBind.inline (.lit (.bool b))) = some _ at h
      cases h
  | constUnit =>
      change some (RBBind.inline (.lit .unit)) = some _ at h
      cases h
  | tnilV =>
      change some (RBBind.inline (.tup [])) = some _ at h
      cases h
  | trip t =>
      rcases args with _ | ⟨lo, _ | ⟨hi, _ | _⟩⟩
      change (match ρ lo with
        | .lit (.int lo') =>
            if boundOk lo' t then (ρ hi).atom?.map fun h => RBBind.inline (.trip lo' h) else none
        | _ => none) = some _ at h
      split at h
      · split at h
        · obtain ⟨_, -, heq⟩ := Option.map_eq_some_iff.mp h
          cases heq
        · cases h
      · cases h
  | tconsV h₀ t =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      change (match (ρ a).atom?, ρ b with
        | some x, .tup as => some (RBBind.inline (.tup (x :: as)))
        | _, _ => none) = some _ at h
      split at h
      · cases h
      · cases h
  | _ => cases h

/-- An atom states the value it reads. -/
theorem rhsVal_of_atom {env : Env} {a : ImpExpr} {w : Value} (h : AtomEval env a w) :
    RhsVal bi env a w := by
  cases a with
  | var s => exact h
  | lit l => exact h
  | _ => exact h.elim

/-- **The write-back of the carried names runs.** From a state agreeing with the environment,
    the write-back of the values of the atoms `as` to the distinct names `ns` runs to a state
    agreeing with an environment in which the names hold the values and every other name is
    unchanged, with the exit flag unchanged. -/
theorem nfAssigns_sound
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) :
    ∀ (ns : List String) (as : List ImpExpr), ns.Nodup → ∀ {C : LowCT},
      nfAssigns A ns as = some C → ∀ {env : Env} {ws : List Value} {rs : RustState},
      AtomsEval env as ws → envAgreesT br A env rs →
      ∃ rs' env', RustExec N leafSpec C rs rs' ∧
        rs'.rsScalar exitRetName = rs.rsScalar exitRetName ∧ envAgreesT br A env' rs' ∧
        NamesVals env' ns ws ∧ ∀ m, m ∉ ns → env' m = env m
  | [], [], _, C, h, env, ws, rs, hev, hag => by
      simp only [nfAssigns, Option.some.injEq] at h
      subst h
      cases ws with
      | nil => exact ⟨rs, env, RustExec.skip rs, rfl, hag, trivial, fun _ _ => rfl⟩
      | cons _ _ => exact hev.elim
  | n :: ns, a :: as, hnd, C, h, env, ws, rs, hev, hag => by
      cases ws with
      | nil => exact hev.elim
      | cons w ws =>
      obtain ⟨ha, has⟩ := hev
      have hnd' := List.nodup_cons.mp hnd
      simp only [nfAssigns] at h
      split at h
      · rename_i hv
        obtain ⟨rs', env', hrun, hret, hag', hnv, hfr⟩ :=
          nfAssigns_sound hL ns as hnd'.2 h has hag
        refine ⟨rs', env', hrun, hret, hag', ⟨?_, hnv⟩,
          fun m hm => hfr m (fun h' => hm (List.mem_cons_of_mem _ h'))⟩
        rw [hfr n hnd'.1]
        cases a with
        | var m =>
            simp only [isVarOf, beq_iff_eq] at hv
            subst hv
            exact ha
        | _ => simp [isVarOf] at hv
      · split at h
        · cases h
        · rename_i hv hany
          obtain ⟨hd, hhd, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨C', hC', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rs1, hag1, hret1, hex⟩ :=
            nfHead_sound (N := N) hL hhd (rhsVal_of_atom ha) hag
          have has' : AtomsEval (env.extend n w) as ws := by
            refine AtomsEval.congr (fun m hm => ?_) has
            have hmn : m ≠ n := by
              intro hmn; subst hmn
              exact hany (List.any_eq_true.mpr ⟨_, hm, by simp [isVarOf]⟩)
            exact Env.extend_other _ _ _ _ hmn
          obtain ⟨rs', env', hrun, hret, hag', hnv, hfr⟩ :=
            nfAssigns_sound hL ns as hnd'.2 hC' has' hag1
          refine ⟨rs', env', hex _ _ hrun, hret.trans hret1, hag', ⟨?_, hnv⟩, fun m hm => ?_⟩
          · rw [hfr n hnd'.1, Env.extend_same]
          · simp only [List.mem_cons, not_or] at hm
            rw [hfr m hm.2, Env.extend_other _ _ _ _ hm.1]
  | [], _ :: _, _, _, h, _, _, _, _, _ => by simp [nfAssigns] at h
  | _ :: _, [], _, _, h, _, _, _, _, _ => by simp [nfAssigns] at h

end Heads

/-! ## 3. The loop slots and the names of a reading -/

/-- The trip index of a loop is a reserved name. -/
theorem nfRunName_reserved (c : Nat) : exitReserved (nfRunName c) = true := by
  unfold exitReserved nfRunName
  rw [String.toList_append, List.isPrefixOf_iff_prefix]
  exact List.IsPrefix.trans ⟨"run".toList, by decide⟩ (List.prefix_append _ _)

/-- The trip index of a loop is not the exit flag. -/
theorem nfRunName_ne_ret (c : Nat) : nfRunName c ≠ exitRetName := by
  intro h
  have h9 := congrArg (fun s : String => s.toList.take 9) h
  simp only [nfRunName, exitRetName, String.toList_append] at h9
  rw [List.take_append_of_le_length (by decide)] at h9
  exact absurd h9 (by decide)

/-- Every name of the reading of a context is a name some variable's reading reads. -/
theorem exists_of_mem_allNames : ∀ {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) {n : String},
    n ∈ RBEnv.allNames ρ → ∃ (t : NfTy) (v : Var Γ t), n ∈ (ρ v).names
  | [], _, _, h => by simp [RBEnv.allNames, allVars, hvNames] at h
  | _ :: Γ, ρ, n, h => by
      change n ∈ (ρ .here).names ++ hvNames ρ (shiftVars (allVars Γ)) at h
      rw [hvNames_shiftVars] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨_, .here, h⟩
      · obtain ⟨t, v, hv⟩ := exists_of_mem_allNames (fun v => ρ v.there) h
        exact ⟨t, v.there, hv⟩

/-- A name the reading with the names `ns` made unreadable reads is not one of `ns`. -/
theorem not_mem_of_mem_allNames_clobber {Γ : Ctxt nfDialect} {ρ : RBEnv Γ}
    {ns : List String} {n : String} (h : n ∈ RBEnv.allNames (RBEnv.clobber ns ρ)) : n ∉ ns := by
  obtain ⟨t, v, hv⟩ := exists_of_mem_allNames _ h
  intro hn
  simp only [RBEnv.clobber] at hv
  split at hv
  · simp [RB.names] at hv
  · rename_i hany
    exact hany (List.any_eq_true.mpr ⟨n, hv, by simp [hn]⟩)

/-! ## 4. The lowering simulates the denotation -/

section Low

variable (bi : Builtins) (tf N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers)

/-- The soundness of a lowering continuation for the returned values `out` and the
    postcondition `Post`: from a reading related to an environment agreeing with a state, its
    command runs to a state satisfying `Post` at that environment, with the exit flag
    unchanged. -/
def LKSound {ts : List NfTy} (lk : LK ts) (out : Valuation (d := nfDialect) ts)
    (Post : Env → RustState → Prop) : Prop :=
  ∀ {Δ : Ctxt nfDialect} (ρ' : RBEnv Δ) (vs : HVector (fun t => Var Δ t) ts) (c₁ : Nat)
    (C : LowCT) (c₁' : Nat) (env₁ : Env) (W : Valuation Δ) (rs₁ : RustState),
    lk ρ' vs c₁ = some (C, c₁') → RBRel ρ' env₁ W → envAgreesT br A env₁ rs₁ →
    Expr.lookupArgs vs W = out →
    ∃ rs', RustExec N leafSpec C rs₁ rs' ∧
      rs'.rsScalar exitRetName = rs₁.rsScalar exitRetName ∧ Post env₁ rs'

/-- **The soundness of the lowering** of the program `p`: a denotation of `p` to `out` from a
    valuation related, through an environment, to a state is matched by a run of the lowered
    command to a state satisfying the postcondition of a sound continuation at an environment
    that agrees with the first off the names the command writes, with the exit flag
    unchanged. -/
def LowSound {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ (ρ : RBEnv Γ) (c : Nat) (lk : LK ts) (C : LowCT) (c' : Nat) (Wr : List String),
    nfLow A p ρ c lk = some (C, c', Wr) →
    ∀ (env : Env) (V : Valuation Γ) (rs : RustState) (out : Valuation (d := nfDialect) ts),
    RBRel ρ env V → envAgreesT br A env rs → PDenP bi tf p V = some out →
    ∀ (Post : Env → RustState → Prop), LKSound N leafSpec br A lk out Post →
    ∃ rs' env₁, RustExec N leafSpec C rs rs' ∧
      rs'.rsScalar exitRetName = rs.rsScalar exitRetName ∧ Post env₁ rs' ∧
      ∀ m, m ∉ Wr → env₁ m = env m

/-- `LowSound` of the continuation of a binding, and `True` for every other program. -/
def LowSoundTail {Γ : Ctxt nfDialect} {ts : List NfTy} : NFProg nfDialect Γ ts → Prop
  | .var _ k => LowSound bi tf N leafSpec br A k
  | _ => True

variable {bi tf N leafSpec br A}

/-- **The lowering is sound.** -/
theorem nfLow_sound_aux
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    LowSound bi tf N leafSpec br A p ∧ LowSoundTail bi tf N leafSpec br A p := by
  induction p with
  | ret vs =>
      refine ⟨fun ρ c lk C c' Wr h env V rs out hrel hag hp Post hPost => ?_, trivial⟩
      change (lk ρ vs c).map (fun r => (r.1, r.2, ([] : List String))) = some (C, c', Wr) at h
      obtain ⟨⟨C₁, c₁⟩, hlk, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      change some (Expr.lookupArgs vs V) = some out at hp
      simp only [Option.some.injEq] at hp
      obtain ⟨rs', hex, hret, hpost⟩ := hPost ρ vs c C₁ c₁ env V rs hlk hrel hag hp
      exact ⟨rs', env, hex, hret, hpost, fun _ _ => rfl⟩
  | var e k ih =>
      refine ⟨fun ρ c lk C c' Wr h env V rs out hrel hag hp Post hPost => ?_, ih.1⟩
      obtain ⟨op, rfl, args⟩ := e
      change ((rbBind ρ c op args).bind fun b => match b with
        | .emit n rhs tmp =>
            (nfHead A n rhs).bind fun h =>
              (nfLow A k (RBEnv.cons (.name n) (RBEnv.clobber [n] ρ))
                (if tmp then c + 1 else c) lk).map fun r => (h r.1, r.2.1, n :: r.2.2)
        | .inline r => nfLow A k (RBEnv.cons r ρ) c lk) = some (C, c', Wr) at h
      rcases hb : rbBind ρ c op args with _ | b
      · rw [hb] at h; cases h
      rw [hb, Option.bind_some] at h
      change (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => PDenP bi tf k (V.extend x)) = some out at hp
      rcases hy : nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) with _ | y
      · rw [hy] at hp; cases hp
      rw [hy, Option.bind_some] at hp
      cases b with
      | emit n rhs tmp =>
          dsimp only at h
          obtain ⟨hd, hhd, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨C₁, c₁, Wr₁⟩, h₁, heq⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          obtain ⟨rs1, hag1, hret1, hex⟩ :=
            nfHead_sound (N := N) hL hhd (rbBind_rhsVal hrel c op args hb hy) hag
          have hrel' : RBRel (RBEnv.cons (.name n) (RBEnv.clobber [n] ρ))
              (env.extend n (enc op.ret y)) (V.extend y) :=
            (hrel.clobber_extend n _).cons (Env.extend_same _ _ _)
          obtain ⟨rs', env₁, hrun, hret, hpost, hfr⟩ :=
            ih.1 _ _ lk C₁ c₁ Wr₁ h₁ _ _ rs1 out hrel' hag1 hp Post hPost
          refine ⟨rs', env₁, hex _ _ hrun, hret.trans hret1, hpost, fun m hm => ?_⟩
          simp only [List.mem_cons, not_or] at hm
          rw [hfr m hm.2, Env.extend_other _ _ _ _ hm.1]
      | inline r =>
          have hbs := rbBind_sound bi hrel c op args hb hy
          exact ih.1 _ _ lk C c' Wr h env _ rs out (hrel.cons hbs) hag hp Post hPost
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      refine ⟨fun ρ c lk C c' Wr h env V rs out hrel hag hp Post hPost => ?_, trivial⟩
      cases body with
      | var e rest =>
          have ihr : LowSound bi tf N leafSpec br A rest := ihb.2
          obtain ⟨op, hop, args⟩ := e
          simp only [nfLow] at h
          rcases hc : ctrOf? op args with _ | ⟨i, a, b⟩
          · rw [hc] at h; cases h
          obtain ⟨hr, hctr⟩ := ctrOf?_sound bi hc
          subst hop
          rw [hc, Option.bind_some] at h
          dsimp only at h
          rcases hcount : ρ count with _ | _ | _ | ⟨lo, hi⟩ | _ | _ <;> rw [hcount] at h <;>
            dsimp only at h <;> try cases h
          rcases hhiSE : atomSE A hi with _ | hiSE
          · rw [hhiSE] at h; cases h
          rw [hhiSE, Option.bind_some] at h
          rcases hxs : rbAtoms ρ inits with _ | xs
          · rw [hxs] at h; cases h
          rw [hxs, Option.bind_some] at h
          rcases hcn : namesOf xs with _ | cn
          · rw [hcn] at h; cases h
          rw [hcn, Option.bind_some] at h
          split at h
          case isFalse => cases h
          rename_i hchk
          obtain ⟨hnd, hires, hiA⟩ := hchk
          split at h
          case h_2 => cases h
          rename_i lo' hra hrb
          split at h
          case isFalse => cases h
          rename_i hlo
          obtain ⟨rfl, hlo0⟩ := hlo
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨bC, c₁, WrB⟩, hbody, h⟩ := h
          dsimp only at h
          split at h
          case isFalse => cases h
          rename_i hwr
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨kC, c₂, Wrk⟩, hkr, heq⟩ := h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          -- the denotation of the loop
          have hp' : ((List.range (count.lookup V : BitVec 64).toNat).foldlM
              (fun acc j => PDenP bi tf (NFProg.var ⟨op, rfl, args⟩ rest)
                (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
              (Expr.lookupArgs inits V)).bind (fun acc => PDenP bi tf k (hvAppend acc V)) =
              some out := hp
          rw [Option.bind_eq_some_iff] at hp'
          obtain ⟨accF, hfold, hkout⟩ := hp'
          have hcv : RBOk env (ρ count) (enc (NfTy.word 64) (count.lookup V)) := hrel _ count
          rw [hcount] at hcv
          obtain ⟨hh, ⟨hv, hhv, hrep⟩, hlt, hcenc⟩ := hcv
          have hcnt : (count.lookup V : BitVec 64).toNat = (hh - lo').toNat := by
            change Value.int ((count.lookup V : BitVec 64).toNat : Int) = _ at hcenc
            simp only [Value.int.injEq] at hcenc
            exact_mod_cast hcenc
          rw [hcnt, List.range_eq_range'] at hfold
          -- the trip count of the lowered loop
          obtain ⟨hsv, hdv⟩ := atomSE_eval hag hhiSE hhv
          have hhb : hh < 2 ^ 64 ∧ hiSE.evalState rs = hh.toNat ∧ 0 ≤ hh := by
            rcases hrep with rfl | ⟨W, n, rfl, rfl⟩
            · obtain ⟨h0, h1⟩ := hsv
              simp only [valueToScalar, h0, if_true, Option.some.injEq] at hdv
              exact ⟨h1, hdv.symm, h0⟩
            · have h1 : n < 2 ^ 64 := hsv
              simp only [valueToScalar, Option.some.injEq] at hdv
              exact ⟨by exact_mod_cast h1, by rw [← hdv]; simp, by positivity⟩
          have hbound : (SExpr.SSub hiSE (SExpr.SLit lo'.toNat)).evalState rs =
              (hh - lo').toNat := by
            show hiSE.evalState rs - lo'.toNat = _
            rw [hhb.2.1]; omega
          -- the names of the context the loop keeps
          have hdisj : ∀ n ∈ RBEnv.allNames (RBEnv.clobber cn ρ), n ∉ i :: WrB ∧ n ∉ cn := by
            intro n hn
            refine ⟨?_, not_mem_of_mem_allNames_clobber hn⟩
            have := List.all_eq_true.mp hwr n hn
            simpa using this
          have hrelΓ : ∀ e : Env, (∀ m, m ∉ i :: WrB → m ∉ cn → e m = env m) →
              RBRel (RBEnv.clobber cn ρ) e V := fun e he =>
            (hrel.clobber cn).congr fun n hn => he n (hdisj n hn).1 (hdisj n hn).2
          have hcar0 : NamesVals env cn (encAll cs (Expr.lookupArgs inits V)) :=
            namesOf_vals hcn (rbAtoms_eval hrel inits hxs)
          -- the invariant of the trips
          let Inv : Env → Valuation (d := nfDialect) cs → RustState → Prop := fun e acc s =>
            envAgreesT br A e s ∧ NamesVals e cn (encAll cs acc) ∧
              s.rsScalar exitRetName = rs.rsScalar exitRetName ∧
              ∀ m, m ∉ i :: WrB → m ∉ cn → e m = env m
          let BODY : LowCT := .RSeq (.RScalarSetExpr i
            (.SAdd (.SVar (nfRunName c)) (.SLit lo'.toNat))) bC
          have HS : ∀ (j : Nat) (e : Env) (s : RustState)
              (acc acc' : Valuation (d := nfDialect) cs), j < (hh - lo').toNat → Inv e acc s →
              PDenP bi tf (NFProg.var ⟨op, rfl, args⟩ rest)
                  (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)) =
                some acc' →
              ∃ s' e', RustExec N leafSpec BODY (rsSetScalar s (nfRunName c) j) s' ∧
                Inv e' acc' s' := by
            intro j e s acc acc' hj hinv hpb
            obtain ⟨hagE, hnvE, hretE, hfrE⟩ := hinv
            have hjlt : j < 2 ^ 64 := by omega
            have hag0 : envAgreesT br A e (rsSetScalar s (nfRunName c) j) :=
              envAgreesT_set_reserved j (nfRunName_reserved c) hagE
            have hret0 : (rsSetScalar s (nfRunName c) j).rsScalar exitRetName =
                s.rsScalar exitRetName := by
              rw [rsScalar_rsSetScalar, if_neg (nfRunName_ne_ret c).symm]
            have hzs : ScalarValN (Value.int (lo' + j)) := ⟨by omega, by omega⟩
            have hzd : valueToScalar (Value.int (lo' + j)) =
                some ((SExpr.SAdd (.SVar (nfRunName c)) (.SLit lo'.toNat)).evalState
                  (rsSetScalar s (nfRunName c) j)) := by
              simp only [valueToScalar, SExpr.evalState, rsScalar_rsSetScalar, if_true]
              rw [if_pos (by omega)]
              congr 1
              omega
            have hag1 := envAgreesT_extend hires hiA hzs hzd hag0
            have hret1 := ret_setScalar hires
              ((SExpr.SAdd (.SVar (nfRunName c)) (.SLit lo'.toNat)).evalState
                (rsSetScalar s (nfRunName c) j)) hret0
            have hrelB : RBRel (RBEnv.appNames cs cn (RBEnv.cons .idx
                (RBEnv.dropIdx (RBEnv.clobber cn ρ)))) e
                (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)) :=
              RBRel.appNames (((hrelΓ e hfrE).dropIdx).cons (r := .idx) trivial) cs cn acc hnvE
            change (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args _)).bind
              (fun x => PDenP bi tf rest (Valuation.extend _ x)) = some acc' at hpb
            rw [hctr, Option.bind_some] at hpb
            have ha := hrelB _ a
            beta_reduce at ha
            rw [hra] at ha
            have ha' : a.lookup (hvAppend acc
                (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)) = lo' := by
              change Value.int lo' = Value.int _ at ha
              exact (Value.int.inj ha).symm
            have hb := idx_appNames (RBEnv.clobber cn ρ) V j hjlt cs cn acc b hrb
            have hb' : ((b.lookup (hvAppend acc
                (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)) : BitVec 64).toNat :
                  Int) = j := by
              change Value.int _ = Value.int _ at hb
              exact Value.int.inj hb
            have henc : ∀ {T : NfTy} (h : NfTy.int = T) (z : Int), enc T (h ▸ z) = .int z := by
              intro T h z; subst h; rfl
            have hrel'' := ((hrelB.clobber_extend i (.int (lo' + j))).cons (s := op.ret)
              (r := .name i)
              (x := hr ▸ ((fun (x : Int) (y : BitVec 64) => x + (y.toNat : Int))
                (a.lookup (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
                (b.lookup (hvAppend acc
                  (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))))
              (by
                show (e.extend i (.int (lo' + j))) i = some _
                rw [Env.extend_same, henc hr.symm, ha']
                beta_reduce
                rw [hb']))
            let PostB : Env → RustState → Prop := fun e₁ s' => ∃ e₂, envAgreesT br A e₂ s' ∧
              NamesVals e₂ cn (encAll cs acc') ∧ ∀ m, m ∉ cn → e₂ m = e₁ m
            obtain ⟨s', e₁, hrun, hret', hpost, hfr1⟩ := ihr _ (c + 1) _ bC c₁ WrB hbody _ _ _ acc'
              hrel'' hag1 hpb PostB (by
                intro Δ ρ' vs c₃ C₃ c₃' env₁ W rs₁ hrk hrelW hagW hvs
                change (rbAtoms ρ' vs).bind (fun as => (nfAssigns A cn as).map (·, c₃)) =
                  some (C₃, c₃') at hrk
                rcases has : rbAtoms ρ' vs with _ | as
                · rw [has] at hrk; cases hrk
                rw [has, Option.bind_some, Option.map_eq_some_iff] at hrk
                obtain ⟨C₄, hC₄, heq⟩ := hrk
                cases heq
                have hev := rbAtoms_eval hrelW vs has
                rw [hvs] at hev
                obtain ⟨rs₂, env₂, hrun₂, hret₂, hag₂, hnv₂, hfr₂⟩ :=
                  nfAssigns_sound (N := N) hL cn as hnd hC₄ hev hagW
                exact ⟨rs₂, hrun₂, hret₂, env₂, hag₂, hnv₂, hfr₂⟩)
            obtain ⟨e₂, hag2, hnv2, hfr2⟩ := hpost
            refine ⟨s', e₂, RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hrun,
              hag2, hnv2, ?_, ?_⟩
            · rw [hret', hret1, hretE]
            · intro m hm1 hm2
              have hm1' := hm1
              simp only [List.mem_cons, not_or] at hm1'
              rw [hfr2 m hm2, hfr1 m hm1'.2, Env.extend_other _ _ _ _ hm1'.1, hfrE m hm1 hm2]
          -- the trips
          have key : ∀ m, m ≤ (hh - lo').toNat → ∀ accm,
              (List.range' 0 m).foldlM (fun acc j => PDenP bi tf (NFProg.var ⟨op, rfl, args⟩ rest)
                (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
                (Expr.lookupArgs inits V) = some accm →
              ∃ sm em, RustExec N leafSpec (.RFor (nfRunName c) m BODY) rs sm ∧ Inv em accm sm := by
            intro m
            induction m with
            | zero =>
                intro _ accm h0
                simp only [List.range'_zero, List.foldlM_nil, Option.pure_def,
                  Option.some.injEq] at h0
                subst h0
                exact ⟨rs, env, RustExec.forZero _ _ _, hag, hcar0, rfl, fun _ _ _ => rfl⟩
            | succ m ihm =>
                intro hm accm h1
                rw [List.range'_concat, List.foldlM_append] at h1
                obtain ⟨accm', h2, h3⟩ := Option.bind_eq_some_iff.mp h1
                simp only [List.foldlM_cons, List.foldlM_nil, Nat.zero_add, Nat.one_mul] at h3
                obtain ⟨acc'', h4, h5⟩ := Option.bind_eq_some_iff.mp h3
                simp only [Option.pure_def, Option.some.injEq] at h5
                subst h5
                obtain ⟨sm, em, hexm, hinvm⟩ := ihm (by omega) accm' h2
                obtain ⟨s', e', hb, hinv'⟩ := HS m em sm accm' acc'' (by omega) hinvm h4
                exact ⟨s', e', RustExec.forSucc _ _ _ _ _ _ hexm hb, hinv'⟩
          obtain ⟨sL, eL, hexL, hagL, hnvL, hretL, hfrL⟩ := key _ le_rfl accF hfold
          have hrelK := RBRel.appNames (hrelΓ eL hfrL) cs cn accF hnvL
          obtain ⟨rs', env₁, hrun, hret, hpost, hfr⟩ :=
            ihk.1 _ c₁ lk kC c₂ Wrk hkr eL _ sL out hrelK hagL hkout Post hPost
          refine ⟨rs', env₁, RustExec.seq _ _ _ _ _
            (RustExec.forRuntime _ _ _ _ _ (by rw [hbound]; exact hexL)) hrun,
            hret.trans hretL, hpost, fun m hm => ?_⟩
          have hmk : m ∉ Wrk := fun h' => hm (by simp [h'])
          have hmc : m ∉ cn := fun h' => hm (by simp [h'])
          have hmB : m ∉ i :: WrB := fun h' => hm (by
            rcases List.mem_cons.mp h' with h' | h' <;> simp [h'])
          rw [hfr m hmk, hfrL m hmB hmc]
      | _ => simp [nfLow] at h
  | ifThenElse cond thn els k _ _ _ =>
      refine ⟨fun ρ c lk C c' Wr h => ?_, trivial⟩
      simp [nfLow] at h
  | whileLoop inits body k _ _ =>
      refine ⟨fun ρ c lk C c' Wr h => ?_, trivial⟩
      simp [nfLow] at h
  | call f args k _ =>
      refine ⟨fun ρ c lk C c' Wr h => ?_, trivial⟩
      simp [nfLow] at h

/-- The result agreement of a value without a control-flow tag is the agreement of its
    outcome. -/
theorem outcomeAgreesT_of_resultAgreesT {R : ExitRes} {v : Value} {rs : RustState}
    (hv : v.isControlFlow = false) (h : resultAgreesT br R v rs) :
    outcomeAgreesT br R (.val v) rs := by
  cases v with
  | controlFlow b w => simp [Value.isControlFlow] at hv
  | _ => exact h

/-- **The lowering of a one-result program simulates its denotation.** Under the leaf
    conditions `ExitLeaves` at the placement `A`, if `nfToLowCT A R p ρ = some C`, the
    reading `ρ` relates an environment to the valuation `V`, and the environment agrees
    with the state `rs` under `A`, then a denotation of `p` from `V` to `y` is matched by a
    run of `C` from `rs` to a state whose result slot agrees with the encoding of `y` under
    the result placement `R`. -/
theorem nfToLowCT_sim
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    (R : ExitRes) {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t])
    (ρ : RBEnv Γ) {C : LowCT} (h : nfToLowCT A R p ρ = some C) {env : Env}
    {V : Valuation Γ} {rs : RustState} {y : t.denote} (hrel : RBRel ρ env V)
    (hag : envAgreesT br A env rs) (hp : PDenP bi tf p V = some (.cons y .nil)) :
    ∃ rs', RustExec N leafSpec C rs rs' ∧ outcomeAgreesT br R (.val (enc t y)) rs' := by
  unfold nfToLowCT at h
  obtain ⟨⟨C₀, c', Wr⟩, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rs', -, hex, -, hpost, -⟩ := (nfLow_sound_aux (tf := tf) (N := N) hL p).1 ρ 0 _
    C₀ c' Wr h₀ env V rs _ hrel hag hp (fun _ rs' => outcomeAgreesT br R (.val (enc t y)) rs')
    (by
      intro Δ ρ' vs c₁ C₁ c₁' env₁ W rs₁ hlk hrelW hagW hvs
      obtain ⟨v, rfl⟩ : ∃ v, vs = .cons v .nil := by
        rcases vs with _ | ⟨v, _ | _⟩; exact ⟨v, rfl⟩
      change (nfResult A R (ρ' v)).map (·, c₁) = some (C₁, c₁') at hlk
      obtain ⟨C₂, hres, heq⟩ := Option.map_eq_some_iff.mp hlk
      cases heq
      have hy : v.lookup W = y := by
        change HVector.cons (v.lookup W) .nil = _ at hvs
        cases hvs; rfl
      subst hy
      have hok := hrelW t v
      beta_reduce at hok
      rcases hρv : ρ' v with _ | _ | _ | _ | _ | _ <;> rw [hρv] at hres hok <;>
        try (simp [nfResult] at hres; done)
      rename_i x
      simp only [nfResult] at hres
      split at hres
      · rename_i hc
        obtain ⟨hxr, hR⟩ := hc
        change env₁ x = some (enc t (v.lookup W)) at hok
        have hcf := envAgreesT_not_cf hagW hxr hok
        rcases hA : A.lookup x with _ | t'
        · rw [hA] at hR
          subst hR
          simp only [resultStoreT, hA, resultStore, storeScalar, Option.some.injEq] at hres
          subst hres
          obtain ⟨-, hdec⟩ := envAgreesT_scalar hagW hxr hA hok
          refine ⟨_, RustExec.scalarSetExpr _ _ rs₁, ?_, outcomeAgreesT_of_resultAgreesT hcf ?_⟩
          · rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_res]
          · show valueToScalar _ = some _
            rw [hdec, rsScalar_rsSetScalar, if_pos rfl]
            rfl
        · rw [hA] at hR
          subst hR
          simp only [resultStoreT, hA, Option.some.injEq] at hres
          subst hres
          obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hagW hxr hA hok
          exact ⟨rsSetTower rs₁ exitResName ⟨t', val⟩,
            RustExec.copy ⟨exitResName, t'⟩ ⟨x, t'⟩ rs₁ rfl val
              (locatedLookup_of_rsTower rs₁ x t' val hval'), rfl,
            outcomeAgreesT_of_resultAgreesT hcf
              ⟨val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _, hbr⟩⟩
      · cases hres)
  exact ⟨rs', hex, hpost⟩

end Low

end CatCrypt.Crypto.Hax.NFToLowCT
