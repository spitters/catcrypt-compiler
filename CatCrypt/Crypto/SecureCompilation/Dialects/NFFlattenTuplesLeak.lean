/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak

/-!
# The leakage of tuple flattening

`NFFlattenTuples.flattenTuples` deletes the bindings of the tuple operations and keeps every
other binding with the same arguments, the trip counts of the counted loops, the conditions of
the branches and the flags of the exit-flag loops. Under a leakage model in which every tuple
operation is quiet, a program the pass returns runs, at a valuation related to the flattened
source valuation, to the flattened results and to the events of the source run
(`flatProg_leakRunM`): the leakage transformer is the identity.

## Main definitions

* `TupleQuiet` — every tuple operation is quiet in a leakage model.

## Main results

* `flatProg_leakRunM` — at valuations related by the renaming, a program `flatProg` returns
  runs to the flattened results and to the events of the source run.
* `flattenTuples_leakRunM` — the statement at the identity renaming and the flattened
  valuation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind Expr.ctLeak opLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-- Every tuple operation, also under `named`, is quiet in the leakage model `M`. -/
def TupleQuiet (M : LeakModel nfDialect) : Prop :=
  ∀ op : NfOp, opIsTuple op = true → M.kind op = .quiet

/-- **The leakage transformer of tuple flattening is the identity.** Under `TupleQuiet M`, a
    program that `flatProg` returns at a renaming `ren` relating `W` to the flattened `V`
    runs at `W`, at every leaf table and fuel, to the flattened results and to the events of
    the source run at `V`. -/
theorem flatProg_leakRunM (M : LeakModel nfDialect) (hM : TupleQuiet M) (T : NfLeafTable)
    (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ)
      (q : NFProg nfDialect Δ (flatCtx ts)), flatProg p ren = some q →
    ∀ (V : Valuation Γ) (W : Valuation Δ), pullV ren W = flatV V →
    @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel Δ _ q W =
      (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel Γ ts p V).map
        fun r => (flatV r.1, r.2) := by
  induction p with
  | ret vs =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      have h2 := Option.some.inj hq
      subst h2
      exact congrArg (fun x => some (x, [])) (lookupArgs_flatArgs ren V W hW vs)
  | var e k ih =>
      obtain ⟨op, rfl, args⟩ := e
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      cases hT : tupleHom? ren op args with
      | some R =>
          simp only [hT] at hq
          obtain ⟨x, hx, hR⟩ := tupleHom?_spec ren V W hW T op args R hT
          have hq0 : opLeak M op (Expr.lookupArgs args V) = [] := by
            unfold opLeak
            rw [hM op (by
              cases h : opIsTuple op with
              | true => rfl
              | false => rw [tupleHom?_eq_none ren op args h] at hT; cases hT)]
          show _ = (Option.bind (nfDenoteOp T op (Expr.lookupArgs args V)) _).map _
          rw [hx, Option.bind_some, ih (appendHom R ren) q hq (V.extend x) W
            (pullV_appendHom_flat ren V W hW R x hR), Option.map_map]
          show _ = Option.map _ _
          congr 1
          funext r
          show _ = (flatV r.1, opLeak M op (Expr.lookupArgs args V) ++ r.2)
          rw [hq0]
          rfl
      | none =>
          simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨args', ha, R, hR, k', hk, rfl⟩ := hq
          have hargs := atomArgs?_spec ren V W hW args args' ha
          show Option.bind (nfDenoteOp T op (Expr.lookupArgs args' W)) _ =
            (Option.bind (nfDenoteOp T op (Expr.lookupArgs args V)) _).map _
          rw [hargs]
          cases nfDenoteOp T op (Expr.lookupArgs args V) with
          | none => rfl
          | some x =>
            rw [Option.bind_some, Option.bind_some,
              ih _ k' hk (V.extend x) (W.extend x)
                (pullV_appendHom_flat _ V _ (pullV_there_flat ren V W hW x) R x
                  (atomRet?_spec op.ret R hR x W)),
              Option.map_map, Option.map_map]
            show Option.map _ _ = Option.map _ _
            congr 1
            funext r
            show (flatV r.1, opLeak M op (Expr.lookupArgs args' W) ++ r.2) =
              (flatV r.1, opLeak M op (Expr.lookupArgs args V) ++ r.2)
            rw [hargs]
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      have hc : (ren (varHom flatTy count .here)).lookup W = count.lookup V :=
        (lookup_varRen ren V W hW count .here).trans rfl
      simp only [NFProg.leakRunM]
      rw [hc, lookupArgs_flatArgs ren V W hW inits,
        NFProg.forIterLeak_transport _ _ flatV (fun i acc => ihb _ body' hb
          (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V))
          (hvAppend (flatV acc) (.cons (HasWord64.ofNat (d := nfDialect) i) W))
          (pullV_appRen _ (.cons (HasWord64.ofNat (d := nfDialect) i) V)
            (.cons (HasWord64.ofNat (d := nfDialect) i) W)
            (pullV_appendHom_flat (t := NfTy.word 64) (Δ := NfTy.word 64 :: Δ) _ V _
              (pullV_there_flat ren V W hW _)
              (fun w => inlHom (d := nfDialect) (xs := [NfTy.word 64]) Δ w) _ rfl)
            _ acc))]
      refine NFProg.bind_map_comm _ _ _ _ _ (fun r => ?_)
      rw [ihk _ k' hk (hvAppend r.1 V) (hvAppend (flatV r.1) W)
        (pullV_appRen ren V W hW _ r.1), Option.map_map, Option.map_map]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨thn', ht, els', he, k', hk, rfl⟩ := hq
      have hc : (ren (varHom flatTy cond .here)).lookup W = cond.lookup V :=
        (lookup_varRen ren V W hW cond .here).trans rfl
      simp only [NFProg.leakRunM]
      rw [hc]
      have harm : (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
            then @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ thn' W
            else @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ els' W) =
          (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
            then @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ thn V
            else @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ els V).map
              fun r => (flatV r.1, r.2) := by
        split
        · exact iht ren thn' ht V W hW
        · exact ihe ren els' he V W hW
      rw [harm]
      refine NFProg.bind_map_comm _ _ _ _ _ (fun r => ?_)
      rw [ihk _ k' hk (hvAppend r.1 V) (hvAppend (flatV r.1) W)
        (pullV_appRen ren V W hW _ r.1), Option.map_map, Option.map_map]
      rfl
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      simp only [NFProg.leakRunM]
      rw [lookupArgs_flatArgs ren V W hW inits,
        NFProg.whileIterLeak_transport
          (fun acc => @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ body
            (hvAppend acc V)) _ flatV id (fun _ => rfl) (fun a => by
          refine (ihb _ body' hb (hvAppend a V) (hvAppend (flatV a) W)
            (pullV_appRen ren V W hW _ a)).trans ?_
          congr 1
          funext r
          obtain ⟨r1, ev⟩ := r
          cases r1
          rfl)]
      refine NFProg.bind_map_comm _ _ _ _ _ (fun r => ?_)
      rw [ihk _ k' hk (hvAppend r.1 V) (hvAppend (flatV r.1) W)
        (pullV_appRen ren V W hW _ r.1), Option.map_map, Option.map_map]
      rfl
  | call f args k _ =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.map_eq_some_iff] at hq
      obtain ⟨k', _, rfl⟩ := hq
      rfl

/-- **The leakage of `flattenTuples`.** Under `TupleQuiet M`, a program `flattenTuples p`
    runs at the flattened valuation of `V`, at every leaf table and fuel, to the flattened
    results and to the events of the run of `p` at `V`. -/
theorem flattenTuples_leakRunM (M : LeakModel nfDialect) (hM : TupleQuiet M)
    (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) {q : NFProg nfDialect (flatCtx Γ) (flatCtx ts)}
    (hq : flattenTuples p = some q) (V : Valuation Γ) :
    @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel _ _ q (flatV V) =
      (@NFProg.leakRunM nfDialect _ _ _ _ (nfDenote T) M fuel Γ ts p V).map
        fun r => (flatV r.1, r.2) :=
  flatProg_leakRunM M hM T fuel p _ q hq V (flatV V) (pullV_id_flat V)

end CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
