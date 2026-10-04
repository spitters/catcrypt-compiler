/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops

/-!
# Lowering the counted-loop fragment of `NFProg catCryptDialect` to `ComL`

`nfToComL` maps an `NFProg catCryptDialect` program with one result, built from
let-bindings, a return and counted loops carrying one value, to a `ComL` program: a
return to `ComL.ret`, a let-binding through `toJExprD`, and a `forLoop` with one
carried value whose body is straight-line (`NFProg.toCom?`) to `ComL.forLoopNRt`, with
its body through `cryptoDialectToJasminCom`, its count and seed variables through
`toJVarD`, and as the invariants the outer variables the body reads (`usedSel`), each once,
in decreasing index. The body is restricted to those variables by `comRestrict`. The trip
counter `CryptoTy.sword 64` maps to `JasminTy.reg 64`, so the restricted body context
`acc :: .sword 64 :: Γ'` maps to the `forLoopNRt` body context
`mapTy acc :: .reg 64 :: Γ'.map mapTy`. Every other program is `none`.

`nfToComL_denote` is the preservation square of
`DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq'`, lifted to loops: the
source program denotes `some` of one value, and the lowered program on the
transported valuation `ctMapValD V` denotes `ctTransTy` of that value.

## Main definitions

* `comToComL` — the embedding of `Com jasminDialect` into `ComL`.
* `VMap`, `comRestrict`, `findIn`, `usedSel` — partial maps of variables, the restriction of
  a program along one, the map onto a selection of variables, and the outer variables a loop
  body reads.
* `nfToComLAt`, `nfToComL` — the lowering.

## Main results

* `comToComL_denote` — the embedding preserves denotation.
* `comRestrict_denote`, `findIn_agree` — the restriction keeps the denotation at related
  valuations; a selection relates a valuation to the values it selects.
* `lookupArgs_toJArgsD_ctMapValD` — the lowered argument variables read the
  transported values.
* `foldl_stepC_ctTransTy` — a lowered loop body folds the transported accumulator
  to the transported source fold.
* `nfToComLAt_denote`, `nfToComL_denote` — the lowering preserves denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-! ## 1. `Com jasminDialect` inside `ComL` -/

/-- The straight-line jasmin program as a `ComL` program with no loop node. -/
def comToComL : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → ComL Γ t
  | _, _, .ret v => .ret v
  | _, _, .var e body => .var e (comToComL body)

/-- `comToComL` preserves denotation. -/
theorem comToComL_denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (comToComL c).denote V = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V => comToComL_denote body (V.extend (e.denote V))

/-! ## 2. The restriction of a program to a selection of variables -/

section Restrict

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty]

/-- The de Bruijn index of a variable. -/
def vIdx : {Γ : Ctxt d} → {t : d.Ty} → Ctxt.Var Γ t → Nat
  | _, _, .here => 0
  | _, _, .there v => vIdx v + 1

omit [DialectSignature d] [TyDenote d.Ty] in
/-- Two variables of the same type and index are equal. -/
theorem var_eq_of_vIdx : {Γ : Ctxt d} → {t : d.Ty} → (v w : Ctxt.Var Γ t) →
    vIdx v = vIdx w → v = w
  | _, _, .here, .here, _ => rfl
  | _, _, .there v, .there w, h => by
      rw [var_eq_of_vIdx v w (by simpa [vIdx] using h)]
  | _, _, .here, .there _, h => by simp [vIdx] at h
  | _, _, .there _, .here, h => by simp [vIdx] at h

/-- A partial map of the variables of `Γ` to variables of `Γ'`. -/
abbrev VMap (Γ Γ' : Ctxt d) : Type := ∀ {t : d.Ty}, Ctxt.Var Γ t → Option (Ctxt.Var Γ' t)

/-- The map under one more binding of both contexts. -/
def VMap.lift {Γ Γ' : Ctxt d} {s : d.Ty} (f : VMap Γ Γ') : VMap (s :: Γ) (s :: Γ')
  | _, .here => some .here
  | _, .there v => (f v).map .there

/-- The map on a vector of variables. -/
def VMap.args {Γ Γ' : Ctxt d} (f : VMap Γ Γ') : {ts : List d.Ty} →
    HVector (fun t => Ctxt.Var Γ t) ts → Option (HVector (fun t => Ctxt.Var Γ' t) ts)
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (f v).bind fun w => (VMap.args f vs).map (.cons w)

/-- The map `f` reads in `V'` what its arguments read in `V`. -/
def VMap.Agree {Γ Γ' : Ctxt d} (f : VMap Γ Γ') (V : Ctxt.Valuation Γ)
    (V' : Ctxt.Valuation Γ') : Prop :=
  ∀ (t : d.Ty) (v : Ctxt.Var Γ t) (w : Ctxt.Var Γ' t), f v = some w → w.lookup V' = v.lookup V

omit [DialectSignature d] in
theorem VMap.agree_lift {Γ Γ' : Ctxt d} {s : d.Ty} {f : VMap Γ Γ'} {V : Ctxt.Valuation Γ}
    {V' : Ctxt.Valuation Γ'} (h : VMap.Agree f V V') (x : ⟦s⟧) :
    VMap.Agree (VMap.lift (s := s) f) (V.extend x) (V'.extend x) := by
  intro t v w hw
  cases v with
  | here =>
      cases hw
      rfl
  | there v =>
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hw
      exact h t v w' hw'

omit [DialectSignature d] in
theorem VMap.lookupArgs_args {Γ Γ' : Ctxt d} {f : VMap Γ Γ'} {V : Ctxt.Valuation Γ}
    {V' : Ctxt.Valuation Γ'} (h : VMap.Agree f V V') :
    ∀ {ts : List d.Ty} (vs : HVector (fun t => Ctxt.Var Γ t) ts)
      (ws : HVector (fun t => Ctxt.Var Γ' t) ts), VMap.args f vs = some ws →
      Expr.lookupArgs ws V' = Expr.lookupArgs vs V
  | [], .nil, ws, hw => by
      cases hw
      rfl
  | _ :: _, .cons v vs, ws, hw => by
      obtain ⟨w, hw1, hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨ws', hws', rfl⟩ := Option.map_eq_some_iff.mp hw
      change HVector.cons (w.lookup V') (Expr.lookupArgs ws' V') =
        HVector.cons (v.lookup V) (Expr.lookupArgs vs V)
      rw [h _ v w hw1, VMap.lookupArgs_args h vs ws' hws']

/-- **The restriction of a program** along `f`: every variable it reads mapped by `f`, or
    `none` when one is outside the domain of `f`. -/
def comRestrict : {Γ Γ' : Ctxt d} → {u : d.Ty} → Com d Γ u → VMap Γ Γ' →
    Option (Com d Γ' u)
  | _, _, _, .ret v, f => (f v).map .ret
  | _, _, _, .var e k, f =>
      (VMap.args f e.args).bind fun as =>
        (comRestrict k (VMap.lift f)).map fun k' => .var ⟨e.op, e.retTy_eq, as⟩ k'

/-- **The restriction keeps the denotation** at valuations the map relates. -/
theorem comRestrict_denote [DialectDenote d] : {Γ Γ' : Ctxt d} → {u : d.Ty} →
    (c : Com d Γ u) → (f : VMap Γ Γ') → (c' : Com d Γ' u) → comRestrict c f = some c' →
    (V : Ctxt.Valuation Γ) → (V' : Ctxt.Valuation Γ') → VMap.Agree f V V' →
    c'.denote V' = c.denote V
  | _, _, _, .ret v, f, c', h, V, V', hag => by
      obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      exact hag _ v w hw
  | _, _, _, .var e k, f, c', h, V, V', hag => by
      obtain ⟨as, has, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have he : (⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V' = e.denote V := by
        unfold Expr.denote
        rw [VMap.lookupArgs_args hag e.args as has]
      change k'.denote (V'.extend ((⟨e.op, e.retTy_eq, as⟩ : Expr d _ _).denote V')) =
        k.denote (V.extend (e.denote V))
      rw [he]
      exact comRestrict_denote k (VMap.lift f) k' hk' _ _ (VMap.agree_lift hag _)

variable [DecidableEq d.Ty]

/-- The variable of `Γ'` at which the selection `sel` reads the variable `v`. -/
def findIn {Γ : Ctxt d} : {Γ' : Ctxt d} → HVector (fun t => Ctxt.Var Γ t) Γ' →
    VMap Γ Γ'
  | [], .nil, _, _ => none
  | s :: _, .cons w ws, t, v =>
      if h : s = t then
        if vIdx (h ▸ w) = vIdx v then some (h ▸ .here) else (findIn ws v).map .there
      else (findIn ws v).map .there

omit [DialectSignature d] in
/-- The selection `sel` reads, at the variable `findIn` gives, what `v` reads. -/
theorem findIn_agree {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    {Γ' : Ctxt d} → (sel : HVector (fun t => Ctxt.Var Γ t) Γ') →
      VMap.Agree (findIn sel) V (Expr.lookupArgs sel V)
  | [], .nil => fun _ _ _ h => by cases h
  | s :: _, .cons u us => by
      intro t v w h
      change findIn (HVector.cons u us) (t := t) v = some w at h
      rw [findIn.eq_2] at h
      split at h
      · rename_i hst
        subst hst
        split at h
        · rename_i hi
          cases h
          obtain rfl := var_eq_of_vIdx u v hi
          rfl
        · obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          exact findIn_agree V us _ v w' hw'
      · obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        exact findIn_agree V us t v w' hw'

/-- The indices of a vector of variables. -/
def argIdxs {Γ : Ctxt d} : {ts : List d.Ty} → HVector (fun t => Ctxt.Var Γ t) ts → List Nat
  | [], .nil => []
  | _ :: _, .cons v vs => vIdx v :: argIdxs vs

/-- The indices of the variables of `Γ` a program reads. -/
def comIdx : {Γ : Ctxt d} → {u : d.Ty} → Com d Γ u → List Nat
  | _, _, .ret v => [vIdx v]
  | _, _, .var e k =>
      argIdxs e.args ++ (comIdx k).filterMap fun i => if i = 0 then none else some (i - 1)

/-- The variable of `Γ` at the index `i`. -/
def varAt : (Γ : Ctxt d) → Nat → Option (Σ t : d.Ty, Ctxt.Var Γ t)
  | [], _ => none
  | t :: _, 0 => some ⟨t, .here⟩
  | _ :: Γ, i + 1 => (varAt Γ i).map fun p => ⟨p.1, .there p.2⟩

/-- The selection of the variables of `Γ` at the indices `is`. -/
def selOf (Γ : Ctxt d) : List Nat → Σ Γ' : Ctxt d, HVector (fun t => Ctxt.Var Γ t) Γ'
  | [] => ⟨[], .nil⟩
  | i :: is =>
      match varAt Γ i with
      | some p => ⟨p.1 :: (selOf Γ is).1, .cons p.2 (selOf Γ is).2⟩
      | none => selOf Γ is

/-- **The outer variables a loop body reads**, over the accumulator and the index: each once,
    in decreasing index, which is the order of the parameters of a layout. -/
def usedSel {Γ : Ctxt d} {a b u : d.Ty} (c : Com d (a :: b :: Γ) u) :
    Σ Γ' : Ctxt d, HVector (fun t => Ctxt.Var Γ t) Γ' :=
  selOf Γ ((((comIdx c).filterMap fun i => if i < 2 then none else some (i - 2)).eraseDups
    ).mergeSort fun i j => decide (j ≤ i))

end Restrict

/-! ## 3. The lowering -/

/-- The `ComL.forLoopNRt` node of a counted loop carrying the tuple `cs`, with the
    lowered continuation `k'`: `none` unless `cs` is one type, the body is
    straight-line (`NFProg.toCom?`) and `cryptoDialectToJasminCom` lowers it. -/
def forNode {Γ : Ctx} {t : CryptoTy} : {cs : List CryptoTy} →
    Ctxt.Var Γ (HasWord64.word (d := catCryptDialect)) →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) cs →
    NFProg catCryptDialect (cs ++ HasWord64.word (d := catCryptDialect) :: Γ) cs →
    ComL (mapCtx (cs ++ Γ)) (mapTy t) → Option (ComL (mapCtx Γ) (mapTy t))
  | [], _, .nil, _, _ => none
  | [_], count, .cons init .nil, body, k' =>
      body.toCom?.bind fun bc =>
        (comRestrict bc (VMap.lift (VMap.lift (findIn (usedSel bc).2)))).bind fun bc' =>
          (cryptoDialectToJasminCom bc').map fun jb =>
            ComL.forLoopNRt (invTys := (usedSel bc).1.map mapTy) jb (toJVarD count)
              (toJVarD init) (toJArgsD (usedSel bc).2) k'
  | _ :: _ :: _, _, .cons _ (.cons _ _), _, _ => none

/-- Lower an `NFProg catCryptDialect` program with the one result `t` (`ts = [t]`) to
    `ComL`. `none` on a branch, an exit-flag loop, a call, a counted loop carrying other than
    one value or with a body that is not straight-line, and when a bound expression or
    a loop body falls outside the fragment `cryptoDialectToJasminCom` lowers. -/
def nfToComLAt : {Γ : Ctx} → {ts : List CryptoTy} → NFProg catCryptDialect Γ ts →
    (t : CryptoTy) → ts = [t] → Option (ComL (mapCtx Γ) (mapTy t))
  | _, _, .ret vs, _, h => by
      subst h
      exact match vs with
        | .cons v .nil => some (.ret (toJVarD v))
  | _, _, .var e k, t, h =>
      (toJExprD e).bind fun e' => (nfToComLAt k t h).map fun k' => .var e' k'
  | _, _, .forLoop count inits body k, t, h =>
      (nfToComLAt k t h).bind (forNode count inits body)
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop .., _, _ => none
  | _, _, .call .., _, _ => none

/-- Lower an `NFProg catCryptDialect` program with one result to `ComL`
    (`nfToComLAt` at `ts = [t]`). -/
def nfToComL {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t]) :
    Option (ComL (mapCtx Γ) (mapTy t)) :=
  nfToComLAt p t rfl

/-! ## 3. Transport lemmas -/

/-- The lowered argument variables, looked up in the transported valuation, are the
    transported argument values. -/
theorem lookupArgs_toJArgsD_ctMapValD {Γ : Ctx} :
    {tys : List CryptoTy} →
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    Expr.lookupArgs (toJArgsD args) (ctMapValD V) = ctMapValD (Expr.lookupArgs args V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((toJVarD v).lookup (ctMapValD V))
        (Expr.lookupArgs (toJArgsD rest) (ctMapValD V)) = _
      rw [ctMapValD_lookup, lookupArgs_toJArgsD_ctMapValD rest V]
      rfl

/-- A lowered loop body, folded over any list of trip indices from the transported
    accumulator, gives the transported fold of the source body. -/
theorem foldl_stepC_ctTransTy {acc : CryptoTy} {invTys : Ctx}
    (body : Com catCryptDialect (acc :: .sword 64 :: invTys) acc)
    (jb : Com jasminDialect (mapTy acc :: .reg 64 :: invTys.map mapTy) (mapTy acc))
    (hb : cryptoDialectToJasminCom body = some jb)
    (W : Ctxt.Valuation (d := catCryptDialect) invTys) :
    (L : List Nat) → (a : CryptoTy.denote acc) →
    L.foldl (fun x t => JLoopBodyN.stepC jb (ctMapValD W) t x) (ctTransTy a) =
      ctTransTy (L.foldl
        (fun x t => body.denote (.cons x (.cons (BitVec.ofNat 64 t) W))) a)
  | [], _ => rfl
  | t :: L, a => by
      simp only [List.foldl_cons]
      have hstep : JLoopBodyN.stepC jb (ctMapValD W) t (ctTransTy a) =
          ctTransTy (body.denote (.cons a (.cons (BitVec.ofNat 64 t) W))) :=
        cryptoDialectToJasminCom_denote_eq' body
          (.cons a (.cons (BitVec.ofNat 64 t) W)) jb hb
      rw [hstep]
      exact foldl_stepC_ctTransTy body jb hb W L _

/-! ## 4. Preservation -/

/-- **Preservation.** When `nfToComLAt p t h = some jcom`, the source program denotes
    `some` of one value `x`, at every fuel, and the lowered program on the transported
    valuation denotes `ctTransTy x`. -/
theorem nfToComLAt_denote {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts)
    (t : CryptoTy) (h : ts = [t]) (jcom : ComL (mapCtx Γ) (mapTy t))
    (hj : nfToComLAt p t h = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (h ▸ .cons x .nil) ∧
      jcom.denote (ctMapValD V) = ctTransTy x := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      have hr : nfToComLAt (.ret (.cons v .nil)) t rfl = some (.ret (toJVarD v)) := rfl
      rw [hr, Option.some.injEq] at hj
      subst hj
      exact ⟨v.lookup V, rfl, ctMapValD_lookup v V⟩
  | var e k ih =>
      subst h
      simp only [nfToComLAt] at hj
      rcases he : toJExprD e with _ | e'
      · rw [he] at hj; cases hj
      rcases hk : nfToComLAt k t rfl with _ | k'
      · rw [he, hk] at hj; cases hj
      rw [he, hk] at hj
      cases hj
      obtain ⟨x, hx, hx'⟩ := ih rfl k' hk (V.extend (e.denote V))
      refine ⟨x, ?_, ?_⟩
      · simp only [NFProg.denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind,
          Option.bind_some]
        exact hx
      · show k'.denote ((ctMapValD V).extend (e'.denote (ctMapValD V))) = _
        rw [dialectJasminLeafAgrees_holds e V e' he, ← ctMapValD_extend V (e.denote V)]
        exact hx'
  | forLoop count inits body k _ ihk =>
      simp only [nfToComLAt] at hj
      rcases hk : nfToComLAt k t h with _ | k'
      · rw [hk] at hj; cases hj
      rw [hk, Option.bind_some] at hj
      rcases inits with _ | ⟨init, _ | _⟩
      · simp [forNode] at hj
      · simp only [forNode] at hj
        rcases hbc : body.toCom? with _ | bc
        · rw [hbc] at hj; cases hj
        rcases hr : comRestrict bc (VMap.lift (VMap.lift (findIn (usedSel bc).2))) with _ | bc'
        · rw [hbc, Option.bind_some, hr] at hj; cases hj
        rcases hb : cryptoDialectToJasminCom bc' with _ | jb
        · rw [hbc, Option.bind_some, hr, Option.bind_some, hb] at hj; cases hj
        rw [hbc, Option.bind_some, hr, Option.bind_some, hb, Option.map_some,
          Option.some.injEq] at hj
        subst hj
        have hsel : ∀ (a : CryptoTy.denote _) (i : Nat),
            bc'.denote (.cons a (.cons (BitVec.ofNat 64 i) (Expr.lookupArgs (usedSel bc).2 V))) =
              bc.denote (.cons a (.cons (BitVec.ofNat 64 i) V)) := fun a i =>
          comRestrict_denote bc _ bc' hr _ _
            (VMap.agree_lift (VMap.agree_lift (findIn_agree V (usedSel bc).2) _) _)
        have hfold := NFProg.foldlM_single (d := catCryptDialect)
          (fun acc i => body.denote fuel
            (MultiBlockLowering.hvAppend acc (.cons (HasWord64.ofNat (d := catCryptDialect) i) V)))
          (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) V)))
          (fun a i => NFProg.denote_of_toCom? body hbc fuel _)
          (List.range (count.lookup V).toNat) (init.lookup V)
        obtain ⟨x, hx, hx'⟩ := ihk h k' hk
          (V.extend ((List.range (count.lookup V).toNat).foldl
            (fun a i => bc.denote (.cons a (.cons (BitVec.ofNat 64 i) V))) (init.lookup V)))
        refine ⟨x, ?_, ?_⟩
        · rw [NFProg.denote_forLoop]
          exact (congrArg (· >>= _) hfold).trans hx
        · show k'.denote ((ctMapValD V).extend
            ((List.range ((toJVarD count).lookup (ctMapValD V)).toNat).foldl
              (fun x t => JLoopBodyN.stepC jb
                (Expr.lookupArgs (toJArgsD (usedSel bc).2) (ctMapValD V)) t x)
              ((toJVarD init).lookup (ctMapValD V)))) = _
          rw [lookupArgs_toJArgsD_ctMapValD, ctMapValD_lookup, ctMapValD_lookup,
            foldl_stepC_ctTransTy bc' jb hb (Expr.lookupArgs (usedSel bc).2 V)]
          simp only [hsel]
          rw [← ctMapValD_extend]
          exact hx'
      · simp [forNode] at hj
  | ifThenElse => simp [nfToComLAt] at hj
  | whileLoop => simp [nfToComLAt] at hj
  | call => simp [nfToComLAt] at hj

/-- **Preservation** for a program with one result: when `nfToComL p = some jcom`, the
    source program denotes `some` of one value `x`, at every fuel, and the lowered
    program on the transported valuation denotes `ctTransTy x`. -/
theorem nfToComL_denote {Γ : Ctx} {t : CryptoTy} (p : NFProg catCryptDialect Γ [t])
    (jcom : ComL (mapCtx Γ) (mapTy t)) (hj : nfToComL p = some jcom) (fuel : Nat)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    ∃ x : CryptoTy.denote t, p.denote fuel V = some (.cons x .nil) ∧
      jcom.denote (ctMapValD V) = ctTransTy x :=
  nfToComLAt_denote p t rfl jcom hj fuel V

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
