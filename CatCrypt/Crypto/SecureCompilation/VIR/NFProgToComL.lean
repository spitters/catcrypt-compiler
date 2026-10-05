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
# Variable restriction for the lowering of counted loops to `ComL`

The lowering of the counted-loop fragment of `NFProg` to `ComL`
(`NFProgCatToJasmin.nfToComLVia`) passes a loop body only the outer variables it reads.
This module holds the machinery for that restriction: partial maps of variables (`VMap`),
the restriction of a program along one (`comRestrict`), the map onto a selection of
variables (`findIn`), and the outer variables a loop body reads (`usedSel`), each once, in
decreasing index. It also holds the embedding `comToComL` of straight-line jasmin programs
into `ComL`.

## Main definitions

* `comToComL` — the embedding of `Com jasminDialect` into `ComL`.
* `VMap`, `comRestrict`, `findIn`, `usedSel` — partial maps of variables, the restriction of
  a program along one, the map onto a selection of variables, and the outer variables a loop
  body reads.

## Main results

* `comToComL_denote` — the embedding preserves denotation.
* `comRestrict_denote`, `findIn_agree` — the restriction keeps the denotation at related
  valuations; a selection relates a valuation to the values it selects.
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

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
