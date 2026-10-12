/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapMulti
public import CatCrypt.Crypto.SecureCompilation.VIR.NFDialect

/-!
# Tuple flattening on structured programs of the normal form

`flattenTuples` replaces every tuple of a program of `NFProg nfDialect` by its components.
The type map `flatTy` sends the empty tuple `tnil` to no type, a tuple `tcons h t` to the
components of `h` followed by those of `t`, and every other type `s` to `[s]`. A context
`Γ` goes to `flatCtx Γ`, the flattening `ctxFlat flatTy Γ` of `VIR/MultiBlockLowering.lean`,
and a value to its components (`flatEnc`; `flatV` on valuations).

The pass `flatProg` threads a renaming `ren : Ctxt.Hom (flatCtx Γ) Δ` from the flattened
source context into the target context, as `NFProg.mapM` (`VIR/NFProgMapMulti.lean`) does:

* a binding of a tuple operation (`tnilV`, `tconsV`, `thead`, `ttail`, also under `named`)
  emits no code: the components of its result are variables of the components of its
  arguments (`tupleHom?`);
* a binding of another operation is kept when no argument type and not the result type is
  a tuple (`atomArgs?`, `atomRet?`), and refused otherwise;
* a return, and the carried tuple and the results of a counted loop, a branch, an exit-flag
  loop and a call, are flattened: a node carrying `cs` carries `flatCtx cs`, and the region
  over `cs ++ Γ` runs over `flatCtx cs ++ Δ` at the renaming `NFProg.appHomM flatTy cs ren`.

Every target context is built from `ctxFlat`, `++` and `::`, so the pass stays within the
intrinsic typing of `NFProg` without a cast along a context equation.

The denotation of `nfDialect` is `Option`-valued, so `NFProg.mapM`, whose blocks denote
through a pure `DialectDenote`, does not apply; the lemmas on renamings and flattened
valuations of `VIR/MultiBlockLowering.lean` and `VIR/NFProgMapMulti.lean` are used at
`nfDialect` with the `DialectDenote` instance `defaultDenote` in their proofs; no statement
of this module mentions it.

## Main definitions

* `flatTy`, `flatCtx`, `flatEnc`, `flatV` — the components of a type, of a context, of a
  value and of a valuation.
* `tupleHom?`, `atomVar?`, `atomArgs?`, `atomRet?` — the renamings of a tuple binding, and
  of the arguments and of the result of another binding.
* `flatProg` — the pass at a renaming; `flattenTuples` — the pass at the identity.
* `flattenStep`, `flattenCert` — the pass as a chain step and its certificate.

## Main results

* `flatProg_denote` — at valuations related by the renaming, a program `flatProg` returns
  denotes the flattened results of the source program.
* `flattenTuples_sound` — `flattenTuples p` denotes, at the flattened valuation, the
  flattened results of `p`, at every leaf table and every fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_there pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (lookup_pullV)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. The components of a type and of a value -/

/-- The components of a type: none for `tnil`, the components of `h` and then of `t` for
    `tcons h t`, and the type itself otherwise. -/
def flatTy : nfDialect.Ty → Ctxt nfDialect
  | .tnil => []
  | .tcons h t => flatTy h ++ flatTy t
  | .bit => [.bit]
  | .unit => [.unit]
  | .word w => [.word w]
  | .arr n t => [.arr n t]
  | .pair a b => [.pair a b]
  | .uint W => [.uint W]
  | .sint W => [.sint W]
  | .int => [.int]
  | .slice t => [.slice t]

/-- The flattened context: the components of its types, in order. -/
abbrev flatCtx (Γ : Ctxt nfDialect) : Ctxt nfDialect :=
  ctxFlat flatTy Γ

/-- The components of a value. -/
def flatEnc : {t : nfDialect.Ty} → ⟦t⟧ → Valuation (flatTy t)
  | .tnil, _ => .nil
  | .tcons _ _, x => hvAppend (flatEnc x.1) (flatEnc x.2)
  | .bit, x => .cons x .nil
  | .unit, x => .cons x .nil
  | .word _, x => .cons x .nil
  | .arr _ _, x => .cons x .nil
  | .pair _ _, x => .cons x .nil
  | .uint _, x => .cons x .nil
  | .sint _, x => .cons x .nil
  | .int, x => .cons x .nil
  | .slice _, x => .cons x .nil

/-- The flattened valuation of a context. -/
abbrev flatV {Γ : Ctxt nfDialect} (V : Valuation Γ) : Valuation (flatCtx Γ) :=
  flatVal flatEnc V

/-! ## 2. The renamings of the pass -/

section Renamings

variable {Γ Δ : Ctxt nfDialect}

/-- The renaming of the components of the result of a tuple operation into `Δ`, from the
    renaming `ren` of the components of its arguments; `none` on every other operation. -/
def tupleHom? (ren : Ctxt.Hom (flatCtx Γ) Δ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Option (Ctxt.Hom (flatTy op.ret) Δ)
  | .tnilV, _ => some (fun v => nomatch v)
  | .tconsV _ _, .cons x (.cons y .nil) =>
      some (appendHom (fun w => ren (varHom flatTy x w)) (fun w => ren (varHom flatTy y w)))
  | .thead _ b, .cons x .nil => some (fun w => ren (varHom flatTy x (inlHom (flatTy b) w)))
  | .ttail a _, .cons x .nil => some (fun w => ren (varHom flatTy x (inrHom (flatTy a) w)))
  | .named _ op, args => tupleHom? ren op args
  | .const _ _, _ | .constBit _, _ | .constUnit, _ | .bin _ _, _ | .un _ _, _
  | .cast _ _, _ | .scast _ _, _ | .cmp _ _, _ | .andB, _ | .orB, _ | .xorB, _ | .eqB, _
  | .notB, _ | .index _ _, _ | .update _ _, _ | .arrLit _ _, _ | .arrRepeat _ _, _
  | .mkPair _ _, _ | .fst _ _, _ | .snd _ _, _ | .call _ _ _, _ | .ilit _ _, _ | .ctr, _
  | .trip _, _ => none

/-- The variable of a value of a type that is not a tuple, from the renaming of its one
    component; `none` at a tuple type. -/
def atomVar? : (s : nfDialect.Ty) → Ctxt.Hom (flatTy s) Δ → Option (Var Δ s)
  | .tnil, _ | .tcons _ _, _ => none
  | .bit, f => some (f .here)
  | .unit, f => some (f .here)
  | .word _, f => some (f .here)
  | .arr _ _, f => some (f .here)
  | .pair _ _, f => some (f .here)
  | .uint _, f => some (f .here)
  | .sint _, f => some (f .here)
  | .int, f => some (f .here)
  | .slice _, f => some (f .here)

/-- The arguments of a binding as variables of `Δ`, when no argument type is a tuple. -/
def atomArgs? (ren : Ctxt.Hom (flatCtx Γ) Δ) :
    {ss : List NfTy} → HVector (fun t => Var Γ t) ss → Option (HVector (fun t => Var Δ t) ss)
  | [], .nil => some .nil
  | s :: _, .cons x xs =>
      (atomVar? s (fun w => ren (varHom flatTy x w))).bind fun y =>
        (atomArgs? ren xs).map (.cons y)

/-- The renaming of the one component of a result of a type that is not a tuple to the
    head of `r :: Δ`; `none` at a tuple type. -/
def atomRet? : (r : nfDialect.Ty) → Option (Ctxt.Hom (flatTy r) (r :: Δ))
  | .tnil | .tcons _ _ => none
  | .bit => some (inlHom Δ)
  | .unit => some (inlHom Δ)
  | .word _ => some (inlHom Δ)
  | .arr _ _ => some (inlHom Δ)
  | .pair _ _ => some (inlHom Δ)
  | .uint _ => some (inlHom Δ)
  | .sint _ => some (inlHom Δ)
  | .int => some (inlHom Δ)
  | .slice _ => some (inlHom Δ)

end Renamings

/-! ## 3. The pass -/

/-- Tuple flattening at the renaming `ren` from the flattened source context into the
    target context `Δ`; `none` at a binding of an operation other than a tuple operation
    with an argument type or a result type that is a tuple. -/
def flatProg : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts →
    {Δ : Ctxt nfDialect} → Ctxt.Hom (flatCtx Γ) Δ → Option (NFProg nfDialect Δ (flatCtx ts))
  | _, _, .ret vs, _, ren => some (.ret (homToHV _ (argsHom flatTy ren vs)))
  | _, _, .var ⟨op, rfl, args⟩ k, Δ, ren =>
      match tupleHom? ren op args with
      | some R => flatProg k (appendHom R ren)
      | none =>
          (atomArgs? ren args).bind fun args' => (atomRet? (Δ := Δ) op.ret).bind fun R =>
            (flatProg k (appendHom R (fun w => (ren w).there))).map (.var ⟨op, rfl, args'⟩)
  | _, _, .forLoop (cs := cs) count inits body k, Δ, ren =>
      (flatProg body (NFProg.appHomM flatTy (Γ := HasWord64.word (d := nfDialect) :: _) cs
          (appendHom (inlHom (xs := [NfTy.word 64]) Δ) (fun w => (ren w).there)))).bind
        fun body' =>
        (flatProg k (NFProg.appHomM flatTy cs ren)).map fun k' =>
          .forLoop (ren (varHom flatTy count .here)) (homToHV _ (argsHom flatTy ren inits))
            body' k'
  | _, _, .ifThenElse (rs := rs) cond thn els k, _, ren =>
      (flatProg thn ren).bind fun thn' => (flatProg els ren).bind fun els' =>
        (flatProg k (NFProg.appHomM flatTy rs ren)).map fun k' =>
          .ifThenElse (ren (varHom flatTy cond .here)) thn' els' k'
  | _, _, .whileLoop (cs := cs) inits body k, _, ren =>
      (flatProg body (NFProg.appHomM flatTy cs ren)).bind fun body' =>
        (flatProg k (NFProg.appHomM flatTy cs ren)).map fun k' =>
          .whileLoop (homToHV _ (argsHom flatTy ren inits)) body' k'
  | _, _, .call (rs := rs) f args k, _, ren =>
      (flatProg k (NFProg.appHomM flatTy rs ren)).map fun k' =>
        .call f (homToHV _ (argsHom flatTy ren args)) k'

/-- Tuple flattening of a program: `flatProg` at the identity renaming. -/
def flattenTuples {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    Option (NFProg nfDialect (flatCtx Γ) (flatCtx ts)) :=
  flatProg p (fun v => v)

/-! ## 4. Preservation -/

/-- A value of each type. -/
def defaultVal : (t : NfTy) → t.denote
  | .bit => false
  | .unit => ()
  | .word _ => 0
  | .arr _ t => fun _ => defaultVal t
  | .pair a b => (defaultVal a, defaultVal b)
  | .uint _ => 0
  | .sint _ => 0
  | .int => 0
  | .tnil => ()
  | .tcons h t => (defaultVal h, defaultVal t)
  | .slice _ => []

/-- The pure denotation of `nfDialect` that returns `defaultVal` of the result type: the
    instance argument of the lemmas on renamings and flattened valuations, whose statements
    do not depend on it. -/
@[instance_reducible] def defaultDenote : DialectDenote nfDialect :=
  ⟨fun op _ => defaultVal (NfOp.ret op)⟩

section Lemmas

variable {Γ Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ) (V : Valuation Γ)
  (W : Valuation Δ) (hW : pullV ren W = flatV V)
include hW

/-- The components of a variable read, through `ren`, the components of its value. -/
theorem pullV_varRen {s : nfDialect.Ty} (x : Var Γ s) :
    pullV (fun w => ren (varHom flatTy x w)) W = flatEnc (x.lookup V) := by
  let inst : DialectDenote nfDialect := defaultDenote
  calc pullV (fun w => ren (varHom flatTy x w)) W
      = pullV (fun w => varHom flatTy x w) (pullV ren W) :=
        pullV_comp (fun w => varHom flatTy x w) ren W
    _ = flatEnc (x.lookup V) := by rw [hW]; exact pullV_varHom_flatVal flatEnc x V

/-- A component of a variable, through `ren`, reads that component of its value. -/
theorem lookup_varRen {s t : nfDialect.Ty} (x : Var Γ s) (u : Var (flatTy s) t) :
    (ren (varHom flatTy x u)).lookup W = u.lookup (flatEnc (x.lookup V)) := by
  let inst : DialectDenote nfDialect := defaultDenote
  rw [← pullV_varRen ren V W hW x]
  exact (lookup_pullV (fun w => ren (varHom flatTy x w)) u W).symm

/-- A tuple operation succeeds, and the renaming `tupleHom?` gives reads the components of
    its value. -/
theorem tupleHom?_spec (T : NfLeafTable) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
      (R : Ctxt.Hom (flatTy op.ret) Δ), tupleHom? ren op args = some @R →
      ∃ x, nfDenoteOp T op (Expr.lookupArgs args V) = some x ∧ pullV R W = flatEnc x := by
  let inst : DialectDenote nfDialect := defaultDenote
  intro op
  induction op
  case tnilV => exact fun _ _ _ => ⟨(), rfl, rfl⟩
  case tconsV a b =>
    intro args R h
    match args with
    | .cons x (.cons y .nil) =>
      rw [tupleHom?] at h
      have h2 := Option.some.inj h
      subst h2
      refine ⟨(x.lookup V, y.lookup V), rfl, ?_⟩
      exact (pullV_appendHom (fun w => ren (varHom flatTy x w))
        (fun w => ren (varHom flatTy y w)) W).trans
        (congrArg₂ hvAppend (pullV_varRen ren V W hW x) (pullV_varRen ren V W hW y))
  case thead a b =>
    intro args R h
    match args with
    | .cons x .nil =>
      rw [tupleHom?] at h
      have h2 := Option.some.inj h
      subst h2
      refine ⟨(x.lookup V).1, rfl, ?_⟩
      calc pullV (fun w => ren (varHom flatTy x (inlHom (flatTy b) w))) W
          = pullV (fun w => inlHom (flatTy b) w)
              (pullV (fun w => ren (varHom flatTy x w)) W) :=
            pullV_comp (fun w => inlHom (flatTy b) w) (fun w => ren (varHom flatTy x w)) W
        _ = _ := (congrArg (pullV (fun w => inlHom (flatTy b) w))
            (pullV_varRen ren V W hW x)).trans (pullV_inlHom _ _)
  case ttail a b =>
    intro args R h
    match args with
    | .cons x .nil =>
      rw [tupleHom?] at h
      have h2 := Option.some.inj h
      subst h2
      refine ⟨(x.lookup V).2, rfl, ?_⟩
      calc pullV (fun w => ren (varHom flatTy x (inrHom (flatTy a) w))) W
          = pullV (fun w => inrHom (flatTy a) w)
              (pullV (fun w => ren (varHom flatTy x w)) W) :=
            pullV_comp (fun w => inrHom (flatTy a) w) (fun w => ren (varHom flatTy x w)) W
        _ = _ := (congrArg (pullV (fun w => inrHom (flatTy a) w))
            (pullV_varRen ren V W hW x)).trans (pullV_inrHom _ _)
  case named n op ih => exact fun args R h => ih args R h
  all_goals intro args R h; simp [tupleHom?] at h

omit hW in
/-- The variable `atomVar?` gives reads the value whose components its renaming reads. -/
theorem atomVar?_spec : ∀ (s : nfDialect.Ty) (f : Ctxt.Hom (flatTy s) Δ) (y : Var Δ s)
    (v : ⟦s⟧), atomVar? s f = some y → pullV f W = flatEnc v → y.lookup W = v := by
  let inst : DialectDenote nfDialect := defaultDenote
  intro s f y v h hf
  cases s <;> simp only [atomVar?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact (lookup_pullV f .here W).symm.trans (by rw [hf]; rfl)

/-- The arguments `atomArgs?` gives read the values of the source arguments. -/
theorem atomArgs?_spec : ∀ {ss : List NfTy} (args : HVector (fun t => Var Γ t) ss)
    (args' : HVector (fun t => Var Δ t) ss), atomArgs? ren args = some args' →
    Expr.lookupArgs args' W = Expr.lookupArgs args V
  | [], .nil, args', h => by
      simp only [atomArgs?, Option.some.injEq] at h
      subst h
      rfl
  | s :: _, .cons x xs, args', h => by
      rw [atomArgs?] at h
      cases hy : atomVar? s (fun w => ren (varHom flatTy x w)) with
      | none => rw [hy] at h; cases h
      | some y =>
        cases hys : atomArgs? ren xs with
        | none => rw [hy, Option.bind_some, hys] at h; cases h
        | some ys =>
          rw [hy, Option.bind_some, hys, Option.map_some] at h
          have h2 := Option.some.inj h
          subst h2
          show HVector.cons _ _ = HVector.cons _ _
          rw [atomVar?_spec W s _ y _ hy (pullV_varRen ren V W hW x),
            atomArgs?_spec xs ys hys]

/-- The variables of the components of `vs`, through `ren`, read the components of the
    values of `vs`. -/
theorem lookupArgs_flatArgs {ss : List NfTy} (vs : HVector (fun t => Var Γ t) ss) :
    Expr.lookupArgs (homToHV _ (argsHom flatTy ren vs)) W = flatV (Expr.lookupArgs vs V) := by
  let inst : DialectDenote nfDialect := defaultDenote
  exact NFProg.lookupArgs_homToHV_argsHom flatEnc ren V W hW vs

/-- The renaming of a bound value of type `t` by `R` in front of `ren` relates the
    extended valuations. -/
theorem pullV_appendHom_flat {t : nfDialect.Ty} (R : Ctxt.Hom (flatTy t) Δ) (x : ⟦t⟧)
    (hR : pullV R W = flatEnc x) :
    pullV (appendHom R ren) W = flatV (V.extend x) := by
  let inst : DialectDenote nfDialect := defaultDenote
  exact (pullV_appendHom R ren W).trans (congrArg₂ hvAppend hR hW)

/-- The renaming `ren` shifted under one binding relates the extended target valuation to
    `V`. -/
theorem pullV_there_flat {s : nfDialect.Ty} (x : ⟦s⟧) :
    pullV (fun w => (ren w).there) (HVector.cons x W : Valuation (s :: Δ)) = flatV V := by
  let inst : DialectDenote nfDialect := defaultDenote
  exact (pullV_there ren x W).trans hW

/-- The renaming `NFProg.appHomM flatTy cs ren` relates the valuations `ren` relates,
    prefixed by a carried tuple and its components. -/
theorem pullV_appRen (cs : List NfTy) (acc : Valuation cs) :
    pullV (NFProg.appHomM flatTy cs ren) (hvAppend (flatV acc) W) = flatV (hvAppend acc V) := by
  let inst : DialectDenote nfDialect := defaultDenote
  exact NFProg.pullV_appHomM flatEnc ren V W hW cs acc

end Lemmas

/-- The identity renaming relates a flattened valuation to its source. -/
theorem pullV_id_flat {Γ : Ctxt nfDialect} (V : Valuation Γ) :
    pullV (fun v => v) (flatV V) = flatV V := by
  let inst : DialectDenote nfDialect := defaultDenote
  exact pullV_id _

/-- The renaming `atomRet?` gives reads the components of the head value. -/
theorem atomRet?_spec {Δ : Ctxt nfDialect} :
    ∀ (r : nfDialect.Ty) (R : Ctxt.Hom (flatTy r) (r :: Δ)),
    atomRet? r = some @R → ∀ (x : ⟦r⟧) (W : Valuation Δ),
      pullV R (HVector.cons x W) = flatEnc x := by
  intro r R h x W
  cases r <;> simp only [atomRet?, reduceCtorEq] at h <;>
    (have h2 := Option.some.inj h; subst h2; rfl)

/-- A fold in `Option` whose step commutes with `T`, followed by a continuation that
    commutes with `T` and `T₂`, commutes with `T₂`. -/
theorem bind_foldlM_map {α α' β γ γ' : Type} (l : List β) (a : α) (F : α → β → Option α)
    (G : α' → β → Option α') (T : α → α') (K : α → Option γ) (K' : α' → Option γ')
    (T₂ : γ → γ') (hs : ∀ a i, G (T a) i = (F a i).map T)
    (hk : ∀ a, K' (T a) = (K a).map T₂) :
    (l.foldlM G (T a) >>= K') = (l.foldlM F a >>= K).map T₂ := by
  rw [NFProg.foldlM_option_map F G T hs]
  exact NFProg.bind_map_comm _ T T₂ K' K hk

/-- An exit-flag iteration whose step commutes with the flattening, followed by a
    continuation that commutes with the flattening and `T₂`, commutes with `T₂`. -/
theorem bind_whileIter_flat {cs : Ctxt nfDialect} {γ γ' : Type}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := nfDialect) :: cs)))
    (step' : Valuation (flatCtx cs) →
      Option (Valuation (HasBitType.bit (d := nfDialect) :: flatCtx cs)))
    (n : Nat) (a : Valuation cs) (a' : Valuation (flatCtx cs)) (ha : a' = flatV a)
    (K : Valuation cs → Option γ)
    (K' : Valuation (flatCtx cs) → Option γ') (T₂ : γ → γ')
    (hs : ∀ a, step' (flatV a) = (step a).map flatV)
    (hk : ∀ a, K' (flatV a) = (K a).map T₂) :
    (NFProg.whileIter (d := nfDialect) step' n a' >>= K') =
      (NFProg.whileIter (d := nfDialect) step n a >>= K).map T₂ := by
  let inst : DialectDenote nfDialect := defaultDenote
  subst ha
  rw [NFProg.whileIter_map step step' flatV id (fun _ => rfl) fun a => by
    rw [hs a]
    congr 1
    funext r
    cases r
    rfl]
  exact NFProg.bind_map_comm _ flatV T₂ K' K hk

/-- **Preservation.** A program that `flatProg` returns at a renaming `ren` relating `W` to
    the flattened `V` denotes at `W`, at every leaf table and fuel, the flattened results of
    the source program at `V`. -/
theorem flatProg_denote (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ)
    (q : NFProg nfDialect Δ (flatCtx ts)), flatProg p ren = some q →
    ∀ (V : Valuation Γ) (W : Valuation Δ), pullV ren W = flatV V →
    @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Δ _ q W =
      (@NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V).map flatV := by
  induction p with
  | ret vs =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      have h2 := Option.some.inj hq
      subst h2
      exact congrArg some (lookupArgs_flatArgs ren V W hW vs)
  | var e k ih =>
      obtain ⟨op, rfl, args⟩ := e
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      cases hT : tupleHom? ren op args with
      | some R =>
          simp only [hT] at hq
          obtain ⟨x, hx, hR⟩ := tupleHom?_spec ren V W hW T op args R hT
          show _ = (Option.bind (nfDenoteOp T op (Expr.lookupArgs args V)) _).map flatV
          rw [hx, Option.bind_some]
          exact ih (appendHom R ren) q hq (V.extend x) W
            (pullV_appendHom_flat ren V W hW R x hR)
      | none =>
          simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨args', ha, R, hR, k', hk, rfl⟩ := hq
          show Option.bind (nfDenoteOp T op (Expr.lookupArgs args' W)) _ =
            (Option.bind (nfDenoteOp T op (Expr.lookupArgs args V)) _).map flatV
          rw [atomArgs?_spec ren V W hW args args' ha]
          cases nfDenoteOp T op (Expr.lookupArgs args V) with
          | none => rfl
          | some x =>
            exact ih _ k' hk (V.extend x) (W.extend x)
              (pullV_appendHom_flat _ V _ (pullV_there_flat ren V W hW x) R x
                (atomRet?_spec op.ret R hR x W))
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      have hc : (ren (varHom flatTy count .here)).lookup W = count.lookup V :=
        (lookup_varRen ren V W hW count .here).trans rfl
      rw [@NFProg.denote_forLoop nfDialect _ _ _ _ (nfDenote T),
        @NFProg.denote_forLoop nfDialect _ _ _ _ (nfDenote T), hc,
        lookupArgs_flatArgs ren V W hW inits]
      exact bind_foldlM_map _ _ _ _ flatV _ _ flatV
        (fun acc i => ihb _ body' hb
          (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V))
          (hvAppend (flatV acc) (.cons (HasWord64.ofNat (d := nfDialect) i) W))
          (pullV_appRen _ (.cons (HasWord64.ofNat (d := nfDialect) i) V)
            (.cons (HasWord64.ofNat (d := nfDialect) i) W)
            (pullV_appendHom_flat (t := NfTy.word 64) (Δ := NfTy.word 64 :: Δ) _ V _
              (pullV_there_flat ren V W hW _)
              (fun w => inlHom (d := nfDialect) (xs := [NfTy.word 64]) Δ w) _ rfl)
            _ acc))
        (fun acc => ihk _ k' hk (hvAppend acc V) (hvAppend (flatV acc) W)
          (pullV_appRen ren V W hW _ acc))
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨thn', ht, els', he, k', hk, rfl⟩ := hq
      have hc : (ren (varHom flatTy cond .here)).lookup W = cond.lookup V :=
        (lookup_varRen ren V W hW cond .here).trans rfl
      have hk' := fun r => ihk _ k' hk (hvAppend r V) (hvAppend (flatV r) W)
        (pullV_appRen ren V W hW _ r)
      rw [@NFProg.denote_ifThenElse nfDialect _ _ _ _ (nfDenote T),
        @NFProg.denote_ifThenElse nfDialect _ _ _ _ (nfDenote T), hc]
      by_cases hb : HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true
      · rw [if_pos hb, if_pos hb, iht ren thn' ht V W hW]
        exact NFProg.bind_map_comm _ flatV flatV _ _ hk'
      · rw [if_neg hb, if_neg hb, ihe ren els' he V W hW]
        exact NFProg.bind_map_comm _ flatV flatV _ _ hk'
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      exact bind_whileIter_flat _ _ _ _ _ (lookupArgs_flatArgs ren V W hW inits) _ _ flatV
        (fun acc => ihb _ body' hb (hvAppend acc V) (hvAppend (flatV acc) W)
          (pullV_appRen ren V W hW _ acc))
        (fun acc => ihk _ k' hk (hvAppend acc V) (hvAppend (flatV acc) W)
          (pullV_appRen ren V W hW _ acc))
  | call f args k _ =>
      intro Δ ren q hq V W hW
      rw [flatProg] at hq
      simp only [Option.map_eq_some_iff] at hq
      obtain ⟨k', _, rfl⟩ := hq
      rfl

/-- **Tuple flattening preserves the denotation.** A program `flattenTuples p` denotes at
    the flattened valuation of `V`, at every leaf table and fuel, the flattened results of
    `p` at `V`. -/
theorem flattenTuples_sound (T : NfLeafTable) (fuel : Nat) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) {q : NFProg nfDialect (flatCtx Γ) (flatCtx ts)}
    (hq : flattenTuples p = some q) (V : Valuation Γ) :
    @NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel _ _ q (flatV V) =
      (@NFProg.denote nfDialect _ _ _ _ (nfDenote T) _ fuel Γ ts p V).map flatV :=
  flatProg_denote T fuel p _ q hq V (flatV V) (pullV_id_flat V)

/-! ## 5. The chain step -/

/-- Tuple flattening as a chain step from `NFProg nfDialect Γ ts` to
    `NFProg nfDialect (flatCtx Γ) (flatCtx ts)`. -/
def flattenStep (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.Step (NFProg nfDialect Γ ts) (NFProg nfDialect (flatCtx Γ) (flatCtx ts)) :=
  ⟨"flattenTuples", flattenTuples⟩

/-- The certificate of tuple flattening at the leaf table `T` and the fuel `fuel`: the
    flattening of the valuations is the input transport and the flattening of the result
    tuples the output transport, from `flattenTuples_sound`. -/
def flattenCert (T : NfLeafTable) (fuel : Nat) (Γ : Ctxt nfDialect) (ts : List NfTy) :
    PassChain.StepCert (flattenStep Γ ts).run
      (@NFProgPasses.nfSem fuel nfDialect _ _ _ _ (nfDenote T) _ Γ ts)
      (@NFProgPasses.nfSem fuel nfDialect _ _ _ _ (nfDenote T) _ (flatCtx Γ) (flatCtx ts)) :=
  PassChain.StepCert.ofTransport _ _ flatV flatV fun p _ V hf =>
    flattenTuples_sound T fuel p hf V

end CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
