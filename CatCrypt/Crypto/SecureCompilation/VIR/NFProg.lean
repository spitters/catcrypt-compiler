/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.Regions
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

/-!
# Structured programs with regions over any dialect

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`NFProg d Γ ts` is the structured layer above the straight-line programs `Com d` of a
dialect `d`: let-bindings, a multi-result return, a counted loop with a carried
tuple, a two-armed branch with results, and a loop in exit-flag form. It is a
sibling inductive above `Com`; the region bodies are `NFProg`s again, so the
constructors nest.

* `forLoop count inits body k` is `scf.for` from `0` to `count` with `iter_args`:
  the body runs over the context `cs ++ word :: Γ` (carried tuple, trip index,
  enclosing context) and returns the next tuple; `k` runs over `cs ++ Γ`.
* `ifThenElse cond thn els k`: both arms return `rs`, and `k` runs over `rs ++ Γ`.
* `whileLoop inits body k`: the body runs over `cs ++ Γ` and returns a continue bit
  followed by the next tuple; the loop stops at the first `false` bit. The body runs
  at least once.

The denotation is monadic in `Option` through `DialectDenoteM d Option`, so that an
op may fail, and takes a fuel bound for `whileLoop`; `forLoop` and `ifThenElse` do
not consume fuel.

## Main definitions

* `NFProg` — the structured programs.
* `NFProg.whileIter` — the fuel-bounded iteration of an exit-flag loop body.
* `NFProg.denote` — the denotation.
* `NFProg.whileFree` — the programs without `whileLoop`.
* `NFProg.ofCom`, `NFProg.ofComLoop`, `NFProg.ofComR` — the embeddings of `Com`,
  `ComLoop` and `ComR`.

## Main results

* `NFProg.denote_ret`, `NFProg.denote_var`, `NFProg.denote_forLoop`,
  `NFProg.denote_ifThenElse`, `NFProg.denote_whileLoop` — the equations of `denote`.
* `NFProg.whileIter_zero` — a `whileLoop` at fuel `0` fails.
* `NFProg.denote_fuel_of_whileFree` — a program without `whileLoop` denotes
  independently of the fuel.
* `NFProg.foldlM_single` — a counted loop over one carried value whose body always
  succeeds is `some` of the `List.foldl`.
* `NFProg.denote_ofCom`, `NFProg.denote_ofComLoop`, `NFProg.denote_ofComR` — the
  embeddings preserve the denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend hvToHom pullV_hvToHom lookupVars_eq_lookupArgs)
open FieldDialectBlockDescent (pullV pullV_there)

/-! ## 1. `NFProg` -/

/-- Structured programs of a dialect `d` returning the list of types `ts`.

    * `ret vs` — return the variables `vs`.
    * `var e k` — let-bind `e` and continue with `k`.
    * `forLoop count inits body k` — run `body` for the trip indices `0, …, count - 1`
      from the carried tuple `inits`; `body` sees the carried tuple, the trip index
      and the enclosing context, and returns the next tuple; `k` sees the final tuple
      and the enclosing context.
    * `ifThenElse cond thn els k` — run `thn` or `els` by the bit `cond`; `k` sees
      their results and the enclosing context.
    * `whileLoop inits body k` — run `body` from the carried tuple `inits` while the
      bit it returns in front of the next tuple is `true`; `k` sees the final tuple
      and the enclosing context. -/
inductive NFProg (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] : Ctxt d → List d.Ty → Type where
  /-- Return a list of variables. -/
  | ret {Γ ts} (vs : HVector (fun t => Var Γ t) ts) : NFProg d Γ ts
  /-- Let-bind an expression and continue with its result in scope. -/
  | var {Γ t ts} (e : Expr d Γ t) (k : NFProg d (t :: Γ) ts) : NFProg d Γ ts
  /-- A counted loop carrying the tuple `cs`. -/
  | forLoop {Γ cs ts} (count : Var Γ (HasWord64.word (d := d)))
      (inits : HVector (fun t => Var Γ t) cs)
      (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs)
      (k : NFProg d (cs ++ Γ) ts) : NFProg d Γ ts
  /-- A two-armed branch with the results `rs`. -/
  | ifThenElse {Γ rs ts} (cond : Var Γ (HasBitType.bit (d := d)))
      (thn els : NFProg d Γ rs) (k : NFProg d (rs ++ Γ) ts) : NFProg d Γ ts
  /-- A loop in exit-flag form carrying the tuple `cs`. -/
  | whileLoop {Γ cs ts} (inits : HVector (fun t => Var Γ t) cs)
      (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs))
      (k : NFProg d (cs ++ Γ) ts) : NFProg d Γ ts

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-! ## 2. Denotation -/

/-- The fuel-bounded iteration of an exit-flag loop body `step`: each unit of fuel
    runs `step` once; a `false` bit returns the tuple after that run, a `true` bit
    continues, and fuel `0` fails. -/
def whileIter {cs : List d.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs))) :
    Nat → Valuation cs → Option (Valuation cs)
  | 0, _ => none
  | n + 1, acc => step acc >>= fun r =>
      if HasBoolBit.toBool (d := d) r.head then whileIter step n r.tail else some r.tail

variable [DialectDenoteM d Option]

/-- Denotation of an `NFProg` at the fuel `fuel`, which bounds the runs of each
    `whileLoop` body. -/
def denote (fuel : Nat) :
    {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Valuation Γ → Option (Valuation ts)
  | _, _, .ret vs, V => some (Expr.lookupArgs vs V)
  | _, _, .var e k, V => e.denoteM V >>= fun x => k.denote fuel (V.extend x)
  | _, _, .forLoop count inits body k, V =>
      (List.range (HasWord64.toNat (d := d) (count.lookup V))).foldlM
          (fun acc i => body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (Expr.lookupArgs inits V) >>= fun acc =>
        k.denote fuel (hvAppend acc V)
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
        else els.denote fuel V) >>= fun r =>
        k.denote fuel (hvAppend r V)
  | _, _, .whileLoop inits body k, V =>
      whileIter (fun acc => body.denote fuel (hvAppend acc V)) fuel (Expr.lookupArgs inits V)
        >>= fun acc => k.denote fuel (hvAppend acc V)

/-- A return denotes its looked-up variables. -/
theorem denote_ret {Γ : Ctxt d} {ts : List d.Ty} (vs : HVector (fun t => Var Γ t) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (NFProg.ret (d := d) vs).denote fuel V = some (Expr.lookupArgs vs V) := rfl

/-- A let-binding denotes its continuation at the extended valuation. -/
theorem denote_var {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty} (e : Expr d Γ t)
    (k : NFProg d (t :: Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.var e k).denote fuel V = e.denoteM V >>= fun x => k.denote fuel (V.extend x) :=
  rfl

/-- A counted loop denotes the `List.range` fold of its body, then its continuation at
    the final tuple. -/
theorem denote_forLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (count : Var Γ (HasWord64.word (d := d))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ HasWord64.word (d := d) :: Γ) cs) (k : NFProg d (cs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (NFProg.forLoop count inits body k).denote fuel V =
      (List.range (HasWord64.toNat (d := d) (count.lookup V))).foldlM
          (fun acc i => body.denote fuel (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)))
          (Expr.lookupArgs inits V) >>= fun acc =>
        k.denote fuel (hvAppend acc V) := rfl

/-- A branch denotes the arm its bit selects, then its continuation at the results. -/
theorem denote_ifThenElse {Γ : Ctxt d} {rs ts : List d.Ty}
    (cond : Var Γ (HasBitType.bit (d := d))) (thn els : NFProg d Γ rs)
    (k : NFProg d (rs ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.ifThenElse cond thn els k).denote fuel V =
      (if HasBoolBit.toBool (d := d) (cond.lookup V) then thn.denote fuel V
        else els.denote fuel V) >>= fun r => k.denote fuel (hvAppend r V) := rfl

/-- An exit-flag loop denotes the fuel-bounded iteration of its body, then its
    continuation at the final tuple. -/
theorem denote_whileLoop {Γ : Ctxt d} {cs ts : List d.Ty}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg d (cs ++ Γ) (HasBitType.bit (d := d) :: cs)) (k : NFProg d (cs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (NFProg.whileLoop inits body k).denote fuel V =
      whileIter (fun acc => body.denote fuel (hvAppend acc V)) fuel (Expr.lookupArgs inits V)
        >>= fun acc => k.denote fuel (hvAppend acc V) := rfl

omit [DialectSignature d] [HasWord64 d] [DialectDenoteM d Option] in
/-- The iteration of an exit-flag loop at fuel `0` fails. -/
theorem whileIter_zero {cs : List d.Ty}
    (step : Valuation cs → Option (Valuation (HasBitType.bit (d := d) :: cs)))
    (acc : Valuation cs) : whileIter step 0 acc = none := rfl

/-! ## 3. Fuel independence without `whileLoop` -/

omit [DialectDenoteM d Option] in
/-- The programs without `whileLoop`. -/
def whileFree : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => k.whileFree
  | _, _, .forLoop _ _ body k => body.whileFree && k.whileFree
  | _, _, .ifThenElse _ thn els k => thn.whileFree && els.whileFree && k.whileFree
  | _, _, .whileLoop _ _ _ => false

/-- A program without `whileLoop` denotes independently of the fuel. -/
theorem denote_fuel_of_whileFree {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.whileFree = true) (fuel fuel' : Nat) (V : Valuation Γ) :
    p.denote fuel V = p.denote fuel' V := by
  induction p with
  | ret vs => rfl
  | var e k ih =>
      simp only [denote, ih hp]
  | forLoop count inits body k ihb ihk =>
      simp only [whileFree, Bool.and_eq_true] at hp
      simp only [denote, ihb hp.1, ihk hp.2]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [whileFree, Bool.and_eq_true] at hp
      simp only [denote, iht hp.1.1, ihe hp.1.2, ihk hp.2]
  | whileLoop inits body k _ _ => simp [whileFree] at hp

end NFProg

/-! ## 4. The embeddings of `Com`, `ComLoop` and `ComR` -/

/-- The `Option`-valued denotation of a dialect with a pure denotation: every op
    succeeds. -/
instance instDialectDenoteMOptionOfPure (d : Dialect) [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] : DialectDenoteM d Option where
  denoteM op args := some (DialectDenote.denote op args)

/-- Under `instDialectDenoteMOptionOfPure`, an expression denotes `some` of its pure
    denotation. -/
@[simp] theorem Expr.denoteM_option_eq_some {d : Dialect} [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (V : Valuation Γ) : e.denoteM (M := Option) V = some (e.denote V) := by
  obtain ⟨op, rfl, args⟩ := e
  rfl

namespace NFProg

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A straight-line program as an `NFProg` with one result. -/
def ofCom : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → NFProg d Γ [t]
  | _, _, .ret v => .ret (.cons v .nil)
  | _, _, .var e k => .var e (ofCom k)

/-- A `ComLoop` as an `NFProg` with one result: `forRt` is a `forLoop` carrying one
    value, whose body reads the invariants `invs` through the renaming `hvToHom invs`
    into the enclosing context. -/
def ofComLoop : {Γ : Ctxt d} → {t : d.Ty} → ComLoop d Γ t → NFProg d Γ [t]
  | _, _, .block c => ofCom c
  | _, _, .var e k => .var e (ofComLoop k)
  | _, _, .forRt count init invs body k =>
      .forLoop count (.cons init .nil)
        (ofCom (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.lift (hvToHom invs))) body))
        (ofComLoop k)

/-- A `ComR` as an `NFProg` with one result: `ifBit` is an `ifThenElse` with one
    result returned by its continuation; the level tag is dropped. -/
def ofComR : {Γ : Ctxt d} → {t : d.Ty} → ComR d Γ t → NFProg d Γ [t]
  | _, _, .ret v => .ret (.cons v .nil)
  | _, _, .var e k => .var e (ofComR k)
  | _, _, .ifBit cond _ thn els =>
      .ifThenElse cond (ofComR thn) (ofComR els) (.ret (.cons .here .nil))

section Pure

variable [DialectDenote d]

/-- The embedding of a straight-line program returns its denotation. -/
theorem denote_ofCom {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (fuel : Nat)
    (V : Valuation Γ) : (ofCom c).denote fuel V = some (.cons (c.denote V) .nil) := by
  induction c with
  | ret v => rfl
  | var e k ih => simp only [ofCom, denote, Expr.denoteM_option_eq_some]; exact ih _

omit [HasWord64 d] [HasBoolBit d] in
/-- Pulling back along a lifted renaming keeps the head and pulls back the tail. -/
theorem pullV_lift_cons {Γ Δ : Ctxt d} {s : d.Ty} (h : Ctxt.Hom Γ Δ) (x : ⟦s⟧)
    (W : Valuation Δ) : pullV h.lift (HVector.cons x W) = HVector.cons x (pullV h W) := by
  show HVector.cons x (pullV (fun v => (h v).there) (HVector.cons x W)) = _
  rw [pullV_there]

omit [HasWord64 d] [HasBoolBit d] [DialectSignature d] [DialectDenote d] in
/-- A fold in `Option` over one carried value whose step always succeeds is `some` of
    the pure fold. -/
theorem foldlM_single {α : Type} {t : d.Ty}
    (f : Valuation [t] → α → Option (Valuation [t])) (g : ⟦t⟧ → α → ⟦t⟧) (hf : ∀ a i, f (.cons a .nil) i = some (.cons (g a i) .nil)) :
    ∀ (l : List α) (a : ⟦t⟧), l.foldlM f (.cons a .nil) = some (.cons (l.foldl g a) .nil)
  | [], _ => rfl
  | i :: l, a => by
      rw [List.foldlM_cons, hf]
      exact foldlM_single f g hf l (g a i)

/-- The embedding of a `ComLoop` returns its denotation. -/
theorem denote_ofComLoop {Γ : Ctxt d} {t : d.Ty} (c : ComLoop d Γ t) (fuel : Nat)
    (V : Valuation Γ) : (ofComLoop c).denote fuel V = some (.cons (c.denote V) .nil) := by
  induction c with
  | block c => exact denote_ofCom c fuel V
  | var e k ih =>
      simp only [ofComLoop, denote, Expr.denoteM_option_eq_some]; exact ih _
  | forRt count init invs body k ih =>
      have hstep : ∀ (acc : Valuation [_]) (i : Nat),
          (ofCom (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.lift (hvToHom invs))) body)).denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            some (.cons (body.denote (.cons acc.head (.cons (HasWord64.ofNat (d := d) i)
              (Expr.lookupArgs invs V)))) .nil) := by
        intro acc i
        rcases acc with _ | ⟨a, _ | _⟩
        rw [denote_ofCom, FieldDialectBlockDescent.Com.denote_rename]
        show some (HVector.cons (body.denote (pullV _ (HVector.cons a (HVector.cons _ V))))
          .nil) = _
        rw [pullV_lift_cons, pullV_lift_cons, pullV_hvToHom, lookupVars_eq_lookupArgs]
        rfl
      simp only [ofComLoop, denote, hstep]
      rw [show Expr.lookupArgs (HVector.cons init .nil) V = .cons (init.lookup V) .nil from rfl,
        foldlM_single _ (fun a i => body.denote
          (.cons a (.cons (HasWord64.ofNat (d := d) i) (Expr.lookupArgs invs V))))
          (fun _ _ => rfl)]
      exact ih _

end Pure

/-- The embedding of a `ComR` returns its `Option`-valued denotation. -/
theorem denote_ofComR [DialectDenoteM d Option] {Γ : Ctxt d} {t : d.Ty} (c : ComR d Γ t)
    (fuel : Nat) (V : Valuation Γ) :
    (ofComR c).denote fuel V = (c.denoteM (M := Option) V).map (fun x => .cons x .nil) := by
  induction c with
  | ret v => rfl
  | var e k ih =>
      simp only [ofComR, denote, ComR.denoteM, ih]
      cases e.denoteM (M := Option) V <;> rfl
  | ifBit cond _ thn els iht ihe =>
      simp only [ofComR, denote, ComR.denoteM]
      split
      · rw [iht]; cases thn.denoteM (M := Option) V <;> rfl
      · rw [ihe]; cases els.denoteM (M := Option) V <;> rfl

end NFProg

end CatCrypt.Crypto.SecureCompilation.VIR
