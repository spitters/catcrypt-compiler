/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

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

The trip counter has the dialect's word type `HasWord64.word`; `HasWord64` also reads
a counter value as a `Nat` and embeds a trip index into the word type, following the
`HasBitType`/`HasBoolBit` pattern of `VIR/Regions.lean`.

## Main definitions

* `HasWord64` — the dialect's trip-counter type and its `Nat` readings.
* `allVars` — every variable of a context, as an argument vector.
* `NFProg` — the structured programs.
* `NFProg.whileIter` — the fuel-bounded iteration of an exit-flag loop body.
* `NFProg.denote` — the denotation.
* `NFProg.whileFree` — the programs without `whileLoop`.
* `NFProg.ofCom`, `NFProg.ofComR` — the embeddings of `Com` and `ComR`.
* `NFProg.toCom?` — the straight-line program of a one-result `NFProg` made of
  bindings and a return.

## Main results

* `lookupArgs_allVars` — `allVars Γ` reads back the whole valuation.
* `NFProg.denote_ret`, `NFProg.denote_var`, `NFProg.denote_forLoop`,
  `NFProg.denote_ifThenElse`, `NFProg.denote_whileLoop` — the equations of `denote`.
* `NFProg.whileIter_zero` — a `whileLoop` at fuel `0` fails.
* `NFProg.denote_fuel_of_whileFree` — a program without `whileLoop` denotes
  independently of the fuel.
* `NFProg.foldlM_single` — a counted loop over one carried value whose body always
  succeeds is `some` of the `List.foldl`.
* `NFProg.denote_ofCom`, `NFProg.denote_ofComR` — the embeddings preserve the
  denotation.
* `NFProg.denote_of_toCom?` — a program `toCom?` reads as a straight-line program
  returns that program's denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)

/-! ## 0. The trip-counter type and the whole context as arguments -/

/-- Shift an argument vector of variables under one more binding. -/
def shiftVars {d : Dialect.{0, 0}} {Γ : Ctxt d} {s : d.Ty} :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    HVector (fun ty => Ctxt.Var (s :: Γ) ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (.there v) (shiftVars rest)

/-- Every variable of `Γ`, in order, as an argument vector. -/
def allVars {d : Dialect.{0, 0}} : (Γ : Ctxt d) → HVector (fun ty => Ctxt.Var Γ ty) Γ
  | [] => .nil
  | _ :: Γ => .cons .here (shiftVars (allVars Γ))

/-- A shifted argument vector reads the valuation below the new binding. -/
theorem lookupArgs_shiftVars {d : Dialect.{0, 0}} [TyDenote d.Ty] {Γ : Ctxt d} {s : d.Ty}
    (x : ⟦s⟧) (V : Ctxt.Valuation Γ) :
    {tys : List d.Ty} → (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    Expr.lookupArgs (shiftVars (s := s) hv) (V.extend x) = Expr.lookupArgs hv V
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (v.lookup V) (Expr.lookupArgs (shiftVars (s := s) rest) (V.extend x)) = _
      rw [lookupArgs_shiftVars x V rest]
      rfl

/-- `allVars Γ` reads back the whole valuation. -/
theorem lookupArgs_allVars {d : Dialect.{0, 0}} [TyDenote d.Ty] :
    {Γ : Ctxt d} → (V : Ctxt.Valuation Γ) → Expr.lookupArgs (allVars Γ) V = V
  | [], .nil => rfl
  | _ :: _, .cons x V =>
      congrArg (HVector.cons x) ((lookupArgs_shiftVars x V (allVars _)).trans (lookupArgs_allVars V))

/-- A dialect with a designated 64-bit word type `word`, used as the trip counter
    of a counted loop, with the reading `toNat` of a counter value and the
    embedding `ofNat` of a trip index. -/
class HasWord64 (d : Dialect.{0, 0}) [TyDenote d.Ty] where
  /-- The dialect's 64-bit word type. -/
  word : d.Ty
  /-- The trip count a counter value denotes. -/
  toNat : ⟦word⟧ → Nat
  /-- The counter value of a trip index. -/
  ofNat : Nat → ⟦word⟧

/-- The trip counter of `catCryptDialect` is `CryptoTy.sword 64`. -/
instance : HasWord64 catCryptDialect where
  word := CryptoTy.sword 64
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

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

/-! ## 4. The embeddings of `Com` and `ComR` -/

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

/-- The straight-line program of an `NFProg` with the one result `t` (`ts = [t]`) made of
    let-bindings and a return; `none` on a region constructor. -/
def toComAt : {Γ : Ctxt d} → {ts : List d.Ty} → NFProg d Γ ts → (t : d.Ty) → ts = [t] →
    Option (Com d Γ t)
  | _, _, .ret vs, _, h => by
      subst h
      exact match vs with
        | .cons v .nil => some (.ret v)
  | _, _, .var e k, t, h => (toComAt k t h).map (.var e)
  | _, _, .forLoop .., _, _ => none
  | _, _, .ifThenElse .., _, _ => none
  | _, _, .whileLoop .., _, _ => none

/-- The straight-line program of a one-result `NFProg` made of let-bindings and a
    return; `none` on a region constructor. -/
def toCom? {Γ : Ctxt d} {t : d.Ty} (p : NFProg d Γ [t]) : Option (Com d Γ t) :=
  toComAt p t rfl

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

/-- A program `toComAt` reads as the straight-line program `c` returns the denotation
    of `c`. -/
theorem denote_of_toComAt {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) (t : d.Ty)
    (h : ts = [t]) {c : Com d Γ t} (hc : p.toComAt t h = some c) (fuel : Nat)
    (V : Valuation Γ) : p.denote fuel V = some (h ▸ .cons (c.denote V) .nil) := by
  induction p with
  | ret vs =>
      subst h
      rcases vs with _ | ⟨v, _ | _⟩
      simp only [toComAt, Option.some.injEq] at hc
      subst hc
      rfl
  | var e k ih =>
      simp only [toComAt, Option.map_eq_some_iff] at hc
      obtain ⟨c', hk, rfl⟩ := hc
      subst h
      simp only [denote, Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
      exact ih rfl hk _
  | forLoop => simp [toComAt] at hc
  | ifThenElse => simp [toComAt] at hc
  | whileLoop => simp [toComAt] at hc

/-- A program `toCom?` reads as the straight-line program `c` returns the denotation of
    `c`. -/
theorem denote_of_toCom? {Γ : Ctxt d} {t : d.Ty} (p : NFProg d Γ [t]) {c : Com d Γ t}
    (hc : p.toCom? = some c) (fuel : Nat) (V : Valuation Γ) :
    p.denote fuel V = some (.cons (c.denote V) .nil) :=
  denote_of_toComAt p t rfl hc fuel V

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
