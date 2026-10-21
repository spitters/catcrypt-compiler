/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect

/-!
# Structured programs translated expression by expression between two dialects

Two dialects `⟨O₁, T⟩` and `⟨O₂, T⟩` over one type alphabet, the second with the trip
counter and the branch bit of the first (`sameWord`, `sameBit`), have the same contexts,
valuations and region constructors. For a map `f` of the expressions of the first to
expressions of the second over the same context and type, `relabel f` translates every
let-bound expression of a structured program by `f` and keeps the regions.

The translation preserves the denotation when every translated expression denotes as the
expression and the two call environments agree. It preserves the leakage run when a
translated expression also emits the events of the expression, and the result of the level
checker when a translated expression has the constraint and the argument levels of the
expression. The inclusion of a summand into an operation sum `Dialect.opSum` over the type
alphabet of the summand is such a map: it tags the operation and keeps the arguments.

`scalarProg` is the instance at `jasminVec`, the operation sum of `jasminDialect` and the
dialect `x86vec` of vector operations, with `scalarExpr` tagging an operation `.inl`: a
program of `jasminDialect` as a program of `jasminVec`.

## Main definitions

* `sameWord`, `sameBit`: the trip counter and the branch bit of the first dialect as those
  of the second.
* `relabel`: the translation of a structured program along a map of expressions.
* `scalarExpr`, `scalarProg`: an expression and a program of `jasminDialect` as an
  expression and a program of `jasminVec`.

## Main results

* `relabel_denote`: the translation preserves the denotation at every fuel.
* `relabel_leakRunM`: the translation preserves the results and the events of the leakage
  run.
* `relabel_levelCheck'`: the translation keeps the result of the level checker.
* `relabel_nfCTRel`: a translated program the level checker accepts in the first dialect
  is constant time in the second relative to its runs.
* `scalarProg_denote`, `scalarProg_leakRun`, `scalarProg_levelCheck'`,
  `scalarProg_nfCTRel`: the four results at `jasminVec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecEmbed

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum
  (castVar castArgs lookup_castVar lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. Two dialects over one type alphabet with one counter and one bit -/

/-- The dialect with the operations `O` over the type alphabet `T`. -/
abbrev opsOver (O T : Type) : Dialect.{0, 0} := ⟨O, T⟩

/-- The dialect with the operations `O₂` over the type alphabet `T`, named beside the
    dialect with the operations `O₁` whose trip counter and branch bit it takes. -/
abbrev opsVia (_O₁ O₂ T : Type) : Dialect.{0, 0} := ⟨O₂, T⟩

section Generic

variable {O₁ O₂ T : Type} [TyDenote T]

/-- The trip counter of the dialect with the operations `O₂`: the counter of the dialect
    with the operations `O₁` over the same types. -/
@[reducible] def sameWord [HasWord64 (opsOver O₁ T)] : HasWord64 (opsVia O₁ O₂ T) where
  word := HasWord64.word (d := (opsOver O₁ T))
  toNat := HasWord64.toNat (d := (opsOver O₁ T))
  ofNat := HasWord64.ofNat (d := (opsOver O₁ T))

/-- The branch bit of the dialect with the operations `O₂`: the bit of the dialect with
    the operations `O₁` over the same types. -/
@[reducible] def sameBit [HasBoolBit (opsOver O₁ T)] : HasBoolBit (opsVia O₁ O₂ T) where
  bit := HasBitType.bit (d := (opsOver O₁ T))
  toBool := HasBoolBit.toBool (d := (opsOver O₁ T))

attribute [local instance] sameWord sameBit

variable [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)]

/-! ## 2. The translation of the let-bound expressions -/

/-- A structured program with every let-bound expression translated by `f` into the
    dialect with the operations `O₂`, the regions kept. -/
def relabel (f : ∀ {Γ : List T} {t : T}, Expr (opsOver O₁ T) Γ t → Expr (opsVia O₁ O₂ T) Γ t) :
    {Γ : Ctxt (opsOver O₁ T)} → {ts : List T} → NFProg (opsOver O₁ T) Γ ts →
      NFProg (opsVia O₁ O₂ T) Γ ts
  | _, _, .ret vs => .ret (castArgs vs)
  | _, _, .var e k => .var (f e) (relabel f k)
  | _, _, .forLoop count inits body k =>
      .forLoop (castVar count) (castArgs inits) (relabel f body) (relabel f k)
  | _, _, .ifThenElse cond thn els k =>
      .ifThenElse (castVar cond) (relabel f thn) (relabel f els) (relabel f k)
  | _, _, .whileLoop inits body k =>
      .whileLoop (castArgs inits) (relabel f body) (relabel f k)
  | _, _, .call g args k => .call g (castArgs args) (relabel f k)

/-! ## 3. Functions of the dialect that depend on its types only

The functions below take the dialect as a parameter and recurse on a list or a count, so
their instances at the two dialects are equal by induction. -/

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The append of two vectors of the two dialects is the same function. -/
theorem hvAppend_left {f : T → Type} :
    ∀ {xs ys : List T} (A : HVector f xs) (B : HVector f ys),
      hvAppend (d := (opsVia O₁ O₂ T)) A B = hvAppend (d := (opsOver O₁ T)) A B
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons a A, B => congrArg (HVector.cons a) (hvAppend_left A B)

omit [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] in
/-- The exit-flag iteration of the two dialects is the same function. -/
theorem whileIter_left {cs : List T}
    (step : Valuation (d := (opsVia O₁ O₂ T)) cs →
      Option (Valuation (d := (opsVia O₁ O₂ T)) (HasBitType.bit (d := (opsVia O₁ O₂ T)) :: cs))) :
    ∀ (n : Nat) (acc : Valuation (d := (opsVia O₁ O₂ T)) cs),
      NFProg.whileIter (d := (opsVia O₁ O₂ T)) step n acc
        = NFProg.whileIter (d := (opsOver O₁ T)) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show (step acc >>= fun r => if HasBoolBit.toBool (d := (opsOver O₁ T)) r.head
          then NFProg.whileIter (d := (opsVia O₁ O₂ T)) step n r.tail else some r.tail)
        = (step acc >>= fun r => if HasBoolBit.toBool (d := (opsOver O₁ T)) r.head
          then NFProg.whileIter (d := (opsOver O₁ T)) step n r.tail else some r.tail)
      simp only [whileIter_left step n]

omit [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The counted iteration with events of the two dialects is the same function. -/
theorem forIterLeak_left {cs : List T}
    (step : Nat → Valuation (d := (opsVia O₁ O₂ T)) cs →
      Option (Valuation (d := (opsVia O₁ O₂ T)) cs × List CTLeak)) :
    ∀ (is : List Nat) (acc : Valuation (d := (opsVia O₁ O₂ T)) cs),
      forIterLeak (d := (opsVia O₁ O₂ T)) step is acc
        = forIterLeak (d := (opsOver O₁ T)) step is acc
  | [], _ => rfl
  | i :: is, acc => by
      show ((step i acc).bind fun r =>
          (forIterLeak (d := (opsVia O₁ O₂ T)) step is r.1).map fun q => (q.1, r.2 ++ q.2))
        = ((step i acc).bind fun r =>
          (forIterLeak (d := (opsOver O₁ T)) step is r.1).map fun q => (q.1, r.2 ++ q.2))
      simp only [forIterLeak_left step is]

omit [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] in
/-- The exit-flag iteration with events of the two dialects is the same function. -/
theorem whileIterLeak_left {cs : List T}
    (step : Valuation (d := (opsVia O₁ O₂ T)) cs →
      Option (Valuation (d := (opsVia O₁ O₂ T)) (HasBitType.bit (d := (opsVia O₁ O₂ T)) :: cs)
        × List CTLeak)) :
    ∀ (n : Nat) (acc : Valuation (d := (opsVia O₁ O₂ T)) cs),
      whileIterLeak (d := (opsVia O₁ O₂ T)) step n acc
        = whileIterLeak (d := (opsOver O₁ T)) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := (opsOver O₁ T)) r.1.head then
            (whileIterLeak (d := (opsVia O₁ O₂ T)) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
        = ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := (opsOver O₁ T)) r.1.head then
            (whileIterLeak (d := (opsOver O₁ T)) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
      simp only [whileIterLeak_left step n]

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The level of a variable read in the other dialect is its level. -/
theorem lvlOf_cast :
    ∀ {Γ : List T} {t : T} (v : Var (d := (opsOver O₁ T)) Γ t)
      (L : Labels (d := (opsOver O₁ T)) Γ),
      lvlOf (d := (opsVia O₁ O₂ T)) (castVar v) L = lvlOf v L
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ L => lvlOf_cast v L

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The levels of arguments read in the other dialect are their levels. -/
theorem argLvls_cast {Γ : List T} (L : Labels (d := (opsOver O₁ T)) Γ) :
    ∀ {ts : List T} (args : HVector (fun t => Var (d := (opsOver O₁ T)) Γ t) ts),
      argLvls (d := (opsVia O₁ O₂ T)) L (castArgs args) = argLvls L args
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ List.cons (lvlOf_cast v L) (argLvls_cast L vs)

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The levels of returned variables read in the other dialect are their levels. -/
theorem retLvls_cast {Γ : List T} (L : Labels (d := (opsOver O₁ T)) Γ) :
    ∀ {ts : List T} (vs : HVector (fun t => Var (d := (opsOver O₁ T)) Γ t) ts),
      retLvls (d := (opsVia O₁ O₂ T)) L (castArgs vs) = retLvls L vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => congrArg₂ HVector.cons (lvlOf_cast v L) (retLvls_cast L vs)

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The pointwise order of levels of the two dialects is the same function. -/
theorem lvlsLe_left : ∀ {cs : List T} (A B : Labels (d := (opsVia O₁ O₂ T)) cs),
    lvlsLe (d := (opsVia O₁ O₂ T)) A B = lvlsLe (d := (opsOver O₁ T)) A B
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => congrArg (lvlLe a b && ·) (lvlsLe_left A B)

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The all-secret levels of the two dialects are the same. -/
theorem allSecret_left : ∀ (cs : List T),
    allSecret (d := (opsVia O₁ O₂ T)) cs = allSecret (d := (opsOver O₁ T)) cs
  | [] => rfl
  | _ :: cs => by
      show HVector.cons SecretLevel.Secret (allSecret (d := (opsVia O₁ O₂ T)) cs)
        = HVector.cons SecretLevel.Secret (allSecret (d := (opsOver O₁ T)) cs)
      rw [allSecret_left cs]

omit [TyDenote T] [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] [HasBoolBit (opsOver O₁ T)] in
/-- The pointwise join of levels of the two dialects is the same function. -/
theorem lvlJoin_left : ∀ {cs : List T} (A B : Labels (d := (opsVia O₁ O₂ T)) cs),
    lvlJoin (d := (opsVia O₁ O₂ T)) A B = lvlJoin (d := (opsOver O₁ T)) A B
  | [], .nil, .nil => rfl
  | _ :: _, .cons a A, .cons b B => by
      show HVector.cons (a.join b) (lvlJoin (d := (opsVia O₁ O₂ T)) A B)
        = HVector.cons (a.join b) (lvlJoin (d := (opsOver O₁ T)) A B)
      rw [lvlJoin_left A B]

omit [DialectSignature (opsOver O₁ T)] [DialectSignature (opsVia O₁ O₂ T)]
  [HasWord64 (opsOver O₁ T)] in
/-- The condition on the levels of an exit-flag loop body of the two dialects is the same
    function. -/
theorem flagOk_left {cs : List T}
    (FB : Labels (d := (opsVia O₁ O₂ T)) (HasBitType.bit (d := (opsVia O₁ O₂ T)) :: cs))
    (A : Labels (d := (opsVia O₁ O₂ T)) cs) :
    flagOk (d := (opsVia O₁ O₂ T)) FB A = flagOk (d := (opsOver O₁ T)) FB A :=
  congrArg (decide (FB.head = .Public) && ·) (lvlsLe_left FB.tail A)

variable (f : ∀ {Γ : List T} {t : T}, Expr (opsOver O₁ T) Γ t → Expr (opsVia O₁ O₂ T) Γ t)

/-! ## 4. The denotation -/

section Denote

variable [DL : DialectDenoteM (opsOver O₁ T) Option]
  [DS : DialectDenoteM (opsVia O₁ O₂ T) Option]
  [CL : CallDenote (opsOver O₁ T)] [CS : CallDenote (opsVia O₁ O₂ T)]

/-- **The translation preserves the denotation**: a translated program denotes, at every
    fuel and valuation, what the program denotes, when every translated expression denotes
    as the expression and the two call environments agree. -/
theorem relabel_denote
    (hD : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t)
      (V : Valuation (d := (opsOver O₁ T)) Γ),
      (f e).denoteM (M := Option) V = e.denoteM (M := Option) V)
    (hC : ∀ (g : String) (as rs : List T) (args : Valuation (d := (opsOver O₁ T)) as),
      CS.env.call g as rs args = CL.env.call g as rs args)
    (fuel : Nat) {Γ : Ctxt (opsOver O₁ T)} {ts : List T} (p : NFProg (opsOver O₁ T) Γ ts)
    (V : Valuation Γ) :
    (relabel f p).denote fuel V = p.denote fuel V := by
  induction p with
  | ret vs => exact congrArg some (lookupArgs_castArgs vs V)
  | var e k ih =>
      simp only [relabel, NFProg.denote, hD, ih]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [relabel, NFProg.denote, ihb, ihk, lookupArgs_castArgs, lookup_castVar,
        hvAppend_left]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [relabel, NFProg.denote, iht, ihe, ihk, lookup_castVar, hvAppend_left]
      rfl
  | whileLoop inits body k ihb ihk =>
      simp only [relabel, NFProg.denote, ihb, ihk, lookupArgs_castArgs, hvAppend_left,
        whileIter_left]
  | call g args k ih =>
      simp only [relabel, NFProg.denote, ih, lookupArgs_castArgs, hvAppend_left, hC]

end Denote

/-! ## 5. The leakage run and the level checker -/

section Leak

variable (ML : LeakModel (opsOver O₁ T)) (MS : LeakModel (opsVia O₁ O₂ T))

section Run

variable [DL : DialectDenoteM (opsOver O₁ T) Option]
  [DS : DialectDenoteM (opsVia O₁ O₂ T) Option]

/-- **The translation preserves the leakage run**: a translated program runs, at every fuel
    and valuation, to the results and the events of the program, when every translated
    expression denotes as the expression and emits its events. -/
theorem relabel_leakRunM
    (hD : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t)
      (V : Valuation (d := (opsOver O₁ T)) Γ),
      (f e).denoteM (M := Option) V = e.denoteM (M := Option) V)
    (hE : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t)
      (V : Valuation (d := (opsOver O₁ T)) Γ), Expr.ctLeak MS (f e) V = Expr.ctLeak ML e V)
    (fuel : Nat) {Γ : Ctxt (opsOver O₁ T)} {ts : List T} (p : NFProg (opsOver O₁ T) Γ ts)
    (V : Valuation Γ) :
    NFProg.leakRunM MS fuel (relabel f p) V = NFProg.leakRunM ML fuel p V := by
  induction p with
  | ret vs => exact congrArg (fun x => some (x, [])) (lookupArgs_castArgs vs V)
  | var e k ih =>
      simp only [relabel, NFProg.leakRunM, hD, hE, ih]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [relabel, NFProg.leakRunM, ihb, ihk, lookupArgs_castArgs, lookup_castVar,
        hvAppend_left, forIterLeak_left]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [relabel, NFProg.leakRunM, iht, ihe, ihk, lookup_castVar, hvAppend_left]
      rfl
  | whileLoop inits body k ihb ihk =>
      simp only [relabel, NFProg.leakRunM, ihb, ihk, lookupArgs_castArgs, hvAppend_left,
        whileIterLeak_left]
  | call g args k => rfl

end Run

/-- **The translation keeps the result of the level checker**, when a translated
    expression has the constraint and the argument levels of the expression. -/
theorem relabel_levelCheck'
    (hA : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t) (ls : List SecretLevel),
      opAccepts MS (f e).op ls = opAccepts ML e.op ls)
    (hL : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t)
      (L : Labels (d := (opsOver O₁ T)) Γ),
      argLvls (d := (opsVia O₁ O₂ T)) L (f e).args = argLvls L e.args)
    {Γ : Ctxt (opsOver O₁ T)} {ts : List T} (p : NFProg (opsOver O₁ T) Γ ts) (L : Labels Γ) :
    NFProg.levelCheck' MS (relabel f p) L = NFProg.levelCheck' ML p L := by
  induction p with
  | ret vs => with_unfolding_all exact congrArg some (retLvls_cast L vs)
  | var e k ih =>
      simp only [relabel, NFProg.levelCheck', ih, hA, hL]
  | forLoop count inits body k ihb ihk =>
      simp only [relabel, NFProg.levelCheck', ihb, ihk, hvAppend_left, lvlsLe_left,
        allSecret_left]
      rw [lvlOf_cast count L, retLvls_cast L inits]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [relabel, NFProg.levelCheck', iht, ihe, ihk, hvAppend_left, lvlJoin_left]
      rw [lvlOf_cast cond L]
      rcases NFProg.levelCheck' ML thn L with _ | R₁ <;>
        rcases NFProg.levelCheck' ML els L with _ | R₂ <;> rfl
  | whileLoop inits body k ihb ihk =>
      simp only [relabel, NFProg.levelCheck', ihb, ihk, hvAppend_left, flagOk_left,
        allSecret_left]
      rw [retLvls_cast L inits]
      rfl
  | call g args k => with_unfolding_all rfl

/-- A translated program the level checker accepts in the source dialect is constant time
    in the target dialect relative to its runs. -/
theorem relabel_nfCTRel [DS : DialectDenoteM (opsVia O₁ O₂ T) Option]
    (hA : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t) (ls : List SecretLevel),
      opAccepts MS (f e).op ls = opAccepts ML e.op ls)
    (hL : ∀ {Γ : List T} {t : T} (e : Expr (opsOver O₁ T) Γ t)
      (L : Labels (d := (opsOver O₁ T)) Γ),
      argLvls (d := (opsVia O₁ O₂ T)) L (f e).args = argLvls L e.args)
    (fuel : Nat) {Γ : Ctxt (opsOver O₁ T)} {ts : List T} (p : NFProg (opsOver O₁ T) Γ ts)
    (L : Labels Γ) (h : (NFProg.levelCheck' ML p L).isSome) :
    NFCTRel MS L fuel (relabel f p) :=
  NFProg.nfCTRel_of_levelCheck' MS fuel _ L
    ((relabel_levelCheck' f ML MS hA hL p L).symm ▸ h)

end Leak

end Generic

/-! ## 6. Programs of `jasminDialect` in `jasminVec` -/

/-- An expression of `jasminDialect` as an expression of `jasminVec`: the operation tagged
    `.inl`, the arguments unchanged. -/
def scalarExpr {Γ : List JasminTy} {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminVec Γ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := castArgs e.args

/-- A scalar expression denotes in `jasminVec` what it denotes in `jasminDialect`. -/
theorem scalarExpr_denoteM {Γ : List JasminTy} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Valuation (d := jasminDialect) Γ) :
    @Expr.denoteM jasminVec Option _ _ jasminVecDenote Γ t (scalarExpr e) V
      = e.denoteM (M := Option) V := by
  obtain ⟨op, rfl, args⟩ := e
  show some (DialectDenote.denote (d := jasminDialect) op
      (Expr.lookupArgs (d := jasminVec) (castArgs args) V)) = _
  rw [lookupArgs_castArgs args V]
  rfl

/-- A scalar expression emits in `jasminVec` the events it emits in `jasminDialect`. -/
theorem scalarExpr_ctLeak (M : LeakModel jasminDialect) {Γ : List JasminTy} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Valuation (d := jasminDialect) Γ) :
    Expr.ctLeak (jasminVecLeak M) (scalarExpr e) V = Expr.ctLeak M e V := by
  show opLeak (jasminVecLeak M) (.inl e.op)
      (Expr.lookupArgs (d := jasminVec) (castArgs e.args) V) = _
  rw [lookupArgs_castArgs e.args V, jasminVec_opLeak_inl]
  rfl

/-- A program of `jasminDialect` as a program of `jasminVec`: every let-bound operation
    tagged as a scalar operation, the regions kept. -/
def scalarProg {Γ : Ctxt jasminVec} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminVec Γ ts :=
  relabel (O₁ := JasminOp) (O₂ := JasminOp ⊕ X86VecOp) (T := JasminTy) scalarExpr p

/-- **A scalar program denotes in `jasminVec` what it denotes in `jasminDialect`**, at
    every fuel and valuation. -/
theorem scalarProg_denote (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    jasminVecDenP fuel (scalarProg p) V = p.denote fuel V :=
  relabel_denote (O₁ := JasminOp) (O₂ := JasminOp ⊕ X86VecOp) (T := JasminTy) scalarExpr
    (DS := jasminVecDenote) (CS := instCallDenoteJasminVec) scalarExpr_denoteM
    (fun _ _ _ _ => rfl) fuel p V

/-- **A scalar program runs in `jasminVec` to the results and the events of its run in
    `jasminDialect`.** -/
theorem scalarProg_leakRun (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminVec}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    jasminVecLeakRun M fuel (scalarProg p) V = NFProg.leakRun M fuel p V := by
  rw [← NFProg.leakRunM_eq_leakRun M fuel p V]
  exact (NFProg.leakRunM_eq_leakRun (jasminVecLeak M) fuel (scalarProg p) V).symm.trans
    (relabel_leakRunM (O₁ := JasminOp) (O₂ := JasminOp ⊕ X86VecOp) (T := JasminTy) scalarExpr
      M (jasminVecLeak M) (DS := jasminVecDenote) scalarExpr_denoteM (scalarExpr_ctLeak M)
      fuel p V)

/-- **The level checker returns on a scalar program in `jasminVec` what it returns in
    `jasminDialect`.** -/
theorem scalarProg_levelCheck' (M : LeakModel jasminDialect) {Γ : Ctxt jasminVec}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (L : Labels Γ) :
    NFProg.levelCheck' (jasminVecLeak M) (scalarProg p) L = NFProg.levelCheck' M p L :=
  relabel_levelCheck' (O₁ := JasminOp) (O₂ := JasminOp ⊕ X86VecOp) (T := JasminTy) scalarExpr
    M (jasminVecLeak M) (fun _ _ => rfl) (fun e L => argLvls_cast L e.args) p L

/-- A scalar program the level checker accepts in `jasminDialect` is constant time in
    `jasminVec` relative to its runs. -/
theorem scalarProg_nfCTRel (M : LeakModel jasminDialect) (fuel : Nat) {Γ : Ctxt jasminVec}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (L : Labels Γ)
    (h : (NFProg.levelCheck' M p L).isSome) :
    NFCTRel (jasminVecLeak M) L fuel (scalarProg p) :=
  jasminVec_nfCTRel_of_levelCheck' M fuel _ L ((scalarProg_levelCheck' M p L).symm ▸ h)

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecEmbed
