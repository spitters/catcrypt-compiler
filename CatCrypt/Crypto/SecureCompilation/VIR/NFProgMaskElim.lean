/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NarrowWordSquares
public import CatCrypt.Crypto.SecureCompilation.VIR.Transforms.NFIfToSelect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap

/-!
# Elimination of masks whose value reaches only width-insensitive operations

A *mask* of width `m` is a binding `and x c` at width `64` whose second argument `c` is bound
by the constant `2 ^ m - 1` (`maskOf?`). The widening `widenJ` emits a mask after every
addition, subtraction, multiplication and left shift at a narrow width. A mask is redundant
when its value is read only by operations whose low `m` bits depend only on the low `m` bits
of their arguments (addition, subtraction, multiplication, the bitwise operations and the
left shift by an immediate, at width `64`; `insens`), and the values of those operations in
turn only by such operations and by masks of width at most `m`: these are the squares of
`NarrowWordSquares` (the lazy relation `x.setWidth m = v`).

The analysis assigns each variable an `Info`: `exact` (the value is that of the source),
`const n` (in addition, it is the constant `n`), or `relaxed w` (only the low `w` bits are
those of the source). `okE` gives the information of a binding: a mask of width `m` of an
argument relaxed at a width of at least `m` is exact, an insensitive operation of relaxed
arguments is relaxed at the least of their widths, a constant at width `64` is a constant, and
every other operation must read only arguments that are not relaxed. `okP` checks this at every
binding, return, region argument and call argument of a program.

`maskElimGo p A ren` removes each mask of width `m` whose continuation passes `okP` with the
mask relaxed at `m`, and lets its uses read the image of its first argument under the
renaming; every other binding is kept. `denoteAt_maskElimGo` states that, when the facts relate
the source valuation and the target valuation along the renaming (`MRel`), the pass denotes
at the target what the source denotes. `maskElim p` starts with no relaxed variable, where
`okP` holds of every program (`okP_of_noRelax`), and preserves the denotation
(`denoteAt_maskElim`).

## Main definitions

* `Info`, `Facts`, `Facts.push`, `Facts.appExact` — the information of the variables.
* `maskWidth?`, `insens`, `okOp`, `okE`, `okP` — the analysis.
* `maskOf?`, `maskElimGo`, `maskElim` — the pass.
* `rel`, `MRel` — the relation of a source and a target valuation.

## Main results

* `okE_sound` — the binding of an expression `okE` accepts relates the source and target
  values by the information it gives.
* `denoteAt_maskElimGo`, `denoteAt_maskElim` — the pass preserves the denotation.
* `maskElimGo_var_mask` — a mask whose continuation passes `okP` with the mask relaxed is not
  in the output; `maskElimGo_var_keep` — every other binding is.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open Transfer
open CatCrypt.Crypto.SecureCompilation.VIR.NFProg (Agrees agrees_lift appLift agrees_appLift
  bindHom varTyCast lookup_varTyCast)

/-! ## 1. The information of a variable -/

/-- The information of a variable: its value is that of the source (`exact`), it is in
    addition the constant `n` at width `64` (`const n`), or only its low `w` bits are those of
    the source (`relaxed w`). -/
inductive Info where
  | exact
  | const (n : Nat)
  | relaxed (w : Nat)
  deriving DecidableEq

/-- The width at which a variable is relaxed. -/
def Info.relW : Info → Option Nat
  | .relaxed w => some w
  | _ => none

/-- The information of the variables of a context. -/
abbrev Facts (Γ : Ctxt jasminDialect) : Type := ∀ {s : JasminTy}, Var Γ s → Info

/-- The facts of a context extended by one binding of information `i`. -/
def Facts.push {Γ : Ctxt jasminDialect} {t : JasminTy} (i : Info) (A : Facts Γ) :
    Facts (t :: Γ) :=
  fun v => match v with
    | .here => i
    | .there v => A v

/-- The facts of a context extended by the prefix `cs`, exact on the prefix. -/
def Facts.appExact {Γ : Ctxt jasminDialect} :
    (cs : List JasminTy) → Facts Γ → Facts (cs ++ Γ)
  | [], A => A
  | _ :: cs, A => Facts.push .exact (Facts.appExact cs A)

/-- No argument of the vector is relaxed. -/
def allExactB {Γ : Ctxt jasminDialect} (A : Facts Γ) :
    {ts : List JasminTy} → HVector (fun t => Var Γ t) ts → Bool
  | [], .nil => true
  | _ :: _, .cons v vs => (A v).relW.isNone && allExactB A vs

/-- The width `m` of a constant `2 ^ m - 1` with `m ≤ 64`. -/
def maskWidth? : Info → Option Nat
  | .const n => if 2 ^ Nat.log2 (n + 1) = n + 1 ∧ Nat.log2 (n + 1) ≤ 64 then
      some (Nat.log2 (n + 1)) else none
  | _ => none

/-- The binary operations whose low bits depend only on the low bits of their arguments. -/
def insens : JasminBinOp → Bool
  | .add | .sub | .mul | .and | .or | .xor | .andn => true
  | .shl | .shr => false

/-- The information of an insensitive operation of two arguments: relaxed at the least of
    their widths. -/
def meet (i j : Info) : Info :=
  match i.relW, j.relW with
  | none, none => .exact
  | some a, none => .relaxed a
  | none, some b => .relaxed b
  | some a, some b => .relaxed (min a b)

/-- The information of a mask of width `m` of an argument of information `i`: exact when the
    argument is relaxed at a width of at least `m`. -/
def maskInfo (i : Info) (m : Nat) : Option Info :=
  match i.relW with
  | none => some .exact
  | some a => if m ≤ a then some .exact else none

/-- The information of an operation that reads only arguments that are not relaxed. -/
def exactOp {Γ : Ctxt jasminDialect} (A : Facts Γ) {ts : List JasminTy}
    (args : HVector (fun t => Var Γ t) ts) : Option Info :=
  if allExactB A args then some .exact else none

/-- **The analysis of an operation.** -/
def okOp {Γ : Ctxt jasminDialect} (A : Facts Γ) : (op : JasminOp) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op) → Option Info
  | .regArith bop w, args =>
      if w = 64 then
        match bop, maskWidth? (A args.tail.head) with
        | .and, some m => maskInfo (A args.head) m
        | _, _ => if insens bop then some (meet (A args.head) (A args.tail.head))
            else exactOp A args
      else exactOp A args
  | .shlImm w _, args => if w = 64 then some (meet (A args.head) .exact) else exactOp A args
  | .regConst w n, _ => some (if w = 64 then .const n else .exact)
  | _, args => exactOp A args

/-- The analysis of an expression. -/
def okE {Γ : Ctxt jasminDialect} {t : JasminTy} (A : Facts Γ) : Expr jasminDialect Γ t →
    Option Info
  | ⟨op, _, args⟩ => okOp A op args

/-- **The analysis of a program**: every binding passes `okE`, and every return, trip count,
    initial value, branch bit and call argument is not relaxed. -/
def okP : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts →
    Facts Γ → Bool
  | _, _, .ret vs, A => allExactB A vs
  | _, _, .var e k, A =>
      match okE A e with
      | some i => okP k (A.push i)
      | none => false
  | _, _, .forLoop (cs := cs) count inits body k, A =>
      (A count).relW.isNone && allExactB A inits &&
        okP body (Facts.appExact cs (A.push .exact)) && okP k (Facts.appExact cs A)
  | _, _, .ifThenElse (rs := rs) cond thn els k, A =>
      (A cond).relW.isNone && okP thn A && okP els A && okP k (Facts.appExact rs A)
  | _, _, .whileLoop (cs := cs) inits body k, A =>
      allExactB A inits && okP body (Facts.appExact cs A) && okP k (Facts.appExact cs A)
  | _, _, .call (rs := rs) _ args k, A => allExactB A args && okP k (Facts.appExact rs A)

/-! ## 2. The pass -/

/-- The first argument and the width of a mask, with the result type `reg 64`. -/
def maskOf? {Γ : Ctxt jasminDialect} {t : JasminTy} (A : Facts Γ) :
    Expr jasminDialect Γ t → Option {_p : Var Γ (.reg 64) × Nat // t = .reg 64}
  | ⟨op, h, args⟩ =>
      match op, h, args with
      | .regArith .and 64, h, args =>
          (maskWidth? (A args.tail.head)).map fun m => ⟨(args.head, m), h.symm⟩
      | _, _, _ => none

/-- **Mask elimination along a renaming.** A mask of width `m` whose continuation passes
    `okP` with the mask relaxed at `m` is removed, and its uses read the image of its first
    argument; every other binding is kept with the information `okE` gives it; the regions
    are entered with exact information on their new variables. -/
def maskElimGo : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Facts Γ → Ctxt.Hom Γ Δ → NFProg jasminDialect Δ ts
  | _, _, _, .ret vs, _, ren => .ret (HVector.renameVars ren vs)
  | _, _, _, .var e k, A, ren =>
      match maskOf? A e with
      | some ⟨(x, m), h⟩ =>
          if okP k (A.push (.relaxed m)) then
            maskElimGo k (A.push (.relaxed m)) (bindHom (.cons (varTyCast h.symm (ren x)) .nil) ren)
          else .var (e.rename ren) (maskElimGo k (A.push ((okE A e).getD .exact))
            (Ctxt.Hom.lift ren))
      | none => .var (e.rename ren) (maskElimGo k (A.push ((okE A e).getD .exact))
          (Ctxt.Hom.lift ren))
  | _, _, _, .forLoop (cs := cs) count inits body k, A, ren =>
      .forLoop (ren count) (HVector.renameVars ren inits)
        (maskElimGo body (Facts.appExact cs (A.push .exact)) (appLift cs (Ctxt.Hom.lift ren)))
        (maskElimGo k (Facts.appExact cs A) (appLift cs ren))
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, A, ren =>
      .ifThenElse (ren cond) (maskElimGo thn A ren) (maskElimGo els A ren)
        (maskElimGo k (Facts.appExact rs A) (appLift rs ren))
  | _, _, _, .whileLoop (cs := cs) inits body k, A, ren =>
      .whileLoop (HVector.renameVars ren inits) (maskElimGo body (Facts.appExact cs A)
        (appLift cs ren)) (maskElimGo k (Facts.appExact cs A) (appLift cs ren))
  | _, _, _, .call (rs := rs) f args k, A, ren =>
      .call f (HVector.renameVars ren args) (maskElimGo k (Facts.appExact rs A) (appLift rs ren))

/-- **Mask elimination**: `maskElimGo` with exact information everywhere, at the identity
    renaming. -/
def maskElim {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    NFProg jasminDialect Γ ts :=
  maskElimGo p (fun _ => .exact) (fun v => v)

/-- **A redundant mask is removed.** A mask of width `m` whose continuation passes `okP` with
    the mask relaxed at `m` (its value reaches only insensitive operations and masks of width
    at most `m`) has no binding in the output. -/
theorem maskElimGo_var_mask {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) (A : Facts Γ)
    (ren : Ctxt.Hom Γ Δ) (x : Var Γ (.reg 64)) (m : Nat) (h : t = .reg 64)
    (he : maskOf? A e = some ⟨(x, m), h⟩) (hk : okP k (A.push (.relaxed m)) = true) :
    maskElimGo (.var e k) A ren =
      maskElimGo k (A.push (.relaxed m)) (bindHom (.cons (varTyCast h.symm (ren x)) .nil) ren) := by
  simp only [maskElimGo, he, hk, ite_true]

/-- **Every other binding is kept.** -/
theorem maskElimGo_var_keep {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) (A : Facts Γ)
    (ren : Ctxt.Hom Γ Δ)
    (hk : ∀ x m h, maskOf? A e = some ⟨(x, m), h⟩ → okP k (A.push (.relaxed m)) = false) :
    maskElimGo (.var e k) A ren =
      .var (e.rename ren) (maskElimGo k (A.push ((okE A e).getD .exact)) (Ctxt.Hom.lift ren)) := by
  simp only [maskElimGo]
  split
  · rename_i x m h he
    simp only [hk x m h he, Bool.false_eq_true, ite_false]
  · rfl

/-! ## 3. The relation of the source and the target -/

/-- The relation of a source value `x` and a target value `y` under the information `i`:
    equal, or, at a register relaxed at `a`, equal in the low `a` bits. -/
def rel (i : Info) : {s : JasminTy} → ⟦s⟧ → ⟦s⟧ → Prop
  | .reg w, x, y => match i with
    | .relaxed a => a ≤ 64 ∧ BitVec.setWidth a (y : BitVec w) = BitVec.setWidth a (x : BitVec w)
    | _ => y = x
  | .stackArr _ _, x, y => y = x
  | .inlineInt, x, y => y = x
  | .bool, x, y => y = x

/-- The constant of the information holds of a source value. -/
def constOK (i : Info) : {s : JasminTy} → ⟦s⟧ → Prop
  | .reg w, x => match i with
    | .const n => (x : BitVec w) = BitVec.ofNat w n
    | _ => True
  | _, _ => True

/-- The facts `A` relate the source valuation `V` to the target valuation `W` along `ren`. -/
def MRel {Γ Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
    (W : Valuation Δ) : Prop :=
  ∀ {s : JasminTy} (v : Var Γ s), rel (A v) (v.lookup V) ((ren v).lookup W) ∧
    constOK (A v) (v.lookup V)

/-- Values related at information that is not relaxed are equal. -/
theorem rel_eq_of_relW {i : Info} (hi : i.relW = none) :
    {s : JasminTy} → {x y : ⟦s⟧} → rel i x y → y = x
  | .reg _, _, _, h => by cases i <;> simp_all [rel, Info.relW]
  | .stackArr _ _, _, _, h => h
  | .inlineInt, _, _, h => h
  | .bool, _, _, h => h

/-- A value is related to itself at exact information. -/
theorem rel_exact {s : JasminTy} (x : ⟦s⟧) : rel .exact x x := by
  cases s <;> rfl

/-- Exact information records no constant. -/
theorem constOK_exact {s : JasminTy} (x : ⟦s⟧) : constOK .exact x := by
  cases s <;> trivial

/-- An exact variable reads in the target what it reads in the source. -/
theorem MRel.lookup_ren_eq {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : MRel A ren V W) {s : JasminTy} (v : Var Γ s)
    (hv : (A v).relW = none) : (ren v).lookup W = v.lookup V :=
  rel_eq_of_relW hv (h v).1

/-- Arguments that are not relaxed read in the target what they read in the source. -/
theorem MRel.lookupArgs_eq {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : MRel A ren V W) :
    {ts : List JasminTy} → (args : HVector (fun t => Var Γ t) ts) → allExactB A args = true →
    Expr.lookupArgs (HVector.renameVars ren args) W = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v vs, hv => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hv
      change HVector.cons _ _ = HVector.cons _ _
      rw [h.lookup_ren_eq v (Option.isNone_iff_eq_none.mp h1), h.lookupArgs_eq vs h2]

/-- The relation extended by one binding. -/
theorem MRel.push {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : MRel A ren V W) {t : JasminTy} {i : Info}
    {x y : ⟦t⟧} (hxy : rel i x y) (hc : constOK i x) :
    MRel (A.push i) (Ctxt.Hom.lift ren) (V.extend x) (W.extend y)
  | _, .here => ⟨hxy, hc⟩
  | _, .there v => h v

/-- The relation extended by one binding read at a target variable. -/
theorem MRel.bind {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : MRel A ren V W) {t : JasminTy} {i : Info}
    {x : ⟦t⟧} (z : Var Δ t) (hxy : rel i x (z.lookup W)) (hc : constOK i x) :
    MRel (A.push i) (bindHom (.cons z .nil) ren) (V.extend x) W
  | _, .here => ⟨hxy, hc⟩
  | _, .there v => h v

/-- The relation extended by a prefix of equal values with exact information. -/
theorem MRel.appExact {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : MRel A ren V W) :
    (cs : List JasminTy) → (acc : Valuation (d := jasminDialect) cs) →
    MRel (Facts.appExact cs A) (appLift cs ren) (hvAppend acc V) (hvAppend acc W)
  | [], .nil => h
  | _ :: cs, .cons a acc => MRel.push (MRel.appExact h cs acc) (rel_exact a) (constOK_exact a)

/-! ## 4. The analysis is sound -/

/-- Two 64-bit values related by `i` agree in the low `m` bits when `i` is not relaxed below
    `m`. -/
theorem rel_low {i : Info} {x y : BitVec 64} (h : rel i (s := .reg 64) x y) {m : Nat}
    (hm : ∀ a, i.relW = some a → m ≤ a) : lowW m y = lowW m x := by
  cases i with
  | relaxed a =>
      obtain ⟨_, h⟩ := h
      have := hm a rfl
      simp only [lowW]
      rw [← BitVec.setWidth_setWidth_of_le y this, h, BitVec.setWidth_setWidth_of_le x this]
  | exact => cases h; rfl
  | const n => cases h; rfl

/-- The low bits of an operation with a square depend only on the low bits of its arguments. -/
theorem low_congr {c : Nat} {op op' : BitVec 64 → BitVec 64 → BitVec 64}
    {op'' : BitVec c → BitVec c → BitVec c} (hop : RelatedBinOp (lowW c) op op'')
    (hop' : op' = op) {x1 x2 y1 y2 : BitVec 64} (h1 : lowW c y1 = lowW c x1)
    (h2 : lowW c y2 = lowW c x2) : lowW c (op' y1 y2) = lowW c (op x1 x2) := by
  subst hop'
  rw [hop.comm, hop.comm, h1, h2]

/-- The low bits of an insensitive operation depend only on the low bits of its arguments. -/
theorem insens_low {bop : JasminBinOp} (hb : insens bop = true) {c : Nat} (hc : c ≤ 64)
    {x1 x2 y1 y2 : BitVec 64} (h1 : lowW c y1 = lowW c x1) (h2 : lowW c y2 = lowW c x2) :
    lowW c (bop.apply y1 y2) = lowW c (bop.apply x1 x2) := by
  have : WordLe64 c := ⟨hc⟩
  cases bop <;> simp only [insens, Bool.false_eq_true] at hb
  · exact low_congr (addSq (w := c)) rfl h1 h2
  · exact low_congr (subSq (w := c)) rfl h1 h2
  · exact low_congr (mulSq (w := c)) rfl h1 h2
  · exact low_congr (andSq (w := c)) rfl h1 h2
  · exact low_congr (orSq (w := c)) rfl h1 h2
  · exact low_congr (xorSq (w := c)) rfl h1 h2
  · exact low_congr (andnSq (w := c)) rfl h1 h2

/-- A relaxed width of a related pair of registers is at most `64`. -/
theorem relW_le64 {i : Info} {x y : BitVec 64} (h : rel i (s := .reg 64) x y) :
    ∀ a, i.relW = some a → a ≤ 64 := by
  cases i <;> simp only [Info.relW, reduceCtorEq, Option.some.injEq, false_imp_iff,
    implies_true]
  rintro a rfl
  exact h.1

/-- An insensitive operation of related arguments is related by `meet`. -/
theorem meet_rel {bop : JasminBinOp} (hb : insens bop = true) {i j : Info}
    {x1 x2 y1 y2 : BitVec 64} (h1 : rel i (s := .reg 64) x1 y1)
    (h2 : rel j (s := .reg 64) x2 y2) :
    rel (meet i j) (s := .reg 64) (bop.apply x1 x2) (bop.apply y1 y2) := by
  have b1 := relW_le64 h1
  have b2 := relW_le64 h2
  unfold meet
  split
  · rename_i ha hb'
    rw [rel_eq_of_relW ha h1, rel_eq_of_relW hb' h2]
    rfl
  · rename_i a ha hb'
    refine ⟨b1 a ha, insens_low hb (b1 a ha) (rel_low h1 ?_) (rel_low h2 ?_)⟩
    · intro a' h; rw [ha] at h; cases h; exact Nat.le_refl _
    · intro a' h; rw [hb'] at h; cases h
  · rename_i b ha hb'
    refine ⟨b2 b hb', insens_low hb (b2 b hb') (rel_low h1 ?_) (rel_low h2 ?_)⟩
    · intro a' h; rw [ha] at h; cases h
    · intro a' h; rw [hb'] at h; cases h; exact Nat.le_refl _
  · rename_i a b ha hb'
    refine ⟨Nat.le_trans (Nat.min_le_left a b) (b1 a ha),
      insens_low hb (Nat.le_trans (Nat.min_le_left a b) (b1 a ha)) (rel_low h1 ?_)
        (rel_low h2 ?_)⟩
    · intro a' h; rw [ha] at h; cases h; exact Nat.min_le_left _ _
    · intro a' h; rw [hb'] at h; cases h; exact Nat.min_le_right _ _

/-- A constant of `maskWidth?` is the mask of its width. -/
theorem maskWidth?_spec {i : Info} {m : Nat} (h : maskWidth? i = some m) :
    i.relW = none ∧
      ∀ x : BitVec 64, constOK i (s := .reg 64) x → x = maskW m ∧ m ≤ 64 := by
  cases i with
  | const n =>
      simp only [maskWidth?] at h
      split at h
      · rename_i hn
        cases h
        refine ⟨rfl, fun x hx => ⟨?_, hn.2⟩⟩
        simp only [constOK] at hx
        rw [hx, maskW, hn.1, Nat.add_sub_cancel]
      · cases h
  | exact => cases h
  | relaxed _ => cases h

/-- **Soundness of the analysis at an operation.** -/
theorem okOp_sound {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (hR : MRel A ren V W) (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    {i : Info} (h : okOp A op args = some i) :
    rel i (Expr.denote (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V)
        (Expr.denote (⟨op, rfl, HVector.renameVars ren args⟩ : Expr jasminDialect Δ _) W) ∧
      constOK i (Expr.denote (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V) := by
  have hex : ∀ {ts : List JasminTy} (as : HVector (fun t => Var Γ t) ts),
      exactOp A as = some i → i = .exact ∧ allExactB A as = true := by
    intro ts as h
    unfold exactOp at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h
  have gen : exactOp A args = some i →
      rel i (Expr.denote (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V)
        (Expr.denote (⟨op, rfl, HVector.renameVars ren args⟩ : Expr jasminDialect Δ _) W) ∧
      constOK i (Expr.denote (⟨op, rfl, args⟩ : Expr jasminDialect Γ _) V) := by
    intro h'
    obtain ⟨rfl, ha⟩ := hex args h'
    have hl := hR.lookupArgs_eq args ha
    change rel .exact _ (DialectDenote.denote op (Expr.lookupArgs (HVector.renameVars ren args) W))
      ∧ _
    rw [hl]
    exact ⟨rel_exact _, constOK_exact _⟩
  cases op
  case regArith bop w =>
    simp only [okOp] at h
    split at h
    · rename_i hw
      subst hw
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      have ha := hR a
      have hb := hR b
      simp only [HVector.head, HVector.tail] at h
      split at h
      · rename_i m hm
        obtain ⟨hbe, hbm⟩ := maskWidth?_spec hm
        have hbv := hbm _ hb.2
        have hbeq := hR.lookup_ren_eq b hbe
        simp only [maskInfo] at h
        refine ⟨?_, ?_⟩
        · change rel i (s := .reg 64) (JasminBinOp.apply .and (a.lookup V) (b.lookup V))
            (JasminBinOp.apply .and ((ren a).lookup W) ((ren b).lookup W))
          have hmk : ∀ X : BitVec 64, JasminBinOp.apply .and X (maskW m) =
              (lowW m X).setWidth 64 := fun X => and_maskW hbv.2 X
          rw [hbeq, hbv.1, hmk, hmk]
          split at h
          · rename_i hn
            cases h
            change _ = _
            rw [rel_eq_of_relW hn ha.1]
          · rename_i a' ha'
            split at h
            · rename_i hle
              cases h
              change _ = _
              rw [rel_low ha.1 (fun a'' h'' => by rw [ha'] at h''; cases h''; exact hle)]
            · cases h
        · split at h
          · cases h; trivial
          · split at h
            · cases h; trivial
            · cases h
      · split at h
        · rename_i hins
          cases h
          exact ⟨meet_rel hins ha.1 hb.1, by
            unfold meet; split <;> trivial⟩
        · exact gen h
    · exact gen h
  case shlImm w k =>
    simp only [okOp] at h
    split at h
    · rename_i hw
      subst hw
      rcases args with _ | ⟨a, _ | _⟩
      have ha := hR a
      simp only [HVector.head] at h
      cases h
      refine ⟨?_, by unfold meet; split <;> trivial⟩
      change rel _ (s := .reg 64) (BitVec.shiftLeft (a.lookup V) (shiftMask 64 k))
        (BitVec.shiftLeft ((ren a).lookup W) (shiftMask 64 k))
      have b1 := relW_le64 ha.1
      unfold meet
      split
      · rename_i hn _
        change _ = _
        rw [rel_eq_of_relW hn ha.1]
      · rename_i c hc _
        have : WordLe64 c := ⟨b1 c hc⟩
        refine ⟨b1 c hc, ?_⟩
        change lowW c _ = lowW c _
        have hs : ∀ (X : BitVec 64) (n : Nat), lowW c (BitVec.shiftLeft X n) =
            BitVec.shiftLeft (lowW c X) n := fun X n => (shlImmSq (w := c) n).comm X
        rw [hs, hs, rel_low ha.1 (fun a' h' => by rw [hc] at h'; cases h'; exact Nat.le_refl _)]
      · rename_i _ h2; cases h2
      · rename_i _ _ _ h2; cases h2
    · exact gen h
  case regConst w n =>
    simp only [okOp, Option.some.injEq] at h
    subst h
    split
    · rename_i hw
      subst hw
      exact ⟨rfl, rfl⟩
    · exact ⟨rfl, trivial⟩
  all_goals exact gen h

/-- **Soundness of the analysis.** The binding of an expression that `okE` accepts relates
    the source value and the target value of the renamed expression by the information
    `okE` gives, and the constant of the information holds of the source value. -/
theorem okE_sound {Γ Δ : Ctxt jasminDialect} {t : JasminTy} {A : Facts Γ}
    {ren : Ctxt.Hom Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (hR : MRel A ren V W)
    (e : Expr jasminDialect Γ t) {i : Info} (h : okE A e = some i) :
    rel i (e.denote V) ((e.rename ren).denote W) ∧ constOK i (e.denote V) := by
  obtain ⟨op, rfl, args⟩ := e
  exact okOp_sound hR op args h

/-- The target of a removed mask, the image of its first argument, holds the low bits of the
    source value of the mask. -/
theorem maskOf?_rel {Γ Δ : Ctxt jasminDialect} {A : Facts Γ} {ren : Ctxt.Hom Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (hR : MRel A ren V W)
    (e : Expr jasminDialect Γ (.reg 64))
    {x : Var Γ (.reg 64)} {m : Nat} {h : (JasminTy.reg 64) = .reg 64}
    (he : maskOf? A e = some ⟨(x, m), h⟩) {i : Info} (hi : okE A e = some i) :
    rel (.relaxed m) (s := .reg 64) (e.denote V) ((ren x).lookup W) := by
  obtain ⟨op, hty, args⟩ := e
  cases op
  case regArith bop w =>
    cases hty
    cases bop <;> simp only [maskOf?, reduceCtorEq] at he
    rcases args with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
    simp only [HVector.head, HVector.tail, Option.map_eq_some_iff, Subtype.mk.injEq,
      Prod.mk.injEq] at he
    obtain ⟨m', hm, rfl, rfl⟩ := he
    simp only [okE, okOp, ite_true, HVector.head, HVector.tail, hm] at hi
    obtain ⟨hce, hcm⟩ := maskWidth?_spec hm
    have hcv := hcm _ (hR c).2
    refine ⟨hcv.2, ?_⟩
    have : WordLe64 m' := ⟨hcv.2⟩
    change lowW m' ((ren a).lookup W) = lowW m' (JasminBinOp.apply .and (a.lookup V) (c.lookup V))
    rw [hcv.1]
    refine (rel_low (hR a).1 ?_).trans ((maskSq (w := m')).comm _).symm
    intro a' ha'
    simp only [maskInfo, ha'] at hi
    split at hi
    · assumption
    · cases hi
  all_goals simp [maskOf?] at he

/-! ## 5. Preservation of the denotation -/

/-- **Preservation along a renaming.** When the facts `A` relate `V` to `W` along `ren` and
    the source passes `okP`, the pass denotes at `W`, at every call environment and fuel,
    what the source denotes at `V`. -/
theorem denoteAt_maskElimGo (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ) (V : Valuation Γ)
      (W : Valuation Δ), MRel A ren V W → okP p A = true →
      (maskElimGo p A ren).denoteAt E fuel W = p.denoteAt E fuel V := by
  induction p with
  | ret vs =>
      intro Δ A ren V W hR hok
      simp only [maskElimGo, NFProg.denoteAt, NFProg.denote, hR.lookupArgs_eq vs hok]
  | var e k ih =>
      intro Δ A ren V W hR hok
      simp only [okP] at hok
      split at hok
      · rename_i i hi
        have hkeep : (NFProg.var (e.rename ren)
            (maskElimGo k (A.push ((okE A e).getD .exact)) (Ctxt.Hom.lift ren))).denoteAt E fuel W =
            (NFProg.var e k).denoteAt E fuel V := by
          simp only [NFProg.denoteAt, NFProg.denote, Expr.denoteM_option_eq_some,
            Option.bind_eq_bind, Option.bind_some, hi, Option.getD_some]
          have hs := okE_sound hR e hi
          exact ih _ _ _ _ (MRel.push hR hs.1 hs.2) hok
        simp only [maskElimGo]
        split
        · rename_i x m h he
          split
          · rename_i hk
            subst h
            have hrel := maskOf?_rel hR e he hi
            rw [ih _ _ _ _ (MRel.bind hR (varTyCast rfl (ren x)) hrel trivial) hk]
            simp only [NFProg.denoteAt, NFProg.denote, Expr.denoteM_option_eq_some,
              Option.bind_eq_bind, Option.bind_some]
          · exact hkeep
        · exact hkeep
      · cases hok
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, hi⟩, hb⟩, hk⟩ := hok
      have hbd : ∀ acc i, (maskElimGo body (Facts.appExact _ (A.push .exact))
            (appLift _ (Ctxt.Hom.lift ren))).denoteAt E fuel
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
          body.denoteAt E fuel (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i => ihb _ _ _ _
          (MRel.appExact (MRel.push hR (rel_exact _) (constOK_exact _)) _ acc) hb
      have hkd : ∀ acc, (maskElimGo k (Facts.appExact _ A) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = k.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [NFProg.denoteAt] at hbd hkd
      simp only [maskElimGo, NFProg.denoteAt, NFProg.denote, hR.lookupArgs_eq inits hi,
        hR.lookup_ren_eq count hc, hbd, hkd]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true, Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨⟨hc, htn⟩, hel⟩, hk⟩ := hok
      have hkd : ∀ r, (maskElimGo k (Facts.appExact _ A) (appLift _ ren)).denoteAt E fuel
            (hvAppend r W) = k.denoteAt E fuel (hvAppend r V) :=
        fun r => ihk _ _ _ _ (MRel.appExact hR _ r) hk
      have ht := iht A ren V W hR htn
      have he := ihe A ren V W hR hel
      simp only [NFProg.denoteAt] at hkd ht he
      simp only [maskElimGo, NFProg.denoteAt, NFProg.denote, hR.lookup_ren_eq cond hc, ht, he, hkd]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨⟨hi, hb⟩, hk⟩ := hok
      have hbd : ∀ acc, (maskElimGo body (Facts.appExact _ A) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = body.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihb _ _ _ _ (MRel.appExact hR _ acc) hb
      have hkd : ∀ acc, (maskElimGo k (Facts.appExact _ A) (appLift _ ren)).denoteAt E fuel
            (hvAppend acc W) = k.denoteAt E fuel (hvAppend acc V) :=
        fun acc => ihk _ _ _ _ (MRel.appExact hR _ acc) hk
      simp only [NFProg.denoteAt] at hbd hkd
      simp only [maskElimGo, NFProg.denoteAt, NFProg.denote, hR.lookupArgs_eq inits hi, hbd, hkd]
  | call f args k ih =>
      intro Δ A ren V W hR hok
      simp only [okP, Bool.and_eq_true] at hok
      obtain ⟨ha, hk⟩ := hok
      have hkd : ∀ r, (maskElimGo k (Facts.appExact _ A) (appLift _ ren)).denoteAt E fuel
            (hvAppend r W) = k.denoteAt E fuel (hvAppend r V) :=
        fun r => ih _ _ _ _ (MRel.appExact hR _ r) hk
      simp only [NFProg.denoteAt] at hkd
      simp only [maskElimGo, NFProg.denoteAt, NFProg.denote, hR.lookupArgs_eq args ha, hkd]

/-! ## 6. The pass from exact information -/

/-- No variable is relaxed. -/
def NoRelax {Γ : Ctxt jasminDialect} (A : Facts Γ) : Prop :=
  ∀ {s : JasminTy} (v : Var Γ s), (A v).relW = none

/-- With no relaxed variable every argument vector is exact. -/
theorem allExactB_of_noRelax {Γ : Ctxt jasminDialect} {A : Facts Γ} (hA : NoRelax A) :
    {ts : List JasminTy} → (args : HVector (fun t => Var Γ t) ts) → allExactB A args = true
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      change (Option.isNone (A v).relW && allExactB A vs) = true
      rw [hA v]
      exact allExactB_of_noRelax hA vs

/-- With no relaxed variable, `okE` accepts every expression, at information that is not
    relaxed. -/
theorem okE_of_noRelax {Γ : Ctxt jasminDialect} {A : Facts Γ} (hA : NoRelax A) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : ∃ i, okE A e = some i ∧ i.relW = none := by
  obtain ⟨op, _, args⟩ := e
  have hx := allExactB_of_noRelax hA args
  cases op <;> simp only [okE, okOp, exactOp, hx, ite_true]
  case regArith bop w =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    simp only [HVector.head, HVector.tail]
    split
    · split
      · rename_i m _
        simp only [maskInfo, hA a]
        exact ⟨_, rfl, rfl⟩
      · split
        · simp only [meet, hA a, hA b]
          exact ⟨_, rfl, rfl⟩
        · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  case shlImm w k =>
    rcases args with _ | ⟨a, _ | _⟩
    simp only [HVector.head]
    split
    · simp only [meet, hA a]
      exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  case regConst w n =>
    split <;> exact ⟨_, rfl, rfl⟩
  all_goals exact ⟨_, rfl, rfl⟩

/-- Pushing information that is not relaxed keeps `NoRelax`. -/
theorem NoRelax.push {Γ : Ctxt jasminDialect} {A : Facts Γ} (hA : NoRelax A) {t : JasminTy}
    {i : Info} (hi : i.relW = none) : NoRelax (A.push (t := t) i)
  | _, .here => hi
  | _, .there v => hA v

/-- Pushing an exact prefix keeps `NoRelax`. -/
theorem NoRelax.appExact {Γ : Ctxt jasminDialect} {A : Facts Γ} (hA : NoRelax A) :
    (cs : List JasminTy) → NoRelax (Facts.appExact cs A)
  | [] => hA
  | _ :: cs => NoRelax.push (NoRelax.appExact hA cs) (i := .exact) rfl

/-- **With no relaxed variable every program passes the analysis.** -/
theorem okP_of_noRelax {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : ∀ (A : Facts Γ), NoRelax A → okP p A = true := by
  induction p with
  | ret vs => intro A hA; exact allExactB_of_noRelax hA vs
  | var e k ih =>
      intro A hA
      obtain ⟨i, hi, hr⟩ := okE_of_noRelax hA e
      simp only [okP, hi]
      exact ih _ (hA.push hr)
  | forLoop count inits body k ihb ihk =>
      intro A hA
      simp only [okP, hA count, Option.isNone_none, allExactB_of_noRelax hA inits,
        ihb _ (NoRelax.appExact (NoRelax.push hA (i := .exact) rfl) _), ihk _ (hA.appExact _),
        Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro A hA
      simp only [okP, hA cond, Option.isNone_none, iht _ hA, ihe _ hA, ihk _ (hA.appExact _),
        Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      intro A hA
      simp only [okP, allExactB_of_noRelax hA inits, ihb _ (hA.appExact _),
        ihk _ (hA.appExact _), Bool.and_self]
  | call f args k ih =>
      intro A hA
      simp only [okP, allExactB_of_noRelax hA args, ih _ (hA.appExact _), Bool.and_self]

/-- **Preservation.** `maskElim p` denotes what `p` denotes, at every call environment, fuel
    and valuation. -/
theorem denoteAt_maskElim (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (V : Valuation Γ) :
    (maskElim p).denoteAt E fuel V = p.denoteAt E fuel V :=
  denoteAt_maskElimGo E fuel p _ _ V V (fun _ => ⟨rel_exact _, constOK_exact _⟩)
    (okP_of_noRelax p _ (fun _ => rfl))

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
