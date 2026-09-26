/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RangeDomain
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.RangeDomain
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth
public import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth
public import CatCryptCore.Tactics.KatGuard

/-!
# A verified range analysis over straight-line `Com jasminDialect`

`rangeAnalysis ivs c` bounds every binding of a straight-line `Com jasminDialect`
program `c` by an integer interval of `RangeDomain`, from the intervals `ivs` of its
inputs, in one pass; the result lists one interval per binding in binding order. A
register variable of type `reg w` is bounded by `Iv.Mem w`; other variables are not
tracked.

Each variable carries, beside its interval, a symbolic fact `Sym` about its value in
terms of an earlier variable, named by its de Bruijn level (its position counted from
the bottom of the context, stable as the context grows): a shift `x >>> s`, the sign
mask `0 - (x >>> (w-1))` and its `and` with a constant, and the three stages of the
Barrett quotient. Two operations take their range from these facts:

* `d + t` where `t` is `(0 - (d >>> (w-1))) &&& C` is the conditional add
  (`RangeDomain.condAdd`), bounded by `ivCondAdd?`;
* `x - y` where `y.toNat = ⌊⌊x/2^s⌋·m/2^t⌋·p` is the Barrett remainder, bounded by
  `ivBarrett?`.

Operations other than `regArith`, `regConst`, `mulhi`, `shrImm`, `shlImm` and `castW`
get the full lane range of their result type.

## Main definitions

* `Sym`, `AEnv`, `EnvOK`: the abstract environment and its meaning.
* `exprAbs`, `analyze`, `rangeAnalysis`, `rangeAnalysisArray`: the analysis.
* `TraceIn`: every binding of a program lies in its interval.

## Main results

* `exprAbs_sound`: the abstract value of an expression holds of its value.
* `analyze_sound`, `rangeAnalysis_sound`: when every register input lies in its
  interval, `TraceIn (rangeAnalysis ivs c) c V`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComRange

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain

/-- A context of the Jasmin dialect. -/
abbrev JCtxt := Ctxt jasminDialect

/-! ## 1. Variables by level -/

/-- The de Bruijn level of a variable: its position from the bottom of the context. -/
def varLevel {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t) : Nat := Γ.length - 1 - varDepth v

theorem varLevel_lt {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t) : varLevel v < Γ.length := by
  have := varDepth_lt v; unfold varLevel; omega

/-- The level of `v` in a context of length `n`. With `n = Γ.length` it is `varLevel v`
    (`levelIn_length`); a pass that tracks the length of its context passes it here and
    so does not recompute `Γ.length` at every variable. -/
def levelIn {Γ : JCtxt} {t : JasminTy} (n : Nat) (v : Ctxt.Var Γ t) : Nat := n - 1 - varDepth v

theorem levelIn_length {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t) :
    levelIn Γ.length v = varLevel v := rfl

/-- A value of type `t` read as a `w`-bit word, when `t = reg w`. -/
def regAs : (t : JasminTy) → (w : Nat) → ⟦t⟧ → Option (BitVec w)
  | .reg w', w, x => if h : w' = w then some (h ▸ (x : BitVec w')) else none
  | _, _, _ => none

theorem regAs_reg (w : Nat) (x : BitVec w) : regAs (.reg w) w x = some x := by
  simp [regAs]

/-- The `w`-bit word at level `ℓ` of a valuation. -/
def atLevel : {Γ : JCtxt} → Ctxt.Valuation Γ → (w : Nat) → Nat → Option (BitVec w)
  | [], _, _, _ => none
  | t :: Γ, .cons x V, w, ℓ => if ℓ = Γ.length then regAs t w x else atLevel V w ℓ

theorem atLevel_extend {Γ : JCtxt} {t : JasminTy} (V : Ctxt.Valuation Γ) (z : ⟦t⟧)
    (w ℓ : Nat)
    (h : ℓ < Γ.length) : atLevel (V.extend z) w ℓ = atLevel V w ℓ := by
  show (if ℓ = Γ.length then regAs t w z else atLevel V w ℓ) = _
  rw [if_neg (by omega)]

theorem atLevel_varLevel : ∀ {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) (w : Nat), atLevel V w (varLevel v) = regAs t w (v.lookup V)
  | t :: Γ, _, .here, .cons x V, w => by
    have hl : varLevel (Ctxt.Var.here (Γ := Γ) (t := t)) = Γ.length := by
      simp [varLevel, varDepth]
    rw [hl]
    show (if Γ.length = Γ.length then regAs t w x else atLevel V w Γ.length) = _
    rw [if_pos rfl]
    rfl
  | s :: Γ, t, .there v, .cons x V, w => by
    have hv := varDepth_lt v
    have ih := atLevel_varLevel v V w
    have hl : varLevel (Ctxt.Var.there (s := s) v) = varLevel v := by
      simp [varLevel, varDepth]; omega
    rw [hl]
    show (if varLevel v = Γ.length then regAs s w x else atLevel V w (varLevel v)) = _
    rw [if_neg (by have := varLevel_lt v; omega), ih]
    rfl

/-- The word a register variable holds under `V`. -/
def regVal {Γ : JCtxt} {w : Nat} (V : Ctxt.Valuation Γ) (v : Ctxt.Var Γ (.reg w)) :
    BitVec w :=
  v.lookup V

theorem atLevel_var {Γ : JCtxt} {w : Nat} (v : Ctxt.Var Γ (.reg w)) (V : Ctxt.Valuation Γ) :
    atLevel V w (varLevel v) = some (regVal V v) := by
  rw [atLevel_varLevel]; exact regAs_reg w _

/-! ## 2. Symbolic facts and the abstract environment -/

/-- A fact about a `w`-bit value `y` in terms of the word `x` at a level. -/
inductive Sym where
  | none
  /-- `y = x >>> s`. -/
  | shr (ℓ s : Nat)
  /-- `y = 0 - (x >>> (w-1))`. -/
  | negSign (ℓ : Nat)
  /-- `y = (0 - (x >>> (w-1))) &&& C` for a `C` whose `toNat` lies in `ic`. -/
  | mask (ℓ : Nat) (ic : Iv)
  /-- `y.toNat = ⌊x/2^s⌋·m`. -/
  | barG (ℓ s m : Nat)
  /-- `y.toNat = ⌊⌊x/2^s⌋·m/2^t⌋`. -/
  | barQ (ℓ s m t : Nat)
  /-- `y.toNat = ⌊⌊x/2^s⌋·m/2^t⌋·p`. -/
  | barY (ℓ s m t p : Nat)

/-- The level a fact refers to. -/
def Sym.level : Sym → Nat
  | .none => 0
  | .shr ℓ _ => ℓ
  | .negSign ℓ => ℓ
  | .mask ℓ _ => ℓ
  | .barG ℓ _ _ => ℓ
  | .barQ ℓ _ _ _ => ℓ
  | .barY ℓ _ _ _ _ => ℓ

/-- The fact `s` of `y` with the referred word `x`. -/
def Sym.Holds {w : Nat} (y x : BitVec w) : Sym → Prop
  | .none => True
  | .shr _ s => y = x >>> s
  | .negSign _ => y = 0 - (x >>> (w - 1))
  | .mask _ ic => ∃ C : BitVec w, ic.1 ≤ (C.toNat : Int) ∧ (C.toNat : Int) ≤ ic.2 ∧
      y = (0 - (x >>> (w - 1))) &&& C
  | .barG _ s m => y.toNat = x.toNat / 2 ^ s * m
  | .barQ _ s m t => y.toNat = x.toNat / 2 ^ s * m / 2 ^ t
  | .barY _ s m t p => y.toNat = x.toNat / 2 ^ s * m / 2 ^ t * p

/-- The fact `s` holds of `y` under `V`, and it refers to a variable of the context. -/
def SymOK {Γ : JCtxt} (V : Ctxt.Valuation Γ) (w : Nat) (y : BitVec w) (s : Sym) : Prop :=
  (s = .none ∨ s.level < Γ.length) ∧ ∀ x, atLevel V w s.level = some x → s.Holds y x

theorem SymOK.none {Γ : JCtxt} (V : Ctxt.Valuation Γ) (w : Nat) (y : BitVec w) :
    SymOK V w y .none :=
  ⟨Or.inl rfl, fun _ _ => trivial⟩

theorem SymOK.extend {Γ : JCtxt} {t : JasminTy} {V : Ctxt.Valuation Γ} {w : Nat} {y : BitVec w}
    {s : Sym} (h : SymOK V w y s) (z : ⟦t⟧) : SymOK (V.extend z) w y s := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 with rfl | h1
  · exact SymOK.none _ _ _
  · refine ⟨Or.inr (by simp; omega), fun x hx => h2 x ?_⟩
    rwa [atLevel_extend V z w _ h1] at hx

/-- The fact of a variable at level `ℓ` that `SymOK` gives. -/
theorem SymOK.holds {Γ : JCtxt} {V : Ctxt.Valuation Γ} {w : Nat} {y : BitVec w} {s : Sym}
    (h : SymOK V w y s) (a : Ctxt.Var Γ (.reg w)) (ha : s.level = varLevel a) :
    s.Holds y (regVal V a) :=
  h.2 _ (by rw [ha]; exact atLevel_var a V)

/-- The abstract value of a variable: an interval and a fact. -/
abbrev AVal := Iv × Sym

/-- The abstract environment: one abstract value per variable. -/
abbrev AEnv (Γ : JCtxt) := HVector (fun _ => AVal) Γ

/-- The entry of an `HVector` at a variable. -/
def hget {f : JasminTy → Type} :
    {Γ : JCtxt} → {t : JasminTy} → HVector f Γ → Ctxt.Var Γ t → f t
  | _, _, .cons a _, .here => a
  | _, _, .cons _ A, .there v => hget A v

/-- The abstract value `a` holds of the value `y` of type `t`: for `t = reg w`, `y` lies
    in the interval and the fact holds. -/
def ValOK {Γ : JCtxt} (V : Ctxt.Valuation Γ) : (t : JasminTy) → AVal → ⟦t⟧ → Prop
  | .reg w, a, y => a.1.Mem w y ∧ SymOK V w y a.2
  | _, _, _ => True

/-- The interval `i` holds of the value `y` of type `t` when `t = reg w`. -/
def valMem : (t : JasminTy) → Iv → ⟦t⟧ → Prop
  | .reg w, i, y => i.Mem w y
  | _, _, _ => True

theorem ValOK.extend {Γ : JCtxt} {V : Ctxt.Valuation Γ} {t u : JasminTy} {a : AVal} {y : ⟦t⟧}
    (h : ValOK V t a y) (z : ⟦u⟧) : ValOK (V.extend z) t a y := by
  cases t with
  | reg w => exact ⟨h.1, h.2.extend z⟩
  | _ => trivial

theorem ValOK.valMem {Γ : JCtxt} {V : Ctxt.Valuation Γ} {t : JasminTy} {a : AVal} {y : ⟦t⟧}
    (h : ValOK V t a y) : valMem t a.1 y := by
  cases t with
  | reg w => exact h.1
  | _ => trivial

/-- The abstract environment holds of the valuation. -/
def EnvOK {Γ : JCtxt} (A : AEnv Γ) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ (t : JasminTy) (v : Ctxt.Var Γ t), ValOK V t (hget A v) (v.lookup V)

theorem EnvOK.cons {Γ : JCtxt} {t : JasminTy} {A : AEnv Γ} {V : Ctxt.Valuation Γ}
    (hA : EnvOK A V) {a : AVal} {z : ⟦t⟧} (hz : ValOK V t a z) :
    EnvOK (HVector.cons (f := fun _ => AVal) a A) (V.extend z) := by
  intro u v
  cases v with
  | here => exact hz.extend z
  | there v => exact (hA u v).extend z

theorem EnvOK.reg {Γ : JCtxt} {A : AEnv Γ} {V : Ctxt.Valuation Γ} (hA : EnvOK A V) {w : Nat}
    (v : Ctxt.Var Γ (.reg w)) :
    (hget A v).1.Mem w (regVal V v) ∧ SymOK V w (regVal V v) (hget A v).2 :=
  hA (.reg w) v

/-! ## 3. Transfer on one operation -/

/-- The full lane range of a register type. -/
def tyTop : JasminTy → Iv
  | .reg w => ivTop w
  | _ => (0, 0)

theorem valOK_top {Γ : JCtxt} (V : Ctxt.Valuation Γ) : ∀ (t : JasminTy) (y : ⟦t⟧),
    ValOK V t (tyTop t, .none) y
  | .reg w, y => ⟨Iv.mem_top y, SymOK.none V w y⟩
  | .stackArr _ _, _ => trivial
  | .inlineInt, _ => trivial
  | .bool, _ => trivial

variable {Γ : JCtxt} (A : AEnv Γ)

/-! The functions below take the length `len` of `Γ` as an argument, by default
`Γ.length`, and read the level of a variable as `levelIn len`. A pass that tracks the
length of its context passes it and so avoids a traversal of `Γ` at each binding. -/

/-- The conditional-add range of `a + b` when the fact of `b` is the mask of `a`. -/
def condAddRule? {w : Nat} (a b : Ctxt.Var Γ (.reg w)) (len : Nat := Γ.length) : Option Iv :=
  match (hget A b).2 with
  | .mask ℓ ic => if ℓ = levelIn len a then ivCondAdd? w (hget A a).1 ic else none
  | _ => none

/-- The Barrett range of `a - b` when the fact of `b` is the Barrett product of `a`. -/
def barrettRule? {w : Nat} (a b : Ctxt.Var Γ (.reg w)) (len : Nat := Γ.length) : Option Iv :=
  match (hget A b).2 with
  | .barY ℓ s m t p =>
    if ℓ = levelIn len a then ivBarrett? w (hget A a).1 s t m p else none
  | _ => none

/-- The interval of `bop a b`. -/
def binIv (w : Nat) (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w))
    (len : Nat := Γ.length) : Iv :=
  match bop with
  | .add =>
    match condAddRule? A a b len with
    | some r => r
    | none =>
      match condAddRule? A b a len with
      | some r => r
      | none => ivAdd w (hget A a).1 (hget A b).1
  | .sub =>
    match barrettRule? A a b len with
    | some r => r
    | none => ivSub w (hget A a).1 (hget A b).1
  | .mul => ivMul w (hget A a).1 (hget A b).1
  | .and => ivAnd w (hget A a).1 (hget A b).1
  | .shr =>
    match ivSingle? (ivLane w (hget A b).1) with
    | some k => ivShr w (hget A a).1 k
    | none => ivTop w
  | .shl =>
    match ivSingle? (ivLane w (hget A b).1) with
    | some k => ivShl w (hget A a).1 k
    | none => ivTop w
  | _ => ivTop w

/-- The fact of `a >>> k`. -/
def shrSym {w : Nat} (a : Ctxt.Var Γ (.reg w)) (k : Nat) (len : Nat := Γ.length) : Sym :=
  match (hget A a).2 with
  | .barG ℓ s m => .barQ ℓ s m k
  | _ => .shr (levelIn len a) k

/-- The fact of `a * b` when `b` is a constant and the product does not wrap. -/
def mulSym? {w : Nat} (a b : Ctxt.Var Γ (.reg w)) : Option Sym :=
  match (hget A a).2, ivSingle? (ivLane w (hget A b).1) with
  | .shr ℓ s, some m =>
    if (ivLane w (hget A a).1).2 * (m : Int) < 2 ^ w then some (.barG ℓ s m) else none
  | .barQ ℓ s m t, some p =>
    if (ivLane w (hget A a).1).2 * (p : Int) < 2 ^ w then some (.barY ℓ s m t p) else none
  | _, _ => none

/-- The fact of `bop a b`. -/
def binSym (w : Nat) (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w))
    (len : Nat := Γ.length) : Sym :=
  match bop with
  | .sub =>
    match ivSingle? (ivLane w (hget A a).1), (hget A b).2 with
    | some 0, .shr ℓ k => if k = w - 1 then .negSign ℓ else .none
    | _, _ => .none
  | .mul =>
    match mulSym? A a b with
    | some s => s
    | none =>
      match mulSym? A b a with
      | some s => s
      | none => .none
  | .and =>
    match (hget A a).2, (hget A b).2 with
    | .negSign ℓ, _ => .mask ℓ (ivLane w (hget A b).1)
    | _, .negSign ℓ => .mask ℓ (ivLane w (hget A a).1)
    | _, _ => .none
  | .shr =>
    match ivSingle? (ivLane w (hget A b).1) with
    | some k => shrSym A a k len
    | none => .none
  | _ => .none

/-- The abstract value of an operation on the variables `args`. -/
def opAbs (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    (len : Nat := Γ.length) : AVal :=
  match op, args with
  | .regArith bop w, .cons a (.cons b .nil) => (binIv A w bop a b len, binSym A w bop a b len)
  | .regConst w n, _ => (ivConst w n, .none)
  | .mulhi w, .cons a (.cons b .nil) => (ivMulhi w (hget A a).1 (hget A b).1, .none)
  | .shrImm w n, .cons a .nil => (ivShr w (hget A a).1 n, shrSym A a n len)
  | .shlImm w n, .cons a .nil => (ivShl w (hget A a).1 n, .none)
  | .castW w w', .cons a .nil => (ivCast w w' (hget A a).1, .none)
  | op, _ => (tyTop (DialectSignature.ret (d := jasminDialect) op), .none)

/-- The abstract value of an expression. -/
def exprAbs {t : JasminTy} (e : Expr jasminDialect Γ t) (len : Nat := Γ.length) : AVal :=
  opAbs A e.op e.args len

/-- `exprAbs` at the length of the context is `exprAbs` with the default length. -/
theorem exprAbs_len {t : JasminTy} (e : Expr jasminDialect Γ t) {len : Nat}
    (h : len = Γ.length) : exprAbs A e len = exprAbs A e := by
  subst h; rfl

/-! ## 4. Soundness of the transfer -/

variable {A} {V : Ctxt.Valuation Γ}

theorem condAddRule_sound (hA : EnvOK A V) {w : Nat} {a b : Ctxt.Var Γ (.reg w)} {r : Iv}
    (h : condAddRule? A a b = some r) : r.Mem w (regVal V a + regVal V b) := by
  unfold condAddRule? at h
  split at h
  · rename_i ℓ ic hs
    split at h
    · rename_i hl
      have hb := (hA.reg b).2
      rw [hs] at hb
      obtain ⟨C, hC1, hC2, hC⟩ := hb.holds a hl
      rw [hC]
      exact Iv.mem_ivCondAdd (hA.reg a).1 hC1 hC2 h
    · cases h
  · cases h

theorem barrettRule_sound (hA : EnvOK A V) {w : Nat} {a b : Ctxt.Var Γ (.reg w)} {r : Iv}
    (h : barrettRule? A a b = some r) : r.Mem w (regVal V a - regVal V b) := by
  unfold barrettRule? at h
  split at h
  · rename_i ℓ s m t p hs
    split at h
    · rename_i hl
      have hb := (hA.reg b).2
      rw [hs] at hb
      exact Iv.mem_ivBarrett (hA.reg a).1 h (hb.holds a hl)
    · cases h
  · cases h

theorem binIv_sound (hA : EnvOK A V) {w : Nat} (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) :
    (binIv A w bop a b).Mem w (bop.apply (regVal V a) (regVal V b)) := by
  have ha := (hA.reg a).1
  have hb := (hA.reg b).1
  cases bop with
  | add =>
    simp only [binIv, JasminBinOp.apply]
    split
    · rename_i r h; exact condAddRule_sound hA h
    · split
      · rename_i r h; rw [BitVec.add_comm]; exact condAddRule_sound hA h
      · exact Iv.mem_add ha hb
  | sub =>
    simp only [binIv, JasminBinOp.apply]
    split
    · rename_i r h; exact barrettRule_sound hA h
    · exact Iv.mem_sub ha hb
  | mul => exact Iv.mem_mul ha hb
  | and => exact Iv.mem_and ha hb
  | shr =>
    simp only [binIv, JasminBinOp.apply]
    split
    · rename_i k hk
      rw [Iv.toNat_eq_of_single hb hk]
      exact Iv.mem_shr ha k
    · exact Iv.mem_top _
  | shl =>
    simp only [binIv, JasminBinOp.apply]
    split
    · rename_i k hk
      rw [Iv.toNat_eq_of_single hb hk]
      exact Iv.mem_shl ha k
    · exact Iv.mem_top _
  | or => exact Iv.mem_top _
  | xor => exact Iv.mem_top _
  | andn => exact Iv.mem_top _

theorem shrSym_sound (hA : EnvOK A V) {w : Nat} (a : Ctxt.Var Γ (.reg w)) (k : Nat) :
    SymOK V w (regVal V a >>> k) (shrSym A a k) := by
  unfold shrSym
  split
  · rename_i ℓ s m hs
    have hsa := (hA.reg a).2
    rw [hs] at hsa
    obtain ⟨h1, h2⟩ := hsa
    refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
    have hg := h2 x hx
    show (regVal V a >>> k).toNat = x.toNat / 2 ^ s * m / 2 ^ k
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact congrArg (· / 2 ^ k) hg
  · exact ⟨Or.inr (varLevel_lt a), fun x hx => by
      change atLevel V w (varLevel a) = some x at hx
      rw [atLevel_var] at hx; cases hx; rfl⟩

theorem mulSym_sound (hA : EnvOK A V) {w : Nat} {a b : Ctxt.Var Γ (.reg w)} {s : Sym}
    (h : mulSym? A a b = some s) : SymOK V w (regVal V a * regVal V b) s := by
  have hla := Iv.mem_lane (hA.reg a).1
  unfold mulSym? at h
  split at h
  · rename_i ℓ s0 m hs hm
    split at h
    · rename_i hlt
      cases h
      have hsa := (hA.reg a).2
      rw [hs] at hsa
      obtain ⟨h1, h2⟩ := hsa
      have hbm := Iv.toNat_eq_of_single (hA.reg b).1 hm
      refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
      have hh : regVal V a = x >>> s0 := h2 x hx
      show (regVal V a * regVal V b).toNat = x.toNat / 2 ^ s0 * m
      have hlt' : (regVal V a).toNat * m < 2 ^ w := by
        have e : ((regVal V a).toNat : Int) * m < 2 ^ w :=
          lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right hla.2 (Int.natCast_nonneg m)) hlt
        exact_mod_cast e
      rw [BitVec.toNat_mul, hbm, Nat.mod_eq_of_lt hlt', hh, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
    · cases h
  · rename_i ℓ s0 m t p hs hm
    split at h
    · rename_i hlt
      cases h
      have hsa := (hA.reg a).2
      rw [hs] at hsa
      obtain ⟨h1, h2⟩ := hsa
      have hbm := Iv.toNat_eq_of_single (hA.reg b).1 hm
      refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
      have hq : (regVal V a).toNat = x.toNat / 2 ^ s0 * m / 2 ^ t := h2 x hx
      show (regVal V a * regVal V b).toNat = x.toNat / 2 ^ s0 * m / 2 ^ t * p
      have hlt' : (regVal V a).toNat * p < 2 ^ w := by
        have e : ((regVal V a).toNat : Int) * p < 2 ^ w :=
          lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right hla.2 (Int.natCast_nonneg p)) hlt
        exact_mod_cast e
      rw [BitVec.toNat_mul, hbm, Nat.mod_eq_of_lt hlt', hq]
    · cases h
  · cases h

theorem binSym_sound (hA : EnvOK A V) {w : Nat} (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) :
    SymOK V w (bop.apply (regVal V a) (regVal V b)) (binSym A w bop a b) := by
  cases bop with
  | sub =>
    simp only [binSym, JasminBinOp.apply]
    split
    · rename_i ℓ k h0 hs
      split
      · rename_i hk
        have hsb := (hA.reg b).2
        rw [hs] at hsb
        obtain ⟨h1, h2⟩ := hsb
        have ha0 := Iv.toNat_eq_of_single (hA.reg a).1 h0
        refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
        have hbx : regVal V b = x >>> k := h2 x hx
        have ha : regVal V a = 0 := BitVec.eq_of_toNat_eq (by rw [ha0]; rfl)
        show regVal V a - regVal V b = 0 - (x >>> (w - 1))
        rw [ha, hbx, hk]
      · exact SymOK.none _ _ _
    · exact SymOK.none _ _ _
  | mul =>
    simp only [binSym, JasminBinOp.apply]
    split
    · rename_i s h; exact mulSym_sound hA h
    · split
      · rename_i s h; rw [BitVec.mul_comm]; exact mulSym_sound hA h
      · exact SymOK.none _ _ _
  | and =>
    simp only [binSym, JasminBinOp.apply]
    split
    · rename_i ℓ s hs
      have hsa := (hA.reg a).2
      rw [hs] at hsa
      obtain ⟨h1, h2⟩ := hsa
      refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
      have hl := Iv.mem_lane (hA.reg b).1
      exact ⟨regVal V b, hl.1, hl.2, by rw [h2 x hx]⟩
    · rename_i ℓ hs _
      have hsb := (hA.reg b).2
      rw [hs] at hsb
      obtain ⟨h1, h2⟩ := hsb
      refine ⟨Or.inr (h1.resolve_left (fun h => nomatch h)), fun x hx => ?_⟩
      have hl := Iv.mem_lane (hA.reg a).1
      exact ⟨regVal V a, hl.1, hl.2, by rw [h2 x hx, BitVec.and_comm]⟩
    · exact SymOK.none _ _ _
  | shr =>
    simp only [binSym, JasminBinOp.apply]
    split
    · rename_i k hk
      rw [Iv.toNat_eq_of_single (hA.reg b).1 hk]
      exact shrSym_sound hA a k
    · exact SymOK.none _ _ _
  | add => exact SymOK.none _ _ _
  | or => exact SymOK.none _ _ _
  | xor => exact SymOK.none _ _ _
  | shl => exact SymOK.none _ _ _
  | andn => exact SymOK.none _ _ _

theorem opAbs_sound (hA : EnvOK A V) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    ValOK V (DialectSignature.ret (d := jasminDialect) op) (opAbs A op args)
      (DialectDenote.denote op (Expr.lookupArgs args V)) := by
  cases op with
  | regArith bop w =>
    match args with
    | .cons a (.cons b .nil) => exact ⟨binIv_sound hA bop a b, binSym_sound hA bop a b⟩
  | regConst w n => exact ⟨Iv.mem_const n, SymOK.none _ _ _⟩
  | mulhi w =>
    match args with
    | .cons a (.cons b .nil) =>
      exact ⟨Iv.mem_mulhi (hA.reg a).1 (hA.reg b).1, SymOK.none _ _ _⟩
  | shrImm w n =>
    match args with
    | .cons a .nil => exact ⟨Iv.mem_shr (hA.reg a).1 n, shrSym_sound hA a n⟩
  | shlImm w n =>
    match args with
    | .cons a .nil => exact ⟨Iv.mem_shl (hA.reg a).1 n, SymOK.none _ _ _⟩
  | castW w w' =>
    match args with
    | .cons a .nil => exact ⟨Iv.mem_cast (hA.reg a).1, SymOK.none _ _ _⟩
  | _ => exact valOK_top V _ _

/-- The abstract value of an expression holds of its value. -/
theorem exprAbs_sound (hA : EnvOK A V) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    ValOK V t (exprAbs A e) (e.denote V) := by
  rcases e with ⟨op, rfl, args⟩
  exact opAbs_sound hA op args

/-! ## 5. The analysis of a program -/

/-- The intervals of the bindings of `c` in order, from the abstract environment `A`. -/
def analyze {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) : Com jasminDialect Γ t → List Iv
  | .ret _ => []
  | .var e body =>
    (exprAbs A e).1 :: analyze (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) body

/-- Every binding of `c` under `V` lies in its interval of `ivs`, in order. -/
def TraceIn : {Γ : JCtxt} → {t : JasminTy} → List Iv → Com jasminDialect Γ t →
    Ctxt.Valuation Γ → Prop
  | _, _, _, .ret _, _ => True
  | _, _, [], .var _ _, _ => False
  | _, _, i :: is, .var (t := u) e body, V =>
    valMem u i (e.denote V) ∧ TraceIn is body (V.extend (e.denote V))

theorem analyze_sound : ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t)
    (A : AEnv Γ) (V : Ctxt.Valuation Γ), EnvOK A V → TraceIn (analyze A c) c V
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .var e body, A, V, hA => by
    have he := exprAbs_sound hA e
    exact ⟨he.valMem, analyze_sound body _ _ (hA.cons he)⟩

/-- The abstract environment of input intervals, with no facts. -/
def AEnv.ofIvs : {Γ : JCtxt} → HVector (fun _ => Iv) Γ → AEnv Γ
  | [], .nil => .nil
  | _ :: _, .cons i is => .cons (i, .none) (AEnv.ofIvs is)

theorem hget_ofIvs : ∀ {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (v : Ctxt.Var Γ t), hget (AEnv.ofIvs ivs) v = (hget ivs v, .none)
  | _ :: _, _, .cons _ _, .here => rfl
  | _ :: _, _, .cons _ is, .there v => hget_ofIvs is v

/-- The range analysis of `c` from the input intervals `ivs`: one interval per binding,
    in binding order. -/
def rangeAnalysis {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) : List Iv :=
  analyze (AEnv.ofIvs ivs) c

/-- `rangeAnalysis` as an array indexed by binding position. -/
def rangeAnalysisArray {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) : Array Iv :=
  (rangeAnalysis ivs c).toArray

/-- Soundness of the range analysis: when every register input lies in its interval,
    every binding lies in its interval. -/
theorem rangeAnalysis_sound {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ)
    (hV : ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), (hget ivs v).Mem w (v.lookup V)) :
    TraceIn (rangeAnalysis ivs c) c V := by
  refine analyze_sound c _ V ?_
  intro u v
  rw [hget_ofIvs]
  cases u with
  | reg w => exact ⟨hV w v, SymOK.none _ _ _⟩
  | _ => trivial

/-! ## 6. Static checks

`build w Γ steps` is the straight-line program over `reg w` whose bindings are `steps`,
each naming its operands by level, returning its last binding. -/

/-- One binding of a check program: operands are levels. -/
inductive Step where
  | bin (bop : JasminBinOp) (a b : Nat)
  | mulhi (a b : Nat)
  | const (n : Nat)

/-- The `reg w` variable at level `ℓ` of `Γ`. -/
def varAt? (w : Nat) : (Γ : JCtxt) → Nat → Option (Ctxt.Var Γ (.reg w))
  | [], _ => none
  | t :: Γ, ℓ =>
    if ℓ = Γ.length then
      if h : t = .reg w then some (by subst h; exact .here) else none
    else (varAt? w Γ ℓ).map .there

/-- The program of `steps` over `Γ`. -/
def build (w : Nat) : (Γ : JCtxt) → List Step → Option (Com jasminDialect Γ (.reg w))
  | Γ, [] => (varAt? w Γ (Γ.length - 1)).map .ret
  | Γ, .bin bop a b :: rest => do
    let va ← varAt? w Γ a
    let vb ← varAt? w Γ b
    let body ← build w (.reg w :: Γ) rest
    pure (.var ⟨.regArith bop w, rfl, .cons va (.cons vb .nil)⟩ body)
  | Γ, .mulhi a b :: rest => do
    let va ← varAt? w Γ a
    let vb ← varAt? w Γ b
    let body ← build w (.reg w :: Γ) rest
    pure (.var ⟨.mulhi w, rfl, .cons va (.cons vb .nil)⟩ body)
  | Γ, .const n :: rest => do
    let body ← build w (.reg w :: Γ) rest
    pure (.var ⟨.regConst w n, rfl, .nil⟩ body)

/-- The two inputs `a, b` (levels 0 and 1) in `[0, p - 1]` for the BabyBear prime `p`. -/
def bbInputs (w : Nat) : HVector (fun _ => Iv) ([.reg w, .reg w] : JCtxt) :=
  .cons (0, 2013265920) (.cons (0, 2013265920) .nil)

/-- The BabyBear multiply of `FieldDescentBB` at 64 bits: the product, the Barrett
    reduction with `m = ⌊2^62/p⌋` (`s = 30`, `t = 32`), a conditional subtract of `p`,
    and the square of the result. -/
def bbMul64 : List Step :=
  [.const 30, .const 2290649223, .const 32, .const 2013265921, .const 63, .const 0,
   .bin .mul 0 1, .bin .shr 8 2, .bin .mul 9 3, .bin .shr 10 4, .bin .mul 11 5,
   .bin .sub 8 12, .bin .sub 13 5, .bin .shr 14 6, .bin .sub 7 15, .bin .and 16 5,
   .bin .add 14 17, .bin .mul 18 18]

/-- The 32-bit Montgomery multiply of `FieldDescentBBMont32` and its conditional add,
    followed by an add of `a` and a conditional subtract of `p`. -/
def bbMont32 : List Step :=
  [.const 2013265921, .const 2281701377, .const 31, .const 0,
   .bin .mul 0 1, .mulhi 0 1, .bin .mul 6 3, .mulhi 8 2, .bin .sub 7 9, .bin .shr 10 4,
   .bin .sub 5 11, .bin .and 12 2, .bin .add 10 13, .bin .add 14 0, .bin .sub 15 2,
   .bin .shr 16 4, .bin .sub 5 17, .bin .and 18 2, .bin .add 16 19]

/- On inputs below `p`, the multiplies of `bbMul64` read operands below `2^32` (the
   shifted product, the quotient and the reduced value), and the reduced value lies in
   `[0, p - 1]`. -/
#kat (build 64 [.reg 64, .reg 64] bbMul64).map (fun c =>
    let r := rangeAnalysisArray (bbInputs 64) c
    decide (r[7]!.2 < 2 ^ 32 ∧ r[9]!.2 < 2 ^ 32 ∧ r[16]! = (0, 2013265920)))
  == some true

/- On inputs below `p`, both conditional adds of `bbMont32` give `[0, p - 1]`. -/
#kat (build 32 [.reg 32, .reg 32] bbMont32).map (fun c =>
    let r := rangeAnalysisArray (bbInputs 32) c
    decide (r[12]! = (0, 2013265920) ∧ r[18]! = (0, 2013265920)))
  == some true

end CatCrypt.Crypto.SecureCompilation.VIR.ComRange
