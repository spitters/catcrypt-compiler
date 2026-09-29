/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public import CatCrypt.Crypto.Jasmin.LowCTTypes

/-!
# Valued leakage and a level checker for `Com`

The constant-time leakage of a straight-line `Com` program over any dialect, and a
level checker whose acceptance implies constant time.

## The leakage

A `LeakModel` classes each operation by the events it emits (`LeakKind`):
nothing (`quiet`), the value of its `k`-th argument as a memory offset
(`addrAt k`), its argument values as the operands of a variable-time instruction
(`vt m`), or its argument values as the arguments of a variable-time leaf call
(`vtCall f`). `Com.ctLeak M c V` is the list of events of the run of `c` from the
valuation `V`, in binding order, over the events of `CT.CTLeak`. `ComCT M L c` is
constant time for the label context `L`: two valuations that agree on the
positions `L` marks public give equal leakage (`CT.ConstantTime`).

## The checker

`Com.levelCheck M c L` threads one `SecretLevel` per binding. A binding's level is
the join of the levels of its arguments; the checker requires the index argument
of an `addrAt` operation, and every argument of a `vt` or `vtCall` operation, to be
public. `levelCheck_sound`: an accepted program is `ComCT` for the entry labels.

## Main definitions

* `LeakKind`, `LeakModel`, `opLeak`, `Com.ctLeak`, `ComCT`
* `Labels`, `lvlOf`, `argLvls`, `joinAll`, `PubEqV`, `opAccepts`, `Com.levelCheck`

## Main results

* `lookupArgs_eq_of_pub`: arguments whose levels join to public have equal values
* `levelCheck_sound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime X86Mnem)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## The leakage -/

/-- The events an operation emits. -/
inductive LeakKind where
  /-- No event. -/
  | quiet
  /-- A memory access at the value of argument `k`. -/
  | addrAt (k : Nat)
  /-- A variable-time instruction on the argument values. -/
  | vt (m : X86Mnem)
  /-- A variable-time leaf call on the argument values. -/
  | vtCall (f : String)

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]

/-- The leakage model of a dialect: the event class of each operation and the
    natural-number reading of a value of each type. -/
structure LeakModel (d : Dialect) [TyDenote d.Ty] [DialectSignature d] where
  kind : d.Op → LeakKind
  valNat : (t : d.Ty) → ⟦t⟧ → Nat

/-- The natural-number readings of a list of values. -/
def valsNat (M : LeakModel d) : {tys : List d.Ty} → HVector (fun t => ⟦t⟧) tys → List Nat
  | [], .nil => []
  | t :: _, .cons v rest => M.valNat t v :: valsNat M rest

/-- The events of operation `op` on the argument values `vals`. -/
def opLeak (M : LeakModel d) (op : d.Op)
    (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig op)) : List CTLeak :=
  match M.kind op with
  | .quiet => []
  | .addrAt k => [.addr "" (((valsNat M vals).getD k 0 : Nat) : Int)]
  | .vt m => [.vt m (valsNat M vals)]
  | .vtCall f => [.vtCall f ((valsNat M vals).map fun x => [x])]

/-- The events of an expression at a valuation. -/
def Expr.ctLeak (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (V : Ctxt.Valuation Γ) : List CTLeak :=
  opLeak M e.op (Expr.lookupArgs e.args V)

variable [DialectDenote d]

/-- The events of the run of a program from a valuation, in binding order. -/
def Com.ctLeak (M : LeakModel d) : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t →
    Ctxt.Valuation Γ → List CTLeak
  | _, _, .ret _, _ => []
  | _, _, .var e body, V => Expr.ctLeak M e V ++ Com.ctLeak M body (V.extend (e.denote V))

/-! ## Labels -/

/-- One `SecretLevel` per binding of the context. -/
abbrev Labels (Γ : Ctxt d) : Type := HVector (fun _ => SecretLevel) Γ

/-- The level of a variable. -/
def lvlOf : {Γ : Ctxt d} → {t : d.Ty} → Ctxt.Var Γ t → Labels Γ → SecretLevel
  | _, _, .here, .cons l _ => l
  | _, _, .there v, .cons _ L => lvlOf v L

/-- The levels of a list of argument variables. -/
def argLvls {Γ : Ctxt d} (L : Labels Γ) :
    {tys : List d.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys → List SecretLevel
  | [], .nil => []
  | _ :: _, .cons v rest => lvlOf v L :: argLvls L rest

/-- The join of a list of levels; public for the empty list. -/
def joinAll : List SecretLevel → SecretLevel
  | [] => .Public
  | l :: ls => l.join (joinAll ls)

/-- Two valuations agree on the positions `L` marks public. -/
def PubEqV {Γ : Ctxt d} (L : Labels Γ) (V₁ V₂ : Ctxt.Valuation Γ) : Prop :=
  ∀ (t : d.Ty) (v : Ctxt.Var Γ t), lvlOf v L = .Public → v.lookup V₁ = v.lookup V₂

/-- Constant time of a program for the entry labels `L`. -/
def ComCT (M : LeakModel d) {Γ : Ctxt d} {t : d.Ty} (L : Labels Γ) (c : Com d Γ t) : Prop :=
  ConstantTime (PubEqV L) (Com.ctLeak M c)

/-- The constraint of an operation on the levels of its arguments. -/
def opAccepts (M : LeakModel d) (op : d.Op) (ls : List SecretLevel) : Bool :=
  match M.kind op with
  | .quiet => true
  | .addrAt k => decide (ls.getD k .Secret = .Public)
  | .vt _ => decide (joinAll ls = .Public)
  | .vtCall _ => decide (joinAll ls = .Public)

/-- The level checker: every operation's constraint holds, and each binding takes
    the join of its argument levels. -/
def Com.levelCheck (M : LeakModel d) : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t →
    Labels Γ → Bool
  | _, _, .ret _, _ => true
  | _, _, .var e body, L =>
      opAccepts M e.op (argLvls L e.args) &&
        Com.levelCheck M body (.cons (joinAll (argLvls L e.args)) L)

/-! ## Soundness -/

theorem join_eq_public {a b : SecretLevel} (h : a.join b = .Public) :
    a = .Public ∧ b = .Public := by
  cases a <;> cases b <;> simp_all [SecretLevel.join]

omit [DialectSignature d] [DialectDenote d] in
/-- Arguments whose levels join to public have equal values under valuations that
    agree on the public positions. -/
theorem lookupArgs_eq_of_pub {Γ : Ctxt d} {L : Labels Γ} {V₁ V₂ : Ctxt.Valuation Γ}
    (h : PubEqV L V₁ V₂) :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      joinAll (argLvls L args) = .Public →
      Expr.lookupArgs args V₁ = Expr.lookupArgs args V₂ := by
  intro tys args
  induction args with
  | nil => intro _; rfl
  | cons v rest ih =>
      intro hj
      obtain ⟨hv, hr⟩ := join_eq_public hj
      simp only [Expr.lookupArgs]
      rw [h _ v hv, ih hr]

omit [DialectDenote d] in
/-- A public argument position has equal readings. -/
theorem valsNat_getD_eq_of_pub (M : LeakModel d) {Γ : Ctxt d} {L : Labels Γ}
    {V₁ V₂ : Ctxt.Valuation Γ} (h : PubEqV L V₁ V₂) :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys) (k : Nat),
      (argLvls L args).getD k .Secret = .Public →
      (valsNat M (Expr.lookupArgs args V₁)).getD k 0
        = (valsNat M (Expr.lookupArgs args V₂)).getD k 0 := by
  intro tys args
  induction args with
  | nil => intro k hk; simp [argLvls] at hk
  | cons v rest ih =>
      intro k hk
      cases k with
      | zero =>
          simp only [argLvls, List.getD_cons_zero] at hk
          simp only [Expr.lookupArgs, valsNat, List.getD_cons_zero, h _ v hk]
      | succ k =>
          simp only [argLvls, List.getD_cons_succ] at hk
          simp only [Expr.lookupArgs, valsNat, List.getD_cons_succ]
          exact ih k hk

omit [DialectDenote d] in
theorem opLeak_eq_of_accepts (M : LeakModel d) {Γ : Ctxt d} {L : Labels Γ}
    {V₁ V₂ : Ctxt.Valuation Γ} (h : PubEqV L V₁ V₂) (op : d.Op)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig op))
    (hacc : opAccepts M op (argLvls L args) = true) :
    opLeak M op (Expr.lookupArgs args V₁) = opLeak M op (Expr.lookupArgs args V₂) := by
  unfold opAccepts at hacc
  unfold opLeak
  split
  · rfl
  · next k hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc
      rw [valsNat_getD_eq_of_pub M h args k hacc]
  · next m hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc
      rw [lookupArgs_eq_of_pub h args hacc]
  · next f hk =>
      rw [hk] at hacc
      simp only [decide_eq_true_eq] at hacc
      rw [lookupArgs_eq_of_pub h args hacc]

/-- **Soundness of the level checker.** A program the checker accepts for the
    entry labels `L` is constant time for `L`. -/
theorem levelCheck_sound (M : LeakModel d) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (L : Labels Γ),
      Com.levelCheck M c L = true → ComCT M L c := by
  intro Γ t c
  induction c with
  | ret v => intro L _ V₁ V₂ _; rfl
  | @var Γ t s e body ih =>
      intro L hc V₁ V₂ hpub
      simp only [Com.levelCheck, Bool.and_eq_true] at hc
      obtain ⟨hacc, hbody⟩ := hc
      simp only [Com.ctLeak, Expr.ctLeak]
      rw [opLeak_eq_of_accepts M hpub e.op e.args hacc]
      congr 1
      apply ih _ hbody
      intro t' v hv
      cases v with
      | here =>
          have heq : Expr.lookupArgs e.args V₁ = Expr.lookupArgs e.args V₂ :=
            lookupArgs_eq_of_pub hpub e.args hv
          simp only [Ctxt.Valuation.extend, Ctxt.Var.lookup, Expr.denote, heq]
      | there v =>
          simp only [Ctxt.Valuation.extend, Ctxt.Var.lookup]
          exact hpub _ v hv

end CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
