/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Input specialisation of a `Com`

Given a program `c : Com d Γ τ` and an assignment of constants to some of its inputs,
`specialize` produces a program over the remaining inputs. Each fixed input becomes a
binding of a nullary operation (a constant expression of the dialect) at the head of
the program, and the body is renamed onto those bindings and the free inputs.

The assignment `Spec Γ Δ` walks `Γ`: each input is either kept (it appears in `Δ`) or
fixed to a `ConstOp`, a nullary operation of the input's type. The pass is stated for
every dialect; for `jasminDialect` the constants are `regConst` bindings
(`regConstOp`), so a lane map broadcasts them instead of reading them from registers.

## Main definitions

* `ConstOp d t`: a nullary operation of result type `t`.
* `Spec Γ Δ`: an assignment of constants to the inputs of `Γ` not in `Δ`.
* `Spec.extend`: the valuation of `Γ` extending a valuation of `Δ` with the constants.
* `specialize s c`: the specialised program over `Δ`.
* `regConstOp`, `fixRegs`, `Spec.keepN`: builders for register contexts.

## Main results

* `specialize_denote`: `(specialize s c).denote V = c.denote (s.extend V)`.
* `pullV_eq_of_lookup`: a pullback valuation is determined by its lookups.

The renaming step reuses `Com.rename` (`MergeCom`) and its dialect-generic denotation
law `FieldDialectBlockDescent.Com.denote_rename`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComSpecialize

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var)

section Generic

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-! ## 1. Constant operations -/

/-- A nullary operation of result type `t`: a constant expression of the dialect. -/
structure ConstOp (d : Dialect) [DialectSignature d] (t : d.Ty) where
  /-- The operation. -/
  op : d.Op
  /-- It takes no arguments. -/
  sig_eq : DialectSignature.sig op = []
  /-- Its result type is `t`. -/
  ret_eq : DialectSignature.ret op = t

/-- The empty argument vector at a signature equal to `[]`. -/
def nilArgs {Γ : Ctxt d} : (l : List d.Ty) → l = [] → HVector (fun ty => Var Γ ty) l
  | [], _ => .nil

/-- The empty value vector at a signature equal to `[]`. -/
def nilVals : (l : List d.Ty) → l = [] → HVector (fun t => ⟦t⟧) l
  | [], _ => .nil

omit [DialectSignature d] [DialectDenote d] in
theorem lookupArgs_nilArgs {Γ : Ctxt d} :
    (l : List d.Ty) → (h : l = []) → (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (nilArgs l h) V = nilVals l h
  | [], _, _ => rfl

namespace ConstOp

/-- The constant as an expression over any context. -/
def expr {t : d.Ty} {Γ : Ctxt d} (c : ConstOp d t) : Expr d Γ t :=
  { op := c.op, retTy_eq := c.ret_eq, args := nilArgs _ c.sig_eq }

/-- The value of the constant. -/
def val {t : d.Ty} (c : ConstOp d t) : ⟦t⟧ :=
  c.ret_eq ▸ DialectDenote.denote c.op (nilVals _ c.sig_eq)

theorem expr_denote {t : d.Ty} {Γ : Ctxt d} (c : ConstOp d t) (V : Ctxt.Valuation Γ) :
    (c.expr : Expr d Γ t).denote V = c.val := by
  show c.ret_eq ▸ DialectDenote.denote c.op (Expr.lookupArgs (nilArgs _ c.sig_eq) V) = _
  rw [lookupArgs_nilArgs]
  rfl

/-- The values of a vector of constants. -/
def vals : {l : Ctxt d} → HVector (ConstOp d) l → HVector (fun t => ⟦t⟧) l
  | [], .nil => .nil
  | _ :: _, .cons c cs => .cons c.val (vals cs)

/-- Every constant of the vector satisfies `P`. -/
def All (P : {t : d.Ty} → ConstOp d t → Prop) : {l : Ctxt d} → HVector (ConstOp d) l → Prop
  | [], .nil => True
  | _ :: _, .cons c cs => P c ∧ All P cs

end ConstOp

/-! ## 2. Valuations of an appended context -/

/-- The valuation of `l ++ Δ` made of a valuation of `l` followed by one of `Δ`. -/
def appendVal {Δ : Ctxt d} : {l : Ctxt d} → HVector (fun t => ⟦t⟧) l →
    Ctxt.Valuation Δ → Ctxt.Valuation (l ++ Δ)
  | [], .nil, V => V
  | _ :: _, .cons x C, V => .cons x (appendVal C V)

/-- The variable at position `l.length` of `l ++ t :: Δ`. -/
def midVar {t : d.Ty} {Δ : Ctxt d} : (l : Ctxt d) → Var (l ++ t :: Δ) t
  | [] => .here
  | _ :: l => .there (midVar l)

/-- Weakening past a binding inserted at position `l.length`. -/
def weakenMid {t s : d.Ty} {Δ : Ctxt d} : (l : Ctxt d) → Var (l ++ Δ) s → Var (l ++ t :: Δ) s
  | [], v => .there v
  | _ :: _, .here => .here
  | _ :: l, .there v => .there (weakenMid l v)

omit [DialectSignature d] [DialectDenote d] in
theorem midVar_lookup {t : d.Ty} {Δ : Ctxt d} (x : ⟦t⟧) (V : Ctxt.Valuation Δ) :
    {l : Ctxt d} → (C : HVector (fun t => ⟦t⟧) l) →
    (midVar l : Var (l ++ t :: Δ) t).lookup (appendVal C (.cons x V)) = x
  | [], .nil => rfl
  | _ :: _, .cons _ C => midVar_lookup x V C

omit [DialectSignature d] [DialectDenote d] in
theorem weakenMid_lookup {t s : d.Ty} {Δ : Ctxt d} (x : ⟦t⟧) (V : Ctxt.Valuation Δ) :
    {l : Ctxt d} → (C : HVector (fun t => ⟦t⟧) l) → (v : Var (l ++ Δ) s) →
    (weakenMid (t := t) l v).lookup (appendVal C (.cons x V)) = v.lookup (appendVal C V)
  | [], .nil, _ => rfl
  | _ :: _, .cons _ _, .here => rfl
  | _ :: _, .cons _ C, .there v => weakenMid_lookup x V C v

omit [DialectSignature d] [DialectDenote d] in
/-- A pullback is determined by the lookups it must reproduce. -/
theorem pullV_eq_of_lookup {Γ Θ : Ctxt d} (h : Ctxt.Hom Γ Θ) (W : Ctxt.Valuation Θ)
    (U : Ctxt.Valuation Γ) (hU : ∀ {t : d.Ty} (v : Var Γ t), (h v).lookup W = v.lookup U) :
    FieldDialectBlockDescent.pullV h W = U := by
  induction Γ with
  | nil => cases U; rfl
  | cons a Γ ih =>
      cases U with
      | cons u U =>
          simp only [FieldDialectBlockDescent.pullV]
          rw [hU .here, ih (fun v => h (.there v)) U (fun v => hU (.there v))]
          rfl

/-! ## 3. Partial constant assignments -/

/-- `Spec Γ Δ`: an assignment of constants to some inputs of `Γ`; `Δ` lists the
    inputs left free, in their order in `Γ`. -/
inductive Spec : Ctxt d → Ctxt d → Type _ where
  /-- The empty context. -/
  | nil : Spec [] []
  /-- The head input stays an input. -/
  | keep {Γ Δ : Ctxt d} (t : d.Ty) : Spec Γ Δ → Spec (t :: Γ) (t :: Δ)
  /-- The head input is the constant `c`. -/
  | fix {Γ Δ : Ctxt d} {t : d.Ty} (c : ConstOp d t) : Spec Γ Δ → Spec (t :: Γ) Δ

namespace Spec

/-- The types of the fixed inputs, in their order in `Γ`. -/
def consts {Γ Δ : Ctxt d} : Spec Γ Δ → Ctxt d
  | .nil => []
  | .keep _ s => s.consts
  | .fix (t := t) _ s => t :: s.consts

/-- The constants of the fixed inputs. -/
def ops {Γ Δ : Ctxt d} : (s : Spec Γ Δ) → HVector (ConstOp d) s.consts
  | .nil => .nil
  | .keep _ s => s.ops
  | .fix c s => .cons c s.ops

/-- The renaming of the inputs of `Γ` into the constants followed by the free inputs. -/
def hom {Γ Δ : Ctxt d} : (s : Spec Γ Δ) → Ctxt.Hom Γ (s.consts ++ Δ)
  | .nil => fun v => v
  | .keep _ s => fun
      | .here => midVar s.consts
      | .there v => weakenMid s.consts (s.hom v)
  | .fix _ s => fun
      | .here => .here
      | .there v => .there (s.hom v)

/-- The valuation of all inputs of `Γ` that extends a valuation of the free inputs
    with the constant values. -/
def extend {Γ Δ : Ctxt d} : Spec Γ Δ → Ctxt.Valuation Δ → Ctxt.Valuation Γ
  | .nil, V => V
  | .keep _ s, .cons x V => .cons x (s.extend V)
  | .fix c s, V => .cons c.val (s.extend V)

/-- Every constant of the assignment satisfies `P`. -/
def AllOps (P : {t : d.Ty} → ConstOp d t → Prop) {Γ Δ : Ctxt d} : Spec Γ Δ → Prop
  | .nil => True
  | .keep _ s => s.AllOps P
  | .fix c s => P c ∧ s.AllOps P

theorem hom_lookup {Γ Δ : Ctxt d} (s : Spec Γ Δ) (V : Ctxt.Valuation Δ) {t : d.Ty}
    (v : Var Γ t) :
    (s.hom v).lookup (appendVal (ConstOp.vals s.ops) V) = v.lookup (s.extend V) := by
  induction s with
  | nil => cases v
  | keep t' s ih =>
      cases V with
      | cons x V =>
          cases v with
          | here => exact midVar_lookup x V _
          | there v =>
              show (weakenMid s.consts (s.hom v)).lookup
                  (appendVal (ConstOp.vals s.ops) (.cons x V)) = v.lookup (s.extend V)
              rw [weakenMid_lookup]
              exact ih V v
  | fix c s ih =>
      cases v with
      | here => rfl
      | there v => exact ih V v

omit [TyDenote d.Ty] [DialectDenote d] in
theorem allOps_ops (P : {t : d.Ty} → ConstOp d t → Prop) {Γ Δ : Ctxt d} (s : Spec Γ Δ)
    (h : s.AllOps P) : ConstOp.All P s.ops := by
  induction s with
  | nil => trivial
  | keep _ s ih => exact ih h
  | fix c s ih => exact ⟨h.1, ih h.2⟩

/-- Keep the first `k` inputs of a context of `k` copies of `t` ahead of `Γ`. -/
def keepN (t : d.Ty) {Γ : Ctxt d} (s : Spec Γ []) :
    (k : Nat) → Spec (List.replicate k t ++ Γ) (List.replicate k t)
  | 0 => s
  | k + 1 => .keep t (keepN t s k)

omit [TyDenote d.Ty] [DialectDenote d] in
theorem allOps_keepN (P : {t : d.Ty} → ConstOp d t → Prop) (t : d.Ty) {Γ : Ctxt d}
    (s : Spec Γ []) (h : s.AllOps P) : (k : Nat) → (keepN t s k).AllOps P
  | 0 => h
  | k + 1 => allOps_keepN P t s h k

end Spec

/-! ## 4. The pass -/

/-- Bind the constants `cs` at the head of a program over `l ++ Δ`. -/
def bindConsts {Δ : Ctxt d} {τ : d.Ty} :
    (l : Ctxt d) → HVector (ConstOp d) l → Com d (l ++ Δ) τ → Com d Δ τ
  | [], .nil, c => c
  | _ :: l, .cons k ks, c => bindConsts l ks (.var k.expr c)

theorem bindConsts_denote {Δ : Ctxt d} {τ : d.Ty} :
    (l : Ctxt d) → (cs : HVector (ConstOp d) l) → (c : Com d (l ++ Δ) τ) →
    (V : Ctxt.Valuation Δ) →
    (bindConsts l cs c).denote V = c.denote (appendVal (ConstOp.vals cs) V)
  | [], .nil, _, _ => rfl
  | _ :: l, .cons k ks, c, V => by
      rw [bindConsts, bindConsts_denote l ks _ V]
      show c.denote (Ctxt.Valuation.extend _ (k.expr.denote _)) = _
      rw [ConstOp.expr_denote]
      rfl

/-- **Input specialisation.** The program over the free inputs `Δ` of `s` that binds
    each fixed input to its constant at the head and renames the body onto the
    constants and the free inputs. -/
def specialize {Γ Δ : Ctxt d} {τ : d.Ty} (s : Spec Γ Δ) (c : Com d Γ τ) : Com d Δ τ :=
  bindConsts s.consts s.ops (Com.rename s.hom c)

/-- **Denotation of the specialised program.** On a valuation of the free inputs it is
    the original program on the valuation of all inputs that extends it with the
    constants. -/
theorem specialize_denote {Γ Δ : Ctxt d} {τ : d.Ty} (s : Spec Γ Δ) (c : Com d Γ τ)
    (V : Ctxt.Valuation Δ) : (specialize s c).denote V = c.denote (s.extend V) := by
  rw [specialize, bindConsts_denote, FieldDialectBlockDescent.Com.denote_rename,
    pullV_eq_of_lookup _ _ _ (fun v => s.hom_lookup V v)]

end Generic

/-! ## 5. Register constants of `jasminDialect` -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The `regConst w n` operation as a constant of type `reg w`. -/
def regConstOp (w n : Nat) : ConstOp jasminDialect (.reg w) := ⟨.regConst w n, rfl, rfl⟩

theorem regConstOp_val (w n : Nat) : (regConstOp w n).val = BitVec.ofNat w n := rfl

/-- Fix every input of a context of `m` registers of width `w`: input `j` is the
    constant `g j`. -/
def fixRegs (w : Nat) (g : Nat → Nat) :
    (m : Nat) → Spec (d := jasminDialect) (List.replicate m (JasminTy.reg w)) []
  | 0 => .nil
  | m + 1 => .fix (regConstOp w (g 0)) (fixRegs w (fun j => g (j + 1)) m)

theorem allOps_fixRegs (P : {t : JasminTy} → ConstOp jasminDialect t → Prop) (w : Nat)
    (hP : ∀ n, P (regConstOp w n)) : (g : Nat → Nat) → (m : Nat) → (fixRegs w g m).AllOps P
  | _, 0 => trivial
  | g, m + 1 => ⟨hP (g 0), allOps_fixRegs P w hP (fun j => g (j + 1)) m⟩

end CatCrypt.Crypto.SecureCompilation.VIR.ComSpecialize
