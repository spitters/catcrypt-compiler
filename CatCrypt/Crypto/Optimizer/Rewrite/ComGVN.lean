/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Data.HashMap
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-!
# Global value numbering of `Com jasminDialect` by hash-consing

A `Com → Com` pass over the typed VIR `jasminDialect` that merges structurally equal
bindings of pure operations. The pass walks the let-chain once and carries

* a renaming `ρ : Ctxt.Hom Γ Δ` from the context of the input program to the context of
  the output program, as in `CopyProp.copyElimGo`, and
* a node table `Tbl`: a hash map from the argument levels of a binding to the list of
  pairs (operation, result level) of the output bindings with those arguments. A level
  counts positions from the bottom of the context, so it is stable under the extension of
  the context by a binding and the table is never re-indexed.

At a binding `let x = op(args)` whose operation is pure (`gvnPure`), the renamed
expression is looked up in the table by its key (operation, argument levels). On a hit
the binding is dropped and `x` is mapped to the output variable of the earlier node; on a
miss the binding is kept and its key is entered. Purity is decided from the operation
alone: stack loads and stores, external and multi-result calls, and the operations of the
instruction pairs of the x86 lowering (`pairedOp`: the multiply and the high multiply, the
carry-chain add and its carry-out) are never merged.

## Main results

* `gvnGo_denote`: under a table sound for the valuation, the output of the traversal
  denotes the input at the pulled-back valuation.
* `gvnCom`, `gvnCom_denote`: the pass from the empty table; it denotes the same function
  as its input.
* `gvnCom_cost_le`: the pass does not increase `comCost`.
* `gvnCom_ctSafe`: the pass preserves `ctSafeComJ`.
* `gvnGo_ctLeak`, `gvnCom_ctLeak_eq`, `gvnCom_constantTime`: for every leakage model
  (`ComLevelCheck.LeakModel`), equal leakage of the input at two valuations gives equal
  leakage of the output, so the pass preserves constant time for every public-equality
  relation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ComGVN

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph (opCost comCost ctSafeComJ ctSafeComJ_true)
open CatCrypt.Crypto.Optimizer.CopyProp
  (pullV consHom pullV_consHom pullV_lift pullV_id Expr.denote_rename)

/-! ## 1. Purity -/

/-- The low halves of the instruction pairs of the x86 lowering: the multiply
    `regArith .mul w`, whose `MUL` the `MULX` fusion pairs with the `MULXHI` of `mulhi w`
    on the same sources, and the carry-chain add `addCarryLo w`, whose `ADCX` sets the
    carry flag that the `setc` of the paired `addCarryHi w` reads. -/
def pairLowOp : JasminOp → Bool
  | .regArith .mul _ | .addCarryLo _ => true
  | _ => false

/-- The operations of the instruction pairs of the x86 lowering: the low halves
    (`pairLowOp`) and the high halves `mulhi w` and `addCarryHi w`. -/
def pairedOp : JasminOp → Bool
  | .mulhi _ | .addCarryHi _ => true
  | op => pairLowOp op

/-- The operations whose bindings the pass may merge: every operation other than a stack
    load or store, an external call, a multi-result call and an operation of an
    instruction pair of the x86 lowering (`pairedOp`). -/
def gvnPure : JasminOp → Bool
  | .stackLoad _ _ | .stackStore _ _ | .extCall _ _ _ | .callN _ _ _ => false
  | op => !pairedOp op

/-! ## 2. Levels and their reading in a valuation -/

/-- The level of a variable: its position counted from the bottom of the context. -/
def varLvl {Δ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Δ t) : Nat :=
  Δ.length - 1 - varDepth v

/-- The levels of an argument vector. -/
def argLvls {Δ : Ctxt jasminDialect} : {tys : List JasminTy} →
    HVector (fun ty => Ctxt.Var Δ ty) tys → List Nat
  | [], .nil => []
  | _ :: _, .cons v rest => varLvl v :: argLvls rest

/-- The typed value at de Bruijn index `k` of a valuation. -/
def getDepth : {Γ : Ctxt jasminDialect} → Ctxt.Valuation Γ → Nat →
    Option (Σ t : JasminTy, ⟦t⟧)
  | [], .nil, _ => none
  | t :: _, .cons x _, 0 => some ⟨t, x⟩
  | _ :: _, .cons _ V, k + 1 => getDepth V k

/-- The typed value at level `l` of a valuation. -/
def getLvl {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (l : Nat) :
    Option (Σ t : JasminTy, ⟦t⟧) :=
  if l < Γ.length then getDepth V (Γ.length - 1 - l) else none

/-- A typed value read at the type `ty`, when its type is `ty`. -/
def castTo? (p : Σ t : JasminTy, ⟦t⟧) (ty : JasminTy) : Option ⟦ty⟧ :=
  if h : p.1 = ty then some (h ▸ p.2) else none

/-- The argument values at the levels `ls`, read at the types `tys`. -/
def gatherArgs {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (tys : List JasminTy) → List Nat → Option (HVector (fun t => ⟦t⟧) tys)
  | [], [] => some .nil
  | ty :: tys, l :: ls =>
      match (getLvl V l).bind (castTo? · ty), gatherArgs V tys ls with
      | some x, some rest => some (.cons x rest)
      | _, _ => none
  | _, _ => none

/-- The value of the node with operation `op` and argument levels `lv` in a valuation. -/
def evalKey {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (op : JasminOp)
    (lv : List Nat) : Option (Σ t : JasminTy, ⟦t⟧) :=
  (gatherArgs V (DialectSignature.sig (d := jasminDialect) op) lv).map fun a =>
    ⟨DialectSignature.ret (d := jasminDialect) op, DialectDenote.denote (d := jasminDialect) op a⟩

/-- The variable of type `s` at de Bruijn index `k`, when the binding there has type `s`. -/
def varOfDepth? : (Δ : Ctxt jasminDialect) → (s : JasminTy) → Nat → Option (Ctxt.Var Δ s)
  | [], _, _ => none
  | t :: _, s, 0 => if h : t = s then some (h ▸ Ctxt.Var.here) else none
  | _ :: Δ, s, k + 1 => (varOfDepth? Δ s k).map Ctxt.Var.there

/-- The variable of type `s` at level `l`, when the binding there has type `s`. -/
def varOfLvl? (Δ : Ctxt jasminDialect) (s : JasminTy) (l : Nat) : Option (Ctxt.Var Δ s) :=
  if l < Δ.length then varOfDepth? Δ s (Δ.length - 1 - l) else none

/-! ### Lemmas on levels -/

theorem getDepth_var : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ), getDepth V (varDepth v) = some ⟨t, v.lookup V⟩
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ V => getDepth_var v V

theorem getLvl_var {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) : getLvl V (varLvl v) = some ⟨t, v.lookup V⟩ := by
  have hlt := varDepth_lt v
  unfold getLvl varLvl
  rw [if_pos (by omega), show Γ.length - 1 - (Γ.length - 1 - varDepth v) = varDepth v by omega]
  exact getDepth_var v V

theorem getLvl_extend_some {Γ : Ctxt jasminDialect} {s : JasminTy}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) {l : Nat} {p : Σ t : JasminTy, ⟦t⟧}
    (h : getLvl V l = some p) :
    getLvl (Γ := s :: Γ) (V.extend x) l = some p := by
  unfold getLvl at h ⊢
  split at h
  · rename_i hl
    rw [if_pos (by simp; omega)]
    simp only [List.length_cons]
    rw [show Γ.length + 1 - 1 - l = (Γ.length - 1 - l) + 1 by omega]
    exact h
  · cases h

theorem getLvl_extend_top {Γ : Ctxt jasminDialect} {s : JasminTy}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) :
    getLvl (Γ := s :: Γ) (V.extend x) Γ.length = some ⟨s, x⟩ := by
  unfold getLvl
  rw [if_pos (by simp)]
  simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]
  rfl

theorem castTo?_mk (ty : JasminTy) (x : ⟦ty⟧) : castTo? ⟨ty, x⟩ ty = some x := by
  simp [castTo?]

theorem gatherArgs_extend_some {Γ : Ctxt jasminDialect} {s : JasminTy}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) :
    ∀ (tys : List JasminTy) (ls : List Nat) (a : HVector (fun t => ⟦t⟧) tys),
      gatherArgs V tys ls = some a → gatherArgs (Γ := s :: Γ) (V.extend x) tys ls = some a
  | [], [], _, h => h
  | [], _ :: _, _, h => by simp [gatherArgs] at h
  | _ :: _, [], _, h => by simp [gatherArgs] at h
  | ty :: tys, l :: ls, a, h => by
      unfold gatherArgs at h ⊢
      rcases hg : getLvl V l with _ | p
      · simp [hg] at h
      · rcases hr : gatherArgs V tys ls with _ | rest
        · simp [hg, hr] at h
        · rw [getLvl_extend_some V x hg, gatherArgs_extend_some V x tys ls rest hr]
          simpa [hg, hr] using h

theorem evalKey_extend_some {Γ : Ctxt jasminDialect} {s : JasminTy}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) {op : JasminOp} {lv : List Nat}
    {p : Σ t : JasminTy, ⟦t⟧} (h : evalKey V op lv = some p) :
    evalKey (Γ := s :: Γ) (V.extend x) op lv = some p := by
  unfold evalKey at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [gatherArgs_extend_some V x _ _ a ha]
  rfl

theorem gatherArgs_argLvls {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    ∀ {tys : List JasminTy} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      gatherArgs V tys (argLvls args) = some (Expr.lookupArgs args V)
  | [], .nil => rfl
  | ty :: _, .cons v rest => by
      show gatherArgs V (ty :: _) (varLvl v :: argLvls rest) =
        some (.cons (v.lookup V) (Expr.lookupArgs rest V))
      simp only [gatherArgs]
      rw [getLvl_var v V, gatherArgs_argLvls V rest]
      simp only [Option.bind_some, castTo?_mk]

theorem evalKey_expr {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) : evalKey V e.op (argLvls e.args) = some ⟨t, e.denote V⟩ := by
  rcases e with ⟨op, hop, args⟩
  cases hop
  unfold evalKey
  rw [gatherArgs_argLvls V args]
  rfl

theorem varOfDepth?_lookup : ∀ (Δ : Ctxt jasminDialect) (s : JasminTy) (k : Nat)
    (w : Ctxt.Var Δ s), varOfDepth? Δ s k = some w →
      ∀ V : Ctxt.Valuation Δ, getDepth V k = some ⟨s, w.lookup V⟩
  | [], _, _, _, h, _ => by simp [varOfDepth?] at h
  | t :: Δ, s, 0, w, h, V => by
      unfold varOfDepth? at h
      split at h
      · rename_i hts
        subst hts
        cases h
        cases V
        rfl
      · cases h
  | t :: Δ, s, k + 1, w, h, V => by
      unfold varOfDepth? at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      cases V with
      | cons y V' => exact varOfDepth?_lookup Δ s k w' hw' V'

theorem varOfLvl?_lookup {Δ : Ctxt jasminDialect} {s : JasminTy} {l : Nat}
    {w : Ctxt.Var Δ s} (h : varOfLvl? Δ s l = some w) (V : Ctxt.Valuation Δ) :
    getLvl V l = some ⟨s, w.lookup V⟩ := by
  unfold varOfLvl? at h
  unfold getLvl
  split at h
  · rw [if_pos ‹_›]
    exact varOfDepth?_lookup Δ s _ w h V
  · cases h

/-! ## 3. The node table -/

/-- The node table: for each list of argument levels, the operations of the nodes with
    those arguments and the level of each node's result. -/
abbrev Tbl := Std.HashMap (List Nat) (List (JasminOp × Nat))

/-- A table is sound for a valuation when every node it records evaluates, at that
    valuation, to the value at its result level. -/
def Sound {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) (M : Tbl) : Prop :=
  ∀ (lv : List Nat) (bucket : List (JasminOp × Nat)), M[lv]? = some bucket →
    ∀ p ∈ bucket, ∃ x, evalKey V p.1 lv = some x ∧ getLvl V p.2 = some x

theorem sound_empty {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    Sound V (∅ : Tbl) := by
  intro lv bucket h
  simp at h

theorem sound_extend {Γ : Ctxt jasminDialect} {s : JasminTy} {V : Ctxt.Valuation Γ}
    (x : ⟦s⟧) {M : Tbl} (hM : Sound V M) : Sound (Γ := s :: Γ) (V.extend x) M := by
  intro lv bucket h p hp
  obtain ⟨y, h1, h2⟩ := hM lv bucket h p hp
  exact ⟨y, evalKey_extend_some V x h1, getLvl_extend_some V x h2⟩

/-- The output variable of type `s` of a recorded node with operation `op` and argument
    levels `lv`, when `op` is pure. -/
def findVar (Δ : Ctxt jasminDialect) (s : JasminTy) (M : Tbl) (op : JasminOp)
    (lv : List Nat) : Option (Ctxt.Var Δ s) :=
  if gvnPure op then
    match M[lv]? with
    | some bucket =>
        match bucket.find? (fun p => p.1 == op) with
        | some p => varOfLvl? Δ s p.2
        | none => none
    | none => none
  else none

theorem findVar_sound {Δ : Ctxt jasminDialect} {s : JasminTy} {M : Tbl} {op : JasminOp}
    {lv : List Nat} {w : Ctxt.Var Δ s} {V : Ctxt.Valuation Δ} (hM : Sound V M)
    (h : findVar Δ s M op lv = some w) : evalKey V op lv = some ⟨s, w.lookup V⟩ := by
  unfold findVar at h
  split at h
  · split at h
    · rename_i bucket hb
      split at h
      · rename_i p hp
        have hmem := List.mem_of_find?_eq_some hp
        have hop : p.1 = op := by simpa using List.find?_some hp
        obtain ⟨y, h1, h2⟩ := hM lv bucket hb p hmem
        rw [varOfLvl?_lookup h V] at h2
        rw [← hop, h1, h2]
      · cases h
    · cases h
  · cases h

/-- The table with the node (`op`, `lv`) of result level `n` entered, when `op` is pure. -/
def insertT (M : Tbl) (op : JasminOp) (lv : List Nat) (n : Nat) : Tbl :=
  if gvnPure op then M.insert lv ((op, n) :: M.getD lv []) else M

theorem sound_insertT {Δ : Ctxt jasminDialect} {s : JasminTy} {V : Ctxt.Valuation Δ}
    {M : Tbl} (hM : Sound V M) (e : Expr jasminDialect Δ s) :
    Sound (Γ := s :: Δ) (V.extend (e.denote V))
      (insertT M e.op (argLvls e.args) Δ.length) := by
  unfold insertT
  split
  · intro lv bucket h p hp
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      have hk' : argLvls e.args = lv := by simpa using hk
      subst hk'
      cases h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨⟨s, e.denote V⟩, evalKey_extend_some V _ (evalKey_expr e V),
          getLvl_extend_top V _⟩
      · rw [Std.HashMap.getD_eq_getD_getElem?] at hp'
        rcases hb : M[argLvls e.args]? with _ | b
        · simp [hb] at hp'
        · rw [hb] at hp'
          exact sound_extend _ hM _ b hb p hp'
    · exact sound_extend _ hM lv bucket h p hp
  · exact sound_extend _ hM

/-! ## 4. The pass -/

/-- Global value numbering under the renaming `ρ` and the node table `M`: a binding of a
    pure operation whose renamed key is recorded is dropped and its variable mapped to the
    recorded node; every other binding is renamed by `ρ`, kept and recorded. -/
def gvnGo : {Γ Δ : Ctxt jasminDialect} → {t : JasminTy} → Ctxt.Hom Γ Δ → Tbl →
    Com jasminDialect Γ t → Com jasminDialect Δ t
  | _, _, _, ρ, _, .ret v => .ret (ρ v)
  | _, Δ, _, ρ, M, .var (t := s) e body =>
      match findVar Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with
      | some w => gvnGo (consHom w ρ) M body
      | none =>
          .var (e.rename ρ)
            (gvnGo ρ.lift (insertT M (e.rename ρ).op (argLvls (e.rename ρ).args) Δ.length)
              body)

/-- **Denotation of the traversal.** Under a table sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem gvnGo_denote : ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Δ),
    Sound V M → (gvnGo ρ M c).denote V = c.denote (pullV ρ V)
  | _, _, _, ρ, _, .ret v, V, _ => CopyProp.Ctxt.Var.lookup_rename ρ v V
  | _, Δ, _, ρ, M, .var (t := s) e body, V, hM => by
      simp only [gvnGo]
      rcases hc : findVar Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [Com.denote]
        rw [gvnGo_denote ρ.lift _ body _ (sound_insertT hM (e.rename ρ)),
          Expr.denote_rename ρ e V, pullV_lift]
      · simp only [Com.denote]
        have h1 := findVar_sound hM hc
        rw [evalKey_expr (e.rename ρ) V] at h1
        have h2 : w.lookup V = (e.rename ρ).denote V :=
          (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h1)).2).symm
        rw [gvnGo_denote (consHom w ρ) M body V hM, pullV_consHom, h2,
          Expr.denote_rename ρ e V]

/-- **Global value numbering**: the traversal from the identity renaming and the empty
    table. -/
def gvnCom {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  gvnGo (Ctxt.Hom.id Γ) ∅ c

/-- **Denotation of the pass.** `gvnCom c` denotes the same function as `c`. -/
theorem gvnCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : (gvnCom c).denote = c.denote :=
  funext fun V => by rw [gvnCom, gvnGo_denote _ _ c V (sound_empty V), pullV_id]

/-! ## 5. Cost and constant time -/

theorem gvnGo_cost_le : ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t),
    comCost (gvnGo ρ M c) ≤ comCost c
  | _, _, _, ρ, _, .ret v => Nat.le_refl _
  | _, Δ, _, ρ, M, .var (t := s) e body => by
      simp only [gvnGo]
      rcases findVar Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [comCost]
        have := gvnGo_cost_le ρ.lift
          (insertT M (e.rename ρ).op (argLvls (e.rename ρ).args) Δ.length) body
        exact Nat.add_le_add_left this _
      · simp only [comCost]
        exact Nat.le_trans (gvnGo_cost_le (consHom w ρ) M body) (Nat.le_add_left _ _)

/-- The pass does not increase `comCost`. -/
theorem gvnCom_cost_le {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comCost (gvnCom c) ≤ comCost c :=
  gvnGo_cost_le _ _ c

/-- The pass preserves the structural CT predicate `ctSafeComJ`. -/
theorem gvnCom_ctSafe {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : ctSafeComJ (gvnCom c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (gvnCom c), ctSafeComJ_true c]

/-! ## 6. Constant time under a leakage model

The leakage of a `Com` (`ComLevelCheck.Com.ctLeak`) is the concatenation of the events of
its bindings, and the number of events of one binding depends on its operation alone. The
output of `gvnGo` keeps a subsequence of the bindings of its input, chosen without
reference to the valuation, so equal input leakage gives equal output leakage, for every
leakage model. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime)
open CatCrypt.Crypto.Optimizer.CopyProp (lookupArgs_renameVars)

/-- The number of events of an operation does not depend on its argument values. -/
theorem opLeak_length (L : LeakModel jasminDialect) (op : JasminOp)
    (a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig (d := jasminDialect) op)) :
    (opLeak L op a).length = (opLeak L op b).length := by
  unfold opLeak
  rcases L.kind op <;> rfl

/-- The events of a renamed expression are those of the expression at the pulled-back
    valuation. -/
theorem Expr.ctLeak_rename (L : LeakModel jasminDialect) {Γ Δ : Ctxt jasminDialect}
    {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Δ) :
    Expr.ctLeak L (e.rename ρ) V = Expr.ctLeak L e (pullV ρ V) := by
  simp only [Expr.ctLeak, Expr.rename]
  rw [lookupArgs_renameVars]

/-- **Leakage of the traversal.** Under tables sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem gvnGo_ctLeak (L : LeakModel jasminDialect) : ∀ {Γ Δ : Ctxt jasminDialect}
    {t : JasminTy} (ρ : Ctxt.Hom Γ Δ) (M : Tbl) (c : Com jasminDialect Γ t)
    (V₁ V₂ : Ctxt.Valuation Δ), Sound V₁ M → Sound V₂ M →
    Com.ctLeak L c (pullV ρ V₁) = Com.ctLeak L c (pullV ρ V₂) →
    Com.ctLeak L (gvnGo ρ M c) V₁ = Com.ctLeak L (gvnGo ρ M c) V₂
  | _, _, _, ρ, _, .ret v, _, _, _, _, _ => rfl
  | _, Δ, _, ρ, M, .var (t := s) e body, V₁, V₂, h₁, h₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
      simp only [gvnGo]
      rcases hc : findVar Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [Com.ctLeak]
        rw [Expr.ctLeak_rename, Expr.ctLeak_rename, hE]
        congr 1
        refine gvnGo_ctLeak L ρ.lift _ body _ _ (sound_insertT h₁ (e.rename ρ))
          (sound_insertT h₂ (e.rename ρ)) ?_
        rw [pullV_lift, pullV_lift, Expr.denote_rename, Expr.denote_rename]
        exact hB
      · have hw : ∀ V : Ctxt.Valuation Δ, Sound V M → w.lookup V = e.denote (pullV ρ V) := by
          intro V hV
          have h1 := findVar_sound hV hc
          rw [evalKey_expr (e.rename ρ) V] at h1
          rw [← Expr.denote_rename ρ e V]
          exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h1)).2).symm
        refine gvnGo_ctLeak L (consHom w ρ) M body V₁ V₂ h₁ h₂ ?_
        rw [pullV_consHom, pullV_consHom, hw V₁ h₁, hw V₂ h₂]
        exact hB

/-- **Leakage of the pass.** Equal leakage of `c` at two valuations gives equal leakage of
    `gvnCom c` there. -/
theorem gvnCom_ctLeak_eq (L : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (gvnCom c) V₁ = Com.ctLeak L (gvnCom c) V₂ :=
  gvnGo_ctLeak L _ _ c V₁ V₂ (sound_empty V₁) (sound_empty V₂)
    (by rw [pullV_id, pullV_id]; exact h)

/-- **Constant time of the pass.** If `c` is constant time for the public-equality
    relation `R`, so is `gvnCom c`. -/
theorem gvnCom_constantTime (L : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (gvnCom c)) :=
  fun V₁ V₂ hR => gvnCom_ctLeak_eq L c V₁ V₂ (h V₁ V₂ hR)

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.ComGVN
