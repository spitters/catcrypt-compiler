/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Peephole
public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.ComVarDepth

/-!
# Global value numbering and the acyclic e-graph over an arbitrary dialect

Two `Com → Com` passes over a dialect `d`, each a single walk of the let-chain that carries
a renaming `ρ : Ctxt.Hom Γ Δ` from the context of the input program to the context of the
output program, and tables keyed by levels (positions counted from the bottom of the
context, stable under the extension of the context by a binding):

* the node table `Tbl d`, from argument levels to the pairs (operation, result level) of
  the recorded nodes; and
* the definition table `Defs d`, from a result level to the operation and argument levels
  of one node defining it, read by the rules.

Global value numbering (`gvnGo`) drops a binding whose renamed key (operation, argument
levels) is recorded and maps its variable to the recorded node. The acyclic e-graph
(`agGo`), in the style of Cranelift, forms at each binding the e-class of the renamed
expression: the expression and the alternatives (`Alt`) the rules of a rule set produce
for it, each hash-consed through the node table. Each rule fires once, at the creation of
the node. Extraction (`choose`) takes the alternative of least key among those whose cost
does not exceed the cost of the expression. The class is a union node: the key of every
one-binding alternative is entered in the node table at the level of the chosen value.

## What a dialect provides

The dialect `d : Dialect.{0, 0}` (operations and types in `Type`) carries
`TyDenote d.Ty`, `DialectSignature d`, `DialectDenote d`, and decidable equality on its
types and its operations (`DecidableEq d.Ty`, `DecidableEq d.Op`). The tables are keyed by
levels, so no hash or order on operations is needed: operations are compared by decidable
equality within a bucket. A rule set (`RuleSet d`) provides the rules, each with its
soundness against the denotation of `d` (`Rule`), the cost of an operation, the extraction
weight of an operation, and the operations the node table may merge (`RuleSet.pure`).

## Main results

* `gvnGo_denote`, `gvnCom_denote`: the value numbering denotes its input.
* `RuleSet.alts_sound`: every alternative of a rule set denotes the expression, from the
  soundness of each rule.
* `extract_denote`, `choose_cost_le`: the extracted alternative denotes the expression and
  costs at most the expression.
* `aegraphOptOf`, `aegraphOptOf_denote`: the e-graph pass at a rule set; it denotes the
  same function as its input.
* `aegraphOptOf_cost_le`: the pass does not increase `comCostOf R.cost`.
* `aegraphOptOf_ctLeak_eq`, `aegraphOptOf_constantTime`: for a leakage model under which
  the events of every rule alternative do not depend on the valuation (`RulesIndep`),
  equal leakage of the input at two valuations gives equal leakage of the output.
* `gvnCom_ctLeak_eq`, `gvnCom_constantTime`: the same for value numbering, for every
  leakage model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Levels and renamings -/

section Levels

variable {d : Dialect.{0, 0}}

/-- The level of a variable: its position counted from the bottom of the context. -/
def varLvl {Δ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Δ t) : Nat :=
  Δ.length - 1 - varDepth v

/-- The levels of an argument vector. -/
def argLvls {Δ : Ctxt d} : {tys : List d.Ty} →
    HVector (fun ty => Ctxt.Var Δ ty) tys → List Nat
  | [], .nil => []
  | _ :: _, .cons v rest => varLvl v :: argLvls rest

/-- The renaming of `t :: Γ` that sends the head to `x` and the rest through `ρ`. -/
def consHom {Γ Δ : Ctxt d} {t : d.Ty} (x : Ctxt.Var Δ t) (ρ : Ctxt.Hom Γ Δ) :
    Ctxt.Hom (t :: Γ) Δ := fun
  | .here => x
  | .there v => ρ v

/-- Syntactic equality of two variables of the same type. -/
def varEq {Γ : Ctxt d} {t : d.Ty} : Ctxt.Var Γ t → Ctxt.Var Γ t → Bool
  | .here, .here => true
  | .there a, .there b => varEq a b
  | _, _ => false

theorem varEq_sound {Γ : Ctxt d} {t : d.Ty} :
    ∀ (a b : Ctxt.Var Γ t), varEq a b = true → a = b
  | .here, .here, _ => rfl
  | .there a, .there b, h => by rw [varEq] at h; rw [varEq_sound a b h]
  | .here, .there b, h => by simp [varEq] at h
  | .there a, .here, h => by simp [varEq] at h

/-- The renaming that shifts past two fresh bindings. -/
def wk2 {Γ Δ : Ctxt d} {s s1 : d.Ty} (ρ : Ctxt.Hom Γ Δ) : Ctxt.Hom Γ (s :: s1 :: Δ) :=
  fun v => (ρ v).there.there

variable [TyDenote d.Ty]

/-- The typed value at de Bruijn index `k` of a valuation. -/
def getDepth : {Γ : Ctxt d} → Ctxt.Valuation Γ → Nat → Option (Σ t : d.Ty, ⟦t⟧)
  | [], .nil, _ => none
  | t :: _, .cons x _, 0 => some ⟨t, x⟩
  | _ :: _, .cons _ V, k + 1 => getDepth V k

/-- The typed value at level `l` of a valuation. -/
def getLvl {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (l : Nat) : Option (Σ t : d.Ty, ⟦t⟧) :=
  if l < Γ.length then getDepth V (Γ.length - 1 - l) else none

theorem comap_consHom {Γ Δ : Ctxt d} {t : d.Ty} (x : Ctxt.Var Δ t) (ρ : Ctxt.Hom Γ Δ)
    (V : Ctxt.Valuation Δ) : V.comap (consHom x ρ) = (V.comap ρ).extend (x.lookup V) :=
  Ctxt.Valuation.ext _ _ fun _ w => by
    cases w <;> simp [consHom, Ctxt.Valuation.extend, Ctxt.Var.lookup]

theorem comap_wk2 {Γ Δ : Ctxt d} {s s1 : d.Ty} (ρ : Ctxt.Hom Γ Δ) (V : Ctxt.Valuation Δ)
    (x1 : ⟦s1⟧) (x : ⟦s⟧) :
    ((V.extend x1).extend x).comap (wk2 (s := s) (s1 := s1) ρ) = V.comap ρ :=
  Ctxt.Valuation.ext _ _ fun _ w => by
    simp [wk2, Ctxt.Valuation.extend, Ctxt.Var.lookup]

theorem getDepth_var : ∀ {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ), getDepth V (varDepth v) = some ⟨t, v.lookup V⟩
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ V => getDepth_var v V

theorem getLvl_var {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ) : getLvl V (varLvl v) = some ⟨t, v.lookup V⟩ := by
  have hlt := varDepth_lt v
  unfold getLvl varLvl
  rw [if_pos (by omega), show Γ.length - 1 - (Γ.length - 1 - varDepth v) = varDepth v by omega]
  exact getDepth_var v V

theorem getLvl_extend_some {Γ : Ctxt d} {s : d.Ty}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) {l : Nat} {p : Σ t : d.Ty, ⟦t⟧}
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

theorem getLvl_extend_top {Γ : Ctxt d} {s : d.Ty}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) :
    getLvl (Γ := s :: Γ) (V.extend x) Γ.length = some ⟨s, x⟩ := by
  unfold getLvl
  rw [if_pos (by simp)]
  simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]
  rfl

variable [DecidableEq d.Ty]

/-- A typed value read at the type `ty`, when its type is `ty`. -/
def castTo? (p : Σ t : d.Ty, ⟦t⟧) (ty : d.Ty) : Option ⟦ty⟧ :=
  if h : p.1 = ty then some (h ▸ p.2) else none

/-- The argument values at the levels `ls`, read at the types `tys`. -/
def gatherArgs {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    (tys : List d.Ty) → List Nat → Option (HVector (fun t => ⟦t⟧) tys)
  | [], [] => some .nil
  | ty :: tys, l :: ls =>
      match (getLvl V l).bind (castTo? · ty), gatherArgs V tys ls with
      | some x, some rest => some (.cons x rest)
      | _, _ => none
  | _, _ => none

omit [TyDenote d.Ty] in
/-- The variable of type `s` at de Bruijn index `k`, when the binding there has type `s`. -/
def varOfDepth? : (Δ : Ctxt d) → (s : d.Ty) → Nat → Option (Ctxt.Var Δ s)
  | [], _, _ => none
  | t :: _, s, 0 => if h : t = s then some (h ▸ Ctxt.Var.here) else none
  | _ :: Δ, s, k + 1 => (varOfDepth? Δ s k).map Ctxt.Var.there

omit [TyDenote d.Ty] in
/-- The variable of type `s` at level `l`, when the binding there has type `s`. -/
def varOfLvl? (Δ : Ctxt d) (s : d.Ty) (l : Nat) : Option (Ctxt.Var Δ s) :=
  if l < Δ.length then varOfDepth? Δ s (Δ.length - 1 - l) else none

theorem castTo?_mk (ty : d.Ty) (x : ⟦ty⟧) : castTo? ⟨ty, x⟩ ty = some x := by
  simp [castTo?]

theorem gatherArgs_extend_some {Γ : Ctxt d} {s : d.Ty}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) :
    ∀ (tys : List d.Ty) (ls : List Nat) (a : HVector (fun t => ⟦t⟧) tys),
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

theorem gatherArgs_argLvls {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    ∀ {tys : List d.Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      gatherArgs V tys (argLvls args) = some (Expr.lookupArgs args V)
  | [], .nil => rfl
  | ty :: _, .cons v rest => by
      show gatherArgs V (ty :: _) (varLvl v :: argLvls rest) =
        some (.cons (v.lookup V) (Expr.lookupArgs rest V))
      simp only [gatherArgs]
      rw [getLvl_var v V, gatherArgs_argLvls V rest]
      simp only [Option.bind_some, castTo?_mk]

theorem varOfDepth?_lookup : ∀ (Δ : Ctxt d) (s : d.Ty) (k : Nat)
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

theorem varOfLvl?_lookup {Δ : Ctxt d} {s : d.Ty} {l : Nat}
    {w : Ctxt.Var Δ s} (h : varOfLvl? Δ s l = some w) (V : Ctxt.Valuation Δ) :
    getLvl V l = some ⟨s, w.lookup V⟩ := by
  unfold varOfLvl? at h
  unfold getLvl
  split at h
  · rw [if_pos ‹_›]
    exact varOfDepth?_lookup Δ s _ w h V
  · cases h

variable [DialectSignature d] [DialectDenote d]

/-- The value of the node with operation `op` and argument levels `lv` in a valuation. -/
def evalKey {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (op : d.Op) (lv : List Nat) :
    Option (Σ t : d.Ty, ⟦t⟧) :=
  (gatherArgs V (DialectSignature.sig op) lv).map fun a =>
    ⟨DialectSignature.ret op, DialectDenote.denote op a⟩

theorem evalKey_extend_some {Γ : Ctxt d} {s : d.Ty}
    (V : Ctxt.Valuation Γ) (x : ⟦s⟧) {op : d.Op} {lv : List Nat}
    {p : Σ t : d.Ty, ⟦t⟧} (h : evalKey V op lv = some p) :
    evalKey (Γ := s :: Γ) (V.extend x) op lv = some p := by
  unfold evalKey at h ⊢
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [gatherArgs_extend_some V x _ _ a ha]
  rfl

theorem evalKey_expr {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t)
    (V : Ctxt.Valuation Γ) : evalKey V e.op (argLvls e.args) = some ⟨t, e.denote V⟩ := by
  rcases e with ⟨op, hop, args⟩
  cases hop
  unfold evalKey
  rw [gatherArgs_argLvls V args]
  rfl

end Levels

/-! ## 2. The node table and the definition table -/

/-- The node table: for each list of argument levels, the operations of the nodes with
    those arguments and the level of each node's result. -/
abbrev Tbl (d : Dialect.{0, 0}) : Type := Std.HashMap (List Nat) (List (d.Op × Nat))

/-- The definition table: for a result level, the operation and argument levels of one
    node defining it. -/
abbrev Defs (d : Dialect.{0, 0}) : Type := Std.HashMap Nat (d.Op × List Nat)

section Tables

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- A node table is sound for a valuation when every node it records evaluates, at that
    valuation, to the value at its result level. -/
def Sound {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (M : Tbl d) : Prop :=
  ∀ (lv : List Nat) (bucket : List (d.Op × Nat)), M[lv]? = some bucket →
    ∀ p ∈ bucket, ∃ x, evalKey V p.1 lv = some x ∧ getLvl V p.2 = some x

theorem sound_empty {Γ : Ctxt d} (V : Ctxt.Valuation Γ) : Sound V (∅ : Tbl d) := by
  intro lv bucket h
  simp at h

theorem sound_extend {Γ : Ctxt d} {s : d.Ty} {V : Ctxt.Valuation Γ}
    (x : ⟦s⟧) {M : Tbl d} (hM : Sound V M) : Sound (Γ := s :: Γ) (V.extend x) M := by
  intro lv bucket h p hp
  obtain ⟨y, h1, h2⟩ := hM lv bucket h p hp
  exact ⟨y, evalKey_extend_some V x h1, getLvl_extend_some V x h2⟩

/-- A definition table is sound for a valuation when every recorded node evaluates, at
    that valuation, to the value at its level. -/
def DSound {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (D : Defs d) : Prop :=
  ∀ (l : Nat) (p : d.Op × List Nat), D[l]? = some p →
    ∃ x, evalKey V p.1 p.2 = some x ∧ getLvl V l = some x

theorem dsound_empty {Γ : Ctxt d} (V : Ctxt.Valuation Γ) : DSound V (∅ : Defs d) := by
  intro l p h
  simp at h

theorem dsound_extend {Γ : Ctxt d} {s : d.Ty} {V : Ctxt.Valuation Γ}
    (x : ⟦s⟧) {D : Defs d} (hD : DSound V D) : DSound (Γ := s :: Γ) (V.extend x) D := by
  intro l p h
  obtain ⟨y, h1, h2⟩ := hD l p h
  exact ⟨y, evalKey_extend_some V x h1, getLvl_extend_some V x h2⟩

theorem dsound_insert {Γ : Ctxt d} {V : Ctxt.Valuation Γ} {D : Defs d}
    (hD : DSound V D) {op : d.Op} {lv : List Nat} {l : Nat}
    {x : Σ t : d.Ty, ⟦t⟧} (h1 : evalKey V op lv = some x) (h2 : getLvl V l = some x) :
    DSound V (D.insert l (op, lv)) := by
  intro l' p h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hk
    have hk' : l = l' := by simpa using hk
    subst hk'
    cases h
    exact ⟨x, h1, h2⟩
  · exact hD l' p h

variable [DecidableEq d.Op]

/-- The output variable of type `s` of a recorded node with operation `op` and argument
    levels `lv`, when `pure op` holds. -/
def findVar (pure : d.Op → Bool) (Δ : Ctxt d) (s : d.Ty) (M : Tbl d) (op : d.Op)
    (lv : List Nat) : Option (Ctxt.Var Δ s) :=
  if pure op then
    match M[lv]? with
    | some bucket =>
        match bucket.find? (fun p => p.1 == op) with
        | some p => varOfLvl? Δ s p.2
        | none => none
    | none => none
  else none

theorem findVar_sound {pure : d.Op → Bool} {Δ : Ctxt d} {s : d.Ty} {M : Tbl d}
    {op : d.Op} {lv : List Nat} {w : Ctxt.Var Δ s} {V : Ctxt.Valuation Δ} (hM : Sound V M)
    (h : findVar pure Δ s M op lv = some w) : evalKey V op lv = some ⟨s, w.lookup V⟩ := by
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

/-- The output variable of a recorded node equal to `e` denotes the value of `e`. -/
theorem findVar_expr {pure : d.Op → Bool} {Δ : Ctxt d} {s : d.Ty} {M : Tbl d}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) {e : Expr d Δ s}
    {w : Ctxt.Var Δ s} (h : findVar pure Δ s M e.op (argLvls e.args) = some w) :
    w.lookup V = e.denote V := by
  have h1 := findVar_sound hM h
  rw [evalKey_expr e V] at h1
  exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h1)).2).symm

/-- The table with the node (`op`, `lv`) of result level `n` entered, when `pure op`
    holds. -/
def insertT (pure : d.Op → Bool) (M : Tbl d) (op : d.Op) (lv : List Nat) (n : Nat) :
    Tbl d :=
  if pure op then M.insert lv ((op, n) :: M.getD lv []) else M

omit [DecidableEq d.Op] in
/-- Entering a node whose value is the value at level `l` keeps a node table sound. -/
theorem sound_insertAt {pure : d.Op → Bool} {Γ : Ctxt d} {V : Ctxt.Valuation Γ} {M : Tbl d}
    (hM : Sound V M) {op : d.Op} {lv : List Nat} {l : Nat}
    {x : Σ t : d.Ty, ⟦t⟧} (h1 : evalKey V op lv = some x) (h2 : getLvl V l = some x) :
    Sound V (insertT pure M op lv l) := by
  unfold insertT
  split
  · intro lv' bucket h p hp
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i hk
      have hk' : lv = lv' := by simpa using hk
      subst hk'
      cases h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨x, h1, h2⟩
      · rw [Std.HashMap.getD_eq_getD_getElem?] at hp'
        rcases hb : M[lv]? with _ | b
        · simp [hb] at hp'
        · rw [hb] at hp'
          exact hM _ b hb p hp'
    · exact hM lv' bucket h p hp
  · exact hM

omit [DecidableEq d.Op] in
theorem sound_insertT {pure : d.Op → Bool} {Δ : Ctxt d} {s : d.Ty} {V : Ctxt.Valuation Δ}
    {M : Tbl d} (hM : Sound V M) (e : Expr d Δ s) :
    Sound (Γ := s :: Δ) (V.extend (e.denote V))
      (insertT pure M e.op (argLvls e.args) Δ.length) :=
  sound_insertAt (sound_extend _ hM) (evalKey_extend_some V _ (evalKey_expr e V))
    (getLvl_extend_top V _)

end Tables

/-! ## 3. Global value numbering -/

section GVN

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

/-- Global value numbering under the renaming `ρ` and the node table `M`: a binding of an
    operation satisfying `pure` whose renamed key is recorded is dropped and its variable
    mapped to the recorded node; every other binding is renamed by `ρ`, kept and
    recorded. -/
def gvnGo (pure : d.Op → Bool) : {Γ Δ : Ctxt d} → {t : d.Ty} → Ctxt.Hom Γ Δ → Tbl d →
    Com d Γ t → Com d Δ t
  | _, _, _, ρ, _, .ret v => .ret (ρ v)
  | _, Δ, _, ρ, M, .var (t := s) e body =>
      match findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with
      | some w => gvnGo pure (consHom w ρ) M body
      | none =>
          .var (e.rename ρ)
            (gvnGo pure ρ.lift
              (insertT pure M (e.rename ρ).op (argLvls (e.rename ρ).args) Δ.length) body)

/-- **Denotation of the traversal.** Under a table sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem gvnGo_denote (pure : d.Op → Bool) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (M : Tbl d) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    Sound V M → (gvnGo pure ρ M c).denote V = c.denote (V.comap ρ)
  | _, _, _, ρ, _, .ret v, V, _ => (Ctxt.Valuation.lookup_comap ρ V v).symm
  | _, Δ, _, ρ, M, .var (t := s) e body, V, hM => by
      simp only [gvnGo]
      rcases hc : findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [Com.denote]
        rw [gvnGo_denote pure ρ.lift _ body _ (sound_insertT hM (e.rename ρ)),
          Expr.denote_rename ρ e V, Ctxt.Valuation.extend_comap_lift]
      · simp only [Com.denote]
        rw [gvnGo_denote pure (consHom w ρ) M body V hM, comap_consHom, findVar_expr hM hc,
          Expr.denote_rename ρ e V]

/-- **Global value numbering**: the traversal from the identity renaming and the empty
    table. -/
def gvnCom (pure : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Com d Γ t :=
  gvnGo pure (Ctxt.Hom.id Γ) ∅ c

/-- **Denotation of the pass.** `gvnCom pure c` denotes the same function as `c`. -/
theorem gvnCom_denote (pure : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    (gvnCom pure c).denote = c.denote :=
  funext fun V => by
    rw [gvnCom, gvnGo_denote pure _ _ c V (sound_empty V), Ctxt.Valuation.comap_id]

end GVN

/-! ## 4. Cost -/

section Cost

variable {d : Dialect.{0, 0}} [DialectSignature d]

/-- The cost of a `Com` under a cost of operations: the sum of the costs of the
    operations of its bindings. -/
def comCostOf (cost : d.Op → Nat) : {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var e body => cost e.op + comCostOf cost body

variable [TyDenote d.Ty] [DecidableEq d.Ty] [DialectDenote d] [DecidableEq d.Op]

omit [TyDenote d.Ty] [DialectDenote d] in
theorem gvnGo_cost_le (cost : d.Op → Nat) (pure : d.Op → Bool) :
    ∀ {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ) (M : Tbl d) (c : Com d Γ t),
      comCostOf cost (gvnGo pure ρ M c) ≤ comCostOf cost c
  | _, _, _, ρ, _, .ret v => Nat.le_refl _
  | _, Δ, _, ρ, M, .var (t := s) e body => by
      simp only [gvnGo]
      rcases findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [comCostOf]
        have := gvnGo_cost_le cost pure ρ.lift
          (insertT pure M (e.rename ρ).op (argLvls (e.rename ρ).args) Δ.length) body
        exact Nat.add_le_add_left this _
      · simp only [comCostOf]
        exact Nat.le_trans (gvnGo_cost_le cost pure (consHom w ρ) M body)
          (Nat.le_add_left _ _)

end Cost

/-! ## 5. Alternatives, rules and rule sets -/

/-- An alternative form of a value of type `s` over the context `Δ`: an existing
    variable, one binding, or two bindings. -/
inductive Alt {d : Dialect.{0, 0}} [DialectSignature d] (Δ : Ctxt d) (s : d.Ty) :
    Type where
  | var (v : Ctxt.Var Δ s)
  | one (e : Expr d Δ s)
  | two {s1 : d.Ty} (e1 : Expr d Δ s1) (e2 : Expr d (s1 :: Δ) s)

namespace Alt

variable {d : Dialect.{0, 0}} [DialectSignature d] {Δ : Ctxt d} {s : d.Ty}

/-- The value of an alternative. -/
def denote [TyDenote d.Ty] [DialectDenote d] : Alt Δ s → Ctxt.Valuation Δ → ⟦s⟧
  | .var v, V => v.lookup V
  | .one e, V => e.denote V
  | .two e1 e2, V => e2.denote (V.extend (e1.denote V))

/-- The cost of the bindings an alternative emits, under a cost of operations. -/
def cost (c : d.Op → Nat) : Alt Δ s → Nat
  | .var _ => 0
  | .one e => c e.op
  | .two e1 e2 => c e1.op + c e2.op

/-- The extraction weight of an alternative, under a weight of operations. -/
def key (k : d.Op → Nat) : Alt Δ s → Nat
  | .var _ => 0
  | .one e => k e.op
  | .two e1 e2 => k e1.op + k e2.op

end Alt

/-- A rule: for an expression and a definition table, a list of alternatives, each of which
    denotes the expression under every definition table sound for the valuation. -/
structure Rule (d : Dialect.{0, 0}) [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
    [DialectDenote d] where
  /-- The alternatives the rule produces for an expression. -/
  apply : Defs d → {Δ : Ctxt d} → {s : d.Ty} → Expr d Δ s → List (Alt Δ s)
  /-- Soundness of the rule against the denotation of the dialect. -/
  sound : ∀ (D : Defs d) {Δ : Ctxt d} (V : Ctxt.Valuation Δ), DSound V D →
    ∀ {s : d.Ty} (e : Expr d Δ s), ∀ a ∈ apply D e, a.denote V = e.denote V

/-- A rule set over a dialect: the rules, the cost of an operation, the extraction weight
    of an operation, and the operations the node table may merge. -/
structure RuleSet (d : Dialect.{0, 0}) [TyDenote d.Ty] [DecidableEq d.Ty]
    [DialectSignature d] [DialectDenote d] where
  /-- The rules, each with its soundness. -/
  rules : List (Rule d)
  /-- The cost of an operation; extraction never increases it. -/
  cost : d.Op → Nat
  /-- The extraction weight of an operation; extraction minimises it. -/
  key : d.Op → Nat
  /-- The operations whose bindings the node table may merge. -/
  pure : d.Op → Bool

namespace RuleSet

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d]

/-- The alternatives all rules of a rule set produce for an expression. -/
def alts (R : RuleSet d) (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    List (Alt Δ s) :=
  R.rules.flatMap fun r => r.apply D e

/-- **Soundness of a rule set.** Under a definition table sound for `V`, every alternative
    of the rule set denotes the expression. -/
theorem alts_sound (R : RuleSet d) {D : Defs d} {Δ : Ctxt d} {V : Ctxt.Valuation Δ}
    (hD : DSound V D) {s : d.Ty} (e : Expr d Δ s) :
    ∀ a ∈ R.alts D e, a.denote V = e.denote V := by
  intro a ha
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp ha
  exact r.sound D V hD e a hr

end RuleSet

/-! ## 6. Hash-consing and extraction -/

section Aegraph

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op]

/-- One binding, replaced by the variable of a recorded node equal to it. -/
def reduceOne (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    Alt Δ s :=
  match findVar pure Δ s M e.op (argLvls e.args) with
  | some w => .var w
  | none => .one e

/-- An alternative with each binding replaced by the variable of a recorded node equal
    to it. -/
def reduceAlt (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty} :
    Alt Δ s → Alt Δ s
  | .var v => .var v
  | .one e => reduceOne pure M e
  | .two (s1 := s1) e1 e2 =>
      match findVar pure Δ s1 M e1.op (argLvls e1.args) with
      | some w1 => reduceOne pure M (e2.rename (consHom w1 (Ctxt.Hom.id Δ)))
      | none => .two e1 e2

theorem reduceOne_denote {pure : d.Op → Bool} {M : Tbl d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) (e : Expr d Δ s) :
    (reduceOne pure M e).denote V = e.denote V := by
  unfold reduceOne
  split
  · rename_i w hw
    exact findVar_expr hM hw
  · rfl

theorem reduceAlt_denote {pure : d.Op → Bool} {M : Tbl d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hM : Sound V M) (a : Alt Δ s) :
    (reduceAlt pure M a).denote V = a.denote V := by
  cases a with
  | var v => rfl
  | one e => exact reduceOne_denote hM e
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · rename_i w1 hw1
        rw [reduceOne_denote hM, Expr.denote_rename, comap_consHom, Ctxt.Valuation.comap_id,
          findVar_expr hM hw1]
        rfl
      · rfl

/-- The alternative of least key among `best` and the members of the list whose cost is
    at most `bound`; on equal keys the earlier one. -/
def pick (R : RuleSet d) {Δ : Ctxt d} {s : d.Ty} (bound : Nat) :
    Alt Δ s → List (Alt Δ s) → Alt Δ s
  | best, [] => best
  | best, a :: as =>
      pick R bound (if a.cost R.cost ≤ bound ∧ a.key R.key < best.key R.key then a else best)
        as

omit [DecidableEq d.Op] in
/-- A property of `best` and of every member of cost at most `bound` holds of the picked
    alternative. -/
theorem pick_prop (R : RuleSet d) {Δ : Ctxt d} {s : d.Ty} (bound : Nat)
    (P : Alt Δ s → Prop) : ∀ (best : Alt Δ s) (as : List (Alt Δ s)), P best →
      (∀ a ∈ as, a.cost R.cost ≤ bound → P a) → P (pick R bound best as)
  | _, [], hb, _ => hb
  | best, a :: as, hb, has => by
      simp only [pick]
      refine pick_prop R bound P _ as ?_ (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))
      split
      · rename_i h
        exact has a List.mem_cons_self h.1
      · exact hb

/-- The e-class of `e`: the rule alternatives, each hash-consed through the node table. -/
def classAlts (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) : List (Alt Δ s) :=
  (R.alts S.2 e).map (reduceAlt R.pure S.1)

/-- The forms of the union node of `e`: `e` itself, hash-consed, and its e-class. -/
def unionAlts (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) : List (Alt Δ s) :=
  reduceOne R.pure S.1 e :: classAlts R S e

/-- **Extraction**: the alternative of least key among `e` and its e-class, over the
    alternatives whose cost is at most the cost of `e`. -/
def choose (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) : Alt Δ s :=
  pick R (R.cost e.op) (reduceOne R.pure S.1 e) (classAlts R S e)

/-- A state of the pass is sound for a valuation when both tables are. -/
def StSound {Γ : Ctxt d} (V : Ctxt.Valuation Γ) (S : Tbl d × Defs d) : Prop :=
  Sound V S.1 ∧ DSound V S.2

omit [DecidableEq d.Op] in
theorem stSound_empty {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    StSound V ((∅, ∅) : Tbl d × Defs d) :=
  ⟨sound_empty V, dsound_empty V⟩

theorem unionAlts_denote (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s) :
    ∀ a ∈ unionAlts R S e, a.denote V = e.denote V := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact reduceOne_denote hS.1 e
  · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    rw [reduceAlt_denote hS.1]
    exact R.alts_sound hS.2 e a' ha'

/-- **Denotation of extraction.** Any alternative extraction chooses from the e-class of
    `e` denotes the value of `e`. -/
theorem extract_denote (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s) :
    (choose R S e).denote V = e.denote V :=
  pick_prop R _ (fun a => a.denote V = e.denote V) _ _
    (unionAlts_denote R hS e _ List.mem_cons_self)
    (fun a ha _ => unionAlts_denote R hS e a (List.mem_cons_of_mem _ ha))

/-- **Cost of extraction.** The extracted alternative costs at most the expression. -/
theorem choose_cost_le (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) : (choose R S e).cost R.cost ≤ R.cost e.op := by
  refine pick_prop R _ (fun a => a.cost R.cost ≤ R.cost e.op) _ _ ?_ (fun _ _ h => h)
  unfold reduceOne
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-! ## 7. State updates -/

/-- The node table with the key of every one-binding form of a union node entered at the
    level `l` of its value. -/
def insUnion (pure : d.Op → Bool) (M : Tbl d) (l : Nat) {Δ : Ctxt d} {s : d.Ty} :
    List (Alt Δ s) → Tbl d
  | [] => M
  | .one e :: U => insUnion pure (insertT pure M e.op (argLvls e.args) l) l U
  | _ :: U => insUnion pure M l U

omit [DecidableEq d.Op] in
theorem sound_insUnion {pure : d.Op → Bool} {Δ' : Ctxt d} {V' : Ctxt.Valuation Δ'}
    {l : Nat} {p : Σ t : d.Ty, ⟦t⟧} {Δ : Ctxt d} {s : d.Ty}
    (hl : getLvl V' l = some p) :
    ∀ (U : List (Alt Δ s)) (M : Tbl d), Sound V' M →
      (∀ e, Alt.one e ∈ U → evalKey V' e.op (argLvls e.args) = some p) →
      Sound V' (insUnion pure M l U)
  | [], _, hM, _ => hM
  | .one e :: U, _, hM, h =>
      sound_insUnion hl U _ (sound_insertAt hM (h e List.mem_cons_self) hl)
        (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | .var _ :: U, M, hM, h =>
      sound_insUnion hl U M hM (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
  | .two _ _ :: U, M, hM, h =>
      sound_insUnion hl U M hM (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- The state after a binding `e` whose extracted form is the existing variable `w`. -/
def stVar (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) (w : Ctxt.Var Δ s) : Tbl d × Defs d :=
  (insUnion R.pure S.1 (varLvl w) (unionAlts R S e), S.2)

/-- The state after a binding `e` whose extracted form is the binding `e2`, bound at
    level `n`. -/
def stOne (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty}
    (e e2 : Expr d Δ s) (n : Nat) : Tbl d × Defs d :=
  (insUnion R.pure (insertT R.pure S.1 e2.op (argLvls e2.args) n) n (unionAlts R S e),
    S.2.insert n (e2.op, argLvls e2.args))

/-- The state after a binding `e` whose extracted form is the bindings `e1` at level `n`
    and `e2` at level `n + 1`. -/
def stTwo (R : RuleSet d) (S : Tbl d × Defs d) {Δ : Ctxt d} {s s1 : d.Ty}
    (e : Expr d Δ s) (e1 : Expr d Δ s1) (e2 : Expr d (s1 :: Δ) s) (n : Nat) :
    Tbl d × Defs d :=
  (insUnion R.pure
      (insertT R.pure (insertT R.pure S.1 e1.op (argLvls e1.args) n) e2.op (argLvls e2.args)
        (n + 1))
      (n + 1) (unionAlts R S e),
    (S.2.insert n (e1.op, argLvls e1.args)).insert (n + 1) (e2.op, argLvls e2.args))

theorem union_keys (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s) :
    ∀ e3, Alt.one e3 ∈ unionAlts R S e → evalKey V e3.op (argLvls e3.args) =
      some ⟨s, e.denote V⟩ := by
  intro e3 h3
  rw [evalKey_expr e3 V]
  have := unionAlts_denote R hS e _ h3
  simp only [Alt.denote] at this
  rw [this]

theorem stVar_sound (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s)
    {w : Ctxt.Var Δ s} (hc : choose R S e = .var w) :
    StSound V (stVar R S e w) ∧ w.lookup V = e.denote V := by
  have hw : w.lookup V = e.denote V := by
    have := extract_denote R hS e
    rw [hc] at this
    exact this
  refine ⟨⟨?_, hS.2⟩, hw⟩
  refine sound_insUnion (getLvl_var w V) _ _ hS.1 ?_
  intro e3 h3
  rw [union_keys R hS e e3 h3, hw]

theorem stOne_sound (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s)
    {e2 : Expr d Δ s} (hc : choose R S e = .one e2) :
    StSound (Γ := s :: Δ) (V.extend (e2.denote V)) (stOne R S e e2 Δ.length) ∧
      e2.denote V = e.denote V := by
  have hw : e2.denote V = e.denote V := by
    have := extract_denote R hS e
    rw [hc] at this
    exact this
  have hk := evalKey_extend_some V (e2.denote V) (evalKey_expr e2 V)
  have hl := getLvl_extend_top V (e2.denote V)
  refine ⟨⟨?_, dsound_insert (dsound_extend _ hS.2) hk hl⟩, hw⟩
  refine sound_insUnion hl _ _ (sound_insertAt (sound_extend _ hS.1) hk hl) ?_
  intro e3 h3
  rw [hw]
  exact evalKey_extend_some V _ (union_keys R hS e e3 h3)

theorem stTwo_sound (R : RuleSet d) {S : Tbl d × Defs d} {Δ : Ctxt d} {s s1 : d.Ty}
    {V : Ctxt.Valuation Δ} (hS : StSound V S) (e : Expr d Δ s)
    {e1 : Expr d Δ s1} {e2 : Expr d (s1 :: Δ) s}
    (hc : choose R S e = .two e1 e2) :
    StSound (Γ := s :: s1 :: Δ)
        ((V.extend (e1.denote V)).extend (e2.denote (V.extend (e1.denote V))))
        (stTwo R S e e1 e2 Δ.length) ∧
      e2.denote (V.extend (e1.denote V)) = e.denote V := by
  have hw : e2.denote (V.extend (e1.denote V)) = e.denote V := by
    have := extract_denote R hS e
    rw [hc] at this
    exact this
  set V1 := V.extend (e1.denote V) with hV1
  set x := e2.denote V1 with hx
  have hk1 := evalKey_extend_some V1 x (evalKey_extend_some V (e1.denote V) (evalKey_expr e1 V))
  have hl1 := getLvl_extend_some V1 x (getLvl_extend_top V (e1.denote V))
  have hk2 := evalKey_extend_some V1 x (evalKey_expr e2 V1)
  have hl2 : getLvl (Γ := s :: s1 :: Δ) (V1.extend x) (Δ.length + 1) = some ⟨s, x⟩ :=
    getLvl_extend_top V1 x
  refine ⟨⟨?_, ?_⟩, hw⟩
  · refine sound_insUnion hl2 _ _ (sound_insertAt (sound_insertAt
      (sound_extend _ (sound_extend _ hS.1)) hk1 hl1) hk2 hl2) ?_
    intro e3 h3
    rw [hw]
    exact evalKey_extend_some V1 _ (evalKey_extend_some V _ (union_keys R hS e e3 h3))
  · exact dsound_insert (dsound_insert (dsound_extend _ (dsound_extend _ hS.2)) hk1 hl1) hk2 hl2

/-! ## 8. The pass -/

/-- The aegraph traversal at the rule set `R` under the renaming `ρ` and the state `S`:
    each binding is renamed, its e-class formed and hash-consed, and the extracted
    alternative emitted. -/
def agGo (R : RuleSet d) : {Γ Δ : Ctxt d} → {t : d.Ty} → Ctxt.Hom Γ Δ → Tbl d × Defs d →
    Com d Γ t → Com d Δ t
  | _, _, _, ρ, _, .ret v => .ret (ρ v)
  | _, Δ, _, ρ, S, .var e body =>
      match choose R S (e.rename ρ) with
      | .var w => agGo R (consHom w ρ) (stVar R S (e.rename ρ) w) body
      | .one e2 => .var e2 (agGo R ρ.lift (stOne R S (e.rename ρ) e2 Δ.length) body)
      | .two e1 e2 =>
          .var e1 (.var e2
            (agGo R (consHom .here (wk2 ρ)) (stTwo R S (e.rename ρ) e1 e2 Δ.length) body))

/-- **Denotation of the traversal.** Under a state sound for `V`, the output denotes the
    input at the valuation pulled back along `ρ`. -/
theorem agGo_denote (R : RuleSet d) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (c : Com d Γ t) (V : Ctxt.Valuation Δ),
    StSound V S → (agGo R ρ S c).denote V = c.denote (V.comap ρ)
  | _, _, _, ρ, _, .ret v, V, _ => (Ctxt.Valuation.lookup_comap ρ V v).symm
  | _, Δ, _, ρ, S, .var (t := s) e body, V, hS => by
      simp only [agGo]
      split
      · rename_i w hc
        obtain ⟨hS', hw⟩ := stVar_sound R hS _ hc
        rw [agGo_denote R _ _ body V hS', comap_consHom, hw, Expr.denote_rename]
        rfl
      · rename_i e2 hc
        obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
        simp only [Com.denote]
        rw [agGo_denote R _ _ body _ hS', Ctxt.Valuation.extend_comap_lift, hw,
          Expr.denote_rename]
      · rename_i s1 e1 e2 hc
        obtain ⟨hS', hw⟩ := stTwo_sound R hS _ hc
        simp only [Com.denote]
        rw [agGo_denote R _ _ body _ hS', comap_consHom, comap_wk2, Expr.denote_rename] at *
        show body.denote ((V.comap ρ).extend (e2.denote _)) = _
        rw [hw]

/-- **The aegraph pass at a rule set**: the traversal from the identity renaming and the
    empty state. -/
def aegraphOptOf (R : RuleSet d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) : Com d Γ t :=
  agGo R (Ctxt.Hom.id Γ) (∅, ∅) c

/-- **Denotation of the pass.** `aegraphOptOf R c` denotes the same function as `c`, for
    every rule set `R`. -/
theorem aegraphOptOf_denote (R : RuleSet d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    (aegraphOptOf R c).denote = c.denote :=
  funext fun V => by
    rw [aegraphOptOf, agGo_denote R _ _ c V (stSound_empty V), Ctxt.Valuation.comap_id]

/-! ## 9. Cost -/

theorem agGo_cost_le (R : RuleSet d) : ∀ {Γ Δ : Ctxt d} {t : d.Ty}
    (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d) (c : Com d Γ t),
    comCostOf R.cost (agGo R ρ S c) ≤ comCostOf R.cost c
  | _, _, _, ρ, _, .ret v => Nat.le_refl _
  | _, Δ, _, ρ, S, .var (t := s) e body => by
      have hch := choose_cost_le R S (e.rename ρ)
      simp only [agGo]
      split
      · rename_i w hc
        simp only [comCostOf]
        exact Nat.le_trans (agGo_cost_le R _ _ body) (Nat.le_add_left _ _)
      · rename_i e2 hc
        rw [hc] at hch
        simp only [comCostOf]
        exact Nat.add_le_add hch (agGo_cost_le R _ _ body)
      · rename_i s1 e1 e2 hc
        rw [hc] at hch
        simp only [comCostOf, Alt.cost] at hch ⊢
        have := agGo_cost_le R (consHom .here (wk2 (s1 := s1) ρ))
          (stTwo R S (e.rename ρ) e1 e2 Δ.length) body
        rw [← Nat.add_assoc]
        exact Nat.add_le_add hch this

/-- The pass does not increase the cost of the rule set. -/
theorem aegraphOptOf_cost_le (R : RuleSet d) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) :
    comCostOf R.cost (aegraphOptOf R c) ≤ comCostOf R.cost c :=
  agGo_cost_le R _ _ c

end Aegraph

/-! ## 10. Constant time under a leakage model

The leakage of a `Com` (`ComLevelCheck.Com.ctLeak`) is the concatenation of the events of
its bindings, and the number of events of one binding depends on its operation alone.
Value numbering keeps a subsequence of the bindings of its input, chosen without
reference to the valuation. The aegraph emits, for each binding, the binding itself
hash-consed, or a rule alternative; when the events of every rule alternative do not
depend on the valuation (`RulesIndep`), equal input leakage gives equal output leakage. -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DialectSignature d]

/-- The number of events of an operation does not depend on its argument values. -/
theorem opLeak_length (L : LeakModel d) (op : d.Op)
    (a b : HVector (fun t => ⟦t⟧) (DialectSignature.sig op)) :
    (opLeak L op a).length = (opLeak L op b).length := by
  unfold opLeak
  rcases L.kind op <;> rfl

/-- The events of a renamed expression are those of the expression at the pulled-back
    valuation. -/
theorem Expr.ctLeak_rename (L : LeakModel d) {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ)
    (e : Expr d Γ t) (V : Ctxt.Valuation Δ) :
    Expr.ctLeak L (e.rename ρ) V = Expr.ctLeak L e (V.comap ρ) := by
  simp only [Expr.ctLeak, Expr.rename]
  rw [Expr.lookupArgs_renameVars]

/-- The events of every binding an alternative emits are the same at every valuation. -/
def Alt.Indep (L : LeakModel d) {Δ : Ctxt d} {s : d.Ty} : Alt Δ s → Prop
  | .var _ => True
  | .one e => ∀ V₁ V₂, Expr.ctLeak L e V₁ = Expr.ctLeak L e V₂
  | .two e1 e2 => (∀ V₁ V₂, Expr.ctLeak L e1 V₁ = Expr.ctLeak L e1 V₂) ∧
      (∀ V₁ V₂, Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂)

variable [DecidableEq d.Ty] [DialectDenote d]

/-- The events of every alternative of every rule of `R` are the same at every
    valuation. -/
def RulesIndep (L : LeakModel d) (R : RuleSet d) : Prop :=
  ∀ (D : Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s), ∀ alt ∈ R.alts D e, alt.Indep L

variable [DecidableEq d.Op]

/-- **Leakage of value numbering.** Under tables sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem gvnGo_ctLeak (L : LeakModel d) (pure : d.Op → Bool) : ∀ {Γ Δ : Ctxt d}
    {t : d.Ty} (ρ : Ctxt.Hom Γ Δ) (M : Tbl d) (c : Com d Γ t)
    (V₁ V₂ : Ctxt.Valuation Δ), Sound V₁ M → Sound V₂ M →
    Com.ctLeak L c (V₁.comap ρ) = Com.ctLeak L c (V₂.comap ρ) →
    Com.ctLeak L (gvnGo pure ρ M c) V₁ = Com.ctLeak L (gvnGo pure ρ M c) V₂
  | _, _, _, ρ, _, .ret v, _, _, _, _, _ => rfl
  | _, Δ, _, ρ, M, .var (t := s) e body, V₁, V₂, h₁, h₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
      simp only [gvnGo]
      rcases hc : findVar pure Δ s M (e.rename ρ).op (argLvls (e.rename ρ).args) with _ | w
      · simp only [Com.ctLeak]
        rw [Expr.ctLeak_rename, Expr.ctLeak_rename, hE]
        congr 1
        refine gvnGo_ctLeak L pure ρ.lift _ body _ _ (sound_insertT h₁ (e.rename ρ))
          (sound_insertT h₂ (e.rename ρ)) ?_
        rw [Ctxt.Valuation.extend_comap_lift, Ctxt.Valuation.extend_comap_lift,
          Expr.denote_rename, Expr.denote_rename]
        exact hB
      · have hw : ∀ V : Ctxt.Valuation Δ, Sound V M → w.lookup V = e.denote (V.comap ρ) := by
          intro V hV
          rw [← Expr.denote_rename ρ e V]
          exact findVar_expr hV hc
        refine gvnGo_ctLeak L pure (consHom w ρ) M body V₁ V₂ h₁ h₂ ?_
        rw [comap_consHom, comap_consHom, hw V₁ h₁, hw V₂ h₂]
        exact hB

/-- **Leakage of value numbering.** Equal leakage of `c` at two valuations gives equal
    leakage of `gvnCom pure c` there. -/
theorem gvnCom_ctLeak_eq (L : LeakModel d) (pure : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Γ) (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (gvnCom pure c) V₁ = Com.ctLeak L (gvnCom pure c) V₂ :=
  gvnGo_ctLeak L pure _ _ c V₁ V₂ (sound_empty V₁) (sound_empty V₂)
    (by rw [Ctxt.Valuation.comap_id, Ctxt.Valuation.comap_id]; exact h)

/-- **Constant time of value numbering.** If `c` is constant time for the relation `R`, so
    is `gvnCom pure c`. -/
theorem gvnCom_constantTime (L : LeakModel d) (pure : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (R : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime R (Com.ctLeak L c)) : ConstantTime R (Com.ctLeak L (gvnCom pure c)) :=
  fun V₁ V₂ hR => gvnCom_ctLeak_eq L pure c V₁ V₂ (h V₁ V₂ hR)

variable {L : LeakModel d}

omit [DialectDenote d] in
theorem reduceOne_cases (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (e : Expr d Δ s) : reduceOne pure M e = .one e ∨ (reduceOne pure M e).Indep L := by
  unfold reduceOne
  split
  · exact Or.inr trivial
  · exact Or.inl rfl

omit [DialectDenote d] in
theorem reduceAlt_indep (pure : d.Op → Bool) (M : Tbl d) {Δ : Ctxt d} {s : d.Ty}
    (a : Alt Δ s) (ha : a.Indep L) : (reduceAlt pure M a).Indep L := by
  cases a with
  | var v => trivial
  | one e =>
      rcases reduceOne_cases (L := L) pure M e with h | h
      · show (reduceOne pure M e).Indep L
        rw [h]
        exact ha
      · exact h
  | two e1 e2 =>
      simp only [reduceAlt]
      split
      · rename_i w1 _
        rcases reduceOne_cases (L := L) pure M
            (e2.rename (consHom w1 (Ctxt.Hom.id Δ))) with h | h
        · rw [h]
          intro V₁ V₂
          rw [Expr.ctLeak_rename, Expr.ctLeak_rename]
          exact ha.2 _ _
        · exact h
      · exact ha

/-- The extracted alternative of `e` is `e` itself or has events independent of the
    valuation. -/
theorem choose_leak (R : RuleSet d) (hI : RulesIndep L R) (S : Tbl d × Defs d)
    {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) :
    choose R S e = .one e ∨ (choose R S e).Indep L :=
  pick_prop R _ (fun a => a = .one e ∨ a.Indep L) _ _ (reduceOne_cases R.pure S.1 e)
    (fun a ha _ => by
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      exact Or.inr (reduceAlt_indep R.pure S.1 a' (hI S.2 e a' ha')))

/-- **Leakage of the traversal.** Under states sound for `V₁` and `V₂`, equal leakage of
    the input at the pulled-back valuations gives equal leakage of the output. -/
theorem agGo_ctLeak (R : RuleSet d) (hI : RulesIndep L R) :
    ∀ {Γ Δ : Ctxt d} {t : d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Δ), StSound V₁ S → StSound V₂ S →
      Com.ctLeak L c (V₁.comap ρ) = Com.ctLeak L c (V₂.comap ρ) →
      Com.ctLeak L (agGo R ρ S c) V₁ = Com.ctLeak L (agGo R ρ S c) V₂
  | _, _, _, ρ, _, .ret v, _, _, _, _, _ => rfl
  | _, Δ, _, ρ, S, .var e body, V₁, V₂, h₁, h₂, h => by
      simp only [Com.ctLeak] at h
      obtain ⟨hE, hB⟩ := List.append_inj h (opLeak_length L e.op _ _)
      rw [← Expr.ctLeak_rename, ← Expr.ctLeak_rename] at hE
      have hP := choose_leak R hI S (e.rename ρ)
      simp only [agGo]
      split
      · rename_i w hc
        obtain ⟨hS₁, hw₁⟩ := stVar_sound R h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stVar_sound R h₂ _ hc
        refine agGo_ctLeak R hI _ _ body V₁ V₂ hS₁ hS₂ ?_
        rw [comap_consHom, comap_consHom, hw₁, hw₂, Expr.denote_rename, Expr.denote_rename]
        exact hB
      · rename_i e2 hc
        obtain ⟨hS₁, hw₁⟩ := stOne_sound R h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stOne_sound R h₂ _ hc
        have hE2 : Expr.ctLeak L e2 V₁ = Expr.ctLeak L e2 V₂ := by
          rw [hc] at hP
          rcases hP with h' | h'
          · injection h' with h''
            subst h''
            exact hE
          · exact h' V₁ V₂
        simp only [Com.ctLeak]
        rw [hE2]
        congr 1
        refine agGo_ctLeak R hI _ _ body _ _ hS₁ hS₂ ?_
        rw [Ctxt.Valuation.extend_comap_lift, Ctxt.Valuation.extend_comap_lift, hw₁, hw₂,
          Expr.denote_rename, Expr.denote_rename]
        exact hB
      · rename_i s1 e1 e2 hc
        obtain ⟨hS₁, hw₁⟩ := stTwo_sound R h₁ _ hc
        obtain ⟨hS₂, hw₂⟩ := stTwo_sound R h₂ _ hc
        have hI2 : (Alt.two e1 e2).Indep L := by
          rw [hc] at hP
          rcases hP with h' | h'
          · cases h'
          · exact h'
        simp only [Com.ctLeak]
        rw [hI2.1 V₁ V₂, hI2.2 _ (V₂.extend (e1.denote V₂))]
        congr 2
        refine agGo_ctLeak R hI _ _ body _ _ hS₁ hS₂ ?_
        rw [comap_consHom, comap_consHom, comap_wk2, comap_wk2]
        show Com.ctLeak L body ((V₁.comap ρ).extend (e2.denote _)) =
          Com.ctLeak L body ((V₂.comap ρ).extend (e2.denote _))
        rw [hw₁, hw₂, Expr.denote_rename, Expr.denote_rename]
        exact hB

/-- **Leakage of the pass.** For a rule set whose alternatives have events independent of
    the valuation, equal leakage of `c` at two valuations gives equal leakage of
    `aegraphOptOf R c` there. -/
theorem aegraphOptOf_ctLeak_eq (R : RuleSet d) (hI : RulesIndep L R) {Γ : Ctxt d}
    {t : d.Ty} (c : Com d Γ t) (V₁ V₂ : Ctxt.Valuation Γ)
    (h : Com.ctLeak L c V₁ = Com.ctLeak L c V₂) :
    Com.ctLeak L (aegraphOptOf R c) V₁ = Com.ctLeak L (aegraphOptOf R c) V₂ :=
  agGo_ctLeak R hI _ _ c V₁ V₂ (stSound_empty V₁) (stSound_empty V₂)
    (by rw [Ctxt.Valuation.comap_id, Ctxt.Valuation.comap_id]; exact h)

/-- **Constant time of the pass.** For a rule set whose alternatives have events
    independent of the valuation, if `c` is constant time for the relation `P`, so is
    `aegraphOptOf R c`. -/
theorem aegraphOptOf_constantTime (R : RuleSet d) (hI : RulesIndep L R) {Γ : Ctxt d}
    {t : d.Ty} (c : Com d Γ t) (P : Ctxt.Valuation Γ → Ctxt.Valuation Γ → Prop)
    (h : ConstantTime P (Com.ctLeak L c)) :
    ConstantTime P (Com.ctLeak L (aegraphOptOf R c)) :=
  fun V₁ V₂ hR => aegraphOptOf_ctLeak_eq R hI c V₁ V₂ (h V₁ V₂ hR)

end Leak

end CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
