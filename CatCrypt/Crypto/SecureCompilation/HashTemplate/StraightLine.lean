/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate

/-!
# A compiler of straight-line word programs to `jasminDialect`

A hash compression function over machine words (SHA-2, BLAKE2) is a straight-line program:
constant-index loads of the input words from stack arrays, let-bound word expressions, and
constant-index stores of the output words. This module is the part of such a template that
is independent of the hash function.

A word expression `WExp w` is built from numbered words, constants, binary register
operations, and rotations and right shifts by an immediate. A list of let-bound word
expressions is compiled by `genLets` to a straight-line `Com jasminDialect` in
continuation-passing style over the context extensions: each compilation step passes to its
continuation a renaming `Ren Γ Δ` into the extended context and the variables of the
numbered words. The value lemmas state that the compiled program has the value `R` when every
continuation has it at variables holding the values `evalLets`; the event lemmas state that
the compiled program has fixed events at leakage parameters with no variable-time operation.

## Main definitions

* `WExp`, `WExp.eval`, `evalLets`: word expressions and the value of a list of let-bound
  word expressions.
* `WExp.gen`, `genLetsR`, `genLets`, `genLoad`, `genLoads`, `genStores`, `genStoresIdx`:
  compilation to `jasminDialect`.
* `LetSt`: a list of let-bound word expressions under construction.
* `RenResp`, `loadVals`: renamings that keep values, and the values after loads.

## Main results

* `WExp.gen_denote`, `genLetsR_denote`, `genLets_denote`, `genLoad_denote`,
  `genLoads_denote`, `genStores_denote`, `genStoresIdx_denote`: the values of the compiled
  programs.
* `WExp.gen_fixed`, `genLetsR_fixed`, `genLets_fixed`, `genLoad_fixed`, `genLoads_fixed`,
  `genStores_fixed`, `genStoresIdx_fixed`: the compiled programs have fixed events.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

/-! ## 1. Word expressions and their compilation -/

/-- A word expression of width `w` over numbered words: a word, a constant, a binary
    register operation, and a rotation or a right shift by an immediate. -/
inductive WExp (w : Nat) where
  /-- The word numbered `i`. -/
  | var (i : Nat)
  /-- A constant. -/
  | const (x : BitVec w)
  /-- A binary register operation. -/
  | bin (op : JasminBinOp) (a b : WExp w)
  /-- A rotation to the right by `k`. -/
  | rotr (k : Nat) (a : WExp w)
  /-- A logical shift to the right by `k`. -/
  | shr (k : Nat) (a : WExp w)

/-- The value of a word expression at the values `ρ` of the numbered words, as
    `jasminDialect` denotes the operations. -/
def WExp.eval {w : Nat} (ρ : Nat → BitVec w) : WExp w → BitVec w
  | .var i => ρ i
  | .const x => x
  | .bin op a b => op.apply (a.eval ρ) (b.eval ρ)
  | .rotr k a => (a.eval ρ).rotateRight k
  | .shr k a => (a.eval ρ) >>> shiftMask w k

/-- The values of the numbered words after a list of let-bound word expressions: the
    expression at position `j` of the list binds the word numbered `n + j`. -/
def evalLets {w : Nat} : (Nat → BitVec w) → Nat → List (WExp w) → Nat → BitVec w
  | ρ, _, [] => ρ
  | ρ, n, e :: es => evalLets (fun i => if i = n then e.eval ρ else ρ i) (n + 1) es

/-- A renaming from the context `Γ` to an extension `Δ`. -/
abbrev Ren (Γ Δ : Ctxt jasminDialect) : Type := ∀ t : JasminTy, Var Γ t → Var Δ t

/-- The compilation of a word expression at the variables `env` of the numbered words: the
    bindings of its operations, in post-order, then the continuation `k` at the extended
    context with the renaming into it and the variable of the value. -/
def WExp.gen {w : Nat} {s : JasminTy} : WExp w → {Γ : Ctxt jasminDialect} →
    (Nat → Var Γ (.reg w)) →
    ({Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s) →
    Com jasminDialect Γ s
  | .var i, _, env, k => k (fun _ v => v) (env i)
  | .const x, _, _, k =>
      .var ⟨.regConst w x.toNat, rfl, .nil⟩ (k (fun _ v => v.there) .here)
  | .bin op a b, _, env, k =>
      a.gen env fun ρ va => b.gen (fun i => ρ _ (env i)) fun ρ' vb =>
        .var ⟨.regArith op w, rfl, .cons (ρ' _ va) (.cons vb .nil)⟩
          (k (fun _ v => (ρ' _ (ρ _ v)).there) .here)
  | .rotr n a, _, env, k =>
      a.gen env fun ρ va =>
        .var ⟨.rorImm w n, rfl, .cons va .nil⟩ (k (fun _ v => (ρ _ v).there) .here)
  | .shr n a, _, env, k =>
      a.gen env fun ρ va =>
        .var ⟨.shrImm w n, rfl, .cons va .nil⟩ (k (fun _ v => (ρ _ v).there) .here)

/-- The compilation of a list of let-bound word expressions, the expression at position `j`
    binding the word numbered `n + j`, then the continuation at the extended context with the
    renaming into it and the variables of the numbered words. -/
def genLetsR {w : Nat} {s : JasminTy} : List (WExp w) → {Γ : Ctxt jasminDialect} → Nat →
    (Nat → Var Γ (.reg w)) →
    ({Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s) →
    Com jasminDialect Γ s
  | [], _, _, env, k => k (fun _ v => v) env
  | e :: es, _, n, env, k =>
      e.gen env fun ρ v =>
        genLetsR es (n + 1) (fun i => if i = n then v else ρ _ (env i))
          fun ρ' env' => k (fun _ x => ρ' _ (ρ _ x)) env'

/-- The compilation of a list of let-bound word expressions, the expression at position `j`
    binding the word numbered `n + j`, then the continuation at the variables of the numbered
    words. -/
def genLets {w : Nat} {s : JasminTy} (es : List (WExp w)) {Γ : Ctxt jasminDialect} (n : Nat)
    (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s) :
    Com jasminDialect Γ s :=
  genLetsR es n env fun _ env' => k env'

/-- The load of the word at the index `i` of a stack array: the index constant and the load. -/
def genLoad {w m : Nat} {s : JasminTy} {Γ : Ctxt jasminDialect} (arr : Var Γ (.stackArr w m))
    (i : Nat)
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s) :
    Com jasminDialect Γ s :=
  .var ⟨.regConst 64 i, rfl, .nil⟩ <|
    .var ⟨.stackLoad w m, rfl, .cons arr.there (.cons .here .nil)⟩
      (k (fun _ v => v.there.there) .here)

/-- The loads of the words at the listed indices of a stack array, the load at position `j`
    of the list binding the word numbered `n + j`. -/
def genLoads {w m : Nat} {s : JasminTy} : List Nat → {Γ : Ctxt jasminDialect} →
    Var Γ (.stackArr w m) → Nat → (Nat → Var Γ (.reg w)) →
    ({Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s) →
    Com jasminDialect Γ s
  | [], _, _, _, env, k => k (fun _ v => v) env
  | i :: is, _, arr, n, env, k =>
      genLoad arr i fun ρ v =>
        genLoads is (ρ _ arr) (n + 1) (fun j => if j = n then v else ρ _ (env j))
          fun ρ' env' => k (fun _ x => ρ' _ (ρ _ x)) env'

/-- The stores of the numbered words into a stack array of `m` words: a pair `(j, i)` stores
    the word numbered `i` at the index `j`; the program returns the array. -/
def genStores {w m : Nat} : List (Nat × Nat) → {Γ : Ctxt jasminDialect} →
    Var Γ (.stackArr w m) → (Nat → Var Γ (.reg w)) → Com jasminDialect Γ (.stackArr w m)
  | [], _, arr, _ => .ret arr
  | (j, i) :: rest, _, arr, env =>
      .var ⟨.stackStoreImm w m j, rfl, .cons arr (.cons (env i) .nil)⟩
        (genStores rest .here (fun x => (env x).there))

/-- The stores of the numbered words into a stack array of `m` words at register indices: a
    pair `(j, i)` binds the index constant `j` and stores the word numbered `i` at that index;
    the program returns the array. -/
def genStoresIdx {w m : Nat} : List (Nat × Nat) → {Γ : Ctxt jasminDialect} →
    Var Γ (.stackArr w m) → (Nat → Var Γ (.reg w)) → Com jasminDialect Γ (.stackArr w m)
  | [], _, arr, _ => .ret arr
  | (j, i) :: rest, _, arr, env =>
      .var ⟨.regConst 64 j, rfl, .nil⟩ <|
      .var ⟨.stackStore w m, rfl, .cons arr.there (.cons .here (.cons (env i).there .nil))⟩
        (genStoresIdx rest .here (fun x => (env x).there.there))

/-! ## 2. Let-lists under construction -/

/-- A list of let-bound word expressions under construction: the number of the next word and
    the expressions in reverse order. -/
structure LetSt (w : Nat) where
  /-- The number of the next bound word. -/
  next : Nat
  /-- The bound expressions, the newest first. -/
  rev : List (WExp w)

/-- Bind a word expression; returns the number of its word. -/
def LetSt.push {w : Nat} (e : WExp w) (s : LetSt w) : Nat × LetSt w :=
  (s.next, ⟨s.next + 1, e :: s.rev⟩)

/-- The let-list `s'` extends the let-list `s`. -/
def LetSt.Ext {w : Nat} (s s' : LetSt w) : Prop := ∃ L, s'.rev = L ++ s.rev

theorem LetSt.Ext.refl {w : Nat} (s : LetSt w) : s.Ext s := ⟨[], rfl⟩

theorem LetSt.Ext.trans {w : Nat} {s s' s'' : LetSt w} (h : s.Ext s') (h' : s'.Ext s'') :
    s.Ext s'' := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨L', hL'⟩ := h'
  exact ⟨L' ++ L, by rw [hL', hL, List.append_assoc]⟩

theorem LetSt.Ext.push {w : Nat} (e : WExp w) (s : LetSt w) : s.Ext (s.push e).2 :=
  ⟨[e], rfl⟩

theorem evalLets_append {w : Nat} (ρ : Nat → BitVec w) (n : Nat) (L₁ L₂ : List (WExp w)) :
    evalLets ρ n (L₁ ++ L₂) = evalLets (evalLets ρ n L₁) (n + L₁.length) L₂ := by
  induction L₁ generalizing ρ n with
  | nil => rfl
  | cons e L ih =>
      simp only [List.cons_append, evalLets, ih, List.length_cons]
      congr 1
      omega

/-- A let-list leaves the words numbered below its first binding unchanged. -/
theorem evalLets_of_lt {w : Nat} (ρ : Nat → BitVec w) (n : Nat) (L : List (WExp w)) (j : Nat)
    (hj : j < n) : evalLets ρ n L j = ρ j := by
  induction L generalizing ρ n with
  | nil => rfl
  | cons e L ih =>
      simp only [evalLets]
      rw [ih _ _ (by omega)]
      simp [Nat.ne_of_lt hj]

/-- The values of the numbered words after the let-list under construction `s`, its first
    binding the word numbered `b`, from the values `ρ` of the input words. -/
def LetSt.val {w : Nat} (b : Nat) (ρ : Nat → BitVec w) (s : LetSt w) : Nat → BitVec w :=
  evalLets ρ b s.rev.reverse

/-- The number of the next word of `s` follows its bound words, from the word numbered
    `b`. -/
def LetSt.Good {w : Nat} (b : Nat) (s : LetSt w) : Prop := s.next = b + s.rev.length

/-- An extension leaves the words numbered below the next word unchanged. -/
theorem LetSt.Ext.val_eq {w b : Nat} {s s' : LetSt w} (h : s.Ext s') (hs : s.Good b)
    (ρ : Nat → BitVec w) (j : Nat) (hj : j < s.next) : s'.val b ρ j = s.val b ρ j := by
  obtain ⟨L, hL⟩ := h
  simp only [LetSt.val, hL, List.reverse_append, evalLets_append]
  exact evalLets_of_lt _ _ _ _ (by rw [List.length_reverse]; unfold LetSt.Good at hs; omega)

/-- An extension does not decrease the number of the next word. -/
theorem LetSt.Ext.next_le {w b : Nat} {s s' : LetSt w} (h : s.Ext s') (hs : s.Good b)
    (hs' : s'.Good b) : s.next ≤ s'.next := by
  obtain ⟨L, hL⟩ := h
  unfold LetSt.Good at hs hs'
  rw [hs, hs', hL, List.length_append]
  omega

theorem LetSt.push_good {w b : Nat} (e : WExp w) {s : LetSt w} (hs : s.Good b) :
    (s.push e).2.Good b := by
  unfold LetSt.Good at *
  simp [LetSt.push, hs]
  omega

/-- A binding sets the word numbered `s.next` to the value of its expression. -/
theorem LetSt.push_val {w b : Nat} (e : WExp w) {s : LetSt w} (hs : s.Good b)
    (ρ : Nat → BitVec w) :
    (s.push e).2.val b ρ =
      fun i => if i = s.next then e.eval (s.val b ρ) else s.val b ρ i := by
  have hrev : (s.push e).2.rev.reverse = s.rev.reverse ++ [e] := by simp [LetSt.push]
  unfold LetSt.Good at hs
  simp only [LetSt.val, hrev, evalLets_append, evalLets, List.length_reverse, hs]

/-- The values after the bindings `L`, newest first, appended to `s`. -/
theorem LetSt.val_extend {w b : Nat} (ρ : Nat → BitVec w) {s : LetSt w} (hs : s.Good b)
    (m : Nat) (L : List (WExp w)) :
    LetSt.val b ρ ⟨m, L ++ s.rev⟩ = evalLets (s.val b ρ) s.next L.reverse := by
  unfold LetSt.Good at hs
  simp only [LetSt.val, List.reverse_append, evalLets_append, List.length_reverse, hs]

/-! ## 3. The values and events of the compiler -/

/-- A renaming `ρ` from `Γ` to `Δ` keeps the value of every variable from the valuation `V`
    to the valuation `V'`. -/
def RenResp {Γ Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (V : Valuation Γ) (V' : Valuation Δ) :
    Prop :=
  ∀ t (x : Var Γ t), (ρ t x).lookup V' = x.lookup V

/-- The compiled word expression passes to its continuation a variable holding the value of
    the expression: the program has the value `R` when every such continuation has it. -/
theorem WExp.gen_denote {w : Nat} {s : JasminTy} (e : WExp w) {Γ : Ctxt jasminDialect}
    (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s)
    (V : Valuation Γ) (ρv : Nat → BitVec w) (henv : ∀ i, (env i).lookup V = ρv i)
    (R : ⟦s⟧)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (V' : Valuation Δ) (v : Var Δ (.reg w)),
      RenResp ρ V V' → v.lookup V' = e.eval ρv → (k ρ v).denote V' = R) :
    (e.gen env k).denote V = R := by
  induction e generalizing Γ with
  | var i => exact hk (fun _ v => v) V (env i) (fun _ _ => rfl) (henv i)
  | const x =>
      exact hk (fun _ v => v.there) _ .here (fun _ _ => rfl)
        (show BitVec.ofNat w x.toNat = x by simp)
  | bin op a b iha ihb =>
      refine iha env _ V henv fun ρ V' va hρ hva => ?_
      refine ihb (fun i => ρ _ (env i)) _ V' (fun i => (hρ _ _).trans (henv i))
        fun ρ' V'' vb hρ' hvb => ?_
      refine hk _ _ .here (fun t x => (hρ' t (ρ t x)).trans (hρ t x)) ?_
      show op.apply ((ρ' _ va).lookup V'') (vb.lookup V'') = _
      rw [hρ', hva, hvb]
      rfl
  | rotr n a iha =>
      refine iha env _ V henv fun ρ V' va hρ hva => ?_
      refine hk _ _ .here (fun t x => hρ t x) ?_
      show (va.lookup V').rotateRight n = _
      rw [hva]
      rfl
  | shr n a iha =>
      refine iha env _ V henv fun ρ V' va hρ hva => ?_
      refine hk _ _ .here (fun t x => hρ t x) ?_
      exact congrArg (fun y : BitVec w => y >>> shiftMask w n) hva

/-- The compiled let-list passes to its continuation a renaming that keeps the values of the
    input variables and variables holding the values `evalLets`: the program has the value `R`
    when every such continuation has it. -/
theorem genLetsR_denote {w : Nat} {s : JasminTy} (es : List (WExp w)) {Γ : Ctxt jasminDialect}
    (n : Nat) (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (V : Valuation Γ) (ρv : Nat → BitVec w) (henv : ∀ i, (env i).lookup V = ρv i)
    (R : ⟦s⟧)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (V' : Valuation Δ)
      (env' : Nat → Var Δ (.reg w)), RenResp ρ V V' →
        (∀ i, (env' i).lookup V' = evalLets ρv n es i) → (k ρ env').denote V' = R) :
    (genLetsR es n env k).denote V = R := by
  induction es generalizing Γ n ρv with
  | nil => exact hk _ V env (fun _ _ => rfl) henv
  | cons e es ih =>
      refine e.gen_denote env _ V ρv henv R fun ρ V' v hρ hv => ?_
      refine ih (n + 1) _ (k := fun ρ' env' => k (fun _ x => ρ' _ (ρ _ x)) env') V'
        (fun i => if i = n then e.eval ρv else ρv i) ?_
        fun ρ' V'' env' hρ' henv' => hk _ V'' env' (fun t x => (hρ' t _).trans (hρ t x)) henv'
      intro i
      by_cases h : i = n
      · simp only [h, ite_true]
        exact hv
      · simp only [h, ite_false]
        exact (hρ _ _).trans (henv i)

/-- The compiled let-list passes to its continuation variables holding the values
    `evalLets`: the program has the value `R` when every such continuation has it. -/
theorem genLets_denote {w : Nat} {s : JasminTy} (es : List (WExp w)) {Γ : Ctxt jasminDialect}
    (n : Nat) (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (V : Valuation Γ) (ρv : Nat → BitVec w) (henv : ∀ i, (env i).lookup V = ρv i)
    (R : ⟦s⟧)
    (hk : ∀ {Δ : Ctxt jasminDialect} (V' : Valuation Δ) (env' : Nat → Var Δ (.reg w)),
      (∀ i, (env' i).lookup V' = evalLets ρv n es i) → (k env').denote V' = R) :
    (genLets es n env k).denote V = R :=
  genLetsR_denote es n env _ V ρv henv R fun _ V' env' _ henv' => hk V' env' henv'

/-- The values of the numbered words after loads from the array `A`: the load of the index
    at position `j` of the list binds the word numbered `n + j`. -/
def loadVals {w m : Nat} (A : Fin m → BitVec w) :
    (Nat → BitVec w) → Nat → List Nat → Nat → BitVec w
  | ρ, _, [] => ρ
  | ρ, n, i :: is =>
      loadVals A (fun j => if j = n then stackGet A (BitVec.ofNat 64 i).toNat else ρ j) (n + 1) is

/-- The load passes to its continuation a variable holding the word at the index `i`. -/
theorem genLoad_denote {w m : Nat} {s : JasminTy} {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (i : Nat)
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s)
    (V : Valuation Γ) (A : Fin m → BitVec w) (harr : arr.lookup V = A) (R : ⟦s⟧)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (V' : Valuation Δ) (v : Var Δ (.reg w)),
      RenResp ρ V V' → v.lookup V' = stackGet A (BitVec.ofNat 64 i).toNat →
        (k ρ v).denote V' = R) :
    (genLoad arr i k).denote V = R := by
  refine hk _ _ .here (fun _ _ => rfl) ?_
  show stackGet (arr.lookup V) (BitVec.ofNat 64 i).toNat = _
  rw [harr]

/-- The loads pass to their continuation variables holding the values `loadVals`. -/
theorem genLoads_denote {w m : Nat} {s : JasminTy} (is : List Nat) {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (n : Nat) (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (V : Valuation Γ) (A : Fin m → BitVec w) (harr : arr.lookup V = A)
    (ρv : Nat → BitVec w) (henv : ∀ i, (env i).lookup V = ρv i) (R : ⟦s⟧)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (V' : Valuation Δ)
      (env' : Nat → Var Δ (.reg w)), RenResp ρ V V' →
        (∀ i, (env' i).lookup V' = loadVals A ρv n is i) → (k ρ env').denote V' = R) :
    (genLoads is arr n env k).denote V = R := by
  induction is generalizing Γ n ρv with
  | nil => exact hk _ V env (fun _ _ => rfl) henv
  | cons i is ih =>
      refine genLoad_denote arr i _ V A harr R fun ρ V' v hρ hv => ?_
      refine ih (ρ _ arr) (n + 1) _ (k := fun ρ' env' => k (fun _ x => ρ' _ (ρ _ x)) env') V'
        ((hρ _ _).trans harr)
        (fun j => if j = n then stackGet A (BitVec.ofNat 64 i).toNat else ρv j) ?_
        fun ρ' V'' env' hρ' henv' => hk _ V'' env' (fun t x => (hρ' t _).trans (hρ t x)) henv'
      intro j
      by_cases h : j = n
      · simp only [h, ite_true]
        exact hv
      · simp only [h, ite_false]
        exact (hρ _ _).trans (henv j)

/-- The stores write the values of the numbered words into the array, in list order. -/
theorem genStores_denote {w m : Nat} (L : List (Nat × Nat)) {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (env : Nat → Var Γ (.reg w)) (V : Valuation Γ)
    (A : Fin m → BitVec w) (harr : arr.lookup V = A) (ρv : Nat → BitVec w)
    (henv : ∀ i, (env i).lookup V = ρv i) :
    (genStores L arr env).denote V = L.foldl (fun A p => stackSet A p.1 (ρv p.2)) A := by
  induction L generalizing Γ A with
  | nil => exact harr
  | cons p L ih =>
      obtain ⟨j, i⟩ := p
      exact ih .here (fun x => (env x).there) _ _
        (by show stackSet (arr.lookup V) j ((env i).lookup V) = _; rw [harr, henv])
        (fun x => henv x)

/-- The stores at register indices below `2 ^ 64` denote the successive updates of the
    array. -/
theorem genStoresIdx_denote {w m : Nat} (L : List (Nat × Nat)) {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (env : Nat → Var Γ (.reg w)) (V : Valuation Γ)
    (A : Fin m → BitVec w) (harr : arr.lookup V = A) (ρv : Nat → BitVec w)
    (henv : ∀ i, (env i).lookup V = ρv i) (hL : ∀ p ∈ L, p.1 < 2 ^ 64) :
    (genStoresIdx L arr env).denote V = L.foldl (fun A p => stackSet A p.1 (ρv p.2)) A := by
  induction L generalizing Γ A with
  | nil => exact harr
  | cons p L ih =>
      obtain ⟨j, i⟩ := p
      have hj : j < 2 ^ 64 := hL _ List.mem_cons_self
      exact ih .here (fun x => (env x).there.there) _ _
        (by
          show stackSet (arr.lookup V) (BitVec.ofNat 64 j).toNat ((env i).lookup V) = _
          rw [harr, henv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj])
        (fun x => henv x) (fun p hp => hL p (List.mem_cons_of_mem _ hp))

/-- A binding of a quiet operation followed by a program with fixed events has fixed
    events. -/
theorem leakFixed_var_quiet (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (hq : Dialects.JasminComLLeak.jKind Pj e.op = .quiet)
    (hb : LeakFixed (jLeakModel Pj) body) : LeakFixed (jLeakModel Pj) (.var e body) := by
  intro V₁ V₂
  simp only [ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak, ComLevelCheck.opLeak,
    jLeakModel, hq, List.nil_append]
  exact hb _ _

/-- A compiled word expression has fixed events when its continuations have. -/
theorem WExp.gen_fixed {w : Nat} {s : JasminTy} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (e : WExp w) {Γ : Ctxt jasminDialect}
    (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (v : Var Δ (.reg w)),
      LeakFixed (jLeakModel Pj) (k ρ v)) :
    LeakFixed (jLeakModel Pj) (e.gen env k) := by
  induction e generalizing Γ with
  | var i => exact hk _ _
  | const x =>
      exact leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV]) (hk _ _)
  | bin op a b iha ihb =>
      exact iha env _ fun ρ va => ihb _ _ fun ρ' vb =>
        leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV]) (hk _ _)
  | rotr n a iha =>
      exact iha env _ fun ρ va =>
        leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV]) (hk _ _)
  | shr n a iha =>
      exact iha env _ fun ρ va =>
        leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV]) (hk _ _)

/-- A compiled let-list with a renaming-receiving continuation has fixed events when its
    continuations have. -/
theorem genLetsR_fixed {w : Nat} {s : JasminTy} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (es : List (WExp w)) {Γ : Ctxt jasminDialect} (n : Nat)
    (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (env' : Nat → Var Δ (.reg w)),
      LeakFixed (jLeakModel Pj) (k ρ env')) :
    LeakFixed (jLeakModel Pj) (genLetsR es n env k) := by
  induction es generalizing Γ n with
  | nil => exact hk _ _
  | cons e es ih => exact e.gen_fixed Pj hV env _ fun ρ v => ih _ _ _ fun _ _ => hk _ _

/-- A compiled let-list has fixed events when its continuations have. -/
theorem genLets_fixed {w : Nat} {s : JasminTy} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (es : List (WExp w)) {Γ : Ctxt jasminDialect} (n : Nat)
    (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (hk : ∀ {Δ : Ctxt jasminDialect} (env' : Nat → Var Δ (.reg w)),
      LeakFixed (jLeakModel Pj) (k env')) :
    LeakFixed (jLeakModel Pj) (genLets es n env k) :=
  genLetsR_fixed Pj hV es n env _ fun _ env' => hk env'

/-- A load at a constant index has fixed events when its continuations have. -/
theorem genLoad_fixed {w m : Nat} {s : JasminTy} {Γ : Ctxt jasminDialect} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (arr : Var Γ (.stackArr w m)) (i : Nat)
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → Var Δ (.reg w) → Com jasminDialect Δ s)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (v : Var Δ (.reg w)),
      LeakFixed (jLeakModel Pj) (k ρ v)) :
    LeakFixed (jLeakModel Pj) (genLoad arr i k) := by
  intro V₁ V₂
  simp only [genLoad, ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak,
    ComLevelCheck.opLeak, jLeakModel, Dialects.JasminComLLeak.jKind, hV, List.nil_append]
  exact congrArg₂ (· ++ ·) rfl (hk _ _ _ _)

/-- Loads at constant indices have fixed events when their continuations have. -/
theorem genLoads_fixed {w m : Nat} {s : JasminTy} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (is : List Nat) {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (n : Nat) (env : Nat → Var Γ (.reg w))
    (k : {Δ : Ctxt jasminDialect} → Ren Γ Δ → (Nat → Var Δ (.reg w)) → Com jasminDialect Δ s)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ρ : Ren Γ Δ) (env' : Nat → Var Δ (.reg w)),
      LeakFixed (jLeakModel Pj) (k ρ env')) :
    LeakFixed (jLeakModel Pj) (genLoads is arr n env k) := by
  induction is generalizing Γ n with
  | nil => exact hk _ _
  | cons i is ih => exact genLoad_fixed Pj hV arr i _ fun ρ v => ih _ _ _ _ fun _ _ => hk _ _

/-- Stores at constant indices have fixed events. -/
theorem genStores_fixed {w m : Nat} (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none)
    (L : List (Nat × Nat)) {Γ : Ctxt jasminDialect} (arr : Var Γ (.stackArr w m))
    (env : Nat → Var Γ (.reg w)) : LeakFixed (jLeakModel Pj) (genStores L arr env) := by
  induction L generalizing Γ with
  | nil => intro _ _; rfl
  | cons p L ih =>
      obtain ⟨j, i⟩ := p
      exact leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV]) (ih _ _)

/-- The stores at register indices have fixed events at leakage parameters with no
    variable-time operation. -/
theorem genStoresIdx_fixed {w m : Nat} (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) (L : List (Nat × Nat)) {Γ : Ctxt jasminDialect}
    (arr : Var Γ (.stackArr w m)) (env : Nat → Var Γ (.reg w)) :
    LeakFixed (jLeakModel Pj) (genStoresIdx L arr env) := by
  induction L generalizing Γ with
  | nil => intro _ _; rfl
  | cons p L ih =>
      obtain ⟨j, i⟩ := p
      intro V₁ V₂
      simp only [genStoresIdx, ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak,
        ComLevelCheck.opLeak, jLeakModel, Dialects.JasminComLLeak.jKind, hV, List.nil_append]
      solve_by_elim

/-- The value of a numbered word after loads: the load at position `j - n` for a word
    numbered `j` among the loaded ones, and the input value otherwise. -/
theorem loadVals_apply {w m : Nat} (A : Fin m → BitVec w) (is : List Nat) :
    ∀ (ρ : Nat → BitVec w) (n j : Nat), loadVals A ρ n is j =
      if n ≤ j ∧ j < n + is.length then stackGet A (BitVec.ofNat 64 (is.getD (j - n) 0)).toNat
      else ρ j := by
  induction is with
  | nil => intro ρ n j; simp [loadVals]
  | cons i is ih =>
      intro ρ n j
      rw [loadVals, ih]
      by_cases hj : j = n
      · subst hj
        simp
      · by_cases hlt : n + 1 ≤ j ∧ j < n + 1 + is.length
        · rw [ite_eq_left hlt, ite_eq_left (by simp; omega)]
          rw [show j - n = (j - (n + 1)) + 1 by omega]
          simp
        · rw [ite_eq_right hlt, ite_eq_right hj, ite_eq_right (by simp; omega)]

/-- Stores of eight words at the indices `0, …, 7` write each word at its index. -/
theorem foldl_stores8 {w : Nat} (L : List (Nat × Nat)) (hl : L.length = 8)
    (hk : ∀ k < 8, (L.getD k (0, 0)).1 = k) (g : Nat → BitVec w) (A : Fin 8 → BitVec w) :
    L.foldl (fun A p => stackSet A p.1 (g p.2)) A =
      fun j : Fin 8 => g ((L.getD j.val (0, 0)).2) := by
  match L, hl with
  | [⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩], _ =>
      have h0 := hk 0 (by omega); have h1 := hk 1 (by omega); have h2 := hk 2 (by omega)
      have h3 := hk 3 (by omega); have h4 := hk 4 (by omega); have h5 := hk 5 (by omega)
      have h6 := hk 6 (by omega); have h7 := hk 7 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7
      subst h0 h1 h2 h3 h4 h5 h6 h7
      funext j
      fin_cases j <;> simp [stackSet]

/-- An invariant of the steps of `Fin.foldl` holds after all of them. -/
theorem fin_foldl_inv {α : Type} (Q : Nat → α → Prop) :
    ∀ {n : Nat} (f : α → Fin n → α) (x : α), Q 0 x →
      (∀ (j : Fin n) a, Q j.val a → Q (j.val + 1) (f a j)) → Q n (Fin.foldl n f x)
  | 0, _, _, h0, _ => by simpa using h0
  | n + 1, f, x, h0, hs => by
      rw [Fin.foldl_succ_last]
      exact hs (Fin.last n) _
        (fin_foldl_inv Q (fun a i => f a i.castSucc) x h0 fun j a h => hs j.castSucc a h)

end CatCrypt.Crypto.SecureCompilation.HashTemplate
