/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain
public import CatCrypt.Crypto.Optimizer.Rewrite.AegraphNFLeak

/-!
# Fusion of vector operations: three-input logic and rotation

Two rules of the generic acyclic e-graph (`AegraphGeneric.Rule`) on the dialect
`jasminVec` of scalar and x86 vector operations, each reading the definition table of the
pass for the bindings of the operands of a lane-wise operation on 512-bit registers.

`fuseTern` fires on a lane-wise operation whose lane function acts bit by bit (`and`,
`or`, `xor`, `andn`: `bitFn`) with an operand bound to another such operation. For
`o₂ (o₁ a b) c` it offers `tern` with the truth table of `fun p q r => f₂ (f₁ p q) r` on
`a`, `b`, `c`; for `o₂ a (o₁ b c)` the truth table of `fun p q r => f₂ p (f₁ q r)`. The
sixteen pairs of operations in each of the two positions are covered by the two lemmas
`tern_left` and `tern_right`, proved bit by bit from `getLsbD_semTern_table`. The Keccak χ
step `a xor (andn b c)` gets the table `ternTable fun p q r => p ^^ (!q && r)`, the table
`chiB` of the text model.

`fuseRol` fires on the lane-wise `or` of the left shift by `imm` and the logical right
shift by `L - imm` of one variable at one lane width `L`, `imm < L`, in either order, and
offers `rol L imm` (`rol_of_shifts`).

The rule set `vecFusions` gives `tern` and `rol` the cost `1` and every other operation the
cost `2`, so extraction takes the fused form; it marks no operation pure, so the pass
merges no binding. The binding of the intermediate value is kept: the fused operation
reads the operands of the intermediate value, and a dead-code pass removes the intermediate
binding when it has no other use. `fuseVec` is the pass `aegraphOptNF vecFusions` on
structured programs.

## Main definitions

* `bitFn`, `Bitwise`: the Boolean function of a lane operation that acts bit by bit, and
  the statement that a value is that function of two values at every bit.
* `lwNode?`, `shiNode?`, `logicNode?`: a node of the definition table read as a lane-wise
  operation, an immediate shift or a bitwise operation on variables.
* `fuseTern`, `fuseRol`: the alternatives of the two rules.
* `ternRule`, `rolRule`, `vecFusions`: the rules and the rule set.
* `fuseVec`, `fuseVecStep`, `vecSem`: the pass, its chain step and the semantics of
  programs of `jasminVec` at a fuel.

## Main results

* `tern_left`, `tern_right`: the truth-table lemma for an intermediate value in the first
  and in the second operand.
* `rol_of_shifts`, `rol_of_shifts_swap`: a rotation from its two shifts.
* `fuseTern_sound`, `fuseRol_sound`: an alternative of a rule denotes the expression.
* `fuseVec_denote`: the pass preserves the denotation at every fuel.
* `fuseVecCert`: the certificate of the chain step, with equality as both relations.
* `vecFusions_indep`: every alternative of the rule set emits no event.
* `fuseVec_nfCT`: the pass keeps a program constant time.
* `nfGo_leakRun`: for a rule set whose extraction returns one binding with the events of
  the input binding, the traversal has the leakage run of its input.
* `fuseVec_leakRun`: the pass runs to the results and the events of its input.
* `fuseTern_chi`: on `a xor n` with `n` bound to `andn b c` the rule offers the one
  alternative `tern` with the χ table on `a`, `b`, `c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecPeephole

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp semLW semShImm semRol
  semTern ternTable getLsbD_semTern_table getLsbD_semLW_bin getLsbD_ofLanes
  rotateLeft_eq_or_shifts)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Labels)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.Optimizer.Rewrite
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (varLvl getLvl_var varOfLvl?
  varOfLvl?_lookup castTo?_mk gatherArgs gatherArgs_argLvls evalKey evalKey_expr DSound Alt
  Rule RuleSet Defs varEq varEq_sound RulesIndep)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote
  aegraphOptNF_nfCT)
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules (rulesIndep_of_forall)
open Ctxt (Var Valuation)

/-! ## 1. Lane operations that act bit by bit -/

/-- The Boolean function of a lane operation that acts bit by bit; `none` for the
    arithmetic operations and the shifts. -/
def bitFn : JasminBinOp → Option (Bool → Bool → Bool)
  | .and => some fun x y => x && y
  | .or => some fun x y => x || y
  | .xor => some fun x y => x ^^ y
  | .andn => some fun x y => !x && y
  | _ => none

/-- A bit of the result of an operation with the Boolean function `f` is `f` of the bits
    of the operands. -/
theorem bitFn_apply {b : JasminBinOp} {f : Bool → Bool → Bool} (h : bitFn b = some f)
    {W : Nat} (x y : BitVec W) (j : Nat) :
    (b.apply x y).getLsbD j = f (x.getLsbD j) (y.getLsbD j) := by
  cases b <;> cases h <;> first
    | (simp [JasminBinOp.apply]; done)
    | (by_cases hj : j < W
       · simp [JasminBinOp.apply, hj]
       · have hy : y.getLsbD j = false := BitVec.getLsbD_of_ge y j (Nat.le_of_not_lt hj)
         simp [JasminBinOp.apply, hj, hy])

/-- `Bitwise f v a b`: every bit of the 512-bit value `v` is `f` of the bits of `a` and
    `b`. -/
def Bitwise (f : Bool → Bool → Bool) (v a b : BitVec 512) : Prop :=
  ∀ i : Nat, v.getLsbD i = (decide (i < 512) && f (a.getLsbD i) (b.getLsbD i))

/-- A lane-wise operation that acts bit by bit is bitwise at every positive lane width. -/
theorem bitwise_semLW {L : Nat} (hL : 0 < L) {b : JasminBinOp} {f : Bool → Bool → Bool}
    (h : bitFn b = some f) (x y : BitVec 512) : Bitwise f (semLW L (.bin b) x y) x y :=
  fun i => getLsbD_semLW_bin hL b f (fun x y j => bitFn_apply h x y j) x y i

/-- **The truth table of an intermediate value in the first operand.** For `u` the
    function `f₁` of `a` and `b` and `v` the function `f₂` of `u` and `c`, the three-input
    operation with the table of `fun p q r => f₂ (f₁ p q) r` on `a`, `b`, `c` is `v`. -/
theorem tern_left {f₁ f₂ : Bool → Bool → Bool} {u v a b c : BitVec 512}
    (hu : Bitwise f₁ u a b) (hv : Bitwise f₂ v u c) :
    semTern (ternTable fun p q r => f₂ (f₁ p q) r) a b c = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_semTern_table, hv i, hu i]
  simp only [hi, decide_true, Bool.true_and]

/-- **The truth table of an intermediate value in the second operand.** For `u` the
    function `f₁` of `b` and `c` and `v` the function `f₂` of `a` and `u`, the three-input
    operation with the table of `fun p q r => f₂ p (f₁ q r)` on `a`, `b`, `c` is `v`. -/
theorem tern_right {f₁ f₂ : Bool → Bool → Bool} {u v a b c : BitVec 512}
    (hu : Bitwise f₁ u b c) (hv : Bitwise f₂ v a u) :
    semTern (ternTable fun p q r => f₂ p (f₁ q r)) a b c = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_semTern_table, hv i, hu i]
  simp only [hi, decide_true, Bool.true_and]

/-- **A rotation from its two shifts.** The lane-wise `or` of the left shift by `imm` and
    the logical right shift by `L - imm`, `imm < L`, is the rotation left by `imm`. -/
theorem rol_of_shifts {L imm : Nat} (hL : 0 < L) (h : imm < L) (x : BitVec 512) :
    semLW L (.bin .or) (semShImm L true imm x) (semShImm L false (L - imm) x)
      = semRol L imm x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_semLW_bin hL .or (fun p q => p || q)
    (fun x y j => by simp [JasminBinOp.apply])]
  simp only [semShImm, semRol, getLsbD_ofLanes, rotateLeft_eq_or_shifts _ h,
    BitVec.getLsbD_or, hi, decide_true, Bool.true_and, ↓reduceIte, Bool.false_eq_true]

/-- The rotation from its two shifts in the other order. -/
theorem rol_of_shifts_swap {L imm : Nat} (hL : 0 < L) (h : imm < L) (x : BitVec 512) :
    semLW L (.bin .or) (semShImm L false (L - imm) x) (semShImm L true imm x)
      = semRol L imm x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_semLW_bin hL .or (fun p q => p || q)
    (fun x y j => by simp [JasminBinOp.apply])]
  simp only [semShImm, semRol, getLsbD_ofLanes, rotateLeft_eq_or_shifts _ h,
    BitVec.getLsbD_or, hi, decide_true, Bool.true_and, ↓reduceIte, Bool.false_eq_true,
    Bool.or_comm]

/-! ## 2. Nodes of the definition table on variables -/

section Nodes

variable {Δ : Ctxt jasminVec}

/-- The value of a variable bound to a recorded node is the value of the node. -/
theorem lookup_of_node {V : Valuation Δ} {D : Defs jasminVec} (hD : DSound V D)
    {t : JasminTy} (a : Var Δ t) {k : jasminVec.Op × List Nat}
    (h : D[varLvl a]? = some k) {v : ⟦t⟧} (hk : evalKey V k.1 k.2 = some ⟨t, v⟩) :
    a.lookup V = v := by
  obtain ⟨x, h1, h2⟩ := hD _ _ h
  rw [getLvl_var] at h2
  rw [hk] at h1
  rw [← h1] at h2
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2

/-- The value of an expression is the value of its node. -/
theorem denote_of_node {V : Valuation Δ} {t : JasminTy} (e : Expr jasminVec Δ t)
    {v : ⟦t⟧} (hk : evalKey V e.op (AegraphGeneric.argLvls e.args) = some ⟨t, v⟩) :
    e.denote V = v := by
  have h := evalKey_expr e V
  rw [hk] at h
  exact (eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2).symm

/-- A node read as a lane-wise operation of a `JasminBinOp` on two 512-bit variables: the
    lane width, the operation and the variables at its argument levels. -/
def lwNode? (Δ : Ctxt jasminVec) :
    jasminVec.Op × List Nat → Option (Nat × JasminBinOp × Var Δ VReg × Var Δ VReg)
  | (.inr (.lw .zmm L (.bin b)), [l1, l2]) =>
      match varOfLvl? Δ VReg l1, varOfLvl? Δ VReg l2 with
      | some a1, some a2 => some (L, b, a1, a2)
      | _, _ => none
  | _ => none

/-- A node read as an immediate shift of a 512-bit variable: the lane width, the
    direction, the immediate and the variable at its argument level. -/
def shiNode? (Δ : Ctxt jasminVec) :
    jasminVec.Op × List Nat → Option (Nat × Bool × Nat × Var Δ VReg)
  | (.inr (.shi .zmm L left imm), [l]) =>
      match varOfLvl? Δ VReg l with
      | some a => some (L, left, imm, a)
      | none => none
  | _ => none

/-- The node `lwNode?` reads evaluates to the lane-wise operation on the variables. -/
theorem lwNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {L : Nat}
    {b : JasminBinOp} {a1 a2 : Var Δ VReg} (h : lwNode? Δ k = some (L, b, a1, a2)) :
    evalKey V k.1 k.2 = some ⟨VReg, semLW L (.bin b) (a1.lookup V) (a2.lookup V)⟩ := by
  unfold lwNode? at h
  split at h
  · rename_i L' b' l1 l2
    split at h
    · rename_i b1 b2 hb1 hb2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have he := evalKey_expr (lwE L' (.bin b') b1 b2) V
      rw [lwE_denote] at he
      refine Eq.trans ?_ he
      have hg : gatherArgs V [VReg, VReg] [l1, l2]
          = some (.cons (b1.lookup V) (.cons (b2.lookup V) .nil)) := by
        simp [gatherArgs, varOfLvl?_lookup hb1 V, varOfLvl?_lookup hb2 V,
          castTo?_mk (d := jasminVec)]
      show (gatherArgs (d := jasminVec) V [VReg, VReg] [l1, l2]).map _
        = (gatherArgs (d := jasminVec) V [VReg, VReg]
            (AegraphGeneric.argLvls (lwE L' (.bin b') b1 b2).args)).map _
      rw [hg]
      exact (congrArg (Option.map _)
        (gatherArgs_argLvls (d := jasminVec) V (lwE L' (.bin b') b1 b2).args)).symm
    · cases h
  · cases h

/-- The node `shiNode?` reads evaluates to the shift of the variable. -/
theorem shiNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {L imm : Nat}
    {left : Bool} {a : Var Δ VReg} (h : shiNode? Δ k = some (L, left, imm, a)) :
    evalKey V k.1 k.2 = some ⟨VReg, semShImm L left imm (a.lookup V)⟩ := by
  unfold shiNode? at h
  split at h
  · rename_i L' left' imm' l
    split at h
    · rename_i b1 hb1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      have he := evalKey_expr (shiE L' left' imm' b1) V
      rw [shiE_denote] at he
      refine Eq.trans ?_ he
      have hg : gatherArgs V [VReg] [l] = some (.cons (b1.lookup V) .nil) := by
        simp [gatherArgs, varOfLvl?_lookup hb1 V, castTo?_mk (d := jasminVec)]
      show (gatherArgs (d := jasminVec) V [VReg] [l]).map _
        = (gatherArgs (d := jasminVec) V [VReg]
            (AegraphGeneric.argLvls (shiE L' left' imm' b1).args)).map _
      rw [hg]
      exact (congrArg (Option.map _)
        (gatherArgs_argLvls (d := jasminVec) V (shiE L' left' imm' b1).args)).symm
    · cases h
  · cases h

/-- A node read as a lane-wise operation that acts bit by bit at a positive lane width:
    the lane width, the Boolean function and the variables. -/
def logicNode? (Δ : Ctxt jasminVec) (k : jasminVec.Op × List Nat) :
    Option (Nat × (Bool → Bool → Bool) × Var Δ VReg × Var Δ VReg) :=
  match lwNode? Δ k with
  | some (L, b, a1, a2) =>
      match bitFn b with
      | some f => if 0 < L then some (L, f, a1, a2) else none
      | none => none
  | none => none

/-- The node `logicNode?` reads evaluates to a value that is the Boolean function of the
    variables at every bit. -/
theorem logicNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {L : Nat}
    {f : Bool → Bool → Bool} {a1 a2 : Var Δ VReg}
    (h : logicNode? Δ k = some (L, f, a1, a2)) :
    ∃ v : BitVec 512, evalKey V k.1 k.2 = some ⟨VReg, v⟩ ∧
      Bitwise f v (a1.lookup V) (a2.lookup V) := by
  unfold logicNode? at h
  split at h
  · rename_i L' b c1 c2 hn
    split at h
    · rename_i f' hf
      split at h
      · rename_i hL
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨_, lwNode?_sound V hn, bitwise_semLW hL hf _ _⟩
      · cases h
    · cases h
  · cases h

end Nodes

/-! ## 3. The alternatives of the two rules -/

section Alts

variable {Δ : Ctxt jasminVec}

/-- The alternatives of the three-input fusion for an expression on a 512-bit register: for
    a bitwise operation `f₂` on `x` and `y`, `tern` on the operands of `x` and on `y` when
    `x` is bound to a bitwise operation, and `tern` on `x` and the operands of `y` when
    `y` is. -/
def fuseTernAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  match logicNode? Δ (e.op, AegraphGeneric.argLvls e.args) with
  | some (L, f₂, x, y) =>
      (match (D[varLvl x]?).bind (logicNode? Δ) with
        | some (_, f₁, a, b) =>
            [Alt.one (ternE L (ternTable fun p q r => f₂ (f₁ p q) r) a b y)]
        | none => []) ++
      (match (D[varLvl y]?).bind (logicNode? Δ) with
        | some (_, f₁, b, c) =>
            [Alt.one (ternE L (ternTable fun p q r => f₂ p (f₁ q r)) x b c)]
        | none => [])
  | none => []

/-- The alternatives of the three-input fusion: those of `fuseTernAt` at the type of a
    512-bit register, none at another type. -/
def fuseTern (D : Defs jasminVec) : {s : JasminTy} → Expr jasminVec Δ s → List (Alt Δ s)
  | .reg 512, e => fuseTernAt D e
  | _, _ => []

/-- The alternatives of the rotation fusion for an expression on a 512-bit register: for
    the lane-wise `or` at width `L` of two shifts of one variable at width `L`, one left by
    `imm < L` and one right by `L - imm`, the rotation left by `imm`. -/
def fuseRolAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  match lwNode? Δ (e.op, AegraphGeneric.argLvls e.args) with
  | some (L, .or, x, y) =>
      match (D[varLvl x]?).bind (shiNode? Δ), (D[varLvl y]?).bind (shiNode? Δ) with
      | some (L₁, d₁, i₁, a), some (L₂, d₂, i₂, a') =>
          if L₁ = L ∧ L₂ = L ∧ 0 < L ∧ varEq a a' = true ∧ d₁ = true ∧ d₂ = false ∧
              i₁ < L ∧ i₂ = L - i₁ then
            [Alt.one (rolE L i₁ a)]
          else if L₁ = L ∧ L₂ = L ∧ 0 < L ∧ varEq a a' = true ∧ d₁ = false ∧ d₂ = true ∧
              i₂ < L ∧ i₁ = L - i₂ then
            [Alt.one (rolE L i₂ a)]
          else []
      | _, _ => []
  | _ => []

/-- The alternatives of the rotation fusion: those of `fuseRolAt` at the type of a 512-bit
    register, none at another type. -/
def fuseRol (D : Defs jasminVec) : {s : JasminTy} → Expr jasminVec Δ s → List (Alt Δ s)
  | .reg 512, e => fuseRolAt D e
  | _, _ => []

variable {D : Defs jasminVec} {V : Valuation Δ}

/-- An alternative of `fuseTernAt` denotes the expression. -/
theorem fuseTernAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ fuseTernAt D e, alt.denote V = e.denote V := by
  intro alt halt
  unfold fuseTernAt at halt
  split at halt
  · rename_i L f₂ x y hn
    obtain ⟨v, hv, hbit⟩ := logicNode?_sound V hn
    have hev : e.denote V = v := denote_of_node e hv
    rcases List.mem_append.mp halt with halt | halt
    · split at halt
      · rename_i L₁ f₁ a b hx
        obtain ⟨k, hk, hk'⟩ := Option.bind_eq_some_iff.mp hx
        obtain ⟨u, hu, hubit⟩ := logicNode?_sound V hk'
        have hxu : x.lookup V = u := lookup_of_node hD x hk hu
        obtain rfl := List.mem_singleton.mp halt
        show (ternE L _ a b y).denote V = e.denote V
        rw [ternE_denote, hev]
        exact tern_left hubit (hxu ▸ hbit)
      · cases halt
    · split at halt
      · rename_i L₁ f₁ b c hy
        obtain ⟨k, hk, hk'⟩ := Option.bind_eq_some_iff.mp hy
        obtain ⟨u, hu, hubit⟩ := logicNode?_sound V hk'
        have hyu : y.lookup V = u := lookup_of_node hD y hk hu
        obtain rfl := List.mem_singleton.mp halt
        show (ternE L _ x b c).denote V = e.denote V
        rw [ternE_denote, hev]
        exact tern_right hubit (hyu ▸ hbit)
      · cases halt
  · cases halt

/-- **An alternative of the three-input fusion denotes the expression.** -/
theorem fuseTern_sound (hD : DSound V D) {s : JasminTy} (e : Expr jasminVec Δ s) :
    ∀ alt ∈ fuseTern D e, alt.denote V = e.denote V := by
  intro alt halt
  unfold fuseTern at halt
  split at halt
  · exact fuseTernAt_sound hD _ alt halt
  · cases halt

/-- An alternative of `fuseRolAt` denotes the expression. -/
theorem fuseRolAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ fuseRolAt D e, alt.denote V = e.denote V := by
  intro alt halt
  unfold fuseRolAt at halt
  split at halt
  · rename_i L x y hn
    have hev : e.denote V = semLW L (.bin .or) (x.lookup V) (y.lookup V) :=
      denote_of_node e (lwNode?_sound V hn)
    split at halt
    · rename_i L₁ d₁ i₁ a L₂ d₂ i₂ a' hx hy
      obtain ⟨kx, hkx, hkx'⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨ky, hky, hky'⟩ := Option.bind_eq_some_iff.mp hy
      have hxv := lookup_of_node hD x hkx (shiNode?_sound V hkx')
      have hyv := lookup_of_node hD y hky (shiNode?_sound V hky')
      split at halt
      · rename_i hc
        obtain ⟨rfl, rfl, hL, ha, rfl, rfl, hi, rfl⟩ := hc
        obtain rfl := varEq_sound a a' ha
        obtain rfl := List.mem_singleton.mp halt
        simp only [Alt.denote]
        rw [rolE_denote, hev, hxv, hyv]
        exact (rol_of_shifts hL hi _).symm
      · split at halt
        · rename_i hc
          obtain ⟨rfl, rfl, hL, ha, rfl, rfl, hi, rfl⟩ := hc
          obtain rfl := varEq_sound a a' ha
          obtain rfl := List.mem_singleton.mp halt
          simp only [Alt.denote]
          rw [rolE_denote, hev, hxv, hyv]
          exact (rol_of_shifts_swap hL hi _).symm
        · cases halt
    · cases halt
  · cases halt

/-- **An alternative of the rotation fusion denotes the expression.** -/
theorem fuseRol_sound (hD : DSound V D) {s : JasminTy} (e : Expr jasminVec Δ s) :
    ∀ alt ∈ fuseRol D e, alt.denote V = e.denote V := by
  intro alt halt
  unfold fuseRol at halt
  split at halt
  · exact fuseRolAt_sound hD _ alt halt
  · cases halt

end Alts

/-! ## 4. The rule set and the pass -/

/-- The rule of the three-input fusion. -/
def ternRule : Rule jasminVec where
  apply D _ _ e := fuseTern D e
  sound _ _ _ hD _ e := fuseTern_sound hD e

/-- The rule of the rotation fusion. -/
def rolRule : Rule jasminVec where
  apply D _ _ e := fuseRol D e
  sound _ _ _ hD _ e := fuseRol_sound hD e

/-- The operation traits of the fusion pass: `tern` and `rol` cost `1`, every other
    operation `2`; no operation is merged. -/
def vecFusionTraits : OpTraits jasminVec where
  pure _ := false
  speculatable _ := false
  constLike _ := false
  cost
    | .inr (.tern ..) => 1
    | .inr (.rol ..) => 1
    | _ => 2

/-- The rule set of the fusion pass: the three-input fusion and the rotation fusion. -/
def vecFusions : RuleSet jasminVec where
  toOpTraits := vecFusionTraits
  rules := [ternRule, rolRule]

/-- **The fusion pass** on structured programs of `jasminVec`. -/
def fuseVec {Γ : Ctxt jasminVec} {ts : List JasminTy} (p : NFProg jasminVec Γ ts) :
    NFProg jasminVec Γ ts :=
  aegraphOptNF vecFusions p

/-- **The fusion pass preserves the denotation**: the output denotes, at every fuel, what
    the input denotes. -/
theorem fuseVec_denote {Γ : Ctxt jasminVec} {ts : List JasminTy} (p : NFProg jasminVec Γ ts)
    (fuel : Nat) : (fuseVec p).denote fuel = p.denote fuel :=
  aegraphOptNF_denote vecFusions p fuel

/-- The semantics of the programs of `jasminVec` over a context at a fuel: the
    denotation. -/
def vecSem (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    Sem (NFProg jasminVec Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den p V := jasminVecDenP fuel p V

/-- The fusion pass as a chain step. -/
def fuseVecStep (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    Step (NFProg jasminVec Γ ts) (NFProg jasminVec Γ ts) :=
  ⟨"x86vec-fuse", fun p => some (fuseVec p)⟩

/-- **The certificate of the fusion step** at every fuel: the output has the denotation of
    the input, so both relations are equality. -/
def fuseVecCert (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    StepCert (fuseVecStep Γ ts).run (vecSem fuel Γ ts) (vecSem fuel Γ ts) :=
  StepCert.ofDenoteEq (vecSem fuel Γ ts) fun p q hf => by
    cases hf
    exact fuseVec_denote p fuel

/-- The input relation of the certificate is equality. -/
theorem fuseVecCert_relIn (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    (fuseVecCert fuel Γ ts).relIn = Eq := rfl

/-- The output relation of the certificate is equality. -/
theorem fuseVecCert_relOut (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    (fuseVecCert fuel Γ ts).relOut = Eq := rfl

/-! ## 5. Leakage -/

section Leak

variable (M : LeakModel jasminDialect) {Δ : Ctxt jasminVec}

/-- An alternative of `fuseTernAt` is one vector operation, which emits no event. -/
theorem fuseTernAt_indep (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ fuseTernAt D e, alt.Indep (jasminVecLeak M) := by
  intro alt halt
  unfold fuseTernAt at halt
  split at halt
  · rcases List.mem_append.mp halt with halt | halt <;> split at halt
    · obtain rfl := List.mem_singleton.mp halt
      exact fun _ _ => rfl
    · cases halt
    · obtain rfl := List.mem_singleton.mp halt
      exact fun _ _ => rfl
    · cases halt
  · cases halt

/-- An alternative of `fuseRolAt` is one vector operation, which emits no event. -/
theorem fuseRolAt_indep (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ fuseRolAt D e, alt.Indep (jasminVecLeak M) := by
  intro alt halt
  unfold fuseRolAt at halt
  split at halt
  · split at halt
    · split at halt
      · obtain rfl := List.mem_singleton.mp halt
        exact fun _ _ => rfl
      · split at halt
        · obtain rfl := List.mem_singleton.mp halt
          exact fun _ _ => rfl
        · cases halt
    · cases halt
  · cases halt

/-- **Every alternative of the fusion rule set emits no event**, so its events do not
    depend on the valuation. -/
theorem vecFusions_indep : RulesIndep (jasminVecLeak M) vecFusions := by
  refine rulesIndep_of_forall fun r hr => ?_
  simp only [vecFusions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · intro D Δ s e alt ha
    change alt ∈ fuseTern D e at ha
    unfold fuseTern at ha
    split at ha
    · exact fuseTernAt_indep M D _ alt ha
    · cases ha
  · intro D Δ s e alt ha
    change alt ∈ fuseRol D e at ha
    unfold fuseRol at ha
    split at ha
    · exact fuseRolAt_indep M D _ alt ha
    · cases ha

/-- **The fusion pass keeps a program constant time** for the entry labels `Lb`. -/
theorem fuseVec_nfCT (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List JasminTy} (Lb : Labels Γ)
    (p : NFProg jasminVec Γ ts) (hct : NFCT (jasminVecLeak M) Lb fuel p) :
    NFCT (jasminVecLeak M) Lb fuel (fuseVec p) :=
  aegraphOptNF_nfCT vecFusions (vecFusions_indep M) fuel Lb p hct

end Leak

/-! ## 6. Equal events

A rule set under which extraction always returns one binding with the events of the input
binding gives a traversal whose leakage run is that of the input. -/

section Events

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (opLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)

section Traversal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- **The leakage run of the traversal.** When extraction at the rule set `R` returns, for
    every expression, one binding with the events of the expression, the traversal of a
    program under a state sound for `V` runs to the results and the events of the program
    at the valuation pulled back along the renaming. -/
theorem nfGo_leakRun (R : RuleSet d) (L : LeakModel d)
    (H : ∀ (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s),
      ∃ e2, choose R S e = .one e2 ∧
        ∀ V, ComLevelCheck.Expr.ctLeak L e2 V = ComLevelCheck.Expr.ctLeak L e V)
    (fuel : Nat) : ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V : Valuation Δ), StSound V S →
      NFProg.leakRun L fuel (nfGo R ρ S p) V = NFProg.leakRun L fuel p (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => by
      simp only [nfGo, NFProg.leakRun, Expr.lookupArgs_renameVars]
  | _, Δ, _, ρ, S, .var (t := s) e k, V, hS => by
      obtain ⟨e2, hc, hl⟩ := H S (e.rename ρ)
      obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
      simp only [nfGo]
      split
      · rename_i w hc'
        rw [hc] at hc'
        cases hc'
      · rename_i e3 hc'
        rw [hc] at hc'
        injection hc' with h3
        subst h3
        simp only [NFProg.leakRun]
        rw [nfGo_leakRun R L H fuel _ _ k _ hS', Ctxt.Valuation.extend_comap_lift, hw,
          Expr.denote_rename, hl, Expr.ctLeak_rename]
      · rename_i s1 e3 e4 hc'
        rw [hc] at hc'
        cases hc'
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k, V, hS => by
      have hb : ∀ (acc : Valuation cs) (i : Nat),
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            NFProg.leakRun L fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) (V.comap ρ))) := by
        intro acc i
        refine (nfGo_leakRun R L H fuel _ S body _
            (stSound_append acc (stSound_extend (HasWord64.ofNat (d := d) i) hS))).trans ?_
        rw [comap_homLiftApp]
        exact congrArg (fun W => NFProg.leakRun L fuel body (hvAppend acc W))
          (Ctxt.Valuation.extend_comap_lift ρ V _)
      have hk : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            NFProg.leakRun L fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_leakRun R L H fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hb, hk, Ctxt.Valuation.lookup_comap,
        Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V, hS => by
      have hk : ∀ r : Valuation rs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp rs ρ) S k) (hvAppend r V) =
            NFProg.leakRun L fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [nfGo_leakRun R L H fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hk, Ctxt.Valuation.lookup_comap,
        nfGo_leakRun R L H fuel ρ S thn V hS, nfGo_leakRun R L H fuel ρ S els V hS]
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k, V, hS => by
      have hb : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend acc V) =
            NFProg.leakRun L fuel body (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_leakRun R L H fuel _ S body _ (stSound_append acc hS), comap_homLiftApp]
      have hk : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            NFProg.leakRun L fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [nfGo_leakRun R L H fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hb, hk, Expr.lookupArgs_renameVars]
  | _, _, _, _, _, .call .., _, _ => by
      simp only [nfGo, NFProg.leakRun]

end Traversal

variable (M : LeakModel jasminDialect) {Δ : Ctxt jasminVec}

/-- A node `lwNode?` reads is a vector operation, which is quiet. -/
theorem lwNode?_quiet {k : jasminVec.Op × List Nat}
    {r : Nat × JasminBinOp × Var Δ VReg × Var Δ VReg} (h : lwNode? Δ k = some r) :
    (jasminVecLeak M).kind k.1 = .quiet := by
  unfold lwNode? at h
  split at h
  · rfl
  · cases h

/-- A node `logicNode?` reads is a vector operation, which is quiet. -/
theorem logicNode?_quiet {k : jasminVec.Op × List Nat}
    {r : Nat × (Bool → Bool → Bool) × Var Δ VReg × Var Δ VReg}
    (h : logicNode? Δ k = some r) : (jasminVecLeak M).kind k.1 = .quiet := by
  unfold logicNode? at h
  split at h
  · rename_i hn
    exact lwNode?_quiet M hn
  · cases h

/-- An expression whose operation is quiet emits no event. -/
theorem ctLeak_of_quiet {s : JasminTy} (e : Expr jasminVec Δ s)
    (h : (jasminVecLeak M).kind e.op = .quiet) (V : Valuation Δ) :
    ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e V = [] := by
  unfold ComLevelCheck.Expr.ctLeak opLeak
  rw [h]

/-- An alternative of the two rules is one binding, and it and the expression emit no
    event. -/
theorem vecFusions_alts (D : Defs jasminVec) {s : JasminTy} (e : Expr jasminVec Δ s) :
    ∀ alt ∈ vecFusions.alts D e, ∃ e2, alt = .one e2 ∧
      ∀ V, ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e2 V
        = ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e V := by
  intro alt halt
  have hq : ∀ {e2 : Expr jasminVec Δ s}, alt = .one e2 →
      (jasminVecLeak M).kind e2.op = .quiet → (jasminVecLeak M).kind e.op = .quiet →
      ∃ e2, alt = .one e2 ∧
        ∀ V, ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e2 V
        = ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e V :=
    fun h h2 he => ⟨_, h, fun V => by rw [ctLeak_of_quiet M _ h2, ctLeak_of_quiet M _ he]⟩
  simp only [RuleSet.alts, vecFusions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at halt
  rcases halt with halt | halt
  · change alt ∈ fuseTern D e at halt
    unfold fuseTern at halt
    split at halt
    · unfold fuseTernAt at halt
      split at halt
      · rename_i hn
        have he := logicNode?_quiet M hn
        rcases List.mem_append.mp halt with halt | halt <;> split at halt
        · exact hq (List.mem_singleton.mp halt) rfl he
        · cases halt
        · exact hq (List.mem_singleton.mp halt) rfl he
        · cases halt
      · cases halt
    · cases halt
  · change alt ∈ fuseRol D e at halt
    unfold fuseRol at halt
    split at halt
    · unfold fuseRolAt at halt
      split at halt
      · rename_i hn
        have he := lwNode?_quiet M hn
        split at halt
        · split at halt
          · exact hq (List.mem_singleton.mp halt) rfl he
          · split at halt
            · exact hq (List.mem_singleton.mp halt) rfl he
            · cases halt
        · cases halt
      · cases halt
    · cases halt

/-- Extraction at the fusion rule set returns one binding with the events of the
    expression. -/
theorem vecFusions_choose (S : Tbl jasminVec × Defs jasminVec) {s : JasminTy}
    (e : Expr jasminVec Δ s) :
    ∃ e2, choose vecFusions S e = .one e2 ∧
      ∀ V, ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e2 V
        = ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e V := by
  have hred : ∀ e' : Expr jasminVec Δ s, reduceOne vecFusions.pure S.1 e' = .one e' :=
    fun e' => rfl
  refine pick_prop vecFusions _
    (fun a => ∃ e2, a = .one e2 ∧
      ∀ V, ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e2 V
        = ComLevelCheck.Expr.ctLeak (jasminVecLeak M) e V)
    _ _ ⟨e, hred e, fun _ => rfl⟩ ?_
  intro a ha _
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨e2, rfl, h2⟩ := vecFusions_alts M S.2 e a' ha'
  exact ⟨e2, hred e2, h2⟩

/-- **The fusion pass emits the events of its input**: the output runs, at every fuel and
    valuation, to the results and the events of the input. -/
theorem fuseVec_leakRun (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List JasminTy}
    (p : NFProg jasminVec Γ ts) (V : Valuation Γ) :
    jasminVecLeakRun M fuel (fuseVec p) V = jasminVecLeakRun M fuel p V := by
  show NFProg.leakRun (jasminVecLeak M) fuel (nfGo vecFusions (Ctxt.Hom.id Γ) (∅, ∅) p) V = _
  rw [nfGo_leakRun vecFusions (jasminVecLeak M) (fun S _ _ e => vecFusions_choose M S e) fuel
    _ _ p V (stSound_empty V), Ctxt.Valuation.comap_id]

end Events

/-! ## 7. The Keccak χ step -/

section Chi

/-- The variable at the depth of a variable is that variable. -/
theorem varOfDepth?_self {d : Dialect.{0, 0}} [DecidableEq d.Ty] :
    ∀ {Δ : Ctxt d} {s : d.Ty} (v : Var Δ s),
      AegraphGeneric.varOfDepth? Δ s (varDepth v) = some v
  | _ :: _, _, .here => by simp [AegraphGeneric.varOfDepth?, varDepth]
  | _ :: _, _, .there v => by
      simp [AegraphGeneric.varOfDepth?, varDepth, varOfDepth?_self v]

/-- The variable at the level of a variable is that variable. -/
theorem varOfLvl?_self {d : Dialect.{0, 0}} [DecidableEq d.Ty] {Δ : Ctxt d} {s : d.Ty}
    (v : Var Δ s) : varOfLvl? Δ s (varLvl v) = some v := by
  have := varDepth_lt v
  unfold varOfLvl? varLvl
  rw [ite_eq_left (by omega),
    show Δ.length - 1 - (Δ.length - 1 - varDepth v) = varDepth v by omega]
  exact varOfDepth?_self v

variable {Δ : Ctxt jasminVec}

/-- **The three-input fusion on the χ step.** For `a xor n` with `n` bound to `andn b c`
    and `a` bound to no recorded node, the rule offers the one alternative `tern` with the
    table of `p ^^ (!q && r)` on `a`, `b`, `c`. -/
theorem fuseTern_chi (D : Defs jasminVec) (a n b c : Var Δ VReg)
    (hn : D[varLvl n]? = some (.inr (.lw .zmm 64 (.bin .andn)), [varLvl b, varLvl c]))
    (ha : D[varLvl a]? = none) :
    fuseTern D (lwE 64 (.bin .xor) a n)
      = [Alt.one (ternE 64 (ternTable fun p q r => p ^^ (!q && r)) a b c)] := by
  have h1 : logicNode? Δ ((lwE 64 (.bin .xor) a n).op,
      AegraphGeneric.argLvls (lwE 64 (.bin .xor) a n).args)
        = some (64, (fun x y => x ^^ y), a, n) := by
    have hl : AegraphGeneric.argLvls (lwE 64 (.bin .xor) a n).args = [varLvl a, varLvl n] :=
      rfl
    show logicNode? Δ (.inr (.lw .zmm 64 (.bin .xor)),
      AegraphGeneric.argLvls (lwE 64 (.bin .xor) a n).args) = _
    rw [hl]
    simp [logicNode?, lwNode?, varOfLvl?_self, bitFn]
  have h2 : logicNode? Δ (.inr (.lw .zmm 64 (.bin .andn)), [varLvl b, varLvl c])
      = some (64, (fun x y => !x && y), b, c) := by
    simp [logicNode?, lwNode?, varOfLvl?_self, bitFn]
  show fuseTernAt D (lwE 64 (.bin .xor) a n) = _
  unfold fuseTernAt
  rw [h1]
  simp only [ha, hn, Option.bind_none, Option.bind_some, h2, List.nil_append]

end Chi

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecPeephole
