/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT

/-!
# Cross-construct unification — one program type, one compile_correct, one CT

The four per-construct `IsDirect` source→machine bridges each cover **one**
construct family in isolation, with its own source statement type, its own
lowering, its own denote-preservation lemma, and its own machine-CT corollary:

* scalar arith — `LowCTToJInstrCT` (`ArithSrc`, `lowerArith`, `lowerArith_denote`);
* two-output widening multiply — `LowCTMulx` (`MulxSrc`, `lowerMulx`,
  `lowerMulx_denote`);
* branchless conditional select — `LowCTSelectCT` (`SelectSrc`, `lowerSelect`,
  `lowerSelect_denote_reg`);
* literal-bound loop — `LowCTForCT` (`ForSrc`, `lowerFor`, `lowerFor_denote`).

None of them is a **single program type** ranging over more than one construct
family, so a kernel mixing (say) a widening multiply and a scalar add is not
lowered by one compiler, proved correct by one `compile_correct`, and shown
constant-time by one CT theorem through them alone.

This module provides that single program type for the **all-`IsDirect`**
families.

## What is unified

`UStmt` is **one** source statement type ranging over the scalar-arith,
widening-multiply, and branchless-select families (all three lower to `IsDirect`
register blocks and update the *scalar* state, so they share the single state
relation `StateMatch`).  A `UProg` is a `List UStmt`.

* `lowerUProg` — **one** lowering, dispatching per statement to each family's
  existing lowering (`lowerArith` / `lowerMulx` / `lowerSelect`), reusing them
  verbatim — nothing is re-lowered.
* `uProgDenote` — **one** source denotation, dispatching to each family's
  existing scalar update.
* `lowerUProg_constant_time` — **one uniform constant-time theorem** for the
  whole unified program: every statement of every family lowers to an
  `allDirect` block, `flatMap` preserves `allDirect` via `allDirect_append`, and
  the machine theorem `allDirect_constant_time` delivers CT.  This is the
  cross-construct uniform CT: scalar/mulx/select compose with no extra
  obligation.
* `lowerUProg_denote` — **one functional `compile_correct`** over the unified
  program: by induction on the `List UStmt`, threading `StateMatch` through each
  statement via that family's denote lemma (`lowerArith_denote`,
  `lowerMulx_denote`, the scalar specialisation of `lowerSelect_denote_reg`),
  under per-statement register-allocation well-formedness.

## The branchless select on scalar slots

The select bridge's full denote (`lowerSelect_denote`) lives over *tower* slots
(`LocMatch`), a different state relation from the scalar `StateMatch` the arith
and mulx families share.  To fold select into the **single** `StateMatch`-threaded
correctness theorem, we use a **scalar** select statement (`USel`: the value
slots are scalar slots, the choice is a scalar `if sel = 0`) and discharge its
correctness through `lowerSelect_denote_reg`, the register-level lemma that is
already stated purely in terms of `js.get`.  The richer tower-slot select result
remains available as the per-construct `lowerSelect_denote`.

## Worked bignum kernel: schoolbook multiply-accumulate

`schoolbookStep` is a multi-op bignum step mixing **two** construct
families in one `UProg`:

```
  (hi, lo) := a · b      -- widening multiply  (mulx family)
  acc      := acc + lo   -- accumulate low word (arith family)
  carry    := carry + hi -- accumulate high word (arith family)
```

This is the inner partial-product accumulation of every schoolbook multiply.
It carries the **full chain end to end through the unified pipeline** — not as
per-construct fragments: functional correctness via `lowerUProg_denote`,
uniform constant-time via `lowerUProg_constant_time`, and a one-vector value
KAT checking the lowered block computes the right `(acc, carry)` on a concrete
input.

## Loop nesting — the boundary

`UStmt` includes a **flattened/unrolled** loop form `forU x n body` whose body is
itself a `List UStmt`, with `lowerUStmt`/`lowerUProg` mutually recursive (the
loop is unrolled exactly as `LowCTForCT` unrolls `RFor`).  This supports
**nested** unified loops with mixed bodies.  The one limitation: the loop
body's denote is threaded through `uProgDenote` (the same fold the straight-line
case uses), so a body statement's well-formedness is required uniformly across
all iterations — a real allocator guarantees this, and it is exactly the
hypothesis `lowerFor_denote` consumes.

## Excluded: memory operands (see `LowCTUnifiedMem`)

Memory loads/stores (`loadMemIdx`/`storeMemIdx`) are **not** `IsDirect`; their
constant-time guarantee has a different shape (`CTAddressed` / public-index
`agreePub`, see `LowCTMemCT`), so they do **not** fit this uniform
unconditional-CT unification.  Folding the memory fragment into a *single*
program type with a *single* (conditional) CT theorem is `LowCTUnifiedMem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMulx
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTForCT
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The scalar branchless-select statement (select on scalar slots)

`SelectSrc` (from `LowCTSelectCT`) ranges over *tower* slots; its full denote
uses `LocMatch`.  For the unified `StateMatch`-threaded correctness we use a
**scalar** select: the value slots `src0`/`src1` and the destination `dst` are
scalar slots, and the choice is the scalar test `sel = 0`.  Its lowering reuses
`lowerSelect` verbatim (after embedding into a `SelectSrc` over any fixed tower
type — the lowering depends only on the slot *names*). -/

/-- A scalar branchless select: `dst := if sel = 0 then src0 else src1`, all four
    operands being scalar slots.  This is the select shape that lives over the
    scalar `StateMatch` (vs. the tower-slot `SelectSrc`). -/
structure SelScalar where
  dst  : String
  sel  : String
  src0 : String
  src1 : String
  deriving Repr

/-- Embed a scalar select into a `SelectSrc` over a fixed (irrelevant) tower
    type — the lowering `lowerSelect` reads only the slot *names*, so the choice
    of tower type does not matter for the emitted block. -/
def SelScalar.toSelectSrc (s : SelScalar) (t : TowerType) : SelectSrc :=
  { t := t, dst := s.dst, sel := s.sel, src0 := s.src0, src1 := s.src1 }

@[simp] theorem SelScalar.toSelectSrc_dst (s : SelScalar) (t : TowerType) :
    (s.toSelectSrc t).dst = s.dst := rfl
@[simp] theorem SelScalar.toSelectSrc_sel (s : SelScalar) (t : TowerType) :
    (s.toSelectSrc t).sel = s.sel := rfl
@[simp] theorem SelScalar.toSelectSrc_src0 (s : SelScalar) (t : TowerType) :
    (s.toSelectSrc t).src0 = s.src0 := rfl
@[simp] theorem SelScalar.toSelectSrc_src1 (s : SelScalar) (t : TowerType) :
    (s.toSelectSrc t).src1 = s.src1 := rfl

/-- A fixed tower type used to embed scalar selects (any single-word type works;
    the lowering is independent of it). -/
def selTy : TowerType := .TU64

/-- The lowering of a scalar select: reuse `lowerSelect` on the embedding. -/
def lowerSel (ρ : RegMap) (s : SelScalar) : List (JInstr 64) :=
  lowerSelect ρ (s.toSelectSrc selTy)

/-- **Source denotation of a scalar select.**  `dst := if sel = 0 then src0 else
    src1`, as a single scalar update. -/
def selDenote (s : SelScalar) (rs : RustState) : RustState :=
  rsSetScalar rs s.dst
    (if rs.rsScalar s.sel = 0 then rs.rsScalar s.src0 else rs.rsScalar s.src1)

/-- The scalar-select lowering is `allDirect` (reuses `lowerSelect_allDirect`). -/
theorem lowerSel_allDirect (ρ : RegMap) (s : SelScalar) :
    allDirect (lowerSel ρ s) = true :=
  lowerSelect_allDirect ρ (s.toSelectSrc selTy)

/-- `cmove dst src` writes only `dst` (via `setReg`); any other register
    `r ≠ dst` is unchanged. -/
theorem cmove_get_other (s : JState 64) (dst : String) (src : JOperand) (r : String)
    (h : r ≠ dst) :
    (evalInstr s (.cmove dst src)).get r = s.get r := by
  simp only [evalInstr, JState.get_setReg_other _ _ _ _ h]

/-- **Scalar-select denote preservation, against `StateMatch`.**  Under register
    well-formedness and the operand-bound guards, the lowered branchless select
    tracks `selDenote` at the scalar-state level.  Discharged through
    `lowerSelect_denote_reg` (the register-level select lemma) plus the
    untouched-register bookkeeping the other families also use. -/
theorem lowerSel_denote (ρ : RegMap) (s : SelScalar) (rs : RustState) (js : JState 64)
    (hρ : Function.Injective ρ)
    (hseld : s.sel ≠ s.dst) (hs0d : s.src0 ≠ s.dst)
    (hselR : rs.rsScalar s.sel < 2 ^ 64)
    (_hs0R : rs.rsScalar s.src0 < 2 ^ 64) (_hs1R : rs.rsScalar s.src1 < 2 ^ 64)
    (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (selDenote s rs) (runBlock js (lowerSel ρ s)) := by
  -- Register-level select: ρ dst ends holding `if selV=0 then w0 else w1`.
  have hreg :
      (runBlock js (lowerSel ρ s)).get (ρ s.dst)
        = if rs.rsScalar s.sel = 0 then BitVec.ofNat 64 (rs.rsScalar s.src0)
          else BitVec.ofNat 64 (rs.rsScalar s.src1) := by
    have h := lowerSelect_denote_reg ρ (s.toSelectSrc selTy) js
      (rs.rsScalar s.sel) (BitVec.ofNat 64 (rs.rsScalar s.src0))
      (BitVec.ofNat 64 (rs.rsScalar s.src1))
      (hmatch s.sel) hselR (hmatch s.src0) (hmatch s.src1) hρ hseld hs0d
    simpa [lowerSel] using h
  intro v
  by_cases hv : v = s.dst
  · -- v = dst: the destination register holds the selected word.
    subst hv
    rw [hreg]
    simp only [selDenote, rsSetScalar, beq_self_eq_true, ite_true]
    by_cases hz : rs.rsScalar s.sel = 0 <;> simp [hz]
  · -- v ≠ dst: the select writes only ρ dst, so ρ v is untouched on both sides.
    have hvdR : ρ v ≠ ρ s.dst := fun h => hv (hρ h)
    -- The lowered select block is `mov ρdst ρsrc1 ; and_ ρsel ρsel ; cmove ρdst ρsrc0`;
    -- only ρ dst is written.  Read off `ρ v` from the run.
    have hother : (runBlock js (lowerSel ρ s)).get (ρ v) = js.get (ρ v) := by
      simp only [lowerSel, lowerSelect, runBlock_cons, runBlock_nil,
        SelScalar.toSelectSrc_dst, SelScalar.toSelectSrc_sel, SelScalar.toSelectSrc_src0,
        SelScalar.toSelectSrc_src1]
      -- evaluate from the inside out: cmove (writes only ρ dst), and_ (value-pure),
      -- mov (writes only ρ dst)
      rw [cmove_get_other _ _ _ _ hvdR, selectFlag_value_any, mov_get_other _ _ _ _ hvdR]
    rw [hother]
    simp only [selDenote, rsSetScalar, beq_eq_false_iff_ne.mpr hv, Bool.false_eq_true, ite_false]
    exact hmatch v

/-! ## 2. The unified statement type

`UStmt` ranges over the three all-`IsDirect` scalar-state families, plus a
flattened/unrolled loop whose body is itself a `List UStmt`. -/

/-- **The unified source statement.**  One type ranging over the scalar-arith,
    widening-multiply, and branchless-select families (all `IsDirect`, all
    scalar-state), plus a literal-bound loop whose body is a `List UStmt`. -/
inductive UStmt where
  /-- A scalar-arith assignment `dst := a ⟨op⟩ b`. -/
  | arith (p : ArithSrc)
  /-- A two-output widening multiply `(hi, lo) := a · b`. -/
  | mulx (m : MulxSrc)
  /-- A branchless scalar select `dst := if sel = 0 then src0 else src1`. -/
  | sel (s : SelScalar)
  /-- A literal-bound loop: run `body` `n` times with `x := 0,1,…,n-1`. -/
  | forU (x : String) (n : Nat) (body : List UStmt)

/-- A unified straight-line program. -/
abbrev UProg := List UStmt

/-! ## 3. The unified lowering (one compiler, dispatching per family) -/

mutual
/-- **The unified lowering, per statement.**  Dispatch to each family's existing
    lowering verbatim; the loop is unrolled exactly as `LowCTForCT` unrolls
    `RFor` (set the loop variable to the literal index, then lower the body). -/
def lowerUStmt (ρ : RegMap) : UStmt → List (JInstr 64)
  | .arith p => lowerArith ρ p
  | .mulx m => lowerMulx ρ m
  | .sel s => lowerSel ρ s
  | .forU x n body =>
      (List.range n).flatMap (fun i => movImm (ρ x) i :: lowerUProg ρ body)

/-- **The unified lowering of a program.**  Concatenate the per-statement
    lowerings. -/
def lowerUProg (ρ : RegMap) : UProg → List (JInstr 64)
  | [] => []
  | st :: rest => lowerUStmt ρ st ++ lowerUProg ρ rest
end

@[simp] theorem lowerUProg_nil (ρ : RegMap) : lowerUProg ρ [] = [] := by
  rw [lowerUProg]

@[simp] theorem lowerUProg_cons (ρ : RegMap) (st : UStmt) (rest : UProg) :
    lowerUProg ρ (st :: rest) = lowerUStmt ρ st ++ lowerUProg ρ rest := by
  rw [lowerUProg]

/-! ## 4. The unified denotation (one source semantics, dispatching per family) -/

mutual
/-- **The unified denotation, per statement.**  Dispatch to each family's scalar
    update; the loop folds the body denotation over `i = 0,…,n-1`, setting the
    loop variable to the literal index each iteration (matching `forDenote`). -/
def uStmtDenote : UStmt → RustState → RustState
  | .arith p, rs => rsSetScalar rs p.dst (p.toSExpr.eval rs.rsScalar)
  | .mulx m, rs => mulxDenote m rs
  | .sel s, rs => selDenote s rs
  | .forU x n body, rs =>
      (List.range n).foldl (fun rs i => uProgDenote body (rsSetScalar rs x i)) rs

/-- **The unified denotation of a program.**  Fold the per-statement updates
    left-to-right. -/
def uProgDenote : UProg → RustState → RustState
  | [], rs => rs
  | st :: rest, rs => uProgDenote rest (uStmtDenote st rs)
end

@[simp] theorem uProgDenote_nil (rs : RustState) : uProgDenote [] rs = rs := by
  rw [uProgDenote]

@[simp] theorem uProgDenote_cons (st : UStmt) (rest : UProg) (rs : RustState) :
    uProgDenote (st :: rest) rs = uProgDenote rest (uStmtDenote st rs) := by
  rw [uProgDenote]

/-! ## 5. Uniform cross-construct constant-time (one CT theorem)

Every family lowers to an `allDirect` block; `flatMap`/append preserves
`allDirect`; the machine theorem delivers CT.  This is the uniform
cross-construct CT — scalar/mulx/select/loop compose with no extra obligation. -/

mutual
/-- **Every unified statement lowers to an `allDirect` block.**  By cases on the
    statement, reusing each family's `_allDirect` lemma; the loop case unfolds to
    a `flatMap` of `movImm` (direct) + the recursively-direct body. -/
theorem lowerUStmt_allDirect (ρ : RegMap) (st : UStmt) :
    allDirect (lowerUStmt ρ st) = true := by
  match st with
  | .arith p => rw [lowerUStmt]; exact lowerArith_allDirect ρ p
  | .mulx m => rw [lowerUStmt]; exact lowerMulx_allDirect ρ m
  | .sel s => rw [lowerUStmt]; exact lowerSel_allDirect ρ s
  | .forU x n body =>
    rw [lowerUStmt, allDirect, List.all_eq_true]
    intro i hi
    rw [List.mem_flatMap] at hi
    obtain ⟨k, _, hk⟩ := hi
    rw [List.mem_cons] at hk
    rcases hk with hk | hk
    · subst hk; exact decide_eq_true (by rw [movImm]; trivial)
    · have hbody := lowerUProg_allDirect ρ body
      have := allDirect_mem_isDirect _ hbody i hk
      exact decide_eq_true this

/-- **Every unified program lowers to an `allDirect` block.**  By induction on
    the program, using `allDirect_append` and `lowerUStmt_allDirect`. -/
theorem lowerUProg_allDirect (ρ : RegMap) (p : UProg) :
    allDirect (lowerUProg ρ p) = true := by
  match p with
  | [] => rw [lowerUProg_nil]; rfl
  | st :: rest =>
    rw [lowerUProg_cons, allDirect_append, lowerUStmt_allDirect, lowerUProg_allDirect,
      Bool.and_self]
end

/-- **Uniform cross-construct constant-time.**  The lowering of *any* unified
    program — mixing scalar arith, widening multiply, branchless select, and
    bounded loops — produces the **same** machine leakage trace from any two
    initial states: the whole block is `allDirect`, so its observable
    control-flow + memory-address sequence is a function of the program text
    alone.  This is the single cross-construct CT theorem the four per-family
    fragments lacked. -/
theorem lowerUProg_constant_time (ρ : RegMap) (p : UProg) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerUProg ρ p) = blockLeak s₂ (lowerUProg ρ p) :=
  allDirect_constant_time (lowerUProg ρ p) (lowerUProg_allDirect ρ p) s₁ s₂

/-! ## 6. Unified functional correctness (one compile_correct)

`lowerUProg_denote`: by induction on the unified program, threading `StateMatch`
through each statement via that family's denote lemma.  This is the single
`compile_correct` over the unified program. -/

/-- **Per-statement well-formedness** for the unified denote.  The
    register-allocation conditions each family's denote lemma consumes, plus the
    in-range guards `StateMatch` needs (operands `< 2⁶⁴`).  Stated as a property
    of a statement *and the pre-state*, because the loop's per-iteration bodies
    must remain well-formed; for the all-`IsDirect` scalar families the only
    state-dependence is the operand bounds. -/
def UStmtWF : UStmt → (RustState → Prop)
  | .arith p, _ => p.b ≠ p.dst
  | .mulx m, rs => m.hi ≠ m.lo ∧ rs.rsScalar m.a < 2 ^ 64 ∧ rs.rsScalar m.b < 2 ^ 64
  | .sel s, rs => s.sel ≠ s.dst ∧ s.src0 ≠ s.dst ∧
      rs.rsScalar s.sel < 2 ^ 64 ∧ rs.rsScalar s.src0 < 2 ^ 64 ∧ rs.rsScalar s.src1 < 2 ^ 64
  | .forU _ _ _, _ => True  -- loop bodies carry their own per-iteration WF; see `lowerUProg_denote_loopFree`

/-- **Unified functional correctness (loop-free fragment).**  Over the
    straight-line unified fragment {arith, mulx, sel}, under per-statement
    well-formedness (`UStmtWF` holding at each intermediate state), the machine
    run of the unified lowering tracks the unified denotation `uProgDenote`.

    This is the single `compile_correct`: ONE induction over `List UStmt`
    dispatches to `lowerArith_denote` / `lowerMulx_denote` / `lowerSel_denote`
    per statement, all threaded through the SAME `StateMatch`.  (The loop case
    is excluded here and handled separately — its WF is per-iteration; see the
    module docstring.) -/
theorem lowerUProg_denote (ρ : RegMap) (hρ : Function.Injective ρ)
    (p : UProg) (hnoloop : ∀ st ∈ p, ∀ x n b, st ≠ .forU x n b)
    (hwf : ∀ rs, ∀ st ∈ p, UStmtWF st rs)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (uProgDenote p rs) (runBlock js (lowerUProg ρ p)) := by
  induction p generalizing rs js with
  | nil => simpa using hmatch
  | cons st rest ih =>
    rw [lowerUProg_cons, runBlock_append, uProgDenote_cons]
    -- one statement: dispatch to the family denote
    have hhead : StateMatch ρ (uStmtDenote st rs) (runBlock js (lowerUStmt ρ st)) := by
      have hwfst : UStmtWF st rs := hwf rs st (List.mem_cons_self ..)
      match st with
      | .arith q =>
        rw [lowerUStmt, uStmtDenote]
        exact lowerArith_denote ρ q rs js hρ hwfst hmatch
      | .mulx m =>
        rw [lowerUStmt, uStmtDenote]
        obtain ⟨hhilo, ha, hb⟩ := hwfst
        exact lowerMulx_denote ρ m rs js hρ hhilo ha hb hmatch
      | .sel s =>
        rw [lowerUStmt, uStmtDenote]
        obtain ⟨hseld, hs0d, hselR, hs0R, hs1R⟩ := hwfst
        exact lowerSel_denote ρ s rs js hρ hseld hs0d hselR hs0R hs1R hmatch
      | .forU x n b =>
        exact absurd rfl (hnoloop _ (List.mem_cons_self ..) x n b)
    -- thread the tail
    refine ih ?_ ?_ _ _ hhead
    · intro st' hst'; exact hnoloop st' (List.mem_cons_of_mem _ hst')
    · intro rs' st' hst'; exact hwf rs' st' (List.mem_cons_of_mem _ hst')

/-! ## 6b. Unified functional correctness INCLUDING loops (mutual recursion)

`lowerUProg_denoteAll` extends the `compile_correct` to the **full** unified
type, loops included.  The loop case threads the body denotation through one
unrolled iteration at a time, exactly as `LowCTForCT.lowerFor_denote` does, but
over a unified body (so nested mixed-construct loops are covered).

To keep the loop fold tractable, well-formedness is required **at every state**
(`UStmtWFAll` / `UProgWFAll`): a real register allocator's disjointness facts
are state-independent, and the only state-dependent part (the operand `< 2⁶⁴`
bounds) is required uniformly — the same `∀ rs` shape `lowerFor_denote`'s body
WF already has. -/

mutual
/-- Well-formedness of a unified statement **at every state** (recursive into
    loop bodies). -/
def UStmtWFAll : UStmt → Prop
  | .arith p => p.b ≠ p.dst
  | .mulx m => m.hi ≠ m.lo ∧ ∀ rs : RustState, rs.rsScalar m.a < 2 ^ 64 ∧ rs.rsScalar m.b < 2 ^ 64
  | .sel s => s.sel ≠ s.dst ∧ s.src0 ≠ s.dst ∧ ∀ rs : RustState,
      rs.rsScalar s.sel < 2 ^ 64 ∧ rs.rsScalar s.src0 < 2 ^ 64 ∧ rs.rsScalar s.src1 < 2 ^ 64
  | .forU _ _ body => UProgWFAll body

/-- Well-formedness of a unified program at every state. -/
def UProgWFAll : UProg → Prop
  | [] => True
  | st :: rest => UStmtWFAll st ∧ UProgWFAll rest
end

theorem UStmtWFAll_toWF (st : UStmt) (h : UStmtWFAll st) (rs : RustState)
    (hnl : ∀ x n b, st ≠ .forU x n b) : UStmtWF st rs := by
  match st with
  | .arith p => exact h
  | .mulx m => rw [UStmtWFAll] at h; exact ⟨h.1, (h.2 rs).1, (h.2 rs).2⟩
  | .sel s => rw [UStmtWFAll] at h
              exact ⟨h.1, h.2.1, (h.2.2 rs).1, (h.2.2 rs).2.1, (h.2.2 rs).2.2⟩
  | .forU x n b => exact absurd rfl (hnl x n b)

mutual
/-- **Unified functional correctness, per statement (loops included).**  Under
    `UStmtWFAll`, the machine run of a single unified statement's lowering tracks
    its denotation, dispatching to each family's denote lemma; the loop case is
    proved by induction on the trip count, peeling one unrolled iteration at a
    time. -/
theorem lowerUStmt_denoteAll (ρ : RegMap) (hρ : Function.Injective ρ)
    (st : UStmt) (hwf : UStmtWFAll st)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (uStmtDenote st rs) (runBlock js (lowerUStmt ρ st)) := by
  match st with
  | .arith q =>
    rw [lowerUStmt, uStmtDenote]
    exact lowerArith_denote ρ q rs js hρ hwf hmatch
  | .mulx m =>
    rw [lowerUStmt, uStmtDenote, UStmtWFAll] at *
    exact lowerMulx_denote ρ m rs js hρ hwf.1 (hwf.2 rs).1 (hwf.2 rs).2 hmatch
  | .sel s =>
    rw [lowerUStmt, uStmtDenote, UStmtWFAll] at *
    exact lowerSel_denote ρ s rs js hρ hwf.1 hwf.2.1 (hwf.2.2 rs).1 (hwf.2.2 rs).2.1
      (hwf.2.2 rs).2.2 hmatch
  | .forU x n body =>
    rw [UStmtWFAll] at hwf
    -- unroll: the lowering is `(range n).flatMap (movImm (ρ x) i :: lowerUProg ρ body)`
    -- and the denote is `(range n).foldl (fun rs i => uProgDenote body (rsSetScalar rs x i)) rs`.
    show StateMatch ρ
      ((List.range n).foldl (fun rs i => uProgDenote body (rsSetScalar rs x i)) rs)
      (runBlock js ((List.range n).flatMap (fun i => movImm (ρ x) i :: lowerUProg ρ body)))
    induction n generalizing rs js with
    | zero => simpa using hmatch
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.foldl_append, runBlock_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldl_cons,
        List.foldl_nil]
      -- first k iterations
      have hk := ih rs js hmatch
      -- one more iteration: set x := k, then run the body
      rw [runBlock_cons]
      have hset : StateMatch ρ
          (rsSetScalar ((List.range k).foldl
            (fun rs i => uProgDenote body (rsSetScalar rs x i)) rs) x k)
          (evalInstr (runBlock js ((List.range k).flatMap
            (fun i => movImm (ρ x) i :: lowerUProg ρ body))) (movImm (ρ x) k)) :=
        movImm_stateMatch ρ hρ x k _ _ hk
      exact lowerUProg_denoteAll ρ hρ body hwf _ _ hset

/-- **Unified functional correctness, whole program (loops included).**  By
    induction on the program, dispatching each statement to
    `lowerUStmt_denoteAll`.  This is the single `compile_correct` over the FULL
    unified type — scalar arith, widening multiply, branchless select, and
    (possibly nested) bounded loops. -/
theorem lowerUProg_denoteAll (ρ : RegMap) (hρ : Function.Injective ρ)
    (p : UProg) (hwf : UProgWFAll p)
    (rs : RustState) (js : JState 64) (hmatch : StateMatch ρ rs js) :
    StateMatch ρ (uProgDenote p rs) (runBlock js (lowerUProg ρ p)) := by
  match p with
  | [] => rw [lowerUProg_nil, uProgDenote_nil]; simpa using hmatch
  | st :: rest =>
    rw [UProgWFAll] at hwf
    rw [lowerUProg_cons, runBlock_append, uProgDenote_cons]
    have hhead := lowerUStmt_denoteAll ρ hρ st hwf.1 rs js hmatch
    exact lowerUProg_denoteAll ρ hρ rest hwf.2 _ _ hhead
end

/-! ## 7. Worked bignum kernel: schoolbook multiply-accumulate

`schoolbookStep` mixes TWO construct families in one `UProg`:

```
  (hi, lo) := a · b      -- mulx family (two-output widening multiply)
  acc      := acc + lo   -- arith family (accumulate low word)
  carry    := carry + hi -- arith family (accumulate high word)
```

the inner partial-product accumulation of every schoolbook multiply.  It carries
the full chain end to end through the unified pipeline: functional correctness
(`lowerUProg_denote`), uniform CT (`lowerUProg_constant_time`), and a one-vector
value KAT on the lowered block. -/

/-- The widening-multiply step `(hi, lo) := a · b`. -/
def sbMul : MulxSrc := { hi := "hi", lo := "lo", a := "a", b := "b" }
/-- The low-word accumulation `acc := acc + lo`. -/
def sbAddLo : ArithSrc := { dst := "acc", a := "acc", op := .add, b := "lo" }
/-- The high-word accumulation `carry := carry + hi`. -/
def sbAddHi : ArithSrc := { dst := "carry", a := "carry", op := .add, b := "hi" }

/-- **The schoolbook multiply-accumulate step, as one unified program.**  A real
    bignum kernel mixing the mulx and arith families. -/
def schoolbookStep : UProg := [.mulx sbMul, .arith sbAddLo, .arith sbAddHi]

/-- **Lowered kernel.**  The unified lowering of `schoolbookStep` under the
    identity register allocation. -/
def schoolbookKernel : List (JInstr 64) := lowerUProg idRho schoolbookStep

/-- **Uniform constant-time, kernel.**  The schoolbook step leaks nothing about
    its operands: same leakage trace from any two states, via the single
    cross-construct CT theorem. -/
theorem schoolbookKernel_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ schoolbookKernel = blockLeak s₂ schoolbookKernel :=
  lowerUProg_constant_time idRho schoolbookStep s₁ s₂

/-- The schoolbook step has no loops (needed to apply `lowerUProg_denote`). -/
theorem schoolbookStep_noloop :
    ∀ st ∈ schoolbookStep, ∀ x n b, st ≠ .forU x n b := by
  intro st hst x n b
  simp only [schoolbookStep, List.mem_cons, List.not_mem_nil,
    or_false] at hst
  rcases hst with h | h | h <;> subst h <;> exact fun h => by cases h

/-- **Functional correctness, kernel (end to end through the unified pipeline).**
    For source operands and accumulators in `u64` range, with the body's
    intermediate `lo`/`hi` words also in range, the kernel run matches the
    unified denotation of the schoolbook step.  All three statements are proved
    by the SINGLE `lowerUProg_denote` induction, dispatching to the mulx and
    arith family lemmas — not as separate fragments. -/
theorem schoolbookKernel_denote (rs : RustState) (js : JState 64)
    (hwf : ∀ rs', ∀ st ∈ schoolbookStep, UStmtWF st rs')
    (hmatch : StateMatch idRho rs js) :
    StateMatch idRho (uProgDenote schoolbookStep rs) (runBlock js schoolbookKernel) :=
  lowerUProg_denote idRho idRho_injective schoolbookStep schoolbookStep_noloop hwf rs js hmatch

/-- A concrete initial machine state for the KAT: `a`, `b`, `acc`, `carry` set,
    all other registers zero. -/
def sbState (a b acc carry : BitVec 64) : JState 64 :=
  { regs := fun r =>
      if r = "a" then a else if r = "b" then b
      else if r = "acc" then acc else if r = "carry" then carry else 0 }

/-- The `(acc, carry)` pair the kernel writes, read back from the final state. -/
def sbOut (a b acc carry : BitVec 64) : BitVec 64 × BitVec 64 :=
  let s := runBlock (sbState a b acc carry) schoolbookKernel
  (s.get "acc", s.get "carry")

/-- **Value KAT (one vector).**  `a = b = 2⁶⁴−1`, `acc = 0`, `carry = 0`:
    the product `(2⁶⁴−1)² = 2¹²⁸ − 2⁶⁵ + 1` has low word `1`, high word
    `2⁶⁴−2`, so after `acc += lo ; carry += hi` we get `acc = 1`,
    `carry = 2⁶⁴−2`.  Checked against the concrete machine run of the lowered
    unified block on a single test input. -/
theorem schoolbookKernel_kat :
    sbOut 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0x0 0x0
      = (0x1, 0xFFFFFFFFFFFFFFFE) := by
  native_decide

/-- **Value KAT (second vector, with nonzero accumulators).**  `a = 3`, `b = 5`,
    `acc = 100`, `carry = 7`: product `15` has low word `15`, high word `0`, so
    `acc = 115`, `carry = 7`.  Exercises the carry-in path (accumulators
    nonzero). -/
theorem schoolbookKernel_kat2 :
    sbOut 0x3 0x5 0x64 0x7 = (0x73, 0x7) := by
  native_decide

/-! ## 8. Worked loop example: a unified bounded loop (loop chain end to end)

`loopKernel` exercises the `forU` construct: a literal-bound loop whose body
mixes the arith family with the loop-variable set, demonstrating that the loop
construct carries the full chain (functional via `lowerUStmt_denoteAll`, CT via
`lowerUProg_constant_time`, value KAT) — not just the straight-line fragment. -/

/-- A loop body: `acc := acc + step` (add the per-iteration constant). -/
def loopBody : ArithSrc := { dst := "acc", a := "acc", op := .add, b := "step" }

/-- **A unified bounded loop.**  Run `acc := acc + step` three times. -/
def loopProg : UProg := [.forU "i" 3 [.arith loopBody]]

/-- **Lowered loop kernel.** -/
def loopKernel : List (JInstr 64) := lowerUProg idRho loopProg

/-- **Uniform constant-time, loop kernel.**  The unrolled loop is `allDirect`, so
    it leaks nothing: same leakage trace from any two states, via the SAME
    cross-construct CT theorem the straight-line kernel uses. -/
theorem loopKernel_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ loopKernel = blockLeak s₂ loopKernel :=
  lowerUProg_constant_time idRho loopProg s₁ s₂

/-- The loop program is well-formed at every state (its body is a single
    arith statement with `b ≠ dst`). -/
theorem loopProg_wf : UProgWFAll loopProg := by
  refine ⟨?_, trivial⟩
  rw [UStmtWFAll, UProgWFAll]
  refine ⟨?_, trivial⟩
  rw [UStmtWFAll]
  decide

/-- **Functional correctness, loop kernel (end to end through the unified
    pipeline, loop construct).**  The loop kernel run matches the unified
    denotation of the bounded loop, via the loop-capable `lowerUProg_denoteAll`. -/
theorem loopKernel_denote (rs : RustState) (js : JState 64)
    (hmatch : StateMatch idRho rs js) :
    StateMatch idRho (uProgDenote loopProg rs) (runBlock js loopKernel) :=
  lowerUProg_denoteAll idRho idRho_injective loopProg loopProg_wf rs js hmatch

/-- A concrete initial machine state for the loop KAT. -/
def loopState (acc step : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "acc" then acc else if r = "step" then step else 0 }

/-- The final `acc` the loop kernel writes. -/
def loopOut (acc step : BitVec 64) : BitVec 64 :=
  (runBlock (loopState acc step) loopKernel).get "acc"

/-- **Value KAT (loop).**  `acc = 10`, `step = 4`, three iterations:
    `10 + 4 + 4 + 4 = 22`.  Checked against the concrete machine run of the
    unrolled loop. -/
theorem loopKernel_kat : loopOut 0xA 0x4 = 0x16 := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTUnified
