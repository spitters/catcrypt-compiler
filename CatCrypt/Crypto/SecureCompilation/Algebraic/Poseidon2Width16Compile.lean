/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
public import CatCrypt.Crypto.Hash.Poseidon2.Width16

/-!
# Width-16 Poseidon2 as a `fieldDialect` program, parameterised

For a parameter record `P : Hash.Poseidon2.Width16.Params`, the permutation is a list
of steps `permSteps P`, each step one `fieldDialect` binding over a builder state of
24 working slots (16 lanes and 8 scratch slots) and `nConst P` constant slots. `run`
turns a step list into a `Com fieldDialect` program; every binding it produces is an
`fAdd`, `fMul`, `fCopy` or `fConst` at the modulus `P.p`, so every program built by
`run` is covered by `GoodW P.p` (`run_covered`).

The schedule is Plonky3's: the round constants and diagonal entries are bound by
`fConst`; an external MDS pre-mix; `halfFullRounds` external rounds;
`partialRounds` internal rounds; `halfFullRounds` external rounds; and sixteen
trailing `fCopy` bindings, one per lane in order, so that the last sixteen bindings
of the program hold the sixteen output lanes. In the external MDS, `2x` and `3x` are
sums. The S-box `x ^ sboxDeg` is the square-and-multiply chain `powSteps`, with
intermediate powers in one scratch slot.

## Main definitions

* `Step`, `run`: single-binding steps and the program they denote.
* `permSteps P`: the permutation schedule.
* `permComAt P i`: the permutation program over the 16 input lanes, returning lane
  `i`.
* `permJasminAt P F i`: its lowering `FieldToJasminWord.lowerK F` through a
  single-word field `F` at the modulus `P.p`.

## Main results

* `run_covered`: every program produced by `run` is `GoodW P.p`-covered.
* `permComAt_lowerK_denote`: the lowered program, run on the encoding of the inputs,
  returns the encoding of lane `i` of the field program's result.
* `permJasminAt_exportFaithful`: for a field whose blocks are in the scalar
  fragment, `permJasminAt P F i` satisfies
  `JasminLsemGeneralFaithful.ComLsemExportFaithful`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField)
open CatCrypt.Crypto.Hash.Poseidon2.Width16 (Params)

variable (P : Params)

/-! ## 1. Slots and the builder state -/

/-- The field type of every lane, scratch slot and constant. -/
abbrev FP : FieldTy := .fp P.p

/-- The input context: the 16 state lanes. -/
abbrev inCtxt : Ctxt fieldDialect := List.replicate 16 (FP P)

/-- The number of constant slots: the external round constants, the internal round
    constants and the diagonal. -/
def nConst : Nat := 32 * P.halfFullRounds + P.partialRounds + 16

/-- The builder state at context `Γ`: the current variable of each of the 24
    working slots (16 lanes, 8 scratch) and of each constant slot. -/
structure BState (Γ : Ctxt fieldDialect) where
  /-- Working slots. -/
  lane : Fin 24 → Ctxt.Var Γ (FP P)
  /-- Constant slots. -/
  const : Fin (nConst P) → Ctxt.Var Γ (FP P)

/-- A step operand: a working slot or a constant slot. -/
inductive Src where
  | lane (i : Fin 24)
  | const (j : Fin (nConst P))

/-- A single-binding step. -/
inductive Step where
  /-- `dst := a + b`. -/
  | add (dst : Fin 24) (a b : Src P)
  /-- `dst := a * b`. -/
  | mul (dst : Fin 24) (a b : Src P)
  /-- `dst := a`, as its own binding. -/
  | copy (dst : Fin 24) (a : Src P)
  /-- Constant slot `j := c`. -/
  | konst (j : Fin (nConst P)) (c : ZMod P.p)

variable {P}

/-- The variable of an operand. -/
def BState.get {Γ : Ctxt fieldDialect} (st : BState P Γ) : Src P → Ctxt.Var Γ (FP P)
  | .lane i => st.lane i
  | .const j => st.const j

/-- The state after a binding: the written slot holds the fresh variable, every
    other variable is shifted past it. -/
def BState.after {Γ : Ctxt fieldDialect} (st : BState P Γ) : Step P → BState P (FP P :: Γ)
  | .add dst _ _ | .mul dst _ _ | .copy dst _ =>
      { lane := fun i => if i = dst then .here else (st.lane i).there
        const := fun j => (st.const j).there }
  | .konst j₀ _ =>
      { lane := fun i => (st.lane i).there
        const := fun j => if j = j₀ then .here else (st.const j).there }

/-- The `fieldDialect` expression of a step. -/
def stepExpr {Γ : Ctxt fieldDialect} (st : BState P Γ) : Step P → Expr fieldDialect Γ (FP P)
  | .add _ a b => ⟨.fAdd P.p, rfl, .cons (st.get a) (.cons (st.get b) .nil)⟩
  | .mul _ a b => ⟨.fMul P.p, rfl, .cons (st.get a) (.cons (st.get b) .nil)⟩
  | .copy _ a => ⟨.fCopy P.p, rfl, .cons (st.get a) .nil⟩
  | .konst _ c => ⟨.fConst P.p c, rfl, .nil⟩

/-- The program of a step list: one binding per step, then the continuation on
    the final state. -/
def run : List (Step P) → {Γ : Ctxt fieldDialect} → BState P Γ →
    ({Γ' : Ctxt fieldDialect} → BState P Γ' → Com fieldDialect Γ' (FP P)) →
    Com fieldDialect Γ (FP P)
  | [], _, st, k => k st
  | s :: ss, _, st, k => .var (stepExpr st s) (run ss (st.after s) k)

theorem stepExpr_good {Γ : Ctxt fieldDialect} (st : BState P Γ) (s : Step P) :
    GoodW P.p (stepExpr st s) := by
  cases s with
  | add => exact Or.inl rfl
  | mul => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | copy => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | konst _ c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))))

/-- **Coverage by construction.** If the continuation produces covered programs,
    so does `run ss`. -/
theorem run_covered (ss : List (Step P)) {Γ : Ctxt fieldDialect} (st : BState P Γ)
    (k : {Γ' : Ctxt fieldDialect} → BState P Γ' → Com fieldDialect Γ' (FP P))
    (hk : ∀ {Γ' : Ctxt fieldDialect} (s : BState P Γ'), CoveredCom (GoodW P.p) (k s)) :
    CoveredCom (GoodW P.p) (run ss st k) := by
  induction ss generalizing Γ with
  | nil => exact hk st
  | cons s ss ih => exact ⟨stepExpr_good st s, ih (st.after s)⟩

/-! ## 2. The schedule -/

/-- Lane slot `i`. -/
def laneSlot (i : Fin 16) : Fin 24 := ⟨i.val, by omega⟩

/-- Scratch slots. -/
def s0 : Fin 24 := ⟨16, by decide⟩
def s1 : Fin 24 := ⟨17, by decide⟩
def s2 : Fin 24 := ⟨18, by decide⟩
def s3 : Fin 24 := ⟨19, by decide⟩
def acc : Fin 24 := ⟨20, by decide⟩
def tmp : Fin 24 := ⟨21, by decide⟩
def tpow : Fin 24 := ⟨22, by decide⟩

variable (P)

/-- Constant slot of the external round constant of round `r`, lane `i`. -/
def cExt (r : Fin (2 * P.halfFullRounds)) (i : Fin 16) : Fin (nConst P) :=
  ⟨r.val * 16 + i.val, by have := r.isLt; unfold nConst; omega⟩

/-- Constant slot of the internal round constant of round `r`. -/
def cInt (r : Fin P.partialRounds) : Fin (nConst P) :=
  ⟨32 * P.halfFullRounds + r.val, by have := r.isLt; unfold nConst; omega⟩

/-- Constant slot of the diagonal entry of lane `i`. -/
def cDiag (i : Fin 16) : Fin (nConst P) :=
  ⟨32 * P.halfFullRounds + P.partialRounds + i.val, by unfold nConst; omega⟩

/-- The value of constant slot `j`. -/
def constVal (j : Fin (nConst P)) : ZMod P.p :=
  if h : j.val < 32 * P.halfFullRounds then
    P.rcExternal ⟨j.val / 16, by omega⟩ ⟨j.val % 16, by omega⟩
  else if h' : j.val < 32 * P.halfFullRounds + P.partialRounds then
    P.rcInternal ⟨j.val - 32 * P.halfFullRounds, by omega⟩
  else
    P.diag ⟨j.val - 32 * P.halfFullRounds - P.partialRounds, by
      have := j.isLt; unfold nConst at this; omega⟩

/-- Bind every constant slot. -/
def constSteps : List (Step P) :=
  (List.finRange (nConst P)).map fun j => .konst j (constVal P j)

/-- `tgt := x ^ n` for `n ≥ 1` by square-and-multiply, the intermediate powers in
    `tpow`. -/
def powSteps (x : Fin 24) (n : Nat) (tgt : Fin 24) : List (Step P) :=
  if n ≤ 1 then [.copy tgt (.lane x)]
  else if n = 2 then [.mul tgt (.lane x) (.lane x)]
  else if n % 2 = 0 then powSteps x (n / 2) tpow ++ [.mul tgt (.lane tpow) (.lane tpow)]
  else powSteps x (n - 1) tpow ++ [.mul tgt (.lane tpow) (.lane x)]
termination_by n
decreasing_by all_goals omega

/-- The S-box on lane `i`, in place. -/
def sboxSteps (i : Fin 16) : List (Step P) :=
  powSteps P (laneSlot i) P.sboxDeg (laneSlot i)

/-- The 4×4 block `circ(2, 3, 1, 1)` on lanes `4b .. 4b+3`, rows staged in
    `s0 .. s3` and copied back. -/
def mat4Steps (b : Fin 4) : List (Step P) :=
  let l0 : Src P := .lane ⟨4 * b.val, by omega⟩
  let l1 : Src P := .lane ⟨4 * b.val + 1, by omega⟩
  let l2 : Src P := .lane ⟨4 * b.val + 2, by omega⟩
  let l3 : Src P := .lane ⟨4 * b.val + 3, by omega⟩
  [ .add acc l0 l0, .add tmp l1 l1, .add tmp (.lane tmp) l1, .add acc (.lane acc) (.lane tmp),
    .add acc (.lane acc) l2, .add s0 (.lane acc) l3,
    .add acc l1 l1, .add tmp l2 l2, .add tmp (.lane tmp) l2, .add acc l0 (.lane acc),
    .add acc (.lane acc) (.lane tmp), .add s1 (.lane acc) l3,
    .add acc l2 l2, .add tmp l3 l3, .add tmp (.lane tmp) l3, .add acc l0 (.lane acc),
    .add acc l1 (.lane acc), .add s2 (.lane acc) (.lane tmp),
    .add acc l0 l0, .add acc (.lane acc) l0, .add tmp l3 l3, .add acc (.lane acc) l1,
    .add acc (.lane acc) l2, .add s3 (.lane acc) (.lane tmp),
    .copy ⟨4 * b.val, by omega⟩ (.lane s0), .copy ⟨4 * b.val + 1, by omega⟩ (.lane s1),
    .copy ⟨4 * b.val + 2, by omega⟩ (.lane s2), .copy ⟨4 * b.val + 3, by omega⟩ (.lane s3) ]

/-- The scratch slot holding column sum `c`. -/
def colSlot (c : Fin 4) : Fin 24 := ⟨16 + c.val, by omega⟩

/-- The column sums into `s0 .. s3`, then lane `i := lane i + sum (i mod 4)`. -/
def colSumSteps : List (Step P) :=
  ((List.finRange 4).flatMap fun c =>
    [ .add acc (.lane (laneSlot ⟨c.val, by omega⟩)) (.lane (laneSlot ⟨c.val + 4, by omega⟩)),
      .add acc (.lane acc) (.lane (laneSlot ⟨c.val + 8, by omega⟩)),
      .add (colSlot c) (.lane acc) (.lane (laneSlot ⟨c.val + 12, by omega⟩)) ]) ++
  (List.finRange 16).map fun i =>
    .add (laneSlot i) (.lane (laneSlot i)) (.lane (colSlot ⟨i.val % 4, by omega⟩))

/-- The external MDS layer. -/
def externalMDSSteps : List (Step P) :=
  (List.finRange 4).flatMap (mat4Steps P) ++ colSumSteps P

/-- External round `r`: round constants, S-box on every lane, external MDS. -/
def externalRoundSteps (r : Fin (2 * P.halfFullRounds)) : List (Step P) :=
  (List.finRange 16).map (fun i => .add (laneSlot i) (.lane (laneSlot i)) (.const (cExt P r i))) ++
  (List.finRange 16).flatMap (sboxSteps P) ++
  externalMDSSteps P

/-- The internal MDS layer: `acc := Σ lanes`, then lane `i := acc + V[i] · lane i`. -/
def internalMDSSteps : List (Step P) :=
  .add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
  ((List.finRange 14).map fun i => .add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩))) ++
  (List.finRange 16).flatMap fun i =>
    [.mul tmp (.const (cDiag P i)) (.lane (laneSlot i)), .add (laneSlot i) (.lane acc) (.lane tmp)]

/-- Internal round `r`: round constant on lane 0, S-box on lane 0, internal MDS. -/
def internalRoundSteps (r : Fin P.partialRounds) : List (Step P) :=
  .add (laneSlot 0) (.lane (laneSlot 0)) (.const (cInt P r)) ::
  sboxSteps P 0 ++ internalMDSSteps P

/-- Copy every lane, in order, as the last sixteen bindings. -/
def outStageSteps : List (Step P) :=
  (List.finRange 16).map fun i => .copy (laneSlot i) (.lane (laneSlot i))

/-- The schedule after the constant bindings. -/
def permRest : List (Step P) :=
  externalMDSSteps P ++
    ((List.finRange P.halfFullRounds).flatMap
      (fun r => externalRoundSteps P ⟨r.val, by omega⟩) ++
    ((List.finRange P.partialRounds).flatMap (internalRoundSteps P) ++
    ((List.finRange P.halfFullRounds).flatMap
      (fun r => externalRoundSteps P ⟨P.halfFullRounds + r.val, by omega⟩) ++
    outStageSteps P)))

/-- The whole schedule. -/
def permSteps : List (Step P) := constSteps P ++ permRest P

/-! ## 3. The program and its lowering -/

/-- Input variable `i` of `List.replicate (m + 1) τ`, with index `0` the most
    recent binding. -/
def inputVar {τ : FieldTy} : (m : Nat) → Nat → @Ctxt.Var fieldDialect (List.replicate (m + 1) τ) τ
  | _, 0 => .here
  | 0, _ => .here
  | m + 1, j + 1 => (inputVar m j).there

/-- The initial state: lane `i` is input `i`; scratch and constant slots point at
    input `0` and are written before they are read. -/
def initState : BState P (inCtxt P) where
  lane := fun i => if i.val < 16 then inputVar 15 i.val else inputVar 15 0
  const := fun _ => inputVar 15 0

/-- **The Poseidon2 permutation over the 16 input lanes, returning lane `i`.** -/
def permComAt (i : Fin 16) : Com fieldDialect (inCtxt P) (FP P) :=
  run (permSteps P) (initState P) (fun st => .ret (st.lane (laneSlot i)))

theorem permComAt_covered (i : Fin 16) : CoveredCom (GoodW P.p) (permComAt P i) :=
  run_covered (permSteps P) (initState P) _ (fun _ => trivial)

/-- The lowered permutation program returning lane `i`. -/
def permJasminAt (F : SingleWordField P.p) (i : Fin 16) :
    Com jasminDialect (mapCtxW (inCtxt P)) (mapTyW (FP P)) :=
  lowerK F (permComAt P i)

/-- **Correctness of the lowered permutation.** On the encoding of any input
    valuation, the lowered program returns the encoding of lane `i` of the field
    program. -/
theorem permComAt_lowerK_denote (F : SingleWordField P.p) (i : Fin 16)
    (V : Ctxt.Valuation (inCtxt P)) :
    (permJasminAt P F i).denote (mapValW F V) = F.enc ((permComAt P i).denote V) :=
  fieldToJasminWord_denote F (permComAt P i) (permComAt_covered P i) V

/-! ## 4. The scalar fragment -/

section Scalar

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar (UniformScalarArith)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful (ComLsemExportFaithful)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-- **Virtual export faithfulness of the lowered permutation.** For a field whose
    blocks are in the scalar fragment, the singleton linear program `straightOps` of
    `permJasminAt P F i`, run under the labeled `lsem` from the encoded inputs, halts
    in a state whose result register decodes to `(permJasminAt P F i).denote`. -/
theorem permJasminAt_exportFaithful (F : SingleWordField P.p) (hs : ScalarBlocks F)
    (i : Fin 16) (fn : String) :
    ComLsemExportFaithful (permJasminAt P F i) fn
      (lowerK_scalar F hs (permComAt P i)).ret_ty :=
  lowerK_exportFaithful F hs (permComAt P i) fn

theorem scalar_binLitBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a : Ctxt.Var Γ w64)
    (n : Nat) : UniformScalarArith 64 (binLitBlk op a n) :=
  .const _ rfl _ (.var _ rfl _ (.ret _))

theorem scalar_foldBlk {Γ : Ctxt jasminDialect} (c : Nat) (x : Ctxt.Var Γ w64) :
    UniformScalarArith 64 (foldBlk c x) :=
  scalar_spliceCom (scalar_binLitBlk _ _ _) (scalar_spliceCom (scalar_binLitBlk _ _ _)
    (scalar_spliceCom (scalar_binLitBlk _ _ _) (scalar_binBlk _ _ _)))

theorem scalar_foldsBlk (c : Nat) :
    ∀ (n : Nat) {Γ : Ctxt jasminDialect} (x : Ctxt.Var Γ w64),
      UniformScalarArith 64 (foldsBlk c n x)
  | 0, _, _ => .ret _
  | n + 1, _, x => scalar_spliceCom (scalar_foldBlk c x) (scalar_foldsBlk c n _)

/-- The fold-reduction multiplication block `foldMulBlk` is in the scalar fragment. -/
theorem scalar_foldMulBlk {Γ : Ctxt jasminDialect} (c n p : Nat) (a b : Ctxt.Var Γ w64) :
    UniformScalarArith 64 (foldMulBlk c n p a b) :=
  scalar_spliceCom (scalar_binBlk _ _ _)
    (scalar_spliceCom (scalar_foldsBlk c n _) (scalar_csubBlk _ _))

end Scalar

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2Width16
