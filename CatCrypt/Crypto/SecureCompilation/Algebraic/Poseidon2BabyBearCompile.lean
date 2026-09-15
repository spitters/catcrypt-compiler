/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear
public import CatCrypt.Crypto.Hash.Poseidon2.BabyBear

/-!
# The Poseidon2 BabyBear width-16 permutation as a `fieldDialect` program

The permutation is a list of steps `permSteps : List Step`, each step one
`fieldDialect` binding over a builder state of 24 working slots (16 lanes and 8
scratch slots) and 157 constant slots. `run` turns a step list into a
`Com fieldDialect` program; every binding it produces is a BabyBear `fAdd`,
`fMul`, `fCopy` or `fConst`, so every program built by `run` is covered by
`GoodW P` (`run_covered`), with no evaluation of the step list.

The schedule is Plonky3's: the 157 round constants and diagonal entries are bound
by `fConst`; an external MDS pre-mix; four external rounds; thirteen internal
rounds; four external rounds; and sixteen trailing `fCopy` bindings, one per
lane in order, so that the last sixteen bindings of the program hold the sixteen
output lanes. In the external MDS, `2x` and `3x` are sums; the S-box `x⁷` is the
chain `x², x⁴, x⁶, x⁷`.

## Main definitions

* `Step`, `run`: single-binding steps and the program they denote.
* `permSteps`: the permutation schedule.
* `permComAt i`: the permutation program over the 16 input lanes, returning lane
  `i`.
* `permJasminAt i`: its lowering `FieldToJasminWord.lowerK babyBear`.

## Main results

* `run_covered`: every program produced by `run` is `GoodW P`-covered.
* `permComAt_lowerK_denote`: the lowered permutation program, run on the
  BabyBear encoding of the inputs, returns the encoding of lane `i` of the field
  program's result.
* `babyBear_scalarBlocks`: the BabyBear blocks bind only `regArith` and `regConst`.
* `permJasminAt_exportFaithful`: `permJasminAt i` satisfies
  `JasminLsemGeneralFaithful.ComLsemExportFaithful`.

The equality of `permComAt i` with `Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute`
is not stated here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.BabyBear (P babyBear)
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear
  (fullRoundConstants partialRoundConstants diagV fullRounds partialRounds)

/-! ## 1. Slots and the builder state -/

/-- The field type of every lane, scratch slot and constant. -/
abbrev FP : FieldTy := .fp P

/-- The input context: the 16 state lanes. -/
abbrev inCtxt : Ctxt fieldDialect := List.replicate 16 FP

/-- The builder state at context `Γ`: the current variable of each of the 24
    working slots (16 lanes, 8 scratch) and of each of the 157 constant slots
    (128 external round constants, 13 internal round constants, 16 diagonal
    entries). -/
structure BState (Γ : Ctxt fieldDialect) where
  /-- Working slots. -/
  lane : Fin 24 → Ctxt.Var Γ FP
  /-- Constant slots. -/
  const : Fin 157 → Ctxt.Var Γ FP

/-- A step operand: a working slot or a constant slot. -/
inductive Src where
  | lane (i : Fin 24)
  | const (j : Fin 157)

/-- A single-binding step. -/
inductive Step where
  /-- `dst := a + b`. -/
  | add (dst : Fin 24) (a b : Src)
  /-- `dst := a * b`. -/
  | mul (dst : Fin 24) (a b : Src)
  /-- `dst := a`, as its own binding. -/
  | copy (dst : Fin 24) (a : Src)
  /-- Constant slot `j := c`. -/
  | konst (j : Fin 157) (c : ZMod P)

/-- The variable of an operand. -/
def BState.get {Γ : Ctxt fieldDialect} (st : BState Γ) : Src → Ctxt.Var Γ FP
  | .lane i => st.lane i
  | .const j => st.const j

/-- The state after a binding: the written slot holds the fresh variable, every
    other variable is shifted past it. -/
def BState.after {Γ : Ctxt fieldDialect} (st : BState Γ) : Step → BState (FP :: Γ)
  | .add dst _ _ | .mul dst _ _ | .copy dst _ =>
      { lane := fun i => if i = dst then .here else (st.lane i).there
        const := fun j => (st.const j).there }
  | .konst j₀ _ =>
      { lane := fun i => (st.lane i).there
        const := fun j => if j = j₀ then .here else (st.const j).there }

/-- The `fieldDialect` expression of a step. -/
def stepExpr {Γ : Ctxt fieldDialect} (st : BState Γ) : Step → Expr fieldDialect Γ FP
  | .add _ a b => ⟨.fAdd P, rfl, .cons (st.get a) (.cons (st.get b) .nil)⟩
  | .mul _ a b => ⟨.fMul P, rfl, .cons (st.get a) (.cons (st.get b) .nil)⟩
  | .copy _ a => ⟨.fCopy P, rfl, .cons (st.get a) .nil⟩
  | .konst _ c => ⟨.fConst P c, rfl, .nil⟩

/-- The program of a step list: one binding per step, then the continuation on
    the final state. -/
def run : List Step → {Γ : Ctxt fieldDialect} → BState Γ →
    ({Γ' : Ctxt fieldDialect} → BState Γ' → Com fieldDialect Γ' FP) →
    Com fieldDialect Γ FP
  | [], _, st, k => k st
  | s :: ss, _, st, k => .var (stepExpr st s) (run ss (st.after s) k)

theorem stepExpr_good {Γ : Ctxt fieldDialect} (st : BState Γ) (s : Step) :
    GoodW P (stepExpr st s) := by
  cases s with
  | add => exact Or.inl rfl
  | mul => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | copy => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | konst _ c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))))

/-- **Coverage by construction.** If the continuation produces covered programs,
    so does `run ss`. -/
theorem run_covered (ss : List Step) {Γ : Ctxt fieldDialect} (st : BState Γ)
    (k : {Γ' : Ctxt fieldDialect} → BState Γ' → Com fieldDialect Γ' FP)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (s : BState Γ'), CoveredCom (GoodW P) (k s)) :
    CoveredCom (GoodW P) (run ss st k) := by
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
def t2 : Fin 24 := ⟨22, by decide⟩
def t4 : Fin 24 := ⟨23, by decide⟩

/-- Constant slot of the external round constant of round `r`, lane `i`. -/
def cExt (r : Fin 8) (i : Fin 16) : Fin 157 := ⟨r.val * 16 + i.val, by omega⟩

/-- Constant slot of the internal round constant of round `r`. -/
def cInt (r : Fin 13) : Fin 157 := ⟨128 + r.val, by omega⟩

/-- Constant slot of the diagonal entry of lane `i`. -/
def cDiag (i : Fin 16) : Fin 157 := ⟨141 + i.val, by omega⟩

/-- The value of constant slot `j`. -/
def constVal (j : Fin 157) : ZMod P :=
  if h : j.val < 128 then
    fullRoundConstants ⟨j.val / 16, by unfold fullRounds; omega⟩
      ⟨j.val % 16, by show _ < 16; omega⟩
  else if h' : j.val < 141 then
    partialRoundConstants ⟨j.val - 128, by unfold partialRounds; omega⟩
  else
    diagV ⟨j.val - 141, by have := j.isLt; show _ < 16; omega⟩

/-- Bind every constant slot. -/
def constSteps : List Step := (List.finRange 157).map fun j => .konst j (constVal j)

/-- The S-box `dst := src⁷` through `t2 := x²`, `t4 := x⁴`, `t4 := x⁶`. -/
def sboxSteps (dst src : Fin 24) : List Step :=
  [.mul t2 (.lane src) (.lane src), .mul t4 (.lane t2) (.lane t2),
   .mul t4 (.lane t4) (.lane t2), .mul dst (.lane t4) (.lane src)]

/-- The 4×4 block `circ(2, 3, 1, 1)` on lanes `4b .. 4b+3`, rows staged in
    `s0 .. s3` and copied back. -/
def mat4Steps (b : Fin 4) : List Step :=
  let l0 : Src := .lane ⟨4 * b.val, by omega⟩
  let l1 : Src := .lane ⟨4 * b.val + 1, by omega⟩
  let l2 : Src := .lane ⟨4 * b.val + 2, by omega⟩
  let l3 : Src := .lane ⟨4 * b.val + 3, by omega⟩
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
def colSumSteps : List Step :=
  ((List.finRange 4).flatMap fun c =>
    [ .add acc (.lane (laneSlot ⟨c.val, by omega⟩)) (.lane (laneSlot ⟨c.val + 4, by omega⟩)),
      .add acc (.lane acc) (.lane (laneSlot ⟨c.val + 8, by omega⟩)),
      .add (colSlot c) (.lane acc) (.lane (laneSlot ⟨c.val + 12, by omega⟩)) ]) ++
  (List.finRange 16).map fun i =>
    .add (laneSlot i) (.lane (laneSlot i)) (.lane (colSlot ⟨i.val % 4, by omega⟩))

/-- The external MDS layer. -/
def externalMDSSteps : List Step :=
  (List.finRange 4).flatMap mat4Steps ++ colSumSteps

/-- External round `r`: round constants, S-box on every lane, external MDS. -/
def externalRoundSteps (r : Fin 8) : List Step :=
  (List.finRange 16).map (fun i => .add (laneSlot i) (.lane (laneSlot i)) (.const (cExt r i))) ++
  (List.finRange 16).flatMap (fun i => sboxSteps (laneSlot i) (laneSlot i)) ++
  externalMDSSteps

/-- The internal MDS layer: `acc := Σ lanes`, then lane `i := acc + V[i] · lane i`. -/
def internalMDSSteps : List Step :=
  .add acc (.lane (laneSlot 0)) (.lane (laneSlot 1)) ::
  ((List.finRange 14).map fun i => .add acc (.lane acc) (.lane (laneSlot ⟨i.val + 2, by omega⟩))) ++
  (List.finRange 16).flatMap fun i =>
    [.mul tmp (.const (cDiag i)) (.lane (laneSlot i)), .add (laneSlot i) (.lane acc) (.lane tmp)]

/-- Internal round `r`: round constant on lane 0, S-box on lane 0, internal MDS. -/
def internalRoundSteps (r : Fin 13) : List Step :=
  .add (laneSlot 0) (.lane (laneSlot 0)) (.const (cInt r)) ::
  sboxSteps (laneSlot 0) (laneSlot 0) ++ internalMDSSteps

/-- Copy every lane, in order, as the last sixteen bindings. -/
def outStageSteps : List Step :=
  (List.finRange 16).map fun i => .copy (laneSlot i) (.lane (laneSlot i))

/-- The whole schedule. -/
def permSteps : List Step :=
  constSteps ++ externalMDSSteps ++
  (List.finRange 4).flatMap (fun r => externalRoundSteps ⟨r.val, by omega⟩) ++
  (List.finRange 13).flatMap internalRoundSteps ++
  (List.finRange 4).flatMap (fun r => externalRoundSteps ⟨r.val + 4, by omega⟩) ++
  outStageSteps

/-! ## 3. The program and its lowering -/

/-- Input variable `i` of `List.replicate (m + 1) FP`, with index `0` the most
    recent binding. -/
def inputVar : (m : Nat) → Nat → @Ctxt.Var fieldDialect (List.replicate (m + 1) FP) FP
  | _, 0 => .here
  | 0, _ => .here
  | m + 1, j + 1 => (inputVar m j).there

/-- The initial state: lane `i` is input `i`; scratch and constant slots point at
    input `0` and are written before they are read. -/
def initState : BState inCtxt where
  lane := fun i => if i.val < 16 then inputVar 15 i.val else inputVar 15 0
  const := fun _ => inputVar 15 0

/-- **The Poseidon2 BabyBear permutation over the 16 input lanes, returning lane
    `i`.** -/
def permComAt (i : Fin 16) : Com fieldDialect inCtxt FP :=
  run permSteps initState (fun st => .ret (st.lane (laneSlot i)))

theorem permComAt_covered (i : Fin 16) : CoveredCom (GoodW P) (permComAt i) :=
  run_covered permSteps initState _ (fun _ => trivial)

/-- The lowered permutation program returning lane `i`. -/
def permJasminAt (i : Fin 16) :
    Com jasminDialect (mapCtxW inCtxt) (mapTyW FP) :=
  lowerK babyBear (permComAt i)

/-- **Correctness of the lowered permutation.** On the BabyBear encoding of any
    input valuation, the lowered program returns the encoding of lane `i` of the
    field program. -/
theorem permComAt_lowerK_denote (i : Fin 16) (V : Ctxt.Valuation inCtxt) :
    (permJasminAt i).denote (mapValW babyBear V) = babyBear.enc ((permComAt i).denote V) :=
  fieldToJasminWord_denote babyBear (permComAt i) (permComAt_covered i) V

/-! ## 4. The scalar fragment of the BabyBear blocks

The BabyBear multiplication block is the `Poseidon2WholePermCom.emitMul` builder;
each builder of that chain binds one `regArith` or `regConst` and passes control
to its continuation. -/

section Scalar

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar (UniformScalarArith)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful (ComLsemExportFaithful)

theorem scalar_emitBin {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : Poseidon2WholePermCom.BState Γ) (op : JasminBinOp) (dst a b : Fin 25)
    (k : Poseidon2WholePermCom.Cont t)
    (hk : ∀ {Γ' : Ctxt jasminDialect} (s : Poseidon2WholePermCom.BState Γ'),
      UniformScalarArith 64 (k s)) :
    UniformScalarArith 64 (Poseidon2WholePermCom.emitBin st op dst a b k) :=
  .var op rfl _ (hk _)

theorem scalar_emitConst {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : Poseidon2WholePermCom.BState Γ) (dst : Fin 25) (n : Nat)
    (k : Poseidon2WholePermCom.Cont t)
    (hk : ∀ {Γ' : Ctxt jasminDialect} (s : Poseidon2WholePermCom.BState Γ'),
      UniformScalarArith 64 (k s)) :
    UniformScalarArith 64 (Poseidon2WholePermCom.emitConst st dst n k) :=
  .const n rfl _ (hk _)

theorem scalar_emitFold {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : Poseidon2WholePermCom.BState Γ) (dst src : Fin 25)
    (k : Poseidon2WholePermCom.Cont t)
    (hk : ∀ {Γ' : Ctxt jasminDialect} (s : Poseidon2WholePermCom.BState Γ'),
      UniformScalarArith 64 (k s)) :
    UniformScalarArith 64 (Poseidon2WholePermCom.emitFold st dst src k) :=
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitBin _ _ _ _ _ _ hk

theorem scalar_emitCsub {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : Poseidon2WholePermCom.BState Γ) (dst src : Fin 25)
    (k : Poseidon2WholePermCom.Cont t)
    (hk : ∀ {Γ' : Ctxt jasminDialect} (s : Poseidon2WholePermCom.BState Γ'),
      UniformScalarArith 64 (k s)) :
    UniformScalarArith 64 (Poseidon2WholePermCom.emitCsub st dst src k) :=
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitConst _ _ _ _ fun _ => scalar_emitBin _ _ _ _ _ _ fun _ =>
  scalar_emitBin _ _ _ _ _ _ hk

theorem scalar_emitReduce {Γ : Ctxt jasminDialect} {t : JasminTy}
    (st : Poseidon2WholePermCom.BState Γ) (dst src : Fin 25)
    (k : Poseidon2WholePermCom.Cont t)
    (hk : ∀ {Γ' : Ctxt jasminDialect} (s : Poseidon2WholePermCom.BState Γ'),
      UniformScalarArith 64 (k s)) :
    UniformScalarArith 64 (Poseidon2WholePermCom.emitReduce st dst src k) :=
  scalar_emitFold _ _ _ _ fun _ => scalar_emitFold _ _ _ _ fun _ =>
  scalar_emitFold _ _ _ _ fun _ => scalar_emitFold _ _ _ _ fun _ =>
  scalar_emitFold _ _ _ _ fun _ => scalar_emitFold _ _ _ _ fun _ =>
  scalar_emitFold _ _ _ _ fun _ => scalar_emitFold _ _ _ _ fun _ =>
  scalar_emitFold _ _ _ _ fun _ => scalar_emitFold _ _ _ _ fun _ =>
  scalar_emitCsub _ _ _ _ fun _ => scalar_emitCsub _ _ _ _ hk

theorem babyBear_mulBlk_scalar {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ FieldWord.w64) :
    UniformScalarArith 64 (FieldWord.BabyBear.mulBlk a b) := by
  unfold FieldWord.BabyBear.mulBlk Poseidon2WholePermCom.emitMul
  exact scalar_emitBin _ _ _ _ _ _ fun _ => scalar_emitReduce _ _ _ _ fun _ => .ret _

theorem babyBear_scalarBlocks : ScalarBlocks babyBear :=
  scalarBlocks_ofCanonical _ _ _ _ babyBear_mulBlk_scalar

/-- **Virtual export faithfulness of the lowered permutation.** The singleton
    linear program `straightOps` of `permJasminAt i`, run under the labeled `lsem`
    from the encoded inputs, halts in a state whose result register decodes to
    `(permJasminAt i).denote`. -/
theorem permJasminAt_exportFaithful (i : Fin 16) (fn : String) :
    ComLsemExportFaithful (permJasminAt i) fn
      (lowerK_scalar babyBear babyBear_scalarBlocks (permComAt i)).ret_ty :=
  lowerK_exportFaithful babyBear babyBear_scalarBlocks (permComAt i) fn

end Scalar

end CatCrypt.Crypto.SecureCompilation.Algebraic.Poseidon2BabyBear
