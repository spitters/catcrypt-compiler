/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar

@[expose] public section

set_option autoImplicit false

/-!
# Toward general-`Com` `lsem` faithfulness — the straight-line side, in the labeled `lsem`

The per-fragment `lsem` faithfulness results (`comToLprog_faithful_leaf` and the
straight-line subsumption tower below it) are stated over `lsemStraight` — the
body-block fold. The control-flow increments (loops/branches/calls) are stated over
the *labeled, program-indexed* `lsemFuel` (`JasminLsemLabeled`). The general-`Com`
faithfulness predicate `ComLsemExportFaithful` lives in the labeled semantics, so
the straight-line tower has to be lifted there first.

The lift glue is `JasminLsemLabeled.lsem_of_straightline`: a **jump-free** body's
`lsemStraight` execution is a labeled `lsem` derivation over the singleton program.
For that to apply to an emitted `Com` body, the body must be all-`IsStraightLine`.

This file proves exactly that structural fact — `opToLinstrR` emits only `Lopn`, so
`straightOps` (the linearizer's body, `Lret` dropped) is jump-free for **any** `Com`.
This is the bridge precondition the straight-line tower needs to enter the labeled
`lsem`, where it composes with the control-flow increments toward the general-`Com`
statement.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar

/-- **`opToLinstrR` emits only `Lopn`.** Every dialect op the linearizer renders
    becomes a straight-line `Lopn` instruction (never a jump/label/call), so its
    image is `IsStraightLine`. The per-op half of the jump-freeness fact. -/
theorem opToLinstrR_isStraightLine (op : JasminOp) (dst : String) (srcs : List LOperand) :
    IsStraightLine (opToLinstrR op dst srcs) := by
  cases op <;>
    simp only [opToLinstrR] <;>
    first
      | rfl
      | (split <;> first | rfl | (split <;> rfl))

/-- **An emitted straight-line body is jump-free.** For any `Com`, every instruction
    of `straightOps` (the linearizer body with the trailing `Lret` dropped) is
    `IsStraightLine` — because each is an `opToLinstrR` image. This is the precondition
    `JasminLsemLabeled.lsem_of_straightline` needs to lift the straight-line tower into
    the labeled `lsem`. -/
theorem straightOps_isStraightLine (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ straightOps nArgs com curDepth, IsStraightLine i := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp only [straightOps, List.not_mem_nil] at hi
  | var e body ih =>
      intro i hi
      rw [straightOps, List.mem_cons] at hi
      rcases hi with h | h
      · subst h; exact opToLinstrR_isStraightLine _ _ _
      · exact ih (curDepth + 1) i h

/-- `encodeAux` only writes registers, so it leaves the program counter unchanged. -/
theorem encodeAux_lpc {w : Nat} {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    (st : Lstate w) : (encodeAux V st).lpc = st.lpc := by
  fun_induction encodeAux V st <;>
    first
      | rfl
      | (simp only [Lstate.lpc_setReg]; assumption)
      | assumption

/-- The encoded initial store starts at program counter `0`. -/
theorem encode_lpc {w : Nat} {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    (encode (w := w) V).lpc = 0 := encodeAux_lpc V _

/-- **Straight-line `Com` faithfulness, lifted into the labeled `lsem`.** A
    uniform-`regArith` straight-line `Com`, emitted to its singleton program, executes
    under the labeled, program-indexed `lsem` (the body-fold `lsemStraight` lifted)
    from the encoded inputs to a state whose result register decodes to `Com.denote`.

    This is the straight-line faithfulness tower (`comToLprog_faithful_straightline`,
    over `lsemStraight`) carried into the semantics the control-flow increments live in,
    via the jump-freeness brick `straightOps_isStraightLine` and the bridge
    `JasminLsemLabeled.lsem_of_straightline`. It is the straight-line half of the
    general-`Com` faithfulness: a `Com` with control flow runs its straight-line segments
    through exactly this lift and its loop/branch/call nodes through the matching
    increments, all in this one `lsem`. -/
theorem straightline_com_labeled_lsem {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) (hu : UniformCtxt w Γ)
    (V : Ctxt.Valuation Γ) (fn : String) :
    ∃ st' : Lstate w,
      lsem (singletonProg fn (straightOps Γ.length com Γ.length))
          { base := encode V, lfn := fn } { base := st', lfn := fn }
        ∧ decode st' (comRetReg Γ.length argName com Γ.length)
            = (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  have hf := comToLprog_faithful_straightline hcom hu V
  rcases hrun : lsemStraight (straightOps Γ.length com Γ.length) (encode V) with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · exact lsem_of_straightline fn (straightOps Γ.length com Γ.length)
        (straightOps_isStraightLine Γ.length com Γ.length)
        { base := encode V, lfn := fn } { base := st', lfn := fn } rfl (encode_lpc V) hrun rfl
    · rw [hrun] at hf; simp only [Option.map_some, Option.some.injEq] at hf; exact hf

/-- **The maximal plain-`Lstate` straight-line fragment, in the labeled `lsem`.** The
    same lift as `straightline_com_labeled_lsem`, over `UniformScalarArith` — the maximal
    fragment whose faithfulness (`comToLprog_faithful_scalar`) is stated in the plain
    `lsemStraight`/`Lstate` semantics the labeled `lsem` extends. It adds the `regConst`
    and `select` ops to the `regArith` core, and subsumes `straightline_com_labeled_lsem`
    (`UniformScalarArith.of_regArith`).

    Because `Com` is straight-line by construction (no regions — `Core.Com` is `ret`/`var`
    only), this is the general-`Com` `lsem` faithfulness for every `Com` over the plain
    `{regArith, regConst, select}` op set: there is no control-flow case to assemble; the
    fragment tower IS the case split. The wider op sets (shift, mul/carry, cast, leaf,
    callN, simd) carry their faithfulness in the `LstateN` N-state machinery
    (`encodeN`/`lsemStraight*`/`.bind`), so lifting them needs an `LstateN`→labeled bridge
    rather than the plain `lsem_of_straightline`. -/
theorem scalar_com_labeled_lsem {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com) (hu : UniformCtxt w Γ)
    (V : Ctxt.Valuation Γ) (fn : String) :
    ∃ st' : Lstate w,
      lsem (singletonProg fn (straightOps Γ.length com Γ.length))
          { base := encode V, lfn := fn } { base := st', lfn := fn }
        ∧ decode st' (comRetReg Γ.length argName com Γ.length)
            = (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  have hf := comToLprog_faithful_scalar hcom hu V
  rcases hrun : lsemStraight (straightOps Γ.length com Γ.length) (encode V) with _ | st'
  · rw [hrun] at hf; simp at hf
  · refine ⟨st', ?_, ?_⟩
    · exact lsem_of_straightline fn (straightOps Γ.length com Γ.length)
        (straightOps_isStraightLine Γ.length com Γ.length)
        { base := encode V, lfn := fn } { base := st', lfn := fn } rfl (encode_lpc V) hrun rfl
    · rw [hrun] at hf; simp only [Option.map_some, Option.some.injEq] at hf; exact hf

/-! ## The general-`Com` `lsem` export-faithfulness predicate

The export-faithfulness predicate over a `Com` and its export name: the emitted
singleton program, run under the labeled program-indexed `lsem` from the encoded
inputs, halts at a state whose result register decodes to `Com.denote`. `Com` being
straight-line (regions-free), this is the whole faithfulness statement — no
control-flow disjunct. -/

/-- **General-`Com` `lsem` export faithfulness** (the content of the export gate).
    For every input valuation, the emitted singleton program drives the encoded inputs,
    under the labeled `lsem`, to a state decoding to `Com.denote`. -/
def ComLsemExportFaithful {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fn : String) (hw : t = .reg w) : Prop :=
  ∀ V : Ctxt.Valuation Γ, ∃ st' : Lstate w,
    lsem (singletonProg fn (straightOps Γ.length com Γ.length))
        { base := encode V, lfn := fn } { base := st', lfn := fn }
      ∧ decode st' (comRetReg Γ.length argName com Γ.length)
          = (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧)

/-- **The export gate is discharged for the maximal plain-`Lstate` fragment.**
    Any `Com` over `{regArith, regConst, select}` satisfies `ComLsemExportFaithful`,
    assembled from the straight-line tower, the jump-freeness brick and the
    `lsem_of_straightline` bridge. -/
theorem comLsemExportFaithful_of_scalar {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformScalarArith w com) (hu : UniformCtxt w Γ)
    (fn : String) : ComLsemExportFaithful com fn hcom.ret_ty :=
  fun V => scalar_com_labeled_lsem hcom hu V fn

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful
