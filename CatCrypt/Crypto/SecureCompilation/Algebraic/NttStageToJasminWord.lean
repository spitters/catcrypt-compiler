/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord

/-!
# The four lanes of one NTT stage, lowered to `jasminDialect`

`VIR/NttStageFieldMultiReturn.lean` carries stage `1` of the four-point
Cooley–Tukey transform as a `MultiReturnCom fieldDialect`, and
`Algebraic/FieldToJasminWord.lean` lowers single-return `Com fieldDialect`
programs to `jasminDialect` through a `SingleWordField`.  This file joins them.

The join is per lane.  `FieldToJasminWord.lowerK` is block-expanding: one source
binding becomes a block of several target bindings, so the last four bindings of
a lowered four-output stage are the tail of the single last block, not the four
lanes.  The shape a positional output-store ABI reads — the last `n` bindings,
one per output — is reached by ending the source program with one `fCopy`
binding per lane, since `fCopy` is the one covered operation whose block is a
single binding.

`capCopies m j` is the source program with copy bindings for lanes `0 … j`,
returning the last of them.  Its four instances share the binding prefix of
`copyOut4 m`, and each is a single-return program whose result is lane `j`, so
each lowers under `fieldToJasminWord_denote` and exports under
`lowerK_exportFaithful`.

## Main definitions

* `copyE` — the one-operand `fCopy q` expression.
* `lane4` — the `j`-th entry of a four-lane multi-return result.
* `copyOut4` — a four-lane `MultiReturnCom` extended with one copy binding per
  lane, returning the copies.
* `capCopies` — a four-lane `MultiReturnCom` capped at lane `j`: copy bindings
  for lanes `0 … j`, returned as a single-return `Com`.

## Main results

* `copyOut4_denote` — `copyOut4` preserves the multi-return denotation.
* `capCopies_denote` — `capCopies m j` denotes lane `j` of `m`.
* `capCopies_covered` — `capCopies m j` is `GoodW q`-covered when `m`'s bindings
  are.
* `lowerBlockW_copyE` — a copy binding lowers to one `jasminDialect` binding.
* `stage1Prog_covered` — the seven bindings of `stage1Prog` are `GoodW q`.
* `stage1_lane_denote` — the lowered lane-`j` cap of `stage1Prog` denotes the
  `SingleWordField` encoding of entry `j` of `butterflyStageSpec D 1`.
* `stage1_lane_exportFaithful` — every lane cap of `stage1Prog` lowers into
  `ComLsemExportFaithful`.
* `stage1_lane_machine` — the lowered lane-`j` cap of `stage1Prog`, run under the
  labeled `lsem` from the encoded stage inputs, halts in a state whose result
  register decodes to the encoding of entry `j` of `butterflyStageSpec D 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.NttStageToJasminWord

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful (ComLsemExportFaithful)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Transform (butterflyStageSpec)

variable {q : Nat}

/-! ## 1. The copy tail -/

/-- The `fCopy q` expression on one variable. -/
def copyE {Γ : Ctxt fieldDialect} (a : Var Γ (F q)) : Expr fieldDialect Γ (F q) :=
  ⟨.fCopy q, rfl, .cons a .nil⟩

/-- `copyE` is covered by `GoodW q`. -/
theorem good_copyE {Γ : Ctxt fieldDialect} (a : Var Γ (F q)) : GoodW q (copyE a) :=
  .inr (.inr (.inr (.inr (.inr (.inl rfl)))))

/-- Entry `j` of a four-lane multi-return result; entries past the last repeat
    the last. -/
def lane4 (vs : ListDenote (Out4 q)) (j : Nat) : ZMod q :=
  match j with
  | 0 => vs.head
  | 1 => vs.tail.head
  | 2 => vs.tail.tail.head
  | _ => vs.tail.tail.tail.head

/-- A four-lane multi-return program extended with one `fCopy` binding per lane,
    returning the copies in lane order. -/
def copyOut4 : {Γ : Ctxt fieldDialect} →
    MultiReturnCom fieldDialect Γ (Out4 q) → MultiReturnCom fieldDialect Γ (Out4 q)
  | _, .ret vs =>
      .var (copyE vs.head)
        (.var (copyE (.there vs.tail.head))
          (.var (copyE (.there (.there vs.tail.tail.head)))
            (.var (copyE (.there (.there (.there vs.tail.tail.tail.head))))
              (.ret (.cons b3 (.cons b2 (.cons b1 (.cons b0 .nil))))))))
  | _, .var e body => .var e (copyOut4 body)

/-- A four-lane multi-return program capped at lane `j`: the program's bindings,
    then one `fCopy` binding per lane `0 … j`, returning the last copy. -/
def capCopies : {Γ : Ctxt fieldDialect} →
    MultiReturnCom fieldDialect Γ (Out4 q) → Nat → Com fieldDialect Γ (F q)
  | _, .ret vs, j =>
      match j with
      | 0 => .var (copyE vs.head) (.ret b0)
      | 1 => .var (copyE vs.head) (.var (copyE (.there vs.tail.head)) (.ret b0))
      | 2 => .var (copyE vs.head)
               (.var (copyE (.there vs.tail.head))
                 (.var (copyE (.there (.there vs.tail.tail.head))) (.ret b0)))
      | _ => .var (copyE vs.head)
               (.var (copyE (.there vs.tail.head))
                 (.var (copyE (.there (.there vs.tail.tail.head)))
                   (.var (copyE (.there (.there (.there vs.tail.tail.tail.head))))
                     (.ret b0))))
  | _, .var e body, j => .var e (capCopies body j)

/-! ## 2. Denotation and coverage of the copy tail -/

/-- `lookupVars` commutes with `HVector.head`. -/
theorem lookupVars_head {Γ : Ctxt fieldDialect} {t : FieldTy} {ts : List FieldTy}
    (vs : HVector (fun ty => Var Γ ty) (t :: ts)) (V : Valuation Γ) :
    (MultiReturnCom.lookupVars vs V).head = vs.head.lookup V := by
  cases vs; rfl

/-- `lookupVars` commutes with `HVector.tail`. -/
theorem lookupVars_tail {Γ : Ctxt fieldDialect} {t : FieldTy} {ts : List FieldTy}
    (vs : HVector (fun ty => Var Γ ty) (t :: ts)) (V : Valuation Γ) :
    (MultiReturnCom.lookupVars vs V).tail = MultiReturnCom.lookupVars vs.tail V := by
  cases vs; rfl

/-- `toComHead` of a `var` program peels the binding. -/
theorem toComHead_var {Γ : Ctxt fieldDialect} {u t : FieldTy} {ts : List FieldTy}
    (e : Expr fieldDialect Γ u) (body : MultiReturnCom fieldDialect (u :: Γ) (t :: ts)) :
    (MultiReturnCom.var e body).toComHead = Com.var e body.toComHead := by
  simp [MultiReturnCom.toComHead]

/-- A `ret` program is covered. -/
theorem covered_ret {Γ : Ctxt fieldDialect} {t : FieldTy} (v : Var Γ t) :
    CoveredCom (GoodW q) (Com.ret v) := trivial

/-- A `var` program is covered when its head expression is good and its body is
    covered. -/
theorem covered_var {Γ : Ctxt fieldDialect} {t s : FieldTy} {e : Expr fieldDialect Γ t}
    {c : Com fieldDialect (t :: Γ) s} (he : GoodW q e) (hc : CoveredCom (GoodW q) c) :
    CoveredCom (GoodW q) (Com.var e c) := And.intro he hc

/-- The head projection of a `ret` program is covered. -/
theorem covered_ret_multi {Γ : Ctxt fieldDialect} {t : FieldTy} {ts : List FieldTy}
    (vs : HVector (fun ty => Var Γ ty) (t :: ts)) :
    CoveredCom (GoodW q) (MultiReturnCom.ret vs).toComHead := by
  cases vs
  rw [MultiReturnCom.toComHead]
  exact covered_ret _

/-- The head expression of a covered `var` program is good. -/
theorem good_of_covered_var {Γ : Ctxt fieldDialect} {t s : FieldTy} {e : Expr fieldDialect Γ t}
    {c : Com fieldDialect (t :: Γ) s} (h : CoveredCom (GoodW q) (Com.var e c)) : GoodW q e :=
  h.1

/-- The body of a covered `var` program is covered. -/
theorem covered_of_covered_var {Γ : Ctxt fieldDialect} {t s : FieldTy}
    {e : Expr fieldDialect Γ t} {c : Com fieldDialect (t :: Γ) s}
    (h : CoveredCom (GoodW q) (Com.var e c)) : CoveredCom (GoodW q) c := h.2

/-- The copy tail preserves the multi-return denotation. -/
theorem copyOut4_denote : ∀ {Γ : Ctxt fieldDialect}
    (m : MultiReturnCom fieldDialect Γ (Out4 q)) (V : Valuation Γ),
    (copyOut4 m).denote V = m.denote V
  | _, .ret vs, _ => by
      match vs with
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))) =>
        simp only [copyOut4]
        rfl
  | _, .var _ body, V => by
      simp only [copyOut4, MultiReturnCom.denote]
      exact copyOut4_denote body _

/-- The lane-`j` cap denotes lane `j`. -/
theorem capCopies_denote : ∀ {Γ : Ctxt fieldDialect}
    (m : MultiReturnCom fieldDialect Γ (Out4 q)) (j : Nat) (V : Valuation Γ),
    (capCopies m j).denote V = lane4 (m.denote V) j
  | _, .ret vs, j, V => by
      match vs, j with
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))), 0 =>
        simp only [capCopies]
        rfl
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))), 1 =>
        simp only [capCopies]
        rfl
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))), 2 =>
        simp only [capCopies]
        rfl
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))), _ + 3 =>
        simp only [capCopies]
        rfl
  | _, .var _ body, j, V => by
      simp only [capCopies, Com.denote, MultiReturnCom.denote]
      exact capCopies_denote body j _

/-- The lane-`j` cap is `GoodW q`-covered when the bindings of `m` are. -/
theorem capCopies_covered : ∀ {Γ : Ctxt fieldDialect}
    (m : MultiReturnCom fieldDialect Γ (Out4 q)),
    CoveredCom (GoodW q) m.toComHead → ∀ j : Nat, CoveredCom (GoodW q) (capCopies m j)
  | _, .ret _, _, j => by
      match j with
      | 0 =>
        simp only [capCopies]
        exact covered_var (good_copyE _) (covered_ret _)
      | 1 =>
        simp only [capCopies]
        exact covered_var (good_copyE _) (covered_var (good_copyE _) (covered_ret _))
      | 2 =>
        simp only [capCopies]
        exact covered_var (good_copyE _) (covered_var (good_copyE _)
          (covered_var (good_copyE _) (covered_ret _)))
      | _ + 3 =>
        simp only [capCopies]
        exact covered_var (good_copyE _) (covered_var (good_copyE _)
          (covered_var (good_copyE _) (covered_var (good_copyE _) (covered_ret _))))
  | _, .var e body, hm, j => by
      rw [toComHead_var] at hm
      simp only [capCopies]
      exact covered_var (good_of_covered_var hm)
        (capCopies_covered body (covered_of_covered_var hm) j)

/-! ## 3. The stage instance -/

/-- The seven bindings of `stage1Prog` — a constant, two products, two sums and
    two differences at modulus `q` — are all `GoodW q`. -/
theorem stage1Prog_covered : CoveredCom (GoodW q) ((stage1Prog (q := q)).toComHead) := by
  simp only [stage1Prog, MultiReturnCom.toComHead]
  refine covered_var ?_ (covered_var ?_ (covered_var ?_ (covered_var ?_
    (covered_var ?_ (covered_var ?_ (covered_var ?_ (covered_ret_multi _)))))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨1, rfl⟩))))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inl rfl)

/-- The block a copy binding lowers to is one `jasminDialect` binding, which is
    the shape a positional output-store ABI reads. -/
theorem lowerBlockW_copyE (SW : SingleWordField q) {Γ : Ctxt fieldDialect}
    (a : Var Γ (F q)) :
    lowerBlockW SW (copyE a) =
      FieldWord.binBlk .or (mapVarW a) (mapVarW a) := rfl

/-- Entry `j` of `toArray4` is lane `j`. -/
theorem getD_toArray4 (vs : ListDenote (Out4 q)) (j : Nat) (hj : j < 4) :
    (toArray4 vs).getD j 0 = lane4 vs j := by
  match vs with
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))) =>
    match j, hj with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl

variable [Fact (Nat.Prime q)]

/-- **The lowered lane.** For a single-word representation of `ZMod q`, the
    lane-`j` cap of `stage1Prog` lowers to a `jasminDialect` program denoting the
    encoding of entry `j` of `butterflyStageSpec D 1`. -/
theorem stage1_lane_denote (SW : SingleWordField q) (D : Domain (ZMod q)) (hlog : D.logN = 2)
    (x0 x1 x2 x3 : ZMod q) (j : Nat) (hj : j < 4) :
    (lowerK SW (capCopies (stage1Prog (q := q)) j)).denote
        (mapValW SW (stageVal D.omega x0 x1 x2 x3))
      = SW.enc ((butterflyStageSpec D 1 #[x0, x1, x2, x3]).getD j 0) := by
  rw [fieldToJasminWord_denote SW _ (capCopies_covered _ stage1Prog_covered j),
    capCopies_denote, stage1_denote D hlog, getD_toArray4 _ j hj]

omit [Fact (Nat.Prime q)] in
/-- **Export faithfulness of the lowered lane.** Under `ScalarBlocks SW` the
    lane-`j` cap of `stage1Prog` lowers into the scalar fragment, so its export
    satisfies `ComLsemExportFaithful`. -/
theorem stage1_lane_exportFaithful (SW : SingleWordField q) (hs : ScalarBlocks SW)
    (j : Nat) (fn : String) :
    ComLsemExportFaithful (lowerK SW (capCopies (stage1Prog (q := q)) j)) fn
      (lowerK_scalar SW hs (capCopies (stage1Prog (q := q)) j)).ret_ty :=
  lowerK_exportFaithful SW hs _ fn

/-- **The stage lane to machine semantics.** The exported lane-`j` cap of
    `stage1Prog`, driven by the labeled `lsem` from the encoded stage inputs,
    halts in a state whose result register decodes to the `SingleWordField`
    encoding of entry `j` of `butterflyStageSpec D 1`. -/
theorem stage1_lane_machine (SW : SingleWordField q) (hs : ScalarBlocks SW)
    (D : Domain (ZMod q)) (hlog : D.logN = 2) (x0 x1 x2 x3 : ZMod q)
    (j : Nat) (hj : j < 4) (fn : String) :
    ∃ st' : Lstate 64,
      lsem (singletonProg fn (straightOps (mapCtxW (Γstage4 q)).length
            (lowerK SW (capCopies (stage1Prog (q := q)) j))
            (mapCtxW (Γstage4 q)).length))
          { base := encode (mapValW SW (stageVal D.omega x0 x1 x2 x3)), lfn := fn }
          { base := st', lfn := fn }
        ∧ decode st' (comRetReg (mapCtxW (Γstage4 q)).length argName
              (lowerK SW (capCopies (stage1Prog (q := q)) j))
              (mapCtxW (Γstage4 q)).length)
          = SW.enc ((butterflyStageSpec D 1 #[x0, x1, x2, x3]).getD j 0) := by
  obtain ⟨st', hrun, hdec⟩ :=
    stage1_lane_exportFaithful SW hs j fn (mapValW SW (stageVal D.omega x0 x1 x2 x3))
  exact ⟨st', hrun, by
    rw [hdec, stage1_lane_denote SW D hlog x0 x1 x2 x3 j hj]⟩

end CatCrypt.Crypto.SecureCompilation.Algebraic.NttStageToJasminWord
