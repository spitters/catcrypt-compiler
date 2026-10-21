/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord

/-!
# `fieldDialect → jasminDialect` for a single-word prime field

For a single-word representation `F : SingleWordField p`, the block-expanding
lowering from `fieldDialect` to `jasminDialect` at the prime fragment: every field
type maps to `reg 64`, a value of `fp p` maps to `F.enc`, and each prime-field
operation at modulus `p` expands into the block of `F`.

| source op at `p` | target block |
|---|---|
| `fAdd`, `fieldDouble` | `F.addBlk a b`, `F.addBlk a a` |
| `fSub` | `F.subBlk a b` |
| `fNeg` | `F.negBlk a` |
| `fMul`, `fieldSquare` | `F.mulBlk a b`, `F.mulBlk a a` |
| `fConst p c` | `F.constBlk c` |
| `fCopy` | one `regArith or` binding `a ||| a` |

The copy is a single binding rather than `F.copyBlk`, which returns its operand
and binds nothing: a copy then occupies exactly one target binding, which is the
shape an output-store ABI reading the last bindings of a program relies on.

Every other operation, and every operation at a modulus other than `p`, lowers
to the literal `0`; the coverage predicate `GoodW p` excludes them. Types
other than `fp p` are mapped to the word `0` by `transW`.

The program lowering is `BlockLoweringData.blockLowerComK`, whose cost is linear
in the size of the lowered program.

## Main definitions

* `mapTyW`, `mapCtxW`, `mapVarW`: the type, context and variable maps.
* `transW F`, `mapValW F`: the value and valuation transports.
* `lowerBlockW F`: the per-operation block.
* `lowering F`: the `BlockLoweringData fieldDialect jasminDialect`.
* `GoodW p`: the operations covered at modulus `p`.
* `lowerK F c`: the lowered program.
* `ScalarBlocks F`: the blocks of `F` bind only `regArith` and `regConst` at width
  64.

## Main results

* `blockTransports_on`: the block square for every `GoodW p` expression.
* `fieldToJasminWord_denote_on`: for a `GoodW p`-covered program of any result
  type, `(lowerK F c).denote (mapValW F V) = transW F (c.denote V)`.
* `fieldToJasminWord_denote`: for a covered program returning `fp p`,
  `(lowerK F c).denote (mapValW F V) = F.enc (c.denote V)`.
* `scalarBlocks_ofCanonical`: the modulus-generic blocks of
  `SingleWordField.ofCanonical` are in the fragment when the multiplication block is.
* `lowerK_scalar`: under `ScalarBlocks F`, every lowered program is in
  `UniformScalarArith 64`.
* `lowerK_exportFaithful`: under `ScalarBlocks F`, every lowered program satisfies
  `JasminLsemGeneralFaithful.ComLsemExportFaithful`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord

/-! ## 1. Type, context and variable maps -/

/-- Every field type is carried by a 64-bit register. -/
@[reducible] def mapTyW : FieldTy → JasminTy := fun _ => .reg 64

/-- The context map: pointwise `mapTyW`. -/
def mapCtxW (Γ : Ctxt fieldDialect) : Ctxt jasminDialect := Γ.map mapTyW

/-- The variable map: the same de Bruijn index in the mapped context. -/
def mapVarW : {Γ : Ctxt fieldDialect} → {t : FieldTy} →
    Var Γ t → Var (mapCtxW Γ) (mapTyW t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVarW v)

variable {p : Nat}

/-! ## 2. Value and valuation transports -/

/-- The value transport: `F.enc` on `fp p`, and the word `0` on every other type. -/
def transW (F : SingleWordField p) : {t : FieldTy} → ⟦t⟧ → ⟦mapTyW t⟧
  | .fp q, x => if h : q = p then F.enc (cast (congrArg ZMod h) x) else BitVec.ofNat 64 0
  | .fp2 _, _ => BitVec.ofNat 64 0
  | .fp6 _, _ => BitVec.ofNat 64 0
  | .fp12 _, _ => BitVec.ofNat 64 0

/-- The valuation transport: positional `transW F`. -/
def mapValW (F : SingleWordField p) :
    {Γ : Ctxt fieldDialect} → Valuation Γ → Valuation (mapCtxW Γ)
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons (transW F x) (mapValW F V)

theorem transW_fp (F : SingleWordField p) (x : ZMod p) :
    transW F (t := .fp p) x = F.enc x := by
  simp only [transW, dite_true]
  rfl

theorem mapVarW_lookup (F : SingleWordField p) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (v : Var Γ t) (V : Valuation Γ) :
    (mapVarW v).lookup (mapValW F V) = transW F (v.lookup V) := by
  induction v with
  | here => cases V with | cons x V => rfl
  | there v ih => cases V with | cons x V => exact ih V

/-! ## 3. Per-operation blocks -/

/-- The constant block for `fConst q c`: `F.constBlk c` when `q = p`, and the
    literal `0` otherwise. -/
def constW (F : SingleWordField p) {Γ : Ctxt jasminDialect} (q : Nat) (c : ZMod q) :
    Com jasminDialect Γ w64 :=
  if h : q = p then F.constBlk (cast (congrArg ZMod h) c) else litBlk 0

/-- The per-operation block of the lowering. -/
def lowerBlockW (F : SingleWordField p) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) : Com jasminDialect (mapCtxW Γ) (mapTyW t) :=
  match e with
  | ⟨.fAdd _, _, .cons a (.cons b .nil)⟩ => F.addBlk (mapVarW a) (mapVarW b)
  | ⟨.fSub _, _, .cons a (.cons b .nil)⟩ => F.subBlk (mapVarW a) (mapVarW b)
  | ⟨.fNeg _, _, .cons a .nil⟩ => F.negBlk (mapVarW a)
  | ⟨.fMul _, _, .cons a (.cons b .nil)⟩ => F.mulBlk (mapVarW a) (mapVarW b)
  | ⟨.fConst q c, _, .nil⟩ => constW F q c
  | ⟨.fCopy _, _, .cons a .nil⟩ => binBlk .or (mapVarW a) (mapVarW a)
  | ⟨.fieldDouble _, _, .cons a .nil⟩ => F.addBlk (mapVarW a) (mapVarW a)
  | ⟨.fieldSquare _, _, .cons a .nil⟩ => F.mulBlk (mapVarW a) (mapVarW a)
  | ⟨_, _, _⟩ => litBlk 0

/-- The block-expanding lowering `fieldDialect → jasminDialect` through `F`. -/
def lowering (F : SingleWordField p) : BlockLoweringData fieldDialect jasminDialect where
  mapTy := mapTyW
  mapCtx := mapCtxW
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarW
  lowerExprBlock := lowerBlockW F

/-- The operations covered at modulus `p`: add, sub, neg, mul, constants, copy,
    doubling and squaring of `fp p`. -/
def GoodW (p : Nat) {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) :
    Prop :=
  e.op = .fAdd p ∨ e.op = .fSub p ∨ e.op = .fNeg p ∨ e.op = .fMul p ∨
    (∃ c : ZMod p, e.op = .fConst p c) ∨ e.op = .fCopy p ∨ e.op = .fieldDouble p ∨
    e.op = .fieldSquare p

/-- The lowered program: `blockLowerComK` of `lowering F`. -/
def lowerK (F : SingleWordField p) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) : Com jasminDialect (mapCtxW Γ) (mapTyW t) :=
  (lowering F).blockLowerComK c

/-! ## 4. The transport squares -/

theorem singleWord_varTransports (F : SingleWordField p) :
    VarTransports (lowering F) (transW F) (mapValW F) :=
  fun v V => mapVarW_lookup F v V

theorem singleWord_mapValExtends (F : SingleWordField p) :
    MapValExtends (lowering F) (transW F) (mapValW F) :=
  fun _ _ => rfl

/-- **Block square for covered operations.** -/
theorem blockTransports_on (F : SingleWordField p) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (e : Expr fieldDialect Γ t) (hg : GoodW p e) (V : Valuation Γ) :
    ((lowering F).lowerExprBlock e).denote (mapValW F V) = transW F (e.denote V) := by
  obtain ⟨op, h, args⟩ := e
  have hv : ∀ (a : Var Γ (.fp p)), (mapVarW a).lookup (mapValW F V) = F.enc (a.lookup V) :=
    fun a => (mapVarW_lookup F a V).trans (transW_fp F _)
  rcases hg with hop | hop | hop | hop | ⟨c, hop⟩ | hop | hop | hop <;> subst hop <;> cases h
  · cases args with
    | cons a args1 => cases args1 with
      | cons b args2 => cases args2 with
        | nil =>
          show (F.addBlk (mapVarW a) (mapVarW b)).denote (mapValW F V) =
            transW F (t := .fp p) (fAddF (a.lookup V) (b.lookup V))
          rw [transW_fp]
          exact F.addBlk_denote _ _ _ _ _ (hv a) (hv b)
  · cases args with
    | cons a args1 => cases args1 with
      | cons b args2 => cases args2 with
        | nil =>
          show (F.subBlk (mapVarW a) (mapVarW b)).denote (mapValW F V) =
            transW F (t := .fp p) (fSubF (a.lookup V) (b.lookup V))
          rw [transW_fp]
          exact F.subBlk_denote _ _ _ _ _ (hv a) (hv b)
  · cases args with
    | cons a args1 => cases args1 with
      | nil =>
        show (F.negBlk (mapVarW a)).denote (mapValW F V) =
          transW F (t := .fp p) (fNegF (a.lookup V))
        rw [transW_fp]
        exact F.negBlk_denote _ _ _ (hv a)
  · cases args with
    | cons a args1 => cases args1 with
      | cons b args2 => cases args2 with
        | nil =>
          show (F.mulBlk (mapVarW a) (mapVarW b)).denote (mapValW F V) =
            transW F (t := .fp p) (fMulF (a.lookup V) (b.lookup V))
          rw [transW_fp]
          exact F.mulBlk_denote _ _ _ _ _ (hv a) (hv b)
  · cases args with
    | nil =>
      show (constW F p c).denote (mapValW F V) = transW F (t := .fp p) (fConstF c)
      rw [transW_fp]
      simp only [constW, dite_true]
      exact F.constBlk_denote _ c
  · cases args with
    | cons a args1 => cases args1 with
      | nil =>
        show (binBlk .or (mapVarW a) (mapVarW a)).denote (mapValW F V) =
          transW F (t := .fp p) (fCopyF (a.lookup V))
        rw [transW_fp, binBlk_denote, hv a]
        exact BitVec.or_self
  · cases args with
    | cons a args1 => cases args1 with
      | nil =>
        show (F.addBlk (mapVarW a) (mapVarW a)).denote (mapValW F V) =
          transW F (t := .fp p) (fDoubleF (a.lookup V))
        rw [transW_fp]
        exact F.addBlk_denote _ _ _ _ _ (hv a) (hv a)
  · cases args with
    | cons a args1 => cases args1 with
      | nil =>
        show (F.mulBlk (mapVarW a) (mapVarW a)).denote (mapValW F V) =
          transW F (t := .fp p) (fSquareF (a.lookup V))
        rw [transW_fp]
        exact F.mulBlk_denote _ _ _ _ _ (hv a) (hv a)

/-- **Denotation preservation at every result type.** A `GoodW p`-covered field
    program lowers to a jasmin program denoting the transport of its
    denotation. -/
theorem fieldToJasminWord_denote_on (F : SingleWordField p) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) (hcov : CoveredCom (GoodW p) c)
    (V : Valuation Γ) :
    (lowerK F c).denote (mapValW F V) = transW F (c.denote V) :=
  (lowering F).blockLowerComK_denote_on (transW F) (mapValW F) (GoodW p)
    (singleWord_varTransports F) (fun e hg V => blockTransports_on F e hg V)
    (singleWord_mapValExtends F) c hcov V

/-- **Denotation preservation of `fieldDialect → jasminDialect`.** A
    `GoodW p`-covered field program returning `fp p` lowers, through the blocks of
    `F`, to a jasmin program whose result on the encoded valuation is the encoding
    of the field result. -/
theorem fieldToJasminWord_denote (F : SingleWordField p) {Γ : Ctxt fieldDialect}
    (c : Com fieldDialect Γ (.fp p)) (hcov : CoveredCom (GoodW p) c) (V : Valuation Γ) :
    (lowerK F c).denote (mapValW F V) = F.enc (c.denote V) :=
  (fieldToJasminWord_denote_on F c hcov V).trans (transW_fp F _)

/-! ## 5. The scalar fragment

`UniformScalarArith 64` is the fragment of `JasminLsemGeneralFaithful.comLsemExportFaithful_of_scalar`:
every binding a `regArith` or `regConst` at width 64. It is closed under renaming
and both block splices, so a lowering whose blocks lie in it produces programs in
it. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (UniformCtxt UniformCtxt.cons)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar (UniformScalarArith)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemGeneralFaithful
  (ComLsemExportFaithful comLsemExportFaithful_of_scalar)

theorem scalar_rename {Γ Γ' : Ctxt jasminDialect} {t : JasminTy} (h : Ctxt.Hom Γ Γ')
    {c : Com jasminDialect Γ t} (hc : UniformScalarArith 64 c) :
    UniformScalarArith 64 (Com.rename h c) := by
  induction hc generalizing Γ' with
  | ret v => exact .ret (h v)
  | var bop heq args _ ih => exact .var bop heq _ (ih h.lift)
  | const n heq args _ ih => exact .const n heq _ (ih h.lift)

theorem scalar_spliceCom {Γ : Ctxt jasminDialect} {t s : JasminTy} {c : Com jasminDialect Γ t}
    {k : Com jasminDialect (t :: Γ) s} (hc : UniformScalarArith 64 c)
    (hk : UniformScalarArith 64 k) : UniformScalarArith 64 (spliceCom c k) := by
  induction hc generalizing s with
  | ret v => exact scalar_rename _ hk
  | var bop heq args _ ih => exact .var bop heq args (ih (scalar_rename _ hk))
  | const n heq args _ ih => exact .const n heq args (ih (scalar_rename _ hk))

theorem scalar_spliceComK {Γ : Ctxt jasminDialect} {a b : JasminTy}
    {blk : Com jasminDialect Γ a} (hb : UniformScalarArith 64 blk)
    (k : {Δ : Ctxt jasminDialect} → Ctxt.Hom Γ Δ → Var Δ a → Com jasminDialect Δ b)
    (hk : ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) (res : Var Δ a),
      UniformScalarArith 64 (k ren res)) :
    UniformScalarArith 64 (spliceComK blk k) := by
  induction hb generalizing b with
  | ret v => exact hk _ v
  | var bop heq args _ ih => exact .var bop heq args (ih _ (fun _ res => hk _ res))
  | const n heq args _ ih => exact .const n heq args (ih _ (fun _ res => hk _ res))

theorem scalar_blockLowerComR (F : SingleWordField p)
    (hblk : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t),
      UniformScalarArith 64 (lowerBlockW F e)) :
    ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} {Δ : Ctxt jasminDialect}
      (ren : Ctxt.Hom (mapCtxW Γ) Δ) (c : Com fieldDialect Γ t),
      UniformScalarArith 64 ((lowering F).blockLowerComR ren c)
  | _, _, _, ren, .ret v => by exact .ret (ren (mapVarW v))
  | _, _, _, ren, .var e body => by
      exact scalar_spliceComK (scalar_rename ren (hblk e)) _
        (fun ren' res => scalar_blockLowerComR F hblk _ body)

/-- The blocks of `F` bind only `regArith` and `regConst` at width 64. -/
structure ScalarBlocks (F : SingleWordField p) : Prop where
  add : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64), UniformScalarArith 64 (F.addBlk a b)
  sub : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64), UniformScalarArith 64 (F.subBlk a b)
  mul : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64), UniformScalarArith 64 (F.mulBlk a b)
  neg : ∀ {Γ : Ctxt jasminDialect} (a : Var Γ w64), UniformScalarArith 64 (F.negBlk a)
  const : ∀ {Γ : Ctxt jasminDialect} (x : ZMod p),
    UniformScalarArith 64 (F.constBlk (Γ := Γ) x)

theorem scalar_litBlk {Γ : Ctxt jasminDialect} (n : Nat) :
    UniformScalarArith 64 (litBlk (Γ := Γ) n) :=
  .const _ rfl _ (.ret _)

theorem scalar_binBlk {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a b : Var Γ w64) :
    UniformScalarArith 64 (binBlk op a b) :=
  .var _ rfl _ (.ret _)

theorem scalar_csubBlk {Γ : Ctxt jasminDialect} (P : Nat) (x : Var Γ w64) :
    UniformScalarArith 64 (csubBlk P x) :=
  .const _ rfl _ (.var _ rfl _ (.const _ rfl _ (.var _ rfl _ (.const _ rfl _
    (.var _ rfl _ (.var _ rfl _ (.var _ rfl _ (.ret _))))))))

/-- The modulus-generic blocks of `SingleWordField.ofCanonical` are in the scalar
    fragment when the multiplication block is. -/
theorem scalarBlocks_ofCanonical (p : Nat) [NeZero p] (hp : 2 * p ≤ 2 ^ 63)
    (mulBlk : ∀ {Γ : Ctxt jasminDialect}, Var Γ w64 → Var Γ w64 → Com jasminDialect Γ w64)
    (mulBlk_denote : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64)
      (V : Valuation Γ) (x y : ZMod p), a.lookup V = canonEnc p x →
      b.lookup V = canonEnc p y → (mulBlk a b).denote V = canonEnc p (x * y))
    (hmul : ∀ {Γ : Ctxt jasminDialect} (a b : Var Γ w64), UniformScalarArith 64 (mulBlk a b)) :
    ScalarBlocks (SingleWordField.ofCanonical p hp mulBlk mulBlk_denote) where
  add _ _ := scalar_spliceCom (scalar_binBlk _ _ _) (scalar_csubBlk _ _)
  sub _ _ := scalar_spliceCom (scalar_litBlk _)
    (scalar_spliceCom (scalar_binBlk _ _ _) (scalar_spliceCom (scalar_binBlk _ _ _)
      (scalar_csubBlk _ _)))
  mul a b := hmul a b
  neg _ := scalar_spliceCom (scalar_litBlk _)
    (scalar_spliceCom (scalar_binBlk _ _ _) (scalar_csubBlk _ _))
  const _ := scalar_litBlk _

theorem scalar_lowerBlockW (F : SingleWordField p) (hs : ScalarBlocks F)
    {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t) :
    UniformScalarArith 64 (lowerBlockW F e) :=
  match e with
  | ⟨.fAdd _, _, .cons _ (.cons _ .nil)⟩ => hs.add _ _
  | ⟨.fSub _, _, .cons _ (.cons _ .nil)⟩ => hs.sub _ _
  | ⟨.fNeg _, _, .cons _ .nil⟩ => hs.neg _
  | ⟨.fMul _, _, .cons _ (.cons _ .nil)⟩ => hs.mul _ _
  | ⟨.fConst q c, _, .nil⟩ => by
      show UniformScalarArith 64 (constW F q c)
      unfold constW
      split
      · exact hs.const _
      · exact scalar_litBlk _
  | ⟨.fCopy _, _, .cons _ .nil⟩ => scalar_binBlk _ _ _
  | ⟨.fieldDouble _, _, .cons _ .nil⟩ => hs.add _ _
  | ⟨.fieldSquare _, _, .cons _ .nil⟩ => hs.mul _ _
  | ⟨.fInv _, _, .cons _ .nil⟩ => scalar_litBlk _

theorem uniformCtxt_mapCtxW : ∀ (Γ : Ctxt fieldDialect), UniformCtxt 64 (mapCtxW Γ)
  | [] => by intro v; cases v
  | _ :: Γ => UniformCtxt.cons (uniformCtxt_mapCtxW Γ)

/-- **The lowered program is in the scalar fragment** when the blocks of `F` are. -/
theorem lowerK_scalar (F : SingleWordField p) (hs : ScalarBlocks F) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (c : Com fieldDialect Γ t) : UniformScalarArith 64 (lowerK F c) :=
  scalar_blockLowerComR F (scalar_lowerBlockW F hs) _ c

/-- **Virtual export faithfulness of the lowered program.** The singleton linear
    program `straightOps` of `lowerK F c`, run under the labeled `lsem` from the
    encoded inputs, halts in a state whose result register decodes to
    `(lowerK F c).denote`. -/
theorem lowerK_exportFaithful (F : SingleWordField p) (hs : ScalarBlocks F)
    {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) (fn : String) :
    ComLsemExportFaithful (lowerK F c) fn (lowerK_scalar F hs c).ret_ty :=
  comLsemExportFaithful_of_scalar (lowerK_scalar F hs c) (uniformCtxt_mapCtxW Γ) fn

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminWord
