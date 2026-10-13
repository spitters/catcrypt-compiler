/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCatComplete
public import CatCrypt.Crypto.Hax.NFInline
public import CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

/-!
# The operations of the Jasmin image of the typed front

A unit-free program of the typed front, translated by `nfToCatExt D` and converted along
`catToJasmin` by `NFProg.map?`, has every let-binding, in every region, at an operation of
the stack-memory fragment `opMemB` whose result type is of positive width. The translation
binds only operations of `catMemB`: word arithmetic, carries, equalities, selections of
words, dynamic memory accesses, bit constants, constants and immediate shifts below the
width, each at a result type of positive width; the unit constant, whose block is a
constant at width `0`, is excluded by `UnitFree`. Every block `toJBlockD` gives an
operation of `catMemB` has its operations in `opMemB` and its result types of positive
width, and `map?` keeps the operations of the blocks it splices.

## Main definitions

* `widthPos`, `bindPosB` — the Jasmin types of positive width, and the Jasmin operations
  whose result type is of positive width.
* `catMemB` — the operations of `catCryptDialect` whose blocks have their operations in
  `opMemB` and their result types of positive width.
* `nfWidthPos`, `NFTysPos` — the types of the typed front of positive width, and the
  programs all of whose types are of positive width.
* `OpResMem` — every expression of the translation of an operation is at an operation of
  `catMemB`.

## Main results

* `coveredCom_rename`, `allOps_spliceNF?`, `allOps_map?` — renaming, splicing and `map?`
  keep an operation predicate that holds of every lowered block.
* `catMemB_block` — the block of an operation of `catMemB` has its operations in `opMemB`
  and its result types of positive width.
* `catToJasmin_allOps_of_catMemB` — the conversion of a program with operations in
  `catMemB` has its operations in `opMemB`, at result types of positive width.
* `scalarBinOf_width` — the widths of the binary scalar calls lie in `(0, 64]`.
* `nfToCatExt_allOps_catMemB` — the translation of a unit-free program has its operations
  in `catMemB`.
* `catToJasmin_allOps_opMemB` — the conversion of the translation of a unit-free program
  has its operations in `opMemB`, at result types of positive width.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (toJBlockD toJExprD toJMultiD)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy Ctx)

/-! ## 0. Positive widths -/

/-- The Jasmin types of positive width: a register of a positive width, and every type other
    than a register. -/
def widthPos : JasminTy → Bool
  | .reg w => decide (0 < w)
  | _ => true

/-- The Jasmin operations whose result type is of positive width. -/
def bindPosB (op : JasminOp) : Bool :=
  widthPos (DialectSignature.ret (d := jasminDialect) op)

/-! ## 1. Operations through renaming, splicing and `map?` -/

/-- A renaming keeps the operations of a block. -/
theorem coveredCom_rename {d : Dialect} [DialectSignature d] (Q : d.Op → Bool) :
    {Γ Γ' : Ctxt d} → {t : d.Ty} → (h : Ctxt.Hom Γ Γ') → (c : Com d Γ t) →
      CoveredCom (fun e => Q e.op = true) c →
        CoveredCom (fun e => Q e.op = true) (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => ⟨hc.1, coveredCom_rename Q h.lift body hc.2⟩

section Generic

variable {d d' : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d] [DialectSignature d'] [TyDenote d'.Ty] [HasWord64 d'] [HasBoolBit d']

/-- Casting the first result type keeps the operations of a program. -/
theorem allOps_castRetHead (Q : d.Op → Bool) {Δ : Ctxt d} {a b : d.Ty} {ts : List d.Ty}
    (h : a = b) (p : NFProg d Δ (a :: ts)) :
    (NFProg.castRetHead h p).allOps Q = p.allOps Q := by
  subst h; rfl

/-- A block whose operations satisfy `Q`, spliced in front of continuations whose programs
    have their operations in `Q`, gives a program with its operations in `Q`. -/
theorem allOps_spliceNF? (Q : d.Op → Bool) {ts : List d.Ty} :
    {Δ : Ctxt d} → {a : d.Ty} → (blk : Com d Δ a) →
    (k : {Δ' : Ctxt d} → Ctxt.Hom Δ Δ' → Ctxt.Var Δ' a → Option (NFProg d Δ' ts)) →
    CoveredCom (fun e => Q e.op = true) blk →
    (∀ {Δ' : Ctxt d} (ren : Ctxt.Hom Δ Δ') (res : Ctxt.Var Δ' a) (q : NFProg d Δ' ts),
      k ren res = some q → q.allOps Q = true) →
    ∀ q, NFProg.spliceNF? blk k = some q → q.allOps Q = true
  | _, _, .ret v, _, _, hk, q, hq => hk _ v q hq
  | _, _, .var _ blk, _, hb, hk, q, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨hb.1, allOps_spliceNF? Q blk _ hb.2 (fun _ res q h => hk _ res q h) q' hq'⟩

/-- **The operations of a lowered program.** If every block the partial lowering `P` gives a
    let-bound expression of `p` has its operations in `Q`, every program `map?` returns for
    `p` has its operations in `Q`. -/
theorem allOps_map? (P : PartialBlockLowering d d') (hT : P.RegionTypes) (Q : d'.Op → Bool)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.Covered (fun e => ∀ blk, P.lowerExprBlock? e = some blk →
      CoveredCom (fun e' => Q e'.op = true) blk)) :
    ∀ {Δ : Ctxt d'} (ren : Ctxt.Hom (P.mapCtx Γ) Δ) (q : NFProg d' Δ (ts.map P.mapTy)),
      NFProg.map? P hT p ren = some q → q.allOps Q = true := by
  induction p with
  | ret => intro _ _ q hq; cases hq; rfl
  | var e k ih =>
      intro _ ren q hq
      obtain ⟨blk, hblk, hq⟩ := Option.bind_eq_some_iff.mp hq
      exact allOps_spliceNF? Q _ _ (coveredCom_rename Q ren blk (hp.1 blk hblk))
        (fun _ _ q' h => ih hp.2 _ q' h) q hq
  | forLoop _ _ _ _ ihb ihk =>
      intro _ ren q hq
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨ihb hp.1 _ b hb, ihk hp.2 _ k' hk⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro _ ren q hq
      obtain ⟨a, ha, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨⟨iht hp.1 _ a ha, ihe hp.2.1 _ b hb⟩, ihk hp.2.2 _ k' hk⟩
  | whileLoop _ _ _ ihb ihk =>
      intro _ ren q hq
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      refine ⟨?_, ihk hp.2 _ k' hk⟩
      rw [allOps_castRetHead]
      exact ihb hp.1 _ b hb
  | call _ _ _ ih =>
      intro _ ren q hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact ih hp _ k' hk

end Generic

/-! ## 2. The operations of `catCryptDialect` with blocks in `opMemB` -/

/-- The operations of `catCryptDialect` whose blocks under `toJBlockD` have their operations
    in `opMemB` and their result types of positive width: the word arithmetic, the carries,
    the equality, the selection of words, the dynamic memory accesses, the bit constants, the
    negation, conjunction, disjunction, exclusive or and equality of bits, a constant, an
    immediate shift by less than `2 ^ w`, each with a result type that `catToJasmin` maps to
    a type of positive width. -/
def catMemB (op : CatCryptOp) : Bool :=
  (match op with
    | .bvAdd _ | .bvSub _ | .bvMul _ | .bvAnd _ | .bvOr _ | .bvXor _ | .bvMulHi _
    | .bvShiftLV _ | .bvShiftRV _ | .bvAddCarryLo _ | .bvAddCarryHi _ | .bvEq _
    | .memrefGetDyn _ | .memrefSetDyn _ | .not | .and | .or | .xor | .eqBit | .constBit _
    | .ite (.sword _) => true
    | .bvConst w _ => decide (0 < w)
    | .bvShiftL w k | .bvShiftR w k => decide (k < 2 ^ w)
    | _ => false) &&
  widthPos (catToJasmin.mapTy (DialectSignature.ret (d := catCryptDialect) op))

/-- **The block of an operation of `catMemB` has its operations in `opMemB` and its result
    types of positive width.** -/
theorem catMemB_block {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (he : catMemB e.op = true) (blk : Com jasminDialect _ _)
    (hb : toJBlockD e = some blk) :
    CoveredCom (fun e' => (opMemB e'.op && bindPosB e'.op) = true) blk := by
  obtain ⟨op, hr, args⟩ := e
  subst hr
  simp only [catMemB, Bool.and_eq_true] at he
  obtain ⟨he, hw⟩ := he
  cases op
  case ite t =>
    cases t <;> simp at he
    cases hb
    simp only [CoveredCom, and_true, Bool.and_eq_true]
    exact ⟨rfl, hw⟩
  all_goals simp at he
  all_goals
    cases hb
    simp only [CoveredCom, and_true, Bool.and_eq_true]
    exact ⟨by simp [opMemB, DialectToJasminCom.mkBin, *], hw⟩

/-- A program whose operations satisfy `Q` is covered by the expressions whose operation
    satisfies `Q`. -/
theorem covered_of_allOps {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] (Q : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts)
    (hp : p.allOps Q = true) : p.Covered (fun e => Q e.op = true) := by
  induction p with
  | ret => trivial
  | var e k ih =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      exact ⟨hp.1, ih hp.2⟩
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      exact ⟨iht hp.1.1, ihe hp.1.2, ihk hp.2⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      exact ⟨ihb hp.1, ihk hp.2⟩
  | call _ _ _ ih => exact ih hp

/-- **The conversion to the Jasmin dialect of a program with operations in `catMemB` has its
    operations in `opMemB`, each with a result type of positive width.** -/
theorem catToJasmin_allOps_of_catMemB {Γ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (p : NFProg catCryptDialect Γ ts) (hp : p.allOps catMemB = true)
    {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (catToJasmin.mapCtx Γ) Δ)
    (q : NFProg jasminDialect Δ (ts.map catToJasmin.mapTy))
    (hq : NFProg.map? catToJasmin catToJasmin_regionTypes p ren = some q) :
    q.allOps (fun op => opMemB op && bindPosB op) = true :=
  allOps_map? catToJasmin catToJasmin_regionTypes (fun op => opMemB op && bindPosB op) p
    ((covered_of_allOps (d := catCryptDialect) catMemB p hp).mono fun e he blk hb => catMemB_block e he blk hb)
    ren q hq

/-! ## 3. The operations of the typed front -/

section Front

open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.NFToCat

/-- The types of the typed front of positive width: a word of a positive width, and every
    type other than a word. -/
def nfWidthPos : NfTy → Bool
  | .word w => decide (0 < w)
  | _ => true

/-- The programs of the typed front whose types are of positive width: the types of the
    let-bindings, the carried tuples, the results of the branches and the argument and result
    types of the calls, in every region. -/
def NFTysPos : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var (t := t) _ k => nfWidthPos t = true ∧ NFTysPos k
  | _, _, .forLoop (cs := cs) _ _ body k =>
      cs.all nfWidthPos = true ∧ NFTysPos body ∧ NFTysPos k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      rs.all nfWidthPos = true ∧ NFTysPos thn ∧ NFTysPos els ∧ NFTysPos k
  | _, _, .whileLoop (cs := cs) _ body k =>
      cs.all nfWidthPos = true ∧ NFTysPos body ∧ NFTysPos k
  | _, _, .call (as := as) (rs := rs) _ _ k =>
      as.all nfWidthPos = true ∧ rs.all nfWidthPos = true ∧ NFTysPos k

/-- The widths of the binary calls of the scalar table lie in `(0, 64]`. -/
theorem scalarBinOf_width {f : String} {o : ImpToNF.ScalarBin} {w : Nat}
    (h : ImpToNF.scalarBinOf f = some (o, w)) : 0 < w ∧ w ≤ 64 := by
  unfold ImpToNF.scalarBinOf at h
  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.mp h
  have hall : ∀ x ∈ ImpToNF.hax64BinTable, 0 < x.2.2 ∧ x.2.2 ≤ 64 := by decide
  have := hall x (List.mem_of_find?_eq_some hx)
  rw [hxe] at this
  exact this

/-- Every expression of the translation of an operation has an operation in `catMemB`. -/
def OpResMem : {Δ : Ctxt catCryptDialect} → {t : NfTy} → OpRes Δ t → Prop
  | _, _, .rd _ => True
  | _, _, .expr e => catMemB e.op = true
  | _, _, .expr1 _ e => catMemB e.op = true
  | _, _, .bind _ e k => catMemB e.op = true ∧ OpResMem k

theorem scalarCatExpr_mem {Δ : Ctxt catCryptDialect} {f : String}
    {a b : Ctxt.Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : scalarCatExpr f a b = some e) : catMemB e.op = true := by
  unfold scalarCatExpr at h
  split at h <;> first | (cases h; rfl) | cases h

theorem selectCat_mem {Δ : Ctxt catCryptDialect} {f : String} {tc ta tb : NfTy}
    {args : HVector (fun t => Ctxt.Var Δ t) ([tc, ta, tb].map catTy)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : selectCat f tc ta tb args = some e) :
    catMemB e.op = true := by
  unfold selectCat at h
  split at h
  · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  · cases h

theorem catCall?_mem {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {args : HVector (fun t => Ctxt.Var Δ t) (as.map catTy)}
    {e : Expr catCryptDialect Δ (catTy r)}
    (h : catCall? f as r args = some e) : catMemB e.op = true := by
  unfold catCall? at h
  split at h
  · split at h
    · obtain ⟨⟨n, a⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact scalarCatExpr_mem h
  · split at h
    · obtain ⟨⟨n, m⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp h
        rfl
      · cases h
    · cases h
  · exact selectCat_mem h
  · exact selectCat_mem h
  · cases h

theorem shiftImm?_mem {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {e : Expr catCryptDialect Δ (catTy r)}
    (h : shiftImm? f as r rs = some e) : catMemB e.op = true := by
  unfold shiftImm? at h
  split at h
  · split at h
    · split at h
      · rename_i k _ hk
        obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · cases h
          simp only [catMemB, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, rfl⟩
        · split at h
          · cases h
            simp only [catMemB, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨by omega, rfl⟩
          · cases h
      · cases h
    · cases h
  · cases h

theorem catCallRd0_mem {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : catCallRd0 f as r rs = some res) : OpResMem res := by
  unfold catCallRd0 at h
  split at h
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact catCall?_mem he
  · split at h
    · rename_i e he
      cases h
      exact shiftImm?_mem he
    · exact pinRes_elim (M := fun _ res => OpResMem res)
        (fun _ _ _ _ he => by simp only [OpResMem]; exact catCall?_mem he)
        (fun _ c _ _ ih => by
          simp only [OpResMem]
          exact ⟨rfl, ih⟩) _ rs res h

theorem binE_mem {Δ : Ctxt catCryptDialect} {o : ImpToNF.ScalarBin}
    {a b : Ctxt.Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : binE o a b = some e) : catMemB e.op = true := by
  cases o <;> first | (cases h; rfl) | cases h

theorem maskRes_mem {Δ : Ctxt catCryptDialect} (w : Nat)
    {e : Expr catCryptDialect Δ (.sword 64)} (h : catMemB e.op = true) :
    OpResMem (maskRes w e) := by
  unfold maskRes
  split
  · exact h
  · exact ⟨h, rfl, rfl⟩

theorem binChain_mem {Δ : Ctxt catCryptDialect} {o : ImpToNF.ScalarBin} {w : Nat}
    {a b : Ctxt.Var Δ (.sword 64)} {res : OpRes Δ (.word 64)}
    (h : binChain o w a b = some res) : OpResMem res := by
  unfold binChain at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact maskRes_mem w (binE_mem he)

theorem rotChain_mem {Δ : Ctxt catCryptDialect} (right : Bool) {w : Nat} (k : Nat)
    (hw : 0 < w ∧ w ≤ 64) (a : Ctxt.Var Δ (.sword 64)) :
    OpResMem (rotChain right w k a) := by
  have hj : k % w < 2 ^ 64 := by
    have := Nat.mod_lt k hw.1
    omega
  have hj' : w - k % w < 2 ^ 64 := by omega
  cases right <;>
    exact ⟨rfl, rfl,
      (Bool.and_eq_true _ _).mpr ⟨by simpa using hj, rfl⟩,
      (Bool.and_eq_true _ _).mpr ⟨by simpa using hj', rfl⟩, rfl, rfl⟩

theorem rotVarChain_mem {Δ : Ctxt catCryptDialect} (right : Bool) (w : Nat)
    (a b : Ctxt.Var Δ (.sword 64)) : OpResMem (rotVarChain right w a b) := by
  cases right <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem notChain_mem {Δ : Ctxt catCryptDialect} (w : Nat) (a : Ctxt.Var Δ (.sword 64)) :
    OpResMem (notChain w a) := by
  unfold notChain
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem unChain_mem {Δ : Ctxt catCryptDialect} (o : ImpToNF.ScalarUn) (w : Nat)
    (a : Ctxt.Var Δ (.sword 64)) : OpResMem (unChain o w a) := by
  cases o
  · exact notChain_mem w a
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem geChain_mem {Δ : Ctxt catCryptDialect} (c : BitVec 1) (x y : Ctxt.Var Δ (.sword 64)) :
    OpResMem (geChain c x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cmpChain_mem {Δ : Ctxt catCryptDialect} (c : ImpToNF.ScalarCmp)
    (x y : Ctxt.Var Δ (.sword 64)) : OpResMem (cmpChain c x y) := by
  cases c
  case eq => exact (rfl : catMemB (.bvEq 64) = true)
  case ne => exact ⟨rfl, rfl⟩
  all_goals exact geChain_mem _ _ _

theorem withVar1_mem {Δ : Ctxt catCryptDialect} {r ta : NfTy} {ra : Rd Δ ta}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Ctxt.Var Δ' (.sword 64) → Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x : Ctxt.Var Δ' (.sword 64)) (res : OpRes Δ' r),
      k x = some res → OpResMem res)
    {res : OpRes Δ r} (h : withVar1 ta ra k = some res) : OpResMem res := by
  unfold withVar1 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact hk x _ h
  · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, hk _ _ hr⟩

theorem withVar2_mem {Δ : Ctxt catCryptDialect} {r ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Ctxt.Var Δ' (.sword 64) → Ctxt.Var Δ' (.sword 64) →
      Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x y : Ctxt.Var Δ' (.sword 64)) (res : OpRes Δ' r),
      k x y = some res → OpResMem res)
    {res : OpRes Δ r} (h : withVar2 ta tb ra rb k = some res) : OpResMem res := by
  unfold withVar2 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact hk x y _ h
  · obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, hk _ _ _ hr⟩
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, hk _ _ _ hr⟩
  · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl, hk _ _ _ hr⟩

theorem bitRes2_mem {Δ : Ctxt catCryptDialect} {f : String} {ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb} {res : OpRes Δ .bit} (h : bitRes2 f ta tb ra rb = some res) :
    OpResMem res := by
  unfold bitRes2 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o, -, h⟩ := Option.bind_eq_some_iff.mp h
    cases o <;> cases h
    · exact (rfl : catMemB .and = true)
    · exact (rfl : catMemB .or = true)
    · exact (rfl : catMemB .eqBit = true)
    · exact (rfl : catMemB .xor = true)
  · cases h

theorem bitRes1_mem {Δ : Ctxt catCryptDialect} {f : String} {ta : NfTy} {ra : Rd Δ ta}
    {res : OpRes Δ .bit} (h : bitRes1 f ta ra = some res) : OpResMem res := by
  unfold bitRes1 at h
  split at h
  · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      exact (rfl : catMemB .not = true)
    · cases h
  · cases h

theorem scalarRes2_mem {Δ : Ctxt catCryptDialect} {f : String} {ta tb : NfTy} {ra : Rd Δ ta}
    {rb : Rd Δ tb} {r : NfTy} {res : OpRes Δ r} (h : scalarRes2 f ta tb ra rb r = some res) :
    OpResMem res := by
  unfold scalarRes2 at h
  split at h
  · obtain ⟨⟨o, w⟩, how, h⟩ := Option.bind_eq_some_iff.mp h
    have hw := scalarBinOf_width how
    dsimp only at h
    split at h
    · split at h
      · exact withVar1_mem (fun x res hx => by cases hx; exact rotChain_mem _ _ hw _) h
      · exact withVar2_mem (fun x y res hx => by cases hx; exact rotVarChain_mem _ _ _ _) h
    · exact withVar2_mem (fun x y res hx => binChain_mem hx) h
  · split at h
    · exact bitRes2_mem h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    exact withVar2_mem (fun x y res hx => by cases hx; exact cmpChain_mem _ _ _) h
  · cases h

theorem scalarRes1_mem {Δ : Ctxt catCryptDialect} {f : String} {ta : NfTy} {ra : Rd Δ ta}
    {r : NfTy} {res : OpRes Δ r} (h : scalarRes1 f ta ra r = some res) : OpResMem res := by
  unfold scalarRes1 at h
  split at h
  · obtain ⟨⟨o, w⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp h
      trivial
    · exact withVar1_mem (fun x res hx => by cases hx; exact unChain_mem _ _ _) h
  · exact bitRes1_mem h
  · cases h

theorem scalarRes?_mem {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : scalarRes? f as r rs = some res) : OpResMem res := by
  rcases rs with _ | ⟨ra, _ | ⟨rb, _ | ⟨rc, rest⟩⟩⟩
  · cases h
  · exact scalarRes1_mem h
  · exact scalarRes2_mem h
  · cases h

theorem catCallRd_mem {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r}
    (h : catCallRd f as r rs = some res) : OpResMem res := by
  unfold catCallRd at h
  split at h
  · rename_i res' h0
    cases h
    exact catCallRd0_mem h0
  · exact scalarRes?_mem h

theorem tripRes_mem {Δ : Ctxt catCryptDialect} (r : Rd Δ (.word 64)) :
    OpResMem (tripRes r) := by
  cases r
  · trivial
  · exact (rfl : catMemB (.bvConst 64 _) = true)

theorem ctrRes_mem {Δ : Ctxt catCryptDialect} {rlo : Rd Δ .int} {ri : Rd Δ (.word 64)}
    {res : OpRes Δ (.word 64)} (h : ctrRes rlo ri = some res) : OpResMem res :=
  withVar2_mem (fun _ _ _ hk => by cases hk; exact (rfl : catMemB (.bvAdd 64) = true)) h

theorem satSubRes_mem {Δ : Ctxt catCryptDialect} (x y : Ctxt.Var Δ (.sword 64)) :
    OpResMem (satSubRes x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tripSub_mem {Δ : Ctxt catCryptDialect} {rlo : Rd Δ .int} {rhi : Rd Δ (.word 64)}
    {res : OpRes Δ (.word 64)} (h : tripSub rlo rhi = some res) : OpResMem res := by
  unfold tripSub at h
  split at h
  · cases h
    exact (rfl : catMemB (.bvConst 64 _) = true)
  · exact withVar2_mem (fun x y _ hk => by cases hk; exact satSubRes_mem x y) h

/-- Every expression of the translation `catOp` of an operation whose result type is not
    `unit` has an operation in `catMemB`. -/
theorem catOp_mem {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (op : NfOp) (hu : op.ret ≠ .unit) (args : HVector (fun t => Ctxt.Var Γ t) op.sig)
    (res : OpRes Δ op.ret) (h : catOp σ op args = some res) : OpResMem res := by
  induction op with
  | named _ op ih => exact ih hu args res h
  | call f as r => exact catCallRd_mem h
  | ilit t v =>
      unfold catOp at h
      split at h
      · cases h; trivial
      · unfold uintLit? at h
        split at h
        · split at h
          · cases h; exact (rfl : catMemB (.bvConst 64 _) = true)
          · cases h
        · cases h
  | ctr =>
      unfold catOp at h
      split at h
      · cases h; trivial
      · exact ctrRes_mem h
  | trip t =>
      unfold catOp at h
      split at h
      · obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact tripRes_mem r'
      · obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.mp h
        exact tripSub_mem h
  | bin o w =>
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      change binRes? o w (σ a) (σ b) = some res at h
      unfold binRes? at h
      split at h
      · obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
        exact withVar2_mem (fun _ _ _ hk => binChain_mem hk) h
      · cases h
  | constBit b =>
      cases h
      exact (rfl : catMemB (.constBit b) = true)
  | constUnit => exact absurd rfl hu
  | _ => cases h

/-- The bindings `emitRes` gives a translation with operations in `catMemB`, in front of a
    continuation whose programs have their operations in `catMemB`, form such a program. -/
theorem emitRes_allOps {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q →
        q.allOps catMemB = true) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), OpResMem res →
      emitRes cont h res σ = some q → q.allOps catMemB = true
  | _, _, _, .rd _, _, q, _, hq => hcont _ q hq
  | _, _, _, .expr _, _, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨hr, hcont _ k' hk'⟩
  | _, _, _, .expr1 _ _, _, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨rfl, hr, hcont _ k' hk'⟩
  | _, _, h, .bind _ _ rest, σ, _, hr, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨hr.1, emitRes_allOps hcont h rest σ.wk k' hr.2 hk'⟩

/-- The `bvConst` bindings of `pinAll` in front of a program `k` gives with operations in
    `catMemB` form such a program. -/
theorem pinAll_allOps {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Ctxt.Var Δ' t) (ts.map catTy) →
        Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Ctxt.Var Δ' t) (ts.map catTy))
      (q : NFProg catCryptDialect Δ' us), k σ' ws = some q → q.allOps catMemB = true)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k σ rs = some q) :
    q.allOps catMemB = true :=
  pinAll_elim (M := fun {_} _ _ q => q.allOps catMemB = true)
    (fun σ _ ws q _ hq => hk σ ws q hq)
    (fun _ _ _ _ _ ih => by
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨rfl, ih⟩) σ rs q h

/-- **The operations of a translated unit-free program lie in `catMemB`.** A program
    `nfToCatExt D` returns for a unit-free program has, at every let-binding of the program
    and of its regions, an operation of `catMemB`. -/
theorem nfToCatExt_allOps_catMemB (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hu : NFFlattenTuples.UnitFree p) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → q.allOps catMemB = true := by
  induction p with
  | ret vs =>
      intro _ σ q h
      refine pinAll_allOps ?_ σ _ q h
      intro _ _ _ q' hq'
      cases hq'
      rfl
  | var e k ih =>
      intro _ σ q h
      rcases e with ⟨op, he, args⟩
      obtain ⟨-, hop, hk⟩ := hu
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op he args = some q at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_allOps (fun σ' q' hq' => ih hk σ' q' hq') he res σ q
          (catOp_mem σ op hop args res hres) h
      · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
        refine pinAll_allOps ?_ σ _ q h
        intro _ _ _ q' hq'
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
        exact ih hk _ k' hk'
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro _ σ q h
      obtain ⟨-, hb, hk⟩ := hu
      refine pinAll_allOps (ts := .word 64 :: cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb', hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [NFProg.allOps, Bool.and_eq_true]
      exact ⟨ihb hb _ b' hb', ihk hk _ k' hk'⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ σ q h
      obtain ⟨-, ht, he, hk⟩ := hu
      simp only [nfToCatExt] at h
      split at h
      · obtain ⟨t', ht', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨⟨iht ht _ t' ht', ihe he _ e' he'⟩, ihk hk _ k' hk'⟩
      · cases h
  | whileLoop => intro _ σ q h; cases h
  | call => intro _ σ q h; cases h

/-- **`catToJasmin_allOps_opMemB`: the Jasmin image of a translated unit-free program has
    its operations in `opMemB`, each with a result type of positive width.** For a unit-free
    program `p`, a program `nfToCatExt D` returns for `p`, and a program `map?` along
    `catToJasmin` returns for it, every let-binding of the result, in every region, has an
    operation of `opMemB` whose result type is of positive width. -/
theorem catToJasmin_allOps_opMemB (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hu : NFFlattenTuples.UnitFree p)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy))
    (hq : nfToCatExt D p σ = some q) {Δ' : Ctxt jasminDialect}
    (ren : Ctxt.Hom (catToJasmin.mapCtx Δ) Δ')
    (r : NFProg jasminDialect Δ' ((ts.map catTy).map catToJasmin.mapTy))
    (hr : NFProg.map? catToJasmin catToJasmin_regionTypes q ren = some r) :
    r.allOps (fun op => opMemB op && bindPosB op) = true :=
  catToJasmin_allOps_of_catMemB q (nfToCatExt_allOps_catMemB D p hu σ q hq) ren r hr

end Front

end CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps
