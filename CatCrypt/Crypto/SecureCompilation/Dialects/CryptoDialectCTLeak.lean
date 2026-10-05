/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# The constant-time leakage of `catCryptDialect`

The instance of `ComLevelCheck.LeakModel` for `catCryptDialect`:

* the dynamic-index memref accesses (`memrefGetDyn`, `memrefSetDyn`,
  `memrefGetDyn128`, `memrefWGetDyn`, `memrefWSetDyn`) leak their index argument
  (position `1`) as a memory offset;
* the opaque array leaves `extCall "arrLoadDyn"` / `extCall "arrStoreDyn"`, which
  the front emits for an array access outside the memref word ABI, leak their last
  argument, the index;
* a leaf call of any other name is quiet when the model lists the name (`leafQuiet`) and
  leaks its argument values otherwise;
* an operation the model maps to a variable-time instruction (`opVT`) leaks its
  argument values as that instruction's operands;
* every other operation is quiet: the static-index memref accesses address a
  constant offset, and `ite` is a select of values.

`ownedQuietLeaf` is the list of quiet leaf names of the owned route: the names the
`LowCT` front reserves for a select of values and for an access at a literal index.

A value reads as a natural number by its bits (`sword`, `bit`) and as `0`
otherwise (`valNat`).

`catCT`, `catLevelCheck` and `catLevelCheck_sound` are the constant-time
predicate, the level checker and its soundness at this model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (X86Mnem)

/-- The parameters of the dialect leakage: the leaf calls classed quiet (every leaf call
    of another name is variable time) and the operations lowered to a variable-time
    instruction. -/
structure CatLeakParams where
  leafQuiet : String → Bool := fun _ => false
  opVT : CatCryptOp → Option X86Mnem := fun _ => none

/-- The quiet leaf names of the owned route: `select`, a select of values, and the names
    with prefix `tupleLoad:`, `arrLoad:` or `arrStore:`, an access at the literal index the
    name carries. The `LowCT` front emits these names for `RSelect`, `RTupleLoad`,
    `RArrLoadLit` and `RArrStoreLit`. -/
def ownedQuietLeaf (f : String) : Bool :=
  f == "select" || "tupleLoad:".toList.isPrefixOf f.toList ||
    "arrLoad:".toList.isPrefixOf f.toList || "arrStore:".toList.isPrefixOf f.toList

/-- The leaf `select` is a quiet leaf of the owned route. -/
@[simp] theorem ownedQuietLeaf_select : ownedQuietLeaf "select" = true := by decide

/-- A name with prefix `tupleLoad:` is a quiet leaf of the owned route. -/
@[simp] theorem ownedQuietLeaf_tupleLoad (s : String) :
    ownedQuietLeaf ("tupleLoad:" ++ s) = true := by
  simp [ownedQuietLeaf, String.toList_append]

/-- A name with prefix `arrLoad:` is a quiet leaf of the owned route. -/
@[simp] theorem ownedQuietLeaf_arrLoad (s : String) :
    ownedQuietLeaf ("arrLoad:" ++ s) = true := by
  simp [ownedQuietLeaf, String.toList_append]

/-- A name with prefix `arrStore:` is a quiet leaf of the owned route. -/
@[simp] theorem ownedQuietLeaf_arrStore (s : String) :
    ownedQuietLeaf ("arrStore:" ++ s) = true := by
  simp [ownedQuietLeaf, String.toList_append]

/-- The parameters of the owned x86 route: the quiet leaves `ownedQuietLeaf` and no
    operation lowered to a variable-time instruction. -/
def CatLeakParams.owned : CatLeakParams := { leafQuiet := ownedQuietLeaf }

/-- The event class of an operation. The match lists every constructor of `CatCryptOp`: the
    dynamic-index accesses leak their index, a leaf call is quiet when `P.leafQuiet` lists
    its name and variable time otherwise, and each remaining operation is classed by
    `P.opVT`. The dialect has no division and no arithmetic shift right by a register count;
    `bvShiftRA` shifts by an immediate. -/
def catKind (P : CatLeakParams) (op : CatCryptOp) : LeakKind :=
  match op with
  | .memrefGetDyn _ | .memrefSetDyn _ | .memrefGetDyn128 _
  | .memrefWGetDyn _ _ | .memrefWSetDyn _ _ => .addrAt 1
  | .extCall name argTys _ =>
      if name = "arrLoadDyn" ∨ name = "arrStoreDyn" then .addrAt (argTys.length - 1)
      else if P.leafQuiet name then .quiet
      else .vtCall name
  | .constBit _ | .constUnit | .xor | .and | .or | .not | .eqBit
  | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _
  | .bvConst _ _ | .bvXor _ | .bvAnd _ | .bvOr _ | .bvNot _ | .bvAdd _ | .bvSub _ | .bvMul _
  | .bvEq _ | .bvShiftL _ _ | .bvShiftR _ _ | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _
  | .andn _ | .bvShiftLV _ | .bvShiftRV _ | .bvAdd64 _ | .bvAdc _ | .bvMulHi _
  | .bvAddCarryLo _ | .bvAddCarryHi _ | .ite _ | .bitToSword _
  | .memrefZero _ | .memrefSet _ _ | .memrefGet _ _
  | .sampleBit | .sampleBv _ | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _
  | .vpslldqC _ | .vconst128 _ | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2 =>
      match P.opVT op with
      | some m => .vt m
      | none => .quiet

/-- The array leaf `arrLoadDyn` leaks its last argument. -/
@[simp] theorem catKind_extCall_arrLoadDyn (P : CatLeakParams) (argTys : List CryptoTy)
    (r : CryptoTy) :
    catKind P (.extCall "arrLoadDyn" argTys r) = .addrAt (argTys.length - 1) := by
  simp [catKind]

/-- The array leaf `arrStoreDyn` leaks its last argument. -/
@[simp] theorem catKind_extCall_arrStoreDyn (P : CatLeakParams) (argTys : List CryptoTy)
    (r : CryptoTy) :
    catKind P (.extCall "arrStoreDyn" argTys r) = .addrAt (argTys.length - 1) := by
  simp [catKind]

/-- A leaf call of a name `P.leafQuiet` lists, other than the two array leaves, is
    quiet. -/
theorem catKind_extCall_quiet {P : CatLeakParams} {name : String}
    (hl : name ≠ "arrLoadDyn") (hs : name ≠ "arrStoreDyn") (hq : P.leafQuiet name = true)
    (argTys : List CryptoTy) (r : CryptoTy) :
    catKind P (.extCall name argTys r) = .quiet := by
  simp [catKind, hl, hs, hq]

/-- A leaf call of a name `P.leafQuiet` does not list, other than the two array leaves, is
    a variable-time leaf call. -/
theorem catKind_extCall_vt {P : CatLeakParams} {name : String}
    (hl : name ≠ "arrLoadDyn") (hs : name ≠ "arrStoreDyn") (hq : P.leafQuiet name = false)
    (argTys : List CryptoTy) (r : CryptoTy) :
    catKind P (.extCall name argTys r) = .vtCall name := by
  simp [catKind, hl, hs, hq]

/-- The natural-number reading of a dialect value. -/
def catValNat: (t : CryptoTy) → ⟦t⟧ → Nat
  | .sword _, w => w.toNat
  | .bit, b => b.toNat
  | _, _ => 0

/-- The leakage model of `catCryptDialect` at the parameters `P`. -/
def catLeakModel (P : CatLeakParams) : LeakModel catCryptDialect where
  kind := catKind P
  valNat := catValNat

/-- Constant time of a `catCryptDialect` program for the entry labels `L`. -/
abbrev catCT (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (L : Labels Γ) (c : Com catCryptDialect Γ t) : Prop :=
  ComCT (catLeakModel P) L c

/-- The level checker at the dialect leakage. -/
abbrev catLevelCheck (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (L : Labels Γ) : Bool :=
  Com.levelCheck (catLeakModel P) c L

/-- A program the checker accepts is constant time for its entry labels. -/
theorem catLevelCheck_sound (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (L : Labels Γ) (h : catLevelCheck P c L = true) :
    catCT P L c :=
  levelCheck_sound _ c L h

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
