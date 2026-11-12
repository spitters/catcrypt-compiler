/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Loops
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.IterModel
import all Init.Internal.Order.Basic
public import HaxAscent.RustSemantics.BackendLoops
public meta import Lean.Elab.Term
public meta import Lean.Meta.Eqns

/-!
# `reifyAeneas%`: NF programs of Aeneas functions with proofs by construction

`reifyAeneas% f` reads the body of an Aeneas function `f` (output of the Aeneas Lean backend,
elaborated over `HaxLean.AeneasBackendPrelude`) as an NF program `p` and proves, for every
argument, that a value of `f` is, embedded, the value of the reading `nfToRustM p` at the
embedded arguments. Composed with the simulation of `AeneasFront/NFToRustM.lean`, a value of
`f` is the denotation of `p` in the compiler's semantics `PDenP hax64WExit`.

The proof is built by construction. The judgement `Reify m V p` (a value of the Aeneas
computation `m` is the value of `nfToRustM p V`) and its expression form `ReifyE m V e` are
type classes; each construct of the source has one instance, an instance of a congruence
lemma proved once:

* a bind `m >>= k`: `Reify.bind`, `Reify.bindLit` (a literal operand is bound first);
* a value `ok x`, `ok (op x y)`: `Reify.okVar`, `Reify.okExpr`, `Reify.okLit`;
* a branch `if x < y then a else b` on unsigned words: `Reify.iteLt`; a branch on any other
  condition that `ReadBit` reads (the other comparisons, connectives, the signed comparisons
  of `AeneasFront/Signed.lean`): `Reify.iteBit`;
* a panic guard, `massert P`, `if c then k else fail e` and `if c then fail e else k`:
  `Reify.assert`, `Reify.iteFailElse`, `Reify.iteFail`, each an instance of `Reify.guardS`, and
  every other guard by `Reify.guardP`, of which `Reify.guardS` is itself an instance: the
  branch to the aborting arm `abortArm` that `NFProg.abortElim` eliminates; a condition read
  as one expression by the class `ReadCond` (every comparison of words of every width of at
  most `64` bits, `readCmp`, with the notations of `CmpProp`; Boolean variables; connectives of
  two Boolean variables, `readBool`; decided propositions and double negations), and any other
  condition as a prefix of bindings and a bit by the class `ReadBit`, whose connectives,
  negations and comparisons take compound operands (`readBitConn`, `readBitNot`,
  `readBitDecNot`, `readBitCmp`);
* a Boolean argument: the word `boolW b` of the layout, whose bit is bound first
  (`Reify.argBit`); a Boolean result `ok b`: the prefix of its bit followed by the bit-to-word
  step `bitWordP` (`Reify.okBit`, at the result map `bitRes`);
* an operation: the `ReifyE` instances of the checked arithmetic, the lifted bitwise
  operations, the wrapping operations, `Array.index_usize` and `Array.update`;
* a variable: `Lookup`, the position of a value in the valuation;
* an exit-flag loop `loop b init`: `Reify.loop`, a `whileLoop`;
* a range loop `loop F (⟨0, n⟩, acc)` whose body steps the range by `IteratorRange.next`:
  `Reify.rangeForLoop`, a counted `forLoop` with the bound `n` as trip count and the range index
  as trip index. Its hypothesis on the body is `range_body` (through `next_usize`) with the
  step of the body split off its final continuation by `tailCont_bind` and `tailCont_ok`; the
  loop is `foldRangeAux` of the step by `loop_range`, and the fold is the counted loop by
  `foldRange_reify`;
* a loop `loop F (st₀, acc)` over an iterator adapter (`enumerate` or `step_by` of a range,
  `enumerate` of an array, `zip` of two arrays) whose state is indexed by the trip index
  (`IndexedIter`, instances in `AeneasFront/Iterators.lean`, which the caller imports):
  `Reify.indexedForLoop`, the counted `forLoop` of the step that binds the item of the trip
  (`loop_indexed`); the adapter's state is built by binds whose value the reader computes
  (`bind_of_eq_ok`).

Instance resolution follows the syntax of the body, and the proof term it returns is the
composition of these lemmas. The elaborator unfolds only the equation lemma `f.eq_1` of the
function. There is no definitional check of the whole term.

## Main definitions

* `AeVal`: the NF type and value of an Aeneas value
* `Lookup`, `ReifyE`, `Reify`: the judgements
* `ReadCond`, `CmpProp`, `BoolForm`: the reading of a condition as one expression
* `preReads`, `ReadBit`, `ReadWord`: the reading of a condition as a prefix and a bit
* `bitWordP`, `bitRes`: the bit-to-word step and the result map of a Boolean result
* `boolW`, `wCons`: the word of a Boolean argument
* `Reified`: an NF program with its soundness statement
* `reifyAeneas%`: the elaborator

## Main results

* `Reify.bind`, `Reify.bindLit`, `Reify.okLit`, `Reify.iteLt`, `Reify.loop`: the congruence
  steps
* `Reify.guard`, `Reify.guardP`, `Reify.guardS`, `Reify.assert`, `Reify.iteFailElse`,
  `Reify.iteFail`: the guards
* `nfToRustM_plug`, `preReads_append`, `preReads_wk`, `ReifyG.plug`: prefixes
* `readBitVar`, `readBitNot`, `readBitDecNot`, `readBitDecEq`, `readBitConn`, `readBitCmp`,
  `readWordVar`, `readWordLit`: conditions with compound operands
* `aeExpr_selE`, `nfToRustM_bitWordP`, `Reify.okBit`: a Boolean result
* `readCmp`, `CmpProp.not`, `CmpOp.aen_neg`, `readBool`, `readBit`, `readNotBit`: the conditions
* `Reify.letE`, `Reify.letLit`: a binding the program reads no further
* `Reify.argBit`: a Boolean argument
* `foldRange_reify`, `range_body`, `Reify.rangeForLoop`: the range loop
* `Reify.toDenote`, `ReifyG.toDenote`: from the reading to the compiler's semantics
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll tableOf PDenP)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)
open Aeneas.Std.ScalarElab
open MultiBlockLowering (hvAppend)

/-! ## Embedding Aeneas values -/

/-- Widths of at most `64` bits, for instance resolution. -/
class Le64 (ty : UScalarTy) : Prop where
  /-- The width has at most `64` bits. -/
  le : ty.numBits ≤ 64

instance : Le64 .U8 := ⟨by decide⟩
instance : Le64 .U16 := ⟨by decide⟩
instance : Le64 .U32 := ⟨by decide⟩
instance : Le64 .U64 := ⟨by decide⟩
instance : Le64 .Usize := ⟨usize_numBits_le⟩

/-- The `64`-bit word of an Aeneas word. -/
def embW {ty : UScalarTy} (x : UScalar ty) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The NF type and value of an Aeneas value. -/
class AeVal (α : Type) where
  /-- The NF type. -/
  nty : NfTy
  /-- The NF value. -/
  emb : α → nty.denote

/-- An Aeneas word is a `64`-bit word. -/
@[reducible] instance (ty : UScalarTy) : AeVal (UScalar ty) := ⟨.word 64, embW⟩

/-- A Boolean is a bit. -/
@[reducible] instance : AeVal Bool := ⟨.bit, id⟩

/-- The unit value is the unit. -/
@[reducible] instance : AeVal Unit := ⟨.unit, fun _ => ()⟩

theorem lt64 {ty : UScalarTy} [h : Le64 ty] (x : UScalar ty) : x.val < 2 ^ 64 :=
  lt_of_lt_of_le x.hBounds (Nat.pow_le_pow_right (by decide) h.le)

theorem enc_embW {ty : UScalarTy} [Le64 ty] (x : UScalar ty) :
    enc (.word 64) (embW x) = wordV x := by
  simp only [ImpToNF.enc, embW, wordV, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt64 x)]

theorem dec_wordV {ty : UScalarTy} [Le64 ty] (z : UScalar ty) :
    dec (.word 64) (wordV z) = some (embW z) := by
  have h := lt64 z
  have h' : ((z.val : Nat) : Int) < 2 ^ 64 := by exact_mod_cast h
  simp only [dec, wordV, embW, Int.natCast_nonneg, h', and_self, ite_true, Int.toNat_natCast]

theorem readW_wordV {ty : UScalarTy} (x : UScalar ty) : readW ty (wordV x) = .ok x := by
  show litA ty (x.val : Int) = .ok x
  rw [litA_ofNat x.hBounds]
  cases x
  simp [UScalar.val]

/-- Extending a valuation is consing its value. -/
theorem extend_eq {Γ : Ctxt nfDialect} {t : NfTy} (V : Valuation Γ) (a : t.denote) :
    V.extend a = HVector.cons a V := rfl

/-- The empty valuation. -/
abbrev vNil : Valuation (d := nfDialect) [] := HVector.nil

/-- The valuation `V` with the embedded Aeneas value `x` in front. -/
abbrev vCons {α : Type} [AeVal α] {Γ : Ctxt nfDialect} (x : α) (V : Valuation Γ) :
    Valuation (d := nfDialect) (AeVal.nty α :: Γ) :=
  HVector.cons (AeVal.emb x) V

/-- The word of a Boolean argument at the System V layout: `1` for `true`, `0` for `false`. -/
def boolW (b : Bool) : BitVec 64 := BitVec.ofNat 64 b.toNat

/-- The valuation `V` with the word of the Boolean argument `b` in front. -/
abbrev wCons {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ) :
    Valuation (d := nfDialect) (.word 64 :: Γ) :=
  HVector.cons (boolW b) V

/-! ## Variables -/

/-- `v` is a variable of `Γ` at which `V` holds `a`. -/
class Lookup {Γ : Ctxt nfDialect} {t : NfTy} (V : Valuation Γ) (a : t.denote)
    (v : outParam (Var Γ t)) : Prop where
  /-- The variable reads `a`. -/
  eq : v.lookup V = a

instance lookupHere {Γ : Ctxt nfDialect} {t : NfTy} (V : Valuation Γ) (a : t.denote) :
    Lookup (Γ := t :: Γ) (HVector.cons a V) a .here := ⟨rfl⟩

instance (priority := low) lookupThere {Γ : Ctxt nfDialect} {t s : NfTy} (V : Valuation Γ)
    (a : t.denote) (b : s.denote) (v : Var Γ t) [h : Lookup V a v] :
    Lookup (Γ := s :: Γ) (HVector.cons b V) a (.there v) := ⟨h.eq⟩

/-! ## The judgements -/

/-- A value of the Aeneas computation `m` is, embedded, the value of the reading of the NF
    expression `e` at `V`. -/
class ReifyE {α : Type} [AeVal α] (m : RustM α) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (e : outParam (Expr nfDialect Γ (AeVal.nty α))) : Prop where
  /-- Soundness of the reading. -/
  sound : ∀ y, m = .ok y → aeExpr e V = .ok (AeVal.emb y)

/-- A value of the Aeneas computation `m` is, mapped by `E` to NF values, the value of the
    reading of the NF program `p` at `V`. -/
class ReifyG {α : Type} {ts : List NfTy} (E : α → Valuation (d := nfDialect) ts)
    (m : RustM α) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (p : outParam (NFProg nfDialect Γ ts)) : Prop where
  /-- Soundness of the reading. -/
  sound : ∀ y, m = .ok y → nfToRustM p V = .ok (E y)

/-- The NF result of a value: the one-element valuation of its embedding. -/
abbrev single {α : Type} [AeVal α] (y : α) : Valuation (d := nfDialect) [AeVal.nty α] :=
  .cons (AeVal.emb y) .nil

/-- A value of the Aeneas computation `m` is, embedded, the value of the reading of the NF
    program `p` at `V`. -/
abbrev Reify {α : Type} [AeVal α] (m : RustM α) {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (p : NFProg nfDialect Γ [AeVal.nty α]) : Prop :=
  ReifyG single m V p

/-- A judgement for a computation transfers along an equation, the equation lemma of the
    reified function or of a definition it calls. -/
theorem ReifyG.of_eq {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m m' : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    (h : m = m') (r : ReifyG E m' V p) : ReifyG E m V p :=
  ⟨fun y hy => r.sound y (h ▸ hy)⟩

/-- **From the reading to the compiler's semantics.** A value of an Aeneas computation read
    by `p` is, embedded, the denotation of `p` in `PDenP hax64WExit` from some fuel on. -/
theorem Reify.toDenote {α : Type} [AeVal α] {m : RustM α} {Γ : Ctxt nfDialect}
    {V : Valuation Γ} {p : NFProg nfDialect Γ [AeVal.nty α]} (r : Reify m V p) {y : α}
    (h : m = .ok y) : ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel p V = some (.cons (AeVal.emb y) .nil) :=
  nfToRustM_sim p V _ ((show ReifyG single m V p from r).sound y h)

/-- **From the reading to the compiler's semantics, at a result map.** A value of an Aeneas
    computation read by `p` with the result map `E` is, mapped by `E`, the denotation of `p` in
    `PDenP hax64WExit` from some fuel on. -/
theorem ReifyG.toDenote {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {m : RustM α} {Γ : Ctxt nfDialect} {V : Valuation Γ} {p : NFProg nfDialect Γ ts}
    (r : ReifyG E m V p) {y : α} (h : m = .ok y) : ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel p V = some (E y) :=
  nfToRustM_sim p V _ (r.sound y h)

/-! ## Calls of two words -/

/-- The NF expression calling `f` on two `64`-bit words with a result of type `r`. -/
def callE2 {Γ : Ctxt nfDialect} (f : String) (r : NfTy) (va vb : Var Γ (.word 64)) :
    Expr nfDialect Γ r :=
  ⟨.call f [.word 64, .word 64] r, rfl, .cons va (.cons vb .nil)⟩

/-- The reading of a call of two words is the reading `aeCall2` of the call on their
    encodings, decoded at the result type. -/
theorem aeExpr_callE2 {Γ : Ctxt nfDialect} {ty ty' : UScalarTy} [Le64 ty] [Le64 ty']
    (f : String) (r : NfTy) (va vb : Var Γ (.word 64)) (V : Valuation Γ) (x : UScalar ty)
    (y : UScalar ty') (hx : va.lookup V = embW x) (hy : vb.lookup V = embW y) {v : Value}
    {res : r.denote} (h : aeCall2 f (wordV x) (wordV y) = .ok v) (hd : dec r v = some res) :
    aeExpr (callE2 f r va vb) V = .ok res := by
  change aeOp (.call f [.word 64, .word 64] r) (.cons (va.lookup V) (.cons (vb.lookup V) .nil))
    = .ok res
  unfold aeOp
  rw [nfDenoteOp]
  unfold aeTable
  simp only [encAll]
  rw [hx, hy, enc_embW, enc_embW, aeCallV, h]
  simp only [hd]

/-- The checked operations at a width of `checkedTy` read their tagged name. -/
theorem aeCall2_checked {ty : UScalarTy} [h : CheckedTy ty] (o : AOp) (ho : taggedOp o = true)
    (x y : UScalar ty) :
    aeCall2 (checkedName o ty) (wordV x) (wordV y) =
      (o.aen x y >>= fun z => .ok (wordV z)) := by
  have hw : wordOpAt? (checkedName o ty) = none := by
    have := h.checked
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd this (by decide) | decide +kernel
  have hc : checkedAt? (checkedName o ty) = some (ty, o) := by
    have := h.checked
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd this (by decide) | decide +kernel
  unfold aeCall2
  rw [hw, hc]
  simp only [h.checked, ho, Bool.and_self, ite_true, readW_wordV, bind_tc_ok]

/-- The word operations of `wordAt` read their tagged name. -/
theorem aeCall2_word {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true)
    (x y : UScalar ty) :
    aeCall2 (opName o ++ uTag ty) (wordV x) (wordV y) =
      (o.aen x y >>= fun z => .ok (wordV z)) := by
  have h : wordOpAt? (opName o ++ uTag ty) = some (ty, o) := by
    cases ty <;> cases o <;> decide +kernel
  unfold aeCall2
  rw [h]
  simp only [hw, ite_true, readW_wordV, bind_tc_ok]

/-- The comparisons read their name on `u64` words. -/
theorem aeCall2_cmp {ty : UScalarTy} [Le64 ty] (c : CmpOp) (x y : UScalar ty) :
    aeCall2 c.name (wordV x) (wordV y) = .ok (.bool (c.aen x y)) := by
  have hw : wordOpAt? c.name = none := by cases c <;> decide +kernel
  have hc : checkedAt? c.name = none := by cases c <;> decide +kernel
  have hn : CmpOp.ofName? c.name = some c := by cases c <;> decide +kernel
  have rx : readW .U64 (wordV x) = .ok ⟨BitVec.ofNat 64 x.val⟩ := litA_ofNat (lt64 x)
  have ry : readW .U64 (wordV y) = .ok ⟨BitVec.ofNat 64 y.val⟩ := litA_ofNat (lt64 y)
  unfold aeCall2
  rw [hw, hc, hn]
  simp only [rx, ry, bind_tc_ok]
  have ex : (⟨BitVec.ofNat 64 x.val⟩ : U64).val = x.val := by
    simp only [UScalar.val]
    exact Nat.mod_eq_of_lt (lt64 x)
  have ey : (⟨BitVec.ofNat 64 y.val⟩ : U64).val = y.val := by
    simp only [UScalar.val]
    exact Nat.mod_eq_of_lt (lt64 y)
  cases c <;> simp only [CmpOp.aen, ex, ey]

/-! ## Expression instances -/

/-- A call of two words with an operation law: the reading of the call is the Aeneas
    operation. -/
theorem reifyE_call2 {ty : UScalarTy} [Le64 ty] {Γ : Ctxt nfDialect} (f : String)
    (op : UScalar ty → UScalar ty → RustM (UScalar ty))
    (hf : ∀ x y, aeCall2 f (wordV x) (wordV y) = (op x y >>= fun z => .ok (wordV z)))
    (x y : UScalar ty) (V : Valuation Γ) (va vb : Var Γ (.word 64))
    (hx : va.lookup V = embW x) (hy : vb.lookup V = embW y) :
    ReifyE (op x y) V (callE2 f (.word 64) va vb) where
  sound z hz := aeExpr_callE2 f _ va vb V x y hx hy (by rw [hf, hz]; rfl) (dec_wordV z)

instance reifyE_add {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (x + y) V (callE2 (checkedName .add ty) (.word 64) va vb) :=
  reifyE_call2 _ (AOp.aen .add) (aeCall2_checked .add rfl) x y V va vb hx.eq hy.eq

instance reifyE_sub {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (x - y) V (callE2 (checkedName .sub ty) (.word 64) va vb) :=
  reifyE_call2 _ (AOp.aen .sub) (aeCall2_checked .sub rfl) x y V va vb hx.eq hy.eq

instance reifyE_mul {ty : UScalarTy} [CheckedTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (x * y) V (callE2 (checkedName .mul ty) (.word 64) va vb) :=
  reifyE_call2 _ (AOp.aen .mul) (aeCall2_checked .mul rfl) x y V va vb hx.eq hy.eq

instance reifyE_band {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (lift (x &&& y)) V (callE2 (opName .band ++ uTag ty) (.word 64) va vb) :=
  reifyE_call2 _ (WordOp.aen .band) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

instance reifyE_bor {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (lift (x ||| y)) V (callE2 (opName .bor ++ uTag ty) (.word 64) va vb) :=
  reifyE_call2 _ (WordOp.aen .bor) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

instance reifyE_bxor {ty : UScalarTy} [h : TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (lift (x ^^^ y)) V (callE2 (opName .bxor ++ uTag ty) (.word 64) va vb) :=
  reifyE_call2 _ (WordOp.aen .bxor) (aeCall2_word (by simp [wordAt, h.table])) x y V va vb
    hx.eq hy.eq

/-- `reify_wrapping U` registers the wrapping operations `core.num.U.wrapping_add`,
    `wrapping_sub`, `wrapping_mul` of the backend output at the width `U` as instances of
    `reifyE_call2`: one registration per name the backend prints, no proof per width. -/
local macro "reify_wrapping " ty:ident : command => do
  let t := ty.getId
  let opI (s : String) := Lean.mkIdent (`core.num ++ t ++ Lean.Name.mkSimple s)
  let nm (s : String) := Lean.mkIdent (Lean.Name.mkSimple ("reifyE_" ++ s ++ "_" ++ t.toString))
  let tyI := Lean.mkIdent (`UScalarTy ++ t)
  `(
  /-- The wrapping addition of the backend output, an instance of `reifyE_call2`. -/
  @[instance] theorem $(nm "wrapping_add"):ident {Γ : Ctxt nfDialect} (x y : UScalar $tyI) (V : Valuation Γ)
      {va vb : Var Γ (.word 64)} [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_add") x y)) V
        (callE2 (opName .wadd ++ uTag $tyI) (.word 64) va vb) :=
    reifyE_call2 _ (WordOp.aen .wadd) (aeCall2_word (by decide)) x y V va vb hx.eq hy.eq
  /-- The wrapping subtraction of the backend output, an instance of `reifyE_call2`. -/
  @[instance] theorem $(nm "wrapping_sub"):ident {Γ : Ctxt nfDialect} (x y : UScalar $tyI) (V : Valuation Γ)
      {va vb : Var Γ (.word 64)} [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_sub") x y)) V
        (callE2 (opName .wsub ++ uTag $tyI) (.word 64) va vb) :=
    reifyE_call2 _ (WordOp.aen .wsub) (aeCall2_word (by decide)) x y V va vb hx.eq hy.eq
  /-- The wrapping multiplication of the backend output, an instance of `reifyE_call2`. -/
  @[instance] theorem $(nm "wrapping_mul"):ident {Γ : Ctxt nfDialect} (x y : UScalar $tyI) (V : Valuation Γ)
      {va vb : Var Γ (.word 64)} [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
      ReifyE (RustM.ok ($(opI "wrapping_mul") x y)) V
        (callE2 (opName .wmul ++ uTag $tyI) (.word 64) va vb) :=
    reifyE_call2 _ (WordOp.aen .wmul) (aeCall2_word (by decide)) x y V va vb hx.eq hy.eq)

reify_wrapping U8
reify_wrapping U16
reify_wrapping U32
reify_wrapping U64

/-! ## Program instances -/

/-- A literal word as an NF expression. -/
def litE {Γ : Ctxt nfDialect} {ty : UScalarTy} (c : UScalar ty) : Expr nfDialect Γ (.word 64) :=
  ⟨.ilit (.word 64) (c.val : Int), rfl, .nil⟩

/-- A natural number below `2 ^ 64` is a literal of a `64`-bit word. -/
theorem ofLit_word64 (n : Nat) (hn : n < 2 ^ 64) :
    NfTy.ofLit? (.word 64) (n : Int) = some (BitVec.ofNat 64 n) := by
  have h : (n : Int) < 2 ^ 64 := by omega
  rw [NfTy.ofLit?, ite_eq_left ⟨Int.natCast_nonneg n, h⟩, Int.toNat_natCast]

/-- An integer literal denotes its value at its type. -/
theorem nfDenoteOp_ilit (T : NfLeafTable) (t : NfTy) (v : Int)
    (xs : HVector NfTy.denote (NfOp.ilit t v).sig) :
    nfDenoteOp T (.ilit t v) xs = NfTy.ofLit? t v := by
  rw [nfDenoteOp]

/-- The reading of a literal is its value at its type. -/
theorem aeOp_ilit (t : NfTy) (v : Int) (y : t.denote) (h : NfTy.ofLit? t v = some y) :
    aeOp (.ilit t v) .nil = .ok y := by
  unfold aeOp
  rw [nfDenoteOp_ilit, h]

theorem aeExpr_litE {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty] (c : UScalar ty)
    (V : Valuation Γ) : aeExpr (litE c) V = .ok (embW c) :=
  aeOp_ilit (.word 64) (c.val : Int) (embW c) (ofLit_word64 c.val (lt64 c))

/-- `c` is the right operand of the operation `m`, read as a literal when it is no variable
    of the valuation. -/
class LitOf {α : Type} (m : RustM α) (ty : outParam UScalarTy) (c : outParam (UScalar ty)) :
    Prop

instance {ty : UScalarTy} (x c : UScalar ty) : LitOf (x + c) ty c := ⟨⟩
instance {ty : UScalarTy} (x c : UScalar ty) : LitOf (x - c) ty c := ⟨⟩
instance {ty : UScalarTy} (x c : UScalar ty) : LitOf (x * c) ty c := ⟨⟩

/-- **Bind.** A bind of an operation and a continuation is the binding of the operation's
    expression followed by the continuation's program. -/
theorem Reify.bind {α β : Type} [AeVal α] {ts : List NfTy}
    {E : β → Valuation (d := nfDialect) ts} {Γ : Ctxt nfDialect}
    {e : Expr nfDialect Γ (AeVal.nty α)} {p : NFProg nfDialect (AeVal.nty α :: Γ) ts}
    (m : RustM α) (k : α → RustM β) (V : Valuation Γ) [he : ReifyE m V e]
    (hk : ∀ x, ReifyG E (k x) (vCons x V) p) :
    ReifyG E (m >>= k) V (.var e p) where
  sound y hy := by
    obtain ⟨x, hx, hy⟩ := rustM_bind_ok hy
    rw [nfToRustM, he.sound x hx, bind_tc_ok, extend_eq]
    exact (hk x).sound y hy

/-- **Bind with a literal operand.** The literal is bound first, then the operation reads it
    as the last bound variable. -/
theorem Reify.bindLit {α β : Type} [AeVal α] {ts : List NfTy}
    {E : β → Valuation (d := nfDialect) ts} {Γ : Ctxt nfDialect} {ty : UScalarTy}
    [Le64 ty] {e : Expr nfDialect (.word 64 :: Γ) (AeVal.nty α)}
    {p : NFProg nfDialect (AeVal.nty α :: .word 64 :: Γ) ts}
    (c : UScalar ty) (m : RustM α) (k : α → RustM β) (V : Valuation Γ)
    [he : ReifyE m (vCons c V) e] (hk : ∀ x, ReifyG E (k x) (vCons x (vCons c V)) p) :
    ReifyG E (m >>= k) V (.var (litE c) (.var e p)) where
  sound y hy := by
    obtain ⟨x, hx, hy⟩ := rustM_bind_ok hy
    have he' : aeExpr e (HVector.cons (embW c) V) = .ok (AeVal.emb x) := he.sound x hx
    rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM, extend_eq, he', bind_tc_ok,
      extend_eq]
    exact (hk x).sound y hy

/-- **A value of an operation with a literal operand.** -/
theorem Reify.okLit {α : Type} [AeVal α] {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty]
    {e : Expr nfDialect (.word 64 :: Γ) (AeVal.nty α)} (c : UScalar ty) (m : RustM α)
    (V : Valuation Γ) [he : ReifyE m (vCons c V) e] :
    ReifyG single m V (.var (litE c) (.var e (.ret (.cons .here .nil)))) where
  sound y hy := by
    have he' : aeExpr e (HVector.cons (embW c) V) = .ok (AeVal.emb y) := he.sound y hy
    rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM, extend_eq, he', bind_tc_ok, nfToRustM]
    rfl

/-- **A value of a variable.** -/
instance Reify.okVar {α : Type} [AeVal α] {Γ : Ctxt nfDialect} (x : α) (V : Valuation Γ)
    {v : Var Γ (AeVal.nty α)} [hx : Lookup V (AeVal.emb x) v] :
    ReifyG single (.ok x) V (.ret (.cons v .nil)) where
  sound y hy := by
    cases hy
    rw [nfToRustM]
    change RustM.ok (HVector.cons (v.lookup V) HVector.nil) = _
    rw [hx.eq]

/-- **A value of an operation.** -/
instance (priority := low) Reify.okExpr {α : Type} [AeVal α] {Γ : Ctxt nfDialect} (m : RustM α)
    (V : Valuation Γ) {e : Expr nfDialect Γ (AeVal.nty α)} [he : ReifyE m V e] :
    ReifyG single m V (.var e (.ret (.cons .here .nil))) where
  sound y hy := by
    rw [nfToRustM, he.sound y hy, bind_tc_ok, nfToRustM]
    rfl

/-- The unit as an NF expression. -/
def unitE {Γ : Ctxt nfDialect} : Expr nfDialect Γ .unit := ⟨.constUnit, rfl, .nil⟩

/-- **The unit value.** -/
instance Reify.okUnit {Γ : Ctxt nfDialect} (V : Valuation Γ) :
    ReifyG single (.ok ()) V (.var unitE (.ret (.cons .here .nil))) where
  sound y hy := by
    cases hy
    change (aeOp .constUnit .nil >>= fun r => nfToRustM (.ret (.cons .here .nil))
      (Valuation.extend V r)) = _
    unfold aeOp
    rw [nfDenoteOp]
    rfl

/-- The variables of the first `ts` bindings of `ts ++ Γ`. -/
def prefixVars : (ts : List NfTy) → (Γ : Ctxt nfDialect) →
    HVector (fun t => Var (d := nfDialect) (ts ++ Γ) t) ts
  | [], _ => .nil
  | _ :: ts, Γ => .cons .here (shiftVars (prefixVars ts Γ))

theorem lookupArgs_prefixVars : ∀ (ts : List NfTy) (Γ : Ctxt nfDialect)
    (r : Valuation (d := nfDialect) ts) (W : Valuation Γ),
    Expr.lookupArgs (prefixVars ts Γ) (hvAppend r W) = r
  | [], _, .nil, _ => rfl
  | _ :: ts, Γ, .cons x r, W => by
    show HVector.cons x (Expr.lookupArgs (shiftVars (prefixVars ts Γ))
      (Valuation.extend (hvAppend r W) x)) = _
    rw [lookupArgs_shiftVars, lookupArgs_prefixVars]

/-- **A branch on a comparison.** The comparison is bound as a bit, the arms are read in the
    extended valuation, and the results of the branch are returned. -/
theorem Reify.iteLt {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty]
    {va vb : Var Γ (.word 64)} {pa pb : NFProg nfDialect (.bit :: Γ) ts}
    (x y : UScalar ty) (a b : RustM α) (V : Valuation Γ)
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb]
    (ha : ReifyG E a (vCons (CmpOp.aen .lt x y) V) pa)
    (hb : ReifyG E b (vCons (CmpOp.aen .lt x y) V) pb) :
    ReifyG E (if x < y then a else b) V
      (.var (callE2 (CmpOp.name .lt) .bit va vb)
        (.ifThenElse .here pa pb (.ret (prefixVars ts _)))) where
  sound r hr := by
    have hc : aeExpr (callE2 (CmpOp.name .lt) .bit va vb) V = .ok (CmpOp.aen .lt x y) :=
      aeExpr_callE2 _ _ va vb V x y hx.eq hy.eq (aeCall2_cmp .lt x y) rfl
    rw [nfToRustM, hc, bind_tc_ok, nfToRustM]
    have hl : HasBoolBit.toBool (d := nfDialect)
        ((Ctxt.Var.here (Γ := Γ)).lookup (Valuation.extend V (CmpOp.aen .lt x y))) =
          CmpOp.aen .lt x y := rfl
    have hiff : CmpOp.aen .lt x y = true ↔ x < y := by
      simp only [CmpOp.aen, decide_eq_true_eq]
      exact Iff.rfl
    rw [hl]
    by_cases hxy : x < y
    · simp only [hxy, ite_true] at hr
      have ha' : nfToRustM pa (HVector.cons (CmpOp.aen .lt x y) V) = .ok (E r) := ha.sound r hr
      rw [ite_eq_left (hiff.mpr hxy), extend_eq, ha', bind_tc_ok, nfToRustM,
        lookupArgs_prefixVars]
    · simp only [hxy, ite_false] at hr
      have hb' : nfToRustM pb (HVector.cons (CmpOp.aen .lt x y) V) = .ok (E r) := hb.sound r hr
      rw [ite_eq_right (fun h => hxy (hiff.mp h)), extend_eq, hb', bind_tc_ok, nfToRustM,
        lookupArgs_prefixVars]

/-! ## Guards

A panic guard of the source is read as the branch `ifThenElse c abortArm (ret []) k` on the bit
`c` of the failing case, whose first arm aborts at once and whose second arm returns at once:
the form that the elimination of aborting branches `NFProg.abortElim` replaces by `k`.

The condition under which the guard passes is read positively by the class `ReadCond`, as one
expression; the bit of the failing case is its negation, bound next. One lemma, `Reify.guardS`,
reads every guard; the three shapes the Aeneas backend prints are its instances:
`massert P` (`Reify.assert`, the passing condition `P`), `if c then k else fail e`
(`Reify.iteFailElse`, the passing condition `c`) and `if c then fail e else k`
(`Reify.iteFail`, the passing condition `¬ c`).

`ReadCond` reads a comparison of two words of any width of at most `64` bits, through the
square `cmp_square` of its name (`readCmp`); the notations the backend prints for the six
comparisons and their negations are the entries of the class `CmpProp`, the negations by one
instance (`CmpProp.not`, by `CmpOp.aen_neg`). It reads a Boolean variable in either
polarity, a connective `&&`, `||` of two Boolean variables through the square
`bool_square` (`BoolForm`), a decided proposition and a double negation. A literal operand
of a comparison is bound before the condition (`Reify.letLit`). -/

/-- The aborting arm of a guard: the abort at the unit type, then the empty return. -/
def abortArm {Γ : Ctxt nfDialect} : NFProg nfDialect Γ [] :=
  .var ⟨.abort .unit, rfl, .nil⟩ (.ret .nil)

/-- **The reading of an abort fails.** -/
theorem nfToRustM_abortArm {Γ : Ctxt nfDialect} (V : Valuation Γ) :
    nfToRustM (abortArm (Γ := Γ)) V = .fail .undef := by
  rw [abortArm, nfToRustM]
  rfl

/-- The bit negation of a variable as an NF expression. -/
def notE {Γ : Ctxt nfDialect} (v : Var Γ .bit) : Expr nfDialect Γ .bit :=
  ⟨.notB, rfl, .cons v .nil⟩

theorem aeExpr_notE {Γ : Ctxt nfDialect} (v : Var Γ .bit) (V : Valuation Γ) (b : Bool)
    (h : v.lookup V = b) : aeExpr (notE v) V = .ok (!b) := by
  change aeOp .notB (.cons (v.lookup V) .nil) = _
  unfold aeOp
  rw [nfDenoteOp, h]
  rfl

/-- **A binding of an expression the program reads no further.** When `e` reads `a` at `V`,
    a reading of `m` at `V` extended by `a` is a reading of `m` after the binding of `e`. -/
theorem Reify.letE {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {t : NfTy} {e : Expr nfDialect Γ t} {p : NFProg nfDialect (t :: Γ) ts}
    (m : RustM α) (V : Valuation Γ) (a : t.denote) (he : aeExpr e V = .ok a)
    (h : ReifyG E m (HVector.cons a V) p) : ReifyG E m V (.var e p) where
  sound y hy := by
    rw [nfToRustM, he, bind_tc_ok, extend_eq]
    exact h.sound y hy

/-- **A literal bound first**: `Reify.letE` at the literal expression `litE c`. -/
theorem Reify.letLit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty] {p : NFProg nfDialect (.word 64 :: Γ) ts}
    (c : UScalar ty) (m : RustM α) (V : Valuation Γ) (h : ReifyG E m (vCons c V) p) :
    ReifyG E m V (.var (litE c) p) :=
  Reify.letE m V (embW c) (aeExpr_litE c V) h

/-- **A guard.** When the expression `e` reads the bit `c` and every value of `m` is a value of
    `k` at the bit `false`, the branch on `c` to the aborting arm, followed by the reading of
    `k`, reads `m`. -/
theorem Reify.guard {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {pk : NFProg nfDialect (.bit :: Γ) ts}
    (m k : RustM α) (c : Bool) (V : Valuation Γ) (he : aeExpr e V = .ok c)
    (hm : ∀ y, m = .ok y → c = false ∧ k = .ok y) (hk : ReifyG E k (vCons c V) pk) :
    ReifyG E m V (.var e (.ifThenElse .here abortArm (.ret .nil) pk)) where
  sound y hy := by
    obtain ⟨hc, hky⟩ := hm y hy
    subst hc
    rw [nfToRustM, he, bind_tc_ok, extend_eq, nfToRustM]
    exact hk.sound y hky

/-! ### Conditions -/

/-- The expression `e` reads, at `V`, the bit `b` of the proposition `P`. -/
class ReadCond {Γ : Ctxt nfDialect} (P : Prop) (V : Valuation Γ) (b : outParam Bool)
    (e : outParam (Expr nfDialect Γ .bit)) : Prop where
  /-- The expression reads the bit. -/
  sound : aeExpr e V = .ok b
  /-- The bit is the truth of the proposition. -/
  iff : b = true ↔ P

/-- The comparison of the opposite truth. -/
def CmpOp.neg : CmpOp → CmpOp
  | .lt => .ge | .le => .gt | .gt => .le | .ge => .lt | .eq => .ne | .ne => .eq

/-- The comparison of the opposite truth is the negation of the comparison. -/
theorem CmpOp.aen_neg {ty : UScalarTy} (c : CmpOp) (x y : UScalar ty) :
    c.neg.aen x y = !c.aen x y := by
  cases c <;> simp only [CmpOp.neg, CmpOp.aen, Bool.not_not] <;>
    simp only [Nat.not_lt, Nat.not_le, ← decide_not]

/-- The proposition `P` is the comparison `c` of `x` and `y`: an entry for each notation of a
    comparison the backend prints. -/
class CmpProp (P : Prop) {ty : outParam UScalarTy} (c : outParam CmpOp)
    (x y : outParam (UScalar ty)) : Prop where
  /-- The comparison is the truth of the proposition. -/
  iff : c.aen x y = true ↔ P

instance CmpProp.lt {ty : UScalarTy} (x y : UScalar ty) : CmpProp (x < y) .lt x y :=
  ⟨decide_eq_true_iff⟩

instance CmpProp.le {ty : UScalarTy} (x y : UScalar ty) : CmpProp (x ≤ y) .le x y :=
  ⟨decide_eq_true_iff⟩

instance CmpProp.gt {ty : UScalarTy} (x y : UScalar ty) : CmpProp (x > y) .gt x y :=
  ⟨decide_eq_true_iff⟩

instance CmpProp.ge {ty : UScalarTy} (x y : UScalar ty) : CmpProp (x ≥ y) .ge x y :=
  ⟨decide_eq_true_iff⟩

instance CmpProp.eq {ty : UScalarTy} (x y : UScalar ty) : CmpProp (x = y) .eq x y :=
  ⟨by
    simp only [CmpOp.aen, decide_eq_true_iff]
    exact ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩⟩

instance CmpProp.bne {ty : UScalarTy} (x y : UScalar ty) : CmpProp ((x != y) = true) .ne x y :=
  ⟨by
    simp only [CmpOp.aen, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq]
    exact ⟨fun h h' => h (h' ▸ rfl), fun h h' => h (UScalar.eq_of_val_eq h')⟩⟩

/-- **The negation of a comparison** is the comparison of the opposite truth. -/
instance CmpProp.not {P : Prop} {ty : UScalarTy} {c : CmpOp} {x y : UScalar ty}
    [h : CmpProp P c x y] : CmpProp (¬ P) c.neg x y :=
  ⟨by rw [CmpOp.aen_neg, Bool.not_eq_true', ← h.iff, Bool.not_eq_true]⟩

/-- **A comparison** of two words, of every width of at most `64` bits, is the call of its
    name; one instance for every comparison and every notation of `CmpProp`. -/
instance readCmp {Γ : Ctxt nfDialect} {P : Prop} {ty : UScalarTy} {c : CmpOp}
    {x y : UScalar ty} [hp : CmpProp P c x y] [Le64 ty] (V : Valuation Γ)
    {va vb : Var Γ (.word 64)} [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReadCond P V (c.aen x y) (callE2 c.name .bit va vb) :=
  ⟨aeExpr_callE2 _ _ va vb V x y hx.eq hy.eq (aeCall2_cmp c x y) rfl, hp.iff⟩

/-- The NF operation of a connective. -/
def BoolOp.nf : BoolOp → NfOp
  | .and => .andB
  | .or => .orB

/-- The connective `o` of two bit variables as an NF expression. -/
def boolE {Γ : Ctxt nfDialect} (o : BoolOp) (va vb : Var Γ .bit) : Expr nfDialect Γ .bit :=
  match o with
  | .and => ⟨.andB, rfl, .cons va (.cons vb .nil)⟩
  | .or => ⟨.orB, rfl, .cons va (.cons vb .nil)⟩

theorem aeExpr_boolE {Γ : Ctxt nfDialect} (o : BoolOp) (va vb : Var Γ .bit) (V : Valuation Γ)
    (a b : Bool) (ha : va.lookup V = a) (hb : vb.lookup V = b) :
    aeExpr (boolE o va vb) V = .ok (o.val a b) := by
  cases o
  · change aeOp .andB (.cons (va.lookup V) (.cons (vb.lookup V) .nil)) = _
    unfold aeOp
    rw [nfDenoteOp, ha, hb]
    rfl
  · change aeOp .orB (.cons (va.lookup V) (.cons (vb.lookup V) .nil)) = _
    unfold aeOp
    rw [nfDenoteOp, ha, hb]
    rfl

/-- The Boolean `b` is the connective `o` of `x` and `y`: an entry for each connective. -/
class BoolForm (b : Bool) (o : outParam BoolOp) (x y : outParam Bool) : Prop where
  /-- The connective is the Boolean. -/
  eq : o.val x y = b

instance BoolForm.and (x y : Bool) : BoolForm (x && y) .and x y := ⟨rfl⟩

instance BoolForm.or (x y : Bool) : BoolForm (x || y) .or x y := ⟨rfl⟩

/-- **A connective of two Boolean variables**, through its NF operation. -/
instance readBool {Γ : Ctxt nfDialect} {b : Bool} {o : BoolOp} {x y : Bool} [hf : BoolForm b o x y]
    (V : Valuation Γ) {va vb : Var Γ .bit} [hx : Lookup V (AeVal.emb x) va]
    [hy : Lookup V (AeVal.emb y) vb] : ReadCond (b = true) V b (boolE o va vb) :=
  ⟨hf.eq ▸ aeExpr_boolE o va vb V x y hx.eq hy.eq, Iff.rfl⟩

/-- **A Boolean variable**: the connective `b && b`. -/
instance readBit {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ) {v : Var Γ .bit}
    [hb : Lookup V (AeVal.emb b) v] : ReadCond (b = true) V b (boolE .and v v) :=
  ⟨(Bool.and_self b) ▸ aeExpr_boolE .and v v V b b hb.eq hb.eq, Iff.rfl⟩

/-- **A negated Boolean variable**: the negation of its bit. -/
instance readNotBit {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ) {v : Var Γ .bit}
    [hb : Lookup V (AeVal.emb b) v] : ReadCond (¬ (b = true)) V (!b) (notE v) :=
  ⟨aeExpr_notE v V b hb.eq, by simp⟩

/-- **A decided proposition** is read as the proposition. -/
instance readDecide {Γ : Ctxt nfDialect} (P : Prop) [Decidable P] (V : Valuation Γ) {b : Bool}
    {e : Expr nfDialect Γ .bit} [h : ReadCond P V b e] : ReadCond (decide P = true) V b e :=
  ⟨h.sound, by rw [decide_eq_true_iff]; exact h.iff⟩

/-- **A double negation** is read as the proposition. -/
instance (priority := low) readNotNot {Γ : Ctxt nfDialect} (P : Prop) (V : Valuation Γ)
    {b : Bool} {e : Expr nfDialect Γ .bit} [h : ReadCond P V b e] : ReadCond (¬ ¬ P) V b e :=
  ⟨h.sound, by rw [not_not]; exact h.iff⟩

/-! ### Conditions with compound operands

A condition whose connectives have compound operands, such as `(¬ b₀) || b₁`, is read as a
prefix of bindings followed by a bit (`ReadBit`): the prefix `NFPre` binds the bits and words
of the subterms in order, and the bit of the condition is a variable of the context after the
prefix. Each construct has one instance, a congruence lemma stated once for every operand:
a Boolean variable (no binding, `readBitVar`), a negation (`readBitNot`, `readBitDecNot`), a
connective of two operands through the square `bool_square` (`readBitConn`), a comparison of
two words of every width of at most `64` bits through the square `cmp_square`
(`readBitCmp`), and the decision of `b = true` (`readBitDecEq`). A word operand is read by
`ReadWord`: a variable of the valuation, or else a literal bound first. -/

/-- The call `f` of the table on one bit, with a bit result, as an NF expression. -/
def callB1 {Γ : Ctxt nfDialect} (f : String) (v : Var Γ .bit) : Expr nfDialect Γ .bit :=
  ⟨.call f [.bit] .bit, rfl, .cons v .nil⟩

/-- The call `f` of the table on two bits, with a bit result, as an NF expression. -/
def callB2 {Γ : Ctxt nfDialect} (f : String) (va vb : Var Γ .bit) : Expr nfDialect Γ .bit :=
  ⟨.call f [.bit, .bit] .bit, rfl, .cons va (.cons vb .nil)⟩

/-- The reading of a call of one bit is the reading `aeCall1` of the call on its encoding. -/
theorem aeExpr_callB1 {Γ : Ctxt nfDialect} (f : String) (v : Var Γ .bit) (V : Valuation Γ)
    (a r : Bool) (ha : v.lookup V = a) (h : aeCall1 f (.bool a) = .ok (.bool r)) :
    aeExpr (callB1 f v) V = .ok r := by
  change aeOp (.call f [.bit] .bit) (.cons (v.lookup V) .nil) = _
  unfold aeOp
  rw [nfDenoteOp]
  unfold aeTable
  simp only [encAll]
  rw [ha, show ImpToNF.enc NfTy.bit a = Value.bool a from rfl, aeCallV, h]
  rfl

/-- The reading of a call of two bits is the reading `aeCall2` of the call on their
    encodings. -/
theorem aeExpr_callB2 {Γ : Ctxt nfDialect} (f : String) (va vb : Var Γ .bit) (V : Valuation Γ)
    (a b r : Bool) (ha : va.lookup V = a) (hb : vb.lookup V = b)
    (h : aeCall2 f (.bool a) (.bool b) = .ok (.bool r)) :
    aeExpr (callB2 f va vb) V = .ok r := by
  change aeOp (.call f [.bit, .bit] .bit) (.cons (va.lookup V) (.cons (vb.lookup V) .nil)) = _
  unfold aeOp
  rw [nfDenoteOp]
  unfold aeTable
  simp only [encAll]
  rw [ha, hb, show ImpToNF.enc NfTy.bit a = Value.bool a from rfl,
    show ImpToNF.enc NfTy.bit b = Value.bool b from rfl, aeCallV, h]
  rfl

/-- The call `Not` reads the negation of a Boolean. -/
theorem aeCall1_not (a : Bool) : aeCall1 "Not" (.bool a) = .ok (.bool !a) := by
  unfold aeCall1
  simp only [ite_true, readB, bind_tc_ok]

/-- The call of the name of a connective reads the connective of two Booleans. -/
theorem aeCall2_bool (o : BoolOp) (a b : Bool) :
    aeCall2 o.name (.bool a) (.bool b) = .ok (.bool (o.val a b)) := by
  have hw : wordOpAt? o.name = none := by cases o <;> decide +kernel
  have hc : checkedAt? o.name = none := by cases o <;> decide +kernel
  have hm : CmpOp.ofName? o.name = none := by cases o <;> decide +kernel
  have hn : BoolOp.ofName? o.name = some o := by cases o <;> decide +kernel
  unfold aeCall2
  rw [hw, hc, hm, hn]
  simp only [readB, bind_tc_ok]

/-- The prefix `p` reads, from `V`, the valuation `W` of its hole: each binding reads its value
    at the valuation before it. A prefix with a loop or a branch reads no valuation. -/
def preReads : {Γ Δ : Ctxt nfDialect} → NFPre nfDialect Γ Δ → Valuation Γ → Valuation Δ → Prop
  | _, _, .nil, V, W => W = V
  | _, _, .var e p, V, W => ∃ a, aeExpr e V = .ok a ∧ preReads p (V.extend a) W
  | _, _, _, _, _ => False

/-- A program after a prefix that reads `W` reads, from `V`, what the program reads from
    `W`. -/
theorem nfToRustM_plug {Γ Δ : Ctxt nfDialect} {ts : List NfTy} (p : NFPre nfDialect Γ Δ)
    (q : NFProg nfDialect Δ ts) :
    ∀ {V : Valuation Γ} {W : Valuation Δ}, preReads p V W →
      nfToRustM (p.plug q) V = nfToRustM q W := by
  induction p with
  | nil =>
    intro V W h
    obtain rfl : W = V := h
    rfl
  | var e p ih =>
    intro V W h
    obtain ⟨a, ha, hp⟩ := h
    rw [NFPre.plug, nfToRustM, ha, bind_tc_ok]
    exact ih q hp
  | forLoop => intro V W h; exact h.elim
  | ifThenElse => intro V W h; exact h.elim
  | whileLoop => intro V W h; exact h.elim

/-- A prefix followed by a prefix reads the valuation the second reads from the valuation the
    first reads. -/
theorem preReads_append {Γ Δ Θ : Ctxt nfDialect} (p : NFPre nfDialect Γ Δ)
    (q : NFPre nfDialect Δ Θ) :
    ∀ {V : Valuation Γ} {W : Valuation Δ} {X : Valuation Θ}, preReads p V W → preReads q W X →
      preReads (p.append q) V X := by
  induction p with
  | nil =>
    intro V W X h hq
    obtain rfl : W = V := h
    exact hq
  | var e p ih =>
    intro V W X h hq
    obtain ⟨a, ha, hp⟩ := h
    exact ⟨a, ha, ih q hp hq⟩
  | forLoop => intro V W X h; exact h.elim
  | ifThenElse => intro V W X h; exact h.elim
  | whileLoop => intro V W X h; exact h.elim

/-- A variable weakened along a prefix reads in the valuation of the hole what it reads at
    the start. -/
theorem preReads_wk {Γ Δ : Ctxt nfDialect} {t : NfTy} (p : NFPre nfDialect Γ Δ) :
    ∀ (v : Var Γ t) {V : Valuation Γ} {W : Valuation Δ}, preReads p V W →
      (p.wk v).lookup W = v.lookup V := by
  induction p with
  | nil =>
    intro v V W h
    obtain rfl : W = V := h
    rfl
  | var e p ih =>
    intro v V W h
    obtain ⟨a, _, hp⟩ := h
    exact ih v.there hp
  | forLoop => intro v V W h; exact h.elim
  | ifThenElse => intro v V W h; exact h.elim
  | whileLoop => intro v V W h; exact h.elim

/-- The prefix of one binding of an expression that reads `a`. -/
theorem preReads_one {Γ : Ctxt nfDialect} {t : NfTy} {V : Valuation Γ} {e : Expr nfDialect Γ t}
    {a : t.denote} (he : aeExpr e V = .ok a) :
    preReads (.var e .nil) V (HVector.cons a V) :=
  ⟨a, he, rfl⟩

/-- A prefix followed by the binding of an expression that reads `a`. -/
theorem preReads_snoc {Γ Δ : Ctxt nfDialect} {t : NfTy} {p : NFPre nfDialect Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} {e : Expr nfDialect Δ t} {a : t.denote}
    (hp : preReads p V W) (he : aeExpr e W = .ok a) :
    preReads (p.append (.var e .nil)) V (HVector.cons a W) :=
  preReads_append p _ hp (preReads_one he)

/-- **A reading of a plugged prefix.** When the prefix `p` reads `W` from `V`, a reading of `m`
    at `W` by `q` is a reading of `m` at `V` by `p` with the hole filled by `q`. -/
theorem ReifyG.plug {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {V : Valuation Γ} {W : Valuation Δ}
    {q : NFProg nfDialect Δ ts} (m : RustM α) (hp : preReads p V W) (h : ReifyG E m W q) :
    ReifyG E m V (p.plug q) :=
  ⟨fun y hy => (nfToRustM_plug p q hp).trans (h.sound y hy)⟩

/-- The prefix `p` reads, from `V`, a valuation `W` in which the variable `v` holds the bit
    `b`. -/
class ReadBit {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ)
    (Δ : outParam (Ctxt nfDialect)) (p : outParam (NFPre nfDialect Γ Δ))
    (W : outParam (Valuation Δ)) (v : outParam (Var Δ .bit)) : Prop where
  /-- The prefix reads the valuation. -/
  reads : preReads p V W
  /-- The variable holds the bit. -/
  bit : v.lookup W = b

/-- The prefix `p` reads, from `V`, a valuation `W` in which the variable `v` holds the word of
    `x`. -/
class ReadWord {Γ : Ctxt nfDialect} {ty : UScalarTy} (x : UScalar ty) (V : Valuation Γ)
    (Δ : outParam (Ctxt nfDialect)) (p : outParam (NFPre nfDialect Γ Δ))
    (W : outParam (Valuation Δ)) (v : outParam (Var Δ (.word 64))) : Prop where
  /-- The prefix reads the valuation. -/
  reads : preReads p V W
  /-- The variable holds the word. -/
  word : v.lookup W = embW x

/-- A Boolean whose truth is a proposition is the decision of the proposition. -/
theorem bit_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P :=
  Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff]; exact h)

/-- **A word variable**: no binding. -/
instance (priority := high) readWordVar {Γ : Ctxt nfDialect} {ty : UScalarTy} (x : UScalar ty)
    (V : Valuation Γ) {v : Var Γ (.word 64)} [hx : Lookup V (embW x) v] :
    ReadWord x V Γ .nil V v :=
  ⟨rfl, hx.eq⟩

/-- **A literal word**, no variable of the valuation: bound as a literal. -/
instance (priority := low) readWordLit {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty]
    (x : UScalar ty) (V : Valuation Γ) :
    ReadWord x V (.word 64 :: Γ) (.var (litE x) .nil) (vCons x V) .here :=
  ⟨preReads_one (aeExpr_litE x V), rfl⟩

/-- **A Boolean variable**: no binding. -/
instance (priority := high) readBitVar {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ)
    {v : Var Γ .bit} [hb : Lookup V (AeVal.emb b) v] : ReadBit b V Γ .nil V v :=
  ⟨rfl, hb.eq⟩

/-- **A negation**: the operand, then the call `Not` of its bit (the square
    `notBool_square`). -/
instance readBitNot {Γ Δ : Ctxt nfDialect} {x : Bool} {V : Valuation Γ}
    {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit} [h : ReadBit x V Δ p W v] :
    ReadBit (!x) V (.bit :: Δ) (p.append (.var (callB1 "Not" v) .nil)) (HVector.cons (!x) W)
      .here :=
  ⟨preReads_snoc h.reads (aeExpr_callB1 _ v W x _ h.bit (aeCall1_not x)), rfl⟩

/-- **A decided negation**: the decided proposition, then the call `Not` of its bit. -/
instance readBitDecNot {Γ Δ : Ctxt nfDialect} {P : Prop} {j : Decidable (¬ P)}
    [i : Decidable P] {V : Valuation Γ} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ}
    {v : Var Δ .bit} [h : ReadBit (@decide P i) V Δ p W v] :
    ReadBit (@decide (¬ P) j) V (.bit :: Δ) (p.append (.var (callB1 "Not" v) .nil))
      (HVector.cons (!@decide P i) W) .here :=
  ⟨preReads_snoc h.reads (aeExpr_callB1 _ v W _ _ h.bit (aeCall1_not _)),
    bit_of_iff (b := !@decide P i) (by rw [Bool.not_eq_true', decide_eq_false_iff_not])⟩

/-- **The decision of `b = true`** is the bit `b`. -/
instance readBitDecEq {Γ Δ : Ctxt nfDialect} {b : Bool} {i : Decidable (b = true)}
    {V : Valuation Γ} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit}
    [h : ReadBit b V Δ p W v] : ReadBit (@decide (b = true) i) V Δ p W v :=
  ⟨h.reads, h.bit.trans (bit_of_iff Iff.rfl)⟩

/-- **A connective of two operands**: the first operand, the second, then the call of the name
    of the connective on their bits (the square `bool_square`). -/
instance readBitConn {Γ Δ₁ Δ₂ : Ctxt nfDialect} {b : Bool} {o : BoolOp} {x y : Bool}
    [hf : BoolForm b o x y] {V : Valuation Γ} {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁}
    {v₁ : Var Δ₁ .bit} [h₁ : ReadBit x V Δ₁ p₁ W₁ v₁] {p₂ : NFPre nfDialect Δ₁ Δ₂}
    {W₂ : Valuation Δ₂} {v₂ : Var Δ₂ .bit} [h₂ : ReadBit y W₁ Δ₂ p₂ W₂ v₂] :
    ReadBit b V (.bit :: Δ₂)
      ((p₁.append p₂).append (.var (callB2 o.name (p₂.wk v₁) v₂) .nil)) (HVector.cons b W₂)
      .here :=
  ⟨preReads_snoc (preReads_append _ _ h₁.reads h₂.reads)
    (hf.eq ▸ aeExpr_callB2 _ _ _ W₂ x y _ ((preReads_wk p₂ v₁ h₂.reads).trans h₁.bit) h₂.bit
      (aeCall2_bool o x y)), rfl⟩

/-- **A comparison of two words**, of every width of at most `64` bits and every notation of
    `CmpProp`: the first operand, the second, then the call of the name of the comparison
    (the square `cmp_square`). -/
instance readBitCmp {Γ Δ₁ Δ₂ : Ctxt nfDialect} {P : Prop} {ty : UScalarTy} {c : CmpOp}
    {x y : UScalar ty} [hp : CmpProp P c x y] [Le64 ty] {i : Decidable P} {V : Valuation Γ}
    {p₁ : NFPre nfDialect Γ Δ₁} {W₁ : Valuation Δ₁} {va : Var Δ₁ (.word 64)}
    [h₁ : ReadWord x V Δ₁ p₁ W₁ va] {p₂ : NFPre nfDialect Δ₁ Δ₂} {W₂ : Valuation Δ₂}
    {vb : Var Δ₂ (.word 64)} [h₂ : ReadWord y W₁ Δ₂ p₂ W₂ vb] :
    ReadBit (@decide P i) V (.bit :: Δ₂)
      ((p₁.append p₂).append (.var (callE2 c.name .bit (p₂.wk va) vb) .nil))
      (HVector.cons (c.aen x y) W₂) .here :=
  ⟨preReads_snoc (preReads_append _ _ h₁.reads h₂.reads)
    (aeExpr_callE2 _ _ _ _ W₂ x y ((preReads_wk p₂ va h₂.reads).trans h₁.word) h₂.word
      (aeCall2_cmp c x y) rfl),
    bit_of_iff hp.iff⟩

/-- **A branch on a condition read as a prefix and a bit.** When the decision of `c` is read
    by the prefix `p` as the bit at `v`, the prefix followed by the branch on `v`, whose arms
    are read at the valuation after the prefix, reads `if c then a else b`. -/
theorem Reify.iteBit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit}
    {pa pb : NFProg nfDialect Δ ts} (c : Prop) [Decidable c] (a b : RustM α)
    (V : Valuation Γ) [hs : ReadBit (decide c) V Δ p W v] (ha : ReifyG E a W pa)
    (hb : ReifyG E b W pb) :
    ReifyG E (if c then a else b) V (p.plug (.ifThenElse v pa pb (.ret (prefixVars ts Δ)))) :=
  ReifyG.plug _ hs.reads ⟨fun r hr => by
    rw [nfToRustM]
    have hl : HasBoolBit.toBool (d := nfDialect) (v.lookup W) = decide c := hs.bit
    rw [hl]
    by_cases hc : c
    · simp only [hc, ite_true, decide_true] at hr ⊢
      rw [ha.sound r hr, bind_tc_ok, nfToRustM, lookupArgs_prefixVars]
    · simp only [hc, ite_false, decide_false] at hr ⊢
      rw [hb.sound r hr, ite_eq_right Bool.false_ne_true, bind_tc_ok, nfToRustM,
        lookupArgs_prefixVars]⟩

/-! ### The guard shapes -/

/-- **The guard on a condition.** When the decision of `S` is read by the prefix `p` as the
    bit at `v`, and every value of `m` is a value of `k` under `S`, the prefix, the binding of
    the negation of the bit and the branch on the negation to the aborting arm, followed by the
    reading of `k`, read `m`. Every guard of the reader is an instance. -/
theorem Reify.guardP {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ Δ : Ctxt nfDialect} {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit}
    {pk : NFProg nfDialect (.bit :: Δ) ts}
    (S : Prop) [Decidable S] (m k : RustM α) (V : Valuation Γ) [hs : ReadBit (decide S) V Δ p W v]
    (hm : ∀ y, m = .ok y → S ∧ k = .ok y) (hk : ReifyG E k (vCons (!decide S) W) pk) :
    ReifyG E m V (p.plug (.var (notE v) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  ReifyG.plug m hs.reads (Reify.guard m k (!decide S) W (aeExpr_notE v W _ hs.bit)
    (fun y hy => ⟨by simp only [decide_eq_true (hm y hy).1, Bool.not_true], (hm y hy).2⟩) hk)

/-- **The guard on a condition read as one expression**: `Reify.guardP` at the prefix of the
    one binding of `e`. When `S` is read as the bit `b`, the binding of `b`, the binding of its
    negation and the branch on the negation to the aborting arm, followed by the reading of
    `k`, read `m`. -/
theorem Reify.guardS {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (S : Prop) [Decidable S] (m k : RustM α) (V : Valuation Γ) [hs : ReadCond S V b e]
    (hm : ∀ y, m = .ok y → S ∧ k = .ok y) (hk : ReifyG E k (vCons (!b) (vCons b V)) pk) :
    ReifyG E m V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  have hb : b = decide S := bit_of_iff hs.iff
  Reify.guardP (v := Var.here) (hs := ⟨preReads_one hs.sound, hb⟩) S m k V hm (by rw [← hb]; exact hk)

/-- The passing condition of `massert P`: a value of `massert P >>= k` is a value of `k ()`
    under `P`. -/
theorem pass_massert {α : Type} (P : Prop) [Decidable P] (k : Unit → RustM α) :
    ∀ y, (massert P >>= k) = .ok y → P ∧ k () = .ok y := fun y hy => by
  unfold massert at hy
  split at hy
  · exact ⟨‹P›, by rw [bind_tc_ok] at hy; exact hy⟩
  · cases hy

/-- The passing condition of `if c then k else fail e`: `c`. -/
theorem pass_iteFailElse {α : Type} (c : Prop) [Decidable c] (k : RustM α) (err : Error) :
    ∀ y, (if c then k else .fail err) = .ok y → c ∧ k = .ok y := fun y hy => by
  split at hy
  · exact ⟨‹c›, hy⟩
  · cases hy

/-- The passing condition of `if c then fail e else k`: `¬ c`. -/
theorem pass_iteFail {α : Type} (c : Prop) [Decidable c] (err : Error) (k : RustM α) :
    ∀ y, (if c then .fail err else k) = .ok y → ¬ c ∧ k = .ok y := fun y hy => by
  split at hy
  · cases hy
  · exact ⟨‹¬ c›, hy⟩

/-- **An assertion `massert P`**: the guard on `P`. -/
theorem Reify.assert {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (P : Prop) [Decidable P] (k : Unit → RustM α) (V : Valuation Γ) [ReadCond P V b e]
    (hk : ReifyG E (k ()) (vCons (!b) (vCons b V)) pk) :
    ReifyG E (massert P >>= k) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  Reify.guardS P _ (k ()) V (pass_massert P k) hk

/-- **A branch `if c then k else fail e`**: the guard on `c`. -/
theorem Reify.iteFailElse {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (c : Prop) [Decidable c] (k : RustM α) (err : Error) (V : Valuation Γ) [ReadCond c V b e]
    (hk : ReifyG E k (vCons (!b) (vCons b V)) pk) :
    ReifyG E (if c then k else .fail err) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  Reify.guardS c _ k V (pass_iteFailElse c k err) hk

/-- **A branch `if c then fail e else k`**: the guard on `¬ c`. -/
theorem Reify.iteFail {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {e : Expr nfDialect Γ .bit} {b : Bool}
    {pk : NFProg nfDialect (.bit :: .bit :: Γ) ts}
    (c : Prop) [Decidable c] (err : Error) (k : RustM α) (V : Valuation Γ) [ReadCond (¬ c) V b e]
    (hk : ReifyG E k (vCons (!b) (vCons b V)) pk) :
    ReifyG E (if c then .fail err else k) V
      (.var e (.var (notE .here) (.ifThenElse .here abortArm (.ret .nil) pk))) :=
  Reify.guardS (¬ c) _ k V (pass_iteFail c err k) hk

/-! ## Boolean arguments

A Boolean argument is passed by the System V layout as the word `boolW b`, `0` or `1`, in a
scalar register. The reading binds its bit as the comparison `≠ 0` of the word, at the head of
the program, and reads the body at the bit. -/

/-- The `u64` word `0`. -/
abbrev zeroU : U64 := 0#u64

/-- The `u64` word of a Boolean. -/
def boolU (b : Bool) : U64 := ⟨BitVec.ofNat 64 b.toNat⟩

theorem embW_boolU (b : Bool) : embW (boolU b) = boolW b := by
  cases b <;> rfl

theorem aen_ne_boolU (b : Bool) : CmpOp.aen .ne (boolU b) zeroU = b := by
  cases b <;> decide

/-- **A Boolean argument**: the comparison `≠ 0` of its word, after the literal `0`, is its
    bit. -/
theorem Reify.argBit {α : Type} {ts : List NfTy} {E : α → Valuation (d := nfDialect) ts}
    {Γ : Ctxt nfDialect} {v : Var Γ (.word 64)} {p : NFProg nfDialect (.bit :: .word 64 :: Γ) ts}
    (b : Bool) (m : RustM α) (V : Valuation Γ) [hv : Lookup V (boolW b) v]
    (h : ReifyG E m (vCons b (vCons zeroU V)) p) :
    ReifyG E m V (.var (litE zeroU) (.var (callE2 (CmpOp.name .ne) .bit v.there .here) p)) :=
  Reify.letLit zeroU m V (Reify.letE m _ b
    (aeExpr_callE2 _ _ v.there .here (vCons zeroU V) (boolU b) zeroU
      (hv.eq.trans (embW_boolU b).symm) rfl (aeCall2_cmp .ne _ _)
      (by rw [aen_ne_boolU]; rfl)) h)

/-! ## Boolean results

A Boolean result is returned by the System V layout as the word `boolW b`, `1` or `0`, in the
result register, the value map `AeTy.val .bool` of the entry. The reading of a Boolean result
`ok b` reads the bit of `b` by `ReadBit` and ends the program with the bit-to-word step
`bitWordP`: the literals `1` and `0` are bound and the call `select` of the table chooses one of
them by the bit (the square `select_square`), a step without a branch. The result map of a
Boolean result is `bitRes`. -/

/-- The `u64` word `1`. -/
abbrev oneU : U64 := 1#u64

/-- The selection of one of two words by a bit as an NF expression: the call `select`. -/
def selE {Γ : Ctxt nfDialect} (vk : Var Γ .bit) (va vb : Var Γ (.word 64)) :
    Expr nfDialect Γ (.word 64) :=
  ⟨.call "select" [.bit, .word 64, .word 64] (.word 64), rfl,
    .cons vk (.cons va (.cons vb .nil))⟩

theorem aeCall3_select (k : Bool) (x y : U64) :
    aeCall3 "select" (.bool k) (wordV x) (wordV y) = .ok (wordV (selW k x y)) := by
  unfold aeCall3
  simp only [show ("select" : String) ≠ "array_update" by decide, ite_false, ite_true, readB,
    readW_wordV, bind_tc_ok]

/-- The reading of a call of a bit and two words is the reading `aeCall3` of the call on their
    encodings, decoded at the result type. -/
theorem aeExpr_call3 {Γ : Ctxt nfDialect} {ty : UScalarTy} [Le64 ty] (f : String) (r : NfTy)
    (vk : Var Γ .bit) (va vb : Var Γ (.word 64)) (V : Valuation Γ) (k : Bool) (x y : UScalar ty)
    (hk : vk.lookup V = k) (hx : va.lookup V = embW x) (hy : vb.lookup V = embW y) {v : Value}
    {res : r.denote} (h : aeCall3 f (.bool k) (wordV x) (wordV y) = .ok v)
    (hd : dec r v = some res) :
    aeExpr (⟨.call f [.bit, .word 64, .word 64] r, rfl,
      .cons vk (.cons va (.cons vb .nil))⟩ : Expr nfDialect Γ r) V = .ok res := by
  change aeOp (.call f [.bit, .word 64, .word 64] r)
    (.cons (vk.lookup V) (.cons (va.lookup V) (.cons (vb.lookup V) .nil))) = _
  unfold aeOp
  rw [nfDenoteOp]
  unfold aeTable
  simp only [encAll]
  rw [hk, hx, hy, enc_embW, enc_embW, show ImpToNF.enc NfTy.bit k = Value.bool k from rfl,
    aeCallV, h]
  simp only [hd]

/-- The reading of a selection is the selected word. -/
theorem aeExpr_selE {Γ : Ctxt nfDialect} (vk : Var Γ .bit) (va vb : Var Γ (.word 64))
    (V : Valuation Γ) (k : Bool) (x y : U64) (hk : vk.lookup V = k) (hx : va.lookup V = embW x)
    (hy : vb.lookup V = embW y) : aeExpr (selE vk va vb) V = .ok (embW (selW k x y)) :=
  aeExpr_call3 _ _ vk va vb V k x y hk hx hy (aeCall3_select k x y) (dec_wordV _)

/-- **The bit-to-word step**: the word `1` or `0` of the bit at `v`, the call `select` on the
    bit and the literals `1` and `0`, returned. -/
def bitWordP {Δ : Ctxt nfDialect} (v : Var Δ .bit) : NFProg nfDialect Δ [.word 64] :=
  .var (litE oneU) (.var (litE zeroU)
    (.var (selE v.there.there (Var.there .here) .here) (.ret (.cons .here .nil))))

/-- The result map of a Boolean result: the word `boolW b` of the layout. -/
def bitRes (b : Bool) : Valuation (d := nfDialect) [.word 64] := .cons (boolW b) .nil

theorem embW_selW_one_zero (b : Bool) : embW (selW b oneU zeroU) = boolW b := by
  cases b <;> rfl

/-- The bit-to-word step reads the word of the bit. -/
theorem nfToRustM_bitWordP {Δ : Ctxt nfDialect} (v : Var Δ .bit) (W : Valuation Δ) (b : Bool)
    (h : v.lookup W = b) : nfToRustM (bitWordP v) W = .ok (bitRes b) := by
  rw [bitWordP, nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM, aeExpr_litE, bind_tc_ok,
    nfToRustM]
  simp only [extend_eq]
  rw [aeExpr_selE v.there.there (Var.there .here) .here
      (HVector.cons (embW zeroU) (HVector.cons (embW oneU) W)) b oneU zeroU h rfl rfl,
    bind_tc_ok, nfToRustM, embW_selW_one_zero]
  rfl

/-- **A Boolean result**: the prefix that reads the bit of `b`, then the bit-to-word step. -/
instance Reify.okBit {Γ Δ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ)
    {p : NFPre nfDialect Γ Δ} {W : Valuation Δ} {v : Var Δ .bit} [h : ReadBit b V Δ p W v] :
    ReifyG bitRes (.ok b) V (p.plug (bitWordP v)) where
  sound y hy := by
    cases hy
    rw [nfToRustM_plug p _ h.reads]
    exact nfToRustM_bitWordP v W b h.bit

/-! ## Loops -/

/-- The NF results of a step of a loop body: the bit `true` and the next state for
    `cont`, the bit `false` and the final state for `done`. -/
def stepVal {σ : Type} [AeVal σ] :
    Aeneas.Std.ControlFlow σ σ → Valuation (d := nfDialect) [.bit, AeVal.nty σ]
  | .cont y => .cons true (.cons (AeVal.emb y) .nil)
  | .done y => .cons false (.cons (AeVal.emb y) .nil)

/-- The bit literal `b` as an NF expression. -/
def bitE {Γ : Ctxt nfDialect} (b : Bool) : Expr nfDialect Γ .bit := ⟨.constBit b, rfl, .nil⟩

theorem aeExpr_bitE {Γ : Ctxt nfDialect} (b : Bool) (V : Valuation Γ) :
    aeExpr (bitE b) V = .ok b := by
  change aeOp (.constBit b) .nil = _
  unfold aeOp
  rw [nfDenoteOp]

/-- **Continuing a loop** with the state `x`. -/
instance ReifyG.cont {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} (x : σ) (V : Valuation Γ)
    {v : Var Γ (AeVal.nty σ)} [hx : Lookup V (AeVal.emb x) v] :
    ReifyG stepVal (.ok (.cont x)) V (.var (bitE true) (.ret (.cons .here (.cons v.there .nil))))
    where
  sound c hc := by
    cases hc
    rw [nfToRustM, aeExpr_bitE, bind_tc_ok, nfToRustM]
    change RustM.ok (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.bit) true
      (HVector.cons (v.lookup V) HVector.nil)) = _
    rw [hx.eq]
    rfl

/-- **Leaving a loop** with the state `x`. -/
instance ReifyG.done {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} (x : σ) (V : Valuation Γ)
    {v : Var Γ (AeVal.nty σ)} [hx : Lookup V (AeVal.emb x) v] :
    ReifyG stepVal (.ok (.done x)) V (.var (bitE false) (.ret (.cons .here (.cons v.there .nil))))
    where
  sound c hc := by
    cases hc
    rw [nfToRustM, aeExpr_bitE, bind_tc_ok, nfToRustM]
    change RustM.ok (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.bit) false
      (HVector.cons (v.lookup V) HVector.nil)) = _
    rw [hx.eq]
    rfl

-- The fixpoint induction on `loop` names the monotonicity proof of its `partial_fixpoint`
-- definition, as `Aeneas.Std.loop_spec` does (see `loop_whileIter`).
set_option linter.auxLemma false in
/-- The Aeneas `loop` of a body read by `pb` and the Aeneas `loop` of the reading of `pb`
    agree on values. -/
theorem loop_reify {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (pb : NFProg nfDialect (AeVal.nty σ :: Γ) [.bit, AeVal.nty σ])
    (b : σ → RustM (Aeneas.Std.ControlFlow σ σ)) (hb : ∀ x, ReifyG stepVal (b x) (vCons x V) pb) :
    ∀ x y, loop b x = .ok y →
      loop (fun acc => nfToRustM pb (hvAppend acc V) >>= fun r => .ok (flagStep r))
        (single x) = .ok (single y) := by
  generalize hL : Aeneas.Std.loop
    (fun acc => nfToRustM pb (hvAppend acc V) >>= fun r => .ok (flagStep r)) = L
  intro x
  delta loop
  refine Lean.Order.fix_induct (loop._proof_1 b)
    (motive := fun g => ∀ x y, g x = .ok y → L (single x) = .ok (single y)) ?_ ?_ x
  · apply Lean.Order.admissible_pi
    intro x
    apply Lean.Order.admissible_apply (β := fun _ => RustM σ)
      (P := fun x r => ∀ y, r = .ok y → L (single x) = .ok (single y)) x
    exact Lean.Order.admissible_flatOrder _ (fun _ h => by cases h)
  · intro g IH x y hg
    simp only [] at hg
    rw [← hL, loop.eq_1]
    rcases hbx : b x with c | e | _
    · rw [hbx] at hg
      have hs : nfToRustM pb (hvAppend (single x) V) = .ok (stepVal c) := (hb x).sound c hbx
      rw [hs, bind_tc_ok]
      cases c with
      | cont x' =>
        rw [hL]
        exact IH x' y hg
      | done x' =>
        cases hg
        rfl
    · rw [hbx] at hg
      cases hg
    · rw [hbx] at hg
      cases hg

/-- **A loop.** An Aeneas `loop` whose body is read by `pb` at every state is the exit-flag
    loop of `pb` from the variable of its initial state. -/
theorem Reify.loop {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} {v : Var Γ (AeVal.nty σ)}
    {pb : NFProg nfDialect (AeVal.nty σ :: Γ) [.bit, AeVal.nty σ]}
    (b : σ → RustM (Aeneas.Std.ControlFlow σ σ)) (init : σ) (V : Valuation Γ)
    [hi : Lookup V (AeVal.emb init) v] (hb : ∀ x, ReifyG stepVal (b x) (vCons x V) pb) :
    ReifyG single (Aeneas.Std.loop b init) V
      (.whileLoop (.cons v .nil) pb (.ret (.cons .here .nil))) where
  sound y hy := by
    rw [nfToRustM]
    have hinit : Expr.lookupArgs (HVector.cons v HVector.nil) V = single init := by
      change HVector.cons (v.lookup V) HVector.nil = _
      rw [hi.eq]
    rw [hinit]
    refine (congrArg (fun z => z >>= fun acc =>
      nfToRustM (NFProg.ret (HVector.cons Var.here HVector.nil)) (hvAppend acc V))
        (loop_reify V pb b hb init y hy)).trans ?_
    rw [bind_tc_ok, nfToRustM]
    rfl

/-! ## Range loops

The Aeneas backend prints a loop `for i in 0..n` as `loop F (⟨0, n⟩, acc)` with a body `F`
that steps the range by `IteratorRange.next` and continues with the stepped range and the
new state. `loop_range` makes such a loop the hax backend's `foldRangeAux` of the step `f`
of the body; the fold is the counted loop `forLoop` of NF, whose trip index is the range
index. -/

/-- The range index of the trip `i` of a counted loop is its trip index: below `2 ^ 64`
    the NF word of the trip is the word of the `usize` index. -/
theorem embW_usize_ofNat {i : Nat} (hi : i < 2 ^ UScalarTy.Usize.numBits) :
    embW (⟨BitVec.ofNat _ i⟩ : Usize) = HasWord64.ofNat (d := nfDialect) i := by
  change BitVec.ofNat 64 (BitVec.ofNat _ i).toNat = BitVec.ofNat 64 i
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- **The fold of a range against the counted loop.** If every step `f acc i` is read by
    `pb` at the state and the index, a value of `foldRangeAux f k s` is the value of the
    fold of the reading of `pb` over the trip indices `s, …, s + k - 1`. -/
theorem foldRange_reify {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: Γ) [AeVal.nty σ])
    (f : σ → Usize → RustM σ)
    (hb : ∀ (i : Usize) (acc : σ), ReifyG single (f acc i) (vCons acc (vCons i V)) pb) :
    ∀ (k s : Nat) (acc y : σ), s + k ≤ 2 ^ UScalarTy.Usize.numBits →
      HaxBackend.foldRangeAux f k s acc = .ok y →
      (List.range' s k).foldlM
          (fun a i => nfToRustM pb (hvAppend a (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
          (single acc) = .ok (single y)
  | 0, _, acc, y, _, h => by
    cases h
    rfl
  | k + 1, s, acc, y, hk, h => by
    rw [HaxBackend.foldRangeAux] at h
    obtain ⟨acc', h1, h2⟩ := rustM_bind_ok h
    have hs := (hb ⟨BitVec.ofNat _ s⟩ acc).sound acc' h1
    have he : AeVal.emb (⟨BitVec.ofNat _ s⟩ : Usize) = HasWord64.ofNat (d := nfDialect) s :=
      embW_usize_ofNat (by omega)
    rw [show vCons acc (vCons (⟨BitVec.ofNat _ s⟩ : Usize) V) =
      hvAppend (single acc) (.cons (HasWord64.ofNat (d := nfDialect) s) V) by
        unfold vCons
        rw [he]
        rfl] at hs
    rw [List.range'_succ, List.foldlM_cons, hs, bind_tc_ok]
    exact foldRange_reify V pb f hb k (s + 1) acc' y (by omega) h2

/-- **The body of a range loop.** A body that steps the range `⟨s, n⟩` by `IteratorRange.next`
    and, at an index `i` and the stepped range `r`, continues with `r` and a value of
    `f acc i`, and is done with `acc` at the end of the range, is the body that `loop_range`
    takes. -/
theorem range_body {σ : Type} (n s : Usize) (acc : σ)
    (K : Option Usize × core.ops.range.Range Usize →
      RustM (Aeneas.Std.ControlFlow (core.ops.range.Range Usize × σ) σ))
    (f : σ → Usize → RustM σ)
    (hnone : ∀ r, K (none, r) = .ok (.done acc))
    (hsome : ∀ i r, K (some i, r) = f acc i >>= fun a => .ok (.cont (r, a))) :
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({ start := s, «end» := n } : core.ops.range.Range Usize) >>= K) =
      if s.val < n.val then
        f acc s >>= fun a =>
          .ok (.cont ({ start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n }, a))
      else .ok (.done acc) := by
  rw [next_usize]
  split
  · rw [bind_tc_ok, hsome]
  · rw [bind_tc_ok, hnone]

/-- A continuation at the end of a bind chain: the computation is the chain `g` followed by
    continuing with the range `r` and the value of `g`. The last step. -/
theorem tailCont_ok {σ R : Type} (r : R) (a : σ) :
    (RustM.ok (Aeneas.Std.ControlFlow.cont (r, a)) :
        RustM (Aeneas.Std.ControlFlow (R × σ) σ)) =
      (RustM.ok a >>= fun a => .ok (.cont (r, a))) := by
  rw [bind_tc_ok]

/-- A continuation at the end of a bind chain: the bind step. -/
theorem tailCont_bind {α σ R : Type} (r : R) (m : RustM α)
    (k : α → RustM (Aeneas.Std.ControlFlow (R × σ) σ)) (g : α → RustM σ)
    (h : ∀ x, k x = g x >>= fun a => .ok (.cont (r, a))) :
    (m >>= k) = ((m >>= g) >>= fun a => .ok (.cont (r, a))) := by
  cases m with
  | ok x => rw [bind_tc_ok, bind_tc_ok, h]
  | fail e => rfl
  | div => rfl

/-- **A range loop.** An Aeneas `loop` over the range `⟨0, n⟩` whose body steps the range and
    runs `f` (`hF`), with each step `f acc i` read by `pb` at the state, the index and the
    bound, is the counted loop of `pb`: the bound `n` is bound as a literal and is the trip
    count, the trip index is the range index. The proof is `loop_range` and
    `foldRange_reify`. -/
theorem Reify.rangeForLoop {σ : Type} [AeVal σ] {Γ : Ctxt nfDialect} {v : Var Γ (AeVal.nty σ)}
    {pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: .word 64 :: Γ) [AeVal.nty σ]}
    (F : core.ops.range.Range Usize × σ →
      RustM (Aeneas.Std.ControlFlow (core.ops.range.Range Usize × σ) σ))
    (n : Usize) (init : σ) (f : σ → Usize → RustM σ) (V : Valuation Γ)
    [hi : Lookup V (AeVal.emb init) v]
    (hF : ∀ (s : Usize) (acc : σ), F ({ start := s, «end» := n }, acc) =
      if s.val < n.val then
        f acc s >>= fun acc' =>
          .ok (.cont ({ start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n }, acc'))
      else .ok (.done acc))
    (hb : ∀ (i : Usize) (acc : σ), ReifyG single (f acc i) (vCons acc (vCons i (vCons n V))) pb) :
    ReifyG single (Aeneas.Std.loop F ({ start := 0#usize, «end» := n }, init)) V
      (.var (litE n) (.forLoop .here (.cons v.there .nil) pb (.ret (.cons .here .nil)))) where
  sound y hy := by
    have h0 : (0#usize : Usize).val = 0 := rfl
    rw [loop_range F f n hF (n.val - (0#usize : Usize).val) 0#usize init rfl, h0,
      Nat.sub_zero] at hy
    have hn : n.val < 2 ^ 64 := lt64 n
    have hfold := foldRange_reify (vCons n V) pb f hb n.val 0 init y
      (by have := n.bv.isLt; simp only [UScalar.val] at this ⊢; omega) hy
    rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM]
    have hc : HasWord64.toNat (d := nfDialect)
        ((Ctxt.Var.here (Γ := Γ)).lookup (Valuation.extend (t := NfTy.word 64) V (embW n))) = n.val := by
      change (BitVec.ofNat 64 n.val).toNat = n.val
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have hinit : Expr.lookupArgs (HVector.cons v.there HVector.nil)
        (Valuation.extend (t := NfTy.word 64) V (embW n)) = single init := by
      change HVector.cons (v.lookup V) HVector.nil = _
      rw [hi.eq]
    rw [hc, hinit, List.range_eq_range', extend_eq]
    refine (congrArg (fun z => z >>= fun acc =>
      nfToRustM (NFProg.ret (HVector.cons Var.here HVector.nil))
        (hvAppend acc (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (embW n) V))) hfold).trans ?_
    rw [bind_tc_ok, nfToRustM]
    rfl

/-! ## Loops over iterator adapters

The Aeneas backend prints a loop over an iterator adapter (`enumerate`, `step_by`, `zip`) as
`loop F (st₀, acc)` whose body steps the adapter state `st₀` by the adapter's `next`. When the
state runs through positions indexed by a trip index (`IndexedIter`), the loop is the fold
`foldRangeAux` of a step that binds the item of the trip (`loop_indexed`), and is read as the
counted loop of that step, as a range loop is (`Reify.indexedForLoop`). The instances of
`IndexedIter` at the adapters are in `AeneasFront/Iterators.lean`. -/

/-- The `usize` word of a natural number. -/
abbrev usz (j : Nat) : Usize := ⟨BitVec.ofNat _ j⟩

theorem usz_val {j : Nat} (h : j < 2 ^ UScalarTy.Usize.numBits) : (usz j).val = j := by
  change (BitVec.ofNat _ j).toNat = j
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **An iterator state indexed by the trip index.** From `st₀ = pos 0`, the function `next`
    at `pos j` yields `item j` and `pos (j + 1)` below the trip count `cnt`, and yields no item
    at `pos cnt`. -/
structure IndexedIter {I Item : Type} (next : I → RustM (Option Item × I)) (st₀ : I)
    (cnt : Usize) where
  /-- The state before the trip `j`. -/
  pos : Nat → I
  /-- The item of the trip at an index. -/
  item : Usize → RustM Item
  /-- The step below the trip count. -/
  hnext : ∀ j, j < cnt.val → next (pos j) = item (usz j) >>= fun x => .ok (some x, pos (j + 1))
  /-- The end at the trip count. -/
  hend : ∃ rest, next (pos cnt.val) = .ok (none, rest)
  /-- The initial state. -/
  h0 : pos 0 = st₀

/-- **The loop over an indexed iterator is a counted loop.** If the body `F` steps the state
    by `next` and continues with `K`, which is done at no item and at an item runs a step
    `f acc i` after binding `item i` (`hsome`), then the Aeneas `loop` from `pos j` is the fold
    `foldRangeAux f` over the remaining trips. -/
theorem loop_indexed {I Item σ : Type} {next : I → RustM (Option Item × I)} {st₀ : I}
    {cnt : Usize} (it : IndexedIter next st₀ cnt)
    (F : I × σ → RustM (Aeneas.Std.ControlFlow (I × σ) σ))
    (K : σ → Option Item × I → RustM (Aeneas.Std.ControlFlow (I × σ) σ))
    (f : σ → Usize → RustM σ)
    (hF : ∀ st acc, F (st, acc) = next st >>= K acc)
    (hnone : ∀ acc r, K acc (none, r) = .ok (.done acc))
    (hsome : ∀ acc i r, (it.item i >>= fun x => K acc (some x, r)) =
      f acc i >>= fun a => .ok (.cont (r, a))) :
    ∀ k j acc, j + k = cnt.val →
      Aeneas.Std.loop F (it.pos j, acc) = HaxBackend.foldRangeAux f k j acc
  | 0, j, acc, hk => by
    obtain rfl : j = cnt.val := by omega
    obtain ⟨rest, hr⟩ := it.hend
    rw [loop.eq_1, hF, hr, bind_tc_ok, hnone]
    rfl
  | k + 1, j, acc, hk => by
    have hs : (next (it.pos j) >>= K acc) =
        f acc (usz j) >>= fun a => .ok (.cont (it.pos (j + 1), a)) := by
      rw [it.hnext j (by omega), bind_assoc_eq]
      simp only [bind_tc_ok]
      exact hsome acc (usz j) (it.pos (j + 1))
    rw [loop.eq_1, hF, hs, HaxBackend.foldRangeAux]
    cases hf : f acc (usz j) with
    | ok a =>
      simp only [bind_tc_ok]
      exact loop_indexed it F K f hF hnone hsome k (j + 1) a (by omega)
    | fail e => rfl
    | div => rfl

/-- **A loop over an indexed iterator.** An Aeneas `loop` from the state `st₀` of an
    `IndexedIter` with the trip count `cnt`, whose body steps the state by `next` and runs `f`
    on the item (`hF`, `hnone`, `hsome`), with each step `f acc i` read by `pb` at the state,
    the trip index and the trip count, is the counted loop of `pb`: the trip count is bound as a
    literal. The proof is `loop_indexed` and `foldRange_reify`. -/
theorem Reify.indexedForLoop {I Item σ : Type} [AeVal σ] {Γ : Ctxt nfDialect}
    {v : Var Γ (AeVal.nty σ)}
    {pb : NFProg nfDialect (AeVal.nty σ :: .word 64 :: .word 64 :: Γ) [AeVal.nty σ]}
    {next : I → RustM (Option Item × I)} {st₀ : I} {cnt : Usize}
    (it : IndexedIter next st₀ cnt)
    (F : I × σ → RustM (Aeneas.Std.ControlFlow (I × σ) σ))
    (K : σ → Option Item × I → RustM (Aeneas.Std.ControlFlow (I × σ) σ))
    (f : σ → Usize → RustM σ) (init : σ) (V : Valuation Γ)
    [hi : Lookup V (AeVal.emb init) v]
    (hF : ∀ st acc, F (st, acc) = next st >>= K acc)
    (hnone : ∀ acc r, K acc (none, r) = .ok (.done acc))
    (hsome : ∀ acc i r, (it.item i >>= fun x => K acc (some x, r)) =
      f acc i >>= fun a => .ok (.cont (r, a)))
    (hb : ∀ (i : Usize) (acc : σ),
      ReifyG single (f acc i) (vCons acc (vCons i (vCons cnt V))) pb) :
    ReifyG single (Aeneas.Std.loop F (st₀, init)) V
      (.var (litE cnt) (.forLoop .here (.cons v.there .nil) pb (.ret (.cons .here .nil)))) where
  sound y hy := by
    rw [← it.h0, loop_indexed it F K f hF hnone hsome cnt.val 0 init (by omega)] at hy
    have hn : cnt.val < 2 ^ 64 := lt64 cnt
    have hfold := foldRange_reify (vCons cnt V) pb f hb cnt.val 0 init y
      (by have := cnt.bv.isLt; simp only [UScalar.val] at this ⊢; omega) hy
    rw [nfToRustM, aeExpr_litE, bind_tc_ok, nfToRustM]
    have hc : HasWord64.toNat (d := nfDialect)
        ((Ctxt.Var.here (Γ := Γ)).lookup
          (Valuation.extend (t := NfTy.word 64) V (embW cnt))) = cnt.val := by
      change (BitVec.ofNat 64 cnt.val).toNat = cnt.val
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    have hinit : Expr.lookupArgs (HVector.cons v.there HVector.nil)
        (Valuation.extend (t := NfTy.word 64) V (embW cnt)) = single init := by
      change HVector.cons (v.lookup V) HVector.nil = _
      rw [hi.eq]
    rw [hc, hinit, List.range_eq_range', extend_eq]
    refine (congrArg (fun z => z >>= fun acc =>
      nfToRustM (NFProg.ret (HVector.cons Var.here HVector.nil))
        (hvAppend acc (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (embW cnt) V)))
          hfold).trans ?_
    rw [bind_tc_ok, nfToRustM]
    rfl

/-- A bind of a computation with the value `v` is the continuation at `v`. -/
theorem bind_of_eq_ok {α β : Type} (m : RustM α) (v : α) (h : m = .ok v) (k : α → RustM β) :
    (m >>= k) = k v := by
  rw [h, bind_tc_ok]

/-! ## The elaborator -/

/-- An NF program with its soundness statement `S`. -/
structure Reified {Γ : Ctxt nfDialect} {t : NfTy} (S : NFProg nfDialect Γ [t] → Prop) where
  /-- The program. -/
  prog : NFProg nfDialect Γ [t]
  /-- The soundness statement at the program. -/
  sound : S prog

namespace ReifyMeta

open Lean Meta Elab Term

/-- The type argument `α` of a computation `m : RustM α`. -/
meta def resTy (m : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType m)
  return t.appArg!

/-- The context `Γ` of a valuation `V : Valuation Γ`. -/
meta def ctxOf (V : Expr) : MetaM Expr := do
  let t ← whnfR (← inferType V)
  return t.appArg!

/-- The result types `ts` of a result map `E : α → Valuation ts`. -/
meta def tsOf (E : Expr) : MetaM Expr := do
  forallTelescope (← inferType E) fun _ b => do
    let b ← whnfR b
    return b.appArg!

/-- `ReifyE m V e` by instance resolution: the expression and the instance, or `none`. -/
meta def synthE (m V : Expr) : MetaM (Option (Expr × Expr)) := do
  let α ← resTy m
  let some inst ← synthInstance? (mkApp (mkConst ``AeVal) α) | return none
  let Γ ← ctxOf V
  let out ← mkFreshExprMVar none
  let ty := mkAppN (mkConst ``ReifyE) #[α, inst, m, Γ, V, out]
  match ← synthInstance? ty with
  | some r => return some (← instantiateMVars out, r)
  | none => return none

/-- `ReifyG E m V p` by instance resolution: the instance, or `none`. -/
meta def synthG (E m V : Expr) : MetaM (Option Expr) := do
  let α ← resTy m
  let ts ← tsOf E
  let Γ ← ctxOf V
  let out ← mkFreshExprMVar none
  synthInstance? (mkAppN (mkConst ``ReifyG) #[α, ts, E, m, Γ, V, out])

/-- The literal operand `c` of a computation `m`, by `LitOf`. -/
meta def litOf (m : Expr) : MetaM (Option Expr) := do
  let α ← resTy m
  let ty ← mkFreshExprMVar (some (mkConst ``UScalarTy))
  let c ← mkFreshExprMVar none
  match ← synthInstance? (mkAppN (mkConst ``LitOf) #[α, m, ty, c]) with
  | some _ => return some (← instantiateMVars c)
  | none => return none

/-- The program a proof of `ReifyG E m V p` is about. -/
meta def progOf (prf : Expr) : MetaM Expr := do
  return (← instantiateMVars (← inferType prf)).appArg!

/-- The chain `g` and the proof of `M = g >>= fun a => ok (cont (r, a))` for a bind chain `M`
    that ends in continuing with the range `r`: one step `tailCont_bind` per bind and the last
    step `tailCont_ok`. -/
meta partial def tailCont (r M : Expr) : MetaM (Expr × Expr) := do
  let M := (← instantiateMVars M).headBeta
  if M.isAppOfArity ``Bind.bind 6 then
    let m := M.getArg! 4
    let k := M.getArg! 5
    let α ← resTy m
    return ← withLocalDeclD `x α fun x => do
      let (gx, px) ← tailCont r (mkApp k x).headBeta
      let g ← mkLambdaFVars #[x] gx
      let h ← mkLambdaFVars #[x] px
      let g' ← mkAppM ``Bind.bind #[m, g]
      let pg ← mkAppM ``tailCont_bind #[r, m, k, g, h]
      return (g', pg)
  let M ← whnfR M
  if M.isAppOfArity ``Aeneas.Std.RustM.ok 2 then
    let c := M.getArg! 1
    if c.isAppOfArity ``Aeneas.Std.ControlFlow.cont 3 then
      let pr := c.getArg! 2
      if pr.isAppOfArity ``Prod.mk 4 then
        if ← isDefEq (pr.getArg! 2) r then
          let a := pr.getArg! 3
          let g ← mkAppM ``Aeneas.Std.RustM.ok #[a]
          let pg ← mkAppM ``tailCont_ok #[r, a]
          return (g, pg)
  throwError "reifyAeneas%: the step of the range loop does not end in continuing with the \
    stepped range{indentExpr M}"

/-- The step `f` of the body `F` of a range loop over `⟨_, n⟩` with states of type `σ`, and the
    proof of the hypothesis `hF` of `Reify.rangeForLoop`: the body at `(⟨s, n⟩, acc)` is unfolded by
    the equation lemma of the definition it calls, its bind of `IteratorRange.next` is
    `range_body`, whose continuation at `none` is done with `acc` and at `some i` and the
    stepped range `r` is the chain `f acc i` continued with `r` (`tailCont`). -/
meta def rangeStep (F n σ : Expr) : MetaM (Expr × Expr) := do
  let usize := Lean.mkConst ``Aeneas.Std.Usize
  withLocalDeclD `s usize fun sv => withLocalDeclD `acc σ fun acc => do
    let rng ← mkAppM ``core.ops.range.Range.mk #[sv, n]
    let lhs ← whnfCore (mkApp F (← mkAppM ``Prod.mk #[rng, acc]))
    let some c := lhs.getAppFn.constName? |
      throwError "reifyAeneas%: no reading of the range loop body{indentExpr lhs}"
    let some eqns ← getEqnsFor? c |
      throwError "reifyAeneas%: no equation lemma for the range loop body {c}"
    let eq1 := mkAppN (mkConst eqns[0]! lhs.getAppFn.constLevels!) lhs.getAppArgs
    let B := (← whnfR (← inferType eq1)).appArg!
    unless B.isAppOfArity ``Bind.bind 6 do
      throwError "reifyAeneas%: the range loop body does not step its range{indentExpr B}"
    let K := B.getArg! 5
    let rTy ← mkAppM ``core.ops.range.Range #[usize]
    let (f, hsome) ← withLocalDeclD `i usize fun i => withLocalDeclD `r rTy fun r => do
      let Ki := (← whnfCore (mkApp K (← mkAppM ``Prod.mk #[← mkAppM ``Option.some #[i], r])))
      let (g, pg) ← tailCont r Ki
      if g.containsFVar r.fvarId! || g.containsFVar sv.fvarId! then
        throwError "reifyAeneas%: the step of the range loop reads the range"
      return (← mkLambdaFVars #[acc, i] g, ← mkLambdaFVars #[i, r] pg)
    let hnone ← withLocalDeclD `r rTy fun r => do
      let Kn := mkApp K (← mkAppM ``Prod.mk #[← mkAppOptM ``Option.none #[usize], r])
      mkLambdaFVars #[r] (← mkEqRefl Kn)
    let rb ← mkAppM ``range_body #[n, sv, acc, K, f, hnone, hsome]
    let hF ← mkLambdaFVars #[sv, acc] (← mkEqTrans eq1 rb)
    return (f, hF)

/-- The binds of a chain with their continuations opened, each final computation in weak
    head normal form without unfolding (`whnfCore`): the matches of a loop body on the item and
    the stepped state are reduced. -/
meta partial def normBinds (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if e.isAppOfArity ``Bind.bind 6 then
    let k := e.getArg! 5
    if k.isLambda then
      let k' ← lambdaTelescope k fun xs b => do mkLambdaFVars xs (← normBinds b)
      return mkAppN e.getAppFn (e.getAppArgs.set! 5 k')
  whnfCore e

/-- The namespace of the adapter instances of `AeneasFront/Iterators.lean`, which a module
    applying `reifyAeneas%` to a loop over an iterator adapter imports. -/
meta def iterNs : Name := `CatCrypt.Crypto.SecureCompilation.AeneasFront

/-- The `IndexedIter` of an adapter state `st` as the backend prints it, with the bind lemma of
    its item (`i ↦ k ↦ proof of item i >>= k = …`), or `none`: `enumerate` and `step_by` of a
    range from `0`, `enumerate` of the iterator of an array, `zip` of the iterators of two
    arrays. -/
meta def adapterIter? (st : Expr) : MetaM (Option (Expr × (Expr → Expr → MetaM Expr))) := do
  let st ← whnfR st
  let rangeFrom0? (r : Expr) : MetaM (Option Expr) := do
    let r ← whnfR r
    if r.isAppOfArity ``core.ops.range.Range.mk 3 then
      if ← isDefEq (← mkAppM ``UScalar.val #[r.getArg! 1]) (mkNatLit 0) then
        return some (r.getArg! 2)
    return none
  let arrayIter? (it : Expr) : MetaM (Option Expr) := do
    let it ← whnfR it
    if it.isAppOfArity ``core.slice.iter.Iter.mk 3 then
      if ← isDefEq (it.getArg! 2) (mkNatLit 0) then
        let sl ← whnfR (it.getArg! 1)
        if sl.isAppOfArity ``Aeneas.Std.Array.to_slice 3 then
          return some (sl.getArg! 2)
    return none
  if st.isAppOfArity ``core.iter.adapters.enumerate.Enumerate.mk 3 then
    if let some n ← rangeFrom0? (st.getArg! 1) then
      return some (← mkAppM (iterNs ++ `enumRangeIter) #[n],
        fun i k => mkAppM (iterNs ++ `enumRange_item_bind) #[n, i, k])
    if let some a ← arrayIter? (st.getArg! 1) then
      return some (← mkAppM (iterNs ++ `enumArrayIter) #[a],
        fun i k => mkAppM (iterNs ++ `enumArray_item_bind) #[a, i, k])
  if st.isAppOfArity ``core.iter.adapters.step_by.StepBy.mk 3 then
    if let some n ← rangeFrom0? (st.getArg! 1) then
      let kk := st.getArg! 2
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``UScalar.val #[kk]])
      return some (← mkAppM (iterNs ++ `stepByRangeIter) #[n, kk, hk],
        fun i k => mkAppM (iterNs ++ `stepByRange_item_bind) #[n, kk, hk, i, k])
  if st.isAppOfArity ``core.iter.adapters.zip.Zip.mk 4 then
    if let some a ← arrayIter? (st.getArg! 2) then
      if let some b ← arrayIter? (st.getArg! 3) then
        return some (← mkAppM (iterNs ++ `zipArrayIter) #[a, b],
          fun i k => mkAppM (iterNs ++ `zipArray_item_bind) #[a, b, i, k])
  return none

/-- The continuation `K`, the step `f` and the hypotheses `hF`, `hnone`, `hsome` of
    `Reify.indexedForLoop` for the body `F` of a loop over the indexed iterator `itE` with
    states of type `σ`: the body at `(st, acc)` is unfolded by the equation lemma of the
    definition it calls into a bind of `next st` and `K acc`; at an item, the bind lemma `ib` of
    the item followed by `K` is split into the step and its final continuation (`tailCont`). -/
meta def indexedStep (F σ itE : Expr) (ib : Expr → Expr → MetaM Expr) :
    MetaM (Expr × Expr × Expr × Expr × Expr) := do
  let itTy ← whnfR (← inferType itE)
  let I := itTy.getArg! 0
  let Item := itTy.getArg! 1
  let (K, hF) ← withLocalDeclD `st I fun st => withLocalDeclD `acc σ fun acc => do
    let lhs ← whnfCore (mkApp F (← mkAppM ``Prod.mk #[st, acc]))
    let some c := lhs.getAppFn.constName? |
      throwError "reifyAeneas%: no reading of the adapter loop body{indentExpr lhs}"
    let some eqns ← getEqnsFor? c |
      throwError "reifyAeneas%: no equation lemma for the adapter loop body {c}"
    let eq1 := mkAppN (mkConst eqns[0]! lhs.getAppFn.constLevels!) lhs.getAppArgs
    let B := (← whnfR (← inferType eq1)).appArg!
    unless B.isAppOfArity ``Bind.bind 6 do
      throwError "reifyAeneas%: the adapter loop body does not step its iterator{indentExpr B}"
    let K ← mkLambdaFVars #[acc] (B.getArg! 5)
    if K.containsFVar st.fvarId! then
      throwError "reifyAeneas%: the adapter loop body reads its iterator"
    return (K, ← mkLambdaFVars #[st, acc] eq1)
  let hnone ← withLocalDeclD `acc σ fun acc => withLocalDeclD `r I fun r => do
    let none' ← mkAppOptM ``Option.none #[Item]
    mkLambdaFVars #[acc, r] (← mkEqRefl (mkApp2 K acc (← mkAppM ``Prod.mk #[none', r])))
  let usize := Lean.mkConst ``Aeneas.Std.Usize
  let (f, hsome) ← withLocalDeclD `acc σ fun acc => withLocalDeclD `i usize fun i =>
    withLocalDeclD `r I fun r => do
      let kx ← withLocalDeclD `x Item fun x => do
        mkLambdaFVars #[x] (mkApp2 K acc (← mkAppM ``Prod.mk #[← mkAppM ``Option.some #[x], r]))
      let hib ← ib i kx
      let rhs ← normBinds (← instantiateMVars (← inferType hib)).appArg!
      let (g, pg) ← tailCont r rhs
      if g.containsFVar r.fvarId! then
        throwError "reifyAeneas%: the step of the adapter loop reads the iterator"
      return (← mkLambdaFVars #[acc, i] g, ← mkLambdaFVars #[acc, i, r] (← mkEqTrans hib pg))
  return (K, f, hF, hnone, hsome)

/-- `ReadCond S V` by instance resolution: the bit, or `none`. -/
meta def readCond? (S V : Expr) : MetaM (Option Expr) := do
  let Γ ← ctxOf V
  let b ← mkFreshExprMVar (some (mkConst ``Bool))
  let e ← mkFreshExprMVar none
  match ← synthInstance? (mkAppN (mkConst ``ReadCond) #[Γ, S, V, b, e]) with
  | some _ => return some (← instantiateMVars b)
  | none => return none

/-- `ReadBit c V` by instance resolution: the context, the prefix, the valuation and the
    variable of the bit, and the instance, or `none`. -/
meta def readBit? (c V : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let Γ ← ctxOf V
  let Δ ← mkFreshExprMVar none
  let p ← mkFreshExprMVar none
  let W ← mkFreshExprMVar none
  let v ← mkFreshExprMVar none
  match ← synthInstance? (mkAppN (mkConst ``ReadBit) #[Γ, c, V, Δ, p, W, v]) with
  | some inst => return some (← instantiateMVars Δ, ← instantiateMVars p,
      ← instantiateMVars W, ← instantiateMVars v, inst)
  | none => return none

/-- The operands of the comparison `S`, by `CmpProp`, or none. -/
meta def cmpOperands (S : Expr) : MetaM (List Expr) := do
  let ty ← mkFreshExprMVar (some (mkConst ``UScalarTy))
  let c ← mkFreshExprMVar (some (mkConst ``CmpOp))
  let u := mkApp (mkConst ``UScalar) ty
  let x ← mkFreshExprMVar (some u)
  let y ← mkFreshExprMVar (some u)
  match ← synthInstance? (mkAppN (mkConst ``CmpProp) #[S, ty, c, x, y]) with
  | some _ => return [← instantiateMVars x, ← instantiateMVars y]
  | none => return []

/-- The valuation `V` holds the `64`-bit word `a` at a variable. -/
meta def hasWord (V a : Expr) : MetaM Bool := do
  let Γ ← ctxOf V
  let v ← mkFreshExprMVar none
  let w64 := mkApp (mkConst ``NfTy.word) (mkNatLit 64)
  return (← synthInstance? (mkAppN (mkConst ``Lookup) #[Γ, w64, V, a, v])).isSome

/-- The reading of a guard of `m` with the passing condition `S`, the continuation `k` and
    the proof `hm` that a value of `m` is a value of `k` under `S`. A condition read as one
    expression (`ReadCond`), after the operands of `S` that no variable of `V` holds are bound
    as literals (`Reify.letLit`), is read by `mk V' b` at the extended valuation `V'` and the
    bit `b` of `S`. Any other condition is read as a prefix and a bit (`ReadBit`) by
    `Reify.guardP`, with the continuation read by `readK` at its valuation. -/
meta def guardWith (m S V k hm : Expr) (mk : Expr → Expr → MetaM Expr)
    (readK : Expr → MetaM Expr) : MetaM Expr := do
  if let some b ← readCond? S V then return ← mk V b
  let mut lits : Array (Expr × Expr) := #[]
  let mut V' := V
  for x in ← cmpOperands S do
    unless ← hasWord V' (← mkAppM ``embW #[x]) do
      lits := lits.push (x, V')
      V' ← mkAppM ``vCons #[x, V']
  if let some b ← readCond? S V' then
    let mut prf ← mk V' b
    for (c, Vc) in lits.reverse do
      prf ← mkAppM ``Reify.letLit #[c, m, Vc, prf]
    return prf
  let c ← mkDecide S
  let some (Δ, p, W, v, inst) ← readBit? c V |
    throwError "reifyAeneas%: no reading of the condition{indentExpr S}"
  let hk ← readK (← mkAppM ``vCons #[← mkAppM ``not #[c], W])
  mkAppOptM ``Reify.guardP #[none, none, none, none, some Δ, some p, some W, some v, none,
    some S, none, some m, some k, some V, some inst, some hm, some hk]

/-- The valuation of the continuation of a guard on the bit `b` at `V`. -/
meta def guardVal (b V : Expr) : MetaM Expr := do
  mkAppM ``vCons #[← mkAppM ``not #[b], ← mkAppM ``vCons #[b, V]]

/-- **The reader.** Reads the computation `m` at the valuation `V` with the result map `E`
    and returns a proof of `ReifyG E m V p`; each step applies the congruence lemma of the
    construct at the head of `m`. A call of a definition of the crate `crate` (the root
    namespace of the reified function) is unfolded by its equation lemma. -/
meta partial def reify (crate : Name) (E m V : Expr) : MetaM Expr := do
  let m := (← instantiateMVars m).headBeta
  if let some prf ← synthG E m V then return prf
  let readUnder (α : Expr) (E' k : Expr) (V' : Expr) : MetaM Expr :=
    withLocalDeclD `x α fun x => do
      let prf ← reify crate E' (mkApp k x).headBeta (← mkAppM ``vCons #[x, V'])
      if (← progOf prf).containsFVar x.fvarId! then
        throwError "reifyAeneas%: the program of the continuation depends on its argument"
      mkLambdaFVars #[x] prf
  if m.isAppOfArity ``Bind.bind 6 then
    let m1 := m.getArg! 4
    let k := m.getArg! 5
    if m1.isAppOfArity ``Aeneas.Std.massert 2 then
      let P := m1.getArg! 0
      let k1 := (mkApp k (mkConst ``Unit.unit)).headBeta
      return ← guardWith m P V k1 (← mkAppM ``pass_massert #[P, k])
        (fun V' b => do mkAppM ``Reify.assert #[P, k, V', ← reify crate E k1 (← guardVal b V')])
        (reify crate E k1)
    let α ← resTy m1
    if (← synthE m1 V).isSome then
      return ← mkAppM ``Reify.bind #[m1, k, V, ← readUnder α E k V]
    if let some c ← litOf m1 then
      let Vc ← mkAppM ``vCons #[c, V]
      if (← synthE m1 Vc).isSome then
        return ← mkAppM ``Reify.bindLit #[c, m1, k, V, ← readUnder α E k Vc]
    if (← synthInstance? (mkApp (mkConst ``AeVal) α)).isNone then
      let w ← whnf m1
      if w.isAppOfArity ``Aeneas.Std.RustM.ok 2 then
        let v := w.getArg! 1
        let h ← mkExpectedTypeHint (← mkEqRefl m1) (← mkEq m1 w)
        let eq ← mkAppM ``bind_of_eq_ok #[m1, v, h, k]
        return ← mkAppM ``ReifyG.of_eq #[eq, ← reify crate E (mkApp k v).headBeta V]
    throwError "reifyAeneas%: no reading of the operation{indentExpr m1}"
  if m.isAppOfArity ``ite 5 then
    let c := m.getArg! 1
    let a := m.getArg! 3
    let b := m.getArg! 4
    let a' ← whnfR a
    if a'.isAppOfArity ``Aeneas.Std.RustM.fail 2 then
      let S ← mkAppM ``Not #[c]
      return ← guardWith m S V b (← mkAppM ``pass_iteFail #[c, a'.getArg! 1, b])
        (fun V' bit => do
          mkAppM ``Reify.iteFail #[c, a'.getArg! 1, b, V', ← reify crate E b (← guardVal bit V')])
        (reify crate E b)
    let b' ← whnfR b
    if b'.isAppOfArity ``Aeneas.Std.RustM.fail 2 then
      return ← guardWith m c V a (← mkAppM ``pass_iteFailElse #[c, a, b'.getArg! 1])
        (fun V' bit => do
          mkAppM ``Reify.iteFailElse #[c, a, b'.getArg! 1, V', ← reify crate E a (← guardVal bit V')])
        (reify crate E a)
    if c.isAppOfArity ``LT.lt 4 &&
        (← whnfR (← inferType (c.getArg! 2))).isAppOf ``UScalar then
      let x := c.getArg! 2
      let y := c.getArg! 3
      let bit ← mkAppM ``CmpOp.aen #[mkConst ``CmpOp.lt, x, y]
      let Vb ← mkAppM ``vCons #[bit, V]
      return ← mkAppM ``Reify.iteLt #[x, y, a, b, V, ← reify crate E a Vb, ← reify crate E b Vb]
    let dc := m.getArg! 2
    if let some (Δ, p, W, v, inst) ← readBit? (← mkAppOptM ``decide #[c, dc]) V then
      return ← mkAppOptM ``Reify.iteBit #[none, none, none, none, some Δ, some p, some W,
        some v, none, none, some c, some dc, some a, some b, some V, some inst,
        some (← reify crate E a W), some (← reify crate E b W)]
    throwError "reifyAeneas%: no reading of the condition{indentExpr c}"
  if m.isAppOfArity ``Aeneas.Std.loop 4 then
    let σ := m.getArg! 0
    let body := m.getArg! 2
    let init := m.getArg! 3
    let σw ← whnfR σ
    if init.isAppOfArity ``Prod.mk 4 && σw.isAppOfArity ``Prod 2 then
      let rng ← whnfR (init.getArg! 2)
      if rng.isAppOfArity ``core.ops.range.Range.mk 3 then
        let s := rng.getArg! 1
        let n := rng.getArg! 2
        unless ← isDefEq (← mkAppM ``UScalar.val #[s]) (mkNatLit 0) do
          throwError "reifyAeneas%: a range loop whose range does not start at 0{indentExpr rng}"
        let σ' := σw.getArg! 1
        let acc0 := init.getArg! 3
        let (f, hF) ← rangeStep body n σ'
        let E' ← mkAppOptM ``single #[some σ', none]
        let hb ← withLocalDeclD `i (Lean.mkConst ``Aeneas.Std.Usize) fun i =>
          withLocalDeclD `acc σ' fun acc => do
            let V' ← mkAppM ``vCons #[acc, ← mkAppM ``vCons #[i, ← mkAppM ``vCons #[n, V]]]
            let prf ← reify crate E' (mkApp2 f acc i).headBeta V'
            let p ← progOf prf
            if p.containsFVar i.fvarId! || p.containsFVar acc.fvarId! then
              throwError "reifyAeneas%: the program of the range loop step depends on its state"
            mkLambdaFVars #[i, acc] prf
        return ← mkAppM ``Reify.rangeForLoop #[body, n, acc0, f, V, hF, hb]
      if let some (itE, ib) ← adapterIter? rng then
        let σ' := σw.getArg! 1
        let acc0 := init.getArg! 3
        let cnt := (← whnfR (← inferType itE)).getArg! 4
        let (K, f, hF, hnone, hsome) ← indexedStep body σ' itE ib
        let E' ← mkAppOptM ``single #[some σ', none]
        let hb ← withLocalDeclD `i (Lean.mkConst ``Aeneas.Std.Usize) fun i =>
          withLocalDeclD `acc σ' fun acc => do
            let V' ← mkAppM ``vCons #[acc, ← mkAppM ``vCons #[i, ← mkAppM ``vCons #[cnt, V]]]
            let prf ← reify crate E' (mkApp2 f acc i).headBeta V'
            let p ← progOf prf
            if p.containsFVar i.fvarId! || p.containsFVar acc.fvarId! then
              throwError "reifyAeneas%: the program of the adapter loop step depends on its state"
            mkLambdaFVars #[i, acc] prf
        return ← mkAppM ``Reify.indexedForLoop #[itE, body, K, f, acc0, V, hF, hnone, hsome, hb]
    let Es ← mkAppOptM ``stepVal #[some σ, none]
    return ← mkAppM ``Reify.loop #[body, init, V, ← readUnder σ Es body V]
  if let some c ← litOf m then
    let Vc ← mkAppM ``vCons #[c, V]
    if (← synthE m Vc).isSome then
      let α ← resTy m
      let some ainst ← synthInstance? (mkApp (mkConst ``AeVal) α) |
        throwError "reifyAeneas%: no NF type of{indentExpr α}"
      let Γ ← ctxOf V
      let w64 := mkApp (mkConst ``NfTy.word) (mkNatLit 64)
      let out ← mkFreshExprMVar none
      let ty := mkAppN (mkConst ``ReifyE)
        #[α, ainst, m, ← mkAppM ``List.cons #[w64, Γ], Vc, out]
      if let some inst ← synthInstance? ty then
        return ← mkAppOptM ``Reify.okLit #[some α, some ainst, some Γ, none, none,
          some (← instantiateMVars out), some c, some m, some V, some inst]
  if let some c := m.getAppFn.constName? then
    if c.getRoot == crate then
      if let some eqns ← getEqnsFor? c then
        let fn := m.getAppFn
        let eqPrf := mkAppN (mkConst eqns[0]! fn.constLevels!) m.getAppArgs
        let rhs := (← whnfR (← inferType eqPrf)).appArg!
        return ← mkAppM ``ReifyG.of_eq #[eqPrf, ← reify crate E rhs V]
  throwError "reifyAeneas%: no reading of{indentExpr m}"

/-- `reifyAeneas% f`: the NF program of the Aeneas function `f` with the proof, for all
    arguments `xs`, of `Reify (f xs) (vCons x₁ (… vNil)) p`. The equation lemma of `f`, and of
    the definitions of its crate it calls (its loop bodies), are the only unfoldings. -/
elab "reifyAeneas% " f:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo f
  let info ← getConstInfo c
  let some eqns ← getEqnsFor? c | throwError "reifyAeneas%: no equation lemma for {c}"
  let lvls := info.levelParams.map Level.param
  forallTelescope info.type fun xs _ => do
    let isBool (x : Expr) : TermElabM Bool := do
      return (← whnfR (← inferType x)).isConstOf ``Bool
    let V ← xs.foldrM (fun x acc => do
      if ← isBool x then mkAppM ``wCons #[x, acc] else mkAppM ``vCons #[x, acc])
      (mkConst ``vNil)
    let eqPrf := mkAppN (mkConst eqns[0]! lvls) xs
    let eqTy ← whnfR (← inferType eqPrf)
    let rhs := eqTy.appArg!
    let resT ← resTy rhs
    let boolRes := (← whnfR resT).isConstOf ``Bool
    let E ← if boolRes then pure (Lean.mkConst ``bitRes) else mkAppOptM ``single #[some resT, none]
    let bools ← xs.filterM isBool
    let zero := Lean.mkConst ``zeroU
    let mut Vs : Array Expr := #[]
    let mut Vb := V
    for b in bools do
      Vs := Vs.push Vb
      Vb ← mkAppM ``vCons #[b, ← mkAppM ``vCons #[zero, Vb]]
    let mut prf ← reify c.getRoot E rhs Vb
    for (b, Vi) in bools.zip Vs |>.reverse do
      prf ← mkAppM ``Reify.argBit #[b, rhs, Vi, prf]
    let p ← progOf prf
    if xs.any (fun x => p.containsFVar x.fvarId!) then
      throwError "reifyAeneas%: the program depends on the arguments"
    let prfEq ← mkAppM ``ReifyG.of_eq #[eqPrf, prf]
    let fx := mkAppN (mkConst c lvls) xs
    let S ← withLocalDeclD `p (← inferType p) fun q => do
      let body ← mkForallFVars xs (← if boolRes then mkAppM ``ReifyG #[E, fx, V, q]
        else mkAppM ``Reify #[fx, V, q])
      mkLambdaFVars #[q] body
    let sound ← mkLambdaFVars xs prfEq
    mkAppOptM ``Reified.mk #[none, none, some S, some p, some sound]

end ReifyMeta

end CatCrypt.Crypto.SecureCompilation.AeneasFront
