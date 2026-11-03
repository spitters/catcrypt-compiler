/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Loops
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
* a branch `if x < y then a else b` (and `≤`, `>`, `≥`, `=`): `Reify.iteCmp`;
* an operation: the `ReifyE` instances of the checked arithmetic, the lifted bitwise
  operations, the wrapping operations, `Array.index_usize` and `Array.update`;
* a variable: `Lookup`, the position of a value in the valuation.

Instance resolution follows the syntax of the body, and the proof term it returns is the
composition of these lemmas. The elaborator unfolds only the equation lemma `f.eq_1` of the
function. There is no definitional check of the whole term.

## Main definitions

* `AeVal`: the NF type and value of an Aeneas value
* `Lookup`, `ReifyE`, `Reify`: the judgements
* `Reified`: an NF program with its soundness statement
* `reifyAeneas%`: the elaborator
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

/-- The checked operations at a width of the table read their tagged name. -/
theorem aeCall2_checked {ty : UScalarTy} [h : TableTy ty] (o : AOp) (ho : taggedOp o = true)
    (x y : UScalar ty) :
    aeCall2 (checkedName o ty) (wordV x) (wordV y) =
      (o.aen x y >>= fun z => .ok (wordV z)) := by
  have hw : wordOpAt? (checkedName o ty) = none := by
    have := h.table
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd this (by decide) | decide +kernel
  have hc : checkedAt? (checkedName o ty) = some (ty, o) := by
    have := h.table
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd this (by decide) | decide +kernel
  unfold aeCall2
  rw [hw, hc]
  simp only [h.table, ho, Bool.and_self, ite_true, readW_wordV, bind_tc_ok]

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

instance reifyE_add {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (x + y) V (callE2 (checkedName .add ty) (.word 64) va vb) :=
  reifyE_call2 _ (AOp.aen .add) (aeCall2_checked .add rfl) x y V va vb hx.eq hy.eq

instance reifyE_sub {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hy : Lookup V (embW y) vb] :
    ReifyE (x - y) V (callE2 (checkedName .sub ty) (.word 64) va vb) :=
  reifyE_call2 _ (AOp.aen .sub) (aeCall2_checked .sub rfl) x y V va vb hx.eq hy.eq

instance reifyE_mul {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
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
    let α ← resTy m1
    if (← synthE m1 V).isSome then
      return ← mkAppM ``Reify.bind #[m1, k, V, ← readUnder α E k V]
    if let some c ← litOf m1 then
      let Vc ← mkAppM ``vCons #[c, V]
      if (← synthE m1 Vc).isSome then
        return ← mkAppM ``Reify.bindLit #[c, m1, k, V, ← readUnder α E k Vc]
    throwError "reifyAeneas%: no reading of the operation{indentExpr m1}"
  if m.isAppOfArity ``ite 5 then
    let c := m.getArg! 1
    let a := m.getArg! 3
    let b := m.getArg! 4
    if c.isAppOfArity ``LT.lt 4 then
      let x := c.getArg! 2
      let y := c.getArg! 3
      let bit ← mkAppM ``CmpOp.aen #[mkConst ``CmpOp.lt, x, y]
      let Vb ← mkAppM ``vCons #[bit, V]
      return ← mkAppM ``Reify.iteLt #[x, y, a, b, V, ← reify crate E a Vb, ← reify crate E b Vb]
    throwError "reifyAeneas%: no reading of the condition{indentExpr c}"
  if m.isAppOfArity ``Aeneas.Std.loop 4 then
    let σ := m.getArg! 0
    let body := m.getArg! 2
    let init := m.getArg! 3
    let Es ← mkAppOptM ``stepVal #[some σ, none]
    return ← mkAppM ``Reify.loop #[body, init, V, ← readUnder σ Es body V]
  if let some c ← litOf m then
    let Vc ← mkAppM ``vCons #[c, V]
    if (← synthE m Vc).isSome then
      return ← mkAppM ``Reify.okLit #[c, m, V]
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
    let V ← xs.foldrM (fun x acc => mkAppM ``vCons #[x, acc]) (mkConst ``vNil)
    let eqPrf := mkAppN (mkConst eqns[0]! lvls) xs
    let eqTy ← whnfR (← inferType eqPrf)
    let rhs := eqTy.appArg!
    let E ← mkAppOptM ``single #[some (← resTy rhs), none]
    let prf ← reify c.getRoot E rhs V
    let p ← progOf prf
    if xs.any (fun x => p.containsFVar x.fvarId!) then
      throwError "reifyAeneas%: the program depends on the arguments"
    let prf ← mkAppM ``ReifyG.of_eq #[eqPrf, prf]
    let fx := mkAppN (mkConst c lvls) xs
    let S ← withLocalDeclD `p (← inferType p) fun q => do
      let body ← mkForallFVars xs (← mkAppM ``Reify #[fx, V, q])
      mkLambdaFVars #[q] body
    let sound ← mkLambdaFVars xs prf
    mkAppOptM ``Reified.mk #[none, none, some S, some p, some sound]

end ReifyMeta

end CatCrypt.Crypto.SecureCompilation.AeneasFront
