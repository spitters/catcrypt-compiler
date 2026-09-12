/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Defs
public import Mathlib.Data.Fin.Basic
public import Init.Data.BitVec.Basic


@[expose] public section
set_option autoImplicit false

/-!
# Mechanical port of jasminc's Coq operational semantics

This file is a **line-by-line mechanical port** of the relevant subset of the
jasminc Coq operational semantics (Phase B approach 2 of the AST-direct emit
work). Every ported definition carries a `-- mirror of <file>:<line> (<name>)`
provenance comment pointing back to the Coq source.

**Source repository**: the Jasmin `proofs/lang/` tree
(reference, READ-ONLY).

## Tiers ported

* **Tier 1 — Types**: `WSize`, `Atype`, `Ctype`, `Var`, `VarI`, `GVar`,
  `Value`, `Pexpr`, `Lval`, `Sopn`, `InstrR`, `Instr`, `Cmd`.
* **Tier 2 — Core semantics**: `exec`, `Vm` (varmap), `Estate`, `Mem`, and
  the `sem_pexpr` / `sem_pexprs` / `write_var` / `write_vars` / `write_lval`
  / `sem_sopn` family.
* **Tier 3 — Top-level semantics**: `sem_i`, `sem_I`, `sem` as a single
  `Inductive` (mutually-recursive in Coq), ported as a Lean `inductive ... where ...`.
* **Tier 4 — Smoke tests**: see `Examples/JasminCoqSemMirrorDemo.lean`.

## Design choices (NON-MIRRORED, documented)

The Coq sources use Mathcomp `seq`, `ssrnat`, dependent records, and Section
contexts heavily. To preserve algebra without dragging in those dependencies:

| Coq idiom | Lean choice | Rationale |
|---|---|---|
| `seq T` (Mathcomp) | `List T` | Same algebra (cons-list). |
| `nat` (Coq) | `Nat` | Same algebra. |
| `Z` (Coq) | `Int` | Same algebra. |
| `positive` | `Nat` (interpreted as positive) | We tag with `1+n` shape where needed. |
| `word sz` (Mathcomp/word) | `BitVec sz.bits` | Standard mapping. |
| `WArray.array n` | `JArrayMirror n` (= `Fin n → BitVec 8`) | Functional array; algebra agrees for non-aliasing programs. |
| `exec T` (Coq `result error T`) | `JResult T` | Sum type with named error constructors. |
| `Section ... Context {wsw:WithSubWord} (gd : glob_decls).` | `variable` block + `gd` parameter | Lean lacks Coq Sections; thread parameters explicitly. |
| Mutually-recursive `Inductive sem ... with sem_I ... with sem_i ...` | Single Lean `inductive` block with constructors of each judgement | Same shape. |

## What this file deliberately does NOT do

* No proofs (beyond `decide`-checked smoke tests in the demo file).
* No bridge to `BignumExec` or the existing `JasminSem.lean`. That is Phase C.
* No port of the `asmOp` / `Sopn`-class infrastructure; we use an opaque
  `AsmOp` token plus an `AsmSem` user-supplied semantics function. This
  matches the existing `JasminAST.lean` and lets the user plug in any
  concrete asm-op set later.
* No port of `glob_decls` / `mem` byte-content details — they're typeclass
  parameters (`MemModel`, `GlobDecls`).

The provenance comments use the schema `mirror of <basename>.v:<line>
(<coq-name>)`.
-/

namespace CatCrypt.Crypto.Jasmin.CoqSemMirror

/-! ## §0. Bookkeeping types

These wrap the standard library to give them Coq-side names. -/

-- mirror of utils.v (exec / result error)
/-- `JResult α` mirrors Coq's `exec α := result error α` (`utils.v`).
    We carry the error tag inline. -/
inductive JResult (α : Type) where
  | ok : α → JResult α
  | typeError : JResult α                     -- mirror of utils.v: `type_error`
  | undefError : JResult α                    -- mirror of utils.v: `undef_error`
  | addrUndef : JResult α                     -- mirror of utils.v: `ErrAddrUndef`
  | otherErr (msg : String) : JResult α       -- mirror of utils.v: ErrType + assertions
  deriving Inhabited

namespace JResult
variable {α β γ : Type}

/-- Monadic bind (Coq's `Let x := r in body` notation). -/
def bind : JResult α → (α → JResult β) → JResult β
  | .ok a,         f => f a
  | .typeError,    _ => .typeError
  | .undefError,   _ => .undefError
  | .addrUndef,    _ => .addrUndef
  | .otherErr m,   _ => .otherErr m

/-- `Let` notation matches Coq's `Let x := e in body`. -/
instance : Monad JResult where
  pure := JResult.ok
  bind := JResult.bind

/-! ### §0.a. Bind-fusion lemmas (2026-05-28)

These are the canonical algebraic laws of the `JResult` monad,
exposed as `@[simp]` lemmas so that downstream proofs (and any
`decide`/`native_decide` reduction) can flatten deeply-nested bind
chains without growing the C-side closure stack.  Used by the MAYO
universal-connector closure path (see
`SecureCompilation/MLIR/VectorDialect/MayoLeafJasminFullBody.lean`). -/

/-- The left identity (`pure-bind`) — used by the `Cassgn`/`Copn`
    arms which all start with `do let v ← .ok ...`. -/
@[simp] theorem bind_ok (a : α) (f : α → JResult β) :
    JResult.bind (.ok a) f = f a := rfl

/-- Bind through the typeError forwarder. -/
@[simp] theorem bind_typeError (f : α → JResult β) :
    JResult.bind (.typeError) f = .typeError := rfl

/-- Bind through the undefError forwarder. -/
@[simp] theorem bind_undefError (f : α → JResult β) :
    JResult.bind (.undefError) f = .undefError := rfl

/-- Bind through the addrUndef forwarder. -/
@[simp] theorem bind_addrUndef (f : α → JResult β) :
    JResult.bind (.addrUndef) f = .addrUndef := rfl

/-- Bind through the otherErr forwarder. -/
@[simp] theorem bind_otherErr (m : String) (f : α → JResult β) :
    JResult.bind (.otherErr m) f = .otherErr m := rfl

/-- The right identity (`bind-pure`) of the `JResult` monad. -/
theorem bind_pure_right (r : JResult α) :
    JResult.bind r (fun a => .ok a) = r := by
  cases r <;> rfl

/-- Associativity of `bind` — fundamental to bind-chain fusion. -/
theorem bind_assoc (r : JResult α) (f : α → JResult β) (g : β → JResult γ) :
    JResult.bind (JResult.bind r f) g
      = JResult.bind r (fun a => JResult.bind (f a) g) := by
  cases r <;> rfl

/-- Bind through `Monad.bind` notation matches the concrete `JResult.bind`. -/
@[simp] theorem monad_bind_eq (r : JResult α) (f : α → JResult β) :
    (r >>= f) = JResult.bind r f := rfl

/-- `pure` through `Monad.pure` is `.ok`. -/
@[simp] theorem pure_eq_ok (a : α) : (pure a : JResult α) = .ok a := rfl

/-- `mapM` over a `List` returning a `JResult`. -/
def mapM (f : α → JResult β) : List α → JResult (List β)
  | []      => .ok []
  | a :: as => do let b ← f a; let bs ← mapM f as; .ok (b :: bs)

/-- `fold2` mirrors Coq utils `fold2 err f xs ys s` — fails with `err` on length mismatch. -/
def fold2 {γ : Type} (err : JResult α) (f : β → γ → α → JResult α) :
    List β → List γ → α → JResult α
  | [],      [],      s => .ok s
  | b :: bs, c :: cs, s => do let s' ← f b c s; fold2 err f bs cs s'
  | _,       _,       _ => err

end JResult

open JResult

/-! ## §1. Tier 1: Syntax types -/

-- mirror of wsize.v: Variant wsize
/-- `WSize` mirrors Coq `wsize` (`wsize.v`).  Six machine widths. -/
inductive WSize where
  | U8 | U16 | U32 | U64 | U128 | U256
  deriving DecidableEq, Repr, Inhabited

namespace WSize
-- mirror of wsize.v: Definition wsize_size_minus_1 + nat_of_wsize
/-- Number of bits per word size (`wsize.v: wsize_bits`). -/
def bits : WSize → Nat
  | .U8 => 8 | .U16 => 16 | .U32 => 32
  | .U64 => 64 | .U128 => 128 | .U256 => 256

-- mirror of wsize.v: Definition wsize_size
/-- Number of bytes per word size (`wsize.v: wsize_size`). -/
def bytes : WSize → Nat
  | .U8 => 1 | .U16 => 2 | .U32 => 4
  | .U64 => 8 | .U128 => 16 | .U256 => 32

-- mirror of wsize.v: Notation Uptr := U64
/-- Pointer size (`wsize.v: Uptr`). -/
def Uptr : WSize := .U64
end WSize

-- mirror of type.v:22-26: Variant atype : Set
/-- `Atype` mirrors Coq `atype` — the "program-visible" type system
    (`type.v` lines 22–26: `abool`, `aint`, `aarr ws n`, `aword ws`). -/
inductive Atype where
  | abool : Atype
  | aint  : Atype
  | aarr (ws : WSize) (n : Nat) : Atype       -- positive in Coq; we use Nat
  | aword (ws : WSize) : Atype
  deriving DecidableEq, Repr, Inhabited

-- mirror of type.v:30-34: Variant ctype : Set
/-- `Ctype` mirrors Coq `ctype` — the "semantic" type system used by `value`
    (`type.v` lines 30–34: `cbool`, `cint`, `carr n`, `cword ws`).  Note the
    array constructor takes only a byte-count `n` (no `ws`). -/
inductive Ctype where
  | cbool : Ctype
  | cint  : Ctype
  | carr (n : Nat) : Ctype
  | cword (ws : WSize) : Ctype
  deriving DecidableEq, Repr, Inhabited

-- mirror of type.v:36-40: Definition atype_of_ltype  (we omit ltype; see header)
-- mirror of type.v:236-240: Definition is_word_type
/-- `Atype.isWordType ty = some sz` iff `ty = aword sz`.  Mirrors
    `type.v:236 (is_word_type)`. -/
def Atype.isWordType : Atype → Option WSize
  | .aword sz => some sz
  | _ => none

-- mirror of var.v:45-46: Record var := Var { vtype : atype; vname : ident }
/-- `Var` mirrors Coq `var` (`var.v:45`): a typed identifier.
    Coq uses an opaque `ident` type from `ident.v`; we model it as `String`. -/
structure Var where
  vtype : Atype
  vname : String
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v:233-236: Record var_i := VarI { v_var :> var; v_info : var_info }
/-- `VarI` mirrors Coq `var_i` (`expr.v:233`).  `v_info` carries dummy source
    location info; we keep it as `Unit` because no semantic rule depends on it. -/
structure VarI where
  v_var : Var
  v_info : Unit := ()
  deriving Repr, Inhabited

instance : DecidableEq VarI := fun a b => by
  rcases a with ⟨v1, _⟩
  rcases b with ⟨v2, _⟩
  by_cases h : v1 = v2
  · exact .isTrue (by subst h; rfl)
  · exact .isFalse (fun e => h (by injection e))

-- mirror of expr.v:248-251: Variant v_scope := Slocal | Sglob
/-- `VScope` mirrors Coq `v_scope` (`expr.v:248`). -/
inductive VScope where
  | Slocal | Sglob
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v:254: Record gvar := Gvar { gv : var_i; gs : v_scope }
/-- `GVar` mirrors Coq `gvar` (`expr.v:254`). -/
structure GVar where
  gv : VarI
  gs : VScope
  deriving Repr, Inhabited

-- mirror of expr.v:256-257: Definition mk_gvar / mk_lvar
def mkGvar (x : VarI) : GVar := { gv := x, gs := .Sglob }
def mkLvar (x : VarI) : GVar := { gv := x, gs := .Slocal }

-- mirror of expr.v:259-260
def GVar.isLvar (x : GVar) : Bool := x.gs == .Slocal
def GVar.isGlob (x : GVar) : Bool := x.gs == .Sglob

-- mirror of var.v: Definition funname
/-- `FunName` mirrors Coq `funname` (`var.v`).  Coq uses an `int63` tag; we
    use a `String` since semantic rules only need decidable equality. -/
structure FunName where
  name : String
  deriving DecidableEq, Repr, Inhabited

/-! ### §1.b. Operators

We do **not** mirror the full Mathcomp-dependent typing infrastructure
(`sem_op_typed`, `etype_of_op1/2`, the `extended_type` family).  Instead we
expose `sop1`/`sop2` as inductive enums and supply user-pluggable semantic
functions `semOp1Impl` / `semOp2Impl` at semantic time.  This is faithful to
the surface syntax and lets us bridge to the `JasminAST.SOp1/SOp2` already
defined in `JasminAST.lean` without circular imports. -/

-- mirror of operators.v: Variant signedness
inductive Signedness where | Signed | Unsigned
  deriving DecidableEq, Repr, Inhabited

-- mirror of operators.v: Variant op_kind
inductive OpKind where
  | Op_int : OpKind
  | Op_w (sz : WSize) : OpKind
  deriving DecidableEq, Repr, Inhabited

-- mirror of operators.v: Variant cmp_kind
inductive CmpKind where
  | Cmp_int : CmpKind
  | Cmp_w (s : Signedness) (sz : WSize) : CmpKind
  deriving DecidableEq, Repr, Inhabited

-- mirror of operators.v: Variant sop1 (subset)
/-- `SOp1` mirrors Coq `sop1` (`operators.v`).  We omit the `wiop1` variants
    (`Owi1`) since they're used only by the `wint` extension; the asm-side
    bignum kernels we target do not produce them. -/
inductive SOp1 where
  | Oword_of_int (sz : WSize) : SOp1
  | Oint_of_word (s : Signedness) (sz : WSize) : SOp1
  | Osignext (szo szi : WSize) : SOp1
  | Ozeroext (szo szi : WSize) : SOp1
  | Onot : SOp1
  | Olnot (sz : WSize) : SOp1
  | Oneg (k : OpKind) : SOp1
  deriving DecidableEq, Repr, Inhabited

-- mirror of operators.v: Variant sop2 (subset, no wiop2 / vector variants)
/-- `SOp2` mirrors Coq `sop2`.  Subset: scalar arithmetic and comparison;
    SIMD/vector ops and the wint subset are deferred (the Phase-C asm bridge
    handles them at the asm-op layer). -/
inductive SOp2 where
  | Obeq | Oand | Oor : SOp2
  | Oadd (k : OpKind) | Omul (k : OpKind) | Osub (k : OpKind) : SOp2
  | Odiv (s : Signedness) (k : OpKind) | Omod (s : Signedness) (k : OpKind) : SOp2
  | Olsl (k : OpKind) | Oasr (k : OpKind) : SOp2
  | Oland (sz : WSize) | Olor (sz : WSize) | Olxor (sz : WSize) : SOp2
  | Olsr (sz : WSize) | Oror (sz : WSize) | Orol (sz : WSize) : SOp2
  | Oeq (k : OpKind) | Oneq (k : OpKind) : SOp2
  | Olt (k : CmpKind) | Ole (k : CmpKind) | Ogt (k : CmpKind) | Oge (k : CmpKind) : SOp2
  deriving DecidableEq, Repr, Inhabited

-- mirror of operators.v: Variant opN (subset)
inductive OpN where
  | Opack (ws : WSize) (pe : WSize) : OpN
  | Ocombine_flags (cf : Nat) : OpN  -- combine_flags tag as Nat
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v: arr_access
/-- `ArrAccess` mirrors Coq `arr_access` (`expr.v`, in `warray_` upstream). -/
inductive ArrAccess where
  | AAscale  | AAdirect
  deriving DecidableEq, Repr, Inhabited

-- mirror of memory_model.v: Variant aligned
/-- We rename the `Aligned` constructor to `IsAligned` to avoid Lean's duplicate-namespace lint. -/
inductive Aligned where | IsAligned | Unaligned
  deriving DecidableEq, Repr, Inhabited

/-! ### §1.c. Expressions, l-values, instructions -/

-- mirror of expr.v:262-273: Inductive pexpr
/-- `Pexpr` mirrors Coq `pexpr` (`expr.v:262`).  Constructors and argument
    order match line-for-line. -/
inductive Pexpr where
  | Pconst (z : Int) : Pexpr                                              -- expr.v:263
  | Pbool (b : Bool) : Pexpr                                              -- expr.v:264
  | Parr_init (ws : WSize) (n : Nat) : Pexpr                              -- expr.v:265
  | Pvar (v : GVar) : Pexpr                                               -- expr.v:266
  | Pget (al : Aligned) (aa : ArrAccess) (ws : WSize)
         (x : GVar) (idx : Pexpr) : Pexpr                                 -- expr.v:267
  | Psub (aa : ArrAccess) (ws : WSize) (len : Nat)
         (x : GVar) (idx : Pexpr) : Pexpr                                 -- expr.v:268
  | Pload (al : Aligned) (sz : WSize) (e : Pexpr) : Pexpr                 -- expr.v:269
  | Papp1 (op : SOp1) (e : Pexpr) : Pexpr                                 -- expr.v:270
  | Papp2 (op : SOp2) (e1 e2 : Pexpr) : Pexpr                             -- expr.v:271
  | PappN (op : OpN) (es : List Pexpr) : Pexpr                            -- expr.v:272
  | Pif (ty : Atype) (cond e1 e2 : Pexpr) : Pexpr                         -- expr.v:273
  deriving Inhabited

-- mirror of expr.v:275: Notation pexprs := (seq pexpr)
abbrev Pexprs := List Pexpr

-- mirror of expr.v:313-318: Variant lval
/-- `Lval` mirrors Coq `lval` (`expr.v:313`). -/
inductive Lval where
  | Lnone (i : Unit) (ty : Atype) : Lval                                  -- expr.v:314
  | Lvar  (x : VarI) : Lval                                               -- expr.v:315
  | Lmem  (al : Aligned) (sz : WSize) (i : Unit) (e : Pexpr) : Lval       -- expr.v:316
  | Laset (al : Aligned) (aa : ArrAccess) (ws : WSize)
          (x : VarI) (idx : Pexpr) : Lval                                 -- expr.v:317
  | Lasub (aa : ArrAccess) (ws : WSize) (len : Nat)
          (x : VarI) (idx : Pexpr) : Lval                                 -- expr.v:318
  deriving Inhabited

-- mirror of expr.v:322: Notation lvals := (seq lval)
abbrev Lvals := List Lval

-- mirror of expr.v:342: Variant dir := UpTo | DownTo
inductive Dir where | UpTo | DownTo
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v:346: Definition range := (dir * pexpr * pexpr)%type
/-- `Range` mirrors Coq `range = (dir * pexpr * pexpr)`. -/
structure Range where
  dir : Dir
  lo : Pexpr
  hi : Pexpr
  deriving Inhabited

-- mirror of expr.v:348-353: Definition wrange
/-- `wrange d n1 n2` mirrors Coq `wrange` (`expr.v:348`).  Produces the
    iteration list `[n1, n1+1, …, n2-1]` for `UpTo`, or `[n2, n2-1, …, n1+1]`
    for `DownTo`.  Both branches have length `(n2 - n1).toNat`. -/
def wrange (d : Dir) (n1 n2 : Int) : List Int :=
  let n : Nat := (n2 - n1).toNat
  match d with
  | .UpTo   => (List.range n).map (fun i : Nat => n1 + (Int.ofNat i))
  | .DownTo => (List.range n).map (fun i : Nat => n2 - (Int.ofNat i))

-- mirror of expr.v:378-386: Variant assgn_tag
inductive AssgnTag where
  | AT_none | AT_keep | AT_rename | AT_inline | AT_phinode
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v:392-394: Variant align := Align | NoAlign
/-- We rename the `Align` constructor to `IsAlign` to avoid duplicate-namespace lint. -/
inductive Align where | IsAlign | NoAlign
  deriving DecidableEq, Repr, Inhabited

-- mirror of expr.v: opaque token for instr_info (positive in Coq)
abbrev InstrInfo := Unit

-- mirror of sopn.v: Inductive sopn (we expose only the surface tag)
/-- `Sopn` mirrors Coq `sopn` (`sopn.v`).  The Coq inductive has variants
    `Ocopy`, `Onop`, `Omulu`, etc. as well as the asm-tagged variant
    `Oasm of asm_op_msb_t`.  We expose them as a small enum + an opaque
    `Oasm` token holding the asm-op identifier; the user supplies the
    concrete semantics via `AsmSem` (see §2.c). -/
inductive Sopn where
  | Ocopy (ws : WSize) (p : Nat) : Sopn
  | Onop : Sopn
  | Omulu (sz : WSize) : Sopn
  | Oaddcarry (sz : WSize) : Sopn
  | Osubcarry (sz : WSize) : Sopn
  | Oasm (op : String) : Sopn                  -- opaque asm-op id
  deriving DecidableEq, Repr, Inhabited

-- mirror of syscall.v: opaque syscall token
abbrev SyscallT := String

mutual
-- mirror of expr.v:412-422: Inductive instr_r ... with instr := MkI : ...
/-- `InstrR` mirrors Coq `instr_r` (`expr.v:412`). -/
inductive InstrR where
  | Cassgn   (lv : Lval) (tag : AssgnTag) (ty : Atype) (e : Pexpr) : InstrR
  | Copn     (xs : Lvals) (tag : AssgnTag) (op : Sopn) (es : Pexprs) : InstrR
  | Csyscall (xs : Lvals) (o : SyscallT) (es : Pexprs) : InstrR
  | Cif      (cond : Pexpr) (cthen : List Instr) (celse : List Instr) : InstrR
  | Cfor     (v : VarI) (r : Range) (body : List Instr) : InstrR
  | Cwhile   (al : Align) (cbefore : List Instr) (cond : Pexpr)
             (ii : InstrInfo) (cafter : List Instr) : InstrR
  | Ccall    (xs : Lvals) (fn : FunName) (es : Pexprs) : InstrR
  deriving Inhabited

/-- `Instr` mirrors Coq `instr := MkI : instr_info -> instr_r -> instr`
    (`expr.v:422`). -/
inductive Instr where
  | MkI (ii : InstrInfo) (i : InstrR) : Instr
  deriving Inhabited
end

-- mirror of expr.v:426: Notation cmd := (seq instr)
abbrev Cmd := List Instr

/-! ## §2. Tier 2: Values and the state -/

/-! ### §2.a. WArrays (functional model) -/

-- mirror of warray_.v: WArray.array
/-- `JArrayMirror n` mirrors Coq `WArray.array n` as a function from byte
    index to byte value.  This is the same model `JasminAST.JArray` uses.
    The algebra agrees for non-aliasing programs (which is all of jasmin —
    arrays have static sizes). -/
def JArrayMirror (n : Nat) : Type := Fin n → BitVec 8

namespace JArrayMirror
-- mirror of warray_.v: WArray.empty
/-- An all-zero array. -/
def empty (n : Nat) : JArrayMirror n := fun _ => 0

/-- Read one byte at index `i`. The word-width read `WArray.get` is `getWord`. -/
def getByte {n : Nat} (a : JArrayMirror n) (i : Fin n) : BitVec 8 := a i

/-- Write one byte at index `i`. The word-width write `WArray.set` is `setWord`. -/
def setByte {n : Nat} (a : JArrayMirror n) (i : Fin n) (v : BitVec 8) : JArrayMirror n :=
  fun j => if j = i then v else a j

-- mirror of warray_.v: WArray.cast
/-- Re-tag the size: succeeds only when sizes match. -/
def cast {n : Nat} (m : Nat) (a : JArrayMirror n) : JResult (JArrayMirror m) :=
  if h : n = m then .ok (h ▸ a) else .typeError

-- mirror of warray_.v: mk_scale
/-- The index scale of an array access (`warray_.v: mk_scale`): the word size in
    bytes for a scaled access, `1` for a direct one. -/
def scale (aa : ArrAccess) (ws : WSize) : Int :=
  match aa with
  | .AAscale => (ws.bytes : Int)
  | .AAdirect => 1

/-- The byte at index `j`, or `0` outside the array. -/
def getD {n : Nat} (a : JArrayMirror n) (j : Nat) : BitVec 8 :=
  if h : j < n then a ⟨j, h⟩ else 0

/-- The little-endian value of the `k` bytes of `a` starting at index `p`. -/
def readLE {n : Nat} (a : JArrayMirror n) (p : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (a.getD p).toNat + 256 * readLE a (p + 1) k

/-- `a` with the `k` bytes starting at index `p` replaced by the little-endian
    bytes of `v`. -/
def writeLE {n : Nat} (a : JArrayMirror n) (p k v : Nat) : JArrayMirror n :=
  fun j => if p ≤ j.val ∧ j.val < p + k then BitVec.ofNat 8 (v / 256 ^ (j.val - p)) else a j

/-- The bounds and alignment condition of an access of width `ws` at the byte
    offset `p` (`warray_.v: in_range`, and `is_align` for an aligned access). -/
def AccessOk (n : Nat) (al : Aligned) (ws : WSize) (p : Int) : Prop :=
  0 ≤ p ∧ p.toNat + ws.bytes ≤ n ∧ (al = .IsAligned → p.toNat % ws.bytes = 0)

instance (n : Nat) (al : Aligned) (ws : WSize) (p : Int) : Decidable (AccessOk n al ws p) := by
  unfold AccessOk; infer_instance

-- mirror of warray_.v: WArray.get (read al (i * mk_scale aa ws) ws)
/-- Read a word of width `ws` at index `i`: the `ws.bytes` bytes at byte offset
    `i * scale aa ws`, little-endian, when that access is in bounds (and aligned,
    for an aligned access). -/
def getWord {n : Nat} (a : JArrayMirror n) (al : Aligned) (aa : ArrAccess) (ws : WSize)
    (i : Int) : JResult (BitVec ws.bits) :=
  let p := i * scale aa ws
  if AccessOk n al ws p then .ok (BitVec.ofNat ws.bits (readLE a p.toNat ws.bytes))
  else .typeError

-- mirror of warray_.v: WArray.set (write al (i * mk_scale aa ws) ws v)
/-- Write a word `v` of width `ws` at index `i`: the `ws.bytes` bytes at byte
    offset `i * scale aa ws` become the little-endian bytes of `v`, under the
    condition of `getWord`. -/
def setWord {n : Nat} (a : JArrayMirror n) (al : Aligned) (aa : ArrAccess) (ws : WSize)
    (i : Int) (v : BitVec ws.bits) : JResult (JArrayMirror n) :=
  let p := i * scale aa ws
  if AccessOk n al ws p then .ok (writeLE a p.toNat ws.bytes v.toNat)
  else .typeError

/-- At width `U8`, `getWord` is the one-byte read at index `i`. -/
theorem getWord_U8 {n : Nat} (a : JArrayMirror n) (al : Aligned) (aa : ArrAccess) (i : Int) :
    getWord a al aa .U8 i
      = if h : 0 ≤ i ∧ i.toNat < n then .ok (a ⟨i.toNat, h.2⟩) else .typeError := by
  have hs : i * scale aa .U8 = i := by cases aa <;> simp [scale, WSize.bytes]
  have hok : AccessOk n al .U8 i ↔ 0 ≤ i ∧ i.toNat < n := by
    simp [AccessOk, WSize.bytes, Nat.mod_one]; omega
  unfold getWord
  simp only [hs]
  by_cases h : 0 ≤ i ∧ i.toNat < n
  · rw [if_pos (hok.mpr h), dif_pos h]
    congr 1
    apply BitVec.eq_of_toNat_eq
    show (readLE a i.toNat 1) % 2 ^ 8 = _
    simp only [readLE, getD, dif_pos h.2, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt (a ⟨i.toNat, h.2⟩).isLt
  · rw [if_neg (fun h' => h (hok.mp h')), dif_neg h]

/-- At width `U8`, `setWord` is the one-byte write at index `i`. -/
theorem setWord_U8 {n : Nat} (a : JArrayMirror n) (al : Aligned) (aa : ArrAccess) (i : Int)
    (v : BitVec 8) :
    setWord a al aa .U8 i v
      = if h : 0 ≤ i ∧ i.toNat < n then .ok (setByte a ⟨i.toNat, h.2⟩ v) else .typeError := by
  have hs : i * scale aa .U8 = i := by cases aa <;> simp [scale, WSize.bytes]
  have hok : AccessOk n al .U8 i ↔ 0 ≤ i ∧ i.toNat < n := by
    simp [AccessOk, WSize.bytes, Nat.mod_one]; omega
  unfold setWord
  simp only [hs]
  by_cases h : 0 ≤ i ∧ i.toNat < n
  · rw [if_pos (hok.mpr h), dif_pos h]
    congr 1
    funext j
    show (if i.toNat ≤ j.val ∧ j.val < i.toNat + WSize.U8.bytes then
        BitVec.ofNat 8 (v.toNat / 256 ^ (j.val - i.toNat)) else a j)
      = (if j = ⟨i.toNat, h.2⟩ then v else a j)
    by_cases hj : j.val = i.toNat
    · have hj' : j = ⟨i.toNat, h.2⟩ := Fin.ext hj
      rw [if_pos (by simp only [WSize.bytes]; omega), if_pos hj', hj]
      apply BitVec.eq_of_toNat_eq
      simp
    · rw [if_neg (by simp only [WSize.bytes]; omega),
        if_neg (fun e => hj (congrArg Fin.val e))]
  · rw [if_neg (fun h' => h (hok.mp h')), dif_neg h]

end JArrayMirror

/-! ### §2.b. Values -/

-- mirror of values.v:48-53: Variant value
/-- `Value` mirrors Coq `value` (`values.v:48`).  The Coq `Vundef` carries a
    proof `is_undef_t t`; we drop the proof and keep a `Ctype` tag plus a
    runtime check via `isUndefT`. -/
inductive Value where
  | Vbool  (b : Bool) : Value                                            -- values.v:49
  | Vint   (z : Int) : Value                                             -- values.v:50
  | Varr   (n : Nat) (a : JArrayMirror n) : Value                        -- values.v:51
  | Vword  (sz : WSize) (w : BitVec sz.bits) : Value                     -- values.v:52
  | Vundef (t : Ctype) : Value                                           -- values.v:53
  deriving Inhabited

/-- A `Repr` instance for `Value` that shows arrays opaquely (we cannot
    derive `Repr` because `JArrayMirror n = Fin n → BitVec 8` is a function
    type). -/
instance : Repr Value where
  reprPrec v _ := match v with
    | .Vbool b => s!"Vbool {b}"
    | .Vint z => s!"Vint {z}"
    | .Varr n _ => s!"Varr {n} <array>"
    | .Vword sz w => s!"Vword U{sz.bits} 0x{w.toNat.toDigits 16}"
    | .Vundef t => s!"Vundef {repr t}"

/-- Decidable equality on `Value` modulo array contents (which can't be
    compared without extensionality on functions).  Two `Varr` values are
    deemed equal only if their lengths match; that's enough for the
    demonstrator examples below — none of them produce `Varr` values. -/
noncomputable instance : DecidableEq Value := fun _ _ => Classical.dec _

-- mirror of values.v:14: Definition is_undef_t
/-- `isUndefT t` mirrors `values.v:14` — true when `t` is one of the
    canonical undef-able ctypes. -/
def Ctype.isUndefT : Ctype → Bool
  | .cbool => true
  | .cint => true
  | .cword .U8 => true
  | _ => false

-- mirror of values.v:91: Definition values := seq value
abbrev Values := List Value

-- mirror of values.v:93: Definition is_defined
def Value.isDefined : Value → Bool
  | .Vundef _ => false
  | _ => true

-- mirror of values.v:125-132: Definition type_of_val
def Value.typeOf : Value → Ctype
  | .Vbool _   => .cbool
  | .Vint _    => .cint
  | .Varr n _  => .carr n
  | .Vword s _ => .cword s
  | .Vundef t  => t

/-! #### Conversions: `to_*` family (`values.v:249-294`) -/

-- mirror of values.v:249-254: Definition to_bool
def Value.toBool : Value → JResult Bool
  | .Vbool b           => .ok b
  | .Vundef .cbool     => .undefError
  | _                  => .typeError

-- mirror of values.v:262-267: Definition to_int
def Value.toInt : Value → JResult Int
  | .Vint i           => .ok i
  | .Vundef .cint     => .undefError
  | _                 => .typeError

-- mirror of values.v:275-279: Definition to_arr
def Value.toArr (n : Nat) : Value → JResult (JArrayMirror n)
  | .Varr m a => JArrayMirror.cast (n := m) n a
  | _         => .typeError

-- mirror of word.v: truncate_word — width-narrowing via low bits
/-- Truncate a word to size `sz` (fails if source width is smaller). -/
def truncateWord (sz : WSize) {sz' : WSize} (w : BitVec sz'.bits) : JResult (BitVec sz.bits) :=
  if sz.bits ≤ sz'.bits then
    .ok (BitVec.ofNat sz.bits w.toNat)
  else
    .typeError

-- mirror of values.v:290-295: Definition to_word
def Value.toWord (sz : WSize) : Value → JResult (BitVec sz.bits)
  | .Vword sz' w        => truncateWord sz (sz' := sz') w
  | .Vundef (.cword _)  => .undefError
  | _                   => .typeError

-- mirror of values.v:297: Notation to_pointer := (to_word Uptr)
abbrev Value.toPointer (v : Value) : JResult (BitVec WSize.Uptr.bits) :=
  v.toWord .Uptr

-- mirror of values.v:85-89: Definition undef_addr
def undefAddr : Ctype → Value
  | .carr n => .Varr n (JArrayMirror.empty n)
  | t       => .Vundef (if t.isUndefT then t else .cword .U8)

-- mirror of varmap.v: Definition truncatable wdb ty v
/-- `truncatable wdb ty v` mirrors `varmap.v:49` (simplified: ignore `wdb`).
    Holds when `v`'s ctype is compatible with the target. -/
def truncatable (ty : Ctype) (v : Value) : Bool :=
  decide (v.typeOf = ty) || !v.isDefined

-- mirror of values.v:154: Definition DB wdb v
/-- `DB wdb v` mirrors `values.v:154` — defined-or-bool check; with `wdb`
    fixed to `true` (our default), reduces to `is_defined v ∨ typeOf = cbool`. -/
def DB (v : Value) : Bool :=
  v.isDefined || decide (v.typeOf = .cbool)

/-! ### §2.c. Memory and global declarations (abstract interfaces)

We do not port `low_memory.mem` byte-by-byte (it depends on `word_ssrZ` and
the Mathcomp word library).  Instead we expose an abstract `MemModel`
typeclass whose operations match the Coq interface line-for-line. -/

-- mirror of low_memory.v: Class WithSubWord  (we don't need it semantically)

/-- Abstract memory model.  Coq side: `low_memory.mem` is an opaque
    record; `read` and `write` are the byte-array operations.  Aligned
    accesses are tagged but we accept any access here (alignment is a
    safety property, not a semantic invariant).  `write` takes `sz` as an
    explicit argument (Lean instance synthesis is happier this way). -/
class MemModel (Mem : Type) where
  read  : Mem → Aligned → BitVec WSize.Uptr.bits → (sz : WSize) → JResult (BitVec sz.bits)
  write : Mem → Aligned → BitVec WSize.Uptr.bits → (sz : WSize) → BitVec sz.bits → JResult Mem

-- mirror of expr.v: Definition glob_decls := seq (var * glob_value)
/-- Global declarations are a list of `(var, value)` pairs.  Coq's
    `gv2val` mirrors the same shape. -/
abbrev GlobDecls := List (Var × Value)

-- mirror of psem_defs.v:40: Definition get_global_value
def getGlobalValue (gd : GlobDecls) (g : Var) : Option Value :=
  (gd.find? (fun p => decide (p.fst = g))).map (·.snd)

-- mirror of psem_defs.v:49: Definition get_global
def getGlobal (gd : GlobDecls) (g : Var) : JResult Value :=
  match getGlobalValue gd g with
  | some v => .ok v   -- (skip the `type_of_val v == eval_atype` check; trusts the gd table)
  | none   => .typeError

/-! ### §2.c.bis. Function declarations and programs (`progT`)

Coq side (`expr.v:512-547`): a `_fundef` records `f_tyin`, `f_params`,
`f_body`, `f_tyout`, `f_res` (plus dependent-record bookkeeping `f_info`
/ `f_contract` / `f_extra`).  A `_prog` is `{ p_funcs; p_globs; p_extra }`.
We omit the extra-typeclass machinery (`progT`-class, `extra_*_t`) and the
contracts: they are not needed for our `Ccall` semantics.  The
result is the `uprog` shape (`extra_fun_t := unit`, `extra_prog_t := unit`).
Placed here (after `GlobDecls`) because `Prog.pGlobs` re-uses the global
declaration list. -/

-- mirror of expr.v:512-521: Record _fundef (omit f_info / f_contract / f_extra)
/-- `FunDef` mirrors Coq `_fundef _ unit` (`expr.v:512`).  We drop the
    Coq fields `f_info` (positive source-location tag), `f_contract`
    (pre/post assertions), and `f_extra` (typeclass-controlled extra
    bookkeeping); none participate in the operational semantics of
    `Ccall`. -/
structure FunDef where
  /-- Parameter types (Coq `f_tyin`). -/
  tyin   : List Atype
  /-- Parameter names (Coq `f_params`). -/
  params : List VarI
  /-- Function body (Coq `f_body`). -/
  body   : Cmd
  /-- Return types (Coq `f_tyout`). -/
  tyout  : List Atype
  /-- Return-value names (Coq `f_res`). -/
  rets   : List VarI
  deriving Inhabited

-- mirror of expr.v:523, 543: Definition fun_decl := (funname * fundef)%type
/-- `FunDecl` mirrors Coq `fun_decl` (`expr.v:543`).  An assoc-list
    binding from a function name to its body. -/
abbrev FunDecl := FunName × FunDef

-- mirror of expr.v:525-528, 545-547: Record _prog (omit p_extra)
/-- `Prog` mirrors Coq `prog` (`expr.v:545`, with `extra_prog_t := unit`).
    The function table `pFuncs` plus the global declarations `pGlobs`.
    `p_extra` is omitted (it carries stack-alloc bookkeeping that the
    pre-allocation surface does not see). -/
structure Prog where
  pFuncs : List FunDecl
  pGlobs : GlobDecls
  deriving Inhabited

/-- The empty program — no functions, no globals.  Useful as a default
    parameter for non-call code. -/
def Prog.empty : Prog := { pFuncs := [], pGlobs := [] }

-- mirror of expr.v: Definition get_fundef (p_funcs : seq fun_decl) (fn : funname)
/-- `getFunDef p fn` looks up the body of function `fn` in program `p`.
    Mirrors Coq `get_fundef` (used at `psem.v:123` in `EcallRun`). -/
def getFunDef (p : Prog) (fn : FunName) : Option FunDef :=
  (p.pFuncs.find? (fun d => decide (d.fst = fn))).map (·.snd)

/-! ### §2.d. Variable map (`Vm.t`) -/

-- mirror of varmap.v: Vm.t — total function var → value satisfying compat_ctype
/-- `Vm` mirrors Coq `Vm.t` (`varmap.v`).  In Coq this is a dependent
    record carrying a totality proof; we model it as a plain function and
    let semantic rules track the defined/undefined distinction via `Vundef`. -/
def Vm : Type := Var → Value

namespace Vm

-- mirror of varmap.v: Definition Vm.init
def init : Vm := fun x => undefAddr (Value.typeOf (undefAddr (match x.vtype with
  | .abool => .cbool
  | .aint => .cint
  | .aarr _ n => .carr n
  | .aword s => .cword s)))

-- mirror of varmap.v: Notation `vm.[x]` := Vm.get vm x
def get (vm : Vm) (x : Var) : Value := vm x

-- mirror of varmap.v: Notation `vm.[x <- v]` := Vm.set vm x v
def set (vm : Vm) (x : Var) (v : Value) : Vm :=
  fun y => if decide (y = x) then v else vm y

end Vm

-- mirror of varmap.v:537-540: Definition get_var
/-- `getVar wdb vm x` mirrors `varmap.v:537`. -/
def getVar (wdb : Bool) (vm : Vm) (x : Var) : JResult Value :=
  let v := vm.get x
  if !wdb || v.isDefined then .ok v else .addrUndef

-- mirror of varmap.v:531-534: Definition set_var
/-- `setVar wdb vm x v` mirrors `varmap.v:531`.  The Coq definition gates
    both checks by `wdb`; when `wdb=false` both are skipped. -/
def setVar (wdb : Bool) (vm : Vm) (x : Var) (v : Value) : JResult Vm :=
  let ty : Ctype := match x.vtype with
    | .abool => .cbool | .aint => .cint
    | .aarr _ n => .carr n | .aword s => .cword s
  if wdb && !DB v then .addrUndef
  else if wdb && !truncatable ty v then .typeError
  else .ok (vm.set x v)

/-! ### §2.e. The execution state `estate` -/

-- mirror of psem_defs.v:62-69: Record estate := Estate { escs; emem; evm }
/-- `Estate` mirrors Coq `estate` (`psem_defs.v:62`).  The `escs` field
    (syscall state) is left abstract via the `SyscallState` parameter. -/
structure Estate (SyscallState : Type) (Mem : Type) where
  escs : SyscallState
  emem : Mem
  evm  : Vm

namespace Estate
variable {SyscallState Mem : Type}

-- mirror of psem_defs.v:101-108: with_vm / with_mem / with_scs
def withVm  (s : Estate SyscallState Mem) (vm : Vm) : Estate SyscallState Mem :=
  { s with evm := vm }
def withMem (s : Estate SyscallState Mem) (m : Mem) : Estate SyscallState Mem :=
  { s with emem := m }
def withScs (s : Estate SyscallState Mem) (scs : SyscallState) : Estate SyscallState Mem :=
  { s with escs := scs }

end Estate

/-! ## §3. Semantics of expressions -/

section SemPexpr
variable {SyscallState Mem : Type} [MemModel Mem]
variable (wdb : Bool) (gd : GlobDecls)

-- mirror of psem_defs.v:76-78: Definition get_gvar
/-- `getGvar wdb gd vm x` mirrors `psem_defs.v:76`. -/
def getGvar (vm : Vm) (x : GVar) : JResult Value :=
  if x.isLvar then getVar wdb vm x.gv.v_var
  else getGlobal gd x.gv.v_var

/-! ### §3.a. Operator semantics — abstracted

We don't port `sem_sop1_typed` etc. (they rely on the Mathcomp typed-tuple
machinery).  Instead `SemPexpr` takes a user-supplied `OpSem` carrying
concrete unary/binary/n-ary semantics. -/

/-- `OpSem` packages the user-supplied semantics for the surface unary,
    binary, and n-ary operators.  The Coq files factor this through the
    `sem_sop1_typed` family; we accept any well-typed instance.  Plugging
    this in is part of Phase C. -/
structure OpSem where
  sem_sop1 : SOp1 → Value → JResult Value
  sem_sop2 : SOp2 → Value → Value → JResult Value
  sem_opN  : OpN  → Values → JResult Value

variable (opS : OpSem)

-- mirror of values.v: Definition truncate_val (atype → value → exec value)
/-- `truncateVal t v` mirrors Coq `truncate_val` (`values.v`) — coerces
    `v` to a value of ctype `t`.  Pointwise: bool → bool, int → int,
    array → array (cast size), word → word (truncate). -/
def truncateVal (t : Ctype) (v : Value) : JResult Value :=
  match t, v with
  | .cbool, .Vbool _ => .ok v
  | .cint,  .Vint  _ => .ok v
  | .carr n, .Varr m a =>
      do let a' ← JArrayMirror.cast (n := m) n a; .ok (.Varr n a')
  | .cword sz, .Vword sz' w =>
      do let w' ← truncateWord sz (sz' := sz') w; .ok (.Vword sz w')
  | _, .Vundef _ => .ok v   -- propagate undef
  | _, _         => .typeError

-- mirror of psem_defs.v: Definition eval_atype  (atype → ctype)
def evalAtype : Atype → Ctype
  | .abool => .cbool
  | .aint  => .cint
  | .aarr _ n => .carr n
  | .aword s => .cword s

mutual
-- mirror of psem_defs.v:121-159: Fixpoint sem_pexpr
/-- `semPexpr wdb gd opS s e` mirrors Coq `sem_pexpr`
    (`psem_defs.v:121`).  The `truncate_val` in `Pif` uses our
    `truncateVal`, matching Coq line 156.  The `PappN` case dispatches to
    `semPexprList` (Lean structural recursion on `Pexpr`). -/
def semPexpr (s : Estate SyscallState Mem) : Pexpr → JResult Value
  | .Pconst z => .ok (.Vint z)                                            -- psem_defs.v:123
  | .Pbool b  => .ok (.Vbool b)                                           -- psem_defs.v:124
  | .Parr_init _ws n =>                                                   -- psem_defs.v:125
      .ok (.Varr n (JArrayMirror.empty n))
  | .Pvar v => getGvar wdb gd s.evm v                                     -- psem_defs.v:128
  | .Pget al aa ws x e =>                                                  -- psem_defs.v:129
      do
        let vr ← getGvar wdb gd s.evm x
        match vr with
        | .Varr n a =>
            let vi ← semPexpr s e
            let i ← vi.toInt
            match ws with
            | .U8 =>
                -- `JArrayMirror.getWord_U8`: the one-byte read
                if h : 0 ≤ i ∧ i.toNat < n then
                  .ok (.Vword .U8 (a ⟨i.toNat, h.2⟩))
                else .typeError
            | ws =>
                let w ← JArrayMirror.getWord a al aa ws i
                .ok (.Vword ws w)
        | _ => .typeError
  | .Psub _aa _ws _len x e =>                                             -- psem_defs.v:134
      do
        let vr ← getGvar wdb gd s.evm x
        match vr with
        | .Varr _ _ =>
            let vi ← semPexpr s e
            let _ ← vi.toInt
            -- get_sub: subarray extraction; abstracted to the same array for the mirror
            -- (Phase C provides the exact byte-window semantics)
            .ok vr
        | _ => .typeError
  | .Pload al sz e =>                                                     -- psem_defs.v:139
      do
        let v2 ← semPexpr s e
        let p  ← v2.toPointer
        let w  ← MemModel.read s.emem al p sz
        .ok (.Vword sz w)
  | .Papp1 o e1 =>                                                        -- psem_defs.v:143
      do
        let v1 ← semPexpr s e1
        opS.sem_sop1 o v1
  | .Papp2 o e1 e2 =>                                                     -- psem_defs.v:146
      do
        let v1 ← semPexpr s e1
        let v2 ← semPexpr s e2
        opS.sem_sop2 o v1 v2
  | .PappN op es =>                                                       -- psem_defs.v:150
      do
        let vs ← semPexprList s es
        opS.sem_opN op vs
  | .Pif ty e e1 e2 =>                                                    -- psem_defs.v:153
      do
        let vc ← semPexpr s e
        let b  ← vc.toBool
        let v1 ← semPexpr s e1
        let v2 ← semPexpr s e2
        let v1' ← truncateVal (evalAtype ty) v1
        let v2' ← truncateVal (evalAtype ty) v2
        .ok (if b then v1' else v2')

/-- Helper used by `semPexpr`'s `PappN` arm.  Structural recursion on the
    list keeps `semPexpr` well-founded under nested `Pexpr` arguments. -/
def semPexprList (s : Estate SyscallState Mem) :
    List Pexpr → JResult (List Value)
  | [] => .ok []
  | e :: es => do
      let v  ← semPexpr s e
      let vs ← semPexprList s es
      .ok (v :: vs)
end

-- mirror of psem_defs.v:161: Definition sem_pexprs s := mapM (sem_pexpr s)
def semPexprs (s : Estate SyscallState Mem) (es : Pexprs) : JResult Values :=
  semPexprList (Mem := Mem) wdb gd opS s es

end SemPexpr

/-! ## §4. Writes -/

section Write
variable {SyscallState Mem : Type} [MemModel Mem]
variable (wdb : Bool) (gd : GlobDecls) (opS : OpSem)

-- mirror of psem_defs.v:163-165: Definition write_var
/-- `writeVar wdb x v s` mirrors Coq `write_var` (`psem_defs.v:163`). -/
def writeVar (x : VarI) (v : Value) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) := do
  let vm ← setVar wdb s.evm x.v_var v
  .ok (s.withVm vm)

-- mirror of psem_defs.v:167-168: Definition write_vars
def writeVars (xs : List VarI) (vs : Values) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) :=
  JResult.fold2 (.otherErr "write_vars length mismatch")
    (fun x v st => writeVar wdb x v st) xs vs s

-- mirror of psem_defs.v: Definition get_var_is wdb vm xs
/-- `getVarIs wdb vm xs` reads each variable in `xs` from `vm`, returning
    the list of values.  Mirrors Coq `get_var_is` (used by the `EcallRun`
    rule at `psem.v:128` to extract return values from the callee state). -/
def getVarIs (vm : Vm) (xs : List VarI) : JResult Values :=
  JResult.mapM (fun x => getVar wdb vm x.v_var) xs

-- mirror of psem_defs.v:170-173: Definition write_none
def writeNone (s : Estate SyscallState Mem) (ty : Ctype) (v : Value) :
    JResult (Estate SyscallState Mem) :=
  if !truncatable ty v then .typeError
  else if !DB v then .addrUndef
  else .ok s

-- mirror of psem_defs.v:175-196: Definition write_lval
/-- `writeLval wdb gd opS l v s` mirrors Coq `write_lval`
    (`psem_defs.v:175`).  The `Laset` case writes `ws.bytes` bytes
    little-endian at the scaled offset (`JArrayMirror.setWord`, stated as the
    one-byte `setByte` at `U8` by `JArrayMirror.setWord_U8`); the byte-window
    semantics of `Lasub` is deferred (same NON-MIRRORED caveat as `Psub`
    above). -/
def writeLval (l : Lval) (v : Value) (s : Estate SyscallState Mem) :
    JResult (Estate SyscallState Mem) := do
  match l with
  | .Lnone _ ty =>                                                        -- psem_defs.v:177
      writeNone s (evalAtype ty) v
  | .Lvar x =>                                                            -- psem_defs.v:178
      writeVar wdb x v s
  | .Lmem al sz _i e =>                                                   -- psem_defs.v:179
      let pVal ← semPexpr (Mem := Mem) wdb gd opS s e
      let p ← pVal.toPointer
      let w ← v.toWord sz
      let m ← MemModel.write s.emem al p sz w
      .ok (s.withMem m)
  | .Laset al aa ws x idx =>                                               -- psem_defs.v:184
      let valR ← getVar wdb s.evm x.v_var
      match valR with
      | .Varr n a =>
          let iV ← semPexpr (Mem := Mem) wdb gd opS s idx
          let i  ← iV.toInt
          match ws with
          | .U8 =>
              -- `JArrayMirror.setWord_U8`: the one-byte write
              let wv ← v.toWord .U8
              if h : 0 ≤ i ∧ i.toNat < n then
                let a' := JArrayMirror.setByte a ⟨i.toNat, h.2⟩ wv
                writeVar wdb x (.Varr n a') s
              else .typeError
          | ws =>
              let wv ← v.toWord ws
              let a' ← JArrayMirror.setWord a al aa ws i wv
              writeVar wdb x (.Varr n a') s
      | _ => .typeError
  | .Lasub _aa _ws _len x idx =>                                          -- psem_defs.v:190
      let valR ← getVar wdb s.evm x.v_var
      match valR with
      | .Varr _ _ =>
          let iV ← semPexpr (Mem := Mem) wdb gd opS s idx
          let _ ← iV.toInt
          -- set_sub byte-window write; abstracted to identity for the mirror.
          .ok s
      | _ => .typeError

-- mirror of psem_defs.v:198-199: Definition write_lvals
def writeLvals (s : Estate SyscallState Mem) (xs : Lvals) (vs : Values) :
    JResult (Estate SyscallState Mem) :=
  JResult.fold2 (.otherErr "write_lvals length mismatch")
    (fun x v st => writeLval (Mem := Mem) wdb gd opS x v st) xs vs s

end Write

/-! ## §5. Asm-op semantics (`sem_sopn`) -/

section ExecAsm
variable {SyscallState Mem : Type} [MemModel Mem]

/-- `AsmSem` packages the user-supplied semantics for the surface `Sopn`
    family.  The Coq side uses the dependent `asmOp`/`sopn_sem` machinery;
    we accept any function from `(op, values)` to a list-of-output-values.
    Plugging in real asm semantics is Phase C. -/
structure AsmSem where
  sopn_sem : Sopn → Values → JResult Values

-- mirror of psem_defs.v:247-250: Definition exec_sopn
/-- `execSopn aS o vs` mirrors `psem_defs.v:247`. -/
def execSopn (aS : AsmSem) (o : Sopn) (vs : Values) : JResult Values :=
  aS.sopn_sem o vs

-- mirror of psem_defs.v:252-253: Definition sem_sopn
/-- `semSopn aS opS gd o m lvs args` mirrors Coq `sem_sopn`
    (`psem_defs.v:252`). -/
def semSopn (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
    (o : Sopn) (m : Estate SyscallState Mem) (lvs : Lvals) (args : Pexprs) :
    JResult (Estate SyscallState Mem) := do
  let vs ← semPexprs (Mem := Mem) true gd opS m args
  let rs ← execSopn aS o vs
  writeLvals (Mem := Mem) true gd opS m lvs rs

end ExecAsm

/-! ## §6. Tier 3: Top-level semantics (`sem_i` / `sem_I` / `sem`)

Coq side (`psem.v:48-132`) defines these three judgements as a single
`Inductive ... with ... with ...` block.  In Lean we mirror that block as
a single `inductive` with the relevant constructors of each judgement.

NON-MIRRORED choice: we omit the `Csyscall` case.  The Coq side requires
`exec_syscall` machinery that depends on a concrete `syscall` interface
typeclass.  `Ccall` is supported via the `Prog` parameter (see §1.d):
the `Ecall` constructor on `SemIr` chains into a `SemCall` judgement that
mirrors Coq `sem_call` (`psem.v:121-132`).  We drop the `init_state` /
`finalize` callbacks (those are stack-allocation bookkeeping that lives
in `extra_*_t`, omitted from our `Prog` per §1.d) — the callee runs on
the caller's `escs` / `emem` with a fresh `Vm.init`. -/

section Sem
variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls) (prog : Prog)

mutual
-- mirror of psem.v:48-50,52-53: Inductive sem (cmd judgement)
/-- `Sem s c s'` mirrors Coq `sem s c s'` (`psem.v:48`). -/
inductive Sem :
    Estate SyscallState Mem → Cmd → Estate SyscallState Mem → Prop where
  | Eskip (s : Estate SyscallState Mem) :                                 -- psem.v:49
      Sem s [] s
  | Eseq (s1 s2 s3 : Estate SyscallState Mem) (i : Instr) (c : Cmd) :     -- psem.v:52
      SemI s1 i s2 → Sem s2 c s3 → Sem s1 (i :: c) s3

-- mirror of psem.v:55-58: with sem_I (annotated-instr judgement)
/-- `SemI s i s'` mirrors Coq `sem_I s i s'` (`psem.v:55`). -/
inductive SemI :
    Estate SyscallState Mem → Instr → Estate SyscallState Mem → Prop where
  | EmkI (ii : InstrInfo) (i : InstrR)                                    -- psem.v:56
         (s1 s2 : Estate SyscallState Mem) :
      SemIr s1 i s2 → SemI s1 (.MkI ii i) s2

-- mirror of psem.v:60-109: with sem_i (raw-instr judgement)
/-- `SemIr s i s'` mirrors Coq `sem_i s i s'` (`psem.v:60`). -/
inductive SemIr :
    Estate SyscallState Mem → InstrR → Estate SyscallState Mem → Prop where
  | Eassgn (s1 s2 : Estate SyscallState Mem) (x : Lval) (tag : AssgnTag)  -- psem.v:61
           (ty : Atype) (e : Pexpr) (v v' : Value) :
      semPexpr (Mem := Mem) true gd opS s1 e = .ok v →
      truncateVal (evalAtype ty) v = .ok v' →
      writeLval (Mem := Mem) true gd opS x v' s1 = .ok s2 →
      SemIr s1 (.Cassgn x tag ty e) s2
  | Eopn (s1 s2 : Estate SyscallState Mem) (t : AssgnTag) (o : Sopn)      -- psem.v:67
         (xs : Lvals) (es : Pexprs) :
      semSopn (Mem := Mem) aS opS gd o s1 xs es = .ok s2 →
      SemIr s1 (.Copn xs t o es) s2
  | Eif_true (s1 s2 : Estate SyscallState Mem) (e : Pexpr)                -- psem.v:77
             (c1 c2 : Cmd) :
      semPexpr (Mem := Mem) true gd opS s1 e = .ok (.Vbool true) →
      Sem s1 c1 s2 →
      SemIr s1 (.Cif e c1 c2) s2
  | Eif_false (s1 s2 : Estate SyscallState Mem) (e : Pexpr)               -- psem.v:82
              (c1 c2 : Cmd) :
      semPexpr (Mem := Mem) true gd opS s1 e = .ok (.Vbool false) →
      Sem s1 c2 s2 →
      SemIr s1 (.Cif e c1 c2) s2
  | Ewhile_true (s1 s2 s3 s4 : Estate SyscallState Mem) (a : Align)       -- psem.v:87
                (c : Cmd) (e : Pexpr) (ii : InstrInfo) (c' : Cmd) :
      Sem s1 c s2 →
      semPexpr (Mem := Mem) true gd opS s2 e = .ok (.Vbool true) →
      Sem s2 c' s3 →
      SemIr s3 (.Cwhile a c e ii c') s4 →
      SemIr s1 (.Cwhile a c e ii c') s4
  | Ewhile_false (s1 s2 : Estate SyscallState Mem) (a : Align) (c : Cmd)  -- psem.v:94
                 (e : Pexpr) (ii : InstrInfo) (c' : Cmd) :
      Sem s1 c s2 →
      semPexpr (Mem := Mem) true gd opS s2 e = .ok (.Vbool false) →
      SemIr s1 (.Cwhile a c e ii c') s2
  | Efor (s1 s2 : Estate SyscallState Mem) (i : VarI) (d : Dir)           -- psem.v:99
         (lo hi : Pexpr) (c : Cmd) (vlo vhi : Int) :
      semPexpr (Mem := Mem) true gd opS s1 lo = .ok (.Vint vlo) →
      semPexpr (Mem := Mem) true gd opS s1 hi = .ok (.Vint vhi) →
      SemFor i (wrange d vlo vhi) s1 c s2 →
      SemIr s1 (.Cfor i ⟨d, lo, hi⟩ c) s2
  | Ecall (s1 s2 : Estate SyscallState Mem) (xs : Lvals)                  -- psem.v:105
          (fn : FunName) (args : Pexprs)
          (escs2 : SyscallState) (emem2 : Mem)
          (vargs vres : Values) :
      semPexprs (Mem := Mem) true gd opS s1 args = .ok vargs →
      SemCall s1.escs s1.emem fn vargs escs2 emem2 vres →
      writeLvals (Mem := Mem) true gd opS
        ({ s1 with emem := emem2, escs := escs2 }) xs vres = .ok s2 →
      SemIr s1 (.Ccall xs fn args) s2
  -- Csyscall : deferred (see §6 header note)

-- mirror of psem.v:111-119: with sem_for (range-list judgement)
/-- `SemFor i ws s1 c s2` mirrors Coq `sem_for i ws s1 c s2`
    (`psem.v:111`).  The range `ws` is the pre-computed list of integer
    iteration values produced by `wrange`. -/
inductive SemFor :
    VarI → List Int → Estate SyscallState Mem → Cmd →
    Estate SyscallState Mem → Prop where
  | EForDone (s : Estate SyscallState Mem) (i : VarI) (c : Cmd) :         -- psem.v:113
      SemFor i [] s c s
  | EForOne (s1 s1' s2 s3 : Estate SyscallState Mem) (i : VarI)            -- psem.v:115
            (w : Int) (ws : List Int) (c : Cmd) :
      writeVar (Mem := Mem) true i (.Vint w) s1 = .ok s1' →
      Sem s1' c s2 →
      SemFor i ws s2 c s3 →
      SemFor i (w :: ws) s1 c s3

-- mirror of psem.v:121-132: with sem_call (function-call judgement)
/-- `SemCall scs1 m1 fn vargs' scs2 m2 vres'` mirrors Coq `sem_call`
    (`psem.v:121`).  Argument truncation is via `truncateVal` on `tyin`;
    return truncation likewise on `tyout`.  `init_state` / `finalize` are
    omitted (see §6 header note); the callee starts at `Estate.scs1.m1`
    with `Vm.init`, and the caller resumes from the callee's `escs`/`emem`. -/
inductive SemCall :
    SyscallState → Mem → FunName → Values →
    SyscallState → Mem → Values → Prop where
  | EcallRun (scs1 : SyscallState) (m1 : Mem) (fn : FunName)              -- psem.v:122
             (f : FunDef) (vargs vargs' : Values)
             (s0 s1 s2 : Estate SyscallState Mem) (vres vres' : Values) :
      getFunDef prog fn = some f →
      JResult.mapM (fun p => truncateVal (evalAtype p.fst) p.snd)
        (f.tyin.zip vargs') = .ok vargs →
      -- init_state: omit extra/finalize hooks; start at (scs1, m1, Vm.init)
      s0 = ({ escs := scs1, emem := m1, evm := Vm.init }) →
      writeVars (Mem := Mem) true f.params vargs s0 = .ok s1 →
      Sem s1 f.body s2 →
      getVarIs true s2.evm f.rets = .ok vres →
      JResult.mapM (fun p => truncateVal (evalAtype p.fst) p.snd)
        (f.tyout.zip vres) = .ok vres' →
      SemCall scs1 m1 fn vargs' s2.escs s2.emem vres'
end

end Sem

/-! ## §7. Functional executor (for smoke tests)

The relational `Sem` / `SemI` / `SemIr` above is the mechanical port of
Coq's `Inductive sem`.  For `#eval` smoke tests we provide a
fuel-bounded *functional* executor that drives the same judgement.  The
functional and relational definitions agree by construction on
straight-line code (Phase C: prove this as `semCmd_sound`). -/

section Exec
variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)

/-! Backwards-compat note (2026-05-28): the `prog : Prog` parameter
introduced for `Ccall` support is **explicit-with-default**
(`:= Prog.empty`) on each executor entry point.  Existing call sites
that omit it continue to type-check against the pre-`Ccall` signature;
any `Ccall` encountered with the empty program returns
`"execCall: unknown function …"` (which is the expected behaviour for
that case). -/

mutual
/-- Fuel-bounded executor for a single raw instruction.  The `prog`
    parameter (default `Prog.empty`) provides the function table consulted
    by `Ccall`.  Existing call sites that omit `prog` get the empty program
    and any `Ccall` returns an "unknown function" error. -/
def execInstrR (fuel : Nat) (s : Estate SyscallState Mem) (i : InstrR)
    (prog : Prog := Prog.empty) :
    JResult (Estate SyscallState Mem) := do
  match fuel with
  | 0 => .otherErr "execInstrR: out of fuel"
  | fuel'+1 =>
    match i with
    | .Cassgn x _tag ty e =>
        let v ← semPexpr (Mem := Mem) true gd opS s e
        let v' ← truncateVal (evalAtype ty) v
        writeLval (Mem := Mem) true gd opS x v' s
    | .Copn xs _tag o es =>
        semSopn (Mem := Mem) aS opS gd o s xs es
    | .Cif cond cthen celse =>
        let vc ← semPexpr (Mem := Mem) true gd opS s cond
        let b ← vc.toBool
        if b then execCmd fuel' s cthen prog else execCmd fuel' s celse prog
    | .Cwhile _al cbefore cond _ii cafter =>
        let s' ← execCmd fuel' s cbefore prog
        let vc ← semPexpr (Mem := Mem) true gd opS s' cond
        let b ← vc.toBool
        if b then do
          let s'' ← execCmd fuel' s' cafter prog
          execInstrR fuel' s'' i prog
        else .ok s'
    | .Cfor v r body =>
        do
          let vloV ← semPexpr (Mem := Mem) true gd opS s r.lo
          let vlo  ← vloV.toInt
          let vhiV ← semPexpr (Mem := Mem) true gd opS s r.hi
          let vhi  ← vhiV.toInt
          execFor fuel' v (wrange r.dir vlo vhi) body s prog
    | .Csyscall _xs _o _es =>
        .otherErr "execInstrR Csyscall: deferred to Phase C"
    | .Ccall xs fn args =>
        do
          let vargs ← semPexprs (Mem := Mem) true gd opS s args
          let (escs2, emem2, vres) ←
            execCall fuel' s.escs s.emem fn vargs prog
          writeLvals (Mem := Mem) true gd opS
            ({ s with escs := escs2, emem := emem2 }) xs vres

/-- Fuel-bounded executor for a `Cfor`-style iteration over a pre-computed
    range list.  Mirrors `SemFor`: each step writes the current `Vint` value
    into the loop variable, then runs the body. -/
def execFor (fuel : Nat) (v : VarI) (ws : List Int) (body : Cmd)
    (s : Estate SyscallState Mem) (prog : Prog := Prog.empty) :
    JResult (Estate SyscallState Mem) :=
  match fuel with
  | 0 => .otherErr "execFor: out of fuel"
  | fuel'+1 =>
    match ws with
    | [] => .ok s
    | w :: ws' => do
        let s' ← writeVar (Mem := Mem) true v (.Vint w) s
        let s'' ← execCmd fuel' s' body prog
        execFor fuel' v ws' body s'' prog

/-- Fuel-bounded executor for an annotated instruction. -/
def execInstr (fuel : Nat) (s : Estate SyscallState Mem) (i : Instr)
    (prog : Prog := Prog.empty) :
    JResult (Estate SyscallState Mem) :=
  match i with
  | .MkI _ ir => execInstrR fuel s ir prog

/-- Fuel-bounded executor for a command (instruction sequence). -/
def execCmd (fuel : Nat) (s : Estate SyscallState Mem) :
    Cmd → (prog : Prog := Prog.empty) → JResult (Estate SyscallState Mem)
  | [],     _    => .ok s
  | i :: c, prog => do
      let s' ← execInstr fuel s i prog
      execCmd fuel s' c prog

/-- Fuel-bounded executor for a function call.  Mirrors `SemCall`:
    lookup `fn` in `prog`, truncate args against `tyin`, run the body on
    a fresh `Vm.init`, read returns via `getVarIs`, truncate against
    `tyout`.  Returns `(escs2, emem2, vres)`. -/
def execCall (fuel : Nat) (scs1 : SyscallState) (m1 : Mem)
    (fn : FunName) (vargs' : Values) (prog : Prog := Prog.empty) :
    JResult (SyscallState × Mem × Values) :=
  match fuel with
  | 0 => .otherErr "execCall: out of fuel"
  | fuel'+1 => do
      match getFunDef prog fn with
      | none => .otherErr s!"execCall: unknown function {fn.name}"
      | some f =>
          let vargs ← JResult.mapM
            (fun p => truncateVal (evalAtype p.fst) p.snd)
            (f.tyin.zip vargs')
          let s0 : Estate SyscallState Mem :=
            { escs := scs1, emem := m1, evm := Vm.init }
          let s1 ← writeVars (Mem := Mem) true f.params vargs s0
          let s2 ← execCmd fuel' s1 f.body prog
          let vres ← getVarIs true s2.evm f.rets
          let vres' ← JResult.mapM
            (fun p => truncateVal (evalAtype p.fst) p.snd)
            (f.tyout.zip vres)
          .ok (s2.escs, s2.emem, vres')
end

/-! ### §7.a. Fused tail-recursive executor for `Cmd` (bind-chain flattening)

The default `execCmd` (above) uses `do`-notation, which desugars into
chained `JResult.bind`.  Each `bind` builds a closure (`fun s' =>
execCmd fuel s' c prog`) — over a long instruction sequence this
produces a deeply-nested closure chain whose compiled-native form
overflows the C-side runtime stack at evaluation time (observed at
~hundreds of `Cassgn` instructions; `native_decide` SIGABRTs on the
MAYO 8×8-unrolled `mayoQuadformCmd` with ~8000 inner instructions).

`execCmdFused` does the same job as `execCmd` over a `Cmd` (a list of
`Instr`s) but with **no bind closures**: it pattern-matches the
`JResult` and tail-calls itself, which the native compiler lowers to
a flat loop.

We prove `execCmdFused = execCmd` so any proof against the new
executor immediately transfers; concrete `native_decide` checks
should use the fused version. -/

section ExecFused
variable {SyscallState Mem : Type} [MemModel Mem]
variable (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)

/-- Tail-recursive executor for a command (instruction sequence).
    Same semantics as `execCmd` (proved by `execCmdFused_eq_execCmd`)
    but emits no `bind` closures — the native compiler lowers this
    into a flat loop.  Use this in `native_decide` proofs of
    long-Cmd executions; otherwise `execCmd` is the canonical name.

    The `fuel` is shared with `execCmd` (passed through to
    `execInstr`); fuel exhaustion in the underlying single-instruction
    executor still surfaces as an error via the matched `JResult`. -/
def execCmdFused (fuel : Nat) :
    Estate SyscallState Mem → Cmd → Prog → JResult (Estate SyscallState Mem)
  | s, [],     _    => .ok s
  | s, i :: c, prog =>
    match execInstr (Mem := Mem) aS opS gd fuel s i prog with
    | .ok s'        => execCmdFused fuel s' c prog
    | .typeError    => .typeError
    | .undefError   => .undefError
    | .addrUndef    => .addrUndef
    | .otherErr m   => .otherErr m

/-- Semantic equivalence: the fused executor matches `execCmd` exactly.
    Proof: induction on the Cmd; the `bind` of the do-notation expands
    via `JResult.bind_ok` (left identity) into the same `match`-then-
    recurse shape.  `cases` on the `JResult` from `execInstr` closes
    each branch by reflexivity / IH. -/
theorem execCmdFused_eq_execCmd (fuel : Nat)
    (s : Estate SyscallState Mem) (c : Cmd) (prog : Prog) :
    execCmdFused (Mem := Mem) aS opS gd fuel s c prog
      = execCmd (Mem := Mem) aS opS gd fuel s c prog := by
  induction c generalizing s with
  | nil =>
    simp only [execCmdFused, execCmd]
  | cons i c ih =>
    -- Both sides unfold to a match on `execInstr fuel s i prog`.
    simp only [execCmdFused, execCmd]
    cases h : execInstr (Mem := Mem) aS opS gd fuel s i prog with
    | ok s'         => simp [JResult.bind, ih]
    | typeError     => rfl
    | undefError    => rfl
    | addrUndef     => rfl
    | otherErr m    => rfl

/-- Corollary: `execCmd` is symbolically the same as `execCmdFused`,
    so any `native_decide` / `decide` goal against `execCmd` can be
    rewritten to `execCmdFused`. -/
theorem execCmd_eq_execCmdFused (fuel : Nat)
    (s : Estate SyscallState Mem) (c : Cmd) (prog : Prog) :
    execCmd (Mem := Mem) aS opS gd fuel s c prog
      = execCmdFused (Mem := Mem) aS opS gd fuel s c prog :=
  (execCmdFused_eq_execCmd aS opS gd fuel s c prog).symm

end ExecFused

end Exec

end CatCrypt.Crypto.Jasmin.CoqSemMirror
