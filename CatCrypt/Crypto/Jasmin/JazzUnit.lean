/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCryptCore.Tactics.KatGuard

/-!
# Jasmin compilation units

A `FunDecl` of `JasminAST` carries the typed body of a function but not the surface
information a Jasmin source file states: the storage class of each variable (`reg`,
`stack`, `reg ptr`, `inline`), the element width of an array (`u64[4]` rather than a
byte count), the function kind (`export fn`, `inline fn`, an annotated `fn`), the
`require` lines and the signatures of external callees. This module defines that
surface information and the units built from it.

## Main definitions

* `Storage`, `PType`, `PType.toSType`: storage classes and surface types; `toSType` is the
  `SType` of a surface type, counting array lengths in bytes.
* `FnKind`, `Decl`, `ExternSig`: function kinds, local declarations and extern signatures.
* `JazzFn`, `JazzUnit`: a function with its surface information, and a list of such
  functions with the extern signatures they call.
* `exprVars`, `lvalVars`, `instrVars`, `cmdVars`, `cmdCalls`: the variables occurring in,
  and the function names called by, expressions, l-values, instructions and commands.
* `JazzUnit.WellFormed`: parameter and result types agree with the `FunDecl`, every
  variable of a body is a parameter or a declared name at its type, each name is declared
  once, results of a non-inline function have register storage, and every callee is a
  function or an extern of the unit.
* `JazzUnit.wellFormedB`: a Boolean check of `WellFormed`.

## Main results

* `JazzUnit.wellFormedB_sound`: `wellFormedB u = true` implies `u.WellFormed`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Jazz

open CatCrypt.Crypto.Jasmin

/-! ## Storage classes and surface types -/

/-- Storage class of a Jasmin variable: `reg`, `stack`, `reg ptr` (`reg mut ptr` when
`mutable`, `reg const ptr` otherwise), `stack ptr`, `inline` and `global`. -/
inductive Storage where
  | reg | stack | regPtr (mutable : Bool) | stackPtr | inlineVar | global
  deriving DecidableEq, Repr, Inhabited

/-- `true` for the register storage classes `reg` and `reg ptr`. -/
def Storage.isReg : Storage → Bool
  | .reg | .regPtr _ => true
  | _ => false

/-- Surface type: a word, `bool`, `int`, or an array `uN[len]` that carries its element
width; `toSType` counts the array length in bytes. -/
inductive PType where
  | word (ws : WSize) | bool | int | arr (ws : WSize) (len : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The `SType` of a surface type; an array of `len` elements of width `ws` has
`len * ws.bytes` bytes. -/
def PType.toSType : PType → SType
  | .word ws => .sword ws
  | .bool => .sbool
  | .int => .sint
  | .arr ws len => .sarr (len * ws.bytes)

/-! ## Functions and units -/

/-- Function kind: `export fn`, `inline fn`, or `fn` preceded by the annotations `annots`
(for instance `returnaddress=stack`, printed `#[returnaddress=stack] fn`). -/
inductive FnKind where
  | exportFn | inlineFn | localFn (annots : List String)
  deriving DecidableEq, Repr, Inhabited

/-- A local declaration `storage ty n₁ n₂ …;`. -/
structure Decl where
  storage : Storage
  ty : PType
  names : List String
  deriving DecidableEq, Repr, Inhabited

/-- The signature of an external function called by the unit. -/
structure ExternSig where
  name : String
  params : List (Storage × PType)
  results : List (Storage × PType)
  deriving DecidableEq, Repr, Inhabited

/-- A function of a unit: the top-level comment lines printed before it, its `require`
lines, its kind, its `FunDecl`, the storage and surface type of each parameter and result,
and its local declarations in print order. -/
structure JazzFn where
  preamble : List String := []
  requires : List String := []
  kind : FnKind
  fd : FunDecl
  paramTys : List (Storage × PType)
  resultTys : List (Storage × PType)
  decls : List Decl

/-- A compilation unit: extern signatures and functions. -/
structure JazzUnit where
  externs : List ExternSig := []
  fns : List JazzFn

/-! ## Variables and callees of a body -/

mutual
/-- The variables occurring in an expression. -/
def exprVars : PExpr → List Var
  | .Pconst _ | .Pbool _ | .Parr_init _ => []
  | .Pvar x => [x.gv.var]
  | .Pget _ _ x i => x.gv.var :: exprVars i
  | .Psub _ _ _ x i => x.gv.var :: exprVars i
  | .Pload _ x o => x.var :: exprVars o
  | .Papp1 _ e => exprVars e
  | .Papp2 _ a b => exprVars a ++ exprVars b
  | .PappN _ es => exprsVars es
  | .Pif _ c a b => exprVars c ++ exprVars a ++ exprVars b

/-- The variables occurring in a list of expressions. -/
def exprsVars : List PExpr → List Var
  | [] => []
  | e :: es => exprVars e ++ exprsVars es
end

/-- The variables occurring in an l-value, written or read in an index. -/
def lvalVars : LVal → List Var
  | .Lnone _ _ => []
  | .Lvar x => [x.var]
  | .Lmem _ x o => x.var :: exprVars o
  | .Laset _ _ x i => x.var :: exprVars i
  | .Lasub _ _ _ x i => x.var :: exprVars i

/-- The variables occurring in a list of l-values. -/
def lvalsVars (lvs : List LVal) : List Var := lvs.flatMap lvalVars

mutual
/-- The variables occurring in an instruction, the loop counter of a `for` included. -/
def instrVars : InstrR → List Var
  | .Cassgn lv _ _ e => lvalVars lv ++ exprVars e
  | .Copn lvs _ _ es => lvalsVars lvs ++ exprsVars es
  | .Cif c t e => exprVars c ++ cmdVars t ++ cmdVars e
  | .Cfor v _ b => v.var :: cmdVars b
  | .Cwhile b c a => cmdVars b ++ exprVars c ++ cmdVars a
  | .Ccall _ lvs _ args => lvalsVars lvs ++ exprsVars args

/-- The variables occurring in a command. -/
def cmdVars : List InstrR → List Var
  | [] => []
  | i :: is => instrVars i ++ cmdVars is
end

mutual
/-- The function names called by an instruction. -/
def instrCalls : InstrR → List String
  | .Cassgn .. | .Copn .. => []
  | .Cif _ t e => cmdCalls t ++ cmdCalls e
  | .Cfor _ _ b => cmdCalls b
  | .Cwhile b _ a => cmdCalls b ++ cmdCalls a
  | .Ccall _ _ f _ => [f.name]

/-- The function names called by a command. -/
def cmdCalls : List InstrR → List String
  | [] => []
  | i :: is => instrCalls i ++ cmdCalls is
end

/-! ## Well-formedness -/

namespace JazzFn

/-- The declared names of a function with their types: parameters first, then each name
of each local declaration. -/
def env (f : JazzFn) : List (String × SType) :=
  f.fd.params.map (fun p => (p.var.var.vname, p.var.var.vtype)) ++
    f.decls.flatMap (fun d => d.names.map (fun n => (n, d.ty.toSType)))

/-- The variables a well-formed function must declare: those of the body and the results. -/
def usedVars (f : JazzFn) : List Var :=
  cmdVars f.fd.body ++ f.fd.results.map (·.var)

/-- Well-formedness of a function against the names `callees` it may call. -/
def WellFormed (callees : List String) (f : JazzFn) : Prop :=
  f.paramTys.length = f.fd.params.length ∧
  f.resultTys.length = f.fd.results.length ∧
  (∀ q ∈ f.fd.params.zip f.paramTys, q.2.2.toSType = q.1.var.var.vtype) ∧
  (∀ q ∈ f.fd.results.zip f.resultTys, q.2.2.toSType = q.1.var.vtype) ∧
  (f.env.map Prod.fst).Nodup ∧
  (∀ v ∈ f.usedVars, (v.vname, v.vtype) ∈ f.env) ∧
  (f.kind ≠ .inlineFn → ∀ q ∈ f.resultTys, q.1.isReg = true) ∧
  (∀ n ∈ cmdCalls f.fd.body, n ∈ callees)

/-- The Boolean check of `WellFormed`. -/
def wellFormedB (callees : List String) (f : JazzFn) : Bool :=
  f.paramTys.length == f.fd.params.length &&
  f.resultTys.length == f.fd.results.length &&
  (f.fd.params.zip f.paramTys).all (fun q => q.2.2.toSType == q.1.var.var.vtype) &&
  (f.fd.results.zip f.resultTys).all (fun q => q.2.2.toSType == q.1.var.vtype) &&
  decide (f.env.map Prod.fst).Nodup &&
  f.usedVars.all (fun v => f.env.contains (v.vname, v.vtype)) &&
  (f.kind == .inlineFn || f.resultTys.all (fun q => q.1.isReg)) &&
  (cmdCalls f.fd.body).all (fun n => callees.contains n)

theorem wellFormedB_sound {callees : List String} {f : JazzFn}
    (h : f.wellFormedB callees = true) : f.WellFormed callees := by
  simp only [wellFormedB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8⟩
  intro hk
  rcases h7 with h7 | h7
  · exact absurd h7 hk
  · exact h7

end JazzFn

namespace JazzUnit

/-- The names a function of the unit may call: the functions of the unit and the externs. -/
def callees (u : JazzUnit) : List String :=
  u.fns.map (·.fd.name.name) ++ u.externs.map (·.name)

/-- Well-formedness of a unit: every function is well formed against `u.callees`.
For each function, `paramTys` and `resultTys` have the lengths of the `FunDecl`'s
parameters and results and the `toSType` of each is that variable's type; every variable
of the body and every result is a parameter or a declared name, at its type; each name is
declared once; results of a non-inline function have storage `reg` or `reg ptr`; every
called name is a function of the unit or an extern. -/
def WellFormed (u : JazzUnit) : Prop :=
  ∀ f ∈ u.fns, f.WellFormed u.callees

/-- The Boolean check of `WellFormed`. -/
def wellFormedB (u : JazzUnit) : Bool :=
  u.fns.all (JazzFn.wellFormedB u.callees)

theorem wellFormedB_sound {u : JazzUnit} (h : u.wellFormedB = true) : u.WellFormed := by
  intro f hf
  exact JazzFn.wellFormedB_sound (List.all_eq_true.mp h f hf)

end JazzUnit

/-! ## The unit of the `bignum_add_4` port

`JazzToInstrR.RoundTrip.bignumAdd4Fd` is the `FunDecl` of the `bignum_add_4` port with
the carry `cf` typed `sbool`. `bignumAdd4Unit` wraps a copy of that `FunDecl` (this module
imports `JasminAST` only) with the declarations `Emit.emitFunDecl` prints for it. -/

namespace BignumAdd4

/-- A `u64` variable. -/
def u (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `bool` variable. -/
def b (s : String) : Var := { vname := s, vtype := .sbool }

/-- The l-value of a variable. -/
def lv (x : Var) : LVal := .Lvar { var := x }

/-- The expression of a local variable. -/
def pv (x : Var) : PExpr := .Pvar { gv := { var := x }, gs := false }

/-- `x = [:u64 base + k];` -/
def load (x base : String) (k : Int) : InstrR :=
  .Cassgn (lv (u x)) .AT_none (.sword .U64) (.Pload .U64 { var := u base } (.Pconst k))

/-- `[:u64 base + k] = src;` -/
def store (base : String) (k : Int) (src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := u base } (.Pconst k)) .AT_none (.sword .U64) (pv (u src))

/-- `_, cf, _, _, _, r = #op(args);` -/
def carry (op r : String) (args : List PExpr) : InstrR :=
  .Copn [.Lnone {} (.sword .U64), lv (b "cf"), .Lnone {} (.sword .U64),
    .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), lv (u r)] .AT_none (.Oasm ⟨op⟩) args

/-- The `bignum_add_4` port with `cf : bool`. -/
def fd : FunDecl where
  name := { name := "bignum_add_4" }
  params := [⟨{ var := u "op" }⟩, ⟨{ var := u "ap" }⟩, ⟨{ var := u "bp" }⟩]
  body :=
    [ load "a0" "ap" 0, load "a1" "ap" 8, load "a2" "ap" 16, load "a3" "ap" 24
    , load "b0" "bp" 0, load "b1" "bp" 8, load "b2" "bp" 16, load "b3" "bp" 24
    , carry "ADD_64" "r0" [pv (u "a0"), pv (u "b0")]
    , carry "ADC_64" "r1" [pv (u "a1"), pv (u "b1"), pv (b "cf")]
    , carry "ADC_64" "r2" [pv (u "a2"), pv (u "b2"), pv (b "cf")]
    , carry "ADC_64" "r3" [pv (u "a3"), pv (u "b3"), pv (b "cf")]
    , store "op" 0 "r0", store "op" 8 "r1", store "op" 16 "r2", store "op" 24 "r3" ]
  results := []

/-- The unit of `bignum_add_4`: `export fn bignum_add_4(reg u64 op, reg u64 ap,
reg u64 bp)` with the locals `reg bool of cf sf pf zf;` and
`reg u64 a0 … a3 b0 … b3 r0 … r3;`. -/
def unit : JazzUnit where
  fns := [{
    kind := .exportFn
    fd := fd
    paramTys := [(.reg, .word .U64), (.reg, .word .U64), (.reg, .word .U64)]
    resultTys := []
    decls :=
      [ { storage := .reg, ty := .bool, names := ["of", "cf", "sf", "pf", "zf"] }
      , { storage := .reg, ty := .word .U64,
          names := ["a0", "a1", "a2", "a3", "b0", "b1", "b2", "b3",
                    "r0", "r1", "r2", "r3"] } ] }]

-- The unit of `bignum_add_4` is well formed.
#kat unit.wellFormedB

end BignumAdd4

end CatCrypt.Crypto.Jasmin.Jazz
