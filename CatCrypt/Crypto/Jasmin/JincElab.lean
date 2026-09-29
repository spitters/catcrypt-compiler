/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.JincToCom
public import CatCrypt.Crypto.Jasmin.JincToCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce

/-!
# `.jinc` elaborator: untyped `JFun` → `Com jasminDialect` → owned x86

Elaborates a parsed straight-line `JFun` (`JincToCom`) into an intrinsically-typed
`Com jasminDialect Γ τ`, then renders it through the owned backend
(`Com.toLprogPhysAbi` → `renderLprogAtt`) — no jasminc. Global tables assigned by
`name = GLOBAL` are turned into pointer parameters (the owned export emits no
globals). The op mapping is `(Wu)x → castW`, the binary ops
`a*b/a+b/a-b/a&b/a|b/a^b/a<<n/a>>n` and `andn a b` (`(~a) & b`) `→ regArith`,
the rotate `ror n src → rorImm`, integer
literals → `regConst`, `tbl[idx] → stackLoad`, `out[k]=v → stackStore`, and the
branchless conditional `c ? a : b → select` (constant-time control flow: renders
to `test`/`cmovcc`, no PC divergence). A bare `lhs = src` is a register copy, in
the dialect the identity shift `shlImm w 0`; `(Wu) arr[idx]` is `stackLoad` then
`castW`; `arr[idx] = rhs` at a general index and right-hand side binds the index
and the value and then `stackStore`s. `for v = lo to hi { body }` is a bounded
inline unroll: one `regConst` binding of the counter per iteration followed by
the elaborated body, the same shape as the dialect front's `loopRForD`. A
`while (c != 0)` loop is data-dependent and outside the fragment; it elaborates
to `none`.

A `Var Γ τ` is built by `mkVar` (a de-Bruijn lookup-with-type-check); each bound
name extends the context. `ecDlog_elaborates` / `ecPowStore_elaborates` check the two leaves elaborate to a
3-argument `Com` of the expected return type, and `ecDlog_denote_concrete` /
`ecPowStore_denote_concrete` check the elaborated `Com` computes the leaf
(`tbl[(x*23+y) mod 529]` for `ec_dlog`; `out[k] = tbl[2m+k]` for `ec_pow_store`).
The `Com → .s` step is the owned backend (`Com.toLprogPhysAbi` /
`renderLprogAtt`), rendered by `emitJincAsm`. Source parameter `j` lands in
SysV register `j` (natural C order: parameter 0 → `RDI`).

`elabStmtsG` is the elaborator over any target with a `ret` and a let-binding:
`elabStmts` is its `Com` instance, and `elabStmtsL` its `ComL` instance, which
keeps a `for` from `0` as one `ComL.forLoopN` node (§3b). `emitJFunRolledAsm`
renders a function elaborated that way through `rolledLfundef`, the owned
back end and the `rorx` selection `rorxLprog` (§6); a base binding `b = @SYM`
is a `.rodata` symbol load. `emitRolledProgramAsm` renders several such functions
as one program through `rolledLfundefWith` (§7), which also exports parameters
held in a shared argument register or in the function's frame, run-time loops
(`ComL.forLoopBlock`) and leaf calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JincElab

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. De-Bruijn variable construction -/

/-- The dialect type a `.jinc` type maps to. -/
def toJ : JTy → JasminTy
  | .reg w => .reg w
  | .arr w n => .stackArr w n

/-- The dialect binary op a parsed `BinKind` maps to. -/
def binOf : BinKind → JasminBinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .and => .and
  | .or => .or
  | .xor => .xor
  | .shl => .shl
  | .shr => .shr
  | .andn => .andn

/-- Build the `Ctxt.Var Γ τ` at de-Bruijn index `i`, succeeding iff `Γ[i] = τ`. -/
def mkVar : (Γ : Ctxt jasminDialect) → Nat → (τ : JasminTy) → Option (Ctxt.Var Γ τ)
  | [], _, _ => none
  | t :: _, 0, τ => if h : t = τ then some (h ▸ Ctxt.Var.here) else none
  | _ :: Γ', n + 1, τ => (mkVar Γ' n τ).map Ctxt.Var.there

/-- The name environment: parallel to `Γ` (head = most-recent binding). -/
abbrev Env := List (String × JasminTy)

/-- Find a name's de-Bruijn index and declared type. -/
def envFind : Env → String → Option (Nat × JasminTy)
  | [], _ => none
  | (n, t) :: rest, nm => if n == nm then some (0, t) else (envFind rest nm).map (fun (i, t') => (i + 1, t'))

/-- Look up a name as a `Var Γ τ` of the expected type. -/
def lookup (Γ : Ctxt jasminDialect) (env : Env) (nm : String) (τ : JasminTy) :
    Option (Ctxt.Var Γ τ) := do
  let (i, _) ← envFind env nm
  mkVar Γ i τ

/-- A name's declared type. -/
def typeOf (env : Env) (nm : String) : Option JasminTy :=
  (envFind env nm).map (·.2)

/-! ## 2. The elaborator -/

/-- The loop hook of `elabStmtsG`: given the context, the environment, the
    counter, the trip count, the body and the statements after the loop of
    `for v = 0 to n { body }`, the elaborated rest of the list. -/
abbrev LoopHook (R : Ctxt jasminDialect → JasminTy → Type) : Type :=
  (Γ : Ctxt jasminDialect) → Env → String → Nat → List Stmt → List Stmt →
    Option (Σ τ : JasminTy, R Γ τ)

/-- The variables of the names `nms` in context `Γ`, with their types. -/
def invVars (Γ : Ctxt jasminDialect) (env : Env) :
    List String → Option (Σ tys : Ctxt jasminDialect, HVector (fun ty => Ctxt.Var Γ ty) tys)
  | [] => some ⟨[], .nil⟩
  | nm :: rest => do
      let t ← typeOf env nm
      let v ← lookup Γ env nm t
      let ⟨tys, hv⟩ ← invVars Γ env rest
      return ⟨t :: tys, .cons v hv⟩

/-- The run-time loop hook of `elabStmtsG`: given the context, the environment,
    the trip index, the name of the trip count, the body and the statements
    after `for v = 0 to count { body }`, the elaborated rest of the list. -/
abbrev LoopRtHook (R : Ctxt jasminDialect → JasminTy → Type) : Type :=
  (Γ : Ctxt jasminDialect) → Env → String → String → List Stmt → List Stmt →
    Option (Σ τ : JasminTy, R Γ τ)

/-- Elaborate a statement list into `Σ τ, R Γ τ` for a target `R` with a `ret`
    and a let-binding `var` (`Com jasminDialect`, or `ComL`), threading the
    context `Γ` and the name environment `env`. Literal operands introduce a
    `regConst` binding; const-indexed stores introduce a `regConst` index;
    `b = @SYM` binds `b` to the base of the `.rodata` table `SYM` (the reserved
    `extCall` `loadSymPrefix ++ SYM`); a call `lhs = sym(args)` is the `extCall`
    `sym` at the declared type of `lhs`. A `for` from `0` goes to `loop` when it
    is given and is unrolled otherwise; a run-time loop goes to `loopRt`, and
    elaborates to `none` without it. -/
partial def elabStmtsG {R : Ctxt jasminDialect → JasminTy → Type}
    (ret : ∀ {Γ t}, Ctxt.Var Γ t → R Γ t)
    (var : ∀ {Γ t s}, Expr jasminDialect Γ t → R (t :: Γ) s → R Γ s)
    (loop : Option (LoopHook R)) (loopRt : Option (LoopRtHook R)) :
    (Γ : Ctxt jasminDialect) → Env → List Stmt → Option (Σ τ : JasminTy, R Γ τ)
  | Γ, env, [Stmt.ret nm] => do
      let (i, t) ← envFind env nm
      let v ← mkVar Γ i t
      return ⟨t, ret v⟩
  | Γ, env, Stmt.assign lhs (Rhs.call sym args) :: rest => do
      let retTy ← typeOf env lhs
      let ⟨tys, hv⟩ ← invVars Γ env args
      let e : Expr jasminDialect Γ retTy := ⟨.extCall sym tys retTy, rfl, hv⟩
      let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (retTy :: Γ) ((lhs, retTy) :: env) rest
      return ⟨s, var e body⟩
  | Γ, env, Stmt.assign lhs (Rhs.cast w src) :: rest => do
      let sTy ← typeOf env src
      match sTy with
      | .reg sw =>
          let sv ← lookup Γ env src (.reg sw)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.castW sw w, rfl, .cons sv .nil⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.ror n src) :: rest => do
      let sTy ← typeOf env src
      match sTy with
      | .reg w =>
          let sv ← lookup Γ env src (.reg w)
          let e : Expr jasminDialect Γ (.reg w) := ⟨.rorImm w n, rfl, .cons sv .nil⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.load arr idx) :: rest => do
      let aTy ← typeOf env arr
      match aTy with
      | .stackArr w n =>
          let av ← lookup Γ env arr (.stackArr w n)
          let iv ← lookup Γ env idx (.reg 64)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.stackLoad w n, rfl, .cons av (.cons iv .nil)⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.select c t f) :: rest => do
      let cv ← lookup Γ env c (.reg 1)
      let tTy ← typeOf env t
      match tTy with
      | .reg w =>
          let tv ← lookup Γ env t (.reg w)
          let fv ← lookup Γ env f (.reg w)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.select w, rfl, .cons cv (.cons tv (.cons fv .nil))⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.bin op a (Operand.var b)) :: rest => do
      let aTy ← typeOf env a
      match aTy with
      | .reg w =>
          let av ← lookup Γ env a (.reg w)
          let bv ← lookup Γ env b (.reg w)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.regArith (binOf op) w, rfl, .cons av (.cons bv .nil)⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.bin op a (Operand.lit n)) :: rest => do
      let aTy ← typeOf env a
      match aTy with
      | .reg w =>
          -- bind a fresh constant, then the binary op over it
          let cName := "%c" ++ toString Γ.length
          let ce : Expr jasminDialect Γ (.reg w) := ⟨.regConst w n, rfl, .nil⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((cName, .reg w) :: env)
            (Stmt.assign lhs (Rhs.bin op a (Operand.var cName)) :: rest)
          return ⟨s, var ce body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.imm n) :: rest => do
      let lTy ← typeOf env lhs
      match lTy with
      | .reg w =>
          let e : Expr jasminDialect Γ (.reg w) := ⟨.regConst w n, rfl, .nil⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.glob src) :: rest => do
      if let '@' :: sym := src.toList then
        let t ← typeOf env lhs
        let e : Expr jasminDialect Γ t :=
          ⟨.extCall (loadSymPrefix ++ String.ofList sym) [] t, rfl, .nil⟩
        let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (t :: Γ) ((lhs, t) :: env) rest
        return ⟨s, var e body⟩
      -- a register copy `lhs = src`, expressed as the identity shift `src <<< 0`
      let sTy ← typeOf env src
      match sTy with
      | .reg w =>
          let sv ← lookup Γ env src (.reg w)
          let e : Expr jasminDialect Γ (.reg w) := ⟨.shlImm w 0, rfl, .cons sv .nil⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.castLoad w arr idx) :: rest =>
      -- `lhs = (Wu) arr[idx]`  ≡  `%l = arr[idx]; lhs = (Wu) %l`
      let tName := "%l" ++ toString Γ.length
      elabStmtsG ret var loop loopRt Γ env (Stmt.assign tName (Rhs.load arr idx) ::
        Stmt.assign lhs (Rhs.cast w tName) :: rest)
  | Γ, env, Stmt.compound op lhs operand :: rest =>
      -- `lhs op= operand`  ≡  `lhs = lhs op operand`
      elabStmtsG ret var loop loopRt Γ env (Stmt.assign lhs (Rhs.bin op lhs operand) :: rest)
  | Γ, env, Stmt.store arr k val :: rest => do
      let aTy ← typeOf env arr
      match aTy with
      | .stackArr w n =>
          -- bind the constant index, then the store (rebinding `arr`), nested
          let ce : Expr jasminDialect Γ (.reg 64) := ⟨.regConst 64 k, rfl, .nil⟩
          let Γ' : Ctxt jasminDialect := .reg 64 :: Γ
          let iName := "%i" ++ toString Γ.length
          let env' : Env := (iName, .reg 64) :: env
          let av ← lookup Γ' env' arr (.stackArr w n)
          let iv ← lookup Γ' env' iName (.reg 64)
          let vv ← lookup Γ' env' val (.reg w)
          let se : Expr jasminDialect Γ' (.stackArr w n) :=
            ⟨.stackStore w n, rfl, .cons av (.cons iv (.cons vv .nil))⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.stackArr w n :: Γ') ((arr, .stackArr w n) :: env') rest
          return ⟨s, var ce (var se body)⟩
      | _ => none
  | Γ, env, Stmt.storeAt arr (Operand.lit k) val :: rest => do
      -- bind the literal index, then store at the bound name
      let iName := "%x" ++ toString Γ.length
      let ce : Expr jasminDialect Γ (.reg 64) := ⟨.regConst 64 k, rfl, .nil⟩
      let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.reg 64 :: Γ) ((iName, .reg 64) :: env)
        (Stmt.storeAt arr (Operand.var iName) val :: rest)
      return ⟨s, var ce body⟩
  | Γ, env, Stmt.storeAt arr (Operand.var idx) (Rhs.glob val) :: rest => do
      let aTy ← typeOf env arr
      match aTy with
      | .stackArr w n =>
          let av ← lookup Γ env arr (.stackArr w n)
          let iv ← lookup Γ env idx (.reg 64)
          let vv ← lookup Γ env val (.reg w)
          let se : Expr jasminDialect Γ (.stackArr w n) :=
            ⟨.stackStore w n, rfl, .cons av (.cons iv (.cons vv .nil))⟩
          let ⟨s, body⟩ ← elabStmtsG ret var loop loopRt (.stackArr w n :: Γ) ((arr, .stackArr w n) :: env) rest
          return ⟨s, var se body⟩
      | _ => none
  | Γ, env, Stmt.storeAt arr idx val :: rest =>
      -- a computed right-hand side: bind it, then store the bound name
      let vName := "%v" ++ toString Γ.length
      elabStmtsG ret var loop loopRt Γ env (Stmt.assign vName val ::
        Stmt.storeAt arr idx (Rhs.glob vName) :: rest)
  | Γ, env, Stmt.forRt v count body :: rest =>
      match loopRt with
      | some h => h Γ env v count body rest
      | none => none
  | Γ, env, Stmt.forTo v lo hi body :: rest =>
      match loop, lo with
      | some h, 0 => h Γ env v hi body rest
      | _, _ =>
      -- one unrolled iteration: the counter is a `regConst` binding, and the
      -- remaining range is the same `forTo` with `lo` advanced
      if lo < hi then do
        let ce : Expr jasminDialect Γ (.reg 64) := ⟨.regConst 64 lo, rfl, .nil⟩
        let ⟨s, cbody⟩ ← elabStmtsG ret var loop loopRt (.reg 64 :: Γ) ((v, .reg 64) :: env)
          (body ++ Stmt.forTo v (lo + 1) hi body :: rest)
        return ⟨s, var ce cbody⟩
      else elabStmtsG ret var loop loopRt Γ env rest
  -- `Stmt.whileNz`: a data-dependent loop, outside the fragment this elaborator
  -- covers.
  | _, _, _ => none

/-- Elaborate a statement list into `Σ τ, Com jasminDialect Γ τ` (`elabStmtsG`
    into `Com`, every `for` unrolled). -/
def elabStmts (Γ : Ctxt jasminDialect) (env : Env) (ss : List Stmt) :
    Option (Σ τ : JasminTy, Com jasminDialect Γ τ) :=
  elabStmtsG Com.ret Com.var none none Γ env ss

/-! ## 3. Whole-function elaboration -/

/-- The local name a `name = GLOBAL` statement binds (a global table assignment).
    A `.rodata` base binding `b = @SYM` is not one. -/
def globName : Stmt → Option String
  | .assign nm (.glob g) => if g.startsWith "@" then none else some nm
  | _ => none

/-- Elaborate a whole parsed function: global-table locals (`name = GLOBAL`)
    become trailing pointer parameters, the global assignments are dropped, and
    the remaining body is elaborated over the parameter context (parameter `0` is
    the head/most-recent `Ctxt.Var`). -/
def elabFun (f : JFun) :
    Option ((Γ : Ctxt jasminDialect) × (τ : JasminTy) × Com jasminDialect Γ τ) := do
  let globs := f.body.filterMap globName
  let globParams ← globs.mapM (fun nm =>
    (f.decls.find? (fun d => d.2 == nm)).map (fun d => Param.mk d.1 nm))
  -- Reverse the parameter order so the source-first parameter is the deepest
  -- `Ctxt.Var` — the owned ABI export maps the deepest var to the first SysV
  -- register, giving the natural C order (parameter 0 → RDI).
  let params' := (f.params ++ globParams).reverse
  let body' := f.body.filter (fun s => (globName s).isNone)
  let Γ₀ : Ctxt jasminDialect := params'.map (fun p => toJ p.ty)
  -- Declared locals sit past the end of `Γ₀`, so `typeOf` finds a declared type
  -- for a name that is not yet bound while `lookup` still fails on it.
  let env₀ : Env := params'.map (fun p => (p.name, toJ p.ty))
    ++ f.decls.map (fun d => (d.2, toJ d.1))
  let ⟨τ, com⟩ ← elabStmts Γ₀ env₀ body'
  return ⟨Γ₀, τ, com⟩

/-! ## 3b. Rolled loops (`ComL`)

`elabStmtsL` elaborates into `ComL`, keeping `for v = 0 to n { body }` as one
`ComL.forLoopN` node (`rolledLoop`), and a run-time loop `Stmt.forRt` as one
`ComL.forLoopBlock` node (`rolledLoopRt`). The body must store into exactly one array,
the accumulator threaded through the loop; `v` is the `reg 64` trip index; every
other name the body reads before binding it is a loop invariant, passed in from
the enclosing context. The body is elaborated by `elabStmts` over the context
`acc :: v :: invariants`, followed by `return acc`. -/

/-- The names a statement list reads before binding them, in first-read order. -/
def freeReads (ss : List Stmt) : List String :=
  (ss.foldl (fun (defs, acc) s =>
    let acc' := (stmtReads s).foldl (fun a x =>
      if defs.contains x || a.contains x then a else a ++ [x]) acc
    (stmtDefs s ++ defs, acc')) (([] : List String), ([] : List String))).2

mutual

/-- The loop hook of `elabStmtsL`: `for v = 0 to n { body }` as `ComL.forLoopN`,
    the rest of the list elaborated with the final accumulator bound to the
    accumulator's name. -/
partial def rolledLoop (Γ : Ctxt jasminDialect) (env : Env) (v : String) (n : Nat)
    (body rest : List Stmt) : Option (Σ τ : JasminTy, ComL Γ τ) := do
  let acc ← body.findSome? fun s => match s with
    | .store a _ _ | .storeAt a _ _ => some a
    | _ => none
  let accTy ← typeOf env acc
  let accV ← lookup Γ env acc accTy
  let free := (freeReads body).filter (fun x => x != v && x != acc)
  let ⟨invTys, invs⟩ ← invVars Γ env free
  let envb : Env := (acc, accTy) :: (v, .reg 64) :: free.zip invTys ++ env.drop Γ.length
  let ⟨τ, com⟩ ← elabStmts (accTy :: .reg 64 :: invTys) envb (body ++ [.ret acc])
  if h : τ = accTy then
    let ⟨s, k⟩ ← elabStmtsL (accTy :: Γ) ((acc, accTy) :: env) rest
    return ⟨s, ComL.forLoopN (invTys := invTys) ⟨n, h ▸ com⟩ accV invs k⟩
  else none

/-- The run-time loop hook of `elabStmtsL`: `for v = 0 to count { body }` as
    `ComL.forLoopBlock` over the run-time count, the body elaborated by
    `elabStmtsL` over the accumulator, the trip index and the invariants, as in
    `rolledLoop`. -/
partial def rolledLoopRt (Γ : Ctxt jasminDialect) (env : Env) (v count : String)
    (body rest : List Stmt) : Option (Σ τ : JasminTy, ComL Γ τ) := do
  let acc ← body.findSome? fun s => match s with
    | .store a _ _ | .storeAt a _ _ => some a
    | _ => none
  let accTy ← typeOf env acc
  let accV ← lookup Γ env acc accTy
  let cntV ← lookup Γ env count (.reg 64)
  let free := (freeReads body).filter (fun x => x != v && x != acc)
  let ⟨invTys, invs⟩ ← invVars Γ env free
  let envb : Env := (acc, accTy) :: (v, .reg 64) :: free.zip invTys ++ env.drop Γ.length
  let ⟨τ, com⟩ ← elabStmtsL (accTy :: .reg 64 :: invTys) envb (body ++ [.ret acc])
  if h : τ = accTy then
    let ⟨s, k⟩ ← elabStmtsL (accTy :: Γ) ((acc, accTy) :: env) rest
    return ⟨s, ComL.forLoopBlock (h ▸ com) cntV accV invs k⟩
  else none

/-- Elaborate a statement list into `Σ τ, ComL Γ τ`: `elabStmtsG` into `ComL`
    with `rolledLoop` and `rolledLoopRt` as the loop hooks. -/
partial def elabStmtsL (Γ : Ctxt jasminDialect) (env : Env) (ss : List Stmt) :
    Option (Σ τ : JasminTy, ComL Γ τ) :=
  elabStmtsG ComL.ret ComL.var (some rolledLoop) (some rolledLoopRt) Γ env ss

end

/-- Elaborate a whole function into `ComL` over its parameters (parameter `0`
    deepest, as in `elabFun`), keeping each `for` from `0` rolled. A plain global
    assignment `name = GLOBAL` is not accepted. -/
def elabFunL (f : JFun) :
    Option ((Γ : Ctxt jasminDialect) × (τ : JasminTy) × ComL Γ τ) := do
  let params' := f.params.reverse
  let Γ₀ : Ctxt jasminDialect := params'.map (fun p => toJ p.ty)
  let env₀ : Env := params'.map (fun p => (p.name, toJ p.ty))
    ++ f.decls.map (fun d => (d.2, toJ d.1))
  let ⟨τ, c⟩ ← elabStmtsL Γ₀ env₀ f.body
  return ⟨Γ₀, τ, c⟩

/-! ## 4. Elaboration self-check (parse → typed `Com`) -/

/-- `ec_dlog` elaborates to a 3-argument (`x`, `y`, table) `Com` returning
    `reg 64`. -/
theorem ecDlog_elaborates :
    (parseJincFun ecDlogSrc).toOption.bind (fun f =>
        (elabFun f).map (fun r => (r.1.length, r.2.1)))
      = some (3, .reg 64) := by native_decide

/-- `ec_pow_store` elaborates to a 3-argument (`out`, `m`, table) `Com` returning
    the updated `stackArr 8 2`. -/
theorem ecPowStore_elaborates :
    (parseJincFun ecPowStoreSrc).toOption.bind (fun f =>
        (elabFun f).map (fun r => (r.1.length, r.2.1)))
      = some (3, .stackArr 8 2) := by native_decide

/-! `mldsa_expand_mask_real` elaborates: its `for i = 0 to 128` loop unrolls into
the straight-line `Com`, over the two source parameters, returning the updated
`stackArr 32 256`. The unrolled program is 8207 bindings and elaborating it takes
seconds, so it is checked where the artifact is produced rather than here. -/

/-! `mldsa_expand_a_real` does not elaborate: its `while (cont != 0)` guard is a
data-dependent loop, outside the fragment this elaborator covers. -/
#guard
  ((parseJincFun mldsaExpandASrc).toOption.map (fun f => (elabFun f).isNone))
    == some true

/-! ## 4b. Denotational self-check (parse → `Com` computes the leaf) -/

/-- The elaborated `ec_dlog` `Com` at its concrete type (`[tbl, y, x] → reg 64`),
    or `none` if parse/elaboration produces a different shape. -/
def ecDlogCom? :
    Option (Com jasminDialect [.stackArr 8 529, .reg 8, .reg 8] (.reg 64)) :=
  match elabFun ((parseJincFun ecDlogSrc).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.stackArr 8 529, .reg 8, .reg 8] then
        if hτ : τ = .reg 64 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-- The elaborated `ec_pow_store` `Com` at its concrete type
    (`[tbl, m, out] → stackArr 8 2`). -/
def ecPowStoreCom? :
    Option (Com jasminDialect [.stackArr 8 56, .reg 64, .stackArr 8 2] (.stackArr 8 2)) :=
  match elabFun ((parseJincFun ecPowStoreSrc).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.stackArr 8 56, .reg 64, .stackArr 8 2] then
        if hτ : τ = .stackArr 8 2 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-- `ec_dlog` denotes to `tbl[(x*23 + y) mod 529]` widened to 64 bits: at
    `x = 5`, `y = 3`, `tbl i = i mod 256`, the index is `118` and the result is
    `118`. -/
theorem ecDlog_denote_concrete :
    ecDlogCom?.map (fun c => (c.denote
      (.cons (fun i => BitVec.ofNat 8 (i.val % 256)) (.cons (3 : BitVec 8) (.cons (5 : BitVec 8) .nil)))
        : BitVec 64))
      = some (118 : BitVec 64) := by native_decide

/-- `ec_pow_store` denotes to `out[0] = tbl[2m]`, `out[1] = tbl[2m+1]`: at `m = 4`,
    `tbl i = i`, the stored bytes are `tbl[8] = 8` and `tbl[9] = 9`. -/
theorem ecPowStore_denote_concrete :
    ecPowStoreCom?.map (fun c =>
      let o : Fin 2 → BitVec 8 := c.denote
        (.cons (fun i => BitVec.ofNat 8 i.val) (.cons (4 : BitVec 64)
          (.cons (fun _ => (0 : BitVec 8)) .nil)))
      (o 0, o 1))
      = some ((8 : BitVec 8), (9 : BitVec 8)) := by native_decide

/-- The elaborated `ct_select` `Com` at its concrete type (`[b, a, c] → reg 64`,
    `Γ` reversed from source order `c, a, b`). -/
def ctSelectCom? :
    Option (Com jasminDialect [.reg 64, .reg 64, .reg 1] (.reg 64)) :=
  match elabFun ((parseJincFun ctSelectSrc).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.reg 64, .reg 64, .reg 1] then
        if hτ : τ = .reg 64 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-- `ct_select` denotes to the branchless `c ? a : b`: with `a = 7`, `b = 9`,
    `c = 1` selects `a = 7`; `c = 0` selects `b = 9`. -/
theorem ctSelect_denote_true :
    ctSelectCom?.map (fun com => (com.denote
      (.cons (9 : BitVec 64) (.cons (7 : BitVec 64) (.cons (1 : BitVec 1) .nil))) : BitVec 64))
      = some (7 : BitVec 64) := by native_decide

theorem ctSelect_denote_false :
    ctSelectCom?.map (fun com => (com.denote
      (.cons (9 : BitVec 64) (.cons (7 : BitVec 64) (.cons (0 : BitVec 1) .nil))) : BitVec 64))
      = some (9 : BitVec 64) := by native_decide

/-! ## 4c. Denotational self-check of the scalar ops (`-`/`&`/`|`/`^`/`<<`/`>>`) -/

/-- The elaborated `Com` of a two-register `reg 64` scalar leaf, at its concrete
    type (`[b, a] → reg 64`, the source parameters `a, b` reversed so `a` is the
    deepest `Ctxt.Var`). -/
def binReg64Com? (src : String) :
    Option (Com jasminDialect [.reg 64, .reg 64] (.reg 64)) :=
  match elabFun ((parseJincFun src).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.reg 64, .reg 64] then
        if hτ : τ = .reg 64 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-- The elaborated `Com` of a one-register shift-by-literal `reg 64` leaf, at its
    concrete type (`[a] → reg 64`). -/
def shiftReg64Com? (src : String) :
    Option (Com jasminDialect [.reg 64] (.reg 64)) :=
  match elabFun ((parseJincFun src).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.reg 64] then
        if hτ : τ = .reg 64 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-- `sub` denotes to `a - b`: at `a = 10`, `b = 3`, the result is `7`. -/
theorem sub_denote_concrete :
    (binReg64Com? subSrc).map (fun c => (c.denote
      (.cons (3 : BitVec 64) (.cons (10 : BitVec 64) .nil)) : BitVec 64))
      = some (7 : BitVec 64) := by native_decide

/-- `bit_and` denotes to `a &&& b`: at `a = 12`, `b = 10`, the result is `8`. -/
theorem and_denote_concrete :
    (binReg64Com? andSrc).map (fun c => (c.denote
      (.cons (10 : BitVec 64) (.cons (12 : BitVec 64) .nil)) : BitVec 64))
      = some (8 : BitVec 64) := by native_decide

/-- `bit_or` denotes to `a ||| b`: at `a = 12`, `b = 10`, the result is `14`. -/
theorem or_denote_concrete :
    (binReg64Com? orSrc).map (fun c => (c.denote
      (.cons (10 : BitVec 64) (.cons (12 : BitVec 64) .nil)) : BitVec 64))
      = some (14 : BitVec 64) := by native_decide

/-- `bit_xor` denotes to `a ^^^ b`: at `a = 12`, `b = 10`, the result is `6`. -/
theorem xor_denote_concrete :
    (binReg64Com? xorSrc).map (fun c => (c.denote
      (.cons (10 : BitVec 64) (.cons (12 : BitVec 64) .nil)) : BitVec 64))
      = some (6 : BitVec 64) := by native_decide

/-- `shl3` denotes to `a <<< 3`: at `a = 5`, the result is `40`. -/
theorem shl_denote_concrete :
    (shiftReg64Com? shlSrc).map (fun c => (c.denote
      (.cons (5 : BitVec 64) .nil) : BitVec 64))
      = some (40 : BitVec 64) := by native_decide

/-- `shr2` denotes to `a >>> 2`: at `a = 40`, the result is `10`. -/
theorem shr_denote_concrete :
    (shiftReg64Com? shrSrc).map (fun c => (c.denote
      (.cons (40 : BitVec 64) .nil) : BitVec 64))
      = some (10 : BitVec 64) := by native_decide

/-! ## 5. Owned x86 emission (no jasminc) -/

/-- The SysV integer/pointer argument registers, in order. -/
def sysvRegs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]

/-- The ABI width of a parameter: a `reg w` argument carries width `w`; an array
    pointer is passed in a 64-bit register. -/
def abiWidth : JasminTy → Nat
  | .reg w => w
  | _ => 64

/-- Render the owned AT&T `.s` for an untyped `JFun`: `elabFun`, then
    `Com.toLprogPhysAbi` and `renderOwned`, argument `j` in `sysvRegs[j]`.
    `"; elaboration failed"` when `elabFun` declines. -/
def emitJFunAsm (f : JFun) (fname : String) : String :=
  match elabFun f with
  | none => "; elaboration failed"
  | some ⟨Γ, _, com⟩ =>
      let abiArgs := sysvRegs.take Γ.length
      let abiTyin := (Γ.map abiWidth).reverse
      CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
        (Com.toLprogPhysAbi com fname (abiArgs := abiArgs) (abiTyin := abiTyin))

/-- Render the owned AT&T `.s` for a parsed `.jinc` function, through
    `Com.toLprogPhysAbi` (no jasminc). Returns the parse/elab error message on
    failure. Argument `j` lands in `sysvRegs[j]` (natural C order): a 3+-argument
    signature is handled by the export's argument-liveness pin + per-argument
    qsave slots, so e.g. `ec_dlog(x, y, table)` exports as
    `(RDI, RSI, RDX) = (x, y, table)`. -/
def emitJincAsm (src : String) (fname : String) : String :=
  match parseJincFun src with
  | .error e => s!"; parse error: {e}"
  | .ok f => emitJFunAsm f fname

/-- The owned AT&T `.s` for a parsed `.jinc` function after `n` rounds of
    register-copy coalescing, which computes a value in the register its copy
    targets and drops the copy (`LprogCopyCoalesce.coalesceBody_stateStore`).
    The elaborator binds every source statement to a fresh name, so an unrolled
    loop carries one copy per binding for the printer to remove. -/
def emitJincAsmCoalesced (src : String) (fname : String) (n : Nat) : String :=
  match parseJincFun src with
  | .error e => s!"; parse error: {e}"
  | .ok f =>
      match elabFun f with
      | none => "; elaboration failed"
      | some ⟨Γ, _, com⟩ =>
          let abiArgs := sysvRegs.take Γ.length
          let abiTyin := (Γ.map abiWidth).reverse
          CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
            (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce.coalesceRounds n
              (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.optimizeLprogBasicBlocks
                (Com.toLprogPhysAbi com fname (abiArgs := abiArgs) (abiTyin := abiTyin))))

/-! ## 6. Owned x86 emission of a rolled `ComL`

`rolledLfundef` is the register-ABI physical export of a `ComL` whose loops
thread one memory array (`elabFunL`), each array parameter a pointer in its
SysV register. Before the physical register allocation (`physBody`), the virtual
body is rewritten in three ways:

* every `stackStore` result is replaced by the array it stores into
  (`canonicalizeMemrefThread`), and each loop's accumulator by the array its seed
  names, so a store addresses the array the source stores into and the loop
  feedback is a self-copy;
* a `LIVEPIN` instruction reading every argument opens the body, so the
  allocator keeps each argument live from entry (it is removed after the
  allocation);
* the symbol of each `LOADSYM` (`b = @SYM`) is carried as the compile-time
  operand `.arr SYM 0`, which the allocators leave untouched and the printer
  renders `leaq SYM(%rip)`.

`emitJFunRolledAsm` attaches each table read at a run-time index as a `.rodata`
table (`Lprog.withRodataTable`), runs the owned back end (`ownedLprog`), selects
`rorx` for each rotate whose destination differs from its source (`rorxLprog`),
and prints. -/

/-- `LOADSYM` with its symbol as the compile-time operand `.arr sym 0`. -/
def symOperandFix (b : Lcmd) : Lcmd :=
  b.map fun i => match i.li_i with
    | .Lopn ds "LOADSYM" [.reg s] => ⟨i.li_ii, .Lopn ds "LOADSYM" [.arr s 0]⟩
    | _ => i

/-- The source of the first 64-bit copy into `acc` (a loop's seed move). -/
def seedOf (b : Lcmd) (acc : String) : Option String :=
  b.findSome? fun i => match i.li_i with
    | .Lopn [.reg d] "MOV:64" [.reg s] => if d == acc then some s else none
    | _ => none

/-- The body with every store result replaced by its array and each accumulator
    of `accs` by the array its seed names, with the induced map on names. -/
def threadAccs (b : Lcmd) (accs : List String) : Lcmd × (String → String) :=
  let m0 := arrChainAlias b
  accs.foldl (fun (b, ren) acc =>
    match seedOf b acc with
    | some s =>
        let tgt := canonMemrefName (arrChainAlias b) s
        (canonicalizeMemrefThread (aliasRegBody acc tgt b),
         fun n => let n' := ren n; if n' == acc then tgt else n')
    | none => (b, ren))
    (canonicalizeMemrefThread b, canonMemrefName m0)

/-- The register-ABI physical `Lfundef` of a rolled `ComL` (see §6): argument `j`
    in `sysvRegs[j]`, the result moved to `RAX`. -/
def rolledLfundef {Γ : Ctxt jasminDialect} {τ : JasminTy} (c : ComL Γ τ) : Lfundef :=
  let virt0 := ComL.toLfundef c
  let pin : Lcmd :=
    [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" (virt0.lfd_arg.map LOperand.reg)⟩]
  let (body, ren) := threadAccs (pin ++ symOperandFix virt0.lfd_body)
    ((ComL.loopAccRegs c Γ.length).map regName)
  let virt := { virt0 with lfd_body := body, lfd_res := virt0.lfd_res.map ren }
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body)
  let resPhys := virt.lfd_res.map (physNameForBody virt.lfd_body tbl)
  let abi := sysvRegs.take virt.lfd_arg.length
  let argMat := buildArgMaterializePhys virt tbl abi
  let pbody := (physBody (fun _ => none) virt.lfd_body).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  let retEpi : Lcmd := match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let body' := if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  { virt with lfd_body := argMat ++ body', lfd_arg := abi,
              lfd_tyin := virt.lfd_tyin.take abi.length, lfd_res := resPhys }

/-- A 64-bit rotate by an immediate into a register other than its source, as
    the BMI2 `rorx` (`RORX:<n>:64`); every other instruction unchanged. -/
def rorxInstr (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn [.reg d] opn [s] =>
      match opn.splitOn ":" with
      | ["ROR", n, "64"] =>
          if s == .reg d then i else ⟨i.li_ii, .Lopn [.reg d] ("RORX:" ++ n ++ ":64") [s]⟩
      | _ => i
  | _ => i

/-- `rorxInstr` on every function body. -/
def rorxLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, { f with lfd_body := f.lfd_body.map rorxInstr }) }

/-- The `Lprog` of a `JFun` imported with rolled loops (`JincInline.importFunRolled`)
    under the symbol `fname`, with the global tables it reads at a run-time index
    (`tables`) as `.rodata`, before the owned back end. `none` when `elabFunL`
    declines. -/
def rolledLprog (f : JFun) (tables : List (String × List Nat)) (fname : String) :
    Option Lprog := do
  let ⟨_, _, c⟩ ← elabFunL f
  let p : Lprog := { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := [],
                     lp_funcs := [(fname, rolledLfundef c)] }
  return tables.foldl (fun p (s, ws) => p.withRodataTable s (ws.map (BitVec.ofNat 64))) p

/-- The owned AT&T `.s` of `rolledLprog`: `ownedLprog`, `rorxLprog`, then the
    printer. `"; elaboration failed"` when `elabFunL` declines. -/
def emitJFunRolledAsm (f : JFun) (tables : List (String × List Nat)) (fname : String) :
    String :=
  match rolledLprog f tables fname with
  | none => "; elaboration failed"
  | some p =>
      CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
        (rorxLprog (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.ownedLprog p))

/-! ## 7. Parameter slots, frame arrays and calls

`rolledLfundefWith` exports a rolled `ComL` whose parameters come from
`ArgSlot`s (`JincInline.importFunRolledWith`): a parameter in the argument
register of an earlier one (a memory view) reads that parameter's name, and the
frame regions lie at the bottom of the function's frame (`FRAMEADD`), the region
at offset `0` of a calling body addressed through `RSP` itself. A leaf call
becomes a System V call (`expandCallShadows`), and a body that issues one is
allocated by `callSafeTable`. With every parameter in its own argument register,
no frame region and no call, it is `rolledLfundef`. -/

/-- The number of argument moves that may precede a call: a value read within
    that many trace events before a call counts as live across it. -/
def callMarshalWindow : Nat := 6

/-- The allocation table `tbl` of a body that issues calls, with every value
    that is live across a call moved out of the caller-saved registers. A value
    is live across a call when its live range, with an argument's starting at
    entry, contains the call or ends within `callMarshalWindow` events before
    it, or when it is written and never read. Such a value held in a
    caller-saved register moves to a callee-saved register that holds no other
    value over its live range, or else to a frame cell of its own; every other
    value keeps its location. The hardware register names the call sequences
    use are resolved to themselves and occupy no allocated register. -/
def callSafeTable (body : Lcmd) (tbl : Array Nat) : Array Nat := Id.run do
  let tr := bodyTrace body
  let calls := bodyCallTracePositions body
  let names : Array String := (bodyNames body).toArray
  let univ := physUniverse tr
  let mut isRead : Array Bool := Array.replicate univ false
  for ev in tr do
    for s in ev.rds do
      if s < isRead.size then isRead := isRead.set! s true
  let items := (physLiveItems tr).filterMap fun (s, st0, en) =>
    let nm := names[s]?.getD ""
    if nm == "%livepin" || isHwRegName nm then none
    else
      let st := if nm.startsWith "a" && (strDropToNat? nm 1).isSome then 0 else st0
      some (s, st, en)
  let callee := straightCallCalleeSavedPool
  let mut t := tbl
  let mut nextSpill := numGPRegs
  for v in tbl do
    if numGPRegs ≤ v && v < vectorBase then nextSpill := Nat.max nextSpill (v + 1)
  for (s, st, en) in items do
    let raw := physMapTabled t s
    let crossing := calls.any (fun p => st < p && p ≤ en + callMarshalWindow)
                      || !(isRead[s]?.getD true)
    if crossing && raw < numGPRegs && !callee.contains raw then
      let busy (r : Nat) : Bool := items.any fun (s', st', en') =>
        s' != s && physMapTabled t s' == r && st' ≤ en && st ≤ en'
      match callee.find? (fun r => !busy r) with
      | some r => t := t.set! s r
      | none =>
          t := t.set! s nextSpill
          nextSpill := nextSpill + 1
  return t

/-- The physical name of `n` under `callSafeTable`: a frame cell and a hardware
    register name are themselves. -/
def callSafeName (body : Lcmd) (tbl : Array Nat) (n : String) : String :=
  if isFrameSlotName n || isHwRegName n then n
  else physRegName (physMapTabled tbl (nameSlot body n))

/-- An operand renamed by `callSafeName`. -/
def callSafeOperand (body : Lcmd) (tbl : Array Nat) : LOperand → LOperand
  | .reg n => .reg (callSafeName body tbl n)
  | .arrIdx b i s => .arrIdx (callSafeName body tbl b) (callSafeName body tbl i) s
  | o => o

/-- The register copies `moves` (destination, source) performed as one parallel
    assignment: a copy is emitted once no pending copy reads its destination,
    and a cycle is broken through `R15`. -/
def parallelCopies (moves : List (String × String)) : Lcmd := Id.run do
  let mut pend := moves.filter (fun (d, s) => d != s)
  let mut out : Lcmd := []
  for _ in [0:2 * moves.length + 2] do
    if pend.isEmpty then break
    match pend.find? (fun (d, _) => !pend.any (fun (_, s) => s == d)) with
    | some (d, s) =>
        out := out ++ [⟨0, .Lopn [.reg d] "MOVQ" [.reg s]⟩]
        pend := pend.filter (· != (d, s))
    | none =>
        match pend.head? with
        | some (d, _) =>
            out := out ++ [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg d]⟩]
            pend := pend.map (fun (d', s) => (d', if s == d then reloadScratch else s))
        | none => pure ()
  return out

/-- The entry copies of the parameters of `virt` the body reads, from their
    slots: an argument register into a frame cell first, then the register
    copies as one parallel assignment, then the address of each frame region.
    `rn` is the physical name of a body name. -/
def slotMaterialize (virt : Lfundef) (rn : String → String) (slots : List ArgSlot) : Lcmd :=
  let body := virt.lfd_body
  let used (nm : String) : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ _ srcs => srcs.any (fun s =>
        match s with
        | .reg n => n == nm
        | .arrIdx b idx _ => b == nm || idx == nm
        | _ => false)
    | _ => false)
  let entries := (slots.zipIdx.filter (fun (_, j) => used (argName j))).map
    (fun (sl, j) => (rn (argName j), sl))
  let isSpill (d : String) : Bool := (LOperand.reg d).isSpill
  let toMem : Lcmd := entries.flatMap fun (d, sl) =>
    match sl with
    | .abi k =>
        if isSpill d then
          [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg (sysvRegs.getD k "RDI")]⟩,
           ⟨0, .Lopn [.reg d] "MOVQ" [.reg reloadScratch]⟩]
        else []
    | .frame _ => []
  let regMoves := entries.filterMap fun (d, sl) =>
    match sl with
    | .abi k => if isSpill d then none else some (d, sysvRegs.getD k "RDI")
    | .frame _ => none
  let leas : Lcmd := entries.flatMap fun (d, sl) =>
    match sl with
    | .frame off =>
        if isSpill d then
          [⟨0, .Lopn [.reg reloadScratch] "LEA:64" [.reg (memName "RSP" off)]⟩,
           ⟨0, .Lopn [.reg d] "MOVQ" [.reg reloadScratch]⟩]
        else [⟨0, .Lopn [.reg d] "LEA:64" [.reg (memName "RSP" off)]⟩]
    | .abi _ => []
  toMem ++ parallelCopies regMoves ++ leas

/-- The bytes of the frame regions of `slots`, whose parameters have the cell
    counts `cells`, rounded up to 16. -/
def frameBytes (slots : List ArgSlot) (cells : List Nat) : Nat :=
  let top := (slots.zip cells).foldl (fun m (sl, n) =>
    match sl with
    | .frame off => max m (off + 8 * n)
    | .abi _ => m) 0
  (top + 15) / 16 * 16

/-- A byte cast (`TRUNC`/`ZEROEXT`) with a frame-cell operand, routed through
    `R15`: the printer renders the cast between registers only. -/
def legalizeByteCasts (body : Lcmd) : Lcmd :=
  body.flatMap fun i =>
    match i.li_i with
    | .Lopn [.reg d] opn [.reg s] =>
        if (opn == "TRUNC" || opn == "ZEROEXT")
            && ((LOperand.reg s).isSpill || (LOperand.reg d).isSpill) then
          let sS := (LOperand.reg s).isSpill
          let dS := (LOperand.reg d).isSpill
          (if sS then [⟨i.li_ii, .Lopn [.reg reloadScratch] "MOVQ" [.reg s]⟩] else [])
            ++ [⟨i.li_ii, .Lopn [.reg (if dS then reloadScratch else d)] opn
                  [.reg (if sS then reloadScratch else s)]⟩]
            ++ (if dS then [⟨i.li_ii, .Lopn [.reg d] "MOVQ" [.reg reloadScratch]⟩] else [])
        else [i]
    | _ => [i]

/-- The register-ABI physical `Lfundef` of a rolled `ComL` whose parameters
    come from `slots`, with `cells` the cell count of each parameter (see §7):
    the result moved to `RAX`, kept live to the return. -/
def rolledLfundefWith {Γ : Ctxt jasminDialect} {τ : JasminTy} (c : ComL Γ τ)
    (slots : List ArgSlot) (cells : List Nat) : Lfundef :=
  let virt00 := ComL.toLfundef c
  let body00 := expandCallShadows virt00.lfd_body
  let hasCall0 := bodyHasCall body00
  let fb := frameBytes slots cells
  if !hasCall0 && fb == 0 && slots == (List.range slots.length).map ArgSlot.abi then
    rolledLfundef c
  else
  -- a parameter sharing its slot with an earlier one reads the earlier one's
  -- name; in a calling body the frame region at offset 0 is addressed through `RSP`
  let aliases : List (String × String) := (slots.zipIdx).filterMap fun (sl, j) =>
    match sl with
    | .abi k =>
        match (slots.take j).findIdx? (· == .abi k) with
        | some i => some (argName j, argName i)
        | none => none
    | .frame 0 => if hasCall0 then some (argName j, "RSP") else none
    | .frame _ => none
  let virt0 := { virt00 with
    lfd_body := aliases.foldl (fun b (f, t) => aliasRegBody f t b) body00 }
  let pin : Lcmd :=
    [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
      ((virt0.lfd_arg.filter (fun a => !aliases.any (·.1 == a))).map LOperand.reg)⟩]
  let (body1, ren) := threadAccs (pin ++ symOperandFix virt0.lfd_body)
    ((ComL.loopAccRegs c Γ.length).map regName)
  let res := virt0.lfd_res.map ren
  let endPin : Lcmd := [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN" (res.map LOperand.reg)⟩]
  let body := match body1.getLast? with
    | some ⟨_, .Lret⟩ => body1.dropLast ++ endPin ++ [⟨0, .Lret⟩]
    | _ => body1 ++ endPin
  let virt := { virt0 with lfd_body := body, lfd_res := res }
  let hasCall := bodyHasCall virt.lfd_body
  let tbl0 := bodyPhysTable virt.lfd_body
  let tbl := if hasCall then callSafeTable virt.lfd_body tbl0 else tbl0
  let rn : String → String :=
    if hasCall then callSafeName virt.lfd_body tbl else physNameForBody virt.lfd_body tbl
  let resPhys := virt.lfd_res.map rn
  let nAbi := slots.foldl (fun m sl => match sl with | .abi k => max m (k + 1) | .frame _ => m) 0
  let abi := sysvRegs.take nAbi
  let argMat := slotMaterialize virt rn slots
  let rmap : LOperand → LOperand :=
    if hasCall then callSafeOperand virt.lfd_body tbl else remapOperand virt.lfd_body tbl
  let pbody := (legalizeByteCasts
      (physBodyRmap rmap (movImmOracle virt.lfd_body) virt.lfd_body)).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  let retEpi : Lcmd := match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let body' := if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  let frameAdd : Lcmd := if fb == 0 then [] else [⟨0, .Lopn [] "FRAMEADD" [.imm fb]⟩]
  { virt with lfd_body := frameAdd ++ argMat ++ body', lfd_arg := abi,
              lfd_tyin := virt.lfd_tyin.take abi.length, lfd_res := resPhys }

/-- The cell count of a parameter type (`1` for a register). -/
def cellsOf : JTy → Nat
  | .arr _ n => n
  | .reg _ => 1

/-- The `Lfundef` of a rolled import with parameter slots `slots`, or `none`
    when `elabFunL` declines. -/
def rolledImportFundef (f : JFun) (slots : List ArgSlot) : Option Lfundef := do
  let ⟨_, _, c⟩ ← elabFunL f
  return rolledLfundefWith c slots (f.params.map (fun p => cellsOf p.ty))

/-- One `Lprog` of the rolled imports `fs` (function, parameter slots, symbol),
    with the global tables `tables` as `.rodata`; `none` when one of them does
    not elaborate. -/
def rolledProgram (fs : List (JFun × List ArgSlot × String))
    (tables : List (String × List Nat)) : Option Lprog := do
  let funcs ← fs.mapM fun (f, sl, nm) => do return (nm, ← rolledImportFundef f sl)
  let p : Lprog := { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := [],
                     lp_funcs := funcs }
  return tables.foldl (fun p (s, ws) => p.withRodataTable s (ws.map (BitVec.ofNat 64))) p

/-- The owned AT&T `.s` of `rolledProgram`: `ownedLprog`, `rorxLprog`, then the
    printer. `"; elaboration failed"` when `rolledProgram` declines. -/
def emitRolledProgramAsm (fs : List (JFun × List ArgSlot × String))
    (tables : List (String × List Nat)) : String :=
  match rolledProgram fs tables with
  | none => "; elaboration failed"
  | some p =>
      CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
        (rorxLprog (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.ownedLprog p))

end CatCrypt.Crypto.Jasmin.JincElab
