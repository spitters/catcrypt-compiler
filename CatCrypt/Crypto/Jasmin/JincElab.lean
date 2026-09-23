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

/-!
# `.jinc` elaborator: untyped `JFun` → `Com jasminDialect` → owned x86

Elaborates a parsed straight-line `JFun` (`JincToCom`) into an intrinsically-typed
`Com jasminDialect Γ τ`, then renders it through the owned backend
(`Com.toLprogPhysAbi` → `renderLprogAtt`) — no jasminc. Global tables assigned by
`name = GLOBAL` are turned into pointer parameters (the owned export emits no
globals). The op mapping is `(Wu)x → castW`, the binary ops
`a*b/a+b/a-b/a&b/a|b/a^b/a<<n/a>>n → regArith`, integer
literals → `regConst`, `tbl[idx] → stackLoad`, `out[k]=v → stackStore`, and the
branchless conditional `c ? a : b → select` (constant-time control flow: renders
to `test`/`cmovcc`, no PC divergence). A bare `lhs = src` is a register copy, in
the dialect the width-preserving `castW w w`; `(Wu) arr[idx]` is `stackLoad` then
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

/-- Elaborate a statement list into `Σ τ, Com jasminDialect Γ τ`, threading the
    context `Γ` and the name environment `env`. Literal operands introduce a
    `regConst` binding; const-indexed stores introduce a `regConst` index. -/
partial def elabStmts : (Γ : Ctxt jasminDialect) → Env → List Stmt →
    Option (Σ τ : JasminTy, Com jasminDialect Γ τ)
  | Γ, env, [Stmt.ret nm] => do
      let (i, t) ← envFind env nm
      let v ← mkVar Γ i t
      return ⟨t, Com.ret v⟩
  | Γ, env, Stmt.assign lhs (Rhs.cast w src) :: rest => do
      let sTy ← typeOf env src
      match sTy with
      | .reg sw =>
          let sv ← lookup Γ env src (.reg sw)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.castW sw w, rfl, .cons sv .nil⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.load arr idx) :: rest => do
      let aTy ← typeOf env arr
      match aTy with
      | .stackArr w n =>
          let av ← lookup Γ env arr (.stackArr w n)
          let iv ← lookup Γ env idx (.reg 64)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.stackLoad w n, rfl, .cons av (.cons iv .nil)⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
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
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.bin op a (Operand.var b)) :: rest => do
      let aTy ← typeOf env a
      match aTy with
      | .reg w =>
          let av ← lookup Γ env a (.reg w)
          let bv ← lookup Γ env b (.reg w)
          let e : Expr jasminDialect Γ (.reg w) :=
            ⟨.regArith (binOf op) w, rfl, .cons av (.cons bv .nil)⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.bin op a (Operand.lit n)) :: rest => do
      let aTy ← typeOf env a
      match aTy with
      | .reg w =>
          -- bind a fresh constant, then the binary op over it
          let cName := "%c" ++ toString Γ.length
          let ce : Expr jasminDialect Γ (.reg w) := ⟨.regConst w n, rfl, .nil⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((cName, .reg w) :: env)
            (Stmt.assign lhs (Rhs.bin op a (Operand.var cName)) :: rest)
          return ⟨s, Com.var ce body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.imm n) :: rest => do
      let lTy ← typeOf env lhs
      match lTy with
      | .reg w =>
          let e : Expr jasminDialect Γ (.reg w) := ⟨.regConst w n, rfl, .nil⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.glob src) :: rest => do
      -- a register copy `lhs = src`, expressed as the width-preserving cast
      let sTy ← typeOf env src
      match sTy with
      | .reg w =>
          let sv ← lookup Γ env src (.reg w)
          let e : Expr jasminDialect Γ (.reg w) := ⟨.castW w w, rfl, .cons sv .nil⟩
          let ⟨s, body⟩ ← elabStmts (.reg w :: Γ) ((lhs, .reg w) :: env) rest
          return ⟨s, Com.var e body⟩
      | _ => none
  | Γ, env, Stmt.assign lhs (Rhs.castLoad w arr idx) :: rest =>
      -- `lhs = (Wu) arr[idx]`  ≡  `%l = arr[idx]; lhs = (Wu) %l`
      let tName := "%l" ++ toString Γ.length
      elabStmts Γ env (Stmt.assign tName (Rhs.load arr idx) ::
        Stmt.assign lhs (Rhs.cast w tName) :: rest)
  | Γ, env, Stmt.compound op lhs operand :: rest =>
      -- `lhs op= operand`  ≡  `lhs = lhs op operand`
      elabStmts Γ env (Stmt.assign lhs (Rhs.bin op lhs operand) :: rest)
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
          let ⟨s, body⟩ ← elabStmts (.stackArr w n :: Γ') ((arr, .stackArr w n) :: env') rest
          return ⟨s, Com.var ce (Com.var se body)⟩
      | _ => none
  | Γ, env, Stmt.storeAt arr (Operand.lit k) val :: rest => do
      -- bind the literal index, then store at the bound name
      let iName := "%x" ++ toString Γ.length
      let ce : Expr jasminDialect Γ (.reg 64) := ⟨.regConst 64 k, rfl, .nil⟩
      let ⟨s, body⟩ ← elabStmts (.reg 64 :: Γ) ((iName, .reg 64) :: env)
        (Stmt.storeAt arr (Operand.var iName) val :: rest)
      return ⟨s, Com.var ce body⟩
  | Γ, env, Stmt.storeAt arr (Operand.var idx) (Rhs.glob val) :: rest => do
      let aTy ← typeOf env arr
      match aTy with
      | .stackArr w n =>
          let av ← lookup Γ env arr (.stackArr w n)
          let iv ← lookup Γ env idx (.reg 64)
          let vv ← lookup Γ env val (.reg w)
          let se : Expr jasminDialect Γ (.stackArr w n) :=
            ⟨.stackStore w n, rfl, .cons av (.cons iv (.cons vv .nil))⟩
          let ⟨s, body⟩ ← elabStmts (.stackArr w n :: Γ) ((arr, .stackArr w n) :: env) rest
          return ⟨s, Com.var se body⟩
      | _ => none
  | Γ, env, Stmt.storeAt arr idx val :: rest =>
      -- a computed right-hand side: bind it, then store the bound name
      let vName := "%v" ++ toString Γ.length
      elabStmts Γ env (Stmt.assign vName val ::
        Stmt.storeAt arr idx (Rhs.glob vName) :: rest)
  | Γ, env, Stmt.forTo v lo hi body :: rest =>
      -- one unrolled iteration: the counter is a `regConst` binding, and the
      -- remaining range is the same `forTo` with `lo` advanced
      if lo < hi then do
        let ce : Expr jasminDialect Γ (.reg 64) := ⟨.regConst 64 lo, rfl, .nil⟩
        let ⟨s, cbody⟩ ← elabStmts (.reg 64 :: Γ) ((v, .reg 64) :: env)
          (body ++ Stmt.forTo v (lo + 1) hi body :: rest)
        return ⟨s, Com.var ce cbody⟩
      else elabStmts Γ env rest
  -- `Stmt.whileNz`: a data-dependent loop, outside the fragment this elaborator
  -- covers.
  | _, _, _ => none

/-! ## 3. Whole-function elaboration -/

/-- The local name a `name = GLOBAL` statement binds (a global table assignment). -/
def globName : Stmt → Option String
  | .assign nm (.glob _) => some nm
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

/-- Render the owned AT&T `.s` for a parsed `.jinc` function, through
    `Com.toLprogPhysAbi` (no jasminc). Returns the parse/elab error message on
    failure. Argument `j` lands in `sysvRegs[j]` (natural C order): a 3+-argument
    signature is handled by the export's argument-liveness pin + per-argument
    qsave slots, so e.g. `ec_dlog(x, y, table)` exports as
    `(RDI, RSI, RDX) = (x, y, table)`. -/
def emitJincAsm (src : String) (fname : String) : String :=
  match parseJincFun src with
  | .error e => s!"; parse error: {e}"
  | .ok f =>
      match elabFun f with
      | none => "; elaboration failed"
      | some ⟨Γ, _, com⟩ =>
          let abiArgs := sysvRegs.take Γ.length
          let abiTyin := (Γ.map abiWidth).reverse
          CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
            (Com.toLprogPhysAbi com fname (abiArgs := abiArgs) (abiTyin := abiTyin))

end CatCrypt.Crypto.Jasmin.JincElab
