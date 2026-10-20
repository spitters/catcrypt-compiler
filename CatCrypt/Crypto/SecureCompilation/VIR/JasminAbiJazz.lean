/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText

/-!
# Orchestration units over linked leaves

An orchestration body is a straight-line program `Com jasminDialect Γ t` whose bindings are
calls `extCall f` of linked leaves and scalar operations. `orchUnit` lowers it to a
compilation unit of the single Jasmin printer: one `export fn` whose body calls the leaves,
and one extern signature per leaf. The calling convention is an `OrchMode`, a choice of
storage classes for the array values:

* `stackArr`: each array input `p_i` (`reg ptr`) is copied into an owned `stack` buffer
  `s_i`; each leaf call `x = f(a, …)` writes a fresh `stack` buffer; the result is copied
  into the `reg mut ptr` parameter `out`, which the function returns. The leaves take
  their arrays as `stack` values.
* `regPtr`: the buffers of `stackArr`; each leaf call `x = f(x, a, …)` passes the fresh
  result buffer first. The leaves take their input arrays as `reg ptr` and the result
  buffer as `reg mut ptr`, which they return.
* `memPtr`: every array is a `reg u64` memory address; the inputs are passed to the leaves
  directly and each array result is written through `out`: `out = f(out, a, …)`.

A scalar result is returned in a register and has no `out` parameter. A scalar binding is
lowered by `NFToJasmin.emitOp`; a binding other than a leaf call that takes or returns an
array is refused. The unit is returned only when it is well formed (`wellFormedB`), so every
called leaf has an extern signature.

## Main definitions

* `OrchMode`, `OrchMode.leafStorage`, `OrchMode.leafInStorage`: the calling conventions,
  the storage class of a leaf's result array and that of its input arrays.
* `leafExtern`: the extern signature of a leaf in a mode.
* `orchBody`, `orchFn`, `orchUnit`: the lowering of a body, of the function and of the unit.
* `emitAbiOrchJ`: the text of the unit through the checked printer `Jazz.printChecked`.
* `emitAbiOrchRegJ`: the text of a register-arithmetic program through `emitJazzN`.

## Main results

* `emitAbiOrchJ_parse`: a returned text parses to the erasure of the unit `orchUnit` builds.
* `emitAbiOrchRegJ_parse`: a returned text parses to the unit `nfToJasmin` builds, without
  its extern signatures.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiJazz

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.Jasmin (SType WSize PExpr LVal InstrR Cmd FunDecl)
open CatCrypt.Crypto.Jasmin.Jazz (Storage PType Decl ExternSig JazzFn JazzUnit cmdVars)

/-! ## 1. Calling conventions -/

/-- The calling convention of an orchestration: owned `stack` buffers passed by value
(`stackArr`), owned `stack` buffers passed as `reg ptr` with the result buffer first
(`regPtr`), or `reg u64` memory addresses (`memPtr`). -/
inductive OrchMode where
  | stackArr | regPtr | memPtr
  deriving DecidableEq, Repr, Inhabited

/-- The storage class of the result array of a leaf, and of its result buffer parameter:
`stack`, `reg mut ptr` or `reg`. -/
def OrchMode.leafStorage : OrchMode → Storage
  | .stackArr => .stack
  | .regPtr => .regPtr true
  | .memPtr => .reg

/-- The storage class of the input array parameters of a leaf: `stack`, `reg ptr` or
`reg`. -/
def OrchMode.leafInStorage : OrchMode → Storage
  | .stackArr => .stack
  | .regPtr => .regPtr false
  | .memPtr => .reg

/-- Whether a leaf receives its result buffer as its first argument. -/
def OrchMode.dstFirst : OrchMode → Bool
  | .stackArr => false
  | _ => true

/-- `true` for the array types `stackArr w n`. -/
def isArrTy : JasminTy → Bool
  | .stackArr _ _ => true
  | _ => false

/-- The storage class and surface type of a value of type `t` in the mode `m`, an array
taking the storage class `s`: a `reg u64` address in `memPtr`, the array type otherwise;
a scalar takes the storage class of its Jasmin type. -/
def OrchMode.slot (m : OrchMode) (s : Storage) (t : JasminTy) : Storage × PType :=
  match m, t with
  | .memPtr, .stackArr _ _ => (.reg, .word .U64)
  | _, .stackArr _ _ => (s, ptyOf t)
  | _, _ => (storOf (styOf t), ptyOf t)

/-- The extern signature of the leaf `(f, argTys, retTy)` in the mode `m`: the slots of the
arguments at the input storage `leafInStorage`, preceded by the slot of the result buffer
when the leaf takes it first, and the slot of the result; the result buffer and the result
take the storage `leafStorage`, so in `regPtr` only the result buffer is mutable. -/
def leafExtern (m : OrchMode) (l : String × List JasminTy × JasminTy) : ExternSig :=
  let ps := l.2.1.map (m.slot m.leafInStorage)
  let dst := m.slot m.leafStorage l.2.2
  { name := l.1
    params := if m.dstFirst && isArrTy l.2.2 then dst :: ps else ps
    results := [dst] }

/-! ## 2. The body -/

/-- The loop counter of the copy loops. -/
def kVar : JVar := mkV 'k' 0 .sint

/-- The copy `for k = 0 to n { dst[k] = src[k]; }` of an array of type `t`; empty for a
scalar type. -/
def arrCopyLoop (dst src : JVar) : JasminTy → Cmd
  | .stackArr w n =>
      [.Cfor ⟨kVar, vi0⟩ ⟨.UpTo, 0, n⟩
        [.Cassgn (.Laset .AAscale (wsOf w) ⟨dst, vi0⟩ (pv kVar)) .AT_none (.sword (wsOf w))
          (.Pget .AAscale (wsOf w) ⟨⟨src, vi0⟩, false⟩ (pv kVar))]]
  | _ => []

/-- The `stack` declaration of an array buffer of type `t`. -/
def stackDecl (x : JVar) (t : JasminTy) : Decl :=
  { storage := .stack, ty := ptyOf t, names := [x.vname] }

/-- **The lowering of an orchestration body.** `env` maps the de Bruijn indices of the
context to their variables, `out` is the result parameter of an array result and `d` the
depth of the next binding. A leaf call with an array result writes the fresh `stack` buffer
`mkV 'r' d` (`stackArr`, `regPtr`) or `out` (`memPtr`); a leaf call with a scalar result
writes the fresh register `mkV 'r' d`; a scalar operation is `emitOp`. Returns the code,
the declarations of the fresh buffers and the variable of the result. -/
def orchBody (m : OrchMode) (out : Option JVar) :
    (env : List JVar) → {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (d : Nat) → Option (Cmd × List Decl × JVar)
  | env, _, _, .ret v, _ => some ([], [], env.getD (varIndex v) dfltV)
  | env, _, _, .var (t := u) e body, d =>
      let as := resolveHV env e.args
      match e.op with
      | .extCall f _ _ =>
          if isArrTy u then
            match m, out with
            | .memPtr, some o =>
                (orchBody m out (o :: env) body (d + 1)).map fun r =>
                  (.Ccall .DoNotInline [lvv o] ⟨f⟩ (pv o :: as.map pv) :: r.1, r.2.1, r.2.2)
            | .memPtr, none => none
            | _, _ =>
                let x := mkV 'r' d (styOf u)
                let args := if m.dstFirst then pv x :: as.map pv else as.map pv
                (orchBody m out (x :: env) body (d + 1)).map fun r =>
                  (.Ccall .DoNotInline [lvv x] ⟨f⟩ args :: r.1, stackDecl x u :: r.2.1, r.2.2)
          else
            let x := mkV 'r' d (styOf u)
            (orchBody m out (x :: env) body (d + 1)).map fun r =>
              (.Ccall .DoNotInline [lvv x] ⟨f⟩ (as.map pv) :: r.1, r.2.1, r.2.2)
      | op =>
          if isArrTy u || (DialectSignature.sig op).any isArrTy then none
          else
            (emitOp op d (mkV 'r' d (styOf u)) as).bind fun cx =>
            (orchBody m out (cx.2 :: env) body (d + 1)).map fun r =>
              (cx.1 ++ r.1, r.2.1, r.2.2)

/-! ## 3. The function and the unit -/

/-- The input parameter `p_i` of type `t`. -/
def inVar (m : OrchMode) (i : Nat) (t : JasminTy) : JVar :=
  mkV 'p' i (m.slot (.regPtr false) t).2.toSType

/-- Whether the input of type `t` is copied into an owned buffer: an array outside
`memPtr`. -/
def owns (m : OrchMode) (t : JasminTy) : Bool := m != .memPtr && isArrTy t

/-- The owned buffer `s_i` of the input of type `t`. -/
def ownVar (i : Nat) (t : JasminTy) : JVar := mkV 's' i (styOf t)

/-- The variable the body reads for the input `i`: its owned buffer or its parameter. -/
def envVar (m : OrchMode) (i : Nat) (t : JasminTy) : JVar :=
  if owns m t then ownVar i t else inVar m i t

/-- The copy of the input `i` into its owned buffer. -/
def copyIn (m : OrchMode) (i : Nat) (t : JasminTy) : Cmd :=
  if owns m t then arrCopyLoop (ownVar i t) (inVar m i t) t else []

/-- The declaration of the owned buffer of the input `i`. -/
def ownDecl (m : OrchMode) (i : Nat) (t : JasminTy) : List Decl :=
  if owns m t then [stackDecl (ownVar i t) t] else []

/-- The `export fn` `fname` over the parameters `ps` with the body `body` and the results
`res` at the slots `resTys`: the array buffers are declared by `arrDecls`, every other
variable of the body and the results by `declOf` at the storage class of its type. -/
def orchFnOf (fname : String) (ps : List (JVar × Storage × PType)) (body : Cmd)
    (arrDecls : List Decl) (res : List JVar) (resTys : List (Storage × PType)) : JazzFn :=
  let pvs := ps.map Prod.fst
  let named := arrDecls.flatMap (·.names)
  let locals := ((cmdVars body ++ res).dedup).filter fun v =>
    !pvs.contains v && !named.contains v.vname
  let fd : FunDecl := ⟨⟨fname⟩, ps.map (fun p => ⟨⟨p.1, vi0⟩⟩), body,
    res.map (fun v => ⟨v, vi0⟩)⟩
  { kind := .exportFn, fd := fd, paramTys := ps.map Prod.snd, resultTys := resTys,
    decls := arrDecls ++ locals.map (declOf []) }

/-- **The function of an orchestration body.** An array result is the `reg mut ptr`
parameter `out` (a `reg u64` address in `memPtr`), placed first and returned; the inputs
follow as `reg ptr` parameters (`reg u64` in `memPtr`). Outside `memPtr` the array inputs
are copied into owned buffers before the body and the result is copied into `out` after
it; in `memPtr` the result must be `out` itself. A scalar result is moved to the register
`mkV 'o' 0` and returned. -/
def orchFn (m : OrchMode) (name : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) : Option JazzFn :=
  let outV : Option JVar :=
    if isArrTy t then some (mkV 'o' 0 (m.slot (.regPtr true) t).2.toSType) else none
  let ps := (outV.map fun o => (o, m.slot (.regPtr true) t)).toList ++
    Γ.mapIdx fun i ty => (inVar m i ty, m.slot (.regPtr false) ty)
  (orchBody m outV (Γ.mapIdx (envVar m)) com 0).bind fun r =>
    let pre := (Γ.mapIdx (copyIn m)).flatten
    let arrDecls := (Γ.mapIdx (ownDecl m)).flatten ++ r.2.1
    match outV with
    | some o =>
        let post? : Option Cmd :=
          if m == .memPtr then (if r.2.2 == o then some [] else none)
          else some (arrCopyLoop o r.2.2 t)
        post?.map fun post =>
          orchFnOf name ps (pre ++ r.1 ++ post) arrDecls [o] [m.slot (.regPtr true) t]
    | none =>
        let rr := mkV 'o' 0 (styOf t)
        some (orchFnOf name ps (pre ++ r.1 ++ [asgn rr (pv r.2.2)]) arrDecls [rr]
          [(.reg, ptyOf t)])

/-- **The unit of an orchestration body**: the function `orchFn` with the `require` lines
`requires`, and the extern signature `leafExtern m` of each leaf of `leaves`. `none` when
the body is refused or the unit is not well formed, in particular when a called leaf is
not in `leaves`. -/
def orchUnit (m : OrchMode) (name : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (leaves : List (String × List JasminTy × JasminTy))
    (requires : List String := []) : Option JazzUnit :=
  (orchFn m name com).bind fun f =>
    let u : JazzUnit :=
      { externs := leaves.map (leafExtern m), fns := [{ f with requires := requires }] }
    if u.wellFormedB then some u else none

/-! ## 4. Text -/

/-- The text of an orchestration body: `orchUnit` followed by the checked printer. -/
def emitAbiOrchJ (m : OrchMode) (name : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (leaves : List (String × List JasminTy × JasminTy))
    (requires : List String := []) : Option String :=
  (orchUnit m name com leaves requires).bind CatCrypt.Crypto.Jasmin.Jazz.printChecked

/-- **A returned text parses to the unit**: to the erasure of the unit `orchUnit` builds. -/
theorem emitAbiOrchJ_parse {m : OrchMode} {name : String} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t}
    {leaves : List (String × List JasminTy × JasminTy)} {requires : List String} {s : String}
    (h : emitAbiOrchJ m name com leaves requires = some s) :
    ∃ u, orchUnit m name com leaves requires = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok u.erase := by
  obtain ⟨u, hu, hs⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨u, hu, (CatCrypt.Crypto.Jasmin.Jazz.printChecked_sound hs).2⟩

/-- The text of a register-arithmetic program as the `export fn` `name` with the signature
`sig`: `emitJazzN`. -/
def emitAbiOrchRegJ {Γ : Ctxt jasminDialect} {t : JasminTy} (name : String)
    (sig : JazzSig Γ t) (com : Com jasminDialect Γ t) : Option String :=
  JasminPrintText.emitJazzN name sig com

/-- **A returned text of a register-arithmetic program parses to the lowered unit** without
its extern signatures. -/
theorem emitAbiOrchRegJ_parse {Γ : Ctxt jasminDialect} {t : JasminTy} {name : String}
    {sig : JazzSig Γ t} {com : Com jasminDialect Γ t} {s : String}
    (h : emitAbiOrchRegJ name sig com = some s) :
    ∃ u, nfToJasmin sig name (NFProg.ofCom com) = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok { u with externs := [] } :=
  JasminPrintText.emitJazzN_parse h

/-! ## 5. Checks -/

/-- The leaf `safegcd_bn254_invert` of the BN254 field inversion: four `u64` limbs to four
`u64` limbs. -/
def safegcdLeaf : String × List JasminTy × JasminTy :=
  ("safegcd_bn254_invert", [.stackArr 64 4], .stackArr 64 4)

/-- The orchestration body of the BN254 field inversion driver
(`bench/bn254_safegcd_compare`): one call of `safegcd_bn254_invert` on the input. -/
def safegcdOrch : Com jasminDialect [.stackArr 64 4] (.stackArr 64 4) :=
  .var ⟨.extCall "safegcd_bn254_invert" [.stackArr 64 4] (.stackArr 64 4), rfl,
    .cons .here .nil⟩ (.ret .here)

-- The BN254 inversion body prints through the checked printer in the `regPtr` mode.
#kat (emitAbiOrchJ .regPtr "bn254_safegcd_invert_rustcmd" safegcdOrch [safegcdLeaf]).isSome

-- In the `regPtr` mode the inversion leaf takes its result buffer as `reg mut ptr` and its
-- input as `reg ptr`, and returns the result buffer.
#kat leafExtern .regPtr safegcdLeaf ==
  { name := "safegcd_bn254_invert"
    params := [(.regPtr true, .arr .U64 4), (.regPtr false, .arr .U64 4)]
    results := [(.regPtr true, .arr .U64 4)] }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiJazz
