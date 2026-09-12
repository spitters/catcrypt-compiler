/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx

/-!
# The extended `JasminAST → CoqSemMirror` translation

`InstrRTranslate.translateInstrR` translates the register-word `Cassgn` fragment
and maps every other instruction to `none`. `translateInstrRExt` translates, in
addition, the other shapes `JasminPrint.lowerExpr` emits: the rotate `Copn`, the
counted `Cfor` of `JForProg`, the leaf `Ccall`, the register-index array read
`Pget` and the array write `Laset`. It agrees with `translateInstrR` wherever
that is defined (`translateInstrRExt_of_translateInstrR`).

## Translation choices

* A JasminAST array type `sarr n` counts bytes; it translates to the mirror byte
  array `aarr U8 n`.
* An array index that is a `u64` register `Pvar idx` translates to
  `Papp1 (Oint_of_word Unsigned U64) (Pvar idx)`, the explicit conversion
  Jasmin's type checker inserts (`ComJasminBridgeArrIdx.idxExpr`).
* The JasminAST `Pget`/`Laset` carry no alignment; the mirror image is `Unaligned`.
* A `Cfor` range bound `n : Nat` translates to `Pconst n`.

## Image theorems

One theorem per emitted shape states that its image is exactly the mirror form
the corresponding bridge arm is stated over: `translateInstrRExt_ror`
(`rorLvals`/`rorArgs`), `translateInstrRExt_cfor` (`forRange`, and `forInstr` for
a mixed-block body), `translateInstrRExt_ccall` (`callInstr`),
`translateInstrRExt_pget` and `translateInstrRExt_laset` (`idxExpr`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate

/-! ## §1. Types, variables and indices -/

/-- `translateSType` extended by byte arrays: `sarr n` becomes `aarr U8 n`. -/
def translateSTypeExt : ASType → Option MAtype
  | .sarr n => some (.aarr .U8 n)
  | t => translateSType t

/-- `translateVar` over `translateSTypeExt`. -/
def translateVarExt (v : AVar) : Option MVar :=
  (translateSTypeExt v.vtype).map (fun t => { vname := v.vname, vtype := t })

/-- `translateVarI` over `translateSTypeExt`. -/
def translateVarIExt (x : AVarI) : Option MVarI :=
  (translateVarExt x.var).map (fun v => { v_var := v })

/-- `translateGVar` over `translateSTypeExt`. -/
def translateGVarExt (g : AGVar) : Option MGVar :=
  (translateVarIExt g.gv).map (fun v => { gv := v, gs := if g.gs then .Sglob else .Slocal })

/-- The array access mode, constructor for constructor. -/
def translateArrAccess : CatCrypt.Crypto.Jasmin.ArrAccess → CatCrypt.Crypto.Jasmin.CoqSemMirror.ArrAccess
  | .AAscale => .AAscale
  | .AAdirect => .AAdirect

/-- The loop direction, constructor for constructor. -/
def translateDir : CatCrypt.Crypto.Jasmin.LoopDir → CatCrypt.Crypto.Jasmin.CoqSemMirror.Dir
  | .UpTo => .UpTo
  | .DownTo => .DownTo

/-- An array index: a `u64` register read becomes its `int_of_word` conversion;
    any other index is translated by `translatePExpr`. -/
def translateIdx : APExpr → Option MPexpr
  | .Pvar g =>
      if g.gv.var.vtype = .sword .U64 then
        (translateGVarExt g).map (fun g' => .Papp1 (.Oint_of_word .Unsigned .U64) (.Pvar g'))
      else (translateGVarExt g).map .Pvar
  | e => translatePExpr e

/-! ## §2. Expressions and l-values -/

/-- `translatePExpr` extended by variables of array type and by the array read
    `Pget`. -/
def translatePExprExt : APExpr → Option MPexpr
  | .Pvar g => (translateGVarExt g).map .Pvar
  | .Pget aa ws x idx =>
      match translateWSize ws, translateGVarExt x, translateIdx idx with
      | some ws', some x', some i' => some (.Pget .Unaligned (translateArrAccess aa) ws' x' i')
      | _, _, _ => none
  | e => translatePExpr e

/-- `translateLVal` extended by the discarded l-value `Lnone`, variables of array
    type, and the array write `Laset`. -/
def translateLValExt : ALVal → Option MLval
  | .Lnone _ ty => (translateSTypeExt ty).map (.Lnone ())
  | .Lvar x => (translateVarIExt x).map .Lvar
  | .Laset aa ws x idx =>
      match translateWSize ws, translateVarIExt x, translateIdx idx with
      | some ws', some x', some i' => some (.Laset .Unaligned (translateArrAccess aa) ws' x' i')
      | _, _, _ => none
  | _ => none

/-! ## §3. Instructions -/

mutual
/-- **The extended translation.** `Cassgn` over the extended l-values and
    expressions, `Copn` of an asm op, `Cfor` with constant bounds, and `Ccall`;
    `Cif`/`Cwhile` translate to `none`. -/
def translateInstrRExt : AInstrR → Option MInstrR
  | .Cassgn lv tag ty e =>
      match translateLValExt lv, translateSTypeExt ty, translatePExprExt e with
      | some lv', some ty', some e' => some (.Cassgn lv' (translateAssgnTag tag) ty' e')
      | _, _, _ => none
  | .Copn lvs tag (.Oasm op) es =>
      match lvs.mapM translateLValExt, es.mapM translatePExprExt with
      | some lvs', some es' => some (.Copn lvs' (translateAssgnTag tag) (.Oasm op.name) es')
      | _, _ => none
  | .Cfor v r body =>
      match translateVarIExt v, translateCmdExt body with
      | some v', some body' =>
          some (.Cfor v' { dir := translateDir r.dir, lo := .Pconst r.lo, hi := .Pconst r.hi } body')
      | _, _ => none
  | .Ccall _ lvs fn args =>
      match lvs.mapM translateLValExt, args.mapM translatePExprExt with
      | some lvs', some args' => some (.Ccall lvs' { name := fn.name } args')
      | _, _ => none
  | _ => none

/-- The extended translation of a command, each instruction annotated `MkI ()`. -/
def translateCmdExt : List AInstrR → Option (List MInstr)
  | [] => some []
  | i :: c =>
      match translateInstrRExt i, translateCmdExt c with
      | some i', some c' => some (.MkI () i' :: c')
      | _, _ => none
end

/-! ## §4. Agreement with `translateInstrR` -/

/-- `translateSTypeExt` agrees with `translateSType` where that is defined. -/
theorem translateSTypeExt_of (t : ASType) (t' : MAtype) (h : translateSType t = some t') :
    translateSTypeExt t = some t' := by
  cases t <;> first | exact h | (simp [translateSType] at h)

/-- `translateVarIExt` agrees with `translateVarI` where that is defined. -/
theorem translateVarIExt_of (x : AVarI) (x' : MVarI) (h : translateVarI x = some x') :
    translateVarIExt x = some x' := by
  unfold translateVarI translateVar at h
  unfold translateVarIExt translateVarExt
  cases ht : translateSType x.var.vtype with
  | none => simp [ht] at h
  | some t => simpa [translateSTypeExt_of _ _ ht, ht] using h

/-- `translateGVarExt` agrees with `translateGVar` where that is defined. -/
theorem translateGVarExt_of (g : AGVar) (g' : MGVar) (h : translateGVar g = some g') :
    translateGVarExt g = some g' := by
  unfold translateGVar at h
  unfold translateGVarExt
  cases hv : translateVarI g.gv with
  | none => simp [hv] at h
  | some v => simpa [translateVarIExt_of _ _ hv, hv] using h

/-- `translatePExprExt` agrees with `translatePExpr` where that is defined. -/
theorem translatePExprExt_of (e : APExpr) (e' : MPexpr) (h : translatePExpr e = some e') :
    translatePExprExt e = some e' := by
  cases e with
  | Pvar g =>
    simp only [translatePExpr] at h
    simp only [translatePExprExt]
    cases hg : translateGVar g with
    | none => simp [hg] at h
    | some g₁ => simpa [translateGVarExt_of _ _ hg, hg] using h
  | Pget aa ws x idx => simp [translatePExpr] at h
  | _ => exact h

/-- **Extension.** `translateInstrRExt` agrees with `translateInstrR` wherever
    `translateInstrR` is defined. -/
theorem translateInstrRExt_of_translateInstrR (i : AInstrR) (j : MInstrR)
    (h : translateInstrR i = some j) : translateInstrRExt i = some j := by
  cases i with
  | Cassgn lv tag ty e =>
    simp only [translateInstrR] at h
    cases hl : translateLVal lv with
    | none => simp [hl] at h
    | some lv' =>
      cases ht : translateSType ty with
      | none => simp [hl, ht] at h
      | some ty' =>
        cases he : translatePExpr e with
        | none => simp [hl, ht, he] at h
        | some e' =>
          simp only [hl, ht, he] at h
          have hl' : translateLValExt lv = some lv' := by
            cases lv with
            | Lvar x =>
              simp only [translateLVal] at hl
              cases hx : translateVarI x with
              | none => simp [hx] at hl
              | some x' => simpa [translateLValExt, translateVarIExt_of _ _ hx, hx] using hl
            | _ => simp [translateLVal] at hl
          simp only [translateInstrRExt, hl', translateSTypeExt_of _ _ ht,
            translatePExprExt_of _ _ he]
          exact h
  | _ => simp [translateInstrR] at h

/-! ## §5. Image theorems -/

open CatCrypt.Crypto.Jasmin.CoqSemMirror (mkLvar)
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCopn
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeFor
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeCall
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeArrIdx

/-- A local variable read translates to the mirror local read `mkLvar`. -/
theorem translatePExprExt_pvar_local (x : AVarI) (x' : MVarI)
    (hx : translateVarIExt x = some x') :
    translatePExprExt (.Pvar { gv := x, gs := false }) = some (.Pvar (mkLvar x')) := by
  simp [translatePExprExt, translateGVarExt, hx, mkLvar]

/-- A local `u64` index register translates to `idxExpr`. -/
theorem translateIdx_u64 (x : AVarI) (x' : MVarI) (hty : x.var.vtype = .sword .U64)
    (hx : translateVarIExt x = some x') :
    translateIdx (.Pvar { gv := x, gs := false }) = some (idxExpr x') := by
  simp [translateIdx, translateGVarExt, hx, hty, idxExpr, mkLvar]

/-- **Rotate image.** The emitted rotate
    `Copn [Lnone _ bool, Lnone _ bool, Lvar dst] tag (Oasm ROR_sz) [Pvar src, Pconst n]`
    translates to `Copn (rorLvals dst') tag' (Oasm (rorOpName sz)) (rorArgs src' n)`. -/
theorem translateInstrRExt_ror (dst src : AVarI) (dst' src' : MVarI) (tag : AAssgnTag)
    (info₁ info₂ : CatCrypt.Crypto.Jasmin.VarInfo) (sz : MWSize) (n : Nat)
    (hdst : translateVarIExt dst = some dst') (hsrc : translateVarIExt src = some src') :
    translateInstrRExt
        (.Copn [.Lnone info₁ .sbool, .Lnone info₂ .sbool, .Lvar dst] tag
          (.Oasm { name := rorOpName sz })
          [.Pvar { gv := src, gs := false }, .Pconst (Int.ofNat n)])
      = some (.Copn (rorLvals dst') (translateAssgnTag tag) (.Oasm (rorOpName sz))
          (rorArgs src' n)) := by
  simp [translateInstrRExt, translateLValExt, translateSTypeExt, translateSType, hdst,
    translatePExprExt, translatePExpr, translateGVarExt, hsrc, mkLvar,
    rorLvals, rorArgs, List.mapM_cons, List.mapM_nil]

/-- **Counted-loop image.** `Cfor v (UpTo, 0, n) body` translates to
    `Cfor v' (forRange n) body'` when the body translates to `body'`. -/
theorem translateInstrRExt_cfor (v : AVarI) (v' : MVarI) (n : Nat)
    (body : List AInstrR) (body' : List MInstr)
    (hv : translateVarIExt v = some v') (hbody : translateCmdExt body = some body') :
    translateInstrRExt (.Cfor v { dir := .UpTo, lo := 0, hi := n } body)
      = some (.Cfor v' (forRange n) body') := by
  simp [translateInstrRExt, hv, hbody, forRange, translateDir]

/-- The counted-loop image is `forInstr` when the translated body is the emitted
    command of a mixed block. -/
theorem translateInstrRExt_cfor_forInstr (v : AVarI) (v' : MVarI) (n : Nat)
    (body : List AInstrR) (steps : List MixedStep)
    (hv : translateVarIExt v = some v') (hbody : translateCmdExt body = some (mixedBlockCmd steps)) :
    translateInstrRExt (.Cfor v { dir := .UpTo, lo := 0, hi := n } body)
      = some (forInstr v' n steps) :=
  translateInstrRExt_cfor v v' n body _ hv hbody

/-- **Leaf-call image.** `Ccall ii [Lvar dst] fn (map Pvar gs)` over local
    argument registers `gs` translates to `callInstr dst' fn' args`, where
    each `g` in `gs` translates to the source register of the matching `args`
    entry. -/
theorem translateInstrRExt_ccall (ii : CatCrypt.Crypto.Jasmin.InlineInfo)
    (dst : AVarI) (dst' : MVarI) (fn : CatCrypt.Crypto.Jasmin.FunName)
    (gs : List AVarI) (args : List CallArg)
    (hdst : translateVarIExt dst = some dst')
    (hargs : List.Forall₂ (fun g a => translateVarIExt g = some a.src) gs args) :
    translateInstrRExt
        (.Ccall ii [.Lvar dst] fn (gs.map (fun g => .Pvar { gv := g, gs := false })))
      = some (callInstr dst' { name := fn.name } args) := by
  have hmap : (gs.map (fun g => (CatCrypt.Crypto.Jasmin.PExpr.Pvar { gv := g, gs := false }))).mapM
      translatePExprExt = some (args.map CallArg.expr) := by
    induction hargs with
    | nil => rfl
    | cons hga _ ih =>
      rw [List.map_cons, List.mapM_cons, translatePExprExt_pvar_local _ _ hga, ih]
      rfl
  simp only [translateInstrRExt]
  rw [hmap]
  simp [translateLValExt, hdst, callInstr]

/-- **Array-read image.** The emitted read
    `Cassgn (Lvar dst) tag (sword U8) (Pget aa ws arr (Pvar idx))` over a local
    array `arr` and a local `u64` index register `idx` translates to
    `Cassgn (Lvar dst') tag' (aword U8) (Pget Unaligned aa' ws' (mkLvar arr') (idxExpr idx'))`. -/
theorem translateInstrRExt_pget (dst arr idx : AVarI) (dst' arr' idx' : MVarI)
    (tag : AAssgnTag) (aa : CatCrypt.Crypto.Jasmin.ArrAccess) (ws : AWSize) (ws' : MWSize)
    (hdst : translateVarIExt dst = some dst') (harr : translateVarIExt arr = some arr')
    (hidx : translateVarIExt idx = some idx') (hty : idx.var.vtype = .sword .U64)
    (hws : translateWSize ws = some ws') :
    translateInstrRExt
        (.Cassgn (.Lvar dst) tag (.sword .U8)
          (.Pget aa ws { gv := arr, gs := false } (.Pvar { gv := idx, gs := false })))
      = some (.Cassgn (.Lvar dst') (translateAssgnTag tag) (.aword .U8)
          (.Pget .Unaligned (translateArrAccess aa) ws' (mkLvar arr') (idxExpr idx'))) := by
  simp [translateInstrRExt, translateLValExt, translateSTypeExt, translateSType, hdst,
    translatePExprExt, hws, translateGVarExt, harr, translateIdx_u64 idx idx' hty hidx,
    mkLvar]
  rfl

/-- **Array-write image.** The emitted write
    `Cassgn (Laset aa U8 arr (Pvar idx)) tag (sword U8) (Pvar src)` over a local
    `u64` index register `idx` and a local source `src` translates to
    `Cassgn (Laset Unaligned aa' U8 arr' (idxExpr idx')) tag' (aword U8) (Pvar (mkLvar src'))`. -/
theorem translateInstrRExt_laset (arr idx src : AVarI) (arr' idx' src' : MVarI)
    (tag : AAssgnTag) (aa : CatCrypt.Crypto.Jasmin.ArrAccess)
    (harr : translateVarIExt arr = some arr') (hidx : translateVarIExt idx = some idx')
    (hty : idx.var.vtype = .sword .U64) (hsrc : translateVarIExt src = some src') :
    translateInstrRExt
        (.Cassgn (.Laset aa .U8 arr (.Pvar { gv := idx, gs := false })) tag (.sword .U8)
          (.Pvar { gv := src, gs := false }))
      = some (.Cassgn (.Laset .Unaligned (translateArrAccess aa) .U8 arr' (idxExpr idx'))
          (translateAssgnTag tag) (.aword .U8) (.Pvar (mkLvar src'))) := by
  simp [translateInstrRExt, translateLValExt, translateSTypeExt, translateSType, harr,
    translateIdx_u64 idx idx' hty hidx, translatePExprExt_pvar_local src src' hsrc,
    translateWSize]

end CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
