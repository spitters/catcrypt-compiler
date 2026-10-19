/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.Jasmin.JazzToInstrRFacts

/-!
# Jasmin compilation units in the `CoqSemMirror` syntax

`translateFn` translates a function `JazzFn` of a Jasmin compilation unit to a function
declaration of the `psem.v` mirror by `InstrRTranslateExt`: the parameters and results by
`translateVarIExt`, the body by `translateCmdExt` followed by the typing `typeC`, the
parameter and result types read off the translated variables. `translateUnit` translates the
functions of a unit to a mirror program `Prog` without globals; the extern signatures of a
unit declare linked callees and contribute no function to the program.

The typing `typeC` writes each integer constant in word position as jasminc's typing does,
`Papp1 (Oword_of_int ws) (Pconst z)`: the right-hand side of an assignment at the assigned
word type, the operands of a word operator, a shift count at `u8`, and the operands of an
asm operation at the operand types `jazzArgTys` of `JazzAsmSem`. The typing acts on the
mirror program; the Jasmin unit and its printed text do not contain the casts.

The image theorems state, for each instruction shape of the op table of `nfToJasmin`, the
mirror command `translateCmdExt` returns, over the mirror builders `mpv` (a local read),
`masgn` (an assignment at the type of its target) and `mcopn` (an asm operation without
tag), in the manner of `InstrRTranslateExt.translateInstrRExt_ccall`; `typeC_mkCmd`,
`typeI_cinCode` and `typeI_masgn_const` give their typed form.

## Main definitions

* `typeE`, `typeI`, `typeC`: the typing of constants in word position.
* `translateFn`, `translateUnit`: the translation of a function and of a unit.
* `mpv`, `masgn`, `mcopn`, `mkCmd`, `mcf`: the mirror builders.

## Main results

* `translateUnit_mkUnit`, `translateFn_eq_some`: the translation of the unit of one
  function, and of a function whose parameters, body and results translate.
* `translateCmdExt_append_eq_some`, `translateCmdExt_seqMoves`: concatenation and sequential moves.
* Image theorems: `translateInstrRExt_cinCode` and `translateCmdExt_matCF` (the carry flag),
  `translateCmdExt_addCarryLo` (the carry pair `ADD_64`/`ADC_64`), `translateCmdExt_cmpCode`
  (the comparison idiom over `NEG_64`/`CMP_64`), `translateCmdExt_select` (the mask select),
  `translateCmdExt_mulhi` (`MULX_lo_hi_64`), `translateCmdExt_forCode` (the counter `while`
  frame), `translateCmdExt_whileCode` (the exit-flag `while`), `translateInstrRExt_ifCode` (the
  branch with its join moves), `translateInstrRExt_call` (a call with several results),
  `translateCmdExt_stackLoad` and `translateCmdExt_stackStore` (the `(uint) e` index), and
  `translateCmdExt_sarImm` (the arithmetic shift by `sarCount`).
* `translateUnit_isSome_of_nfToJasmin`: every unit `nfToJasmin` returns translates. The
  lowering refuses a 512-bit word (`jasminWidthsB`), and every variable, operation and `_`
  output of the lowered code then has one of the six word sizes of the mirror
  (`body_trC`, `emitOp_trC`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.Jasmin.CoqSemMirror (mkLvar OpKind CmpKind Sopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (jazzArgTys)
open CatCrypt.Crypto.Jasmin.JazzToInstrR (opnNoneTys opnNoneTys_ADD_64 opnNoneTys_ADC_64
  opnNoneTys_NEG_64 opnNoneTys_CMP_64 opnNoneTys_MULX_64)

/-- A mirror function name. -/
abbrev MFunName := CatCrypt.Crypto.Jasmin.CoqSemMirror.FunName

/-- A mirror function definition. -/
abbrev MFunDef := CatCrypt.Crypto.Jasmin.CoqSemMirror.FunDef

/-- A mirror program. -/
abbrev MProg := CatCrypt.Crypto.Jasmin.CoqSemMirror.Prog

/-! ## 1. Constants in word position -/

/-- The operand type of an operation of kind `k`. -/
def kindTy : OpKind → MAtype
  | .Op_int => .aint
  | .Op_w ws => .aword ws

/-- The type of the count of a shift of kind `k`: `u8` for a word shift. -/
def countTy : OpKind → MAtype
  | .Op_int => .aint
  | .Op_w _ => .aword .U8

/-- The operand type of a comparison of kind `k`. -/
def cmpTy : CmpKind → MAtype
  | .Cmp_int => .aint
  | .Cmp_w _ ws => .aword ws

/-- The operand type of a unary operator (`type_of_op1` of `sem_op_typed.v`). -/
def op1Ty : MSOp1 → MAtype
  | .Oword_of_int _ => .aint
  | .Oint_of_word _ ws => .aword ws
  | .Osignext _ wsi => .aword wsi
  | .Ozeroext _ wsi => .aword wsi
  | .Onot => .abool
  | .Olnot ws => .aword ws
  | .Oneg k => kindTy k

/-- The operand types of a binary operator (`type_of_op2` of `sem_op_typed.v`): a shift
count is a `u8`. -/
def op2Tys : MSOp2 → MAtype × MAtype
  | .Obeq | .Oand | .Oor => (.abool, .abool)
  | .Oadd k | .Omul k | .Osub k | .Odiv _ k | .Omod _ k | .Oeq k | .Oneq k =>
      (kindTy k, kindTy k)
  | .Olsl k | .Oasr k => (kindTy k, countTy k)
  | .Oland ws | .Olor ws | .Olxor ws => (.aword ws, .aword ws)
  | .Olsr ws | .Oror ws | .Orol ws => (.aword ws, .aword .U8)
  | .Olt k | .Ole k | .Ogt k | .Oge k => (cmpTy k, cmpTy k)

/-- The integer constant `z` at the type `ty`: `Papp1 (Oword_of_int ws) (Pconst z)` at a word
type, as jasminc's typing writes an integer literal in word position, and `Pconst z`
otherwise. -/
def typeConst : MAtype → Int → MPexpr
  | .aword ws, z => .Papp1 (.Oword_of_int ws) (.Pconst z)
  | _, z => .Pconst z

/-- The typing of an expression at the type `ty`: each integer constant becomes `typeConst`
at the type of its position, the operand types of the operators, `int` for an array index
and `u64` for an address. -/
def typeE : MAtype → MPexpr → MPexpr
  | ty, .Pconst z => typeConst ty z
  | _, .Pget al aa ws x i => .Pget al aa ws x (typeE .aint i)
  | _, .Psub aa ws n x i => .Psub aa ws n x (typeE .aint i)
  | _, .Pload al ws e => .Pload al ws (typeE (.aword .U64) e)
  | _, .Papp1 op e => .Papp1 op (typeE (op1Ty op) e)
  | _, .Papp2 op a b => .Papp2 op (typeE (op2Tys op).1 a) (typeE (op2Tys op).2 b)
  | _, .Pif t c a b => .Pif t (typeE .abool c) (typeE t a) (typeE t b)
  | _, e => e

/-- The typing of an l-value: its index at `int`, its address at `u64`. -/
def typeLv : MLval → MLval
  | .Lmem al ws i e => .Lmem al ws i (typeE (.aword .U64) e)
  | .Laset al aa ws x i => .Laset al aa ws x (typeE .aint i)
  | .Lasub aa ws n x i => .Lasub aa ws n x (typeE .aint i)
  | lv => lv

/-- The typing of the operands `es` at the types `tys`, operands past the end of `tys`
unchanged. -/
def typeArgs : List MAtype → List MPexpr → List MPexpr
  | ty :: tys, e :: es => typeE ty e :: typeArgs tys es
  | _, es => es

/-- The operand types of an operator: those of `jazzArgTys` for an asm operation, none for
an operation outside it. -/
def sopnTys : Sopn → List MAtype
  | .Oasm o => (jazzArgTys o).getD []
  | .Oaddcarry ws | .Osubcarry ws => [.aword ws, .aword ws, .abool]
  | .Omulu ws => [.aword ws, .aword ws]
  | _ => []

mutual
/-- The typing of an instruction: the right-hand side of an assignment at the assigned
type, the operands of an operator at its operand types, and conditions at `bool`. -/
def typeI : MInstrR → MInstrR
  | .Cassgn lv tag ty e => .Cassgn (typeLv lv) tag ty (typeE ty e)
  | .Copn xs tag o es => .Copn (xs.map typeLv) tag o (typeArgs (sopnTys o) es)
  | .Cif c t e => .Cif (typeE .abool c) (typeC t) (typeC e)
  | .Cfor v r b => .Cfor v r (typeC b)
  | .Cwhile al b c ii a => .Cwhile al (typeC b) (typeE .abool c) ii (typeC a)
  | i => i

/-- The typing of a command: `typeI` at each instruction. -/
def typeC : List MInstr → List MInstr
  | [] => []
  | .MkI ii i :: c => .MkI ii (typeI i) :: typeC c
end

/-! ## 2. Functions and units -/

/-- The translation of a function: its name, the translated parameters with their types,
the typed translated body (`typeC`), and the translated results with their types. -/
def translateFn (f : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) : Option (MFunName × MFunDef) :=
  match f.fd.params.mapM (fun p => translateVarIExt p.var), translateCmdExt f.fd.body,
      f.fd.results.mapM translateVarIExt with
  | some ps, some body, some rs =>
      some ({ name := f.fd.name.name },
        { tyin := ps.map (·.v_var.vtype), params := ps, body := typeC body,
          tyout := rs.map (·.v_var.vtype), rets := rs })
  | _, _, _ => none

/-- The translation of a unit: the program of its translated functions, without globals. -/
def translateUnit (u : CatCrypt.Crypto.Jasmin.Jazz.JazzUnit) : Option MProg :=
  (u.fns.mapM translateFn).map fun fs => { pFuncs := fs, pGlobs := [] }

/-- A function translates when its parameters, body and results translate. -/
theorem translateFn_eq_some (f : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) {ps : List MVarI}
    {body : List MInstr} {rs : List MVarI}
    (hps : f.fd.params.mapM (fun p => translateVarIExt p.var) = some ps)
    (hb : translateCmdExt f.fd.body = some body)
    (hrs : f.fd.results.mapM translateVarIExt = some rs) :
    translateFn f = some ({ name := f.fd.name.name },
      { tyin := ps.map (·.v_var.vtype), params := ps, body := typeC body,
        tyout := rs.map (·.v_var.vtype), rets := rs }) := by
  simp [translateFn, hps, hb, hrs]

/-- The unit of one function translates to the program of that function. -/
theorem translateUnit_mkUnit (fn : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) (fd : MFunName × MFunDef)
    (h : translateFn fn = some fd) :
    translateUnit (mkUnit fn) = some { pFuncs := [fd], pGlobs := [] } := by
  simp [translateUnit, mkUnit, h]

/-! ## 3. Mirror builders -/

/-- The mirror read of a local variable. -/
def mpv (x : MVarI) : MPexpr := .Pvar (mkLvar x)

/-- The mirror assignment `x = e` at the type of `x`. -/
def masgn (x : MVarI) (e : MPexpr) : MInstrR := .Cassgn (.Lvar x) .AT_none x.v_var.vtype e

/-- The mirror asm operation `o` with the l-values `lvs` and the operands `es`. -/
def mcopn (o : String) (lvs : List MLval) (es : List MPexpr) : MInstrR :=
  .Copn lvs .AT_none (.Oasm o) es

/-- A mirror command of instructions, each annotated `MkI ()`. -/
def mkCmd (c : List MInstrR) : List MInstr := c.map (.MkI ())

/-- The mirror carry flag `cf`. -/
def mcf : MVarI := { v_var := { vtype := .abool, vname := "cf" } }

/-- A discarded Boolean output. -/
def mnb : MLval := .Lnone () .abool

/-- The `b5w_ty` outputs with the carry flag and the word `x`. -/
def mCWOuts (x : MVarI) : List MLval := [mnb, .Lvar mcf, mnb, mnb, mnb, .Lvar x]

/-- The `b5w_ty` outputs with the word `x` only. -/
def mWOuts (x : MVarI) : List MLval := [mnb, mnb, mnb, mnb, mnb, .Lvar x]

/-- The mirror condition `v != 0`. -/
def mnz (v : MVarI) : MPexpr := .Papp2 (.Oneq (.Op_w .U64)) (mpv v) (.Pconst 0)

/-! ## 4. Variables, expressions and commands -/

/-- The variable of a translated local carries the translated type. -/
theorem translateSTypeExt_of_var {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateSTypeExt x.vtype = some x'.v_var.vtype := by
  unfold translateVarIExt translateVarExt at hx
  cases ht : translateSTypeExt x.vtype with
  | none => simp [ht] at hx
  | some t =>
      simp only [ht, Option.map_some, Option.some.injEq] at hx
      subst hx; rfl

/-- The carry flag translates to `mcf`. -/
theorem translateVarIExt_cf : translateVarIExt ⟨cfVar, vi0⟩ = some mcf := rfl

/-- A local read translates to `mpv`. -/
theorem translatePExprExt_pv {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translatePExprExt (pv x) = some (mpv x') :=
  translatePExprExt_pvar_local _ _ hx

/-- An integer constant translates to itself. -/
theorem translatePExprExt_cnst (z : Int) : translatePExprExt (cnst z) = some (.Pconst z) := rfl

/-- The l-value of a local translates to the mirror `Lvar`. -/
theorem translateLValExt_lvv {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateLValExt (lvv x) = some (.Lvar x') := by
  simp [lvv, translateLValExt, hx]

/-- An assignment translates to `masgn`. -/
theorem translateInstrRExt_asgn {x : JVar} {x' : MVarI} {e : CatCrypt.Crypto.Jasmin.PExpr}
    {e' : MPexpr} (hx : translateVarIExt ⟨x, vi0⟩ = some x') (he : translatePExprExt e = some e') :
    translateInstrRExt (asgn x e) = some (masgn x' e') := by
  simp [asgn, translateInstrRExt, translateLValExt_lvv hx, translateSTypeExt_of_var hx, he,
    masgn, translateAssgnTag]

/-- A binary operation over translated operands. -/
theorem translatePExprExt_papp2 {op : ASOp2} {op' : MSOp2} {e1 e2 : APExpr} {e1' e2' : MPexpr}
    (ho : translateSOp2Ext op = some op') (h1 : translatePExprExt e1 = some e1')
    (h2 : translatePExprExt e2 = some e2') :
    translatePExprExt (.Papp2 op e1 e2) = some (.Papp2 op' e1' e2') := by
  simp [translatePExprExt, ho, h1, h2]

/-- A unary operation over a translated operand. -/
theorem translatePExprExt_papp1 {op : ASOp1} {op' : MSOp1} {e : APExpr} {e' : MPexpr}
    (ho : translateSOp1 op = some op') (h : translatePExprExt e = some e') :
    translatePExprExt (.Papp1 op e) = some (.Papp1 op' e') := by
  simp [translatePExprExt, ho, h]

/-- The translation of a command with a translated head. -/
theorem translateCmdExt_cons {i : AInstrR} {c : List AInstrR} {i' : MInstrR} {c' : List MInstr}
    (hi : translateInstrRExt i = some i') (hc : translateCmdExt c = some c') :
    translateCmdExt (i :: c) = some (.MkI () i' :: c') := by
  simp [translateCmdExt, hi, hc]

/-- The translation of a concatenation of translated commands. -/
theorem translateCmdExt_append_eq_some : ∀ {a b : List AInstrR} {a' b' : List MInstr},
    translateCmdExt a = some a' → translateCmdExt b = some b' →
    translateCmdExt (a ++ b) = some (a' ++ b')
  | [], _, a', _, ha, hb => by
      simp only [translateCmdExt, Option.some.injEq] at ha; subst ha; simpa using hb
  | i :: a, b, a', b', ha, hb => by
      simp only [translateCmdExt] at ha
      cases hi : translateInstrRExt i with
      | none => simp [hi] at ha
      | some i' =>
          cases hc : translateCmdExt a with
          | none => simp [hi, hc] at ha
          | some c' =>
              simp only [hi, hc, Option.some.injEq] at ha
              subst ha
              rw [List.cons_append, translateCmdExt_cons hi (translateCmdExt_append_eq_some hc hb)]
              rfl

/-- A command of assignments translates to `mkCmd` of their images. -/
theorem translateCmdExt_mkCmd : ∀ {c : List AInstrR} {c' : List MInstrR},
    List.Forall₂ (fun i i' => translateInstrRExt i = some i') c c' →
    translateCmdExt c = some (mkCmd c')
  | _, _, .nil => rfl
  | _, _, .cons h hs => translateCmdExt_cons h (translateCmdExt_mkCmd hs)

/-- **Sequential moves.** The moves `seqMoves ps` translate to the mirror assignments of
the translated pairs. -/
theorem translateCmdExt_seqMoves {ps : List (JVar × JVar)} {ps' : List (MVarI × MVarI)}
    (h : List.Forall₂ (fun p p' => translateVarIExt ⟨p.1, vi0⟩ = some p'.1 ∧
      translateVarIExt ⟨p.2, vi0⟩ = some p'.2) ps ps') :
    translateCmdExt (seqMoves ps) = some (mkCmd (ps'.map fun p => masgn p.1 (mpv p.2))) := by
  apply translateCmdExt_mkCmd
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
      exact .cons (translateInstrRExt_asgn hp.1 (translatePExprExt_pv hp.2)) ih

/-! ## 5. Image theorems of the op table -/

/-- A discarded Boolean output translates to `mnb`. -/
theorem translateLValExt_lnone_bool :
    translateLValExt (.Lnone vi0 .sbool) = some mnb := rfl

/-- A discarded `u64` output translates to the discarded mirror word. -/
theorem translateLValExt_lnone_u64 :
    translateLValExt (.Lnone vi0 (.sword .U64)) = some (.Lnone () (.aword .U64)) := rfl

/-- The 64-bit names of the asm operations of the op table. -/
theorem asmName_U64 :
    asmName "ADC" .U64 = "ADC_64" ∧ asmName "NEG" .U64 = "NEG_64" ∧
      asmName "CMP" .U64 = "CMP_64" ∧ asmName "MULX_lo_hi" .U64 = "MULX_lo_hi_64" := by
  simp [asmName, CatCrypt.Crypto.Jasmin.WSize.bits, Nat.repr_of_ge, Nat.repr_of_lt,
    Nat.digitChar_eq_six.mpr rfl, Nat.digitChar_eq_four.mpr rfl]

/-- The l-values of translated locals. -/
theorem mapM_lvv {xs : List JVar} {xs' : List MVarI}
    (h : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs') :
    (xs.map lvv).mapM translateLValExt = some (xs'.map .Lvar) := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [List.mapM_cons, translateLValExt_lvv hx, ih]

/-- The reads of translated locals. -/
theorem mapM_pv {xs : List JVar} {xs' : List MVarI}
    (h : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs') :
    (xs.map pv).mapM translatePExprExt = some (xs'.map mpv) := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [List.mapM_cons, translatePExprExt_pv hx, ih]

/-- An asm operation with the `b5w_ty` outputs of the carry flag and the word `x`, for an
operation whose `_` outputs are five flags and a word. -/
theorem translateInstrRExt_copnCW {o : String} {x : JVar} {x' : MVarI}
    {es : List CatCrypt.Crypto.Jasmin.PExpr} {es' : List MPexpr}
    (ho : opnNoneTys o 6 = List.replicate 5 .sbool ++ [.sword .U64])
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hes : es.mapM translatePExprExt = some es') :
    translateInstrRExt (copn o (outsCW x) es) = some (mcopn o (mCWOuts x') es') := by
  have hl : (outsCW x).length = 6 := rfl
  simp only [copn, hl, ho]
  simp only [outsCW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv hx, translateLValExt_lvv translateVarIExt_cf, hes]
  rfl

/-- An asm operation with the `b5w_ty` outputs of the word `x` only. -/
theorem translateInstrRExt_copnW {o : String} {x : JVar} {x' : MVarI}
    {es : List CatCrypt.Crypto.Jasmin.PExpr} {es' : List MPexpr}
    (ho : opnNoneTys o 6 = List.replicate 5 .sbool ++ [.sword .U64])
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hes : es.mapM translatePExprExt = some es') :
    translateInstrRExt (copn o (outsW x) es) = some (mcopn o (mWOuts x') es') := by
  have hl : (outsW x).length = 6 := rfl
  simp only [copn, hl, ho]
  simp only [outsW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv hx, hes]
  rfl

/-- **Carry-in image.** `#ADD_64(cin, -1)` into the scratch word `t0`. -/
theorem translateInstrRExt_cinCode {cin : JVar} {cin' t0' : MVarI}
    (hcin : translateVarIExt ⟨cin, vi0⟩ = some cin')
    (ht0 : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t0') :
    translateInstrRExt (cinCode cin) =
      some (mcopn "ADD_64" (mCWOuts t0') [mpv cin', .Pconst (-1)]) :=
  translateInstrRExt_copnCW opnNoneTys_ADD_64 ht0
    (by simp [List.mapM_cons, translatePExprExt_pv hcin, translatePExprExt_cnst])

/-- **Carry materialisation image.** `x = 0; #ADC_64(x, x, cf)`. -/
theorem translateCmdExt_matCF {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateCmdExt (matCF x) = some (mkCmd [masgn x' (.Pconst 0),
      mcopn "ADC_64" (mWOuts x') [mpv x', mpv x', mpv mcf]]) :=
  translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx (translatePExprExt_cnst 0))
    (.cons (translateInstrRExt_copnW opnNoneTys_ADC_64 hx
      (by simp [List.mapM_cons, translatePExprExt_pv hx,
        translatePExprExt_pv translateVarIExt_cf])) .nil))

/-- **Carry-pair image.** The binding of `addCarryLo 64` to `x` on `a`, `b` and the
carry-in word `cin`: `#ADD_64(cin, -1)`, `x = a`, `#ADC_64(x, b, cf)`. -/
theorem translateCmdExt_addCarryLo {d : Nat} {x a b cin : JVar} {x' a' b' cin' t0' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hb : translateVarIExt ⟨b, vi0⟩ = some b') (hcin : translateVarIExt ⟨cin, vi0⟩ = some cin')
    (ht0 : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t0') :
    (emitOp (.addCarryLo 64) d x [a, b, cin]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [mcopn "ADD_64" (mCWOuts t0') [mpv cin', .Pconst (-1)], masgn x' (mpv a'),
        mcopn "ADC_64" (mCWOuts x') [mpv x', mpv b', mpv mcf]]) := by
  have he : emitOp (.addCarryLo 64) d x [a, b, cin] =
      some ([cinCode cin, asgn x (pv a),
        copn (asmName "ADC" .U64) (outsCW x) [pv x, pv b, pv cfVar]], x) := rfl
  have hn : asmName "ADC" .U64 = "ADC_64" := asmName_U64.1
  rw [he, Option.bind_some, hn]
  exact translateCmdExt_mkCmd (.cons (translateInstrRExt_cinCode hcin ht0)
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
      (.cons (translateInstrRExt_copnCW opnNoneTys_ADC_64 hx
        (by simp [List.mapM_cons, translatePExprExt_pv hx, translatePExprExt_pv hb,
          translatePExprExt_pv translateVarIExt_cf])) .nil)))

/-- The mirror comparison idiom at `u64`, with the scratch words `t`, `t'`: the carry of
`#NEG_64(a ^ b)` (`eq`, `ne`) or of `#CMP_64` (orderings), materialised by `#ADC_64` and
flipped by `^ 1` for the complemented codes. -/
def mcmpCode (c : JasminDialect.JasminCmp) (t t' x : MVarI) (ea eb : MPexpr) :
    List MInstrR :=
  let neq := [masgn t ea, masgn t (.Papp2 (.Olxor .U64) (mpv t) eb),
    mcopn "NEG_64" (mCWOuts t) [mpv t]]
  let below (e1 e2 : MPexpr) := [masgn t e1, masgn t' e2,
    mcopn "CMP_64" [mnb, .Lvar mcf, mnb, mnb, mnb] [mpv t, mpv t']]
  let mat := [masgn x (.Pconst 0), mcopn "ADC_64" (mWOuts x) [mpv x, mpv x, mpv mcf]]
  let flip := [masgn x (.Papp2 (.Olxor .U64) (mpv x) (.Pconst 1))]
  match c with
  | .ne => neq ++ mat
  | .eq => neq ++ mat ++ flip
  | .ult => below ea eb ++ mat
  | .uge => below ea eb ++ mat ++ flip
  | .ugt => below eb ea ++ mat
  | .ule => below eb ea ++ mat ++ flip

/-- **Comparison image.** The comparison idiom `cmpCode c U64 x ea eb` translates to
`mcmpCode c`. -/
theorem translateCmdExt_cmpCode (c : JasminDialect.JasminCmp) {x : JVar}
    {ea eb : CatCrypt.Crypto.Jasmin.PExpr} {x' t' t1' : MVarI} {ea' eb' : MPexpr}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x')
    (ht : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t')
    (ht1 : translateVarIExt ⟨tmp 1 .U64, vi0⟩ = some t1')
    (hea : translatePExprExt ea = some ea') (heb : translatePExprExt eb = some eb') :
    translateCmdExt (cmpCode c .U64 x ea eb) = some (mkCmd (mcmpCode c t' t1' x' ea' eb')) := by
  have hneq : translateCmdExt [asgn (tmp 0 .U64) ea,
      asgn (tmp 0 .U64) (.Papp2 (.Olxor .U64) (pv (tmp 0 .U64)) eb),
      copn "NEG_64" (outsCW (tmp 0 .U64)) [pv (tmp 0 .U64)]] =
      some (mkCmd [masgn t' ea', masgn t' (.Papp2 (.Olxor .U64) (mpv t') eb'),
        mcopn "NEG_64" (mCWOuts t') [mpv t']]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn ht hea)
      (.cons (translateInstrRExt_asgn ht
        (translatePExprExt_papp2 rfl (translatePExprExt_pv ht) heb))
        (.cons (translateInstrRExt_copnCW opnNoneTys_NEG_64 ht
          (by simp [List.mapM_cons, translatePExprExt_pv ht])) .nil)))
  have hbelow : ∀ {e1 e2 : CatCrypt.Crypto.Jasmin.PExpr} {e1' e2' : MPexpr},
      translatePExprExt e1 = some e1' → translatePExprExt e2 = some e2' →
      translateCmdExt [asgn (tmp 0 .U64) e1, asgn (tmp 1 .U64) e2,
        copn "CMP_64" [none, some cfVar, none, none, none]
          [pv (tmp 0 .U64), pv (tmp 1 .U64)]] =
      some (mkCmd [masgn t' e1', masgn t1' e2',
        mcopn "CMP_64" [mnb, .Lvar mcf, mnb, mnb, mnb] [mpv t', mpv t1']]) := by
    intro e1 e2 e1' e2' h1 h2
    refine translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn ht h1)
      (.cons (translateInstrRExt_asgn ht1 h2) (.cons ?_ .nil)))
    have hl : ([none, some cfVar, none, none, none] : List (Option JVar)).length = 5 := rfl
    simp only [copn, hl, opnNoneTys_CMP_64]
    simp only [outLvs, List.replicate, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
      translateLValExt_lvv translateVarIExt_cf, translatePExprExt_pv ht,
      translatePExprExt_pv ht1]
    rfl
  have hflip : translateCmdExt [asgn x (.Papp2 (.Olxor .U64) (pv x) (cnst 1))] =
      some (mkCmd [masgn x' (.Papp2 (.Olxor .U64) (mpv x') (.Pconst 1))]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_cnst 1))) .nil)
  have hmat := translateCmdExt_matCF hx
  have hnN : asmName "NEG" .U64 = "NEG_64" := asmName_U64.2.1
  have hnC : asmName "CMP" .U64 = "CMP_64" := asmName_U64.2.2.1
  cases c <;> simp only [cmpCode, mcmpCode, mkCmd, List.map_append, hnN, hnC] <;>
    first
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hneq hmat) hflip
    | exact translateCmdExt_append_eq_some hneq hmat
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some (hbelow hea heb) hmat) hflip
    | exact translateCmdExt_append_eq_some (hbelow hea heb) hmat
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some (hbelow heb hea) hmat) hflip
    | exact translateCmdExt_append_eq_some (hbelow heb hea) hmat

/-- **Mask-select image.** The binding of `select 64` to `x` on the condition `c` and the
words `a`, `b`, with the mask in the scratch word `m`: `m = c; m = -m; x = a; x = x ^ b;
x = x & m; x = x ^ b`. -/
theorem translateCmdExt_select {d : Nat} {x c a b : JVar} {x' c' a' b' m' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hc : translateVarIExt ⟨c, vi0⟩ = some c')
    (ha : translateVarIExt ⟨a, vi0⟩ = some a') (hb : translateVarIExt ⟨b, vi0⟩ = some b')
    (hm : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some m') :
    (emitOp (.select 64) d x [c, a, b]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn m' (mpv c'), masgn m' (.Papp1 (.Oneg (.Op_w .U64)) (mpv m')),
        masgn x' (mpv a'), masgn x' (.Papp2 (.Olxor .U64) (mpv x') (mpv b')),
        masgn x' (.Papp2 (.Oland .U64) (mpv x') (mpv m')),
        masgn x' (.Papp2 (.Olxor .U64) (mpv x') (mpv b'))]) := by
  have he : emitOp (.select 64) d x [c, a, b] =
      some ([asgn (tmp 0 .U64) (pv c), asgn (tmp 0 .U64) (.Papp1 (.Oneg .U64) (pv (tmp 0 .U64))),
        asgn x (pv a), asgn x (.Papp2 (.Olxor .U64) (pv x) (pv b)),
        asgn x (.Papp2 (.Oland .U64) (pv x) (pv (tmp 0 .U64))),
        asgn x (.Papp2 (.Olxor .U64) (pv x) (pv b))], x) := rfl
  rw [he, Option.bind_some]
  exact translateCmdExt_mkCmd
    (.cons (translateInstrRExt_asgn hm (translatePExprExt_pv hc))
    (.cons (translateInstrRExt_asgn hm (translatePExprExt_papp1 rfl (translatePExprExt_pv hm)))
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hb)))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hm)))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hb)))
      .nil))))))

/-- **High-multiply image.** The binding of `mulhi 64` to `x` on `a`, `b`:
`_, x = #MULX_lo_hi_64(a, b)`, the discarded low word typed `u64`. -/
theorem translateCmdExt_mulhi {d : Nat} {x a b : JVar} {x' a' b' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hb : translateVarIExt ⟨b, vi0⟩ = some b') :
    (emitOp (.mulhi 64) d x [a, b]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [mcopn "MULX_lo_hi_64" [.Lnone () (.aword .U64), .Lvar x'] [mpv a', mpv b']]) := by
  have he : emitOp (.mulhi 64) d x [a, b] =
      some ([copn (asmName "MULX_lo_hi" .U64) [none, some x] [pv a, pv b]], x) := rfl
  have hn : asmName "MULX_lo_hi" .U64 = "MULX_lo_hi_64" := asmName_U64.2.2.2
  rw [he, Option.bind_some, hn]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  have hl : ([none, some x] : List (Option JVar)).length = 2 := rfl
  simp only [copn, hl, opnNoneTys_MULX_64]
  simp only [outLvs, List.getElem?_cons_zero, Option.getD_some]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_u64,
    translateLValExt_lvv hx, translatePExprExt_pv ha, translatePExprExt_pv hb]
  rfl

/-- **Arithmetic-shift image.** The binding of `sarImm w n` to `x` on `a`:
`x = a; x = x >>s sarCount w n`, the count clamped to `w - 1`. -/
theorem translateCmdExt_sarImm {w n d : Nat} {x a : JVar} {x' a' : MVarI} {ws' : MWSize}
    (hws : translateWSize (wsOf w) = some ws')
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a') :
    (emitOp (.sarImm w n) d x [a]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn x' (mpv a'),
        masgn x' (.Papp2 (.Oasr (.Op_w ws')) (mpv x') (.Pconst (sarCount w n)))]) := by
  have he : emitOp (.sarImm w n) d x [a] =
      some ([asgn x (pv a), asgn x (.Papp2 (.Oasr (wsOf w)) (pv x) (cnst (sarCount w n)))], x) :=
    rfl
  rw [he, Option.bind_some]
  exact translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_papp2
      (by simp [translateSOp2Ext, translateSOp2, hws]) (translatePExprExt_pv hx)
      (translatePExprExt_cnst _))) .nil))

/-- The `(uint) i` index over a non-array local `i` translates to the unsigned
`int_of_word` of its mirror read. -/
theorem translateIdx_uint {i : JVar} {i' : MVarI} (hi : translateVarIExt ⟨i, vi0⟩ = some i') :
    translateIdx (.Papp1 (.Oint_of_word .U64) (pv i)) =
      some (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i')) :=
  translatePExprExt_papp1 rfl (translatePExprExt_pv hi)

/-- **Array-load image.** The binding of `stackLoad w k` to `x` on the array `a` and the
index `i`: `x = a[(uint) i]`. -/
theorem translateCmdExt_stackLoad {w k d : Nat} {x a i : JVar} {x' a' i' : MVarI}
    {ws' : MWSize} (hws : translateWSize (wsOf w) = some ws')
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hi : translateVarIExt ⟨i, vi0⟩ = some i') :
    (emitOp (.stackLoad w k) d x [a, i]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn x' (.Pget .Unaligned .AAscale ws' (mkLvar a')
        (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i')))]) := by
  have he : emitOp (.stackLoad w k) d x [a, i] =
      some ([asgn x (.Pget .AAscale (wsOf w) ⟨⟨a, vi0⟩, false⟩
        (.Papp1 (.Oint_of_word .U64) (pv i)))], x) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx ?_) .nil)
  simp [translatePExprExt_pget, hws, translateGVarExt, ha, translateIdx_uint hi,
    translateArrAccess, mkLvar]

/-- **Array-store image.** The binding of `stackStore w k` on the array `a`, the index `i`
and the value `v`: `a[(uint) i] = v`, in place. -/
theorem translateCmdExt_stackStore {w k d : Nat} {x a i v : JVar} {a' i' v' : MVarI}
    {ws' : MWSize} (hws : translateWSize (wsOf w) = some ws')
    (ha : translateVarIExt ⟨a, vi0⟩ = some a') (hi : translateVarIExt ⟨i, vi0⟩ = some i')
    (hv : translateVarIExt ⟨v, vi0⟩ = some v') :
    (emitOp (.stackStore w k) d x [a, i, v]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [.Cassgn (.Laset .Unaligned .AAscale ws' a'
        (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i'))) .AT_none (.aword ws') (mpv v')]) := by
  have he : emitOp (.stackStore w k) d x [a, i, v] =
      some ([.Cassgn (.Laset .AAscale (wsOf w) ⟨a, vi0⟩ (.Papp1 (.Oint_of_word .U64) (pv i)))
        .AT_none (.sword (wsOf w)) (pv v)], a) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  simp [translateInstrRExt, translateLValExt, hws, ha, translateIdx_uint hi, translateArrAccess,
    translateSTypeExt, translateSType, translatePExprExt_pv hv, translateAssgnTag]

/-- The condition `v != 0` translates to `mnz`. -/
theorem translatePExprExt_nz {v : JVar} {v' : MVarI} (hv : translateVarIExt ⟨v, vi0⟩ = some v') :
    translatePExprExt (nz v) = some (mnz v') :=
  translatePExprExt_papp2 rfl (translatePExprExt_pv hv) (translatePExprExt_cnst 0)

/-- **Counter-loop frame image.** The frame `forCode` of a counted loop translates to the
translated seeds, the trip index and counter initialisations, the mirror loop
`while (ctr != 0)` over the translated body, moves and advance, and the translated moves
after the loop. -/
theorem translateCmdExt_forCode {env : List JVar} {d n ci : Nat}
    {cs : List JasminDialect.JasminTy} {inits : List JVar} {b : JOut}
    {s1 body pm s2 : List MInstr} {idx' ctr' cnt' : MVarI}
    (hs1 : translateCmdExt (seqMoves ((blockVars (d + 1) cs).zip inits)) = some s1)
    (hidx : translateVarIExt ⟨mkV 'r' d u64, vi0⟩ = some idx')
    (hctr : translateVarIExt ⟨mkV 'c' n u64, vi0⟩ = some ctr')
    (hcnt : translateVarIExt ⟨env.getD ci dfltV, vi0⟩ = some cnt')
    (hb : translateCmdExt b.code = some body)
    (hpm : translateCmdExt (parMovesJ b.depth ((blockVars (d + 1) cs).zip b.res)) = some pm)
    (hs2 : translateCmdExt (seqMoves ((blockVars d cs).zip (blockVars (d + 1) cs)).reverse) =
      some s2) :
    translateCmdExt (forCode env d n cs inits ci b) =
      some (s1 ++ mkCmd [masgn idx' (.Pconst 0), masgn ctr' (mpv cnt'),
        .Cwhile .NoAlign [] (mnz ctr') () (body ++ pm ++ mkCmd
          [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
           masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))])] ++ s2) := by
  have hadv : translateCmdExt
      [asgn (mkV 'r' d u64) (.Papp2 (.Oadd .U64) (pv (mkV 'r' d u64)) (cnst 1)),
       asgn (mkV 'c' n u64) (.Papp2 (.Osub .U64) (pv (mkV 'c' n u64)) (cnst 1))] =
      some (mkCmd [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
        masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hidx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hidx) (translatePExprExt_cnst 1)))
      (.cons (translateInstrRExt_asgn hctr
        (translatePExprExt_papp2 rfl (translatePExprExt_pv hctr) (translatePExprExt_cnst 1)))
        .nil))
  have hloop := translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hb hpm) hadv
  have hw : translateInstrRExt (.Cwhile [] (nz (mkV 'c' n u64)) (b.code ++
      parMovesJ b.depth ((blockVars (d + 1) cs).zip b.res) ++
      [asgn (mkV 'r' d u64) (.Papp2 (.Oadd .U64) (pv (mkV 'r' d u64)) (cnst 1)),
       asgn (mkV 'c' n u64) (.Papp2 (.Osub .U64) (pv (mkV 'c' n u64)) (cnst 1))])) =
      some (.Cwhile .NoAlign [] (mnz ctr') () (body ++ pm ++ mkCmd
        [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
         masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))])) := by
    simp only [translateInstrRExt, translateCmdExt, translatePExprExt_nz hctr, hloop]
  have hmid := translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hidx
    (translatePExprExt_cnst 0)) (.cons (translateInstrRExt_asgn hctr (translatePExprExt_pv hcnt))
    (.cons hw .nil)))
  exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hs1 hmid) hs2

/-- **Exit-flag loop image.** The frame `whileCode` translates to the translated seeds and
the mirror loop `while { body; flag = r; moves } (flag != 0)`. -/
theorem translateCmdExt_whileCode {d : Nat} {cs : List JasminDialect.JasminTy}
    {inits : List JVar} {b : JOut} {s1 body pm : List MInstr} {flag' r' : MVarI}
    (hs1 : translateCmdExt (seqMoves ((blockVars d cs).zip inits)) = some s1)
    (hb : translateCmdExt b.code = some body)
    (hflag : translateVarIExt ⟨mkV 'r' (b.depth + cs.length) u64, vi0⟩ = some flag')
    (hr : translateVarIExt ⟨b.res.headD dfltV, vi0⟩ = some r')
    (hpm : translateCmdExt (parMovesJ b.depth ((blockVars d cs).zip b.res.tail)) = some pm) :
    translateCmdExt (whileCode d cs inits b) =
      some (s1 ++ mkCmd [.Cwhile .NoAlign (body ++ .MkI () (masgn flag' (mpv r')) :: pm)
        (mnz flag') () []]) := by
  have hbody := translateCmdExt_append_eq_some hb
    (translateCmdExt_cons (translateInstrRExt_asgn hflag (translatePExprExt_pv hr)) hpm)
  have hi : translateInstrRExt (.Cwhile (b.code ++
      asgn (mkV 'r' (b.depth + cs.length) u64) (pv (b.res.headD dfltV)) ::
        parMovesJ b.depth ((blockVars d cs).zip b.res.tail))
      (nz (mkV 'r' (b.depth + cs.length) u64)) []) =
      some (.Cwhile .NoAlign (body ++ .MkI () (masgn flag' (mpv r')) :: pm) (mnz flag') () []) := by
    simp only [translateInstrRExt, translateCmdExt, translatePExprExt_nz hflag, hbody]
  exact translateCmdExt_append_eq_some hs1 (translateCmdExt_mkCmd (.cons hi .nil))

/-- **Branch image.** The branch `ifCode` translates to the mirror `if (c != 0)` over the
translated branches, each followed by its translated join moves. -/
theorem translateInstrRExt_ifCode {env : List JVar} {d ci : Nat}
    {rs : List JasminDialect.JasminTy} {bt be : JOut} {c' : MVarI}
    {t' e' pmt pme : List MInstr}
    (hc : translateVarIExt ⟨env.getD ci dfltV, vi0⟩ = some c')
    (ht : translateCmdExt bt.code = some t') (he : translateCmdExt be.code = some e')
    (hpt : translateCmdExt (parMovesJ (bt.depth + rs.length) ((blockVars d rs).zip bt.res)) =
      some pmt)
    (hpe : translateCmdExt (parMovesJ (be.depth + rs.length) ((blockVars d rs).zip be.res)) =
      some pme) :
    translateInstrRExt (ifCode env d rs ci bt be) =
      some (.Cif (mnz c') (t' ++ pmt) (e' ++ pme)) := by
  simp only [ifCode, translateInstrRExt, translatePExprExt_nz hc, translateCmdExt_append_eq_some ht hpt,
    translateCmdExt_append_eq_some he hpe]

/-- **Call image.** The call of `f` with the result variables `xs` and the argument
variables `as` translates to the mirror call with the translated l-values and reads. -/
theorem translateInstrRExt_call (f : String) {xs as : List JVar} {xs' as' : List MVarI}
    (hxs : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs')
    (has : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') as as') :
    translateInstrRExt (.Ccall .DoNotInline (xs.map lvv) ⟨f⟩ (as.map pv)) =
      some (.Ccall (xs'.map .Lvar) { name := f } (as'.map mpv)) := by
  simp only [translateInstrRExt, mapM_lvv hxs, mapM_pv has]

/-! ### The typed images -/

/-- The typing of a command of `mkCmd` is `mkCmd` of the typed instructions. -/
theorem typeC_mkCmd : ∀ c : List MInstrR, typeC (mkCmd c) = mkCmd (c.map typeI)
  | [] => rfl
  | i :: c => by
      simp only [mkCmd, List.map_cons] at typeC_mkCmd ⊢
      rw [typeC, typeC_mkCmd c]

/-- A constant assigned to a variable is typed at the type of the variable. -/
theorem typeI_masgn_const (x : MVarI) (z : Int) :
    typeI (masgn x (.Pconst z)) = masgn x (typeConst x.v_var.vtype z) := rfl

/-- **Typed carry-in.** The constant of `#ADD_64(cin, -1)` is the word `(64u) -1`. -/
theorem typeI_cinCode (cin t0 : MVarI) :
    typeI (mcopn "ADD_64" (mCWOuts t0) [mpv cin, .Pconst (-1)]) =
      mcopn "ADD_64" (mCWOuts t0) [mpv cin, .Papp1 (.Oword_of_int .U64) (.Pconst (-1))] := by
  rfl

/-- **Typed flip.** The constant of the flip `x = x ^ 1` of the comparison idiom is the word
`(64u) 1`. -/
theorem typeI_flip (x : MVarI) :
    typeI (masgn x (.Papp2 (.Olxor .U64) (mpv x) (.Pconst 1))) =
      masgn x (.Papp2 (.Olxor .U64) (mpv x) (.Papp1 (.Oword_of_int .U64) (.Pconst 1))) := rfl

/-- **Typed loop condition.** The constant of the condition `v != 0` is the word `(64u) 0`. -/
theorem typeE_mnz (v : MVarI) :
    typeE .abool (mnz v) =
      .Papp2 (.Oneq (.Op_w .U64)) (mpv v) (.Papp1 (.Oword_of_int .U64) (.Pconst 0)) := rfl

/-- **Typed shift count.** The count of a word shift is a `u8`. -/
theorem typeE_olsr (ty : MAtype) (ws : MWSize) (x : MVarI) (z : Int) :
    typeE ty (.Papp2 (.Olsr ws) (mpv x) (.Pconst z)) =
      .Papp2 (.Olsr ws) (mpv x) (.Papp1 (.Oword_of_int .U8) (.Pconst z)) := rfl

/-! ## 6. Completeness on the units of `nfToJasmin` -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminTy)

/-- A variable whose type is not a 512-bit word. -/
def OkV (v : JVar) : Prop := v.vtype ≠ .sword .U512

/-- A command that translates. -/
@[irreducible] def TrC (c : List AInstrR) : Prop := (translateCmdExt c).isSome = true

theorem translateWSize_isSome {ws : AWSize} (h : ws ≠ .U512) : (translateWSize ws).isSome := by
  cases ws <;> simp_all [translateWSize]

theorem translateSTypeExt_isSome {s : ASType} (h : s ≠ .sword .U512) :
    (translateSTypeExt s).isSome := by
  cases s with
  | sword ws => cases ws <;> simp_all [translateSTypeExt, translateSType, translateWSize]
  | _ => simp [translateSTypeExt, translateSType]

theorem translateVarIExt_isSome {v : JVar} (h : OkV v) (i : CatCrypt.Crypto.Jasmin.VarInfo) :
    (translateVarIExt ⟨v, i⟩).isSome := by
  simpa [translateVarIExt, translateVarExt] using translateSTypeExt_isSome h

theorem okV_tmp {k : Nat} {ws : AWSize} (h : ws ≠ .U512) : OkV (tmp k ws) := by
  simpa [OkV, tmp, mkV] using h

theorem okV_cf : OkV cfVar := by simp [OkV, cfVar]

theorem okV_u64 {c : Char} {k : Nat} : OkV (mkV c k u64) := by simp [OkV, mkV]

theorem okV_getD {env : List JVar} (h : ∀ v ∈ env, OkV v) (i : Nat) :
    OkV (env.getD i dfltV) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : env[i]? with
  | none => simp [dfltV, OkV, mkV]
  | some v => exact h v (List.mem_of_getElem? hi)

theorem okV_headD {l : List JVar} (h : ∀ v ∈ l, OkV v) : OkV (l.headD dfltV) := by
  cases l with
  | nil => simp [dfltV, OkV, mkV]
  | cons v l => exact h v (by simp)

theorem okV_resolveHV {env : List JVar} (h : ∀ v ∈ env, OkV v) {Γ : Ctxt jasminDialect}
    {ts : List JasminDialect.JasminTy} (hv : HVector (fun t => Ctxt.Var Γ t) ts) :
    ∀ v ∈ resolveHV env hv, OkV v := by
  intro v hv'
  simp only [resolveHV, List.mem_map] at hv'
  obtain ⟨i, _, rfl⟩ := hv'
  exact okV_getD h i

theorem okV_blockVars (base : Nat) {cs : List JasminDialect.JasminTy}
    (h : cs.all tyOkB = true) : ∀ v ∈ blockVars base cs, OkV v := by
  intro v hv
  simp only [blockVars, List.mem_map] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  exact styOf_ne_U512 (List.all_eq_true.mp h _ (List.fst_mem_of_mem_zipIdx hp))

theorem okV_append {l l' : List JVar} (h : ∀ v ∈ l, OkV v) (h' : ∀ v ∈ l', OkV v) :
    ∀ v ∈ l ++ l', OkV v := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact h v hv
  · exact h' v hv

theorem okV_cons {v : JVar} {l : List JVar} (h : OkV v) (h' : ∀ v ∈ l, OkV v) :
    ∀ w ∈ v :: l, OkV w := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact h
  · exact h' w hw

theorem okV_zip {l l' : List JVar} (h : ∀ v ∈ l, OkV v) (h' : ∀ v ∈ l', OkV v) :
    ∀ p ∈ l.zip l', OkV p.1 ∧ OkV p.2 :=
  fun _ hp => ⟨h _ (List.of_mem_zip hp).1, h' _ (List.of_mem_zip hp).2⟩

/-! ### Expressions, l-values and instructions -/

theorem isSome_pv {v : JVar} (h : OkV v) : (translatePExprExt (pv v)).isSome := by
  obtain ⟨v', hv⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome h vi0)
  rw [translatePExprExt_pv hv]; rfl

theorem isSome_cnst (z : Int) : (translatePExprExt (cnst z)).isSome := rfl

theorem isSome_papp2 {op : ASOp2} {e1 e2 : APExpr} (ho : (translateSOp2Ext op).isSome)
    (h1 : (translatePExprExt e1).isSome) (h2 : (translatePExprExt e2).isSome) :
    (translatePExprExt (.Papp2 op e1 e2)).isSome := by
  obtain ⟨_, ho⟩ := Option.isSome_iff_exists.mp ho
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp h2
  rw [translatePExprExt_papp2 ho h1 h2]; rfl

theorem isSome_papp1 {op : ASOp1} {e : APExpr} (ho : (translateSOp1 op).isSome)
    (h : (translatePExprExt e).isSome) : (translatePExprExt (.Papp1 op e)).isSome := by
  obtain ⟨_, ho⟩ := Option.isSome_iff_exists.mp ho
  obtain ⟨_, h⟩ := Option.isSome_iff_exists.mp h
  rw [translatePExprExt_papp1 ho h]; rfl

theorem isSome_nz {v : JVar} (h : OkV v) : (translatePExprExt (nz v)).isSome :=
  isSome_papp2 rfl (isSome_pv h) (isSome_cnst 0)

theorem isSome_binSop {ws : AWSize} (h : ws ≠ .U512) (bop : JasminDialect.JasminBinOp) :
    (translateSOp2Ext (binSop ws bop)).isSome := by
  cases bop <;> cases ws <;> simp_all [binSop, translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_olsr {ws : AWSize} (h : ws ≠ .U512) : (translateSOp2Ext (.Olsr ws)).isSome := by
  cases ws <;> simp_all [translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_olsl {ws : AWSize} (h : ws ≠ .U512) : (translateSOp2Ext (.Olsl ws)).isSome := by
  cases ws <;> simp_all [translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_oasr {ws : AWSize} (h : ws ≠ .U512) : (translateSOp2Ext (.Oasr ws)).isSome := by
  cases ws <;> simp_all [translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_olxor {ws : AWSize} (h : ws ≠ .U512) : (translateSOp2Ext (.Olxor ws)).isSome := by
  cases ws <;> simp_all [translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_oland {ws : AWSize} (h : ws ≠ .U512) : (translateSOp2Ext (.Oland ws)).isSome := by
  cases ws <;> simp_all [translateSOp2Ext, translateSOp2, translateWSize]

theorem isSome_oneg {ws : AWSize} (h : ws ≠ .U512) : (translateSOp1 (.Oneg ws)).isSome := by
  cases ws <;> simp_all [translateSOp1, translateWSize]

theorem isSome_ozeroext {ws ws' : AWSize} (h : ws ≠ .U512) (h' : ws' ≠ .U512) :
    (translateSOp1 (.Ozeroext ws ws')).isSome := by
  cases ws <;> cases ws' <;> simp_all [translateSOp1, translateWSize]

theorem isSome_oint_of_word : (translateSOp1 (.Oint_of_word .U64)).isSome := rfl

theorem u64_ne_U512 : (CatCrypt.Crypto.Jasmin.WSize.U64 : AWSize) ≠ .U512 := by decide

theorem sint_ne_U512 : (CatCrypt.Crypto.Jasmin.SType.sint : ASType) ≠ .sword .U512 := by decide

theorem sword_ne_U512 {ws : AWSize} (h : ws ≠ .U512) :
    CatCrypt.Crypto.Jasmin.SType.sword ws ≠ .sword .U512 := by
  simpa using h

theorem okV_mkV {c : Char} {k : Nat} {s : ASType} (h : s ≠ .sword .U512) : OkV (mkV c k s) := h

theorem translateIdx_isSome {e : APExpr} (h : (translatePExprExt e).isSome) :
    (translateIdx e).isSome := by
  cases e with
  | Pvar g =>
      simp only [translateIdx, intOfWordIdx]
      split
      · simpa [translatePExprExt] using h
      · exact h
  | _ => exact h

theorem isSome_pget {aa : CatCrypt.Crypto.Jasmin.ArrAccess} {ws : AWSize} {a : JVar}
    {i : APExpr} (hws : ws ≠ .U512) (ha : OkV a) (hi : (translatePExprExt i).isSome) :
    (translatePExprExt (.Pget aa ws ⟨⟨a, vi0⟩, false⟩ i)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (translateWSize_isSome hws)
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome ha vi0)
  obtain ⟨_, h3⟩ := Option.isSome_iff_exists.mp (translateIdx_isSome hi)
  simp [translatePExprExt_pget, h1, translateGVarExt, h2, h3]

theorem isSome_asgn {x : JVar} {e : APExpr} (hx : OkV x) (he : (translatePExprExt e).isSome) :
    (translateInstrRExt (asgn x e)).isSome := by
  obtain ⟨_, hx⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome hx vi0)
  obtain ⟨_, he⟩ := Option.isSome_iff_exists.mp he
  rw [translateInstrRExt_asgn hx he]; rfl

theorem isSome_laset {aa : CatCrypt.Crypto.Jasmin.ArrAccess} {ws : AWSize} {a : JVar}
    {i e : APExpr} {ty : ASType} (hws : ws ≠ .U512) (ha : OkV a)
    (hi : (translatePExprExt i).isSome) (hty : ty ≠ .sword .U512)
    (he : (translatePExprExt e).isSome) :
    (translateInstrRExt (.Cassgn (.Laset aa ws ⟨a, vi0⟩ i) .AT_none ty e)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (translateWSize_isSome hws)
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome ha vi0)
  obtain ⟨_, h3⟩ := Option.isSome_iff_exists.mp (translateIdx_isSome hi)
  obtain ⟨_, h4⟩ := Option.isSome_iff_exists.mp (translateSTypeExt_isSome hty)
  obtain ⟨_, h5⟩ := Option.isSome_iff_exists.mp he
  simp [translateInstrRExt, translateLValExt, h1, h2, h3, h4, h5]

theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | a :: l, h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
        (mapM_isSome (f := f) (l := l) fun a ha => h a (by simp [ha]))
      simp [List.mapM_cons, hb, hbs]

theorem outLvs_isSome {tys : List ASType} (htys : ∀ ty ∈ tys, ty ≠ .sword .U512) :
    ∀ (k : Nat) (outs : List (Option JVar)), (∀ x, some x ∈ outs → OkV x) →
      ∀ lv ∈ outLvs tys k outs, (translateLValExt lv).isSome
  | _, [], _, lv, hlv => by simp [outLvs] at hlv
  | k, none :: outs, h, lv, hlv => by
      simp only [outLvs, List.mem_cons] at hlv
      rcases hlv with rfl | hlv
      · have hty : (tys[k]?).getD u64 ≠ .sword .U512 := by
          cases hk : tys[k]? with
          | none => simp
          | some ty => exact htys ty (List.mem_of_getElem? hk)
        simpa [translateLValExt] using translateSTypeExt_isSome hty
      · exact outLvs_isSome htys (k + 1) outs (fun x hx => h x (by simp [hx])) lv hlv
  | k, some v :: outs, h, lv, hlv => by
      simp only [outLvs, List.mem_cons] at hlv
      rcases hlv with rfl | hlv
      · obtain ⟨_, hv⟩ := Option.isSome_iff_exists.mp
          (translateVarIExt_isSome (h v (by simp)) vi0)
        rw [translateLValExt_lvv hv]; rfl
      · exact outLvs_isSome htys (k + 1) outs (fun x hx => h x (by simp [hx])) lv hlv

theorem isSome_copn {o : String} {outs : List (Option JVar)} {es : List APExpr}
    (htys : ∀ ty ∈ opnNoneTys o outs.length, ty ≠ .sword .U512)
    (hout : ∀ x, some x ∈ outs → OkV x) (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn o outs es)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (mapM_isSome (outLvs_isSome htys 0 outs hout))
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (mapM_isSome hes)
  simp only [copn, translateInstrRExt, h1, h2]; rfl

/-- The `_` outputs of the width variants of the asm operations of the op table have no
512-bit word type. -/
theorem opnNoneTys_asmName {base : String}
    (hb : base ∈ ["ANDN", "ADC", "NEG", "CMP", "MULX_lo_hi"]) {ws : AWSize} (hws : ws ≠ .U512)
    {n : Nat} (hn : n ∈ [2, 5, 6]) :
    ∀ ty ∈ opnNoneTys (asmName base ws) n, ty ≠ .sword .U512 :=
  CatCrypt.Crypto.Jasmin.JazzToInstrR.opnNoneTys_ne_U512 ws (by cases ws <;> simp_all)
    base hb n hn

theorem translateCmdExt_isSome {c : List AInstrR} (h : TrC c) :
    (translateCmdExt c).isSome := by
  unfold TrC at h; exact h

theorem trC_append {a b : List AInstrR} (ha : TrC a) (hb : TrC b) : TrC (a ++ b) := by
  obtain ⟨_, ha⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome ha)
  obtain ⟨_, hb⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome hb)
  unfold TrC; rw [translateCmdExt_append_eq_some ha hb]; rfl

theorem trC_nil : TrC [] := by unfold TrC; rfl

theorem trC_cons {i : AInstrR} {c : List AInstrR} (hi : (translateInstrRExt i).isSome)
    (hc : TrC c) : TrC (i :: c) := by
  obtain ⟨_, hi⟩ := Option.isSome_iff_exists.mp hi
  obtain ⟨_, hc⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome hc)
  unfold TrC; rw [translateCmdExt_cons hi hc]; rfl

theorem trC_of_forall : ∀ {c : List AInstrR}, (∀ i ∈ c, (translateInstrRExt i).isSome) → TrC c
  | [], _ => trC_nil
  | i :: c, h => trC_cons (h i (by simp)) (trC_of_forall fun j hj => h j (by simp [hj]))

theorem forall_mem_nil_isSome : ∀ e ∈ ([] : List APExpr), (translatePExprExt e).isSome := by
  simp

theorem forall_mem_cons_isSome {e : APExpr} {es : List APExpr}
    (he : (translatePExprExt e).isSome) (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    ∀ e' ∈ e :: es, (translatePExprExt e').isSome := by
  intro e' he'
  rcases List.mem_cons.mp he' with rfl | he'
  · exact he
  · exact hes e' he'

/-- The asm operation with the `b5w_ty` outputs of the word `x`. -/
theorem isSome_copnW {base : String}
    (hb : base ∈ ["ANDN", "ADC", "NEG", "CMP", "MULX_lo_hi"]) {ws : AWSize} (hws : ws ≠ .U512)
    {x : JVar} (hx : OkV x) {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName base ws) (outsW x) es)).isSome :=
  isSome_copn (opnNoneTys_asmName hb hws (by simp [outsW]))
    (fun y hy => by simp [outsW] at hy; subst hy; exact hx) hes

/-- The asm operation with the `b5w_ty` outputs of the carry flag and the word `x`. -/
theorem isSome_copnCW {base : String}
    (hb : base ∈ ["ANDN", "ADC", "NEG", "CMP", "MULX_lo_hi"]) {ws : AWSize} (hws : ws ≠ .U512)
    {x : JVar} (hx : OkV x) {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName base ws) (outsCW x) es)).isSome :=
  isSome_copn (opnNoneTys_asmName hb hws (by simp [outsCW]))
    (fun y hy => by
      simp [outsCW] at hy
      rcases hy with rfl | rfl
      · exact okV_cf
      · exact hx) hes

theorem isSome_andn {ws : AWSize} (hws : ws ≠ .U512) {x : JVar} (hx : OkV x)
    {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName "ANDN" ws) (outsW x) es)).isSome :=
  isSome_copnW (by simp) hws hx hes

theorem isSome_adc {ws : AWSize} (hws : ws ≠ .U512) {x : JVar} (hx : OkV x)
    {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName "ADC" ws) (outsCW x) es)).isSome :=
  isSome_copnCW (by simp) hws hx hes

theorem isSome_neg {ws : AWSize} (hws : ws ≠ .U512) {x : JVar} (hx : OkV x)
    {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName "NEG" ws) (outsCW x) es)).isSome :=
  isSome_copnCW (by simp) hws hx hes

theorem isSome_cmpOp {ws : AWSize} (hws : ws ≠ .U512) {es : List APExpr}
    (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName "CMP" ws) [none, some cfVar, none, none, none] es)).isSome :=
  isSome_copn (opnNoneTys_asmName (by simp) hws (by simp))
    (fun y hy => by simp at hy; subst hy; exact okV_cf) hes

theorem isSome_mulx {ws : AWSize} (hws : ws ≠ .U512) {x : JVar} (hx : OkV x)
    {es : List APExpr} (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn (asmName "MULX_lo_hi" ws) [none, some x] es)).isSome :=
  isSome_copn (opnNoneTys_asmName (by simp) hws (by simp))
    (fun y hy => by simp at hy; subst hy; exact hx) hes

theorem isSome_add64 {x : JVar} (hx : OkV x) {es : List APExpr}
    (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn "ADD_64" (outsCW x) es)).isSome :=
  isSome_copn (by simp [outsCW, opnNoneTys_ADD_64])
    (fun y hy => by
      simp [outsCW] at hy
      rcases hy with rfl | rfl
      · exact okV_cf
      · exact hx) hes

theorem isSome_adc64 {x : JVar} (hx : OkV x) {es : List APExpr}
    (hes : ∀ e ∈ es, (translatePExprExt e).isSome) :
    (translateInstrRExt (copn "ADC_64" (outsW x) es)).isSome :=
  isSome_copn (by simp [outsW, opnNoneTys_ADC_64])
    (fun y hy => by simp [outsW] at hy; subst hy; exact hx) hes

theorem isSome_cfor {v : JVar} (hv : OkV v) (r : CatCrypt.Crypto.Jasmin.Range)
    {body : List AInstrR} (hb : TrC body) :
    (translateInstrRExt (.Cfor ⟨v, vi0⟩ r body)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome hv vi0)
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome hb)
  simp [translateInstrRExt, h1, h2]

theorem isSome_cwhile {c1 c2 : List AInstrR} {e : APExpr} (h1 : TrC c1)
    (he : (translatePExprExt e).isSome) (h2 : TrC c2) :
    (translateInstrRExt (.Cwhile c1 e c2)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome h1)
  obtain ⟨_, he⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome h2)
  simp [translateInstrRExt, h1, he, h2]

theorem isSome_cif {c1 c2 : List AInstrR} {e : APExpr} (he : (translatePExprExt e).isSome)
    (h1 : TrC c1) (h2 : TrC c2) : (translateInstrRExt (.Cif e c1 c2)).isSome := by
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome h1)
  obtain ⟨_, he⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome h2)
  simp [translateInstrRExt, h1, he, h2]

theorem okV_getElem? {l : List JVar} (h : ∀ v ∈ l, OkV v) (i : Nat) :
    OkV (l[i]?.getD dfltV) := by
  simpa [List.getD_eq_getElem?_getD] using okV_getD h i

/-- Closes the translation goals of the emitted instructions by the closure lemmas above,
each applied at reducible transparency. -/
local macro "tr_solve" : tactic => `(tactic| repeat' (first
  | assumption
  | with_reducible apply okV_getElem?
  | ((with_reducible apply wsOf_ne_U512); first | assumption | rfl)
  | ((with_reducible apply wsOf_ne_U512_of_bit); assumption)
  | with_reducible apply trC_nil | with_reducible apply trC_cons
  | with_reducible apply isSome_asgn | with_reducible apply isSome_pv
  | with_reducible apply isSome_cnst | with_reducible apply isSome_papp2
  | with_reducible apply isSome_papp1 | with_reducible apply isSome_pget
  | with_reducible apply isSome_laset | with_reducible apply isSome_cfor
  | with_reducible apply isSome_binSop | with_reducible apply isSome_olsr
  | with_reducible apply isSome_olsl | with_reducible apply isSome_oasr
  | with_reducible apply isSome_olxor | with_reducible apply isSome_oland
  | with_reducible apply isSome_oneg | with_reducible apply isSome_ozeroext
  | with_reducible apply isSome_oint_of_word | with_reducible apply isSome_andn
  | with_reducible apply isSome_adc | with_reducible apply isSome_neg
  | with_reducible apply isSome_cmpOp | with_reducible apply isSome_mulx
  | with_reducible apply isSome_add64 | with_reducible apply isSome_adc64
  | with_reducible apply forall_mem_nil_isSome | with_reducible apply forall_mem_cons_isSome
  | with_reducible apply okV_tmp | with_reducible apply okV_cf
  | with_reducible apply okV_mkV
  | with_reducible apply u64_ne_U512 | with_reducible apply sint_ne_U512
  | with_reducible apply sword_ne_U512))

/-- The code of the binding of an operation that passes `opOkB` translates, on variables
without a 512-bit word type. -/
theorem emitOp_trC {op : JasminDialect.JasminOp} {d : Nat} {x : JVar} {as : List JVar}
    {c : List AInstrR} {y : JVar} (h : emitOp op d x as = some (c, y)) (hop : opOkB op = true)
    (hx : OkV x) (has : ∀ v ∈ as, OkV v) : TrC c ∧ OkV y := by
  cases op
  all_goals try (cases ‹JasminDialect.JasminBinOp›)
  all_goals try (cases ‹JasminDialect.JasminCmp›)
  all_goals simp [emitOp] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals refine ⟨?_, by first | exact hx | exact okV_getElem? has _⟩
  all_goals simp only [opOkB, Bool.and_eq_true] at hop
  all_goals try obtain ⟨hop, hop'⟩ := hop
  all_goals try replace hop := widthOkB_of_bmi hop
  all_goals try simp only [castCode, matCF, cmpCode, cinCode, List.cons_append, List.nil_append,
    List.append_assoc]
  all_goals repeat' split
  all_goals refine trC_of_forall ?_
  all_goals simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or,
    forall_eq_or_imp, forall_eq]
  all_goals and_intros
  all_goals tr_solve

/-! ### The frames of the lowering -/

theorem trC_seqMoves {ps : List (JVar × JVar)} (h : ∀ p ∈ ps, OkV p.1 ∧ OkV p.2) :
    TrC (seqMoves ps) := by
  refine trC_of_forall fun i hi => ?_
  simp only [seqMoves, List.mem_map] at hi
  obtain ⟨p, hp, rfl⟩ := hi
  exact isSome_asgn (h p hp).1 (isSome_pv (h p hp).2)

theorem trC_parMovesJ (D : Nat) {ps : List (JVar × JVar)} (h : ∀ p ∈ ps, OkV p.1 ∧ OkV p.2) :
    TrC (parMovesJ D ps) := by
  refine trC_of_forall fun i hi => ?_
  simp only [parMovesJ] at hi
  split at hi
  · simp only [List.mem_map, List.mem_filter] at hi
    obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hi
    exact isSome_asgn (h p hp).1 (isSome_pv (h p hp).2)
  · simp only [List.mem_append, List.mem_map] at hi
    rcases hi with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have hq' := (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hq)).1
      exact isSome_asgn (okV_mkV (h _ hq').1) (isSome_pv (h _ hq').2)
    · have hq' := (List.mem_filter.mp (List.fst_mem_of_mem_zipIdx hq)).1
      exact isSome_asgn (h _ hq').1 (isSome_pv (okV_mkV (h _ hq').1))

theorem trC_forCode {env : List JVar} {d n : Nat} {cs : List JasminTy} {inits : List JVar}
    {ci : Nat} {b : JOut} (hcs : cs.all tyOkB = true) (henv : ∀ v ∈ env, OkV v)
    (hinit : ∀ v ∈ inits, OkV v) (hb1 : TrC b.code) (hb2 : ∀ v ∈ b.res, OkV v) :
    TrC (forCode env d n cs inits ci b) := by
  have hcar := okV_blockVars (d + 1) hcs
  unfold forCode
  refine trC_append (trC_append (trC_seqMoves (okV_zip hcar hinit)) ?_)
    (trC_seqMoves fun p hp => okV_zip (okV_blockVars d hcs) hcar p (List.mem_reverse.mp hp))
  refine trC_cons (isSome_asgn okV_u64 (isSome_cnst 0))
    (trC_cons (isSome_asgn okV_u64 (isSome_pv (okV_getD henv ci))) (trC_cons ?_ trC_nil))
  refine isSome_cwhile trC_nil (isSome_nz okV_u64) ?_
  refine trC_append (trC_append hb1 (trC_parMovesJ _ (okV_zip hcar hb2))) ?_
  exact trC_cons (isSome_asgn okV_u64 (isSome_papp2 rfl (isSome_pv okV_u64) (isSome_cnst 1)))
    (trC_cons (isSome_asgn okV_u64 (isSome_papp2 rfl (isSome_pv okV_u64) (isSome_cnst 1)))
      trC_nil)

theorem isSome_ifCode {env : List JVar} {d : Nat} {rs : List JasminTy} {ci : Nat}
    {bt be : JOut} (hrs : rs.all tyOkB = true) (henv : ∀ v ∈ env, OkV v)
    (ht1 : TrC bt.code) (ht2 : ∀ v ∈ bt.res, OkV v) (he1 : TrC be.code)
    (he2 : ∀ v ∈ be.res, OkV v) :
    (translateInstrRExt (ifCode env d rs ci bt be)).isSome := by
  have hblk := okV_blockVars d hrs
  exact isSome_cif (isSome_nz (okV_getD henv ci))
    (trC_append ht1 (trC_parMovesJ _ (okV_zip hblk ht2)))
    (trC_append he1 (trC_parMovesJ _ (okV_zip hblk he2)))

theorem trC_whileCode {d : Nat} {cs : List JasminTy} {inits : List JVar} {b : JOut}
    (hcs : cs.all tyOkB = true) (hinit : ∀ v ∈ inits, OkV v) (hb1 : TrC b.code)
    (hb2 : ∀ v ∈ b.res, OkV v) : TrC (whileCode d cs inits b) := by
  have hcar := okV_blockVars d hcs
  have htail : ∀ v ∈ b.res.tail, OkV v := fun v hv => hb2 v (List.mem_of_mem_tail hv)
  unfold whileCode
  refine trC_append (trC_seqMoves (okV_zip hcar hinit)) (trC_cons ?_ trC_nil)
  exact isSome_cwhile (trC_append hb1 (trC_cons (isSome_asgn okV_u64 (isSome_pv (okV_headD hb2)))
    (trC_parMovesJ _ (okV_zip hcar htail)))) (isSome_nz okV_u64) trC_nil

theorem isSome_call (f : String) {xs as : List JVar} (hxs : ∀ v ∈ xs, OkV v)
    (has : ∀ v ∈ as, OkV v) :
    (translateInstrRExt (.Ccall .DoNotInline (xs.map lvv) ⟨f⟩ (as.map pv))).isSome := by
  have h1 : ((xs.map lvv).mapM translateLValExt).isSome := mapM_isSome fun lv hlv => by
    simp only [List.mem_map] at hlv
    obtain ⟨x, hx, rfl⟩ := hlv
    obtain ⟨_, h⟩ := Option.isSome_iff_exists.mp (translateVarIExt_isSome (hxs x hx) vi0)
    rw [translateLValExt_lvv h]; rfl
  have h2 : ((as.map pv).mapM translatePExprExt).isSome := mapM_isSome fun e he => by
    simp only [List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact isSome_pv (has a ha)
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp h2
  simp only [translateInstrRExt, h1, h2]; rfl

/-- **Translation of a lowered region.** On an environment of variables without a 512-bit
word type, the code of every region `nfToJasminBody` lowers from a program that passes
`widthsGo` translates, and its returned variables have no 512-bit word type. -/
theorem body_trC : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (env : List JVar) (d n : Nat) (r : JOut),
    widthsGo p = true → (∀ v ∈ env, OkV v) → nfToJasminBody env p d n = some r →
    TrC r.code ∧ ∀ v ∈ r.res, OkV v := by
  intro Γ ts p
  induction p with
  | ret vs =>
      intro env d n r _ henv h
      simp only [nfToJasminBody, Option.some.injEq] at h
      subst h
      exact ⟨trC_nil, okV_resolveHV henv vs⟩
  | @var Γ t ts e k ih =>
      intro env d n r hw henv h
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨ht, hop⟩, hk⟩ := hw
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨c, y⟩, hc, r', hr', rfl⟩ := h
      obtain ⟨hc1, hy⟩ := emitOp_trC hc hop (okV_mkV (styOf_ne_U512 ht))
        (okV_resolveHV henv e.args)
      obtain ⟨hk1, hk2⟩ := ih _ _ _ _ hk (okV_cons hy henv) hr'
      exact ⟨trC_append hc1 hk1, hk2⟩
  | forLoop count inits body k ihb ihk =>
      intro env d n r hw henv h
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨hcs, hwb⟩, hwk⟩ := hw
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      obtain ⟨hb1, hb2⟩ := ihb _ _ _ _ hwb (okV_append (okV_blockVars _ hcs)
        (okV_cons okV_u64 henv)) hb
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ hwk (okV_append (okV_blockVars _ hcs) henv) hr'
      exact ⟨trC_append (trC_forCode hcs henv (okV_resolveHV henv inits) hb1 hb2) hk1, hk2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro env d n r hw henv h
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨⟨hrs, hwt⟩, hwe⟩, hwk⟩ := hw
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, r', hr', rfl⟩ := h
      obtain ⟨ht1, ht2⟩ := iht _ _ _ _ hwt henv ht
      obtain ⟨he1, he2⟩ := ihe _ _ _ _ hwe henv he
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ hwk (okV_append (okV_blockVars _ hrs) henv) hr'
      exact ⟨trC_append (trC_cons (isSome_ifCode hrs henv ht1 ht2 he1 he2) trC_nil) hk1, hk2⟩
  | whileLoop inits body k ihb ihk =>
      intro env d n r hw henv h
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨⟨hcs, hwb⟩, hwk⟩ := hw
      simp only [nfToJasminBody, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, r', hr', rfl⟩ := h
      obtain ⟨hb1, hb2⟩ := ihb _ _ _ _ hwb (okV_append (okV_blockVars _ hcs) henv) hb
      obtain ⟨hk1, hk2⟩ := ihk _ _ _ _ hwk (okV_append (okV_blockVars _ hcs) henv) hr'
      exact ⟨trC_append (trC_whileCode hcs (okV_resolveHV henv inits) hb1 hb2) hk1, hk2⟩
  | call f args k ih =>
      intro env d n r hw henv h
      simp only [widthsGo, Bool.and_eq_true] at hw
      obtain ⟨hrs, hwk⟩ := hw
      simp only [nfToJasminBody] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨r', hr', rfl⟩ := h
        obtain ⟨hk1, hk2⟩ := ih _ _ _ _ hwk (okV_append (okV_blockVars _ hrs) henv) hr'
        exact ⟨trC_append (trC_cons (isSome_call f (okV_blockVars _ hrs)
          (okV_resolveHV henv args)) trC_nil) hk1, hk2⟩
      · simp at h

/-! ### Units -/

/-- The parameters of a fitting signature over a context that passes `tyOkB` have no
512-bit word type. -/
theorem okV_paramPairs {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    (hfit : sig.fitsB = true) (hΓ : Γ.all tyOkB = true) : ∀ p ∈ paramPairs sig, OkV p.1 := by
  intro p hp
  simp only [paramPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hlen : j < Γ.reverse.length := by
    rw [List.length_reverse, ← sig.params_length]; exact hj
  have hmem : (sig.params[j], Γ.reverse[j]) ∈ sig.params.zip Γ.reverse := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simpa [hj] using hlen, by simp⟩
  have hty := (sig.fitsB_iff.mp hfit).1 _ hmem
  show (mkV _ _ _).vtype ≠ _
  simp only [mkV, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hty]
  exact styOf_ne_U512 (List.all_eq_true.mp hΓ _ (List.mem_reverse.mp (List.getElem_mem hlen)))

/-- The function of a body translates when its parameters and results have no 512-bit
word type and its body translates. -/
theorem translateFn_mkFn_isSome {fname : String}
    {ps : List (JVar × CatCrypt.Crypto.Jasmin.Jazz.Storage × CatCrypt.Crypto.Jasmin.Jazz.PType)}
    {body : List AInstrR} {res : List JVar}
    {resTys : List (CatCrypt.Crypto.Jasmin.Jazz.Storage × CatCrypt.Crypto.Jasmin.Jazz.PType)}
    (hps : ∀ p ∈ ps, OkV p.1) (hb : TrC body) (hres : ∀ v ∈ res, OkV v) :
    (translateFn (mkFn fname ps body res resTys)).isSome := by
  obtain ⟨_, e1⟩ := Option.isSome_iff_exists.mp
    (mapM_isSome (f := fun p : CatCrypt.Crypto.Jasmin.FunParam => translateVarIExt p.var)
      (l := (mkFn fname ps body res resTys).fd.params) fun q hq => by
        simp only [mkFn, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        exact translateVarIExt_isSome (hps p hp) vi0)
  obtain ⟨_, e2⟩ := Option.isSome_iff_exists.mp (translateCmdExt_isSome hb)
  obtain ⟨_, e3⟩ := Option.isSome_iff_exists.mp
    (mapM_isSome (f := translateVarIExt) (l := (mkFn fname ps body res resTys).fd.results)
      fun x hx => by
        simp only [mkFn, List.mem_map] at hx
        obtain ⟨v, hv, rfl⟩ := hx
        exact translateVarIExt_isSome (hres v hv) vi0)
  rw [translateFn_eq_some _ e1 e2 e3]; rfl

/-- **Completeness of the translation on the units of the lowering**: every unit
`nfToJasmin` returns translates to a program of the `CoqSemMirror` syntax. -/
theorem translateUnit_isSome_of_nfToJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    {sig : JazzSig Γ t} {fname : String} {p : NFProg jasminDialect Γ [t]}
    {u : CatCrypt.Crypto.Jasmin.Jazz.JazzUnit} (h : nfToJasmin sig fname p = some u) :
    (translateUnit u).isSome := by
  have hw := jasminWidthsB_of_nfToJasmin h
  simp only [jasminWidthsB, Bool.and_eq_true] at hw
  obtain ⟨⟨hΓ, ht⟩, hwp⟩ := hw
  obtain ⟨hfit, r, hr, rfl⟩ := nfToJasmin_eq_some h
  have hpp := okV_paramPairs hfit hΓ
  have hpv : ∀ v ∈ (paramPairs sig).map Prod.fst, OkV v := by
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨q, hq, rfl⟩ := hv
    exact hpp q hq
  obtain ⟨hb, hres⟩ := body_trC p _ _ _ r hwp
    (fun v hv => hpv v (List.mem_reverse.mp hv)) hr
  have hrv : OkV (r.res.headD dfltV) := okV_headD hres
  have htt : styOf t ≠ .sword .U512 := styOf_ne_U512 (by simpa using ht)
  obtain ⟨fd, hfd⟩ : ∃ fd, translateFn (finish sig fname r) = some fd := by
    apply Option.isSome_iff_exists.mp
    cases hrp : sig.resultParam with
    | some j =>
        simp only [finish, hrp]
        refine translateFn_mkFn_isSome hpp (trC_append hb ?_) (by simp)
        split
        · exact trC_nil
        · exact trC_cons (isSome_asgn (okV_getD hpv j) (isSome_pv hrv)) trC_nil
    | none =>
        simp only [finish, hrp]
        have hrt : sig.result.2.toSType = styOf t := by
          simp only [JazzSig.fitsB, hrp, Bool.and_eq_true, beq_iff_eq] at hfit
          exact hfit.2.2
        have hrr : OkV (mkV 'r' r.depth sig.result.2.toSType) := okV_mkV (hrt ▸ htt)
        refine translateFn_mkFn_isSome hpp
          (trC_append hb (trC_cons (isSome_asgn hrr (isSome_pv hrv)) trC_nil)) ?_
        simpa using hrr
  rw [translateUnit_mkUnit _ _ hfd]; rfl

end CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
