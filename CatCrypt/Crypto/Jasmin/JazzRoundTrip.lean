/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JazzPrint
public import CatCrypt.Crypto.Jasmin.JazzToInstrR
public meta import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.JazzUnit
public meta import CatCrypt.Crypto.Jasmin.JazzPrint
public meta import CatCrypt.Crypto.Jasmin.JazzToInstrR
public import CatCryptCore.Tactics.KatGuard

/-!
# The printed text of a unit parses back to the unit

`print` (`JazzPrint`) and `parseUnit` (`JazzToInstrR`) are related per unit: the gate
`printChecked u` prints `u`, parses the text and returns it only when the parse is the
erasure `u.erase`, the information the text carries. `erase` sets assignment tags to
`AT_none`, call inline information to `DoNotInline`, variable information to `{}`, the
type of each `_` output of an intrinsic to its `asmOutTys` entry (else `u64`), deletes
the assignments `x = Parr_init n` (printed as comments) and the extern signatures
(which have no text), and keeps everything else.

The Boolean equalities `pexprBEq`, `instrsBEq` and `funDeclBEq` of `JazzToInstrR` are
sound, and so is `unitBEq`; `printChecked_sound` is the resulting guarantee.

## Main definitions

* `Cmd.erase`, `JazzUnit.erase`: the erasure of a command and of a unit.
* `unitBEq`: structural equality of units.
* `printChecked`: the printed text of a unit when it parses back to the erasure.
* `printCheckedWhy`: the first difference between the parse of the text and the
  erasure, or the parse error, when `printChecked` refuses.

## Main results

* `JazzUnit.erase_erase`: erasure is idempotent.
* `JazzToInstrR.pexprBEq_sound`, `JazzToInstrR.instrsBEq_sound`, `unitBEq_sound`:
  the Boolean equalities imply equality.
* `printChecked_sound`: a text returned by `printChecked u` is `print u` and parses to
  `u.erase`.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JazzToInstrR

open CatCrypt.Crypto.Jasmin

/-! ## Soundness of the Boolean equalities -/

theorem varIBEq_sound {x y : VarI} (h : varIBEq x y = true) : x = y := by
  cases x; cases y
  simp only [varIBEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1 h2; rfl

theorem gvarBEq_sound {x y : GVar} (h : gvarBEq x y = true) : x = y := by
  cases x; cases y
  simp only [gvarBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [varIBEq_sound h1, h2]

mutual
theorem pexprBEq_sound {a b : PExpr} (h : pexprBEq a b = true) : a = b := by
  cases a <;> cases b <;>
    simp only [pexprBEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
  case Pconst.Pconst => rw [h]
  case Pbool.Pbool => rw [h]
  case Parr_init.Parr_init => rw [h]
  case Pvar.Pvar => rw [gvarBEq_sound h]
  case Pget.Pget =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h2, gvarBEq_sound h3, pexprBEq_sound h4]
  case Psub.Psub =>
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, gvarBEq_sound h4, pexprBEq_sound h5]
  case Pload.Pload =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, varIBEq_sound h2, pexprBEq_sound h3]
  case Papp1.Papp1 =>
    obtain ⟨h1, h2⟩ := h
    rw [h1, pexprBEq_sound h2]
  case Papp2.Papp2 =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, pexprBEq_sound h2, pexprBEq_sound h3]
  case PappN.PappN =>
    obtain ⟨h1, h2⟩ := h
    rw [h1, pexprsBEq_sound h2]
  case Pif.Pif =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, pexprBEq_sound h2, pexprBEq_sound h3, pexprBEq_sound h4]

theorem pexprsBEq_sound {as bs : List PExpr} (h : pexprsBEq as bs = true) : as = bs := by
  cases as <;> cases bs <;>
    simp only [pexprsBEq, Bool.and_eq_true, Bool.false_eq_true] at h
  case nil.nil => rfl
  case cons.cons =>
    obtain ⟨h1, h2⟩ := h
    rw [pexprBEq_sound h1, pexprsBEq_sound h2]
end

theorem lvalBEq_sound {a b : LVal} (h : lvalBEq a b = true) : a = b := by
  cases a <;> cases b <;>
    simp only [lvalBEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
  case Lnone.Lnone => rw [h.1, h.2]
  case Lvar.Lvar => rw [varIBEq_sound h]
  case Lmem.Lmem =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [h1, varIBEq_sound h2, pexprBEq_sound h3]
  case Laset.Laset =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h2, varIBEq_sound h3, pexprBEq_sound h4]
  case Lasub.Lasub =>
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [h1, h2, h3, varIBEq_sound h4, pexprBEq_sound h5]

theorem lvalsBEq_sound {as bs : List LVal} (h : lvalsBEq as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [lvalsBEq]
  | cons a as ih =>
    cases bs with
    | nil => simp [lvalsBEq] at h
    | cons b bs =>
      simp only [lvalsBEq, Bool.and_eq_true] at h
      rw [lvalBEq_sound h.1, ih h.2]

theorem range_eq {r r' : Range} (h1 : r.dir = r'.dir) (h2 : r.lo = r'.lo)
    (h3 : r.hi = r'.hi) : r = r' := by
  cases r; cases r'; simp_all

mutual
theorem instrBEq_sound {a b : InstrR} (h : instrBEq a b = true) : a = b := by
  cases a <;> cases b <;>
    simp only [instrBEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.false_eq_true] at h
  case Cassgn.Cassgn =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [lvalBEq_sound h1, h2, h3, pexprBEq_sound h4]
  case Copn.Copn =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [lvalsBEq_sound h1, h2, h3, pexprsBEq_sound h4]
  case Cif.Cif =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [pexprBEq_sound h1, instrsBEq_sound h2, instrsBEq_sound h3]
  case Cfor.Cfor =>
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [varIBEq_sound h1, range_eq h2 h3 h4, instrsBEq_sound h5]
  case Cwhile.Cwhile =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [instrsBEq_sound h1, pexprBEq_sound h2, instrsBEq_sound h3]
  case Ccall.Ccall =>
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, lvalsBEq_sound h2, h3, pexprsBEq_sound h4]

theorem instrsBEq_sound {a b : List InstrR} (h : instrsBEq a b = true) : a = b := by
  cases a <;> cases b <;>
    simp only [instrsBEq, Bool.and_eq_true, Bool.false_eq_true] at h
  case nil.nil => rfl
  case cons.cons =>
    obtain ⟨h1, h2⟩ := h
    rw [instrBEq_sound h1, instrsBEq_sound h2]
end

/-- Two lists of variables of equal length whose pairs are equal by `varIBEq` are
equal. -/
theorem varIs_eq_of_zip {as bs : List VarI} (hl : as.length = bs.length)
    (h : (as.zip bs).all (fun p => varIBEq p.1 p.2) = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [varIBEq_sound h.1, ih hl h.2]

/-- Two parameter lists with the same variables are equal. -/
theorem funParams_eq_of_map {ps ps' : List FunParam}
    (h : ps.map (·.var) = ps'.map (·.var)) : ps = ps' := by
  induction ps generalizing ps' with
  | nil => cases ps' <;> simp_all
  | cons p ps ih =>
    cases ps' with
    | nil => simp at h
    | cons q qs =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      cases p; cases q
      simp only at h1
      rw [h1, ih h2]

theorem funDeclBEq_sound {f g : FunDecl} (h : funDeclBEq f g = true) : f = g := by
  obtain ⟨n, ps, b, rs⟩ := f
  obtain ⟨n', ps', b', rs'⟩ := g
  simp only [funDeclBEq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hp : ps.map (·.var) = ps'.map (·.var) := varIs_eq_of_zip h2 h3
  rw [h1, funParams_eq_of_map hp, instrsBEq_sound h4, varIs_eq_of_zip h5 h6]

end CatCrypt.Crypto.Jasmin.JazzToInstrR

namespace CatCrypt.Crypto.Jasmin.Jazz

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JazzToInstrR (parseUnit pexprBEq instrBEq instrsBEq funDeclBEq
  retypeOpnLvs retypeGo opnNoneTys)

/-! ## Erasure -/

/-- A variable with its information erased. -/
def eraseVarI (x : VarI) : VarI := { var := x.var }

/-- A global-variable reference with its information erased. -/
def eraseGVar (x : GVar) : GVar := { gv := eraseVarI x.gv, gs := x.gs }

mutual
/-- The erasure of an expression: every variable's information is `{}`. -/
def eraseExpr : PExpr → PExpr
  | .Pconst z => .Pconst z
  | .Pbool b => .Pbool b
  | .Parr_init n => .Parr_init n
  | .Pvar x => .Pvar (eraseGVar x)
  | .Pget aa ws x i => .Pget aa ws (eraseGVar x) (eraseExpr i)
  | .Psub aa ws n x i => .Psub aa ws n (eraseGVar x) (eraseExpr i)
  | .Pload ws x o => .Pload ws (eraseVarI x) (eraseExpr o)
  | .Papp1 op e => .Papp1 op (eraseExpr e)
  | .Papp2 op a b => .Papp2 op (eraseExpr a) (eraseExpr b)
  | .PappN op es => .PappN op (eraseExprs es)
  | .Pif t c a b => .Pif t (eraseExpr c) (eraseExpr a) (eraseExpr b)

/-- The erasure of a list of expressions. -/
def eraseExprs : List PExpr → List PExpr
  | [] => []
  | e :: es => eraseExpr e :: eraseExprs es
end

/-- The erasure of an l-value: variable information `{}`, and `_` at type `u64`. -/
def eraseLval : LVal → LVal
  | .Lnone _ _ => .Lnone {} (.sword .U64)
  | .Lvar x => .Lvar (eraseVarI x)
  | .Lmem ws x o => .Lmem ws (eraseVarI x) (eraseExpr o)
  | .Laset aa ws x i => .Laset aa ws (eraseVarI x) (eraseExpr i)
  | .Lasub aa ws n x i => .Lasub aa ws n (eraseVarI x) (eraseExpr i)

/-- The name of an intrinsic. -/
def opnName : SOpn → String
  | .Oasm op => op.name

/-- Whether an instruction is an assignment `x = Parr_init n`. -/
def isZeroInit : InstrR → Bool
  | .Cassgn (.Lvar _) _ _ (.Parr_init _) => true
  | _ => false

mutual
/-- The erasure of an instruction: tags `AT_none`, calls `DoNotInline`, variable
information `{}`, and the `_` outputs of an intrinsic typed by `asmOutTys`. -/
def eraseInstr : InstrR → InstrR
  | .Cassgn lv _ ty e => .Cassgn (eraseLval lv) .AT_none ty (eraseExpr e)
  | .Copn lvs _ op es =>
    .Copn (retypeOpnLvs (opnName op) (lvs.map eraseLval)) .AT_none op (eraseExprs es)
  | .Cif c th el => .Cif (eraseExpr c) (Cmd.erase th) (Cmd.erase el)
  | .Cfor v r b => .Cfor (eraseVarI v) r (Cmd.erase b)
  | .Cwhile pre c post => .Cwhile (Cmd.erase pre) (eraseExpr c) (Cmd.erase post)
  | .Ccall _ lvs fn args => .Ccall .DoNotInline (lvs.map eraseLval) fn (eraseExprs args)

/-- The erasure of a command: each instruction erased, the assignments
`x = Parr_init n` deleted. -/
def Cmd.erase : Cmd → Cmd
  | [] => []
  | i :: is => if isZeroInit i then Cmd.erase is else eraseInstr i :: Cmd.erase is
end

/-- The erasure of a function declaration. -/
def FunDecl.erase (fd : FunDecl) : FunDecl :=
  { name := fd.name, params := fd.params.map (fun p => ⟨eraseVarI p.var⟩),
    body := Cmd.erase fd.body, results := fd.results.map eraseVarI }

/-- The erasure of a function of a unit. -/
def JazzFn.erase (f : JazzFn) : JazzFn := { f with fd := FunDecl.erase f.fd }

/-- The erasure of a unit: its functions erased, no extern signatures. -/
def JazzUnit.erase (u : JazzUnit) : JazzUnit := { externs := [], fns := u.fns.map JazzFn.erase }

/-! ## Erasure is idempotent -/

theorem eraseVarI_eraseVarI (x : VarI) : eraseVarI (eraseVarI x) = eraseVarI x := rfl

theorem eraseGVar_eraseGVar (x : GVar) : eraseGVar (eraseGVar x) = eraseGVar x := rfl

mutual
theorem eraseExpr_eraseExpr (e : PExpr) : eraseExpr (eraseExpr e) = eraseExpr e := by
  cases e <;> simp only [eraseExpr, eraseGVar_eraseGVar, eraseVarI_eraseVarI]
  case Pget i => rw [eraseExpr_eraseExpr i]
  case Psub i => rw [eraseExpr_eraseExpr i]
  case Pload o => rw [eraseExpr_eraseExpr o]
  case Papp1 e => rw [eraseExpr_eraseExpr e]
  case Papp2 a b => rw [eraseExpr_eraseExpr a, eraseExpr_eraseExpr b]
  case PappN es => rw [eraseExprs_eraseExprs es]
  case Pif c a b => rw [eraseExpr_eraseExpr c, eraseExpr_eraseExpr a, eraseExpr_eraseExpr b]

theorem eraseExprs_eraseExprs (es : List PExpr) : eraseExprs (eraseExprs es) = eraseExprs es := by
  cases es with
  | nil => rfl
  | cons e es => simp only [eraseExprs, eraseExpr_eraseExpr e, eraseExprs_eraseExprs es]
end

theorem eraseLval_eraseLval (lv : LVal) : eraseLval (eraseLval lv) = eraseLval lv := by
  cases lv <;> simp [eraseLval, eraseVarI_eraseVarI, eraseExpr_eraseExpr]

theorem eraseLval_comp_eraseLval : eraseLval ∘ eraseLval = eraseLval :=
  funext eraseLval_eraseLval

theorem map_eraseLval_retypeGo (tys : List SType) (k : Nat) (lvs : List LVal) :
    (retypeGo tys k lvs).map eraseLval = lvs.map eraseLval := by
  induction lvs generalizing k with
  | nil => rfl
  | cons lv lvs ih => cases lv <;> simp [retypeGo, eraseLval, ih]

theorem map_eraseLval_retypeOpnLvs (op : String) (lvs : List LVal) :
    (retypeOpnLvs op lvs).map eraseLval = lvs.map eraseLval :=
  map_eraseLval_retypeGo _ _ _

theorem isZeroInit_eraseInstr (i : InstrR) : isZeroInit (eraseInstr i) = isZeroInit i := by
  cases i with
  | Cassgn lv t ty e => cases lv <;> cases e <;> rfl
  | _ => rfl

mutual
theorem eraseInstr_eraseInstr (i : InstrR) : eraseInstr (eraseInstr i) = eraseInstr i := by
  cases i with
  | Cassgn lv t ty e => simp only [eraseInstr, eraseLval_eraseLval, eraseExpr_eraseExpr]
  | Copn lvs t op es =>
    simp only [eraseInstr, map_eraseLval_retypeOpnLvs, List.map_map, eraseLval_comp_eraseLval,
      eraseExprs_eraseExprs]
  | Cif c th el =>
    simp only [eraseInstr, eraseExpr_eraseExpr, Cmd.erase_erase th, Cmd.erase_erase el]
  | Cfor v r b => simp only [eraseInstr, eraseVarI_eraseVarI, Cmd.erase_erase b]
  | Cwhile pre c post =>
    simp only [eraseInstr, eraseExpr_eraseExpr, Cmd.erase_erase pre, Cmd.erase_erase post]
  | Ccall ii lvs fn args =>
    simp only [eraseInstr, List.map_map, eraseLval_comp_eraseLval, eraseExprs_eraseExprs]

theorem Cmd.erase_erase (c : Cmd) : Cmd.erase (Cmd.erase c) = Cmd.erase c := by
  cases c with
  | nil => rfl
  | cons i is =>
    by_cases h : isZeroInit i = true
    · simp only [Cmd.erase, h, if_true, Cmd.erase_erase is]
    · simp only [Cmd.erase, h, if_false, Bool.false_eq_true, isZeroInit_eraseInstr,
        eraseInstr_eraseInstr i, Cmd.erase_erase is]
end

theorem FunDecl.erase_erase (fd : FunDecl) : FunDecl.erase (FunDecl.erase fd) = FunDecl.erase fd := by
  simp [FunDecl.erase, Cmd.erase_erase, List.map_map, Function.comp_def, eraseVarI]

theorem JazzUnit.erase_erase (u : JazzUnit) : u.erase.erase = u.erase := by
  simp [JazzUnit.erase, JazzFn.erase, List.map_map, Function.comp_def, FunDecl.erase_erase]

/-! ## Structural equality of units -/

/-- Structural equality of functions of a unit. -/
def jazzFnBEq (f g : JazzFn) : Bool :=
  decide (f.preamble = g.preamble) && decide (f.requires = g.requires) &&
  decide (f.kind = g.kind) && funDeclBEq f.fd g.fd && decide (f.paramTys = g.paramTys) &&
  decide (f.resultTys = g.resultTys) && decide (f.decls = g.decls)

/-- Structural equality of lists of functions. -/
def jazzFnsBEq : List JazzFn → List JazzFn → Bool
  | [], [] => true
  | f :: fs, g :: gs => jazzFnBEq f g && jazzFnsBEq fs gs
  | _, _ => false

/-- Structural equality of units. -/
def unitBEq (u v : JazzUnit) : Bool := decide (u.externs = v.externs) && jazzFnsBEq u.fns v.fns

theorem jazzFnBEq_sound {f g : JazzFn} (h : jazzFnBEq f g = true) : f = g := by
  cases f; cases g
  simp only [jazzFnBEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  rw [h1, h2, h3, JazzToInstrR.funDeclBEq_sound h4, h5, h6, h7]

theorem jazzFnsBEq_sound {fs gs : List JazzFn} (h : jazzFnsBEq fs gs = true) : fs = gs := by
  induction fs generalizing gs with
  | nil => cases gs <;> simp_all [jazzFnsBEq]
  | cons f fs ih =>
    cases gs with
    | nil => simp [jazzFnsBEq] at h
    | cons g gs =>
      simp only [jazzFnsBEq, Bool.and_eq_true] at h
      rw [jazzFnBEq_sound h.1, ih h.2]

theorem unitBEq_sound {u v : JazzUnit} (h : unitBEq u v = true) : u = v := by
  cases u; cases v
  simp only [unitBEq, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1, jazzFnsBEq_sound h.2]

/-! ## The gate -/

/-- The printed text of `u` when it parses back to `u.erase`, else `none`. -/
def printChecked (u : JazzUnit) : Option String :=
  match parseUnit (print u) with
  | .ok v => if unitBEq v u.erase then some (print u) else none
  | .error _ => none

theorem printChecked_sound {u : JazzUnit} {s : String} (h : printChecked u = some s) :
    s = print u ∧ parseUnit s = .ok u.erase := by
  unfold printChecked at h
  split at h
  · rename_i v hv
    split at h
    · rename_i hb
      cases h
      exact ⟨rfl, by rw [hv, unitBEq_sound hb]⟩
    · cases h
  · cases h

/-- The first instruction at which two bodies differ, as text naming its index. -/
def firstInstrMismatch : Nat → List InstrR → List InstrR → Option String
  | _, [], [] => none
  | k, a :: as, b :: bs =>
    if instrBEq a b then firstInstrMismatch (k + 1) as bs
    else some s!"instruction {k}: parsed {reprStr a}, expected {reprStr b}"
  | k, as, bs => some s!"instruction {k}: {as.length} parsed and {bs.length} expected remain"

/-- The first difference between two functions. -/
def fnMismatch (f g : JazzFn) : Option String :=
  let pre := s!"function {g.fd.name.name}: "
  if f.preamble != g.preamble then some (pre ++ "preamble")
  else if f.requires != g.requires then some (pre ++ "require lines")
  else if f.kind != g.kind then some (pre ++ "kind")
  else if f.fd.name != g.fd.name then some (pre ++ s!"name {f.fd.name.name}")
  else if f.paramTys != g.paramTys then some (pre ++ "parameter types")
  else if f.resultTys != g.resultTys then some (pre ++ "result types")
  else if f.decls != g.decls then some (pre ++ "declarations")
  else if !funDeclBEq { f.fd with body := [] } { g.fd with body := [] } then
    some (pre ++ "parameters or results")
  else (firstInstrMismatch 0 f.fd.body g.fd.body).map (pre ++ ·)

/-- The first difference between two lists of functions. -/
def fnsMismatch : List JazzFn → List JazzFn → Option String
  | [], [] => none
  | f :: fs, g :: gs => (fnMismatch f g).orElse fun _ => fnsMismatch fs gs
  | fs, gs => some s!"{fs.length} parsed and {gs.length} expected functions remain"

/-- Why `printChecked u` refuses: the parse error of the printed text, or the first
difference between its parse and `u.erase`; `none` when `printChecked u` is `some`. -/
def printCheckedWhy (u : JazzUnit) : Option String :=
  match parseUnit (print u) with
  | .error e => some ("parse error: " ++ e)
  | .ok v =>
    if unitBEq v u.erase then none
    else (fnsMismatch v.fns u.erase.fns).getD "extern signatures"

/-! ## Round trips -/

namespace RoundTrip

/-- The unit of the `bignum_add_4` port with the banner line `Emit.emitFunDecl` prints. -/
def bignumAdd4Unit : JazzUnit where
  fns := BignumAdd4.unit.fns.map fun f =>
    { f with preamble := ["// Auto-generated from CatCrypt Jasmin AST. Do not edit by hand."] }

-- The printed unit of `bignum_add_4` parses back to its erasure.
#kat (printChecked bignumAdd4Unit).isSome

-- The printed unit of `bignum_add_4` is the text `Emit.emitFunDecl` prints for the port.
#kat print bignumAdd4Unit == JazzToInstrR.RoundTrip.bignumAdd4Jazz

/-- A `u64` variable. -/
def u (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A variable of type `t`. -/
def vr (s : String) (t : SType) : Var := { vname := s, vtype := t }

/-- The expression of a local variable. -/
def pv (x : Var) : PExpr := .Pvar { gv := { var := x }, gs := false }

/-- `x = e;` at type `u64`. -/
def asg (x : String) (e : PExpr) : InstrR := .Cassgn (.Lvar { var := u x }) .AT_none (.sword .U64) e

/-- A one-function unit around a body, with the given kind, preamble, requires and
declarations, parameters `p : reg mut ptr u64[4]` and `k : reg u64`, result `x`. -/
def oneFn (kind : FnKind) (pre reqs : List String) (decls : List Decl) (body : Cmd) :
    JazzUnit where
  fns := [{
    preamble := pre
    requires := reqs
    kind := kind
    fd := { name := { name := "f" },
            params := [⟨{ var := vr "p" (.sarr 32) }⟩, ⟨{ var := u "k" }⟩],
            body := body, results := [{ var := u "x" }] }
    paramTys := [(.regPtr true, .arr .U64 4), (.reg, .word .U64)]
    resultTys := [(.reg, .word .U64)]
    decls := decls }]

/-- The declarations `reg u64 x y;`. -/
def xyDecl : Decl := { storage := .reg, ty := .word .U64, names := ["x", "y"] }

-- Storage classes: `reg mut ptr` and `reg` parameters, `stack` array, `reg bool` and
-- `inline int` declarations.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl,
    { storage := .stack, ty := .arr .U64 2, names := ["s"] },
    { storage := .reg, ty := .bool, names := ["c"] },
    { storage := .inlineVar, ty := .int, names := ["i"] }]
  [asg "x" (pv (u "k"))])).isSome

-- `reg const ptr` is read as `regPtr false` and `stack ptr` as `stackPtr`.
#kat match parseUnit "fn g(reg const ptr u32[8] a, stack ptr u8[3] b) { }" with
  | .ok v => v.fns.map (·.paramTys) == [[(.regPtr false, .arr .U32 8), (.stackPtr, .arr .U8 3)]]
  | .error _ => false

-- Function kinds and annotations.
#kat (printChecked (oneFn (.localFn ["returnaddress=stack"]) [] [] [xyDecl]
  [asg "x" (pv (u "k"))])).isSome

#kat (printChecked (oneFn .inlineFn [] [] [xyDecl] [asg "x" (pv (u "k"))])).isSome

-- `require` lines and top-level `//` lines.
#kat (printChecked (oneFn .exportFn ["// first line", "// second line"]
  ["../include/a.jinc", "../include/b.jinc"] [xyDecl] [asg "x" (pv (u "k"))])).isSome

-- The conditional `c ? a : b`.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl]
  [asg "x" (.Pif (.sword .U64) (.Papp2 (.Oeq .U64) (pv (u "k")) (.Pconst 0))
    (pv (u "y")) (pv (u "k")))])).isSome

-- `for i = hi downto lo`.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl,
    { storage := .inlineVar, ty := .int, names := ["i"] }]
  [.Cfor { var := vr "i" .sint } { dir := .DownTo, lo := 0, hi := 3 }
    [asg "x" (.Pget .AAscale .U64 { gv := { var := vr "p" (.sarr 32) }, gs := false }
      (pv (vr "i" .sint)))]])).isSome

-- `_` outputs typed by `asmOutTys`: the flags of `ADD_64` are `bool`; the AST types them
-- `u64`, and the erasure retypes them.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl,
    { storage := .reg, ty := .bool, names := ["c"] }]
  [.Copn [.Lnone {} (.sword .U64), .Lvar { var := vr "c" .sbool }, .Lnone {} (.sword .U64),
      .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lvar { var := u "x" }]
    .AT_none (.Oasm ⟨"ADD_64"⟩) [pv (u "k"), pv (u "y")]])).isSome

-- A zero-initialised array prints as a comment and is erased.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl,
    { storage := .stack, ty := .arr .U64 2, names := ["s"] }]
  [.Cassgn (.Lvar { var := vr "s" (.sarr 16) }) .AT_none (.sarr 16) (.Parr_init 16),
   asg "x" (pv (u "k"))])).isSome

-- A unit with an expression without surface syntax is refused, and the reason names the
-- parse error.
#kat (printChecked (oneFn .exportFn [] [] [xyDecl]
  [asg "x" (.Papp1 (.Oneg .U64) (pv (u "k")))])).isNone &&
  (printCheckedWhy (oneFn .exportFn [] [] [xyDecl]
    [asg "x" (.Papp1 (.Oneg .U64) (pv (u "k")))])).isSome

end RoundTrip

end CatCrypt.Crypto.Jasmin.Jazz
