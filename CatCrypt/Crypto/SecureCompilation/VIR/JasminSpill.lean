/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminSpillPass

/-!
# Properties of the spill pass for straight-line Jasmin functions

The pass `spillFn k` (`JasminSpillPass`) rewrites a function whose body is straight line so
that at most `k` register variables of a general-purpose word type are live at each
instruction, spilling to fresh `stack` variables and rematerialising stable right-hand
sides. This module proves that it keeps well-formedness and the translation to the
`psem.v` mirror, that it preserves the semantics of the mirror, and that it meets the
liveness bound; it then states the well-formedness and the translation of the units of the
lowering `NFToJasmin.nfToJasmin`, which applies the pass.

## Main results

* `liveRegsB_sound`: `liveRegsB k fn = true` implies `LiveRegs k fn`.
* `liveRegsB_spillFn`: the pass establishes `liveRegsB k` on a straight-line body without
  fresh-prefix names whose register demand fits in `k` (`DemandOK`: the registers live
  before the body, the operands and outputs of each instruction, twice the largest operand
  count plus one, and the register results with one reload).
* `spillFn_wellFormed`, `spillUnit_wellFormed`: the pass keeps `wellFormedB`.
* `translateFn_isSome_spill`, `translateUnit_isSome_spill`: the spilled function and unit
  translate to the `psem.v` mirror whenever the original does.
* `spillFn_sem`: a run of the typed translation of the original body from `s` to `s'` gives
  a run of the typed translation of the spilled body from `s` to a state with the memory and
  syscall state of `s'` that agrees with `s'` on every variable whose name does not start
  with `spl_`. The hypotheses are that every defined value of `s` has the type of its
  variable (`WT`) and that the results are defined in `s'`. The mirror's `setVar` stores a
  value without truncating it to the variable's type, so a store `s = h` of a spilled
  value preserves it only when it has that type; the mirror does not distinguish storage
  classes, so a `stack` variable and a `reg` variable hold values alike.

* `NFToJasmin.nfToJasmin_wellFormed`, `InstrRTranslateJazz.translateUnit_isSome_of_nfToJasmin`:
  every unit the lowering `nfToJasmin` returns, after the pass, is well formed and
  translates to the mirror.

The simulation relates the two runs by `SI`: holders hold the value of their variable,
stack variables the stored value, and rematerialised right-hand sides evaluate to it. The
liveness proof builds a register certificate (`CertC`) from the holders of the pass state.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Jazz

/-! ## 4. Renaming in the mirror -/

section MirrorRen

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem GlobDecls JResult truncateVal
  evalAtype MemModel semPexpr getVar)

/-- A local mirror variable renamed by `R`, a global one unchanged. -/
def mrenG (R : MVar → MVar) (g : MGVar) : MGVar :=
  match g.gs with
  | .Slocal => { g with gv := { g.gv with v_var := R g.gv.v_var } }
  | .Sglob => g

/-- The mirror expression with the local reads of the translated fragment renamed. -/
def mrenE (R : MVar → MVar) : MPexpr → MPexpr
  | .Pvar g => .Pvar (mrenG R g)
  | .Pget al aa ws x i => .Pget al aa ws (mrenG R x) (mrenE R i)
  | .Papp1 op e => .Papp1 op (mrenE R e)
  | .Papp2 op a b => .Papp2 op (mrenE R a) (mrenE R b)
  | e => e

/-- The local variable a mirror variable read names. -/
def mlocal (g : MGVar) : List MVar :=
  match g.gs with
  | .Slocal => [g.gv.v_var]
  | .Sglob => []

/-- The local reads of a mirror expression of the translated fragment. -/
def mreads : MPexpr → List MVar
  | .Pvar g => mlocal g
  | .Pget _ _ _ x i => mlocal x ++ mreads i
  | .Papp1 _ e => mreads e
  | .Papp2 _ a b => mreads a ++ mreads b
  | _ => []

/-- The translated fragment of mirror expressions. -/
def mfrag : MPexpr → Bool
  | .Pconst _ => true
  | .Pbool _ => true
  | .Parr_init _ _ => true
  | .Pvar _ => true
  | .Pget _ _ _ _ i => mfrag i
  | .Papp1 _ e => mfrag e
  | .Papp2 _ a b => mfrag a && mfrag b
  | _ => false

theorem typeE_mrenE (R : MVar → MVar) : ∀ (ty : MAtype) (a : MPexpr),
    typeE ty (mrenE R a) = mrenE R (typeE ty a)
  | ty, .Pconst z => by cases ty <;> rfl
  | _, .Pbool _ => rfl
  | _, .Parr_init _ _ => rfl
  | _, .Pvar _ => rfl
  | _, .Pget al aa ws x i => by
      simp only [mrenE, typeE, typeE_mrenE R .aint i]
  | _, .Psub _ _ _ _ _ => rfl
  | _, .Pload _ _ _ => rfl
  | _, .Papp1 op e => by
      simp only [mrenE, typeE, typeE_mrenE R (op1Ty op) e]
  | _, .Papp2 op a b => by
      simp only [mrenE, typeE, typeE_mrenE R (op2Tys op).1 a, typeE_mrenE R (op2Tys op).2 b]
  | _, .PappN _ _ => rfl
  | _, .Pif _ _ _ _ => rfl

theorem mreads_typeE : ∀ (ty : MAtype) (a : MPexpr), mreads (typeE ty a) = mreads a
  | ty, .Pconst z => by cases ty <;> rfl
  | _, .Pbool _ => rfl
  | _, .Parr_init _ _ => rfl
  | _, .Pvar _ => rfl
  | _, .Pget al aa ws x i => by simp only [typeE, mreads, mreads_typeE .aint i]
  | _, .Psub _ _ _ _ _ => rfl
  | _, .Pload _ _ _ => rfl
  | _, .Papp1 op e => by simp only [typeE, mreads, mreads_typeE (op1Ty op) e]
  | _, .Papp2 op a b => by
      simp only [typeE, mreads, mreads_typeE (op2Tys op).1 a, mreads_typeE (op2Tys op).2 b]
  | _, .PappN _ _ => rfl
  | _, .Pif _ _ _ _ => rfl

theorem mfrag_typeE : ∀ (ty : MAtype) (a : MPexpr), mfrag a = true → mfrag (typeE ty a) = true
  | ty, .Pconst z, _ => by cases ty <;> rfl
  | _, .Pbool _, _ => rfl
  | _, .Parr_init _ _, _ => rfl
  | _, .Pvar _, _ => rfl
  | _, .Pget al aa ws x i, h => by
      simp only [mfrag] at h; simp only [typeE, mfrag, mfrag_typeE .aint i h]
  | _, .Papp1 op e, h => by
      simp only [mfrag] at h; simp only [typeE, mfrag, mfrag_typeE (op1Ty op) e h]
  | _, .Papp2 op a b, h => by
      simp only [mfrag, Bool.and_eq_true] at h
      simp only [typeE, mfrag, mfrag_typeE _ a h.1, mfrag_typeE _ b h.2, Bool.and_self]

variable {SyscallState Mem : Type} [MemModel Mem] (gd : GlobDecls) (opS : OpSem)

omit [MemModel Mem] in
theorem getGvar_mrenG (R : MVar → MVar) (t o : Estate SyscallState Mem) (g : MGVar)
    (h : ∀ v ∈ mlocal g, t.evm (R v) = o.evm v) :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar true gd t.evm (mrenG R g) =
      CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar true gd o.evm g := by
  rcases g with ⟨⟨v, _⟩, gs⟩
  cases gs with
  | Slocal =>
      have := h v (by simp [mlocal])
      simp [mrenG, CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar,
        CatCrypt.Crypto.Jasmin.CoqSemMirror.GVar.isLvar, getVar, Vm.get, this]
  | Sglob => rfl

/-- **Renaming in the mirror.** An expression of the fragment renamed by `R` evaluates in `t`
as the expression does in `o` when each local read `v` has in `t` at `R v` the value it has
in `o`. -/
theorem semPexpr_mrenE (R : MVar → MVar) (t o : Estate SyscallState Mem) :
    ∀ a : MPexpr, mfrag a = true → (∀ v ∈ mreads a, t.evm (R v) = o.evm v) →
      semPexpr true gd opS t (mrenE R a) = semPexpr true gd opS o a
  | .Pconst _, _, _ => rfl
  | .Pbool _, _, _ => rfl
  | .Parr_init _ _, _, _ => rfl
  | .Pvar g, _, h => by
      simp only [mrenE, semPexpr]
      exact getGvar_mrenG gd R t o g h
  | .Pget al aa ws x i, hf, h => by
      simp only [mfrag] at hf
      have hx := getGvar_mrenG gd R t o x (fun v hv => h v (by simp [mreads, hv]))
      have hi := semPexpr_mrenE R t o i hf (fun v hv => h v (by simp [mreads, hv]))
      simp only [mrenE, semPexpr, hx, hi]
  | .Papp1 op e, hf, h => by
      simp only [mfrag] at hf
      have he := semPexpr_mrenE R t o e hf (fun v hv => h v (by simpa [mreads] using hv))
      simp only [mrenE, semPexpr, he]
  | .Papp2 op a b, hf, h => by
      simp only [mfrag, Bool.and_eq_true] at hf
      have ha := semPexpr_mrenE R t o a hf.1 (fun v hv => h v (by simp [mreads, hv]))
      have hb := semPexpr_mrenE R t o b hf.2 (fun v hv => h v (by simp [mreads, hv]))
      simp only [mrenE, semPexpr, ha, hb]

end MirrorRen

/-! ## 5. The translation of renamed expressions -/

section TransRen

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt

theorem translateWSize_inj : ∀ {a b : AWSize} {w : MWSize},
    translateWSize a = some w → translateWSize b = some w → a = b := by
  intro a b w ha hb
  cases a <;> cases b <;> simp only [translateWSize, Option.some.injEq, reduceCtorEq] at ha hb <;>
    first | rfl | (subst ha; cases hb)

theorem translateSTypeExt_inj {a b : ASType} {t : MAtype}
    (ha : translateSTypeExt a = some t) (hb : translateSTypeExt b = some t) : a = b := by
  cases a <;> cases b <;>
    simp_all [translateSTypeExt, translateSType, Option.map_eq_some_iff] <;>
    first
    | (obtain ⟨w, hw, rfl⟩ := ha; obtain ⟨w', hw', h⟩ := hb; cases h
       exact translateWSize_inj hw hw')
    | (obtain ⟨w, hw, rfl⟩ := ha; simp_all)

/-- The translation of variables is injective. -/
theorem translateVarExt_inj {x y : AVar} {v : MVar} (hx : translateVarExt x = some v)
    (hy : translateVarExt y = some v) : x = y := by
  rcases x with ⟨xn, xt⟩
  rcases y with ⟨yn, yt⟩
  simp only [translateVarExt, Option.map_eq_some_iff] at hx hy
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨t', ht', h⟩ := hy
  simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.Var.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [translateSTypeExt_inj ht ht']

/-- Variables of the same type translate together. -/
theorem translateVarExt_isSome_of_vtype {x y : AVar} (h : x.vtype = y.vtype) :
    (translateVarExt x).isSome = (translateVarExt y).isSome := by
  simp [translateVarExt, h]

variable (r : AVar → AVar) (R : MVar → MVar)

/-- `r` renames AST variables at their types and `R` is its image in the mirror. -/
structure RenOK : Prop where
  ty : ∀ x, (r x).vtype = x.vtype
  tr : ∀ x x', translateVarExt x = some x' → translateVarExt (r x) = some (R x')

variable {r R}

theorem translateGVarExt_renG (h : RenOK r R) (g : AGVar) :
    translateGVarExt (renG r g) = (translateGVarExt g).map (mrenG R) := by
  rcases g with ⟨⟨x, inf⟩, gs⟩
  cases gs with
  | true => cases hx : translateVarExt x <;> simp [renG, translateGVarExt, translateVarIExt, hx, mrenG]
  | false =>
      cases hx : translateVarExt x with
      | none =>
          have : translateVarExt (r x) = none := by
            have := translateVarExt_isSome_of_vtype (h.ty x); simp_all
          simp [renG, translateGVarExt, translateVarIExt, hx, this]
      | some x' =>
          simp [renG, translateGVarExt, translateVarIExt, hx, h.tr x x' hx, mrenG]

theorem translateIdx_renE_of (h : RenOK r R) (e : APExpr)
    (he : translatePExprExt (renE r e) = (translatePExprExt e).map (mrenE R)) :
    translateIdx (renE r e) = (translateIdx e).map (mrenE R) := by
  unfold translateIdx
  cases e with
  | Pvar g =>
      have hty : (renG r g).gv.var.vtype = g.gv.var.vtype := by
        unfold renG; split <;> simp [h.ty]
      simp only [renE] at he ⊢
      simp only [intOfWordIdx, hty, translateGVarExt_renG h g]
      split
      · cases translateGVarExt g <;> rfl
      · exact he
  | _ => simp only [renE] at he ⊢; simpa [intOfWordIdx] using he

/-- **Renaming commutes with the translation.** -/
theorem translatePExprExt_renE (h : RenOK r R) : ∀ e : APExpr,
    translatePExprExt (renE r e) = (translatePExprExt e).map (mrenE R)
  | .Pconst _ => rfl
  | .Pbool _ => rfl
  | .Parr_init _ => rfl
  | .Pvar g => by
      simp only [renE, translatePExprExt, translateGVarExt_renG h g]
      cases translateGVarExt g <;> rfl
  | .Pget aa ws x i => by
      have hi := translateIdx_renE_of h i (translatePExprExt_renE h i)
      rw [renE, translatePExprExt_pget, translatePExprExt_pget, hi, translateGVarExt_renG h x]
      cases translateWSize ws <;> cases translateGVarExt x <;> cases translateIdx i <;> rfl
  | .Psub _ _ _ _ _ => rfl
  | .Pload _ _ _ => rfl
  | .Papp1 op e => by
      simp only [renE, translatePExprExt, translatePExprExt_renE h e]
      cases translateSOp1 op <;> cases translatePExprExt e <;> rfl
  | .Papp2 op a b => by
      simp only [renE, translatePExprExt, translatePExprExt_renE h a, translatePExprExt_renE h b]
      cases translateSOp2Ext op <;> cases translatePExprExt a <;> cases translatePExprExt b <;> rfl
  | .PappN _ _ => rfl
  | .Pif _ _ _ _ => rfl

theorem translateIdx_renE (h : RenOK r R) (e : APExpr) :
    translateIdx (renE r e) = (translateIdx e).map (mrenE R) :=
  translateIdx_renE_of h e (translatePExprExt_renE h e)

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {m : List β}, l.mapM f = some m → ∀ x ∈ l, ∃ y ∈ m, f x = some y
  | [], _, _, x, hx => by simp at hx
  | a :: l, m, h, x, hx => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp, hb⟩
      · obtain ⟨y, hy, hfy⟩ := mapM_some_mem hbs x hx
        exact ⟨y, by simp [hy], hfy⟩

theorem exists_of_mem_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {m : List β}, l.mapM f = some m → ∀ y ∈ m, ∃ x ∈ l, f x = some y
  | [], m, h, y, hy => by simp at h; subst h; simp at hy
  | a :: l, m, h, y, hy => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, by simp, hb⟩
      · obtain ⟨x, hx, hfx⟩ := exists_of_mem_mapM_some hbs y hy
        exact ⟨x, by simp [hx], hfx⟩

theorem mapM_append_some {α β : Type} {f : α → Option β} {l1 l2 : List α} {m1 m2 : List β}
    (h1 : l1.mapM f = some m1) (h2 : l2.mapM f = some m2) : (l1 ++ l2).mapM f = some (m1 ++ m2) := by
  simp [List.mapM_append, h1, h2]

theorem mreads_mlocal_of {g : AGVar} {g' : MGVar} (h : translateGVarExt g = some g') :
    (if g.gs then [] else [g.gv.var]).mapM translateVarExt = some (mlocal g') := by
  rcases g with ⟨⟨x, inf⟩, gs⟩
  simp only [translateGVarExt, translateVarIExt, Option.map_map, Option.map_eq_some_iff,
    Function.comp_def] at h
  obtain ⟨x', hx', rfl⟩ := h
  cases gs <;> simp [mlocal, hx']

theorem translateIdx_of {e : APExpr} {b : MPexpr} (h : translateIdx e = some b)
    (ih : ∀ b', translatePExprExt e = some b' → mfrag b' = true ∧
      (readsE e).mapM translateVarExt = some (mreads b')) :
    mfrag b = true ∧ (readsE e).mapM translateVarExt = some (mreads b) := by
  unfold translateIdx intOfWordIdx at h
  cases e with
  | Pvar g =>
      by_cases hty : g.gv.var.vtype = .sword .U64
      · simp only [hty, if_true, Option.map_eq_some_iff] at h
        obtain ⟨g', hg', rfl⟩ := h
        exact ⟨rfl, by simpa [readsE, mreads] using mreads_mlocal_of hg'⟩
      · simp only [hty, if_false] at h
        exact ih b h
  | _ => exact ih b h

/-- A translated expression is in the fragment, and its local reads are the translations of
those of the expression. -/
theorem translatePExprExt_of : ∀ (e : APExpr) (b : MPexpr), translatePExprExt e = some b →
    mfrag b = true ∧ (readsE e).mapM translateVarExt = some (mreads b)
  | .Pconst _, b, h => by
      simp [translatePExprExt, InstrRTranslate.translatePExpr] at h; subst h
      simp [mfrag, readsE, mreads]
  | .Pbool _, b, h => by
      simp [translatePExprExt, InstrRTranslate.translatePExpr] at h; subst h
      simp [mfrag, readsE, mreads]
  | .Parr_init _, b, h => by simp [translatePExprExt] at h; subst h; simp [mfrag, readsE, mreads]
  | .Pvar g, b, h => by
      simp only [translatePExprExt, Option.map_eq_some_iff] at h
      obtain ⟨g', hg', rfl⟩ := h
      exact ⟨rfl, by simpa [readsE, mreads] using mreads_mlocal_of hg'⟩
  | .Pget aa ws x i, b, h => by
      rw [translatePExprExt_pget] at h
      cases hw : translateWSize ws <;> cases hx : translateGVarExt x <;>
        cases hi : translateIdx i <;> simp only [hw, hx, hi, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨hf, hr⟩ := translateIdx_of hi (translatePExprExt_of i)
      exact ⟨hf, by simpa [readsE, mreads] using mapM_append_some (mreads_mlocal_of hx) hr⟩
  | .Psub _ _ _ _ _, b, h => by simp [translatePExprExt, InstrRTranslate.translatePExpr] at h
  | .Pload _ _ _, b, h => by simp [translatePExprExt, InstrRTranslate.translatePExpr] at h
  | .Papp1 op e, b, h => by
      simp only [translatePExprExt] at h
      cases ho : translateSOp1 op <;> cases he : translatePExprExt e <;>
        simp only [ho, he, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨hf, hr⟩ := translatePExprExt_of e _ he
      exact ⟨hf, by simpa [readsE, mreads] using hr⟩
  | .Papp2 op a c, b, h => by
      simp only [translatePExprExt] at h
      cases ho : translateSOp2Ext op <;> cases ha : translatePExprExt a <;>
        cases hc : translatePExprExt c <;>
        simp only [ho, ha, hc, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨hfa, hra⟩ := translatePExprExt_of a _ ha
      obtain ⟨hfc, hrc⟩ := translatePExprExt_of c _ hc
      exact ⟨by simp [mfrag, hfa, hfc], by simpa [readsE, mreads] using mapM_append_some hra hrc⟩
  | .PappN _ _, b, h => by simp [translatePExprExt, InstrRTranslate.translatePExpr] at h
  | .Pif _ _ _ _, b, h => by simp [translatePExprExt, InstrRTranslate.translatePExpr] at h

theorem translateIdx_frag_reads {e : APExpr} {b : MPexpr} (h : translateIdx e = some b) :
    mfrag b = true ∧ (readsE e).mapM translateVarExt = some (mreads b) :=
  translateIdx_of h (translatePExprExt_of e)

end TransRen

/-! ## 6. Writes in the mirror -/

section MirrorWrite

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem GlobDecls JResult truncateVal
  evalAtype MemModel semPexpr getVar setVar writeLval writeLvals DB truncatable
  JArrayMirror)

theorem bind_eq_ok {α β : Type} {r : JResult α} {f : α → JResult β} {c : β}
    (h : JResult.bind r f = .ok c) : ∃ a, r = .ok a ∧ f a = .ok c := by
  cases r <;> simp_all [JResult.bind]

/-- Every defined value of a variable map has the type of its variable. -/
def WT (vm : Vm) : Prop :=
  ∀ v : MVar, (vm v).isDefined = true → (vm v).typeOf = evalAtype v.vtype

theorem setVar_ok {vm vm1 : Vm} {x : MVar} {v : Value} (h : setVar true vm x v = .ok vm1) :
    vm1 = vm.set x v ∧ DB v = true ∧ truncatable (evalAtype x.vtype) v = true ∧
      ∀ vm' : Vm, setVar true vm' x v = .ok (vm'.set x v) := by
  obtain ⟨xt, xn⟩ := x
  unfold setVar at h ⊢
  cases xt <;> simp only [evalAtype] at h ⊢ <;> split_ifs at h with h1 h2 <;> simp_all

theorem WT.set {vm : Vm} (h : WT vm) {x : MVar} {v : Value}
    (ht : truncatable (evalAtype x.vtype) v = true) : WT (vm.set x v) := by
  intro u hu
  by_cases hux : u = x
  · subst hux
    simp only [Vm.set, decide_true, if_true] at hu ⊢
    simp only [truncatable, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ht
    rcases ht with ht | ht
    · exact ht
    · simp [ht] at hu
  · simp only [Vm.set, hux, decide_false] at hu ⊢
    exact h u hu

variable {SyscallState Mem : Type} [MemModel Mem] (gd : GlobDecls) (opS : OpSem)

omit [MemModel Mem] in
theorem writeVar_ok {s s1 : Estate SyscallState Mem} {x : MVarI} {v : Value}
    (h : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true x v s = .ok s1) :
    s1 = s.withVm (s.evm.set x.v_var v) ∧ truncatable (evalAtype x.v_var.vtype) v = true ∧
      DB v = true ∧
      ∀ s' : Estate SyscallState Mem, CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true x v s' = .ok (s'.withVm (s'.evm.set x.v_var v)) := by
  unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar at h
  simp only [JResult.monad_bind_eq] at h
  obtain ⟨vm, hvm, h⟩ := bind_eq_ok h
  obtain ⟨rfl, hdb, ht, hall⟩ := setVar_ok hvm
  refine ⟨?_, ht, hdb, fun s' => ?_⟩
  · simpa using h.symm
  · unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar; simp only [JResult.monad_bind_eq, hall]; rfl

/-- The array value an array write `x[i] = v` produces from the value `vr` of `x` and the
value `vi` of the index. -/
def lasetVal (al : CatCrypt.Crypto.Jasmin.CoqSemMirror.Aligned)
    (aa : CatCrypt.Crypto.Jasmin.CoqSemMirror.ArrAccess) (ws : MWSize)
    (vr vi : JResult Value) (v : Value) : JResult Value :=
  JResult.bind vr fun valR =>
    match valR with
    | .Varr n a =>
        JResult.bind vi fun iV => JResult.bind iV.toInt fun i =>
          match ws with
          | .U8 =>
              JResult.bind (v.toWord .U8) fun wv =>
                if h : 0 ≤ i ∧ i.toNat < n then .ok (.Varr n (JArrayMirror.setByte a ⟨i.toNat, h.2⟩ wv))
                else .typeError
          | ws =>
              JResult.bind (v.toWord ws) fun wv =>
                JResult.bind (JArrayMirror.setWord a al aa ws i wv) fun a' => .ok (.Varr n a')
    | _ => .typeError

theorem writeLval_laset (s : Estate SyscallState Mem) (al aa ws) (x : MVarI) (idx : MPexpr)
    (v : Value) :
    writeLval true gd opS (.Laset al aa ws x idx) v s =
      JResult.bind (lasetVal al aa ws (getVar true s.evm x.v_var) (semPexpr true gd opS s idx) v)
        (fun val => CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true x val s) := by
  simp only [writeLval, lasetVal, JResult.monad_bind_eq]
  cases getVar true s.evm x.v_var with
  | ok valR =>
      cases valR with
      | Varr n a =>
          simp only [JResult.bind_ok]
          cases semPexpr true gd opS s idx with
          | ok iV =>
              simp only [JResult.bind_ok]
              cases iV.toInt with
              | ok i =>
                  simp only [JResult.bind_ok]
                  cases ws with
                  | U8 =>
                      simp only
                      cases v.toWord .U8 with
                      | ok wv => simp only [JResult.bind_ok]; split <;> rfl
                      | _ => rfl
                  | _ =>
                      simp only
                      cases v.toWord _ <;> simp only [JResult.bind]
                      all_goals (try cases JArrayMirror.setWord _ _ _ _ _ _)
                      all_goals rfl
              | _ => rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- The mirror l-value with the index of an array write renamed. -/
def mrenLv (R : MVar → MVar) : MLval → MLval
  | .Laset al aa ws x i => .Laset al aa ws x (mrenE R i)
  | lv => lv

/-- The translated fragment of mirror l-values. -/
def mlvfrag : MLval → Bool
  | .Lnone _ _ => true
  | .Lvar _ => true
  | .Laset _ _ _ _ i => mfrag i
  | _ => false

/-- The reads of an l-value that are renamed: the index of an array write. -/
def mlvReads : MLval → List MVar
  | .Laset _ _ _ _ i => mreads i
  | _ => []

/-- The array an array write reads. -/
def mlvBase : MLval → List MVar
  | .Laset _ _ _ x _ => [x.v_var]
  | _ => []

/-- The variable an l-value writes. -/
def mlvW : MLval → List MVar
  | .Lvar x => [x.v_var]
  | .Laset _ _ _ x _ => [x.v_var]
  | _ => []

/-- The states `t1` and `o1` after writes of the variables `W` from `t` and `o`: the
variables of `W` agree, the others are unchanged, and so are memories and syscall states. -/
structure WR (t o t1 o1 : Estate SyscallState Mem) (W : List MVar) : Prop where
  tmem : t1.emem = t.emem
  tscs : t1.escs = t.escs
  omem : o1.emem = o.emem
  oscs : o1.escs = o.escs
  inW : ∀ v ∈ W, t1.evm v = o1.evm v
  outW : ∀ v, v ∉ W → t1.evm v = t.evm v ∧ o1.evm v = o.evm v

omit [MemModel Mem] in
theorem WR.set (t o : Estate SyscallState Mem) (x : MVar) (val : Value) :
    WR t o (t.withVm (t.evm.set x val)) (o.withVm (o.evm.set x val)) [x] where
  tmem := rfl
  tscs := rfl
  omem := rfl
  oscs := rfl
  inW v hv := by
    simp only [List.mem_singleton] at hv; subst hv
    exact (NFToJasminSem.set_same _ _ _).trans (NFToJasminSem.set_same _ _ _).symm
  outW v hv := by
    simp only [List.mem_singleton] at hv
    exact ⟨NFToJasminSem.set_ne_var _ hv, NFToJasminSem.set_ne_var _ hv⟩

omit [MemModel Mem] in
theorem WR.refl (t o : Estate SyscallState Mem) : WR t o t o [] where
  tmem := rfl
  tscs := rfl
  omem := rfl
  oscs := rfl
  inW _ h := by simp at h
  outW _ _ := ⟨rfl, rfl⟩

omit [MemModel Mem] in
theorem WR.trans {t o t1 o1 t2 o2 : Estate SyscallState Mem} {W1 W2 : List MVar}
    (h1 : WR t o t1 o1 W1) (h2 : WR t1 o1 t2 o2 W2) : WR t o t2 o2 (W1 ++ W2) where
  tmem := h2.tmem.trans h1.tmem
  tscs := h2.tscs.trans h1.tscs
  omem := h2.omem.trans h1.omem
  oscs := h2.oscs.trans h1.oscs
  inW v hv := by
    by_cases hv2 : v ∈ W2
    · exact h2.inW v hv2
    · have hv1 : v ∈ W1 := by simp_all
      rw [(h2.outW v hv2).1, (h2.outW v hv2).2]; exact h1.inW v hv1
  outW v hv := by
    simp only [List.mem_append, not_or] at hv
    rw [(h2.outW v hv.2).1, (h2.outW v hv.2).2]; exact h1.outW v hv.1

theorem getVar_ok {vm : Vm} {x : MVar} {v : Value} (h : getVar true vm x = .ok v) :
    v = vm x ∧ (vm x).isDefined = true := by
  unfold getVar at h
  by_cases hd : (vm.get x).isDefined = true <;> simp_all [Vm.get]

/-- A read of an expression of the fragment that evaluates reads defined values. -/
theorem semPexpr_reads_def (s : Estate SyscallState Mem) : ∀ (a : MPexpr) (w : Value),
    mfrag a = true → semPexpr true gd opS s a = .ok w → ∀ v ∈ mreads a, (s.evm v).isDefined = true
  | .Pvar g, w, _, h, v, hv => by
      rcases g with ⟨⟨x, _⟩, gs⟩
      cases gs with
      | Slocal =>
          simp only [mreads, mlocal, List.mem_singleton] at hv; subst hv
          simp only [semPexpr, CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar,
            CatCrypt.Crypto.Jasmin.CoqSemMirror.GVar.isLvar] at h
          exact (getVar_ok (by simpa using h)).2
      | Sglob => simp [mreads, mlocal] at hv
  | .Pget al aa ws g i, w, hf, h, v, hv => by
      simp only [mfrag] at hf
      simp only [semPexpr, JResult.monad_bind_eq] at h
      obtain ⟨vr, hvr, h⟩ := bind_eq_ok h
      simp only [mreads, List.mem_append] at hv
      rcases hv with hv | hv
      · rcases g with ⟨⟨x, _⟩, gs⟩
        cases gs with
        | Slocal =>
            simp only [mlocal, List.mem_singleton] at hv; subst hv
            simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar,
              CatCrypt.Crypto.Jasmin.CoqSemMirror.GVar.isLvar] at hvr
            exact (getVar_ok (by simpa using hvr)).2
        | Sglob => simp [mlocal] at hv
      · cases vr with
        | Varr n a =>
            simp only at h
            obtain ⟨vi, hvi, -⟩ := bind_eq_ok h
            exact semPexpr_reads_def s i vi hf hvi v hv
        | _ => simp at h
  | .Papp1 op e, w, hf, h, v, hv => by
      simp only [mfrag] at hf
      simp only [semPexpr, JResult.monad_bind_eq] at h
      obtain ⟨we, hwe, -⟩ := bind_eq_ok h
      exact semPexpr_reads_def s e we hf hwe v hv
  | .Papp2 op a b, w, hf, h, v, hv => by
      simp only [mfrag, Bool.and_eq_true] at hf
      simp only [semPexpr, JResult.monad_bind_eq] at h
      obtain ⟨wa, hwa, h⟩ := bind_eq_ok h
      obtain ⟨wb, hwb, -⟩ := bind_eq_ok h
      simp only [mreads, List.mem_append] at hv
      rcases hv with hv | hv
      · exact semPexpr_reads_def s a wa hf.1 hwa v hv
      · exact semPexpr_reads_def s b wb hf.2 hwb v hv
  | .Pconst _, _, _, _, _, hv => by simp [mreads] at hv
  | .Pbool _, _, _, _, _, hv => by simp [mreads] at hv
  | .Parr_init _ _, _, _, _, _, hv => by simp [mreads] at hv
  | .Psub _ _ _ _ _, _, _, _, _, hv => by simp [mreads] at hv
  | .Pload _ _ _, _, _, _, _, hv => by simp [mreads] at hv
  | .PappN _ _, _, _, _, _, hv => by simp [mreads] at hv
  | .Pif _ _ _ _, _, _, _, _, hv => by simp [mreads] at hv

/-- **A write of the fragment, renamed.** A write of `o` by `l` gives a write of `t` by `l`
with its index renamed by `R`, when the index reads and the array agree; the two writes
write the same variables with the same values. The write of `o` reads defined values, and
keeps the variables of `o` at their types. -/
theorem writeLval_rel (R : MVar → MVar) {t o o1 : Estate SyscallState Mem} {l : MLval}
    {v : Value} (hf : mlvfrag l = true) (hr : ∀ u ∈ mlvReads l, t.evm (R u) = o.evm u)
    (hb : ∀ u ∈ mlvBase l, t.evm u = o.evm u) (h : writeLval true gd opS l v o = .ok o1) :
    (∃ t1, writeLval true gd opS (mrenLv R l) v t = .ok t1 ∧ WR t o t1 o1 (mlvW l)) ∧
    (∀ u ∈ mlvReads l ++ mlvBase l, (o.evm u).isDefined = true) ∧
    (WT o.evm → WT o1.evm) := by
  cases l with
  | Lnone i ty =>
      have h' : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone o (evalAtype ty) v = .ok o1 := h
      unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone at h'
      split_ifs at h' with h1 h2
      cases h'
      refine ⟨⟨t, ?_, WR.refl t o⟩, by simp [mlvReads, mlvBase], id⟩
      show CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone t (evalAtype ty) v = _
      simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.writeNone, h1, h2]
  | Lvar x =>
      have h' : CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true x v o = .ok o1 := h
      obtain ⟨rfl, ht, -, hall⟩ := writeVar_ok h'
      exact ⟨⟨_, hall t, WR.set t o x.v_var v⟩, by simp [mlvReads, mlvBase],
        fun hw => WT.set hw ht⟩
  | Laset al aa ws x i =>
      simp only [mlvfrag] at hf
      rw [writeLval_laset] at h
      obtain ⟨val, hval, h⟩ := bind_eq_ok h
      obtain ⟨rfl, ht, -, hall⟩ := writeVar_ok h
      have hx : t.evm x.v_var = o.evm x.v_var := hb _ (by simp [mlvBase])
      have hi : semPexpr true gd opS t (mrenE R i) = semPexpr true gd opS o i :=
        semPexpr_mrenE gd opS R t o i hf (fun u hu => hr u (by simpa [mlvReads] using hu))
      refine ⟨⟨_, ?_, WR.set t o x.v_var val⟩, ?_, fun hw => WT.set hw ht⟩
      · simp only [mrenLv]
        rw [writeLval_laset, show getVar true t.evm x.v_var = getVar true o.evm x.v_var by
          simp [getVar, Vm.get, hx], hi, hval, JResult.bind_ok, hall]
      · simp only [lasetVal] at hval
        obtain ⟨vr, hvr, hval⟩ := bind_eq_ok hval
        have hxd := getVar_ok hvr
        intro u hu
        simp only [mlvReads, mlvBase, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · cases vr with
          | Varr n a =>
              simp only at hval
              obtain ⟨vi, hvi, -⟩ := bind_eq_ok hval
              exact semPexpr_reads_def gd opS o i vi hf hvi u hu
          | _ => simp at hval
        · exact hxd.2
  | Lmem _ _ _ _ => simp [mlvfrag] at hf
  | Lasub _ _ _ _ _ => simp [mlvfrag] at hf

/-- A register or discarded mirror output. -/
def msimple : MLval → Bool
  | .Lnone _ _ => true
  | .Lvar _ => true
  | _ => false

theorem mlvfrag_of_simple {l : MLval} (h : msimple l = true) : mlvfrag l = true := by
  cases l <;> simp_all [msimple, mlvfrag]

theorem mrenLv_simple {R : MVar → MVar} {l : MLval} (h : msimple l = true) : mrenLv R l = l := by
  cases l <;> simp_all [msimple, mrenLv]

theorem semPexprs_mrenE (R : MVar → MVar) (t o : Estate SyscallState Mem) :
    ∀ es : List MPexpr, (∀ e ∈ es, mfrag e = true) →
      (∀ e ∈ es, ∀ v ∈ mreads e, t.evm (R v) = o.evm v) →
      CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList true gd opS t (es.map (mrenE R)) =
        CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList true gd opS o es
  | [], _, _ => rfl
  | e :: es, hf, h => by
      simp only [List.map_cons, CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList]
      rw [semPexpr_mrenE gd opS R t o e (hf e (by simp)) (h e (by simp)),
        semPexprs_mrenE R t o es (fun e he => hf e (by simp [he]))
          (fun e he => h e (by simp [he]))]

theorem semPexprs_reads_def (s : Estate SyscallState Mem) :
    ∀ (es : List MPexpr) (ws : List Value), (∀ e ∈ es, mfrag e = true) →
      CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList true gd opS s es = .ok ws →
      ∀ e ∈ es, ∀ v ∈ mreads e, (s.evm v).isDefined = true
  | [], _, _, _, e, he, _, _ => by simp at he
  | e :: es, ws, hf, h, e', he', v, hv => by
      simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprList,
        JResult.monad_bind_eq] at h
      obtain ⟨w, hw, h⟩ := bind_eq_ok h
      obtain ⟨ws', hws, -⟩ := bind_eq_ok h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact semPexpr_reads_def gd opS s _ w (hf _ (by simp)) hw v hv
      · exact semPexprs_reads_def s es ws' (fun e he => hf e (by simp [he])) hws e' he' v hv

theorem writeLvals_rel {t o o1 : Estate SyscallState Mem} :
    ∀ (xs : List MLval) (vs : List Value), (∀ l ∈ xs, msimple l = true) →
      writeLvals true gd opS o xs vs = .ok o1 →
      (∃ t1, writeLvals true gd opS t xs vs = .ok t1 ∧ WR t o t1 o1 (xs.flatMap mlvW)) ∧
      (WT o.evm → WT o1.evm)
  | [], [], _, h => by
      cases h
      exact ⟨⟨t, rfl, WR.refl t o⟩, id⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | l :: xs, v :: vs, hs, h => by
      simp only [writeLvals, JResult.fold2, JResult.monad_bind_eq] at h
      obtain ⟨o', ho', h⟩ := bind_eq_ok h
      have hl := hs l (by simp)
      obtain ⟨⟨t', ht', hwr⟩, -, hwt⟩ := writeLval_rel gd opS id (t := t) (mlvfrag_of_simple hl)
        (by cases l <;> simp_all [msimple, mlvReads]) (by cases l <;> simp_all [msimple, mlvBase]) ho'
      rw [mrenLv_simple hl] at ht'
      obtain ⟨⟨t1, ht1, hwr1⟩, hwt1⟩ := writeLvals_rel (t := t') xs vs
        (fun l hl => hs l (by simp [hl])) h
      refine ⟨⟨t1, ?_, by simpa using hwr.trans hwr1⟩, fun hw => hwt1 (hwt hw)⟩
      simp only [writeLvals, JResult.fold2, JResult.monad_bind_eq, ht', JResult.bind_ok]
      exact ht1

/-- The mirror instruction with its renamed reads renamed by `R`. -/
def mrenI (R : MVar → MVar) : MInstrR → MInstrR
  | .Cassgn lv tag ty e => .Cassgn (mrenLv R lv) tag ty (mrenE R e)
  | .Copn xs tag o es => .Copn xs tag o (es.map (mrenE R))
  | i => i

/-- The translated straight-line fragment of mirror instructions. -/
def mifrag : MInstrR → Bool
  | .Cassgn lv _ _ e => mlvfrag lv && mfrag e
  | .Copn xs _ _ es => xs.all msimple && es.all mfrag
  | _ => false

/-- The reads of an instruction that are renamed. -/
def mreadsI : MInstrR → List MVar
  | .Cassgn lv _ _ e => mreads e ++ mlvReads lv
  | .Copn _ _ _ es => es.flatMap mreads
  | _ => []

/-- The array an instruction writes in place. -/
def mbaseI : MInstrR → List MVar
  | .Cassgn lv _ _ _ => mlvBase lv
  | _ => []

/-- The variables an instruction writes. -/
def mwI : MInstrR → List MVar
  | .Cassgn lv _ _ _ => mlvW lv
  | .Copn xs _ _ _ => xs.flatMap mlvW
  | _ => []

section Instr
variable (aS : CatCrypt.Crypto.Jasmin.CoqSemMirror.AsmSem)
  (prog : CatCrypt.Crypto.Jasmin.CoqSemMirror.Prog)

/-- **An instruction of the fragment, renamed.** A step of `o` by `j` gives a step of `t`
by `j` with its reads renamed by `R`, writing the same variables with the same values; the
step of `o` reads defined values and keeps the variables of `o` at their types. -/
theorem semIr_rel (R : MVar → MVar) {t o o1 : Estate SyscallState Mem} {j : MInstrR}
    (hf : mifrag j = true) (hr : ∀ u ∈ mreadsI j, t.evm (R u) = o.evm u)
    (hb : ∀ u ∈ mbaseI j, t.evm u = o.evm u)
    (h : CatCrypt.Crypto.Jasmin.CoqSemMirror.SemIr aS opS gd prog o j o1) :
    (∃ t1, CatCrypt.Crypto.Jasmin.CoqSemMirror.SemIr aS opS gd prog t (mrenI R j) t1 ∧
      WR t o t1 o1 (mwI j)) ∧
    (∀ u ∈ mreadsI j ++ mbaseI j, (o.evm u).isDefined = true) ∧ (WT o.evm → WT o1.evm) := by
  cases j with
  | Cassgn lv tag ty e =>
      simp only [mifrag, Bool.and_eq_true] at hf
      cases h with
      | Eassgn _ _ _ _ _ _ v v' he htr hw =>
          have he' : semPexpr true gd opS t (mrenE R e) = .ok v := by
            rw [semPexpr_mrenE gd opS R t o e hf.2 (fun u hu => hr u (by simp [mreadsI, hu]))]
            exact he
          obtain ⟨⟨t1, ht1, hwr⟩, hdef, hwt⟩ := writeLval_rel gd opS R hf.1
            (fun u hu => hr u (by simp [mreadsI, hu])) hb hw
          refine ⟨⟨t1, .Eassgn _ _ _ _ _ _ v v' he' htr ht1, hwr⟩, ?_, hwt⟩
          intro u hu
          simp only [mreadsI, mbaseI, List.mem_append] at hu
          rcases hu with (hu | hu) | hu
          · exact semPexpr_reads_def gd opS o e v hf.2 he u hu
          · exact hdef u (by simp [hu])
          · exact hdef u (by simp [hu])
  | Copn xs tag op es =>
      simp only [mifrag, Bool.and_eq_true, List.all_eq_true] at hf
      cases h with
      | Eopn _ _ _ _ _ _ hs =>
          simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.semSopn, JResult.monad_bind_eq] at hs
          obtain ⟨vs, hvs, hs⟩ := bind_eq_ok hs
          obtain ⟨rs, hrs, hs⟩ := bind_eq_ok hs
          obtain ⟨⟨t1, ht1, hwr⟩, hwt⟩ := writeLvals_rel gd opS (t := t) xs rs hf.1 hs
          have hvs' : CatCrypt.Crypto.Jasmin.CoqSemMirror.semPexprs true gd opS t
              (es.map (mrenE R)) = .ok vs := by
            have := semPexprs_mrenE gd opS R t o es hf.2
              (fun e he u hu => hr u (by simp only [mreadsI, List.mem_flatMap]; exact ⟨e, he, hu⟩))
            exact this.trans hvs
          refine ⟨⟨t1, .Eopn _ _ _ _ _ _ ?_, hwr⟩, ?_, hwt⟩
          · simp only [CatCrypt.Crypto.Jasmin.CoqSemMirror.semSopn,
              JResult.monad_bind_eq, hvs', JResult.bind_ok, hrs]
            exact ht1
          · intro u hu
            simp only [mreadsI, mbaseI, List.append_nil, List.mem_flatMap] at hu
            obtain ⟨e, he, hu⟩ := hu
            exact semPexprs_reads_def gd opS o es vs hf.2 hvs e he u hu
  | _ => simp [mifrag] at hf

end Instr

end MirrorWrite

/-! ## 7. Instructions and their translation -/

section TransInstr

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz

theorem renEs_eq (r : AVar → AVar) : ∀ es : List APExpr, renEs r es = es.map (renE r)
  | [] => rfl
  | e :: es => by simp [renEs, renEs_eq r es]

variable {r : AVar → AVar} {R : MVar → MVar}

theorem translateLValExt_renLv (h : RenOK r R) (lv : ALVal) :
    translateLValExt (renLv r lv) = (translateLValExt lv).map (mrenLv R) := by
  cases lv with
  | Lnone _ ty => cases hty : translateSTypeExt ty <;> simp [renLv, translateLValExt, hty, mrenLv]
  | Lvar x => cases hx : translateVarIExt x <;> simp [renLv, translateLValExt, hx, mrenLv]
  | Lmem _ _ _ => rfl
  | Laset aa ws x i =>
      simp only [renLv, translateLValExt, translateIdx_renE h i]
      cases translateWSize ws <;> cases translateVarIExt x <;> cases translateIdx i <;> rfl
  | Lasub _ _ _ _ _ => rfl

theorem mapM_renE (h : RenOK r R) : ∀ es : List APExpr,
    (es.map (renE r)).mapM translatePExprExt = (es.mapM translatePExprExt).map (List.map (mrenE R))
  | [] => rfl
  | e :: es => by
      simp only [List.map_cons, List.mapM_cons, translatePExprExt_renE h e, mapM_renE h es]
      cases translatePExprExt e <;> cases es.mapM translatePExprExt <;> rfl

theorem translateInstrRExt_renI (h : RenOK r R) {i : AInstrR} (hs : straightI i = true) :
    translateInstrRExt (renI r i) = (translateInstrRExt i).map (mrenI R) := by
  cases i with
  | Cassgn lv tag ty e =>
      simp only [renI, translateInstrRExt, translateLValExt_renLv h, translatePExprExt_renE h]
      cases translateLValExt lv <;> cases translateSTypeExt ty <;> cases translatePExprExt e <;> rfl
  | Copn lvs tag op es =>
      rcases op with ⟨op⟩
      simp only [renI, translateInstrRExt, renEs_eq, mapM_renE h]
      cases lvs.mapM translateLValExt <;> cases es.mapM translatePExprExt <;> rfl
  | _ => simp [straightI] at hs

theorem typeLv_mrenLv (lv : MLval) : typeLv (mrenLv R lv) = mrenLv R (typeLv lv) := by
  cases lv <;> simp [typeLv, mrenLv, typeE_mrenE]

theorem typeArgs_map_mrenE : ∀ (tys : List MAtype) (es : List MPexpr),
    typeArgs tys (es.map (mrenE R)) = (typeArgs tys es).map (mrenE R)
  | [], es => by cases es <;> rfl
  | _ :: _, [] => rfl
  | ty :: tys, e :: es => by
      simp [typeArgs, typeE_mrenE, typeArgs_map_mrenE tys es]

theorem typeI_mrenI (j : MInstrR) : typeI (mrenI R j) = mrenI R (typeI j) := by
  cases j with
  | Cassgn lv tag ty e => simp [mrenI, typeI, typeLv_mrenLv, typeE_mrenE]
  | Copn xs tag o es =>
      simp only [mrenI, typeI, typeArgs_map_mrenE]
  | _ => rfl

/-- The reads of an l-value that the renaming renames. -/
def lvIdx : ALVal → List AVar
  | .Lmem _ x o => x.var :: readsE o
  | .Laset _ _ _ i => readsE i
  | .Lasub _ _ _ _ i => readsE i
  | _ => []

/-- The array an l-value writes in place. -/
def lvBase : ALVal → List AVar
  | .Laset _ _ x _ => [x.var]
  | .Lasub _ _ _ x _ => [x.var]
  | _ => []

/-- The reads of an instruction that the renaming renames. -/
def rdR : AInstrR → List AVar
  | .Cassgn lv _ _ e => readsE e ++ lvIdx lv
  | .Copn _ _ _ es => readsEs es
  | _ => []

/-- The arrays an instruction writes in place. -/
def rdB : AInstrR → List AVar
  | .Cassgn lv _ _ _ => lvBase lv
  | _ => []

theorem mem_readsI {i : AInstrR} {x : AVar} : x ∈ readsI i ↔ x ∈ rdR i ∨ x ∈ rdB i := by
  cases i with
  | Cassgn lv _ _ e => cases lv <;> simp [readsI, rdR, rdB, readsLv, lvIdx, lvBase] <;> tauto
  | _ => simp [readsI, rdR, rdB]

theorem translateVarExt_of_varI {x : AVarI} {x' : MVarI} (h : translateVarIExt x = some x') :
    translateVarExt x.var = some x'.v_var := by
  simp only [translateVarIExt, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  exact hv

theorem translateLValExt_of {lv : ALVal} {l : MLval} (h : translateLValExt lv = some l) :
    mlvfrag (typeLv l) = true ∧ (lvIdx lv).mapM translateVarExt = some (mlvReads (typeLv l)) ∧
    (lvBase lv).mapM translateVarExt = some (mlvBase (typeLv l)) ∧
    (writesLv lv).mapM translateVarExt = some (mlvW (typeLv l)) := by
  cases lv with
  | Lnone _ ty =>
      simp only [translateLValExt, Option.map_eq_some_iff] at h
      obtain ⟨t, -, rfl⟩ := h
      simp [typeLv, mlvfrag, lvIdx, mlvReads, lvBase, mlvBase, writesLv, mlvW]
  | Lvar x =>
      simp only [translateLValExt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      simp [typeLv, mlvfrag, lvIdx, mlvReads, lvBase, mlvBase, writesLv, mlvW,
        translateVarExt_of_varI hx]
  | Laset aa ws x i =>
      simp only [translateLValExt] at h
      cases hw : translateWSize ws <;> cases hx : translateVarIExt x <;>
        cases hi : translateIdx i <;> simp only [hw, hx, hi, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨hf, hr⟩ := translateIdx_frag_reads hi
      simp [typeLv, mlvfrag, mfrag_typeE _ _ hf, lvIdx, mlvReads, mreads_typeE, hr, lvBase,
        mlvBase, writesLv, mlvW, translateVarExt_of_varI hx]
  | Lmem _ _ _ => simp [translateLValExt] at h
  | Lasub _ _ _ _ _ => simp [translateLValExt] at h

theorem typeArgs_mem : ∀ (tys : List MAtype) (es : List MPexpr), ∀ e ∈ typeArgs tys es,
    ∃ e0 ∈ es, ∃ ty, e = typeE ty e0 ∨ e = e0
  | [], es, e, he => ⟨e, by cases es <;> simp_all [typeArgs], .aint, Or.inr rfl⟩
  | _ :: _, [], e, he => by simp [typeArgs] at he
  | ty :: tys, e0 :: es, e, he => by
      simp only [typeArgs, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨e0, by simp, ty, Or.inl rfl⟩
      · obtain ⟨e1, he1, t, h⟩ := typeArgs_mem tys es e he
        exact ⟨e1, by simp [he1], t, h⟩

theorem typeArgs_flatMap_mreads : ∀ (tys : List MAtype) (es : List MPexpr),
    (typeArgs tys es).flatMap mreads = es.flatMap mreads
  | [], es => by cases es <;> rfl
  | _ :: _, [] => rfl
  | ty :: tys, e :: es => by
      simp [typeArgs, mreads_typeE, typeArgs_flatMap_mreads tys es]

theorem readsEs_of : ∀ (es : List APExpr) (es' : List MPexpr), es.mapM translatePExprExt = some es' →
    (∀ e ∈ es', mfrag e = true) ∧ (readsEs es).mapM translateVarExt = some (es'.flatMap mreads)
  | [], es', h => by simp at h; subst h; simp [readsEs]
  | e :: es, es', h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      obtain ⟨hf, hr⟩ := translatePExprExt_of e b hb
      obtain ⟨hfs, hrs⟩ := readsEs_of es bs hbs
      refine ⟨fun e he => ?_, by simpa [readsEs] using mapM_append_some hr hrs⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hf
      · exact hfs e he

theorem simpleLvs_of : ∀ (lvs : List ALVal) (ls : List MLval), (∀ l ∈ lvs, simpleLv l = true) →
    lvs.mapM translateLValExt = some ls →
    (∀ l ∈ ls, msimple l = true) ∧ ls.map typeLv = ls ∧
    (lvs.flatMap writesLv).mapM translateVarExt = some (ls.flatMap mlvW)
  | [], ls, _, h => by simp at h; subst h; simp
  | lv :: lvs, ls, hs, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨l, hl, ls', hls, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := simpleLvs_of lvs ls' (fun l hl => hs l (by simp [hl])) hls
      have hlv := hs lv (by simp)
      obtain ⟨-, -, -, hw⟩ := translateLValExt_of hl
      have hsl : msimple l = true ∧ typeLv l = l := by
        cases lv <;> simp [simpleLv] at hlv <;>
          simp only [translateLValExt, Option.map_eq_some_iff] at hl <;>
          obtain ⟨_, _, rfl⟩ := hl <;> simp [msimple, typeLv]
      refine ⟨fun l' hl' => ?_, by simp [hsl.2, h2], ?_⟩
      · rcases List.mem_cons.mp hl' with rfl | hl'
        · exact hsl.1
        · exact h1 l' hl'
      · rw [hsl.2] at hw
        simpa using mapM_append_some hw h3

/-- The translation of a straight-line instruction, typed, is in the fragment; its renamed
reads, in-place arrays and writes translate to those of the mirror instruction. -/
theorem translateInstrRExt_of {i : AInstrR} {j : MInstrR} (hs : straightI i = true)
    (h : translateInstrRExt i = some j) :
    mifrag (typeI j) = true ∧ (rdR i).mapM translateVarExt = some (mreadsI (typeI j)) ∧
    (rdB i).mapM translateVarExt = some (mbaseI (typeI j)) ∧
    (writesI i).mapM translateVarExt = some (mwI (typeI j)) := by
  cases i with
  | Cassgn lv tag ty e =>
      simp only [translateInstrRExt] at h
      cases hl : translateLValExt lv <;> cases hty : translateSTypeExt ty <;>
        cases he : translatePExprExt e <;> simp only [hl, hty, he, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨hf, hr⟩ := translatePExprExt_of e _ he
      obtain ⟨hlf, hlr, hlb, hlw⟩ := translateLValExt_of hl
      simp [typeI, mifrag, hlf, mfrag_typeE _ _ hf, rdR, mreadsI, mreads_typeE,
        mapM_append_some hr hlr, rdB, mbaseI, hlb, writesI, mwI, hlw]
  | Copn lvs tag op es =>
      rcases op with ⟨op⟩
      simp only [straightI, List.all_eq_true] at hs
      simp only [translateInstrRExt] at h
      cases hl : lvs.mapM translateLValExt <;> cases he : es.mapM translatePExprExt <;>
        simp only [hl, he, reduceCtorEq, Option.some.injEq] at h
      subst h
      rename_i ls es'
      obtain ⟨hfs, hrs⟩ := readsEs_of es es' he
      obtain ⟨h1, h2, h3⟩ := simpleLvs_of lvs ls hs hl
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [typeI, mifrag, h2, Bool.and_eq_true, List.all_eq_true]
        refine ⟨h1, fun e he => ?_⟩
        obtain ⟨e0, he0, ty, h | h⟩ := typeArgs_mem _ _ e he <;> rw [h]
        · exact mfrag_typeE _ _ (hfs e0 he0)
        · exact hfs e0 he0
      · simpa [typeI, rdR, mreadsI, typeArgs_flatMap_mreads] using hrs
      · simp [typeI, rdB, mbaseI]
      · simpa [typeI, writesI, mwI, h2] using h3
  | _ => simp [straightI] at hs

end TransInstr

/-! ## 8. Runs of translated commands -/

section Run

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem AsmSem GlobDecls Prog Sem SemIr
  JResult truncateVal evalAtype MemModel semPexpr getVar DB truncatable)

variable {SyscallState Mem : Type} [MemModel Mem] (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
  (prog : Prog)

/-- A run of the typed translation of `c` from `s` to `s'`. -/
def RunA (s : Estate SyscallState Mem) (c : List InstrR) (s' : Estate SyscallState Mem) : Prop :=
  ∃ c', translateCmdExt c = some c' ∧ Sem aS opS gd prog s (typeC c') s'

theorem RunA.nil (s : Estate SyscallState Mem) : RunA aS opS gd prog s [] s :=
  ⟨[], rfl, .Eskip _⟩

theorem RunA.append {s s1 s2 : Estate SyscallState Mem} {a b : List InstrR}
    (ha : RunA aS opS gd prog s a s1) (hb : RunA aS opS gd prog s1 b s2) :
    RunA aS opS gd prog s (a ++ b) s2 := by
  obtain ⟨a', ha', h1⟩ := ha
  obtain ⟨b', hb', h2⟩ := hb
  exact ⟨a' ++ b', translateCmdExt_append_eq_some ha' hb', by
    rw [NFToJasminSem.typeC_append]; exact ComJasminBridgeProgram.sem_append aS opS gd prog h1 h2⟩

theorem RunA.single {s s1 : Estate SyscallState Mem} {i : InstrR} {j : MInstrR}
    (hi : translateInstrRExt i = some j) (h : SemIr aS opS gd prog s (typeI j) s1) :
    RunA aS opS gd prog s [i] s1 :=
  ⟨[.MkI () j], by simp [translateCmdExt, hi], by
    simp only [typeC]; exact NFToJasminSem.sem_cons aS opS gd prog h (.Eskip _)⟩

theorem RunA.cons_inv {s s2 : Estate SyscallState Mem} {i : InstrR} {c : List InstrR}
    (h : RunA aS opS gd prog s (i :: c) s2) :
    ∃ j s1, translateInstrRExt i = some j ∧ SemIr aS opS gd prog s (typeI j) s1 ∧
      RunA aS opS gd prog s1 c s2 := by
  obtain ⟨c', hc', hs⟩ := h
  obtain ⟨j, c'', hj, hc'', rfl⟩ := NFToJasminSem.translateCmdExt_cons_inv hc'
  simp only [typeC] at hs
  cases hs with
  | Eseq _ s1 _ _ _ hI hc =>
      cases hI with
      | EmkI _ _ _ _ hir => exact ⟨j, s1, hj, hir, c'', hc'', hc⟩

/-- An assignment to a variable in the run of `t`. -/
theorem RunA.asgn {t : Estate SyscallState Mem} {d : JVar} {tag : AssgnTag} {ty : SType}
    {e : PExpr} {d' : MVar} {ty' : MAtype} {e' : MPexpr}
    (hd : translateVarExt d = some d') (hty : translateSTypeExt ty = some ty')
    (he : translatePExprExt e = some e') (hdt : d'.vtype = ty') {w val : Value}
    (hs : semPexpr true gd opS t (typeE ty' e') = .ok w)
    (htr : truncateVal (evalAtype ty') w = .ok val) (hdb : DB val = true)
    (htc : truncatable (evalAtype ty') val = true) :
    RunA aS opS gd prog t [.Cassgn (.Lvar (vi d)) tag ty e] (t.withVm (t.evm.set d' val)) := by
  have hi : translateInstrRExt (.Cassgn (.Lvar (vi d)) tag ty e) =
      some (.Cassgn (.Lvar { v_var := d' }) (translateAssgnTag tag) ty' e') := by
    simp [translateInstrRExt, translateLValExt, translateVarIExt, vi, hd, hty, he]
  refine RunA.single aS opS gd prog hi (.Eassgn _ _ _ _ _ _ w val hs htr ?_)
  show CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar true { v_var := d' } val t = _
  unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.writeVar
  have : CatCrypt.Crypto.Jasmin.CoqSemMirror.setVar true t.evm d' val = .ok (t.evm.set d' val) := by
    obtain ⟨dt, dn⟩ := d'
    simp only at hdt; subst hdt
    unfold CatCrypt.Crypto.Jasmin.CoqSemMirror.setVar
    cases dt <;> simp_all [evalAtype]
  simp [this]

theorem translateSTypeExt_of_var {x : JVar} {x' : MVar} (h : translateVarExt x = some x') :
    translateSTypeExt x.vtype = some x'.vtype := by
  simp only [translateVarExt, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  exact ht

/-- A move `d = s` of a defined value of the type of `d`. -/
theorem RunA.mv {t : Estate SyscallState Mem} {d s : JVar} {d' s' : MVar}
    (hd : translateVarExt d = some d') (hs : translateVarExt s = some s') {val : Value} (hv : t.evm s' = val) (hdef : val.isDefined = true)
    (hty : val.typeOf = evalAtype d'.vtype) :
    RunA aS opS gd prog t [mv d s] (t.withVm (t.evm.set d' val)) := by
  have hl : translatePExprExt (lpv s) = some (.Pvar { gv := { v_var := s' }, gs := .Slocal }) := by
    simp [lpv, vi, translatePExprExt, translateGVarExt, translateVarIExt, hs]
  refine RunA.asgn aS opS gd prog (w := val) hd (translateSTypeExt_of_var hd) hl rfl ?_ ?_ ?_ ?_
  · show CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar true gd t.evm _ = _
    simp [CatCrypt.Crypto.Jasmin.CoqSemMirror.getGvar, CatCrypt.Crypto.Jasmin.CoqSemMirror.GVar.isLvar,
      getVar, Vm.get, hv, hdef]
  · rw [← hty]; exact NFToJasminSem.truncateVal_typeOf hdef
  · simp [DB, hdef]
  · simp [truncatable, hty]

end Run

/-! ## 9. Lookups, fresh names and the renaming of holders -/

section Basic

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt

theorem lookR_some {rho : List (JVar × JVar)} {x h : JVar} (hl : lookR rho x = some h) :
    (x, h) ∈ rho := by
  simp only [lookR, Option.map_eq_some_iff] at hl
  obtain ⟨p, hp, rfl⟩ := hl
  have := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  subst hx
  exact this

theorem lookR_none {rho : List (JVar × JVar)} {x : JVar} (hl : lookR rho x = none) :
    ∀ p ∈ rho, p.1 ≠ x := by
  simp only [lookR, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq] at hl
  exact hl

theorem lookR_isSome_iff {rho : List (JVar × JVar)} {x : JVar} :
    (lookR rho x).isSome = true ↔ ∃ p ∈ rho, p.1 = x := by
  simp [lookR, List.find?_isSome]

theorem lookS_some {sig : List (JVar × Src)} {x : JVar} {s : Src} (hl : lookS sig x = some s) :
    (x, s) ∈ sig := by
  simp only [lookS, Option.map_eq_some_iff] at hl
  obtain ⟨p, hp, rfl⟩ := hl
  have := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  subst hx
  exact this

theorem lookS_isSome_iff {sig : List (JVar × Src)} {x : JVar} :
    (lookS sig x).isSome = true ↔ ∃ p ∈ sig, p.1 = x := by
  simp [lookS, List.find?_isSome]

theorem renOf_cases (rho : List (JVar × JVar)) (x : JVar) :
    (renOf rho x = x ∧ lookR rho x = none) ∨ (x, renOf rho x) ∈ rho := by
  unfold renOf
  cases hl : lookR rho x with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some h => exact Or.inr (lookR_some hl)

theorem isFreshName_freshName (n : Nat) : isFreshName (freshName n) = true := by
  simp [isFreshName, freshName, List.isPrefixOf_iff_prefix]

theorem freshName_inj {n m : Nat} (h : freshName n = freshName m) : n = m := by
  simp only [freshName, String.append_right_inj] at h
  have h' : Nat.toDigits 10 n = Nat.toDigits 10 m := by
    rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits] at h
    exact String.ofList_injective h
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) h'
  simpa [Nat.ofDigitChars_ten_toDigits] using this

theorem translateVarExt_vname {x : JVar} {x' : MVar} (h : translateVarExt x = some x') :
    x'.vname = x.vname := by
  simp only [translateVarExt, Option.map_eq_some_iff] at h
  obtain ⟨t, -, rfl⟩ := h
  rfl

theorem isSome_translateSTypeExt_gpr {t : SType} (h : isGprTy t = true) :
    (translateSTypeExt t).isSome = true := by
  rcases t with _ | _ | _ | ws <;> simp [isGprTy] at h
  cases ws <;> simp_all [translateSTypeExt, translateSType, translateWSize]

theorem isSome_translateVarExt_gpr {x : JVar} (h : isGprTy x.vtype = true) :
    (translateVarExt x).isSome = true := by
  simpa [translateVarExt] using isSome_translateSTypeExt_gpr h

/-- The mirror image of the renaming to holders. -/
def Rof (rho : List (JVar × JVar)) (v : MVar) : MVar :=
  match rho.find? (fun p => decide (translateVarExt p.1 = some v)) with
  | some p => (translateVarExt p.2).getD v
  | none => v

theorem find?_congr {α : Type} {P Q : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, P a = Q a) →
    l.find? P = l.find? Q
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?_cons, h a (by simp)]
      split <;> [rfl; exact find?_congr (fun b hb => h b (by simp [hb]))]

theorem renOK_renOf {rho : List (JVar × JVar)} (hty : ∀ p ∈ rho, p.2.vtype = p.1.vtype) :
    RenOK (renOf rho) (Rof rho) where
  ty x := by
    rcases renOf_cases rho x with ⟨h, -⟩ | h
    · rw [h]
    · exact hty _ h
  tr x x' hx := by
    have hf : rho.find? (fun p => decide (translateVarExt p.1 = some x')) =
        rho.find? (fun p => p.1 == x) := by
      refine find?_congr fun p _ => ?_
      by_cases hp : p.1 = x
      · simp [hp, hx]
      · have : ¬ translateVarExt p.1 = some x' := fun h' => hp (translateVarExt_inj h' hx)
        simp [hp, this]
    unfold Rof renOf lookR
    rw [hf]
    cases hfind : rho.find? (fun p => p.1 == x) with
    | none => simpa using hx
    | some p =>
        have hmem := List.mem_of_find?_eq_some hfind
        have hpx := List.find?_some hfind
        simp only [beq_iff_eq] at hpx
        have hs : (translateVarExt p.2).isSome = true := by
          rw [translateVarExt_isSome_of_vtype (hty p hmem), hpx]; simp [hx]
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
        simp [hv]

mutual
theorem pexprVars_renE (r : JVar → JVar) : ∀ (e : PExpr) (v : JVar), v ∈ pexprVars (renE r e) →
    ∃ y ∈ pexprVars e, v = y ∨ v = r y
  | .Pconst _, v, h => by simp [renE, pexprVars] at h
  | .Pbool _, v, h => by simp [renE, pexprVars] at h
  | .Parr_init _, v, h => by simp [renE, pexprVars] at h
  | .Pvar g, v, h => by
      simp only [renE, pexprVars, renG, List.mem_singleton] at h
      refine ⟨g.gv.var, by simp [pexprVars], ?_⟩
      split at h <;> simp_all
  | .Pget _ _ g i, v, h => by
      simp only [renE, pexprVars, List.mem_cons] at h
      rcases h with h | h
      · refine ⟨g.gv.var, by simp [pexprVars], ?_⟩
        unfold renG at h; split at h <;> simp_all
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r i v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
  | .Psub _ _ _ g i, v, h => by
      simp only [renE, pexprVars, List.mem_cons] at h
      rcases h with h | h
      · refine ⟨g.gv.var, by simp [pexprVars], ?_⟩
        unfold renG at h; split at h <;> simp_all
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r i v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
  | .Pload _ x o, v, h => by
      simp only [renE, pexprVars, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨x.var, by simp [pexprVars], Or.inr h⟩
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r o v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
  | .Papp1 _ e, v, h => by
      simp only [renE, pexprVars] at h
      exact pexprVars_renE r e v h
  | .Papp2 _ a b, v, h => by
      simp only [renE, pexprVars, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r a v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r b v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
  | .PappN _ es, v, h => by
      simp only [renE, pexprVars] at h
      exact pexprsVars_renEs r es v h
  | .Pif _ c a b, v, h => by
      simp only [renE, pexprVars, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r c v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r a v h
        exact ⟨y, by simp [pexprVars, hy], h⟩
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r b v h
        exact ⟨y, by simp [pexprVars, hy], h⟩

theorem pexprsVars_renEs (r : JVar → JVar) : ∀ (es : List PExpr) (v : JVar),
    v ∈ pexprsVars (renEs r es) → ∃ y ∈ pexprsVars es, v = y ∨ v = r y
  | [], v, h => by simp [renEs, pexprsVars] at h
  | e :: es, v, h => by
      simp only [renEs, pexprsVars, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r e v h
        exact ⟨y, by simp [pexprsVars, hy], h⟩
      · obtain ⟨y, hy, h⟩ := pexprsVars_renEs r es v h
        exact ⟨y, by simp [pexprsVars, hy], h⟩
end

mutual
theorem readsE_sub : ∀ (e : PExpr) (v : JVar), v ∈ readsE e → v ∈ pexprVars e
  | .Pconst _, v, h => by simp [readsE] at h
  | .Pbool _, v, h => by simp [readsE] at h
  | .Parr_init _, v, h => by simp [readsE] at h
  | .Pvar g, v, h => by
      simp only [readsE] at h; split at h <;> simp_all [pexprVars]
  | .Pget _ _ g i, v, h => by
      simp only [readsE, List.mem_append] at h
      rcases h with h | h
      · split at h <;> simp_all [pexprVars]
      · simp [pexprVars, readsE_sub i v h]
  | .Psub _ _ _ g i, v, h => by
      simp only [readsE, List.mem_append] at h
      rcases h with h | h
      · split at h <;> simp_all [pexprVars]
      · simp [pexprVars, readsE_sub i v h]
  | .Pload _ x o, v, h => by
      simp only [readsE, List.mem_cons] at h
      rcases h with h | h
      · simp [pexprVars, h]
      · simp [pexprVars, readsE_sub o v h]
  | .Papp1 _ e, v, h => by simp only [readsE] at h; simp [pexprVars, readsE_sub e v h]
  | .Papp2 _ a b, v, h => by
      simp only [readsE, List.mem_append] at h
      rcases h with h | h
      · simp [pexprVars, readsE_sub a v h]
      · simp [pexprVars, readsE_sub b v h]
  | .PappN _ es, v, h => by simp only [readsE] at h; simp [pexprVars, readsEs_sub es v h]
  | .Pif _ c a b, v, h => by
      simp only [readsE, List.mem_append] at h
      rcases h with (h | h) | h
      · simp [pexprVars, readsE_sub c v h]
      · simp [pexprVars, readsE_sub a v h]
      · simp [pexprVars, readsE_sub b v h]

theorem readsEs_sub : ∀ (es : List PExpr) (v : JVar), v ∈ readsEs es → v ∈ pexprsVars es
  | [], v, h => by simp [readsEs] at h
  | e :: es, v, h => by
      simp only [readsEs, List.mem_append] at h
      rcases h with h | h
      · simp [pexprsVars, readsE_sub e v h]
      · simp [pexprsVars, readsEs_sub es v h]
end

theorem readsI_sub {i : InstrR} {v : JVar} (h : v ∈ readsI i) : v ∈ instrVars i := by
  cases i with
  | Cassgn lv _ _ e =>
      simp only [readsI, List.mem_append] at h
      rcases h with h | h
      · simp [instrVars, readsE_sub e v h]
      · cases lv with
        | Lmem _ x o =>
            simp only [readsLv, List.mem_cons] at h
            rcases h with rfl | h
            · simp [instrVars, lvalVars]
            · simp [instrVars, lvalVars, readsE_sub o v h]
        | Laset _ _ x o =>
            simp only [readsLv, List.mem_cons] at h
            rcases h with rfl | h
            · simp [instrVars, lvalVars]
            · simp [instrVars, lvalVars, readsE_sub o v h]
        | Lasub _ _ _ x o =>
            simp only [readsLv, List.mem_cons] at h
            rcases h with rfl | h
            · simp [instrVars, lvalVars]
            · simp [instrVars, lvalVars, readsE_sub o v h]
        | _ => simp [readsLv] at h
  | Copn _ _ _ es => simp only [readsI] at h; simp [instrVars, readsEs_sub es v h]
  | _ => simp [readsI] at h

theorem writesI_sub {i : InstrR} {v : JVar} (h : v ∈ writesI i) : v ∈ instrVars i := by
  cases i with
  | Cassgn lv _ _ e =>
      simp only [writesI] at h
      cases lv <;> simp [writesLv] at h <;> simp [instrVars, lvalVars, h]
  | Copn lvs _ _ es =>
      simp only [writesI, List.mem_flatMap] at h
      obtain ⟨l, hl, hv⟩ := h
      simp only [instrVars, lvalsVars, List.mem_append, List.mem_flatMap]
      left; refine ⟨l, hl, ?_⟩
      cases l <;> simp [writesLv] at hv <;> simp [lvalVars, hv]
  | _ => simp [writesI] at h

theorem instrVars_renI (r : JVar → JVar) {i : InstrR} {v : JVar} (h : v ∈ instrVars (renI r i)) :
    ∃ y ∈ instrVars i, v = y ∨ v = r y := by
  cases i with
  | Cassgn lv tag ty e =>
      simp only [renI, instrVars, List.mem_append] at h
      rcases h with h | h
      · cases lv with
        | Lmem ws x o =>
            simp only [renLv, lvalVars, List.mem_cons] at h
            rcases h with h | h
            · exact ⟨x.var, by simp [instrVars, lvalVars], Or.inr h⟩
            · obtain ⟨y, hy, h⟩ := pexprVars_renE r o v h
              exact ⟨y, by simp [instrVars, lvalVars, hy], h⟩
        | Laset aa ws x i =>
            simp only [renLv, lvalVars, List.mem_cons] at h
            rcases h with h | h
            · exact ⟨x.var, by simp [instrVars, lvalVars], Or.inl h⟩
            · obtain ⟨y, hy, h⟩ := pexprVars_renE r i v h
              exact ⟨y, by simp [instrVars, lvalVars, hy], h⟩
        | Lasub aa ws n x i =>
            simp only [renLv, lvalVars, List.mem_cons] at h
            rcases h with h | h
            · exact ⟨x.var, by simp [instrVars, lvalVars], Or.inl h⟩
            · obtain ⟨y, hy, h⟩ := pexprVars_renE r i v h
              exact ⟨y, by simp [instrVars, lvalVars, hy], h⟩
        | Lnone _ _ => simp [renLv, lvalVars] at h
        | Lvar x => exact ⟨v, by simp_all [renLv, instrVars, lvalVars], Or.inl rfl⟩
      · obtain ⟨y, hy, h⟩ := pexprVars_renE r e v h
        exact ⟨y, by simp [instrVars, hy], h⟩
  | Copn lvs tag op es =>
      simp only [renI, instrVars, List.mem_append] at h
      rcases h with h | h
      · exact ⟨v, by simp [instrVars, h], Or.inl rfl⟩
      · obtain ⟨y, hy, h⟩ := pexprsVars_renEs r es v h
        exact ⟨y, by simp [instrVars, hy], h⟩
  | _ => exact ⟨v, by simpa [renI] using h, Or.inl rfl⟩

end Basic

/-! ## 10. Invariants of the pass -/

section Inv

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Value Vm Estate OpSem AsmSem GlobDecls Prog
  JResult truncateVal evalAtype MemModel semPexpr DB truncatable)

variable (T : Prop) (O : List JVar)

/-- `st'` extends the fresh variables of `st`. -/
structure StLe (st st' : St) : Prop where
  slots : st.slots ⊆ st'.slots
  regs : st.regs ⊆ st'.regs
  cnt : st.cnt ≤ st'.cnt

theorem StLe.refl (st : St) : StLe st st := ⟨fun _ h => h, fun _ h => h, le_rfl⟩

theorem StLe.trans {a b c : St} (h1 : StLe a b) (h2 : StLe b c) : StLe a c :=
  ⟨fun _ h => h2.slots (h1.slots h), fun _ h => h2.regs (h1.regs h), h1.cnt.trans h2.cnt⟩

/-- A reload source of `x` is well formed: a stack variable of the type of `x` among the
fresh ones, or a right-hand side at the type of `x` over variables of `O` (translating when
`T` holds). -/
def SrcGood (st : St) (x : JVar) : Src → Prop
  | .slot s => s.vtype = x.vtype ∧ s ∈ st.slots
  | .remat ty e => ty = x.vtype ∧ (T → (translatePExprExt e).isSome = true) ∧
      ∀ v ∈ pexprVars e, v ∈ O

/-- The structural invariant of the pass state over the original variables `O`. -/
structure GoodSt (st : St) : Prop where
  rho : ∀ p ∈ st.rho, p.1 ∈ O ∧ isGprTy p.1.vtype = true ∧ p.2.vtype = p.1.vtype ∧
    (p.2 = p.1 ∨ p.2 ∈ st.regs)
  sig : ∀ p ∈ st.sig, p.1 ∈ O ∧ isGprTy p.1.vtype = true ∧ SrcGood T O st p.1 p.2
  fresh : ∀ v ∈ st.slots ++ st.regs, isGprTy v.vtype = true ∧ ∃ n < st.cnt, v.vname = freshName n
  nodup : ((st.slots ++ st.regs).map (·.vname)).Nodup

/-- An emitted instruction is straight line, translates when `T` holds, and reads and writes
original or fresh variables. -/
def EmitOK (st : St) (i : InstrR) : Prop :=
  straightI i = true ∧ (T → (translateInstrRExt i).isSome = true) ∧
    ∀ v ∈ instrVars i, v ∈ O ∨ v ∈ st.slots ++ st.regs

variable {T O}

theorem SrcGood.mono {st st' : St} (h : StLe st st') {x : JVar} {s : Src}
    (hs : SrcGood T O st x s) : SrcGood T O st' x s := by
  cases s with
  | slot s => exact ⟨hs.1, h.slots hs.2⟩
  | remat ty e => exact hs

theorem EmitOK.mono {st st' : St} (h : StLe st st') {i : InstrR} (hi : EmitOK T O st i) :
    EmitOK T O st' i := by
  refine ⟨hi.1, hi.2.1, fun v hv => ?_⟩
  rcases hi.2.2 v hv with h' | h'
  · exact Or.inl h'
  · simp only [List.mem_append] at h' ⊢
    rcases h' with h' | h'
    · exact Or.inr (Or.inl (h.slots h'))
    · exact Or.inr (Or.inr (h.regs h'))

theorem GoodSt.rho_sub {st : St} (hG : GoodSt T O st) {rho : List (JVar × JVar)}
    (h : ∀ p ∈ rho, p ∈ st.rho) : GoodSt T O { st with rho := rho } :=
  ⟨fun p hp => hG.rho p (h p hp), hG.sig, hG.fresh, hG.nodup⟩

/-- The fresh name of the counter is not the name of a fresh variable already created. -/
theorem GoodSt.new_name {st : St} (hG : GoodSt T O st) :
    ∀ v ∈ st.slots ++ st.regs, v.vname ≠ freshName st.cnt := by
  intro v hv h
  obtain ⟨-, n, hn, hvn⟩ := hG.fresh v hv
  rw [hvn] at h
  exact absurd (freshName_inj h) (by omega)

/-- `GoodSt` after a new fresh variable `f` of the counter, with `f` in `slots` or `regs`. -/
theorem GoodSt.add_fresh {st : St} (hG : GoodSt T O st) {f : JVar} (hf : f.vname = freshName st.cnt)
    (hg : isGprTy f.vtype = true) {st' : St} (hcnt : st'.cnt = st.cnt + 1)
    (hsl : List.Perm (st'.slots ++ st'.regs) (f :: (st.slots ++ st.regs))) :
    (∀ v ∈ st'.slots ++ st'.regs, isGprTy v.vtype = true ∧ ∃ n < st'.cnt, v.vname = freshName n) ∧
    ((st'.slots ++ st'.regs).map (·.vname)).Nodup := by
  constructor
  · intro v hv
    rcases List.mem_cons.mp (hsl.subset hv) with rfl | hv
    · exact ⟨hg, st.cnt, by omega, hf⟩
    · obtain ⟨h1, n, hn, h2⟩ := hG.fresh v hv
      exact ⟨h1, n, by omega, h2⟩
  · rw [(hsl.map (·.vname)).nodup_iff]
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun v hv h => hG.new_name v hv (h.trans hf), hG.nodup⟩

section Sem

variable {SyscallState Mem : Type} [MemModel Mem] (gd : GlobDecls) (opS : OpSem)

/-- What a reload source of `x'` gives in the states `o` and `t`: a stack variable holding
in `t` the defined value of `x'` in `o`, at its type; or a right-hand side evaluating in `o`
to a value that truncates to the value of `x'`, which a write accepts. -/
def SrcFact (o t : Estate SyscallState Mem) (x' : MVar) : Src → Prop
  | .slot s => ∀ s', translateVarExt s = some s' →
      t.evm s' = o.evm x' ∧ (o.evm x').isDefined = true ∧ (o.evm x').typeOf = evalAtype x'.vtype
  | .remat ty e => ∀ e' ty', translatePExprExt e = some e' → translateSTypeExt ty = some ty' →
      ∃ w, semPexpr true gd opS o (typeE ty' e') = .ok w ∧
        truncateVal (evalAtype ty') w = .ok (o.evm x') ∧ DB (o.evm x') = true ∧
        truncatable (evalAtype ty') (o.evm x') = true

/-- **The simulation invariant.** The run of the spilled code is in `t` when the run of the
original is in `o`: memories and syscall states agree, every variable of a name outside the
fresh prefix agrees, each holder holds the value of its variable, and each reload source
gives it. -/
structure SI (o t : Estate SyscallState Mem) (rho : List (JVar × JVar)) (sig : List (JVar × Src)) :
    Prop where
  mem : t.emem = o.emem
  scs : t.escs = o.escs
  orig : ∀ v : MVar, isFreshName v.vname = false → t.evm v = o.evm v
  rho : ∀ p ∈ rho, ∀ x' h', translateVarExt p.1 = some x' → translateVarExt p.2 = some h' →
    t.evm h' = o.evm x'
  sig : ∀ p ∈ sig, ∀ x', translateVarExt p.1 = some x' → SrcFact gd opS o t x' p.2

variable {gd opS}

theorem SI.rho_sub {o t : Estate SyscallState Mem} {rho rho' : List (JVar × JVar)}
    {sig : List (JVar × Src)} (h : SI gd opS o t rho sig) (hs : ∀ p ∈ rho', p ∈ rho) :
    SI gd opS o t rho' sig :=
  ⟨h.mem, h.scs, h.orig, fun p hp => h.rho p (hs p hp), h.sig⟩

/-- A write of `t` at a fresh name no holder or stack variable uses keeps the invariant. -/
theorem SI.set_fresh (hO : ∀ x ∈ O, isFreshName x.vname = false) {st : St} (hG : GoodSt T O st)
    {o t : Estate SyscallState Mem} (h : SI gd opS o t st.rho st.sig) {f' : MVar} {val : Value}
    (hf : isFreshName f'.vname = true) (hn : ∀ v ∈ st.slots ++ st.regs, v.vname ≠ f'.vname) :
    SI gd opS o (t.withVm (t.evm.set f' val)) st.rho st.sig := by
  have hne : ∀ v : MVar, v.vname ≠ f'.vname → (t.withVm (t.evm.set f' val)).evm v = t.evm v :=
    fun v hv => NFToJasminSem.set_ne _ hv
  refine ⟨h.mem, h.scs, fun v hv => ?_, fun p hp x' h' hx hh => ?_, fun p hp x' hx => ?_⟩
  · rw [hne v (by intro e; rw [e] at hv; simp_all)]; exact h.orig v hv
  · rw [hne h' ?_]; exact h.rho p hp x' h' hx hh
    rw [translateVarExt_vname hh]
    rcases (hG.rho p hp).2.2.2 with he | he
    · rw [he]; intro e; have := hO _ (hG.rho p hp).1; rw [e] at this; simp_all
    · exact hn _ (by simp [he])
  · have := h.sig p hp x' hx
    obtain ⟨-, -, hsg⟩ := hG.sig p hp
    cases hs : p.2 with
    | slot s =>
        rw [hs] at this hsg
        intro s' hs'
        rw [hne s' (by rw [translateVarExt_vname hs']; exact hn s (by simp [hsg.2]))]
        exact this s' hs'
    | remat ty e => rw [hs] at this; exact this

end Sem

theorem translateInstrRExt_mv_isSome {d s : JVar} (hd : isGprTy d.vtype = true)
    (hs : isGprTy s.vtype = true) : (translateInstrRExt (mv d s)).isSome = true := by
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hd)
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hs)
  simp [mv, lpv, vi, translateInstrRExt, translateLValExt, translateVarIExt, translatePExprExt,
    translateGVarExt, hd', hs', translateSTypeExt_of_var hd']

theorem instrVars_mv (d s : JVar) : instrVars (mv d s) = [d, s] := by
  simp [mv, lpv, vi, instrVars, lvalVars, pexprVars]

theorem emitOK_mv {st : St} {d s : JVar} (hd : isGprTy d.vtype = true)
    (hs : isGprTy s.vtype = true) (hd' : d ∈ O ∨ d ∈ st.slots ++ st.regs)
    (hs' : s ∈ O ∨ s ∈ st.slots ++ st.regs) : EmitOK T O st (mv d s) := by
  refine ⟨rfl, fun _ => translateInstrRExt_mv_isSome hd hs, fun v hv => ?_⟩
  simp only [instrVars_mv, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hd'
  · exact hs'

/-! ### Eviction -/

theorem evict_rho (res : List JVar) (c : List InstrR) (st : St) (p : JVar × JVar) :
    (evict res c st p).1.rho = st.rho.filter (fun q => q.1 != p.1) := by
  unfold evict; split <;> rfl

theorem evict_good {res : List JVar} {c : List InstrR} {st : St} {p : JVar × JVar}
    (hG : GoodSt T O st) (hp : p ∈ st.rho) :
    GoodSt T O (evict res c st p).1 ∧ StLe st (evict res c st p).1 ∧
      ∀ i ∈ (evict res c st p).2, EmitOK T O (evict res c st p).1 i := by
  obtain ⟨hpO, hpg, hpt, hph⟩ := hG.rho p hp
  unfold evict
  split
  · dsimp only
    have hle : StLe st ⟨st.rho.filter (fun q => q.1 != p.1),
        (p.1, .slot ⟨freshName st.cnt, p.1.vtype⟩) :: st.sig, st.cnt + 1,
        ⟨freshName st.cnt, p.1.vtype⟩ :: st.slots, st.regs⟩ :=
      ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ h => h, by simp⟩
    obtain ⟨hf, hn⟩ := hG.add_fresh (f := ⟨freshName st.cnt, p.1.vtype⟩) rfl hpg
      (st' := ⟨st.rho.filter (fun q => q.1 != p.1),
        (p.1, .slot ⟨freshName st.cnt, p.1.vtype⟩) :: st.sig, st.cnt + 1,
        ⟨freshName st.cnt, p.1.vtype⟩ :: st.slots, st.regs⟩) rfl (by simp)
    refine ⟨⟨fun q hq => ?_, fun q hq => ?_, hf, hn⟩, hle, fun i hi => ?_⟩
    · exact hG.rho q (List.mem_of_mem_filter hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hpO, hpg, rfl, by simp⟩
      · obtain ⟨h1, h2, h3⟩ := hG.sig q hq
        exact ⟨h1, h2, h3.mono hle⟩
    · simp only [List.mem_singleton] at hi; subst hi
      refine emitOK_mv hpg (by rw [hpt]; exact hpg) (Or.inr (by simp)) ?_
      rcases hph with h | h
      · exact Or.inl (h ▸ hpO)
      · exact Or.inr (by simp [h])
  · exact ⟨hG.rho_sub (fun q hq => List.mem_of_mem_filter hq), ⟨fun _ h => h, fun _ h => h, le_rfl⟩,
      by simp⟩

/-- A step of the pass from `st` keeps the invariant, extends the fresh variables, emits
well-formed instructions and keeps the reload sources. -/
structure Res (st : St) (r : St × List InstrR) : Prop where
  good : GoodSt T O r.1
  le : StLe st r.1
  emit : ∀ i ∈ r.2, EmitOK T O r.1 i
  sig : ∀ q ∈ st.sig, q ∈ r.1.sig

theorem Res.refl {st : St} (hG : GoodSt T O st) : Res (T := T) (O := O) st (st, []) :=
  ⟨hG, StLe.refl st, by simp, fun _ h => h⟩

theorem Res.trans {st : St} {r1 r2 : St × List InstrR} (h1 : Res (T := T) (O := O) st r1)
    (h2 : Res (T := T) (O := O) r1.1 r2) : Res (T := T) (O := O) st (r2.1, r1.2 ++ r2.2) where
  good := h2.good
  le := h1.le.trans h2.le
  emit i hi := by
    rcases List.mem_append.mp hi with hi | hi
    · exact (h1.emit i hi).mono h2.le
    · exact h2.emit i hi
  sig q hq := h2.sig q (h1.sig q hq)

theorem evict_res {res : List JVar} {c : List InstrR} {st : St} {p : JVar × JVar}
    (hG : GoodSt T O st) (hp : p ∈ st.rho) : Res (T := T) (O := O) st (evict res c st p) := by
  obtain ⟨h1, h2, h3⟩ := evict_good (res := res) (c := c) hG hp
  refine ⟨h1, h2, h3, fun q hq => ?_⟩
  unfold evict; split <;> simp [hq]

theorem pickVictim_mem {st : St} {prot res : List JVar} {c : List InstrR} {p : JVar × JVar}
    (h : pickVictim st prot res c = some p) : p ∈ st.rho ∧ prot.contains p.1 = false := by
  have := maxBy_mem h
  simp only [List.mem_filter, Bool.not_eq_true'] at this
  exact this

theorem makeRoom_res (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    ∀ (fuel : Nat) (st : St), GoodSt T O st →
      Res (T := T) (O := O) st (makeRoom k need prot res c fuel st)
  | 0, st, hG => Res.refl hG
  | fuel + 1, st, hG => by
      unfold makeRoom
      split
      · exact Res.refl hG
      · split
        · exact Res.refl hG
        · rename_i p hp
          have h1 := evict_res (res := res) (c := c) hG (pickVictim_mem hp).1
          exact h1.trans (makeRoom_res k need prot res c fuel _ h1.good)

theorem reloadFresh_res {st : St} {x : JVar} {src : Src} (hG : GoodSt T O st)
    (hx : (x, src) ∈ st.sig) : Res (T := T) (O := O) st (reloadFresh st x src) := by
  obtain ⟨hxO, hxg, hsrc⟩ := hG.sig _ hx
  have hle : StLe st (reloadFresh st x src).1 :=
    ⟨fun _ h => h, fun _ h => List.mem_cons_of_mem _ h, by simp [reloadFresh]⟩
  obtain ⟨hf, hn⟩ := hG.add_fresh (f := ⟨freshName st.cnt, x.vtype⟩) rfl hxg
    (st' := (reloadFresh st x src).1) rfl (by simp [reloadFresh, List.perm_middle])
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, hf, hn⟩, hle, fun i hi => ?_, fun q hq => hq⟩
  · simp only [reloadFresh, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hxO, hxg, rfl, Or.inr (by simp [reloadFresh])⟩
    · obtain ⟨a, b, c, d⟩ := hG.rho q hq
      exact ⟨a, b, c, d.imp id (fun h => by simp [reloadFresh, h])⟩
  · obtain ⟨a, b, c⟩ := hG.sig q hq
    exact ⟨a, b, c.mono hle⟩
  · simp only [reloadFresh, List.mem_singleton] at hi; subst hi
    cases src with
    | slot s =>
        exact emitOK_mv hxg (hsrc.1 ▸ hxg) (Or.inr (by simp [reloadFresh]))
          (Or.inr (List.mem_append_left _ hsrc.2))
    | remat ty e =>
        obtain ⟨hty, htr, hvars⟩ := hsrc
        refine ⟨rfl, fun hT => ?_, fun v hv => ?_⟩
        · have hR := renOK_renOf (rho := st.rho) (fun p hp => (hG.rho p hp).2.2.1)
          obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp (htr hT)
          obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.mp
            (isSome_translateVarExt_gpr (x := ⟨freshName st.cnt, x.vtype⟩) hxg)
          obtain ⟨ty', hty'⟩ := Option.isSome_iff_exists.mp
            (isSome_translateSTypeExt_gpr (t := ty) (hty ▸ hxg))
          simp [reloadSrc, translateInstrRExt, translateLValExt, translateVarIExt, vi, hf', hty',
            translatePExprExt_renE hR, he']
        · simp only [reloadSrc, instrVars, lvalVars, vi, List.mem_append, List.mem_singleton] at hv
          rcases hv with rfl | hv
          · exact Or.inr (by simp [reloadFresh])
          · obtain ⟨y, hy, hvy | hvy⟩ := pexprVars_renE _ e v hv <;> rw [hvy]
            · exact Or.inl (hvars y hy)
            · rcases renOf_cases st.rho y with ⟨h, -⟩ | h
              · rw [h]; exact Or.inl (hvars y hy)
              · rcases (hG.rho _ h).2.2.2 with h' | h'
                · simp only at h'; rw [h']; exact Or.inl (hvars y hy)
                · exact Or.inr (by simp [reloadFresh, h'])

theorem helper_res (cand : JVar → Bool) {st : St} (y : JVar) (hG : GoodSt T O st) :
    Res (T := T) (O := O) st (helper cand st y) := by
  unfold helper
  split
  · exact Res.refl hG
  · split
    · rename_i ty e hl
      split
      · exact reloadFresh_res hG (lookS_some hl)
      · exact Res.refl hG
    · exact Res.refl hG

theorem helpers_res (cand : JVar → Bool) :
    ∀ (ys : List JVar) (st : St), GoodSt T O st → Res (T := T) (O := O) st (helpers cand st ys)
  | [], st, hG => Res.refl hG
  | y :: ys, st, hG => by
      have h1 := helper_res (T := T) (O := O) cand y hG
      exact h1.trans (helpers_res cand ys _ h1.good)

theorem helpersOf_res (cand : JVar → Bool) {st : St} (src : Src) (hG : GoodSt T O st) :
    Res (T := T) (O := O) st (helpersOf cand st src) := by
  cases src with
  | slot s => exact Res.refl hG
  | remat ty e => exact helpers_res cand _ st hG

theorem dropDead_res {res : List JVar} {c : List InstrR} {st : St} (hG : GoodSt T O st) :
    Res (T := T) (O := O) st (dropDead res c st, []) :=
  ⟨hG.rho_sub (fun q hq => List.mem_of_mem_filter hq), ⟨fun _ h => h, fun _ h => h, le_rfl⟩,
    by simp, fun _ h => h⟩

theorem loadOne_res (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR)
    {st : St} (x : JVar) (hG : GoodSt T O st) :
    Res (T := T) (O := O) st (loadOne k cand prot res c st x) := by
  unfold loadOne
  split
  · exact Res.refl hG
  · split
    · exact Res.refl hG
    · rename_i src hl
      have h1 := makeRoom_res (T := T) (O := O) k (needOf cand src) prot res c st.rho.length st hG
      have h2 := helpersOf_res (T := T) (O := O) cand src h1.good
      have h3 := reloadFresh_res (x := x) (src := src) h2.good (h2.sig _ (h1.sig _ (lookS_some hl)))
      have h4 := dropDead_res (res := res) (c := c) h3.good
      have := ((h1.trans h2).trans h3).trans h4
      simpa using this

theorem loadAll_res (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR) :
    ∀ (xs : List JVar) (st : St), GoodSt T O st →
      Res (T := T) (O := O) st (loadAll k cand prot res c st xs)
  | [], st, hG => Res.refl hG
  | x :: xs, st, hG => by
      have h1 := loadOne_res (T := T) (O := O) k cand prot res c x hG
      exact h1.trans (loadAll_res k cand prot res c xs _ h1.good)

/-- `Res` without the reload sources. -/
structure ResEmit (st : St) (r : St × List InstrR) : Prop where
  good : GoodSt T O r.1
  le : StLe st r.1
  emit : ∀ i ∈ r.2, EmitOK T O r.1 i

theorem Res.toResEmit {st : St} {r : St × List InstrR} (h : Res (T := T) (O := O) st r) :
    ResEmit (T := T) (O := O) st r := ⟨h.good, h.le, h.emit⟩

theorem ResEmit.trans {st : St} {r1 r2 : St × List InstrR} (h1 : ResEmit (T := T) (O := O) st r1)
    (h2 : ResEmit (T := T) (O := O) r1.1 r2) : ResEmit (T := T) (O := O) st (r2.1, r1.2 ++ r2.2) where
  good := h2.good
  le := h1.le.trans h2.le
  emit i hi := by
    rcases List.mem_append.mp hi with hi | hi
    · exact (h1.emit i hi).mono h2.le
    · exact h2.emit i hi

/-- The hypotheses on an original instruction: straight line, over variables of `O`, and
translating when `T` holds. -/
def OrigOK (T' : Prop) (O' : List JVar) (i : InstrR) : Prop :=
  straightI i = true ∧ (∀ v ∈ instrVars i, v ∈ O') ∧ (T' → (translateInstrRExt i).isSome = true)

theorem afterDef_good {cand : JVar → Bool} (hcand : ∀ x, cand x = true → isGprTy x.vtype = true)
    {c : List InstrR} {st : St} {i : InstrR} (hG : GoodSt T O st) (hi : OrigOK T O i) :
    GoodSt T O (afterDef cand c st i) ∧ StLe st (afterDef cand c st i) := by
  obtain ⟨hs, hv, ht⟩ := hi
  have hle : StLe st (afterDef cand c st i) := ⟨fun _ h => h, fun _ h => h, le_rfl⟩
  refine ⟨⟨fun q hq => ?_, fun q hq => ?_, hG.fresh, hG.nodup⟩, hle⟩
  · simp only [afterDef, List.mem_append, List.mem_map, List.mem_filter] at hq
    rcases hq with ⟨x, hx, rfl⟩ | ⟨hq, -⟩
    · simp only [defsOf, List.mem_dedup, List.mem_filter] at hx
      exact ⟨hv x (writesI_sub hx.1), hcand x hx.2, rfl, Or.inl rfl⟩
    · exact hG.rho q hq
  · have hold : ∀ q ∈ st.sig, q.1 ∈ O ∧ isGprTy q.1.vtype = true ∧
        SrcGood T O (afterDef cand c st i) q.1 q.2 := fun q hq =>
      ⟨(hG.sig q hq).1, (hG.sig q hq).2.1, (hG.sig q hq).2.2.mono hle⟩
    simp only [afterDef] at hq
    split at hq
    · rename_i x tag ty e
      split at hq
      · rename_i hc
        rcases List.mem_cons.mp hq with rfl | hq
        · simp only [rematOK, Bool.and_eq_true, beq_iff_eq] at hc
          refine ⟨hv _ (by simp [instrVars, lvalVars]), hcand _ hc.1, hc.2.1.1.1, fun hT => ?_,
            fun v hv' => hv v (by simp [instrVars, hv'])⟩
          have := ht hT
          simp only [translateInstrRExt] at this
          cases h1 : translateLValExt (.Lvar x) <;> cases h2 : translateSTypeExt ty <;>
            cases h3 : translatePExprExt e <;> simp_all
        · exact hold q (List.mem_of_mem_filter hq)
      · exact hold q (List.mem_of_mem_filter hq)
    · exact hold q (List.mem_of_mem_filter hq)

theorem straightI_renI (r : JVar → JVar) {i : InstrR} (h : straightI i = true) :
    straightI (renI r i) = true := by
  cases i <;> simp_all [renI, straightI]

theorem renI_emit {st : St} {i : InstrR} (hG : GoodSt T O st) (hi : OrigOK T O i) :
    EmitOK T O st (renI (renOf st.rho) i) := by
  obtain ⟨hs, hv, ht⟩ := hi
  have hR := renOK_renOf (rho := st.rho) (fun p hp => (hG.rho p hp).2.2.1)
  refine ⟨straightI_renI _ hs, fun hT => ?_, fun v hvi => ?_⟩
  · rw [translateInstrRExt_renI hR hs]; simpa using ht hT
  · obtain ⟨y, hy, hvy | hvy⟩ := instrVars_renI _ hvi <;> rw [hvy]
    · exact Or.inl (hv y hy)
    · rcases renOf_cases st.rho y with ⟨h, -⟩ | h
      · rw [h]; exact Or.inl (hv y hy)
      · rcases (hG.rho _ h).2.2.2 with h' | h'
        · simp only at h'; rw [h']; exact Or.inl (hv y hy)
        · exact Or.inr (by simp [h'])

theorem stepI_res {k : Nat} {cand : JVar → Bool}
    (hcand : ∀ x, cand x = true → isGprTy x.vtype = true) {res : List JVar} {st : St}
    {i : InstrR} {c : List InstrR} (hG : GoodSt T O st) (hi : OrigOK T O i) :
    ResEmit (T := T) (O := O) st (stepI k cand res st i c) := by
  unfold stepI
  dsimp only
  have h0 := dropDead_res (T := T) (O := O) (res := res) (c := i :: c) hG
  have h1 := loadAll_res (T := T) (O := O) k cand (usesOf cand i) res (i :: c) (usesOf cand i)
    (dropDead res (i :: c) st) h0.good
  have h2 := makeRoom_res (T := T) (O := O) k (defsOf cand i).length (usesOf cand i) res (i :: c)
    (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1.rho.length _ h1.good
  obtain ⟨h3, h3le⟩ := afterDef_good (c := c) (i := i) hcand h2.good hi
  have h4 : ResEmit (T := T) (O := O) _ (afterDef cand c _ i, [renI (renOf _) i]) :=
    ⟨h3, h3le, fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj
      exact (renI_emit h2.good hi).mono h3le⟩
  have := ((h0.toResEmit.trans h1.toResEmit).trans h2.toResEmit).trans h4
  simpa using this

theorem goBody_res {k : Nat} {cand : JVar → Bool}
    (hcand : ∀ x, cand x = true → isGprTy x.vtype = true) {res : List JVar} :
    ∀ (c : List InstrR) (st : St), GoodSt T O st → (∀ i ∈ c, OrigOK T O i) →
      ResEmit (T := T) (O := O) st (goBody k cand res st c)
  | [], st, hG, _ => (Res.refl hG).toResEmit
  | i :: c, st, hG, hc => by
      have h1 := stepI_res (k := k) (res := res) (c := c) hcand hG (hc i (by simp))
      exact h1.trans (goBody_res hcand c _ h1.good (fun j hj => hc j (by simp [hj])))

theorem reloadSrc_emit {st : St} {x d : JVar} {src : Src} (hG : GoodSt T O st)
    (hx : (x, src) ∈ st.sig) (hd : d.vtype = x.vtype) (hdO : d ∈ O ∨ d ∈ st.slots ++ st.regs) :
    EmitOK T O st (reloadSrc st.rho d src) := by
  obtain ⟨hxO, hxg, hsrc⟩ := hG.sig _ hx
  cases src with
  | slot s =>
      exact emitOK_mv (hd ▸ hxg) (hsrc.1 ▸ hxg) hdO (Or.inr (List.mem_append_left _ hsrc.2))
  | remat ty e =>
      obtain ⟨hty, htr, hvars⟩ := hsrc
      refine ⟨rfl, fun hT => ?_, fun v hv => ?_⟩
      · have hR := renOK_renOf (rho := st.rho) (fun p hp => (hG.rho p hp).2.2.1)
        obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp (htr hT)
        obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr (hd ▸ hxg))
        obtain ⟨ty', hty'⟩ := Option.isSome_iff_exists.mp
          (isSome_translateSTypeExt_gpr (t := ty) (hty ▸ hxg))
        simp [reloadSrc, translateInstrRExt, translateLValExt, translateVarIExt, vi, hd', hty',
          translatePExprExt_renE hR, he']
      · simp only [reloadSrc, instrVars, lvalVars, vi, List.mem_append, List.mem_singleton] at hv
        rcases hv with rfl | hv
        · exact hdO
        · obtain ⟨y, hy, hvy | hvy⟩ := pexprVars_renE _ e v hv <;> rw [hvy]
          · exact Or.inl (hvars y hy)
          · rcases renOf_cases st.rho y with ⟨h, -⟩ | h
            · rw [h]; exact Or.inl (hvars y hy)
            · rcases (hG.rho _ h).2.2.2 with h' | h'
              · simp only at h'; rw [h']; exact Or.inl (hvars y hy)
              · exact Or.inr (by simp [h'])

theorem fixOne_res {k : Nat} {cand : JVar → Bool} {res : List JVar} {st : St} {r : JVar}
    (hG : GoodSt T O st) (hrO : r ∈ O) (hrg : isGprTy r.vtype = true) :
    ResEmit (T := T) (O := O) st (fixOne k cand res st r) := by
  unfold fixOne
  split
  · rename_i h hl
    split
    · exact (Res.refl hG).toResEmit
    · have h1 := makeRoom_res (T := T) (O := O) k 1 res res [] st.rho.length st hG
      have hrh := hG.rho _ (lookR_some hl)
      have h2 : ResEmit (T := T) (O := O) (makeRoom k 1 res res [] st.rho.length st).1
          ({ (makeRoom k 1 res res [] st.rho.length st).1 with
              rho := (r, r) :: (makeRoom k 1 res res [] st.rho.length st).1.rho.filter
                (fun q => q.1 != r) }, [mv r h]) := by
        refine ⟨⟨fun q hq => ?_, h1.good.sig, h1.good.fresh, h1.good.nodup⟩,
          ⟨fun _ h => h, fun _ h => h, le_rfl⟩, fun j hj => ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hrO, hrg, rfl, Or.inl rfl⟩
          · exact h1.good.rho q (List.mem_of_mem_filter hq)
        · simp only [List.mem_singleton] at hj; subst hj
          refine emitOK_mv hrg (hrh.2.2.1 ▸ hrg) (Or.inl hrO) ?_
          rcases hrh.2.2.2 with h' | h'
          · simp only at h'; rw [h']; exact Or.inl hrO
          · exact Or.inr (List.mem_append_right _ (h1.le.regs h'))
      exact h1.toResEmit.trans h2
  · split
    · exact (Res.refl hG).toResEmit
    · rename_i src hl
      have h1 := makeRoom_res (T := T) (O := O) k (needOf cand src) res res [] st.rho.length st hG
      have h2 := helpersOf_res (T := T) (O := O) cand src h1.good
      have hx := h2.sig _ (h1.sig _ (lookS_some hl))
      have h3 : ResEmit (T := T) (O := O) (helpersOf cand (makeRoom k (needOf cand src) res res []
          st.rho.length st).1 src).1
          (dropDead res [] { (helpersOf cand (makeRoom k (needOf cand src) res res []
            st.rho.length st).1 src).1 with
            rho := (r, r) :: (helpersOf cand (makeRoom k (needOf cand src) res res []
              st.rho.length st).1 src).1.rho },
            [reloadSrc (helpersOf cand (makeRoom k (needOf cand src) res res []
              st.rho.length st).1 src).1.rho r src]) := by
        refine ⟨⟨fun q hq => ?_, h2.good.sig, h2.good.fresh, h2.good.nodup⟩,
          ⟨fun _ h => h, fun _ h => h, le_rfl⟩, fun j hj => ?_⟩
        · simp only [dropDead, List.mem_filter, List.mem_cons] at hq
          rcases hq.1 with rfl | hq
          · exact ⟨hrO, hrg, rfl, Or.inl rfl⟩
          · exact h2.good.rho q hq
        · simp only [List.mem_singleton] at hj; subst hj
          exact reloadSrc_emit h2.good hx rfl (Or.inl hrO)
      have := (h1.toResEmit.trans h2.toResEmit).trans h3
      simpa using this

theorem fixAll_res {k : Nat} {cand : JVar → Bool} {res : List JVar} :
    ∀ (rs : List JVar) (st : St), GoodSt T O st → (∀ r ∈ rs, r ∈ O ∧ isGprTy r.vtype = true) →
      ResEmit (T := T) (O := O) st (fixAll k cand res st rs)
  | [], st, hG, _ => (Res.refl hG).toResEmit
  | r :: rs, st, hG, hr => by
      have h1 := fixOne_res (k := k) (cand := cand) (res := res) hG (hr r (by simp)).1
        (hr r (by simp)).2
      exact h1.trans (fixAll_res rs _ h1.good (fun q hq => hr q (by simp [hq])))

theorem initSt_good {cand : JVar → Bool} (hcand : ∀ x, cand x = true → isGprTy x.vtype = true)
    {res : List JVar} {body : List InstrR} (hO : ∀ v ∈ cmdVars body ++ res, v ∈ O) :
    GoodSt T O (initSt cand res body) := by
  refine ⟨fun q hq => ?_, by simp [initSt], by simp [initSt], by simp [initSt]⟩
  simp only [initSt, List.mem_map, List.mem_dedup, List.mem_filter, Bool.and_eq_true] at hq
  obtain ⟨x, ⟨hx, hc, -⟩, rfl⟩ := hq
  exact ⟨hO x hx, hcand x hc, rfl, Or.inl rfl⟩

section Sem

variable {SyscallState Mem : Type} [MemModel Mem] (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
  (prog : Prog)

theorem evict_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) {res : List JVar}
    {c : List InstrR} {st : St} {p : JVar × JVar} (hG : GoodSt T O st) (hp : p ∈ st.rho)
    {o t : Estate SyscallState Mem} (hSI : SI gd opS o t st.rho st.sig)
    (HD : ∀ x x', liveB res x c = true → translateVarExt x = some x' → (o.evm x').isDefined = true)
    (HW : WT o.evm) :
    ∃ t', RunA aS opS gd prog t (evict res c st p).2 t' ∧
      SI gd opS o t' (evict res c st p).1.rho (evict res c st p).1.sig := by
  obtain ⟨hpO, hpg, hpt, hph⟩ := hG.rho p hp
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hpg)
  obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp
    (isSome_translateVarExt_gpr (x := p.2) (hpt ▸ hpg))
  unfold evict
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    dsimp only
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp
      (isSome_translateVarExt_gpr (x := ⟨freshName st.cnt, p.1.vtype⟩) hpg)
    have hval : t.evm h' = o.evm x' := hSI.rho p hp x' h' hx' hh'
    have hdef := HD p.1 x' hc.1 hx'
    have hsx : s'.vtype = x'.vtype := by
      have h1 := translateSTypeExt_of_var hs'
      have h2 := translateSTypeExt_of_var hx'
      simp only at h1
      rw [h1] at h2; exact Option.some.inj h2
    refine ⟨_, RunA.mv aS opS gd prog hs' hh' hval hdef (by rw [hsx]; exact HW x' hdef), ?_⟩
    have h1 := SI.set_fresh hO hG hSI (f' := s') (val := o.evm x')
      (by rw [translateVarExt_vname hs']; exact isFreshName_freshName _)
      (by rw [translateVarExt_vname hs']; exact hG.new_name)
    refine ⟨h1.mem, h1.scs, h1.orig, fun q hq => h1.rho q (List.mem_of_mem_filter hq),
      fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · intro y hy s'' hs''
      rw [hx'] at hy; cases hy
      rw [hs'] at hs''; cases hs''
      exact ⟨NFToJasminSem.set_same _ _ _, hdef, HW x' hdef⟩
    · exact h1.sig q hq
  · exact ⟨t, RunA.nil aS opS gd prog t, hSI.rho_sub (fun q hq => List.mem_of_mem_filter hq)⟩

/-- A step of the pass from `st` simulates: from every `t` related to `o` by `st`, the
emitted code runs to a `t'` related to `o` by the new state. -/
def SemOK (o : Estate SyscallState Mem) (st : St) (r : St × List InstrR) : Prop :=
  ∀ t, SI gd opS o t st.rho st.sig → ∃ t', RunA aS opS gd prog t r.2 t' ∧
    SI gd opS o t' r.1.rho r.1.sig

theorem SemOK.refl (o : Estate SyscallState Mem) (st : St) :
    SemOK aS opS gd prog o st (st, []) := fun t h => ⟨t, RunA.nil aS opS gd prog t, h⟩

theorem SemOK.trans {o : Estate SyscallState Mem} {st : St} {r1 r2 : St × List InstrR}
    (h1 : SemOK aS opS gd prog o st r1) (h2 : SemOK aS opS gd prog o r1.1 r2) :
    SemOK aS opS gd prog o st (r2.1, r1.2 ++ r2.2) := fun t h => by
  obtain ⟨t1, ht1, h1'⟩ := h1 t h
  obtain ⟨t2, ht2, h2'⟩ := h2 t1 h1'
  exact ⟨t2, RunA.append aS opS gd prog ht1 ht2, h2'⟩

theorem makeRoom_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k need : Nat)
    (prot res : List JVar) (c : List InstrR) {o : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x c = true → translateVarExt x = some x' → (o.evm x').isDefined = true)
    (HW : WT o.evm) :
    ∀ (fuel : Nat) (st : St), GoodSt T O st →
      SemOK aS opS gd prog o st (makeRoom k need prot res c fuel st)
  | 0, st, _ => SemOK.refl aS opS gd prog o st
  | fuel + 1, st, hG => by
      unfold makeRoom
      split
      · exact SemOK.refl aS opS gd prog o st
      · split
        · exact SemOK.refl aS opS gd prog o st
        · rename_i p hp
          have hpm := (pickVictim_mem hp).1
          have h1 : SemOK aS opS gd prog o st (evict res c st p) := fun t h =>
            evict_sem aS opS gd prog hO hG hpm h HD HW
          exact h1.trans aS opS gd prog
            (makeRoom_sem hO k need prot res c HD HW fuel _ (evict_res hG hpm).good)

/-- The variable an original variable is read from in `t`: its holder, else itself. -/
theorem env_of_SI (hO : ∀ x ∈ O, isFreshName x.vname = false) {st : St} (hG : GoodSt T O st)
    {o t : Estate SyscallState Mem} (hSI : SI gd opS o t st.rho st.sig) {y : JVar} (hy : y ∈ O)
    {y' : MVar} (hy' : translateVarExt y = some y') : t.evm (Rof st.rho y') = o.evm y' := by
  have hR := renOK_renOf (rho := st.rho) (fun p hp => (hG.rho p hp).2.2.1)
  have htr := hR.tr y y' hy'
  rcases renOf_cases st.rho y with ⟨h, -⟩ | h
  · rw [h, hy'] at htr
    rw [← Option.some.inj htr]
    exact hSI.orig y' (by rw [translateVarExt_vname hy']; exact hO y hy)
  · exact hSI.rho _ h y' _ hy' htr

/-- The reload of `x` from its source into `d` writes the value of `x` in `o`. -/
theorem reloadSrc_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) {st : St}
    (hG : GoodSt True O st) {o t : Estate SyscallState Mem} (hSI : SI gd opS o t st.rho st.sig)
    {x d : JVar} {src : Src} (hx : (x, src) ∈ st.sig) (hd : d.vtype = x.vtype) {x' d' : MVar}
    (hx' : translateVarExt x = some x') (hd' : translateVarExt d = some d') :
    RunA aS opS gd prog t [reloadSrc st.rho d src] (t.withVm (t.evm.set d' (o.evm x'))) := by
  obtain ⟨-, hxg, hsrc⟩ := hG.sig _ hx
  have hdx : d'.vtype = x'.vtype := by
    have h1 := translateSTypeExt_of_var hd'
    have h2 := translateSTypeExt_of_var hx'
    rw [hd, h2] at h1; exact (Option.some.inj h1).symm
  have hfact := hSI.sig _ hx x' hx'
  cases src with
  | slot s =>
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp
        (isSome_translateVarExt_gpr (x := s) (hsrc.1 ▸ hxg))
      obtain ⟨h1, h2, h3⟩ := hfact s' hs'
      exact RunA.mv aS opS gd prog hd' hs' h1 h2 (by rw [hdx]; exact h3)
  | remat ty e =>
      obtain ⟨hty, htr, hvars⟩ := hsrc
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp (htr trivial)
      have hty' : translateSTypeExt ty = some x'.vtype := hty ▸ translateSTypeExt_of_var hx'
      obtain ⟨w, hw, htr', hdb, htc⟩ := hfact e' x'.vtype he' hty'
      have hR := renOK_renOf (rho := st.rho) (fun p hp => (hG.rho p hp).2.2.1)
      obtain ⟨hf, hrd⟩ := translatePExprExt_of e e' he'
      refine RunA.asgn aS opS gd prog hd' hty'
        (by rw [translatePExprExt_renE hR e, he']; rfl) hdx ?_ htr' hdb htc
      rw [typeE_mrenE, semPexpr_mrenE gd opS _ t o _ (mfrag_typeE _ _ hf) ?_]
      · exact hw
      · intro v hv
        rw [mreads_typeE] at hv
        obtain ⟨y, hy, hyv⟩ := exists_of_mem_mapM_some hrd v hv
        exact env_of_SI opS gd hO hG hSI (hvars y (readsE_sub e y hy)) hyv

theorem reloadFresh_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) {st : St}
    (hG : GoodSt True O st) {o : Estate SyscallState Mem} {x : JVar} {src : Src}
    (hx : (x, src) ∈ st.sig) : SemOK aS opS gd prog o st (reloadFresh st x src) := by
  intro t hSI
  obtain ⟨-, hxg, -⟩ := hG.sig _ hx
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hxg)
  obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.mp
    (isSome_translateVarExt_gpr (x := ⟨freshName st.cnt, x.vtype⟩) hxg)
  refine ⟨_, reloadSrc_sem aS opS gd prog hO hG hSI (d := ⟨freshName st.cnt, x.vtype⟩) hx rfl
    hx' hf', ?_⟩
  have h1 := SI.set_fresh hO hG hSI (f' := f') (val := o.evm x')
    (by rw [translateVarExt_vname hf']; exact isFreshName_freshName _)
    (by rw [translateVarExt_vname hf']; exact hG.new_name)
  refine ⟨h1.mem, h1.scs, h1.orig, fun q hq => ?_, h1.sig⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · intro y h hy hh
    rw [hx'] at hy; cases hy
    rw [hf'] at hh; cases hh
    exact NFToJasminSem.set_same _ _ _
  · exact h1.rho q hq

theorem helper_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (cand : JVar → Bool) {st : St}
    (y : JVar) (hG : GoodSt True O st) {o : Estate SyscallState Mem} :
    SemOK aS opS gd prog o st (helper cand st y) := by
  unfold helper
  split
  · exact SemOK.refl aS opS gd prog o st
  · split
    · rename_i ty e hl
      split
      · exact reloadFresh_sem aS opS gd prog hO hG (lookS_some hl)
      · exact SemOK.refl aS opS gd prog o st
    · exact SemOK.refl aS opS gd prog o st

theorem helpers_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (cand : JVar → Bool)
    {o : Estate SyscallState Mem} :
    ∀ (ys : List JVar) (st : St), GoodSt True O st →
      SemOK aS opS gd prog o st (helpers cand st ys)
  | [], _st, _ => SemOK.refl aS opS gd prog o _
  | y :: ys, _st, hG =>
      (helper_sem aS opS gd prog hO cand y hG).trans aS opS gd prog
        (helpers_sem hO cand ys _ (helper_res cand y hG).good)

theorem helpersOf_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (cand : JVar → Bool)
    {st : St} (src : Src) (hG : GoodSt True O st) {o : Estate SyscallState Mem} :
    SemOK aS opS gd prog o st (helpersOf cand st src) := by
  cases src with
  | slot s => exact SemOK.refl aS opS gd prog o st
  | remat ty e => exact helpers_sem aS opS gd prog hO cand _ st hG

theorem dropDead_sem {res : List JVar} {c : List InstrR} (st : St) (o : Estate SyscallState Mem) :
    SemOK aS opS gd prog o st (dropDead res c st, []) := fun t h =>
  ⟨t, RunA.nil aS opS gd prog t, h.rho_sub (fun _ hq => List.mem_of_mem_filter hq)⟩

theorem loadOne_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (prot res : List JVar) (c : List InstrR) {o : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x c = true → translateVarExt x = some x' → (o.evm x').isDefined = true)
    (HW : WT o.evm) {st : St} (x : JVar) (hG : GoodSt True O st) :
    SemOK aS opS gd prog o st (loadOne k cand prot res c st x) := by
  unfold loadOne
  split
  · exact SemOK.refl aS opS gd prog o st
  · split
    · exact SemOK.refl aS opS gd prog o st
    · rename_i src hl
      have r1 := makeRoom_res (T := True) (O := O) k (needOf cand src) prot res c st.rho.length st hG
      have r2 := helpersOf_res (T := True) (O := O) cand src r1.good
      have hx := r2.sig _ (r1.sig _ (lookS_some hl))
      have h1 := makeRoom_sem aS opS gd prog hO k (needOf cand src) prot res c HD HW
        st.rho.length st hG
      have h2 := helpersOf_sem aS opS gd prog hO cand src r1.good (o := o)
      have h3 := reloadFresh_sem aS opS gd prog hO r2.good hx (o := o)
      have h4 := dropDead_sem aS opS gd prog (res := res) (c := c) (reloadFresh (helpersOf cand
        (makeRoom k (needOf cand src) prot res c st.rho.length st).1 src).1 x src).1 o
      have := ((h1.trans aS opS gd prog h2).trans aS opS gd prog h3).trans aS opS gd prog h4
      simpa using this

theorem loadAll_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (prot res : List JVar) (c : List InstrR) {o : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x c = true → translateVarExt x = some x' → (o.evm x').isDefined = true)
    (HW : WT o.evm) :
    ∀ (xs : List JVar) (st : St), GoodSt True O st →
      SemOK aS opS gd prog o st (loadAll k cand prot res c st xs)
  | [], _st, _ => SemOK.refl aS opS gd prog o _
  | x :: xs, _st, hG =>
      (loadOne_sem aS opS gd prog hO k cand prot res c HD HW x hG).trans aS opS gd prog
        (loadAll_sem hO k cand prot res c HD HW xs _
          (loadOne_res (T := True) (O := O) k cand prot res c x hG).good)

theorem contains_eq_false_iff {l : List JVar} {a : JVar} : l.contains a = false ↔ a ∉ l := by
  rw [← Bool.not_eq_true, List.contains_iff_mem]

theorem mrenE_id : ∀ a : MPexpr, mrenE id a = a
  | .Pvar g => by rcases g with ⟨⟨v, _⟩, gs⟩; cases gs <;> rfl
  | .Pget al aa ws g i => by
      rcases g with ⟨⟨v, _⟩, gs⟩; cases gs <;> simp [mrenE, mrenG, mrenE_id i]
  | .Papp1 op e => by simp [mrenE, mrenE_id e]
  | .Papp2 op a b => by simp [mrenE, mrenE_id a, mrenE_id b]
  | .Pconst _ => rfl
  | .Pbool _ => rfl
  | .Parr_init _ _ => rfl
  | .Psub _ _ _ _ _ => rfl
  | .Pload _ _ _ => rfl
  | .PappN _ _ => rfl
  | .Pif _ _ _ _ => rfl

theorem semPexpr_frame (s1 s2 : Estate SyscallState Mem) (a : MPexpr) (hf : mfrag a = true)
    (h : ∀ v ∈ mreads a, s1.evm v = s2.evm v) :
    semPexpr true gd opS s1 a = semPexpr true gd opS s2 a := by
  have := semPexpr_mrenE gd opS id s1 s2 a hf h
  rwa [mrenE_id] at this

/-- The state after an original instruction: the run of `o` by the instruction and the run
of `t` by its renaming write the same variables with the same values, and the invariant
holds for the state of the pass after the instruction. -/
theorem afterDef_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (cand : JVar → Bool)
    {c : List InstrR} {st : St} {i : InstrR} (hi : OrigOK True O i)
    {j : MInstrR} (hj : translateInstrRExt i = some j) {o t o1 t1 : Estate SyscallState Mem}
    (hSI : SI gd opS o t st.rho st.sig) (hWR : WR t o t1 o1 (mwI (typeI j)))
    (hstep : CatCrypt.Crypto.Jasmin.CoqSemMirror.SemIr aS opS gd prog o (typeI j) o1) :
    SI gd opS o1 t1 (afterDef cand c st i).rho (afterDef cand c st i).sig := by
  obtain ⟨-, -, -, hW⟩ := translateInstrRExt_of hi.1 hj
  have notW : ∀ y y', translateVarExt y = some y' → y ∉ writesI i → y' ∉ mwI (typeI j) := by
    intro y y' hy hny hy'
    obtain ⟨w, hw, hw'⟩ := exists_of_mem_mapM_some hW y' hy'
    exact hny (translateVarExt_inj hw' hy ▸ hw)
  have orig1 : ∀ v : MVar, isFreshName v.vname = false → t1.evm v = o1.evm v := by
    intro v hv
    by_cases hvW : v ∈ mwI (typeI j)
    · exact hWR.inW v hvW
    · rw [(hWR.outW v hvW).1, (hWR.outW v hvW).2]; exact hSI.orig v hv
  refine ⟨hWR.tmem.trans (hSI.mem.trans hWR.omem.symm),
    hWR.tscs.trans (hSI.scs.trans hWR.oscs.symm), orig1, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [afterDef, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true', contains_eq_false_iff] at hq
    rcases hq with ⟨x, hx, rfl⟩ | ⟨hq, h1, h2⟩
    · intro y' h' hy hh
      rw [hy] at hh; cases hh
      simp only [defsOf, List.mem_dedup, List.mem_filter] at hx
      exact orig1 y' (by rw [translateVarExt_vname hy]; exact hO x (hi.2.1 x (writesI_sub hx.1)))
    · intro y' h' hy hh
      rw [(hWR.outW _ (notW _ _ hh h2)).1, (hWR.outW _ (notW _ _ hy h1)).2]
      exact hSI.rho q hq y' h' hy hh
  · have hold : ∀ q ∈ st.sig, (writesI i).contains q.1 = false →
        q.2.reads.any (writesI i).contains = false →
        ∀ x', translateVarExt q.1 = some x' → SrcFact gd opS o1 t1 x' q.2 := by
      intro q hq h1 h2 x' hx'
      rw [contains_eq_false_iff] at h1
      have hfact := hSI.sig q hq x' hx'
      have ho1 : o1.evm x' = o.evm x' := (hWR.outW _ (notW _ _ hx' h1)).2
      cases hs : q.2 with
      | slot s =>
          rw [hs] at hfact h2
          simp only [Src.reads, List.any_cons, List.any_nil, Bool.or_false,
            contains_eq_false_iff] at h2
          intro s' hs'
          rw [ho1, (hWR.outW _ (notW _ _ hs' h2)).1]
          exact hfact s' hs'
      | remat ty e =>
          rw [hs] at hfact h2
          simp only [Src.reads, List.any_eq_false, Bool.not_eq_true, contains_eq_false_iff] at h2
          intro e' ty' he' hty'
          obtain ⟨w, hw, h3⟩ := hfact e' ty' he' hty'
          obtain ⟨hf, hrd⟩ := translatePExprExt_of e e' he'
          refine ⟨w, ?_, by rw [ho1]; exact h3⟩
          rw [semPexpr_frame opS gd o1 o _ (mfrag_typeE _ _ hf) ?_]
          · exact hw
          · intro v hv
            rw [mreads_typeE] at hv
            obtain ⟨y, hy, hyv⟩ := exists_of_mem_mapM_some hrd v hv
            exact (hWR.outW _ (notW _ _ hyv (h2 y hy))).2
    simp only [afterDef] at hq
    split at hq
    · rename_i x tag ty e
      split at hq
      · rename_i hc
        rcases List.mem_cons.mp hq with rfl | hq
        · simp only [rematOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
            contains_eq_false_iff] at hc
          obtain ⟨-, ⟨⟨⟨hty, hxe⟩, -⟩, -⟩⟩ := hc
          simp only [translateInstrRExt] at hj
          cases hl : translateLValExt (.Lvar x) <;> cases hty' : translateSTypeExt ty <;>
            cases he : translatePExprExt e <;> simp only [hl, hty', he, reduceCtorEq,
              Option.some.injEq] at hj
          rename_i l ty' e'
          subst hj
          simp only [translateLValExt, Option.map_eq_some_iff] at hl
          obtain ⟨x'', hx'', rfl⟩ := hl
          have hxv := translateVarExt_of_varI hx''
          simp only [typeI, typeLv] at hstep
          cases hstep with
          | Eassgn _ _ _ _ _ _ v v' hs htr hw =>
              obtain ⟨rfl, htc, hdb, -⟩ := writeVar_ok hw
              intro y' hy'
              rw [hxv] at hy'; cases hy'
              intro e2 ty2 he2 hty2
              rw [he] at he2; cases he2
              rw [hty'] at hty2; cases hty2
              have htyx : ty' = x''.v_var.vtype := by
                have := translateSTypeExt_of_var hxv
                rw [← hty, hty'] at this; exact Option.some.inj this
              obtain ⟨hf, hrd⟩ := translatePExprExt_of e _ he
              have hx1 : (o.withVm (o.evm.set x''.v_var v')).evm x''.v_var = v' :=
                NFToJasminSem.set_same _ _ _
              refine ⟨v, ?_, by rw [hx1]; exact htr, by rw [hx1]; exact hdb,
                by rw [hx1, htyx]; exact htc⟩
              rw [semPexpr_frame opS gd _ o _ (mfrag_typeE _ _ hf) ?_]
              · exact hs
              · intro u hu
                rw [mreads_typeE] at hu
                obtain ⟨y, hy, hyu⟩ := exists_of_mem_mapM_some hrd u hu
                have hne : u ≠ x''.v_var := by
                  rintro rfl
                  exact hxe (translateVarExt_inj hyu hxv ▸ hy)
                exact NFToJasminSem.set_ne_var _ hne
        · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hq
          exact hold q hq.1 hq.2.1 hq.2.2
      · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hq
        exact hold q hq.1 hq.2.1 hq.2.2
    · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hq
      exact hold q hq.1 hq.2.1 hq.2.2

/-- **One original instruction.** A step of `o` by an original instruction gives a run of
`t` by the code the pass emits for it, ending related by the state after it. -/
theorem stepI_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (res : List JVar) {st : St} (hG : GoodSt True O st) {i : InstrR} {c : List InstrR}
    (hi : OrigOK True O i) {o o1 : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x (i :: c) = true → translateVarExt x = some x' →
      (o.evm x').isDefined = true)
    (HW : WT o.evm) {j : MInstrR} (hj : translateInstrRExt i = some j)
    (hstep : CatCrypt.Crypto.Jasmin.CoqSemMirror.SemIr aS opS gd prog o (typeI j) o1)
    {t : Estate SyscallState Mem} (hSI : SI gd opS o t st.rho st.sig) :
    ∃ t1, RunA aS opS gd prog t (stepI k cand res st i c).2 t1 ∧
      SI gd opS o1 t1 (stepI k cand res st i c).1.rho (stepI k cand res st i c).1.sig := by
  unfold stepI
  dsimp only
  have g0 := (dropDead_res (T := True) (O := O) (res := res) (c := i :: c) hG).good
  have g1 := (loadAll_res (T := True) (O := O) k cand (usesOf cand i) res (i :: c)
    (usesOf cand i) _ g0).good
  have g2 := (makeRoom_res (T := True) (O := O) k (defsOf cand i).length (usesOf cand i) res
    (i :: c) (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1.rho.length _ g1).good
  have hS0 : SI gd opS o t (dropDead res (i :: c) st).rho (dropDead res (i :: c) st).sig :=
    hSI.rho_sub (fun _ hq => List.mem_of_mem_filter hq)
  obtain ⟨t1, ht1, hS1⟩ := loadAll_sem aS opS gd prog hO k cand (usesOf cand i) res (i :: c) HD HW
    (usesOf cand i) _ g0 t hS0
  obtain ⟨t2, ht2, hS2⟩ := makeRoom_sem aS opS gd prog hO k (defsOf cand i).length
    (usesOf cand i) res (i :: c) HD HW _ _ g1 t1 hS1
  set st2 := (makeRoom k (defsOf cand i).length (usesOf cand i) res (i :: c)
    (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1.rho.length
    (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1).1 with hst2
  have hR := renOK_renOf (rho := st2.rho) (fun p hp => (g2.rho p hp).2.2.1)
  obtain ⟨hfr, hrd, hbd, -⟩ := translateInstrRExt_of hi.1 hj
  obtain ⟨⟨t3, h3, hWR⟩, -, -⟩ := semIr_rel gd opS aS prog (Rof st2.rho) (t := t2) hfr
    (fun u hu => by
      obtain ⟨y, hy, hyu⟩ := exists_of_mem_mapM_some hrd u hu
      exact env_of_SI opS gd hO g2 hS2
        (hi.2.1 y (readsI_sub (mem_readsI.mpr (Or.inl hy)))) hyu)
    (fun u hu => by
      obtain ⟨y, hy, hyu⟩ := exists_of_mem_mapM_some hbd u hu
      exact hS2.orig u (by
        rw [translateVarExt_vname hyu]
        exact hO y (hi.2.1 y (readsI_sub (mem_readsI.mpr (Or.inr hy)))))) hstep
  rw [← typeI_mrenI] at h3
  have h4 : RunA aS opS gd prog t2 [renI (renOf st2.rho) i] t3 :=
    RunA.single aS opS gd prog (by rw [translateInstrRExt_renI hR hi.1, hj]; rfl) h3
  exact ⟨t3, RunA.append aS opS gd prog (RunA.append aS opS gd prog ht1 ht2) h4,
    afterDef_sem aS opS gd prog hO cand hi hj hS2 hWR hstep⟩

/-- The variables live before a command are defined in the state that runs it, when the
results are defined at the end. -/
theorem liveB_def {res : List JVar} :
    ∀ (c : List InstrR) (o oe : Estate SyscallState Mem), (∀ i ∈ c, OrigOK True O i) →
      RunA aS opS gd prog o c oe →
      (∀ x x', x ∈ res → translateVarExt x = some x' → (oe.evm x').isDefined = true) →
      ∀ x x', liveB res x c = true → translateVarExt x = some x' → (o.evm x').isDefined = true
  | [], o, oe, _, hrun, hres, x, x', hl, hx => by
      obtain ⟨c', hc', hs⟩ := hrun
      simp only [translateCmdExt, Option.some.injEq] at hc'; subst hc'
      cases hs
      simp only [liveB, List.contains_iff_mem] at hl
      exact hres x x' hl hx
  | i :: c, o, oe, hc, hrun, hres, x, x', hl, hx => by
      obtain ⟨j, o1, hj, hstep, hrest⟩ := RunA.cons_inv aS opS gd prog hrun
      have hi := hc i (by simp)
      obtain ⟨hfr, hrd, hbd, hW⟩ := translateInstrRExt_of hi.1 hj
      obtain ⟨⟨t1, -, hWR⟩, hdef, -⟩ := semIr_rel gd opS aS prog id (t := o) hfr
        (fun _ _ => rfl) (fun _ _ => rfl) hstep
      simp only [liveB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_iff_mem, contains_eq_false_iff] at hl
      rcases hl with hl | ⟨hnw, hl⟩
      · rcases mem_readsI.mp hl with hl | hl
        · obtain ⟨u, hu, hxu⟩ := mapM_some_mem hrd x hl
          rw [hx] at hxu; cases hxu
          exact hdef _ (List.mem_append_left _ hu)
        · obtain ⟨u, hu, hxu⟩ := mapM_some_mem hbd x hl
          rw [hx] at hxu; cases hxu
          exact hdef _ (List.mem_append_right _ hu)
      · have ih := liveB_def c o1 oe (fun j hj => hc j (by simp [hj])) hrest hres x x' hl hx
        have hnot : x' ∉ mwI (typeI j) := by
          intro hx'
          obtain ⟨w, hw, hw'⟩ := exists_of_mem_mapM_some hW x' hx'
          exact hnw (translateVarExt_inj hw' hx ▸ hw)
        rw [← (hWR.outW _ hnot).2]
        exact ih

theorem goBody_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (hcand : ∀ x, cand x = true → isGprTy x.vtype = true) (res : List JVar) :
    ∀ (c : List InstrR) (st : St) (o t oe : Estate SyscallState Mem), GoodSt True O st →
      (∀ i ∈ c, OrigOK True O i) → SI gd opS o t st.rho st.sig → RunA aS opS gd prog o c oe →
      WT o.evm →
      (∀ x x', x ∈ res → translateVarExt x = some x' → (oe.evm x').isDefined = true) →
      ∃ te, RunA aS opS gd prog t (goBody k cand res st c).2 te ∧
        SI gd opS oe te (goBody k cand res st c).1.rho (goBody k cand res st c).1.sig ∧
        WT oe.evm
  | [], st, o, t, oe, _, _, hSI, hrun, hW, _ => by
      obtain ⟨c', hc', hs⟩ := hrun
      simp only [translateCmdExt, Option.some.injEq] at hc'; subst hc'
      cases hs
      exact ⟨t, RunA.nil aS opS gd prog t, hSI, hW⟩
  | i :: c, st, o, t, oe, hG, hc, hSI, hrun, hW, hres => by
      have HD := liveB_def aS opS gd prog (i :: c) o oe hc hrun hres
      obtain ⟨j, o1, hj, hstep, hrest⟩ := RunA.cons_inv aS opS gd prog hrun
      have hi := hc i (by simp)
      obtain ⟨hfr, -, -, -⟩ := translateInstrRExt_of hi.1 hj
      obtain ⟨-, -, hW1⟩ := semIr_rel gd opS aS prog id (t := o) hfr
        (fun _ _ => rfl) (fun _ _ => rfl) hstep
      obtain ⟨t1, ht1, hS1⟩ := stepI_sem aS opS gd prog hO k cand res hG hi HD hW hj hstep hSI
      have g1 := (stepI_res (k := k) (res := res) (c := c) hcand hG hi).good
      obtain ⟨te, hte, hSe, hWe⟩ := goBody_sem hO k cand hcand res c _ o1 t1 oe g1
        (fun j hj => hc j (by simp [hj])) hS1 hrest (hW1 hW) hres
      exact ⟨te, RunA.append aS opS gd prog ht1 hte, hSe, hWe⟩

omit [MemModel Mem] in
theorem withVm_set_self (t : Estate SyscallState Mem) (x : MVar) :
    t.withVm (t.evm.set x (t.evm x)) = t := by
  have : t.evm.set x (t.evm x) = t.evm := by
    funext y
    simp only [Vm.set]
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; rw [h]
    · rfl
  rw [this]; rfl

theorem makeRoom_keep (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    ∀ (fuel : Nat) (st : St), ∀ q ∈ st.rho, prot.contains q.1 = true →
      q ∈ (makeRoom k need prot res c fuel st).1.rho
  | 0, st, q, hq, _ => hq
  | fuel + 1, st, q, hq, hp => by
      unfold makeRoom
      split
      · exact hq
      · split
        · exact hq
        · rename_i p hpv
          refine makeRoom_keep k need prot res c fuel _ q ?_ hp
          rw [evict_rho]
          refine List.mem_filter.mpr ⟨hq, ?_⟩
          have := (pickVictim_mem hpv).2
          simp only [bne_iff_ne, ne_eq]
          intro h; rw [← h, hp] at this; cases this

theorem fixOne_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (res : List JVar) {st : St} (hG : GoodSt True O st) {r : JVar} (hrO : r ∈ O)
    (hrres : r ∈ res) {o : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x [] = true → translateVarExt x = some x' →
      (o.evm x').isDefined = true)
    (HW : WT o.evm) : SemOK aS opS gd prog o st (fixOne k cand res st r) := by
  have hrl : liveB res r [] = true := by simp [liveB, hrres]
  have hrf : isFreshName r.vname = false := hO r hrO
  unfold fixOne
  split
  · rename_i h hl
    split
    · exact SemOK.refl aS opS gd prog o st
    · have g1 := (makeRoom_res (T := True) (O := O) k 1 res res [] st.rho.length st hG).good
      have h1 := makeRoom_sem aS opS gd prog hO k 1 res res [] HD HW st.rho.length st hG
      have hkeep := makeRoom_keep k 1 res res [] st.rho.length st _ (lookR_some hl)
        (by simpa using hrres)
      intro t hSI
      obtain ⟨t2, ht2, hS2⟩ := h1 t hSI
      obtain ⟨-, hrg, hhr, -⟩ := g1.rho _ hkeep
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hrg)
      obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp
        (isSome_translateVarExt_gpr (x := h) (hhr ▸ hrg))
      have hval := hS2.rho _ hkeep r' h' hr' hh'
      have hdef := HD r r' hrl hr'
      have ho : o.evm r' = t2.evm r' :=
        (hS2.orig r' (by rw [translateVarExt_vname hr']; exact hrf)).symm
      have h3 := RunA.mv aS opS gd prog hr' hh' hval hdef (HW r' hdef)
      rw [ho, withVm_set_self] at h3
      refine ⟨t2, RunA.append aS opS gd prog ht2 h3, hS2.mem, hS2.scs, hS2.orig,
        fun q hq => ?_, hS2.sig⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · intro y' h'' hy hh
        rw [hy] at hh; cases hh
        exact hS2.orig y' (by rw [translateVarExt_vname hy]; exact hrf)
      · exact hS2.rho q (List.mem_of_mem_filter hq)
  · split
    · exact SemOK.refl aS opS gd prog o st
    · rename_i src hl
      have r1 := makeRoom_res (T := True) (O := O) k (needOf cand src) res res [] st.rho.length st hG
      have r2 := helpersOf_res (T := True) (O := O) cand src r1.good
      have hx := r2.sig _ (r1.sig _ (lookS_some hl))
      have h12 := (makeRoom_sem aS opS gd prog hO k (needOf cand src) res res [] HD HW
        st.rho.length st hG).trans aS opS gd prog
        (helpersOf_sem aS opS gd prog hO cand src r1.good (o := o))
      intro t hSI
      obtain ⟨t2, ht2, hS2⟩ := h12 t hSI
      obtain ⟨-, hrg, -⟩ := r2.good.sig _ hx
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (isSome_translateVarExt_gpr hrg)
      have h3 := reloadSrc_sem aS opS gd prog hO r2.good hS2 hx rfl hr' hr'
      have ho : o.evm r' = t2.evm r' :=
        (hS2.orig r' (by rw [translateVarExt_vname hr']; exact hrf)).symm
      rw [ho, withVm_set_self] at h3
      refine ⟨t2, by simpa using RunA.append aS opS gd prog ht2 h3, hS2.mem, hS2.scs, hS2.orig,
        fun q hq => ?_, hS2.sig⟩
      simp only [dropDead, List.mem_filter, List.mem_cons] at hq
      rcases hq.1 with rfl | hq
      · intro y' h'' hy hh
        rw [hy] at hh; cases hh
        exact hS2.orig y' (by rw [translateVarExt_vname hy]; exact hrf)
      · exact hS2.rho q hq

theorem fixAll_sem (hO : ∀ x ∈ O, isFreshName x.vname = false) (k : Nat) (cand : JVar → Bool)
    (res : List JVar) {o : Estate SyscallState Mem}
    (HD : ∀ x x', liveB res x [] = true → translateVarExt x = some x' →
      (o.evm x').isDefined = true)
    (HW : WT o.evm) :
    ∀ (rs : List JVar) (st : St), GoodSt True O st → (∀ r ∈ rs, r ∈ O ∧ r ∈ res ∧
      isGprTy r.vtype = true) → SemOK aS opS gd prog o st (fixAll k cand res st rs)
  | [], _st, _, _ => SemOK.refl aS opS gd prog o _
  | r :: rs, _st, hG, hr =>
      (fixOne_sem aS opS gd prog hO k cand res hG (hr r (by simp)).1 (hr r (by simp)).2.1 HD
        HW).trans aS opS gd prog
        (fixAll_sem hO k cand res HD HW rs _
          (fixOne_res (k := k) (cand := cand) (res := res) hG (hr r (by simp)).1
            (hr r (by simp)).2.2).good (fun q hq => hr q (by simp [hq])))

end Sem

end Inv

/-! ## 11. Well-formedness and translation of the spilled unit -/

section Struct

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz

theorem mem_cmdVars : ∀ {l : List InstrR} {v : JVar}, v ∈ cmdVars l ↔ ∃ i ∈ l, v ∈ instrVars i
  | [], v => by simp [cmdVars]
  | i :: l, v => by
      simp only [cmdVars, List.mem_append, mem_cmdVars, List.mem_cons, exists_eq_or_imp]

theorem cmdCalls_straight : ∀ {l : List InstrR}, (∀ i ∈ l, straightI i = true) → cmdCalls l = []
  | [], _ => by simp [cmdCalls]
  | i :: l, h => by
      have hi := h i (by simp)
      have hl := cmdCalls_straight (l := l) (fun j hj => h j (List.mem_cons_of_mem _ hj))
      cases i <;> simp_all [cmdCalls, instrCalls, straightI]

theorem regWordB_gpr {fn : JazzFn} {x : JVar} (h : regWordB fn x = true) :
    isGprTy x.vtype = true := by
  simp only [regWordB, Bool.and_eq_true] at h
  exact h.1

/-- The pass state and body of `run` are well formed over the variables of the function. -/
theorem run_res {T : Prop} (k : Nat) (fn : JazzFn) (hs : ∀ i ∈ fn.fd.body, straightI i = true)
    (hT : ∀ i ∈ fn.fd.body, T → (translateInstrRExt i).isSome = true) :
    GoodSt T (cmdVars fn.fd.body ++ resOf fn) (run k fn).1 ∧
      ∀ i ∈ (run k fn).2, EmitOK T (cmdVars fn.fd.body ++ resOf fn) (run k fn).1 i := by
  have hO : ∀ v ∈ cmdVars fn.fd.body ++ resOf fn, v ∈ cmdVars fn.fd.body ++ resOf fn :=
    fun _ h => h
  have h0 := initSt_good (T := T) (fun x h => regWordB_gpr (fn := fn) h) hO
  have h1 := goBody_res (k := k) (res := resOf fn) (fun x h => regWordB_gpr (fn := fn) h)
    fn.fd.body _ h0 (fun i hi => ⟨hs i hi,
      fun v hv => List.mem_append_left _ (mem_cmdVars.mpr ⟨i, hi, hv⟩), hT i hi⟩)
  have h2 := fixAll_res (k := k) (cand := regWordB fn) (res := resOf fn)
    (((resOf fn).filter (regWordB fn)).dedup) _ h1.good (fun r hr => by
      simp only [List.mem_dedup, List.mem_filter] at hr
      exact ⟨List.mem_append_right _ hr.1, regWordB_gpr hr.2⟩)
  have := h1.trans h2
  exact ⟨this.good, this.emit⟩

theorem ptyOf_toSType (t : SType) : (ptyOf t).toSType = t := by
  cases t <;> simp [ptyOf, PType.toSType, WSize.bytes]

theorem mem_env_declsOf {fn : JazzFn} {st : St} {v : JVar} (hv : v ∈ st.slots ++ st.regs) :
    (v.vname, v.vtype) ∈ ({ fn with decls := fn.decls ++ declsOf st } : JazzFn).env := by
  simp only [JazzFn.env, List.mem_append, List.mem_map, List.mem_flatMap, declsOf] at hv ⊢
  right
  rcases hv with hv | hv
  · exact ⟨_, Or.inr (Or.inl ⟨v, hv, rfl⟩), v.vname, by simp, by simp [ptyOf_toSType]⟩
  · exact ⟨_, Or.inr (Or.inr ⟨v, hv, rfl⟩), v.vname, by simp, by simp [ptyOf_toSType]⟩

theorem isFreshName_ne {n : String} (hn : isFreshName n = false) (m : Nat) :
    n ≠ freshName m := by
  intro h; rw [h, isFreshName_freshName] at hn; cases hn

/-- **The pass keeps well-formedness.** -/
theorem spillFn_wellFormed (k : Nat) {callees : List String} {fn : JazzFn}
    (h : fn.wellFormedB callees = true) : (spillFn k fn).wellFormedB callees = true := by
  unfold spillFn
  split
  · rename_i hg
    simp only [Bool.and_eq_true, List.all_eq_true] at hg
    obtain ⟨hs, hfr⟩ := hg
    obtain ⟨hG, hE⟩ := run_res (T := False) k fn hs (fun _ _ h => h.elim)
    simp only [JazzFn.wellFormedB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      decide_eq_true_eq, List.contains_iff_mem, Bool.or_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, ?_⟩, h7⟩, ?_⟩
    · have heq : ∀ g : JazzFn, g.fd.params = fn.fd.params →
          g.decls = fn.decls ++ declsOf (run k fn).1 →
          List.map Prod.fst g.env = List.map Prod.fst fn.env ++
            ((run k fn).1.slots ++ (run k fn).1.regs).map (·.vname) := by
        intro g hp hd
        have hf : ∀ (c : Storage) (l : List JVar), List.flatMap (fun a : Decl => a.names)
            (l.map fun s => ({ storage := c, ty := ptyOf s.vtype, names := [s.vname] } : Decl)) =
            l.map (·.vname) := by
          intro c l; induction l <;> simp_all
        simp [JazzFn.env, hp, hd, declsOf, List.flatMap_append, Function.comp_def,
          List.map_flatMap, hf]
      rw [heq _ (by rfl) (by rfl)]
      have hfn : ∀ n ∈ List.map Prod.fst fn.env, isFreshName n = false := by
        intro n hn
        simp only [noFreshB, List.all_eq_true, Bool.not_eq_true'] at hfr
        exact hfr n (List.mem_append_left _ hn)
      refine List.nodup_append.mpr ⟨h5, hG.nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      simp only [List.mem_map] at hb
      obtain ⟨v, hv, rfl⟩ := hb
      obtain ⟨-, n, -, hn⟩ := hG.fresh v hv
      exact isFreshName_ne (hfn _ ha) n hn
    · intro v hv
      simp only [JazzFn.usedVars, List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨i, hi, hvi⟩ := mem_cmdVars.mp hv
        rcases (hE i hi).2.2 v hvi with hO | hF
        · have : v ∈ fn.usedVars := by simpa [JazzFn.usedVars, resOf] using hO
          have := h6 v this
          simp only [JazzFn.env, List.mem_append] at this ⊢
          simp only [List.mem_append, List.mem_flatMap] at this ⊢
          rcases this with h' | ⟨d, hd, h'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨d, Or.inl hd, h'⟩
        · exact mem_env_declsOf hF
      · have := h6 v (by simp [JazzFn.usedVars, hv])
        simp only [JazzFn.env, List.mem_append, List.mem_flatMap] at this ⊢
        rcases this with h' | ⟨d, hd, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨d, Or.inl hd, h'⟩
    · intro n hn
      rw [cmdCalls_straight (fun i hi => (hE i hi).1)] at hn
      simp at hn
  · exact h

theorem spillUnit_wellFormed (k : Nat) {u : JazzUnit} (h : u.wellFormedB = true) :
    (spillUnit k u).wellFormedB = true := by
  have hc : (spillUnit k u).callees = u.callees := by
    simp only [JazzUnit.callees, spillUnit, List.map_map]
    congr 1
    refine List.map_congr_left fun f _ => ?_
    simp only [Function.comp_apply, spillFn]; split <;> rfl
  simp only [JazzUnit.wellFormedB, List.all_eq_true] at h ⊢
  intro f hf
  rw [hc]
  simp only [spillUnit, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact spillFn_wellFormed k (h g hg)

theorem mapM_isSome_iff {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (l.mapM f).isSome = true ↔ ∀ a ∈ l, (f a).isSome = true
  | [] => by simp
  | a :: l => by
      rw [List.mapM_cons, List.forall_mem_cons, ← mapM_isSome_iff (l := l)]
      cases f a <;> cases l.mapM f <;> simp

theorem translateCmdExt_isSome_iff :
    ∀ {c : List InstrR}, (translateCmdExt c).isSome = true ↔ ∀ i ∈ c, (translateInstrRExt i).isSome = true
  | [] => by simp [translateCmdExt]
  | i :: c => by
      simp only [translateCmdExt, List.mem_cons, forall_eq_or_imp]
      rw [← translateCmdExt_isSome_iff (c := c)]
      cases translateInstrRExt i <;> cases translateCmdExt c <;> simp

theorem translateFn_isSome_iff (f : JazzFn) : (translateFn f).isSome = true ↔
    (f.fd.params.mapM (fun p => translateVarIExt p.var)).isSome = true ∧
      (translateCmdExt f.fd.body).isSome = true ∧
      (f.fd.results.mapM translateVarIExt).isSome = true := by
  unfold translateFn
  cases f.fd.params.mapM (fun p => translateVarIExt p.var) <;>
    cases translateCmdExt f.fd.body <;> cases f.fd.results.mapM translateVarIExt <;> simp

/-- The pass keeps the translation of a function to the `psem.v` mirror. -/
theorem translateFn_isSome_spill (k : Nat) {f : JazzFn} (h : (translateFn f).isSome = true) :
    (translateFn (spillFn k f)).isSome = true := by
  unfold spillFn
  split
  · rename_i hg
    simp only [Bool.and_eq_true, List.all_eq_true] at hg
    rw [translateFn_isSome_iff] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    have hb := translateCmdExt_isSome_iff.mp h2
    obtain ⟨-, hE⟩ := run_res (T := True) k f hg.1 (fun i hi _ => hb i hi)
    exact ⟨h1, translateCmdExt_isSome_iff.mpr (fun i hi => (hE i hi).2.1 trivial), h3⟩
  · exact h

/-- **The spilled unit translates.** When a unit translates to a mirror program, so does the
spilled unit. -/
theorem translateUnit_isSome_spill (k : Nat) {u : JazzUnit} (h : (translateUnit u).isSome = true) :
    (translateUnit (spillUnit k u)).isSome = true := by
  simp only [translateUnit, Option.isSome_map] at h ⊢
  rw [mapM_isSome_iff] at h ⊢
  intro f hf
  simp only [spillUnit, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact translateFn_isSome_spill k (h g hg)

end Struct

/-! ## 12. Semantic preservation -/

section Main

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
open CatCrypt.Crypto.Jasmin.CoqSemMirror (Estate OpSem AsmSem GlobDecls Prog Sem MemModel)

variable {SyscallState Mem : Type} [MemModel Mem] (aS : AsmSem) (opS : OpSem) (gd : GlobDecls)
  (prog : Prog)

/-- **Semantic preservation of the pass in the `psem.v` mirror.** A run of the typed
translation of the body of `fn` from `s` to `s'`, from a state whose defined values have the
types of their variables and ending with defined results, gives a run of the typed
translation of the spilled body from `s` to a state with the memory and syscall state of
`s'` that agrees with `s'` on every variable whose name does not start with the fresh
prefix, in particular on every variable of `fn`. -/
theorem spillFn_sem (k : Nat) (fn : JazzFn) {c : List MInstr}
    (hc : translateCmdExt fn.fd.body = some c) {s s' : Estate SyscallState Mem}
    (hrun : Sem aS opS gd prog s (typeC c) s') (hwt : WT s.evm)
    (hres : ∀ r ∈ fn.fd.results, ∀ r', translateVarIExt r = some r' →
      (s'.evm r'.v_var).isDefined = true) :
    ∃ c' t', translateCmdExt (spillFn k fn).fd.body = some c' ∧
      Sem aS opS gd prog s (typeC c') t' ∧ t'.emem = s'.emem ∧ t'.escs = s'.escs ∧
      ∀ v : MVar, isFreshName v.vname = false → t'.evm v = s'.evm v := by
  unfold spillFn
  split
  · rename_i hg
    simp only [Bool.and_eq_true, List.all_eq_true] at hg
    obtain ⟨hs, hfr⟩ := hg
    have hO : ∀ x ∈ cmdVars fn.fd.body ++ resOf fn, isFreshName x.vname = false := by
      intro x hx
      simp only [noFreshB, List.all_eq_true, Bool.not_eq_true'] at hfr
      exact hfr _ (List.mem_append_right _ (List.mem_map_of_mem hx))
    have hb := translateCmdExt_isSome_iff.mp (by rw [hc]; rfl)
    have hOK : ∀ i ∈ fn.fd.body, OrigOK True (cmdVars fn.fd.body ++ resOf fn) i :=
      fun i hi => ⟨hs i hi, fun v hv => List.mem_append_left _ (mem_cmdVars.mpr ⟨i, hi, hv⟩),
        fun _ => hb i hi⟩
    have hcand : ∀ x, regWordB fn x = true → isGprTy x.vtype = true := fun x h => regWordB_gpr h
    have g0 := initSt_good (T := True) (O := cmdVars fn.fd.body ++ resOf fn) hcand
      (res := resOf fn) (body := fn.fd.body) (fun _ h => h)
    have hS0 : SI gd opS s s (initSt (regWordB fn) (resOf fn) fn.fd.body).rho
        (initSt (regWordB fn) (resOf fn) fn.fd.body).sig := by
      refine ⟨rfl, rfl, fun _ _ => rfl, fun q hq x' h' hx hh => ?_, by simp [initSt]⟩
      simp only [initSt, List.mem_map] at hq
      obtain ⟨y, -, rfl⟩ := hq
      rw [hx] at hh; cases hh; rfl
    have hres' : ∀ x x', x ∈ resOf fn → translateVarExt x = some x' →
        (s'.evm x').isDefined = true := by
      intro x x' hx hx'
      simp only [resOf, List.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact hres r hr { v_var := x' } (by simp [translateVarIExt, hx'])
    obtain ⟨te, hte, hSe, hWe⟩ := goBody_sem aS opS gd prog hO k (regWordB fn) hcand (resOf fn)
      fn.fd.body _ s s s' g0 hOK hS0 ⟨c, hc, hrun⟩ hwt hres'
    have g1 := (goBody_res (k := k) (res := resOf fn) hcand fn.fd.body _ g0 hOK).good
    obtain ⟨tf, htf, hSf⟩ := fixAll_sem aS opS gd prog hO k (regWordB fn) (resOf fn)
      (fun x x' hl hx => hres' x x' (by simpa [liveB] using hl) hx) hWe
      (((resOf fn).filter (regWordB fn)).dedup) _ g1 (fun r hr => by
        simp only [List.mem_dedup, List.mem_filter] at hr
        exact ⟨List.mem_append_right _ hr.1, hr.1, regWordB_gpr hr.2⟩) te hSe
    obtain ⟨c', hc', hsem⟩ := RunA.append aS opS gd prog hte htf
    exact ⟨c', tf, hc', hsem, hSf.mem, hSf.scs, hSf.orig⟩
  · exact ⟨c, s', hc, hrun, rfl, rfl, fun _ _ => rfl⟩

end Main

/-! ## 13. The liveness check -/

section Live

theorem mem_liveScan (k : Nat) (reg : JVar → Bool) (res : List JVar) :
    ∀ (c : List InstrR) (x : JVar), x ∈ (liveScan k reg res c).1 ↔ reg x = true ∧ liveB res x c = true
  | [], x => by simp [liveScan, liveB, and_comm]
  | i :: c, x => by
      simp only [liveScan, List.mem_dedup, List.mem_append, List.mem_filter, mem_liveScan k reg res c,
        Bool.not_eq_true', contains_eq_false_iff, liveB, Bool.or_eq_true, Bool.and_eq_true,
        List.contains_iff_mem]
      tauto

theorem liveScan_ok (k : Nat) (reg : JVar → Bool) (res : List JVar) :
    ∀ (c : List InstrR), (liveScan k reg res c).2 = true →
      ∀ (p : Nat) (i : InstrR) (rest : List InstrR), c.drop p = i :: rest →
        ((liveScan k reg res (i :: rest)).1 ++ (writesI i).filter reg).dedup.length ≤ k
  | [], _, p, i, rest, h => by simp at h
  | j :: c, hok, 0, i, rest, h => by
      simp only [List.drop_zero, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [liveScan, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.2
  | j :: c, hok, p + 1, i, rest, h => by
      simp only [liveScan, Bool.and_eq_true] at hok
      exact liveScan_ok k reg res c hok.1 p i rest (by simpa using h)

theorem length_le_of_sub {S L : List JVar} (hS : S.Nodup) (h : ∀ x ∈ S, x ∈ L) :
    S.length ≤ L.dedup.length :=
  (List.subperm_of_subset hS (fun x hx => List.mem_dedup.mpr (h x hx))).length_le

/-- **Soundness of the liveness check.** -/
theorem liveRegsB_sound {k : Nat} {fn : JazzFn} (h : liveRegsB k fn = true) : LiveRegs k fn := by
  simp only [liveRegsB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun p i rest hp S hS hx => ?_⟩
  have hok := liveScan_ok k (regWordB fn) (resOf fn) _ h.2 p i rest hp
  refine (length_le_of_sub hS fun x hxS => ?_).trans hok
  obtain ⟨hr, hl⟩ := hx x hxS
  rcases hl with hl | hl
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hl, hr⟩)
  · exact List.mem_append_left _ ((mem_liveScan k _ _ _ x).mpr ⟨hr, hl⟩)

/-- A register certificate for a command: before each instruction a set `Ri` of variables,
within the set before it, that contains the register variables it reads, with at most `k`
register variables in `Ri` and its outputs; the set after the instruction is within `Ri` and
its outputs. -/
def CertC (k : Nat) (reg : JVar → Bool) : List JVar → List InstrR → List JVar → Prop
  | R, [], R' => ∀ x ∈ R', x ∈ R
  | R, i :: c, R' => ∃ Ri : List JVar, (∀ x ∈ Ri, x ∈ R) ∧
      (∀ x ∈ readsI i, reg x = true → x ∈ Ri) ∧
      (Ri ++ (writesI i).filter reg).dedup.length ≤ k ∧
      ∃ R1 : List JVar, (∀ x ∈ R1, x ∈ Ri ∨ x ∈ writesI i) ∧ CertC k reg R1 c R'

theorem CertC.mono {k : Nat} {reg : JVar → Bool} {R R0 R' : List JVar} {c : List InstrR}
    (hR : ∀ x ∈ R0, x ∈ R) (h : CertC k reg R0 c R') : CertC k reg R c R' := by
  cases c with
  | nil => exact fun x hx => hR x (h x hx)
  | cons i c =>
      obtain ⟨Ri, h1, h2⟩ := h
      exact ⟨Ri, fun x hx => hR x (h1 x hx), h2⟩

theorem CertC.append {k : Nat} {reg : JVar → Bool} :
    ∀ {R R1 R2 : List JVar} {a b : List InstrR}, CertC k reg R a R1 → CertC k reg R1 b R2 →
      CertC k reg R (a ++ b) R2
  | _, _, _, [], _, ha, hb => CertC.mono ha hb
  | _, _, _, _ :: _, _, ⟨Ri, h1, h2, h3, R1', h4, h5⟩, hb =>
      ⟨Ri, h1, h2, h3, R1', h4, CertC.append h5 hb⟩

/-- A certificate bounds the liveness check. -/
theorem CertC.live {k : Nat} {reg : JVar → Bool} {res : List JVar} :
    ∀ {R R' : List JVar} {c : List InstrR}, CertC k reg R c R' →
      (∀ x ∈ res, reg x = true → x ∈ R') →
      (liveScan k reg res c).2 = true ∧ ∀ x ∈ (liveScan k reg res c).1, x ∈ R
  | R, R', [], h, hres => by
      refine ⟨rfl, fun x hx => ?_⟩
      simp only [liveScan, List.mem_dedup, List.mem_filter] at hx
      exact h x (hres x hx.1 hx.2)
  | R, R', i :: c, ⟨Ri, h1, h2, h3, R1, h4, h5⟩, hres => by
      obtain ⟨ihok, ihsub⟩ := CertC.live h5 hres
      have hsub : ∀ x ∈ (liveScan k reg res (i :: c)).1, x ∈ Ri := by
        intro x hx
        simp only [liveScan, List.mem_dedup, List.mem_append, List.mem_filter, Bool.not_eq_true',
          contains_eq_false_iff] at hx
        rcases hx with ⟨hx, hr⟩ | ⟨hx, hw⟩
        · exact h2 x hx hr
        · rcases h4 x (ihsub x hx) with h | h
          · exact h
          · exact absurd h hw
      have hle : ((liveScan k reg res (i :: c)).1 ++ (writesI i).filter reg).dedup.length ≤ k := by
        refine (length_le_of_sub (List.nodup_dedup _) fun x hx => ?_).trans h3
        rw [List.mem_dedup, List.mem_append] at hx
        rcases hx with hx | hx
        · exact List.mem_append_left _ (hsub x hx)
        · exact List.mem_append_right _ hx
      refine ⟨?_, fun x hx => h1 x (hsub x hx)⟩
      simp only [liveScan, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ihok, hle⟩

mutual
theorem readsE_renE (r : JVar → JVar) : ∀ e : PExpr, readsE (renE r e) = (readsE e).map r
  | .Pconst _ => rfl
  | .Pbool _ => rfl
  | .Parr_init _ => rfl
  | .Pvar g => by unfold renE renG readsE; split <;> simp_all
  | .Pget _ _ g i => by
      simp only [renE, readsE, readsE_renE r i, List.map_append]
      unfold renG; split <;> simp_all
  | .Psub _ _ _ g i => by
      simp only [renE, readsE, readsE_renE r i, List.map_append]
      unfold renG; split <;> simp_all
  | .Pload _ x o => by simp [renE, readsE, readsE_renE r o]
  | .Papp1 _ e => by simp [renE, readsE, readsE_renE r e]
  | .Papp2 _ a b => by simp [renE, readsE, readsE_renE r a, readsE_renE r b]
  | .PappN _ es => by simp [renE, readsE, readsEs_renEs r es]
  | .Pif _ c a b => by simp [renE, readsE, readsE_renE r c, readsE_renE r a, readsE_renE r b]

theorem readsEs_renEs (r : JVar → JVar) : ∀ es : List PExpr, readsEs (renEs r es) = (readsEs es).map r
  | [] => rfl
  | e :: es => by simp [renEs, readsEs, readsE_renE r e, readsEs_renEs r es]
end

theorem readsI_renI (r : JVar → JVar) {i : InstrR} {v : JVar} (h : v ∈ readsI (renI r i)) :
    (∃ y ∈ rdR i, v = r y) ∨ v ∈ rdB i := by
  cases i with
  | Cassgn lv tag ty e =>
      simp only [renI, readsI, List.mem_append, readsE_renE, List.mem_map] at h
      rcases h with ⟨y, hy, rfl⟩ | h
      · exact Or.inl ⟨y, by simp [rdR, hy], rfl⟩
      · cases lv with
        | Lmem ws x o =>
            simp only [renLv, readsLv, List.mem_cons, readsE_renE, List.mem_map] at h
            rcases h with rfl | ⟨y, hy, rfl⟩
            · exact Or.inl ⟨x.var, by simp [rdR, lvIdx], rfl⟩
            · exact Or.inl ⟨y, by simp [rdR, lvIdx, hy], rfl⟩
        | Laset aa ws x i =>
            simp only [renLv, readsLv, List.mem_cons, readsE_renE, List.mem_map] at h
            rcases h with rfl | ⟨y, hy, rfl⟩
            · exact Or.inr (by simp [rdB, lvBase])
            · exact Or.inl ⟨y, by simp [rdR, lvIdx, hy], rfl⟩
        | Lasub aa ws n x i =>
            simp only [renLv, readsLv, List.mem_cons, readsE_renE, List.mem_map] at h
            rcases h with rfl | ⟨y, hy, rfl⟩
            · exact Or.inr (by simp [rdB, lvBase])
            · exact Or.inl ⟨y, by simp [rdR, lvIdx, hy], rfl⟩
        | Lnone _ _ => simp [renLv, readsLv] at h
        | Lvar _ => simp [renLv, readsLv] at h
  | Copn lvs tag op es =>
      simp only [renI, readsI, readsEs_renEs, List.mem_map] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact Or.inl ⟨y, by simp [rdR, hy], rfl⟩
  | _ => simp [renI, readsI] at h

theorem writesI_renI (r : JVar → JVar) (i : InstrR) : writesI (renI r i) = writesI i := by
  cases i with
  | Cassgn lv _ _ _ => cases lv <;> rfl
  | _ => rfl

theorem readsI_mv (d s : JVar) : readsI (mv d s) = [s] := by
  simp [mv, lpv, vi, readsI, readsE, readsLv]

theorem writesI_mv (d s : JVar) : writesI (mv d s) = [d] := by
  simp [mv, vi, writesI, writesLv]

theorem readsI_reloadSrc_remat (rho : List (JVar × JVar)) (d : JVar) (ty : SType) (e : PExpr) :
    readsI (reloadSrc rho d (.remat ty e)) = (readsE e).map (renOf rho) := by
  simp [reloadSrc, readsI, readsE_renE, readsLv]

theorem writesI_reloadSrc (rho : List (JVar × JVar)) (d : JVar) (src : Src) :
    writesI (reloadSrc rho d src) = [d] := by
  cases src <;> simp [reloadSrc, mv, vi, writesI, writesLv]

theorem lookR_of_mem {rho : List (JVar × JVar)} (hk : (rho.map Prod.fst).Nodup) {x h : JVar}
    (hm : (x, h) ∈ rho) : lookR rho x = some h := by
  cases hl : lookR rho x with
  | none => exact absurd rfl (lookR_none hl _ hm)
  | some h' =>
      have hm' := lookR_some hl
      have := List.inj_on_of_nodup_map hk hm hm' rfl
      cases this; rfl

theorem lookS_of_mem {sig : List (JVar × Src)} (hk : (sig.map Prod.fst).Nodup) {x : JVar}
    {s : Src} (hm : (x, s) ∈ sig) : lookS sig x = some s := by
  cases hl : lookS sig x with
  | none =>
      have : (lookS sig x).isSome = true := lookS_isSome_iff.mpr ⟨_, hm, rfl⟩
      rw [hl] at this; cases this
  | some s' =>
      have hm' := lookS_some hl
      have := List.inj_on_of_nodup_map hk hm hm' rfl
      cases this; rfl

theorem length_filter_key {rho : List (JVar × JVar)} (hk : (rho.map Prod.fst).Nodup)
    {p : JVar × JVar} (hp : p ∈ rho) : (rho.filter (fun q => q.1 != p.1)).length + 1 = rho.length := by
  induction rho with
  | nil => simp at hp
  | cons a l ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hk
      rcases List.mem_cons.mp hp with rfl | hp
      · have : l.filter (fun q => q.1 != p.1) = l := by
          refine List.filter_eq_self.mpr fun q hq => ?_
          simp only [bne_iff_ne, ne_eq]
          intro h; exact hk.1 ⟨q, hq, h⟩
        simp [this]
      · have hne : (a.1 != p.1) = true := by
          simp only [bne_iff_ne, ne_eq]
          intro h; exact hk.1 ⟨p, hp, h.symm⟩
        simp [hne, ih hk.2 hp]

section LiveInv

variable (k : Nat) (cand : JVar → Bool) (res : List JVar) (m : Nat)

/-- The liveness invariant of the pass before the command `c`: holder and source keys are
distinct, at most `k` holders, holders of register variables, every live register variable
has a holder or a source, and every rematerialised right-hand side is stable over `c`, does
not read its variable, reads at most `m` register variables, each rematerialised without
register reads. -/
structure LInv (c : List InstrR) (st : St) : Prop where
  keys : (st.rho.map Prod.fst).Nodup
  skeys : (st.sig.map Prod.fst).Nodup
  len : st.rho.length ≤ k
  kcand : ∀ p ∈ st.rho, cand p.1 = true
  skcand : ∀ p ∈ st.sig, cand p.1 = true
  live : ∀ x, cand x = true → liveB res x c = true →
    (∃ h, (x, h) ∈ st.rho) ∨ ∃ s, (x, s) ∈ st.sig
  remat : ∀ x ty e, (x, Src.remat ty e) ∈ st.sig →
    (∀ y ∈ readsE e, stableB c y = true) ∧ x ∉ readsE e ∧ (candReads cand e).length ≤ m ∧
    ∀ y ∈ candReads cand e, ∃ ty' e', (y, Src.remat ty' e') ∈ st.sig ∧ candReads cand e' = []

/-- The holders of a state. -/
def H (st : St) : List JVar := st.rho.map Prod.snd

variable {k cand res m}

theorem dropDead_live {c : List InstrR} {st : St} (hL : LInv k cand res m c st) (reg : JVar → Bool) :
    LInv k cand res m c (dropDead res c st) ∧ CertC k reg (H st) [] (H (dropDead res c st)) := by
  refine ⟨⟨hL.keys.sublist (List.Sublist.map _ List.filter_sublist), hL.skeys,
    (List.length_filter_le _ _).trans hL.len, fun p hp => hL.kcand p (List.mem_of_mem_filter hp),
    hL.skcand, fun x hx hl => ?_, hL.remat⟩, fun x hx => ?_⟩
  · rcases hL.live x hx hl with ⟨h, hh⟩ | hs
    · exact Or.inl ⟨h, List.mem_filter.mpr ⟨hh, hl⟩⟩
    · exact Or.inr hs
  · simp only [H, dropDead, List.mem_map] at hx ⊢
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, List.mem_of_mem_filter hq, rfl⟩

theorem H_filter_sub {st : St} {P : JVar × JVar → Bool} :
    ∀ x ∈ (st.rho.filter P).map Prod.snd, x ∈ H st := by
  intro x hx
  simp only [List.mem_map, H] at hx ⊢
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, List.mem_of_mem_filter hq, rfl⟩

theorem CertC.nil_sub {reg : JVar → Bool} {R R' : List JVar} (h : ∀ x ∈ R', x ∈ R) :
    CertC k reg R [] R' := h

/-- The certificate of one instruction `i` from `R`, reading registers of `R`, with at most
`k` registers in `R` and its outputs, to `R'` within `R` and its outputs. -/
theorem CertC.single {reg : JVar → Bool} {R R' : List JVar} {i : InstrR}
    (hr : ∀ x ∈ readsI i, reg x = true → x ∈ R)
    (hk : (R ++ (writesI i).filter reg).dedup.length ≤ k)
    (h' : ∀ x ∈ R', x ∈ R ∨ x ∈ writesI i) : CertC k reg R [i] R' :=
  ⟨R, fun _ h => h, hr, hk, R', h', fun _ h => h⟩

theorem evict_live {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) {c : List InstrR} {st : St} (hL : LInv k cand res m c st)
    {p : JVar × JVar} (hp : p ∈ st.rho) (hsl : ∀ s ∈ (evict res c st p).1.slots, s ∈ Zs) :
    LInv k cand res m c (evict res c st p).1 ∧
      CertC k reg (H st) (evict res c st p).2 (H (evict res c st p).1) ∧
      (evict res c st p).1.rho.length + 1 = st.rho.length := by
  have hlen : (evict res c st p).1.rho.length + 1 = st.rho.length := by
    rw [evict_rho]; exact length_filter_key hL.keys hp
  refine ⟨?_, ?_, hlen⟩ <;> unfold evict at hsl ⊢ <;> split
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    dsimp only
    refine ⟨hL.keys.sublist (List.Sublist.map _ List.filter_sublist), ?_,
      (List.length_filter_le _ _).trans hL.len, fun q hq => hL.kcand q (List.mem_of_mem_filter hq),
      fun q hq => ?_, fun x hx hl => ?_, fun x ty e hx => ?_⟩
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      refine ⟨fun q hq h => ?_, hL.skeys⟩
      have : (lookS st.sig p.1).isSome = true := lookS_isSome_iff.mpr ⟨q, hq, h⟩
      rw [hc.2] at this; cases this
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hL.kcand p hp
      · exact hL.skcand q hq
    · by_cases hxp : x = p.1
      · subst hxp; exact Or.inr ⟨_, List.mem_cons_self⟩
      · rcases hL.live x hx hl with ⟨h, hh⟩ | ⟨s, hs⟩
        · exact Or.inl ⟨h, List.mem_filter.mpr ⟨hh, by simpa using hxp⟩⟩
        · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs⟩
    · rcases List.mem_cons.mp hx with h | hx
      · cases h
      · obtain ⟨h1, h2, h3, h4⟩ := hL.remat x ty e hx
        exact ⟨h1, h2, h3, fun y hy => by
          obtain ⟨ty', e', h5, h6⟩ := h4 y hy
          exact ⟨ty', e', List.mem_cons_of_mem _ h5, h6⟩⟩
  · rename_i hc
    refine ⟨hL.keys.sublist (List.Sublist.map _ List.filter_sublist), hL.skeys,
      (List.length_filter_le _ _).trans hL.len, fun q hq => hL.kcand q (List.mem_of_mem_filter hq),
      hL.skcand, fun x hx hl => ?_, hL.remat⟩
    by_cases hxp : x = p.1
    · subst hxp
      rcases hL.live _ hx hl with ⟨h, hh⟩ | hs
      · have : (lookS st.sig p.1).isSome = true := by
          by_contra hn
          exact hc (by simp [hl, Option.not_isSome_iff_eq_none.mp hn])
        exact Or.inr (by
          obtain ⟨q, hq, hq1⟩ := lookS_isSome_iff.mp this
          exact ⟨q.2, hq1 ▸ hq⟩)
      · exact Or.inr hs
    · rcases hL.live x hx hl with ⟨h, hh⟩ | hs
      · exact Or.inl ⟨h, List.mem_filter.mpr ⟨hh, by simpa using hxp⟩⟩
      · exact Or.inr hs
  · rename_i hc
    rw [if_pos hc] at hsl
    dsimp only at hsl ⊢
    refine CertC.single ?_ ?_ ?_
    · intro x hx _
      rw [readsI_mv, List.mem_singleton] at hx
      subst hx
      exact List.mem_map_of_mem hp
    · have hs : reg ⟨freshName st.cnt, p.1.vtype⟩ = false := hZ _ (hsl _ List.mem_cons_self)
      rw [writesI_mv]
      simp only [List.filter_cons, hs, List.filter_nil]
      exact (List.dedup_sublist _).length_le.trans (by simpa [H] using hL.len)
    · intro x hx
      exact Or.inl (H_filter_sub x hx)
  · exact CertC.nil_sub (fun x hx => H_filter_sub x hx)

omit k cand res m in
theorem evict_slots (res : List JVar) (c : List InstrR) (st : St) (p : JVar × JVar) :
    ∀ s ∈ st.slots, s ∈ (evict res c st p).1.slots := by
  intro s hs; unfold evict; split
  · exact List.mem_cons_of_mem _ hs
  · exact hs

omit k cand res m in
theorem makeRoom_slots (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    ∀ (fuel : Nat) (st : St), ∀ s ∈ st.slots, s ∈ (makeRoom k need prot res c fuel st).1.slots
  | 0, _, _, hs => hs
  | fuel + 1, st, s, hs => by
      unfold makeRoom
      split
      · exact hs
      · split
        · exact hs
        · exact makeRoom_slots k need prot res c fuel _ s (evict_slots res c st _ s hs)

theorem keys_le_prot {c0 : List InstrR} {st : St} (hL : LInv k cand res m c0 st)
    {prot : List JVar} (h : ∀ q ∈ st.rho, prot.contains q.1 = true) :
    st.rho.length ≤ ((prot.filter cand).dedup).length := by
  have : (st.rho.map Prod.fst).length ≤ ((prot.filter cand).dedup).length :=
    length_le_of_sub hL.keys (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact List.mem_filter.mpr ⟨by simpa using h q hq, hL.kcand q hq⟩)
  simpa using this

theorem makeRoom_live {reg : JVar → Bool} {Zs : List JVar} (hZ : ∀ s ∈ Zs, reg s = false)
    (need : Nat) (prot : List JVar) (hP : ((prot.filter cand).dedup).length + need ≤ k)
    (c : List InstrR) :
    ∀ (fuel : Nat) (st : St), LInv k cand res m c st → st.rho.length ≤ fuel →
      (∀ s ∈ (makeRoom k need prot res c fuel st).1.slots, s ∈ Zs) →
      LInv k cand res m c (makeRoom k need prot res c fuel st).1 ∧
      CertC k reg (H st) (makeRoom k need prot res c fuel st).2
        (H (makeRoom k need prot res c fuel st).1) ∧
      (makeRoom k need prot res c fuel st).1.rho.length + need ≤ k
  | 0, st, hL, hf, _ => by
      refine ⟨hL, CertC.nil_sub (fun _ h => h), ?_⟩
      simp only [makeRoom]
      omega
  | fuel + 1, st, hL, hf, hsl => by
      unfold makeRoom at hsl ⊢
      split
      · rename_i hroom
        exact ⟨hL, CertC.nil_sub (fun _ h => h), hroom⟩
      · rename_i hroom
        split
        · rename_i hpv
          exfalso
          simp only [pickVictim, maxBy_eq_none, List.filter_eq_nil_iff, Bool.not_eq_true',
            Bool.not_eq_false] at hpv
          have := keys_le_prot hL (prot := prot) (fun q hq => by simpa using hpv q hq)
          omega
        · rename_i p hpv
          rw [if_neg hroom] at hsl
          simp only [hpv] at hsl
          have hpm := (pickVictim_mem hpv).1
          obtain ⟨h1, h2, h3⟩ := evict_live hZ (reg := reg) hL hpm (fun s hs =>
            hsl s (makeRoom_slots k need prot res c fuel _ s hs))
          obtain ⟨h4, h5, h6⟩ := makeRoom_live hZ need prot hP c fuel _ h1 (by omega) hsl
          exact ⟨h4, CertC.append h2 h5, h6⟩

/-- A reload into a fresh holder: the reload reads registers held or no register at all. -/
theorem reloadFresh_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR} {st : St}
    (hG : GoodSt T O st) (hL : LInv k cand res m c st) {x : JVar} {src : Src}
    (hx : (x, src) ∈ st.sig) (hnx : ∀ q ∈ st.rho, q.1 ≠ x) (hroom : st.rho.length + 1 ≤ k)
    (hrd : ∀ ty e, src = .remat ty e → ∀ y ∈ readsE e, cand y = true → ∃ h, (y, h) ∈ st.rho)
    (hsl : ∀ s ∈ st.slots, s ∈ Zs) :
    LInv k cand res m c (reloadFresh st x src).1 ∧
      CertC k reg (H st) (reloadFresh st x src).2 (H (reloadFresh st x src).1) ∧
      (∃ h, (x, h) ∈ (reloadFresh st x src).1.rho) ∧
      (∀ q ∈ st.rho, q ∈ (reloadFresh st x src).1.rho) ∧
      (∀ q ∈ (reloadFresh st x src).1.rho, q ∈ st.rho ∨ q.1 = x) := by
  obtain ⟨-, -, hsrc⟩ := hG.sig _ hx
  refine ⟨⟨?_, hL.skeys, by simpa [reloadFresh] using hroom, fun q hq => ?_, hL.skcand,
    fun y hy hl => ?_, hL.remat⟩, CertC.single ?_ ?_ ?_, ⟨_, List.mem_cons_self⟩,
    fun q hq => List.mem_cons_of_mem _ hq, fun q hq => ?_⟩
  · simp only [reloadFresh, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun q hq h => hnx q hq h, hL.keys⟩
  · simp only [reloadFresh, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hL.skcand _ hx
    · exact hL.kcand q hq
  · rcases hL.live y hy hl with ⟨h, hh⟩ | hs
    · exact Or.inl ⟨h, List.mem_cons_of_mem _ hh⟩
    · exact Or.inr hs
  · intro v hv hrv
    cases src with
    | slot s =>
        rw [reloadSrc, readsI_mv, List.mem_singleton] at hv
        subst hv
        rw [hZ _ (hsl _ hsrc.2)] at hrv; cases hrv
    | remat ty e =>
        rw [readsI_reloadSrc_remat, List.mem_map] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rcases renOf_cases st.rho y with ⟨h, hn⟩ | h
        · rw [h] at hrv ⊢
          rw [hreg y (hsrc.2.2 y (readsE_sub e y hy))] at hrv
          obtain ⟨h', hh'⟩ := hrd ty e rfl y hy hrv
          exact absurd rfl (lookR_none hn _ hh')
        · exact List.mem_map_of_mem h
  · simp only [writesI_reloadSrc]
    refine (List.dedup_sublist _).length_le.trans ?_
    simp only [List.length_append, H, List.length_map]
    have := List.length_filter_le reg [(⟨freshName st.cnt, x.vtype⟩ : JVar)]
    simp only [List.length_singleton] at this
    omega
  · intro v hv
    simp only [reloadFresh, H, List.map_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inr (by simp [writesI_reloadSrc])
    · exact Or.inl hv
  · simp only [reloadFresh, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inr rfl
    · exact Or.inl hq

theorem helper_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR} {st : St}
    (hG : GoodSt T O st) (hL : LInv k cand res m c st) (y : JVar) (hroom : st.rho.length + 1 ≤ k)
    (hy : (∃ h, (y, h) ∈ st.rho) ∨ ∃ ty e, (y, Src.remat ty e) ∈ st.sig ∧ candReads cand e = [])
    (hsl : ∀ s ∈ st.slots, s ∈ Zs) :
    LInv k cand res m c (helper cand st y).1 ∧
      CertC k reg (H st) (helper cand st y).2 (H (helper cand st y).1) ∧
      (∃ h, (y, h) ∈ (helper cand st y).1.rho) ∧
      (∀ q ∈ st.rho, q ∈ (helper cand st y).1.rho) ∧
      (∀ q ∈ (helper cand st y).1.rho, q ∈ st.rho ∨ q.1 = y) ∧
      (helper cand st y).1.rho.length ≤ st.rho.length + 1 ∧
      (helper cand st y).1.sig = st.sig ∧ (helper cand st y).1.slots = st.slots := by
  unfold helper
  split
  · rename_i hl
    obtain ⟨q, hq, hq1⟩ := lookR_isSome_iff.mp hl
    exact ⟨hL, CertC.nil_sub (fun _ h => h), ⟨q.2, hq1 ▸ hq⟩, fun _ h => h,
      fun q hq => Or.inl hq, Nat.le_succ _, rfl, rfl⟩
  · rename_i hl
    have hnx : ∀ q ∈ st.rho, q.1 ≠ y := fun q hq h => hl (lookR_isSome_iff.mpr ⟨q, hq, h⟩)
    obtain ⟨ty0, e0, hy0, he0⟩ : ∃ ty e, (y, Src.remat ty e) ∈ st.sig ∧ candReads cand e = [] := by
      rcases hy with ⟨h, hh⟩ | h
      · exact absurd rfl (hnx _ hh)
      · exact h
    have hls := lookS_of_mem hL.skeys hy0
    rw [hls]
    simp only [he0, List.isEmpty_nil, if_true]
    obtain ⟨h1, h2, h3, h4, h5⟩ := reloadFresh_live hZ hreg hG hL hy0 hnx hroom
      (fun ty e he y' hy' hc => by
        cases he
        have : y' ∈ candReads cand e0 := by simp [candReads, hy', hc]
        rw [he0] at this; cases this) hsl
    exact ⟨h1, h2, h3, h4, h5, by simp [reloadFresh], rfl, rfl⟩

theorem helpers_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR} :
    ∀ (ys : List JVar) (st : St), GoodSt T O st → LInv k cand res m c st →
      st.rho.length + 1 + ys.length ≤ k →
      (∀ y ∈ ys, (∃ h, (y, h) ∈ st.rho) ∨
        ∃ ty e, (y, Src.remat ty e) ∈ st.sig ∧ candReads cand e = []) →
      (∀ s ∈ st.slots, s ∈ Zs) →
      LInv k cand res m c (helpers cand st ys).1 ∧
      CertC k reg (H st) (helpers cand st ys).2 (H (helpers cand st ys).1) ∧
      (∀ y ∈ ys, ∃ h, (y, h) ∈ (helpers cand st ys).1.rho) ∧
      (∀ q ∈ st.rho, q ∈ (helpers cand st ys).1.rho) ∧
      (∀ q ∈ (helpers cand st ys).1.rho, q ∈ st.rho ∨ q.1 ∈ ys) ∧
      (helpers cand st ys).1.rho.length + 1 ≤ k ∧
      (helpers cand st ys).1.sig = st.sig ∧ (helpers cand st ys).1.slots = st.slots
  | [], st, _, hL, hroom, _, _ =>
      ⟨hL, CertC.nil_sub (fun _ h => h), by simp, fun _ h => h, fun q hq => Or.inl hq,
        by simpa [helpers] using hroom, rfl, rfl⟩
  | y :: ys, st, hG, hL, hroom, hys, hsl => by
      simp only [List.length_cons] at hroom
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := helper_live hZ hreg hG hL y (by omega)
        (hys y (by simp)) hsl
      have g1 := (helper_res (T := T) (O := O) cand y hG).good
      obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := helpers_live hZ hreg ys _ g1 h1 (by omega)
        (fun z hz => by
          rcases hys z (by simp [hz]) with ⟨h, hh⟩ | ⟨ty, e, he, hc⟩
          · exact Or.inl ⟨h, h4 _ hh⟩
          · exact Or.inr ⟨ty, e, h7 ▸ he, hc⟩)
        (by rw [h8]; exact hsl)
      refine ⟨i1, CertC.append h2 i2, fun z hz => ?_, fun q hq => i4 q (h4 q hq), fun q hq => ?_,
        i6, i7.trans h7, i8.trans h8⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · obtain ⟨h, hh⟩ := h3; exact ⟨h, i4 _ hh⟩
        · exact i3 z hz
      · rcases i5 q hq with hq | hq
        · rcases h5 q hq with hq | hq
          · exact Or.inl hq
          · exact Or.inr (by simp [hq])
        · exact Or.inr (List.mem_cons_of_mem _ hq)

omit k cand res m in
theorem makeRoom_rho_sub (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    ∀ (fuel : Nat) (st : St), ∀ q ∈ (makeRoom k need prot res c fuel st).1.rho, q ∈ st.rho
  | 0, _, _, hq => hq
  | fuel + 1, st, q, hq => by
      unfold makeRoom at hq
      split at hq
      · exact hq
      · split at hq
        · exact hq
        · have := makeRoom_rho_sub k need prot res c fuel _ q hq
          rw [evict_rho] at this
          exact List.mem_of_mem_filter this

theorem loadOne_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR} {st : St}
    (hG : GoodSt T O st) (hL : LInv k cand res m c st) (prot : List JVar)
    (hprot : ((prot.filter cand).dedup).length + 1 + m ≤ k)
    (hpl : ∀ y ∈ prot, liveB res y c = true) (x : JVar) (hxc : cand x = true)
    (hxl : liveB res x c = true) (hsl : ∀ s ∈ (loadOne k cand prot res c st x).1.slots, s ∈ Zs) :
    LInv k cand res m c (loadOne k cand prot res c st x).1 ∧
      CertC k reg (H st) (loadOne k cand prot res c st x).2 (H (loadOne k cand prot res c st x).1) ∧
      (∃ h, (x, h) ∈ (loadOne k cand prot res c st x).1.rho) ∧
      (∀ q ∈ st.rho, prot.contains q.1 = true → q ∈ (loadOne k cand prot res c st x).1.rho) := by
  unfold loadOne at hsl ⊢
  split
  · rename_i hl
    obtain ⟨q, hq, hq1⟩ := lookR_isSome_iff.mp hl
    exact ⟨hL, CertC.nil_sub (fun _ h => h), ⟨q.2, hq1 ▸ hq⟩, fun q hq _ => hq⟩
  · rename_i hl
    rw [if_neg hl] at hsl
    have hnx : ∀ q ∈ st.rho, q.1 ≠ x := fun q hq h => hl (lookR_isSome_iff.mpr ⟨q, hq, h⟩)
    split
    · rename_i hs
      exfalso
      rcases hL.live x hxc hxl with ⟨h, hh⟩ | ⟨s, hs'⟩
      · exact hnx _ hh rfl
      · have : (lookS st.sig x).isSome = true := lookS_isSome_iff.mpr ⟨_, hs', rfl⟩
        rw [hs] at this; cases this
    · rename_i src hs
      rw [hs] at hsl
      simp only at hsl ⊢
      have hxs := lookS_some hs
      have hneed : needOf cand src ≤ 1 + m := by
        cases src with
        | slot s => simp [needOf]
        | remat ty e => simp only [needOf]; have := (hL.remat x ty e hxs).2.2.1; omega
      have r1 := makeRoom_res (T := T) (O := O) k (needOf cand src) prot res c st.rho.length st hG
      have r2 := helpersOf_res (T := T) (O := O) cand src r1.good
      have r3 := reloadFresh_res (x := x) (src := src) r2.good (r2.sig _ (r1.sig _ hxs))
      have hsl3 : ∀ s ∈ (reloadFresh (helpersOf cand (makeRoom k (needOf cand src) prot res c
          st.rho.length st).1 src).1 x src).1.slots, s ∈ Zs := hsl
      obtain ⟨l1, c1, b1⟩ := makeRoom_live hZ (reg := reg) (need := needOf cand src) prot
        (by omega) c st.rho.length st hL le_rfl (fun s hs => hsl3 s (r3.le.slots (r2.le.slots hs)))
      -- the helpers
      have hhelp : LInv k cand res m c (helpersOf cand (makeRoom k (needOf cand src) prot res c
            st.rho.length st).1 src).1 ∧
          CertC k reg (H (makeRoom k (needOf cand src) prot res c st.rho.length st).1)
            (helpersOf cand (makeRoom k (needOf cand src) prot res c st.rho.length st).1 src).2
            (H (helpersOf cand (makeRoom k (needOf cand src) prot res c
              st.rho.length st).1 src).1) ∧
          (∀ ty e, src = .remat ty e → ∀ y ∈ candReads cand e, ∃ h, (y, h) ∈
            (helpersOf cand (makeRoom k (needOf cand src) prot res c
              st.rho.length st).1 src).1.rho) ∧
          (∀ q ∈ (makeRoom k (needOf cand src) prot res c st.rho.length st).1.rho,
            q ∈ (helpersOf cand (makeRoom k (needOf cand src) prot res c
              st.rho.length st).1 src).1.rho) ∧
          (∀ q ∈ (helpersOf cand (makeRoom k (needOf cand src) prot res c
              st.rho.length st).1 src).1.rho,
            q ∈ (makeRoom k (needOf cand src) prot res c st.rho.length st).1.rho ∨
            ∃ ty e, src = .remat ty e ∧ q.1 ∈ candReads cand e) ∧
          (helpersOf cand (makeRoom k (needOf cand src) prot res c
              st.rho.length st).1 src).1.rho.length + 1 ≤ k := by
        cases src with
        | slot s =>
            have hn : needOf cand (Src.slot s) = 1 := rfl
            exact ⟨l1, CertC.nil_sub (fun _ h => h), fun _ _ h => (by cases h), fun _ h => h,
              fun q hq => Or.inl hq, by simp only [helpersOf]; omega⟩
        | remat ty e =>
            obtain ⟨-, -, -, h4⟩ := hL.remat x ty e hxs
            have hn : needOf cand (Src.remat ty e) = 1 + (candReads cand e).length := rfl
            obtain ⟨i1, i2, i3, i4, i5, i6, -, -⟩ := helpers_live hZ hreg (candReads cand e) _
              r1.good l1 (by omega)
              (fun y hy => by
                obtain ⟨ty', e', h5, h6⟩ := h4 y hy
                exact Or.inr ⟨ty', e', r1.sig _ h5, h6⟩)
              (fun s hs => hsl3 s (r3.le.slots (r2.le.slots hs)))
            refine ⟨i1, i2, fun ty' e' he y hy => ?_, i4, fun q hq => ?_, i6⟩
            · cases he; exact i3 y hy
            · rcases i5 q hq with h | h
              · exact Or.inl h
              · exact Or.inr ⟨ty, e, rfl, h⟩
      obtain ⟨l2, c2, h2, k2, n2, b2⟩ := hhelp
      obtain ⟨l3, c3, h3, k3, -⟩ := reloadFresh_live hZ hreg r2.good l2
        (r2.sig _ (r1.sig _ hxs))
        (fun q hq h => by
          rcases n2 q hq with hq | ⟨ty, e, rfl, hq'⟩
          · exact hnx q (makeRoom_rho_sub k _ prot res c _ st q hq) h
          · have := (hL.remat x ty e hxs).2.1
            rw [h] at hq'
            exact this (List.mem_filter.mp (List.mem_dedup.mp hq')).1)
        b2
        (fun ty e he y hy hc => h2 ty e he y (by simp [candReads, hy, hc]))
        (fun s hs => hsl3 s (r3.le.slots hs))
      obtain ⟨l4, c4⟩ := dropDead_live (c := c) l3 reg
      refine ⟨l4, ?_, ?_, fun q hq hp => ?_⟩
      · have := CertC.append (CertC.append c1 c2) (CertC.append c3 c4)
        simpa using this
      · obtain ⟨h, hh⟩ := h3
        exact ⟨h, List.mem_filter.mpr ⟨hh, hxl⟩⟩
      · refine List.mem_filter.mpr ⟨k3 _ (k2 _ (makeRoom_keep k _ prot res c _ st q hq hp)), ?_⟩
        exact hpl q.1 (by simpa using hp)

theorem loadAll_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR}
    (prot : List JVar) (hprot : ((prot.filter cand).dedup).length + 1 + m ≤ k)
    (hpl : ∀ y ∈ prot, liveB res y c = true) :
    ∀ (xs : List JVar) (st : St), GoodSt T O st → LInv k cand res m c st →
      (∀ x ∈ xs, cand x = true ∧ x ∈ prot) →
      (∀ s ∈ (loadAll k cand prot res c st xs).1.slots, s ∈ Zs) →
      LInv k cand res m c (loadAll k cand prot res c st xs).1 ∧
      CertC k reg (H st) (loadAll k cand prot res c st xs).2 (H (loadAll k cand prot res c st xs).1) ∧
      (∀ x ∈ xs, ∃ h, (x, h) ∈ (loadAll k cand prot res c st xs).1.rho) ∧
      (∀ q ∈ st.rho, prot.contains q.1 = true → q ∈ (loadAll k cand prot res c st xs).1.rho)
  | [], st, _, hL, _, _ => ⟨hL, CertC.nil_sub (fun _ h => h), by simp, fun _ hq _ => hq⟩
  | x :: xs, st, hG, hL, hxs, hsl => by
      have r1 := loadOne_res (T := T) (O := O) k cand prot res c x hG
      have hsl1 : ∀ s ∈ (loadOne k cand prot res c st x).1.slots, s ∈ Zs := fun s hs =>
        hsl s ((loadAll_res (T := T) (O := O) k cand prot res c xs _ r1.good).le.slots hs)
      obtain ⟨l1, c1, h1, k1⟩ := loadOne_live hZ hreg hG hL prot hprot hpl x (hxs x (by simp)).1
        (hpl x (hxs x (by simp)).2) hsl1
      obtain ⟨l2, c2, h2, k2⟩ := loadAll_live hZ hreg prot hprot hpl xs _ r1.good l1
        (fun y hy => hxs y (by simp [hy])) hsl
      refine ⟨l2, CertC.append c1 c2, fun y hy => ?_, fun q hq hp => k2 q (k1 q hq hp) hp⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · obtain ⟨h, hh⟩ := h1
        exact ⟨h, k2 _ hh (by simpa using (hxs y (by simp)).2)⟩
      · exact h2 y hy

omit k cand res m in
theorem afterDef_rho_mem {cand : JVar → Bool} {c : List InstrR} {st : St} {i : InstrR}
    {q : JVar × JVar} :
    q ∈ (afterDef cand c st i).rho ↔ (∃ x ∈ defsOf cand i, q = (x, x)) ∨
      (q ∈ st.rho ∧ q.1 ∉ writesI i ∧ q.2 ∉ writesI i) := by
  simp only [afterDef, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', contains_eq_false_iff]
  constructor
  · rintro (⟨x, hx, rfl⟩ | h)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  · rintro (⟨x, hx, rfl⟩ | h)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩

/-- The sources kept by `afterDef`. -/
def keptSig (i : InstrR) (sig : List (JVar × Src)) : List (JVar × Src) :=
  sig.filter (fun p => !(writesI i).contains p.1 && !(p.2.reads.any (writesI i).contains))

omit k cand res m in
theorem afterDef_sig_mem {cand : JVar → Bool} {c : List InstrR} {st : St} {i : InstrR}
    {q : JVar × Src} (hq : q ∈ (afterDef cand c st i).sig) :
    q ∈ keptSig i st.sig ∨ ∃ x tag ty e, i = .Cassgn (.Lvar x) tag ty e ∧ q = (x.var, .remat ty e) ∧
      cand x.var = true ∧ rematOK cand (keptSig i st.sig) c x.var ty e = true := by
  simp only [afterDef] at hq
  split at hq
  · rename_i x tag ty e
    split at hq
    · rename_i hc
      rcases List.mem_cons.mp hq with rfl | hq
      · simp only [Bool.and_eq_true] at hc
        exact Or.inr ⟨x, tag, ty, e, rfl, rfl, hc.1, hc.2⟩
      · exact Or.inl hq
    · exact Or.inl hq
  · exact Or.inl hq

omit k cand res m in
theorem keptSig_sub_afterDef {cand : JVar → Bool} {c : List InstrR} {st : St} {i : InstrR}
    {q : JVar × Src} (hq : q ∈ keptSig i st.sig) : q ∈ (afterDef cand c st i).sig := by
  simp only [afterDef]
  split
  · split
    · exact List.mem_cons_of_mem _ hq
    · exact hq
  · exact hq

theorem mem_keptSig {i : InstrR} {sig : List (JVar × Src)} {q : JVar × Src} :
    q ∈ keptSig i sig ↔ q ∈ sig ∧ q.1 ∉ writesI i ∧ ∀ y ∈ q.2.reads, y ∉ writesI i := by
  simp only [keptSig, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', contains_eq_false_iff,
    List.any_eq_false, Bool.not_eq_true]

theorem usesOf_filter_dedup (i : InstrR) :
    (((usesOf cand i).filter cand).dedup).length = (usesOf cand i).length := by
  have h1 : (usesOf cand i).filter cand = usesOf cand i :=
    List.filter_eq_self.mpr fun x hx => by
      simp only [usesOf, List.mem_dedup, List.mem_filter] at hx; exact hx.2
  rw [h1]
  exact congrArg List.length (List.dedup_eq_self.mpr (by unfold usesOf; exact List.nodup_dedup _))

/-- The liveness invariant after an original instruction. -/
theorem afterDef_live {T : Prop} {O : List JVar} (hO : ∀ x ∈ O, isFreshName x.vname = false)
    {c : List InstrR} {st : St} {i : InstrR} (hG : GoodSt T O st)
    (hL : LInv k cand res m (i :: c) st) (hi : OrigOK T O i)
    (hD : st.rho.length + (defsOf cand i).length ≤ k) (hm : (usesOf cand i).length ≤ m) :
    LInv k cand res m c (afterDef cand c st i) := by
  have hWO : ∀ w ∈ writesI i, w ∈ O := fun w hw => hi.2.1 w (writesI_sub hw)
  have hfresh : ∀ v ∈ st.slots ++ st.regs, v ∉ writesI i := by
    intro v hv hw
    obtain ⟨-, n, -, hn⟩ := hG.fresh v hv
    have := hO v (hWO v hw)
    rw [hn, isFreshName_freshName] at this; cases this
  have hhold : ∀ q ∈ st.rho, q.1 ∉ writesI i → q.2 ∉ writesI i := by
    intro q hq h1
    rcases (hG.rho q hq).2.2.2 with h | h
    · rw [h]; exact h1
    · exact hfresh _ (List.mem_append_right _ h)
  have hDw : ∀ x ∈ defsOf cand i, x ∈ writesI i ∧ cand x = true := by
    intro x hx
    simp only [defsOf, List.mem_dedup, List.mem_filter] at hx
    exact hx
  refine ⟨?_, ?_, ?_, fun q hq => ?_, fun q hq => ?_, fun x hx hl => ?_, fun x ty e hx => ?_⟩
  · simp only [afterDef, List.map_append, List.map_map]
    refine List.nodup_append.mpr ⟨?_, hL.keys.sublist (List.Sublist.map _ List.filter_sublist),
      ?_⟩
    · have : (defsOf cand i).map ((·.1) ∘ fun x => (x, x)) = defsOf cand i := by
        simp [Function.comp_def]
      rw [this]; exact List.nodup_dedup _
    · intro a ha b hb hab
      subst hab
      simp only [Function.comp_def, List.map_id', List.mem_map, List.mem_filter, Bool.and_eq_true,
        Bool.not_eq_true', contains_eq_false_iff] at ha hb
      obtain ⟨q, ⟨-, h1, -⟩, rfl⟩ := hb
      exact h1 (hDw _ (by simpa using ha)).1
  · have hk : ∀ q ∈ (afterDef cand c st i).sig, True := fun _ _ => trivial
    clear hk
    simp only [afterDef]
    have hks : ((keptSig i st.sig).map Prod.fst).Nodup :=
      hL.skeys.sublist (List.Sublist.map _ List.filter_sublist)
    split
    · split
      · rename_i x tag ty e _ hc
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun h => ?_, hks⟩
        simp only [List.mem_map] at h
        obtain ⟨q, hq, hqx⟩ := h
        exact (mem_keptSig.mp hq).2.1 (hqx ▸ by simp [writesI, writesLv])
      · exact hks
    · exact hks
  · simp only [afterDef, List.length_append, List.length_map]
    have := List.length_filter_le (fun p : JVar × JVar => !(writesI i).contains p.1 &&
      !(writesI i).contains p.2) st.rho
    omega
  · rcases afterDef_rho_mem.mp hq with ⟨x, hx, rfl⟩ | ⟨hq, -, -⟩
    · exact (hDw x hx).2
    · exact hL.kcand q hq
  · rcases afterDef_sig_mem hq with hq | ⟨x, tag, ty, e, -, rfl, hc, -⟩
    · exact hL.skcand q (mem_keptSig.mp hq).1
    · exact hc
  · by_cases hxw : x ∈ writesI i
    · exact Or.inl ⟨x, afterDef_rho_mem.mpr (Or.inl ⟨x, by simp [defsOf, hxw, hx], rfl⟩)⟩
    · have hl' : liveB res x (i :: c) = true := by
        simp [liveB, hl, hxw]
      rcases hL.live x hx hl' with ⟨h, hh⟩ | ⟨s, hs⟩
      · exact Or.inl ⟨h, afterDef_rho_mem.mpr (Or.inr ⟨hh, hxw, hhold _ hh hxw⟩)⟩
      · refine Or.inr ⟨s, keptSig_sub_afterDef (mem_keptSig.mpr ⟨hs, hxw, fun y hy => ?_⟩)⟩
        cases s with
        | slot s0 =>
            simp only [Src.reads, List.mem_singleton] at hy; subst hy
            obtain ⟨-, -, hsg⟩ := hG.sig _ hs
            exact hfresh _ (List.mem_append_left _ hsg.2)
        | remat ty e =>
            have := (hL.remat x ty e hs).1 y hy
            simp only [stableB, Bool.not_eq_true', List.any_eq_false, List.mem_cons,
              forall_eq_or_imp, Bool.not_eq_true] at this
            simpa [contains_eq_false_iff] using this.1
  · rcases afterDef_sig_mem hx with hx | ⟨x0, tag, ty0, e0, hi0, hq, hc, hr⟩
    · obtain ⟨hx, -, hrd⟩ := mem_keptSig.mp hx
      obtain ⟨h1, h2, h3, h4⟩ := hL.remat x ty e hx
      refine ⟨fun y hy => ?_, h2, h3, fun y hy => ?_⟩
      · have := h1 y hy
        simp only [stableB, Bool.not_eq_true', List.any_eq_false, List.mem_cons,
          forall_eq_or_imp] at this ⊢
        exact this.2
      · obtain ⟨ty', e', h5, h6⟩ := h4 y hy
        refine ⟨ty', e', keptSig_sub_afterDef (mem_keptSig.mpr ⟨h5, ?_, fun z hz => ?_⟩), h6⟩
        · have := h1 y (List.mem_filter.mp (List.mem_dedup.mp hy)).1
          simp only [stableB, Bool.not_eq_true', List.any_eq_false, List.mem_cons,
            forall_eq_or_imp, Bool.not_eq_true] at this
          simpa [contains_eq_false_iff] using this.1
        · have := (hL.remat y ty' e' h5).1 z hz
          simp only [stableB, Bool.not_eq_true', List.any_eq_false, List.mem_cons,
            forall_eq_or_imp, Bool.not_eq_true] at this
          simpa [contains_eq_false_iff] using this.1
    · simp only [Prod.mk.injEq, Src.remat.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      simp only [rematOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', contains_eq_false_iff,
        List.all_eq_true] at hr
      obtain ⟨⟨⟨-, hxe⟩, hst⟩, hcr⟩ := hr
      refine ⟨hst, hxe, ?_, fun y hy => ?_⟩
      · refine le_trans ?_ hm
        have : (candReads cand e).length ≤ (usesOf cand i).dedup.length :=
          length_le_of_sub (List.nodup_dedup _) fun y hy => by
            simp only [candReads, List.mem_dedup, List.mem_filter] at hy
            simp only [usesOf, List.mem_dedup, List.mem_filter]
            exact ⟨by subst hi0; simp [readsI, hy.1], hy.2⟩
        rwa [List.dedup_eq_self.mpr (by unfold usesOf; exact List.nodup_dedup _)] at this
      · have := hcr y hy
        split at this
        · rename_i ty' e' hl
          exact ⟨ty', e', keptSig_sub_afterDef (lookS_some hl), by simpa using this⟩
        · cases this

/-- **One original instruction, liveness.** -/
theorem stepI_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x)
    (hO : ∀ x ∈ O, isFreshName x.vname = false) {st : St} (hG : GoodSt T O st) {i : InstrR}
    {c : List InstrR} (hL : LInv k cand res m (i :: c) st) (hi : OrigOK T O i)
    (hU : (usesOf cand i).length + (defsOf cand i).length ≤ k)
    (hU2 : (usesOf cand i).length + 1 + m ≤ k) (hm : (usesOf cand i).length ≤ m)
    (hB : ∀ x ∈ rdB i, cand x = false)
    (hsl : ∀ s ∈ (stepI k cand res st i c).1.slots, s ∈ Zs) :
    LInv k cand res m c (stepI k cand res st i c).1 ∧
      CertC k reg (H st) (stepI k cand res st i c).2 (H (stepI k cand res st i c).1) := by
  unfold stepI at hsl ⊢
  dsimp only at hsl ⊢
  have g0 := (dropDead_res (T := T) (O := O) (res := res) (c := i :: c) hG).good
  have r1 := loadAll_res (T := T) (O := O) k cand (usesOf cand i) res (i :: c) (usesOf cand i)
    (dropDead res (i :: c) st) g0
  have r2 := makeRoom_res (T := T) (O := O) k (defsOf cand i).length (usesOf cand i) res (i :: c)
    (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1.rho.length _ r1.good
  set st1 := (loadAll k cand (usesOf cand i) res (i :: c) (dropDead res (i :: c) st)
      (usesOf cand i)).1 with hst1
  set st2 := (makeRoom k (defsOf cand i).length (usesOf cand i) res (i :: c) st1.rho.length
    st1).1 with hst2
  have hsl2 : ∀ s ∈ st2.slots, s ∈ Zs := hsl
  obtain ⟨l0, c0⟩ := dropDead_live (c := i :: c) hL reg
  have hUu := usesOf_filter_dedup (cand := cand) i
  have hUr : ∀ y ∈ usesOf cand i, y ∈ readsI i ∧ cand y = true := by
    intro y hy; simpa [usesOf] using hy
  obtain ⟨l1, c1, h1, -⟩ := loadAll_live hZ hreg (usesOf cand i) (by omega)
    (fun y hy => by simp [liveB, (hUr y hy).1]) (usesOf cand i) _ g0 l0
    (fun x hx => ⟨(hUr x hx).2, hx⟩) (fun s hs => hsl2 s (r2.le.slots hs))
  obtain ⟨l2, c2, b2⟩ := makeRoom_live hZ (reg := reg) (need := (defsOf cand i).length)
    (usesOf cand i) (by omega) (i :: c) st1.rho.length st1 l1 le_rfl hsl2
  have hU2' : ∀ y ∈ usesOf cand i, ∃ h, (y, h) ∈ st2.rho := by
    intro y hy
    obtain ⟨h, hh⟩ := h1 y hy
    exact ⟨h, makeRoom_keep k _ _ res _ _ st1 _ hh (by simpa using hy)⟩
  have hyO : ∀ y ∈ readsI i, y ∈ O := fun y hy => hi.2.1 y (readsI_sub hy)
  have cr : CertC k reg (H st2) [renI (renOf st2.rho) i] (H (afterDef cand c st2 i)) := by
    refine CertC.single ?_ ?_ ?_
    · intro v hv hrv
      rcases readsI_renI _ hv with ⟨y, hy, rfl⟩ | hb
      · have hyr : y ∈ readsI i := mem_readsI.mpr (Or.inl hy)
        rcases renOf_cases st2.rho y with ⟨h, hn⟩ | h
        · rw [h] at hrv ⊢
          rw [hreg y (hyO y hyr)] at hrv
          obtain ⟨h', hh'⟩ := hU2' y (by simp [usesOf, hyr, hrv])
          exact absurd rfl (lookR_none hn _ hh')
        · exact List.mem_map_of_mem h
      · have hvr : v ∈ readsI i := mem_readsI.mpr (Or.inr hb)
        rw [hreg v (hyO v hvr), hB v hb] at hrv; cases hrv
    · rw [writesI_renI]
      refine (length_le_of_sub (List.nodup_dedup _) (L := H st2 ++ defsOf cand i)
        fun x hx => ?_).trans ((List.dedup_sublist _).length_le.trans ?_)
      · rw [List.mem_dedup, List.mem_append] at hx
        rcases hx with hx | hx
        · exact List.mem_append_left _ hx
        · obtain ⟨hxw, hxr⟩ := List.mem_filter.mp hx
          rw [hreg x (hi.2.1 x (writesI_sub hxw))] at hxr
          exact List.mem_append_right _ (by simp [defsOf, hxw, hxr])
      · simp only [List.length_append, H, List.length_map]; omega
    · intro v hv
      simp only [H, List.mem_map] at hv
      obtain ⟨q, hq, rfl⟩ := hv
      rcases afterDef_rho_mem.mp hq with ⟨x, hx, rfl⟩ | ⟨hq, -, -⟩
      · right; rw [writesI_renI]
        simp only [defsOf, List.mem_dedup, List.mem_filter] at hx
        exact hx.1
      · exact Or.inl (List.mem_map_of_mem hq)
  refine ⟨afterDef_live hO r2.good l2 hi b2 hm, ?_⟩
  have := CertC.append (CertC.append c0 (CertC.append c1 c2)) cr
  simpa using this

theorem goBody_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x)
    (hO : ∀ x ∈ O, isFreshName x.vname = false)
    (hcand : ∀ x, cand x = true → isGprTy x.vtype = true) :
    ∀ (c : List InstrR) (st : St), GoodSt T O st → LInv k cand res m c st →
      (∀ i ∈ c, OrigOK T O i ∧ (usesOf cand i).length + (defsOf cand i).length ≤ k ∧
        (usesOf cand i).length + 1 + m ≤ k ∧ (usesOf cand i).length ≤ m ∧
        ∀ x ∈ rdB i, cand x = false) →
      (∀ s ∈ (goBody k cand res st c).1.slots, s ∈ Zs) →
      LInv k cand res m [] (goBody k cand res st c).1 ∧
      CertC k reg (H st) (goBody k cand res st c).2 (H (goBody k cand res st c).1)
  | [], st, _, hL, _, _ => ⟨hL, CertC.nil_sub (fun _ h => h)⟩
  | i :: c, st, hG, hL, hc, hsl => by
      obtain ⟨hi, h1, h2, h3, h4⟩ := hc i (by simp)
      have r1 := stepI_res (k := k) (res := res) (c := c) hcand hG hi
      have rest := goBody_res (T := T) (O := O) (k := k) (res := res) hcand c _ r1.good
        (fun j hj => (hc j (by simp [hj])).1)
      obtain ⟨l1, c1⟩ := stepI_live hZ hreg hO hG hL hi h1 h2 h3 h4
        (fun s hs => hsl s (rest.le.slots hs))
      obtain ⟨l2, c2⟩ := goBody_live hZ hreg hO hcand c _ r1.good l1
        (fun j hj => hc j (by simp [hj])) hsl
      exact ⟨l2, CertC.append c1 c2⟩

/-- A reload of `x` from its source into `d`, which becomes the holder of `x`. -/
theorem reloadInto_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {c : List InstrR} {st : St}
    (hG : GoodSt T O st) (hL : LInv k cand res m c st) {x d : JVar} {src : Src}
    (hx : (x, src) ∈ st.sig) (hnx : ∀ q ∈ st.rho, q.1 ≠ x) (hroom : st.rho.length + 1 ≤ k)
    (hrd : ∀ ty e, src = .remat ty e → ∀ y ∈ readsE e, cand y = true → ∃ h, (y, h) ∈ st.rho)
    (hsl : ∀ s ∈ st.slots, s ∈ Zs) :
    LInv k cand res m c { st with rho := (x, d) :: st.rho } ∧
      CertC k reg (H st) [reloadSrc st.rho d src] (d :: H st) := by
  obtain ⟨-, -, hsrc⟩ := hG.sig _ hx
  refine ⟨⟨?_, hL.skeys, by simpa using hroom, fun q hq => ?_, hL.skcand,
    fun y hy hl => ?_, hL.remat⟩, CertC.single ?_ ?_ ?_⟩
  · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun q hq h => hnx q hq h, hL.keys⟩
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact hL.skcand _ hx
    · exact hL.kcand q hq
  · rcases hL.live y hy hl with ⟨h, hh⟩ | hs
    · exact Or.inl ⟨h, List.mem_cons_of_mem _ hh⟩
    · exact Or.inr hs
  · intro v hv hrv
    cases src with
    | slot s =>
        rw [reloadSrc, readsI_mv, List.mem_singleton] at hv
        subst hv
        rw [hZ _ (hsl _ hsrc.2)] at hrv; cases hrv
    | remat ty e =>
        rw [readsI_reloadSrc_remat, List.mem_map] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rcases renOf_cases st.rho y with ⟨h, hn⟩ | h
        · rw [h] at hrv ⊢
          rw [hreg y (hsrc.2.2 y (readsE_sub e y hy))] at hrv
          obtain ⟨h', hh'⟩ := hrd ty e rfl y hy hrv
          exact absurd rfl (lookR_none hn _ hh')
        · exact List.mem_map_of_mem h
  · rw [writesI_reloadSrc]
    refine (List.dedup_sublist _).length_le.trans ?_
    simp only [List.length_append, H, List.length_map]
    have := List.length_filter_le reg [d]
    simp only [List.length_singleton] at this
    omega
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inr (by simp [writesI_reloadSrc])
    · exact Or.inl hv

theorem fixOne_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x) {st : St}
    (hG : GoodSt T O st) (hL : LInv k cand res m [] st) {r : JVar} (hrc : cand r = true)
    (hrres : r ∈ res) (hP : ((res.filter cand).dedup).length + 1 + m ≤ k)
    (hsl : ∀ s ∈ (fixOne k cand res st r).1.slots, s ∈ Zs) :
    LInv k cand res m [] (fixOne k cand res st r).1 ∧
      CertC k reg (H st) (fixOne k cand res st r).2 (H (fixOne k cand res st r).1) ∧
      (r, r) ∈ (fixOne k cand res st r).1.rho ∧
      (∀ q ∈ st.rho, res.contains q.1 = true → q.1 ≠ r → q ∈ (fixOne k cand res st r).1.rho) := by
  have hrl : liveB res r [] = true := by simp [liveB, hrres]
  unfold fixOne at hsl ⊢
  split
  · rename_i h hl
    simp only [hl] at hsl
    split
    · rename_i hh
      simp only [beq_iff_eq] at hh; subst hh
      exact ⟨hL, CertC.nil_sub (fun _ h => h), lookR_some hl, fun q hq _ _ => hq⟩
    · rename_i hh
      rw [if_neg hh] at hsl
      have hsl1 : ∀ s ∈ (makeRoom k 1 res res [] st.rho.length st).1.slots, s ∈ Zs := hsl
      obtain ⟨l1, c1, b1⟩ := makeRoom_live hZ (reg := reg) (need := 1) res (by omega) []
        st.rho.length st hL le_rfl hsl1
      have hkeep := makeRoom_keep k 1 res res [] st.rho.length st _ (lookR_some hl)
        (by simpa using hrres)
      have hlen := length_filter_key l1.keys hkeep
      refine ⟨⟨?_, l1.skeys, ?_, fun q hq => ?_, l1.skcand, fun x hx hl' => ?_, l1.remat⟩,
        CertC.append c1 (CertC.single ?_ ?_ ?_), List.mem_cons_self, fun q hq hres hne => ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, l1.keys.sublist (List.Sublist.map _ List.filter_sublist)⟩
        obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hmem
        have := (List.mem_filter.mp hq).2
        simp only [bne_iff_ne, ne_eq] at this
        exact this hq1
      · have hlen' : (List.filter (fun q => q.1 != r)
            (makeRoom k 1 res res [] st.rho.length st).1.rho).length + 1 =
            (makeRoom k 1 res res [] st.rho.length st).1.rho.length := hlen
        simp only [List.length_cons]; omega
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact hrc
        · exact l1.kcand q (List.mem_of_mem_filter hq)
      · by_cases hxr : x = r
        · subst hxr; exact Or.inl ⟨x, List.mem_cons_self⟩
        · rcases l1.live x hx hl' with ⟨h', hh'⟩ | hs
          · exact Or.inl ⟨h', List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hh', by simpa using hxr⟩)⟩
          · exact Or.inr hs
      · intro v hv _
        rw [readsI_mv, List.mem_singleton] at hv; subst hv
        exact List.mem_map_of_mem hkeep
      · rw [writesI_mv]
        refine (List.dedup_sublist _).length_le.trans ?_
        simp only [List.length_append, H, List.length_map]
        have := List.length_filter_le reg [r]
        simp only [List.length_singleton] at this
        omega
      · intro v hv
        simp only [H, List.map_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact Or.inr (by simp [writesI_mv])
        · exact Or.inl (H_filter_sub v hv)
      · refine List.mem_cons_of_mem _ (List.mem_filter.mpr
          ⟨makeRoom_keep k 1 res res [] st.rho.length st q hq hres, by simpa using hne⟩)
  · rename_i hl
    have hnx : ∀ q ∈ st.rho, q.1 ≠ r := fun q hq h => by
      obtain ⟨a, b⟩ := q
      simp only at h; subst h
      have := lookR_of_mem hL.keys hq; rw [hl] at this; cases this
    simp only [hl] at hsl
    split
    · rename_i hs
      exfalso
      rcases hL.live r hrc hrl with ⟨h, hh⟩ | ⟨s, hs'⟩
      · exact hnx _ hh rfl
      · have : (lookS st.sig r).isSome = true := lookS_isSome_iff.mpr ⟨_, hs', rfl⟩
        rw [hs] at this; cases this
    · rename_i src hs
      rw [hs] at hsl
      simp only at hsl ⊢
      have hxs := lookS_some hs
      have hneed : needOf cand src ≤ 1 + m := by
        cases src with
        | slot s => simp [needOf]
        | remat ty e => simp only [needOf]; have := (hL.remat r ty e hxs).2.2.1; omega
      have r1 := makeRoom_res (T := T) (O := O) k (needOf cand src) res res [] st.rho.length st hG
      have r2 := helpersOf_res (T := T) (O := O) cand src r1.good
      set st1 := (makeRoom k (needOf cand src) res res [] st.rho.length st).1 with hst1
      set st2 := (helpersOf cand st1 src).1 with hst2
      have hsl2 : ∀ s ∈ st2.slots, s ∈ Zs := hsl
      obtain ⟨l1, c1, b1⟩ := makeRoom_live hZ (reg := reg) (need := needOf cand src) res
        (by omega) [] st.rho.length st hL le_rfl (fun s hs => hsl2 s (r2.le.slots hs))
      have hhelp : LInv k cand res m [] st2 ∧ CertC k reg (H st1) (helpersOf cand st1 src).2 (H st2) ∧
          (∀ ty e, src = .remat ty e → ∀ y ∈ candReads cand e, ∃ h, (y, h) ∈ st2.rho) ∧
          (∀ q ∈ st1.rho, q ∈ st2.rho) ∧
          (∀ q ∈ st2.rho, q ∈ st1.rho ∨ ∃ ty e, src = .remat ty e ∧ q.1 ∈ candReads cand e) ∧
          st2.rho.length + 1 ≤ k := by
        cases src with
        | slot s =>
            have hn : needOf cand (Src.slot s) = 1 := rfl
            exact ⟨l1, CertC.nil_sub (fun _ h => h), fun _ _ h => (by cases h), fun _ h => h,
              fun q hq => Or.inl hq, by simp only [hst2, hst1, helpersOf]; omega⟩
        | remat ty e =>
            obtain ⟨-, -, -, h4⟩ := hL.remat r ty e hxs
            have hn : needOf cand (Src.remat ty e) = 1 + (candReads cand e).length := rfl
            obtain ⟨i1, i2, i3, i4, i5, i6, -, -⟩ := helpers_live hZ hreg (candReads cand e) _
              r1.good l1 (by omega)
              (fun y hy => by
                obtain ⟨ty', e', h5, h6⟩ := h4 y hy
                exact Or.inr ⟨ty', e', r1.sig _ h5, h6⟩)
              (fun s hs => hsl2 s (r2.le.slots hs))
            refine ⟨i1, i2, fun ty' e' he y hy => ?_, i4, fun q hq => ?_, i6⟩
            · cases he; exact i3 y hy
            · rcases i5 q hq with h | h
              · exact Or.inl h
              · exact Or.inr ⟨ty, e, rfl, h⟩
      obtain ⟨l2, c2, h2, k2, n2, b2⟩ := hhelp
      obtain ⟨l3, c3⟩ := reloadInto_live (d := r) hZ hreg r2.good l2 (r2.sig _ (r1.sig _ hxs))
        (fun q hq h => by
          rcases n2 q hq with hq | ⟨ty, e, rfl, hq'⟩
          · exact hnx q (makeRoom_rho_sub k _ res res [] _ st q hq) h
          · have := (hL.remat r ty e hxs).2.1
            rw [h] at hq'
            exact this (List.mem_filter.mp (List.mem_dedup.mp hq')).1)
        b2 (fun ty e he y hy hc => h2 ty e he y (by simp [candReads, hy, hc])) hsl2
      obtain ⟨l4, c4⟩ := dropDead_live (c := []) l3 reg
      refine ⟨l4, ?_, List.mem_filter.mpr ⟨List.mem_cons_self, hrl⟩, fun q hq hres _ => ?_⟩
      · have := CertC.append (CertC.append c1 c2) (CertC.append c3 c4)
        simpa [H] using this
      · refine List.mem_filter.mpr ⟨List.mem_cons_of_mem _ (k2 _
          (makeRoom_keep k _ res res [] _ st q hq hres)), ?_⟩
        simpa [liveB] using hres

theorem fixAll_live {T : Prop} {O : List JVar} {reg : JVar → Bool} {Zs : List JVar}
    (hZ : ∀ s ∈ Zs, reg s = false) (hreg : ∀ x ∈ O, reg x = cand x)
    (hcand : ∀ x, cand x = true → isGprTy x.vtype = true)
    (hP : ((res.filter cand).dedup).length + 1 + m ≤ k) :
    ∀ (rs : List JVar) (st : St), GoodSt T O st → LInv k cand res m [] st →
      (∀ r ∈ rs, cand r = true ∧ r ∈ res ∧ r ∈ O) → rs.Nodup →
      (∀ s ∈ (fixAll k cand res st rs).1.slots, s ∈ Zs) →
      LInv k cand res m [] (fixAll k cand res st rs).1 ∧
      CertC k reg (H st) (fixAll k cand res st rs).2 (H (fixAll k cand res st rs).1) ∧
      (∀ r ∈ rs, (r, r) ∈ (fixAll k cand res st rs).1.rho) ∧
      (∀ q ∈ st.rho, res.contains q.1 = true → q.1 ∉ rs → q ∈ (fixAll k cand res st rs).1.rho)
  | [], st, _, hL, _, _, _ =>
      ⟨hL, CertC.nil_sub (fun _ h => h), by simp, fun _ hq _ _ => hq⟩
  | r :: rs, st, hG, hL, hr, hnd, hsl => by
      obtain ⟨hrc, hrres, hrO⟩ := hr r (by simp)
      have r1 := fixOne_res (T := T) (O := O) (k := k) (cand := cand) (res := res) hG hrO
        (hcand r hrc)
      have rest := fixAll_res (T := T) (O := O) (k := k) (cand := cand) (res := res) rs _ r1.good
        (fun q hq => ⟨(hr q (by simp [hq])).2.2, hcand q (hr q (by simp [hq])).1⟩)
      obtain ⟨l1, c1, h1, k1⟩ := fixOne_live hZ hreg hG hL hrc hrres hP
        (fun s hs => hsl s (rest.le.slots hs))
      obtain ⟨l2, c2, h2, k2⟩ := fixAll_live hZ hreg hcand hP rs _ r1.good l1
        (fun q hq => hr q (by simp [hq])) (List.nodup_cons.mp hnd).2 hsl
      refine ⟨l2, CertC.append c1 c2, fun q hq => ?_, fun q hq hres hn => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact k2 _ h1 (by simpa using hrres) (List.nodup_cons.mp hnd).1
        · exact h2 q hq
      · simp only [List.mem_cons, not_or] at hn
        exact k2 q (k1 q hq hres hn.1) hres hn.2

omit k cand m in
theorem liveB_mem {x : JVar} : ∀ {c : List InstrR}, liveB res x c = true →
    x ∈ cmdVars c ∨ x ∈ res
  | [], h => by simp only [liveB, List.contains_iff_mem] at h; exact Or.inr h
  | i :: c, h => by
      simp only [liveB, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
      rcases h with h | ⟨-, h⟩
      · exact Or.inl (mem_cmdVars.mpr ⟨i, by simp, readsI_sub h⟩)
      · rcases liveB_mem h with h | h
        · obtain ⟨j, hj, hx⟩ := mem_cmdVars.mp h
          exact Or.inl (mem_cmdVars.mpr ⟨j, by simp [hj], hx⟩)
        · exact Or.inr h

theorem initSt_live {body : List InstrR} (hlen : (initSt cand res body).rho.length ≤ k) :
    LInv k cand res m body (initSt cand res body) := by
  refine ⟨?_, by simp [initSt], hlen, fun q hq => ?_, by simp [initSt], fun x hx hl => ?_,
    by simp [initSt]⟩
  · simp only [initSt, List.map_map, Function.comp_def, List.map_id']
    exact List.nodup_dedup _
  · simp only [initSt, List.mem_map, List.mem_dedup, List.mem_filter, Bool.and_eq_true] at hq
    obtain ⟨y, ⟨-, hy, -⟩, rfl⟩ := hq
    exact hy
  · refine Or.inl ⟨x, ?_⟩
    simp only [initSt, List.mem_map, List.mem_dedup, List.mem_filter, Bool.and_eq_true,
      Prod.mk.injEq]
    refine ⟨x, ⟨?_, hx, hl⟩, rfl, rfl⟩
    rcases liveB_mem hl with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h

end LiveInv

/-- The largest number of register variables an instruction of `body` reads. -/
def maxUses (cand : JVar → Bool) (body : List InstrR) : Nat :=
  (body.map fun i => (usesOf cand i).length).foldr max 0

theorem le_maxUses {cand : JVar → Bool} : ∀ {body : List InstrR} {i : InstrR}, i ∈ body →
    (usesOf cand i).length ≤ maxUses cand body
  | j :: body, i, h => by
      simp only [maxUses, List.map_cons, List.foldr_cons] at *
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (le_maxUses h).trans (le_max_right _ _)

/-- **The register demand of a straight-line body.** With `cand = regWordB fn` and `m` the
largest number of register variables an instruction reads: the register variables live
before the body number at most `k`; each instruction reads and writes at most `k` register
variables together and writes no register variable in place; `2 m + 1 ≤ k`, room for the
operands of an instruction and the reload of one more with its own operands; and the
register results with one reload fit in `k`. -/
def DemandOK (k : Nat) (fn : JazzFn) : Prop :=
  (initSt (regWordB fn) (resOf fn) fn.fd.body).rho.length ≤ k ∧
  (∀ i ∈ fn.fd.body, (usesOf (regWordB fn) i).length + (defsOf (regWordB fn) i).length ≤ k ∧
    ∀ x ∈ rdB i, regWordB fn x = false) ∧
  2 * maxUses (regWordB fn) fn.fd.body + 1 ≤ k ∧
  (((resOf fn).filter (regWordB fn)).dedup).length + 1 + maxUses (regWordB fn) fn.fd.body ≤ k

theorem storageOf_spill {fn g : JazzFn} {st : St} (hp : g.fd.params = fn.fd.params)
    (hpt : g.paramTys = fn.paramTys) (hd : g.decls = fn.decls ++ declsOf st)
    (hfr : ∀ v ∈ st.slots ++ st.regs, isFreshName v.vname = true) {n : String}
    (hn : isFreshName n = false) : storageOf g n = storageOf fn n := by
  unfold storageOf
  rw [hp, hpt, hd]
  split
  · rfl
  · rw [List.find?_append]
    cases hf : fn.decls.find? (fun d => d.names.contains n) with
    | some d => rfl
    | none =>
        have : (declsOf st).find? (fun d => d.names.contains n) = none := by
          rw [List.find?_eq_none]
          intro d hd' hc
          simp only [declsOf, List.mem_append, List.mem_map] at hd'
          rcases hd' with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;>
            simp only [List.contains_iff_mem, List.mem_singleton] at hc <;> subst hc <;>
            [rw [hfr v (List.mem_append_left _ hv)] at hn; rw [hfr v (List.mem_append_right _ hv)] at hn] <;>
            cases hn
        rw [this]; rfl

theorem regWordB_spill_slot {fn g : JazzFn} {st : St} (hp : g.fd.params = fn.fd.params)
    (hpt : g.paramTys = fn.paramTys) (hd : g.decls = fn.decls ++ declsOf st)
    (henv : ∀ n ∈ fn.env.map Prod.fst, isFreshName n = false) {s : JVar} (hs : s ∈ st.slots)
    (hsf : isFreshName s.vname = true) : regWordB g s = false := by
  have hst : storageOf g s.vname = some .stack := by
    unfold storageOf
    rw [hp, hpt, hd]
    split
    · rename_i p hpf
      exfalso
      have hm := List.mem_of_find?_eq_some hpf
      have he := List.find?_some hpf
      simp only [beq_iff_eq] at he
      have hpm : p.1 ∈ fn.fd.params := (List.of_mem_zip hm).1
      have : isFreshName p.1.var.var.vname = false :=
        henv _ (by simp only [JazzFn.env, List.map_append, List.map_map, List.mem_append,
          List.mem_map]; exact Or.inl ⟨p.1, hpm, rfl⟩)
      rw [he, hsf] at this; cases this
    · rw [List.find?_append]
      have hf : fn.decls.find? (fun d => d.names.contains s.vname) = none := by
        rw [List.find?_eq_none]
        intro d hd' hc
        simp only [List.contains_iff_mem] at hc
        have : isFreshName s.vname = false := henv _ (by
          simp [JazzFn.env]
          exact Or.inr ⟨d, hd', hc⟩)
        rw [hsf] at this; cases this
      rw [hf, Option.none_or]
      simp only [declsOf, List.find?_append]
      have : ((st.slots.map fun s => (⟨.stack, ptyOf s.vtype, [s.vname]⟩ : Decl)).find?
          (fun d => d.names.contains s.vname)).isSome := by
        rw [List.find?_isSome]
        exact ⟨_, List.mem_map_of_mem hs, by simp⟩
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp this
      rw [hd]
      have := List.mem_of_find?_eq_some hd
      simp only [List.mem_map] at this
      obtain ⟨v, -, rfl⟩ := this
      rfl
  simp only [regWordB, hst]
  cases isGprTy s.vtype <;> decide

/-- **The pass establishes the liveness check.** On a straight-line body without names of
the fresh prefix and with the register demand `DemandOK k`, at most `k` register variables
are live at each instruction of the spilled body. -/
theorem liveRegsB_spillFn (k : Nat) (fn : JazzFn) (hs : ∀ i ∈ fn.fd.body, straightI i = true)
    (hfr : noFreshB fn = true) (hd : DemandOK k fn) : liveRegsB k (spillFn k fn) = true := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
  have hguard : (fn.fd.body.all straightI && noFreshB fn) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true]; exact ⟨hs, hfr⟩
  have e1 : (spillFn k fn).fd.params = fn.fd.params := by unfold spillFn; rw [if_pos hguard]
  have e2 : (spillFn k fn).paramTys = fn.paramTys := by unfold spillFn; rw [if_pos hguard]
  have e3 : (spillFn k fn).decls = fn.decls ++ declsOf (run k fn).1 := by
    unfold spillFn; rw [if_pos hguard]
  have e4 : (spillFn k fn).fd.body = (run k fn).2 := by unfold spillFn; rw [if_pos hguard]
  have e5 : resOf (spillFn k fn) = resOf fn := by unfold spillFn resOf; rw [if_pos hguard]
  obtain ⟨hG, hE⟩ := run_res (T := False) k fn hs (fun _ _ h => h.elim)
  have hnf : ∀ n ∈ fn.env.map Prod.fst ++ (cmdVars fn.fd.body ++ resOf fn).map (·.vname),
      isFreshName n = false := by
    intro n hn
    simp only [noFreshB, List.all_eq_true, Bool.not_eq_true'] at hfr
    exact hfr n hn
  have hO : ∀ x ∈ cmdVars fn.fd.body ++ resOf fn, isFreshName x.vname = false :=
    fun x hx => hnf _ (List.mem_append_right _ (List.mem_map_of_mem hx))
  have hfresh : ∀ v ∈ (run k fn).1.slots ++ (run k fn).1.regs, isFreshName v.vname = true := by
    intro v hv
    obtain ⟨-, n, -, hn⟩ := hG.fresh v hv
    rw [hn]; exact isFreshName_freshName n
  have henv : ∀ n ∈ fn.env.map Prod.fst, isFreshName n = false :=
    fun n hn => hnf n (List.mem_append_left _ hn)
  have hreg : ∀ x ∈ cmdVars fn.fd.body ++ resOf fn,
      regWordB (spillFn k fn) x = regWordB fn x := by
    intro x hx
    simp only [regWordB]
    rw [storageOf_spill e1 e2 e3 hfresh (hO x hx)]
  have hZ : ∀ s ∈ (run k fn).1.slots, regWordB (spillFn k fn) s = false := fun s hs =>
    regWordB_spill_slot e1 e2 e3 henv hs (hfresh s (List.mem_append_left _ hs))
  unfold liveRegsB
  rw [e4, e5]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun i hi => (hE i hi).1, ?_⟩
  have hcand : ∀ x, regWordB fn x = true → isGprTy x.vtype = true := fun x h => regWordB_gpr h
  have g0 := initSt_good (T := False) (O := cmdVars fn.fd.body ++ resOf fn) hcand
    (res := resOf fn) (body := fn.fd.body) (fun _ h => h)
  have L0 := initSt_live (k := k) (cand := regWordB fn) (res := resOf fn)
    (m := maxUses (regWordB fn) fn.fd.body) hd1
  have hOK : ∀ i ∈ fn.fd.body, OrigOK False (cmdVars fn.fd.body ++ resOf fn) i :=
    fun i hi => ⟨hs i hi, fun v hv => List.mem_append_left _ (mem_cmdVars.mpr ⟨i, hi, hv⟩),
      fun h => h.elim⟩
  have r1 := goBody_res (T := False) (O := cmdVars fn.fd.body ++ resOf fn) (k := k)
    (res := resOf fn) hcand fn.fd.body _ g0 hOK
  have hrs : ∀ r ∈ ((resOf fn).filter (regWordB fn)).dedup,
      regWordB fn r = true ∧ r ∈ resOf fn ∧ r ∈ cmdVars fn.fd.body ++ resOf fn := by
    intro r hr
    simp only [List.mem_dedup, List.mem_filter] at hr
    exact ⟨hr.2, hr.1, List.mem_append_right _ hr.1⟩
  have r2 := fixAll_res (T := False) (O := cmdVars fn.fd.body ++ resOf fn) (k := k)
    (cand := regWordB fn) (res := resOf fn) (((resOf fn).filter (regWordB fn)).dedup) _ r1.good
    (fun r hr => ⟨(hrs r hr).2.2, hcand r (hrs r hr).1⟩)
  obtain ⟨L1, C1⟩ := goBody_live (k := k) (cand := regWordB fn) (res := resOf fn)
    (m := maxUses (regWordB fn) fn.fd.body) hZ hreg hO hcand fn.fd.body _ g0 L0
    (fun i hi => by
      have hu := le_maxUses (cand := regWordB fn) hi
      exact ⟨hOK i hi, (hd2 i hi).1, by omega, hu, (hd2 i hi).2⟩)
    (fun s hs => r2.le.slots hs)
  obtain ⟨L2, C2, h2, -⟩ := fixAll_live (k := k) (cand := regWordB fn) (res := resOf fn)
    (m := maxUses (regWordB fn) fn.fd.body) hZ hreg hcand hd4 _ _ r1.good L1 hrs
    (List.nodup_dedup _) (fun s hs => hs)
  have C := CertC.append C1 C2
  refine (CertC.live C (fun x hx hrx => ?_)).1
  rw [hreg x (List.mem_append_right _ hx)] at hrx
  have := h2 x (by simp [hx, hrx])
  exact List.mem_map_of_mem (f := Prod.snd) this

end Live

/-! ## 14. The units of the lowering -/

/-- The Boolean check of well-formedness holds on every well-formed function. -/
theorem wellFormedB_of_wellFormed {callees : List String} {f : JazzFn}
    (h : f.WellFormed callees) : f.wellFormedB callees = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [JazzFn.wellFormedB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq, List.contains_iff_mem, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, ?_⟩, h8⟩
  by_cases hk : f.kind = .inlineFn
  · exact Or.inl hk
  · exact Or.inr (h7 hk)

/-- The Boolean check of well-formedness holds on every well-formed unit. -/
theorem unit_wellFormedB_of_wellFormed {u : JazzUnit} (h : u.WellFormed) :
    u.wellFormedB = true :=
  List.all_eq_true.mpr fun f hf => wellFormedB_of_wellFormed (h f hf)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Jasmin.Jazz (JazzUnit)

/-- **The units of the lowering are well formed.** -/
theorem nfToJasmin_wellFormed {Γ : Ctxt jasminDialect} {t : JasminTy} {sig : JazzSig Γ t}
    {fname : String} {p : NFProg jasminDialect Γ [t]} {u : JazzUnit}
    (h : nfToJasmin sig fname p = some u) : u.WellFormed := by
  obtain ⟨hfit, r, hr, rfl⟩ := nfToJasmin_eq_some h
  exact JazzUnit.wellFormedB_sound (JasminSpill.spillUnit_wellFormed spillK
    (JasminSpill.unit_wellFormedB_of_wellFormed (mkUnit_finish_wellFormed sig fname hfit hr)))

end CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin

namespace CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin

/-- **Completeness of the translation on the units of the lowering**: every unit
`nfToJasmin` returns, after the spill pass, translates to a program of the `CoqSemMirror`
syntax. -/
theorem translateUnit_isSome_of_nfToJasmin {Γ : Ctxt jasminDialect} {t : JasminTy}
    {sig : JazzSig Γ t} {fname : String} {p : NFProg jasminDialect Γ [t]}
    {u : CatCrypt.Crypto.Jasmin.Jazz.JazzUnit} (h : nfToJasmin sig fname p = some u) :
    (translateUnit u).isSome := by
  have hw := jasminWidthsB_of_nfToJasmin h
  obtain ⟨hfit, r, hr, rfl⟩ := nfToJasmin_eq_some h
  exact JasminSpill.translateUnit_isSome_spill spillK
    (translateUnit_isSome_mkUnit_finish hfit hw hr)

end CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
