/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

/-!
# The region export against call trees

`ExportRegions.ExportRSim` relates the denotation of a structured program at one call
environment to a run of its export: a call is a step of the instruction set that writes the
answer of the environment. A call tree of the program answers each call by an event, and the
answers of the events need not come from one environment. The call tree of a program and the
runs of its export are related segment by segment: from a state at the start of the code, the
tree and the state are related by `TSim` when a leaf of the tree is reached by steps in a state
satisfying the end condition, and an event of the tree is reached by steps in a state at a call
site of the event, from which each answer of the event and each state after the call with that
answer are related in the same way to the continuation of the tree.

The relation is stated for an instruction set `I`, a program `P`, a predicate `Site` of the
states at the call of an event and a relation `Q` between such a state, an answer and the state
after the call; in the simulation statement both depend on the program. On the x86 flag machine
a step never performs a call, so the steps between two events of the tree pass no call.
`ExportTSim` is the statement `ExportRSim` with the denotation at an environment replaced by
`TSim` of the call tree `treeAt` at a tree call environment.

## Main definitions

* `TSim`: a call tree and a state related through the runs of a program, with the events of
  the tree at call sites.
* `TCallsSim`: a tree call environment whose trees of calls of words and word arrays are
  related by `TSim` to the states at the call instruction, with the state after the call as end
  condition.
* `ExportTSim`: the simulation statement of the region export for call trees.
* `CallSite`, `CallRet`: a state at the call of an event and the state after it at an answer.

## Main results

* `TSim.steps`, `TSim.post`, `TSim.obind`: steps in front, a weaker end condition reached by
  steps, and sequencing.
* `exportTSim_ret`, `exportTSim_var`, `exportTSim_call`, `exportTSim_callArr`,
  `exportTSim_if`, `exportTSim_while`, `exportTSim_for`: the statement for each construct of a
  program, from the statements for its parts.
* `exportT_sim`: every program of `RegionExportable` satisfies the statement, on an instruction
  set with the steps of the x86 flag machine, at a tree call environment that performs the
  calls.
* `tCallsSim_eventEnv`: the tree call environment of the call events performs the calls, at the
  call sites and the states after the calls.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa IsaData callShadow retWord)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend hvToHom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (loopCtr_ne_argName
  loopCtr_ne_regName)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree

/-! ## Trees related to states through runs -/

section TSim

variable {E : EventSig} (I : Isa) (P : LprogM) (Site : E.Event → LstateMF → Prop)
  (Q : (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop)

/-- **A call tree and a state related through the runs of `P`.** A failed leaf is related to
    every state; a leaf `some v` to a state from which steps reach a state where `Post v`
    holds; an event `e` to a state from which steps reach a state `u` at a call site of `e`
    such that at every answer `a` and every state `u'` that `Q` relates to `u` and `a`, the
    continuation at `a` is related to `u'`. -/
def TSim {α : Type} : CallTree E (Option α) → LstateMF → (α → LstateMF → Prop) → Prop
  | .ret none, _, _ => True
  | .ret (some v), m, Post => ∃ k m', Steps I P k m m' ∧ Post v m'
  | .vis e c, m, Post => ∃ k u, Steps I P k m u ∧ Site e u ∧
      ∀ a u', Q e u a u' → TSim (c a) u' Post

variable {I P Site Q}

/-- **Steps in front of a related state.** -/
theorem TSim.steps {α : Type} {t : CallTree E (Option α)} {m m₁ : LstateMF}
    {Post : α → LstateMF → Prop} {k : Nat} (hs : Steps I P k m m₁)
    (h : TSim I P Site Q t m₁ Post) : TSim I P Site Q t m Post := by
  cases t with
  | ret o =>
      cases o with
      | none => trivial
      | some v =>
          obtain ⟨k', m', hs', hp⟩ := h
          exact ⟨k + k', m', hs.trans hs', hp⟩
  | vis e c =>
      obtain ⟨k', u, hs', hsite, hc⟩ := h
      exact ⟨k + k', u, hs.trans hs', hsite, hc⟩

/-- **A weaker end condition reached by steps.** If every state where `Post v` holds reaches
    by steps a state where `Post' v` holds, a relation at `Post` is a relation at `Post'`. -/
theorem TSim.post {α : Type} {Post Post' : α → LstateMF → Prop}
    (hP : ∀ v m', Post v m' → ∃ k m'', Steps I P k m' m'' ∧ Post' v m'') :
    ∀ {t : CallTree E (Option α)} {m : LstateMF}, TSim I P Site Q t m Post →
      TSim I P Site Q t m Post'
  | .ret none, _, _ => trivial
  | .ret (some v), _, ⟨k, m', hs, hp⟩ => by
      obtain ⟨k', m'', hs', hp'⟩ := hP v m' hp
      exact ⟨k + k', m'', hs.trans hs', hp'⟩
  | .vis _ c, _, ⟨k, u, hs, hsite, hc⟩ =>
      ⟨k, u, hs, hsite, fun a u' hq => TSim.post hP (t := c a) (hc a u' hq)⟩

/-- `TSim` is monotone in the end condition. -/
theorem TSim.mono {α : Type} {Post Post' : α → LstateMF → Prop}
    (hP : ∀ v m', Post v m' → Post' v m') {t : CallTree E (Option α)} {m : LstateMF}
    (h : TSim I P Site Q t m Post) : TSim I P Site Q t m Post' :=
  TSim.post (fun v m' hp => ⟨0, m', Steps.refl I P m', hP v m' hp⟩) h

/-- **Sequencing.** A tree related at the end condition that relates each value and state to
    the continuation at that value gives the relation of the sequence. -/
theorem TSim.obind {α β : Type} {f : α → CallTree E (Option β)} {Post : β → LstateMF → Prop} :
    ∀ {t : CallTree E (Option α)} {m : LstateMF},
      TSim I P Site Q t m (fun x m' => TSim I P Site Q (f x) m' Post) →
      TSim I P Site Q (obind t f) m Post
  | .ret none, _, _ => trivial
  | .ret (some _), _, ⟨_, _, hs, hp⟩ => TSim.steps hs hp
  | .vis _ c, _, ⟨k, u, hs, hsite, hc⟩ =>
      ⟨k, u, hs, hsite, fun a u' hq => TSim.obind (t := c a) (hc a u' hq)⟩

/-- A leaf `some v` is related to a state where `Post v` holds. -/
theorem TSim.ret {α : Type} {v : α} {m : LstateMF} {Post : α → LstateMF → Prop}
    (h : Post v m) : TSim I P Site Q (.ret (some v)) m Post :=
  ⟨0, m, Steps.refl I P m, h⟩

end TSim

/-! ## The simulation statement for call trees -/

/-- **The tree call environment performs the calls of words and word arrays.** In every
    program, at every state at the counter of the shadow instruction of a call of `f` on as
    many operands as arguments, whose operands read as the words of the arguments `a`, the
    tree of the call is related by `TSim` to the state, with the state after the call as end
    condition: the word of the answer written to the destination at a word result (`retWord`),
    the array of the answer written to the array carrier at a result of `n` words
    (`retArr`). -/
def TCallsSim {E : EventSig} (I : Isa) (Site : LprogM → E.Event → LstateMF → Prop)
    (Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop)
    (tE : TreeCallEnv E jasminDialect) : Prop :=
  (∀ (P : LprogM) (f : String) (as : List JasminTy), (∀ t ∈ as, callArgTy t = true) →
    ∀ (a : Ctxt.Valuation (d := jasminDialect) as) (dst : String) (srcs : List LOperand)
      (tag : MemTag) (k : Nat) (s : LstateMF), atPc P k s →
      P.body[k]? = some (callShadow dst f srcs, tag) → srcs.length = as.length →
      LprogIsa.argsRead (arrArgsOf as) s.prog.base 0 srcs = some (wordsOf a) →
      TSim I P (Site P) (Q P) (tE.call f as [JasminTy.reg 64] a) s
        (fun res s' => s' = retWord dst (resWord res) s))
  ∧ (∀ (P : LprogM) (f : String) (as : List JasminTy) (nr : Nat),
    (∀ t ∈ as, callArgTy t = true) →
    ∀ (a : Ctxt.Valuation (d := jasminDialect) as) (dst : String) (srcs : List LOperand)
      (tag : MemTag) (k : Nat) (s : LstateMF), atPc P k s →
      P.body[k]? = some (callShadow dst f srcs, tag) → srcs.length = as.length →
      LprogIsa.argsRead (arrArgsOf as) s.prog.base 0 srcs = some (wordsOf a) →
      TSim I P (Site P) (Q P) (tE.call f as [JasminTy.stackArr 64 nr] a) s
        (fun res s' => s' = LprogIsa.retArr dst (resArr res) s))

/-- **The simulation statement of the region export for call trees.** The statement
    `ExportRSim` with the denotation of `p` at a call environment replaced by its call tree
    `treeAt pureReader tE`: from a state at the first instruction whose store agrees with `V`,
    the tree of `p` at `V` is related by `TSim` to the state, with the end condition of
    `ExportRSim` (the counter after the code, the returned operands agreeing with the value,
    the frame of the region) relative to that state. -/
def ExportTSim {E : EventSig} (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (I : Isa)
    (Site : LprogM → E.Event → LstateMF → Prop)
    (Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop)
    (tE : TreeCallEnv E jasminDialect) : Prop :=
  ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n = some r → Γ.length = d → nArgs ≤ d →
  ∀ (P : LprogM) (pre post : List LinstrRM), P.lfn = fn → P.body = pre ++ r.code ++ post →
    (∀ l, n ≤ l → findLabelMem l pre = none) →
  ∀ (fuel : Nat) (V : Ctxt.Valuation Γ) (m : LstateMF),
    atPc P pre.length m → StoreAgreesM nArgs d m.prog.base V →
    TSim I P (Site P) (Q P) (treeAt pureReader tE fuel p V) m fun v m' =>
      atPc P (pre.length + r.code.length) m'
      ∧ ResAgrees nArgs r.depth m'.prog.base r.res v
      ∧ RegionFrame d n m.prog.base m'.prog.base

/-! ## The return, the binding and the call -/

section Cases

variable {E : EventSig} {I : Isa} {Site : LprogM → E.Event → LstateMF → Prop}
  {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
  {tE : TreeCallEnv E jasminDialect}

/-- **The return.** -/
theorem exportTSim_ret (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts) :
    ExportTSim nArgs fn (NFProg.ret (d := jasminDialect) vs) I Site Q tE := by
  intro d n r h hlen _ P pre post _ _ _ fuel V m hat hag
  simp only [exportR, Option.some.injEq] at h
  subst h
  exact TSim.ret ⟨by simpa using hat, ⟨Γ, V, vs, hlen, hag, rfl, rfl⟩, RegionFrame.refl d n _⟩

/-- **The frame rule of a binding** for call trees. -/
theorem exportTSim_var (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {ts : List JasminTy} (e : Expr jasminDialect Γ t)
    (k : NFProg jasminDialect (t :: Γ) ts) (he : BindMemN e) (hI : x86Isa.StepLe I)
    (hk : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.var e k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  simp only [exportR, Option.map_eq_some_iff] at h
  obtain ⟨rk, hrk, rfl⟩ := h
  obtain ⟨st', hrun, hAg, hFr⟩ := he.step (nArgs := nArgs) hlen harg hag
  have hplain : PlainLopnBody (bindOps nArgs e d) :=
    JasminLsemMemFlagArrLoop.straightOpsMem_plain nArgs (Com.var e (Com.ret Ctxt.Var.here))
      (show JasminLsemMemFlagArrLoop.OpPlain e.op ∧ True from ⟨he.opPlain, trivial⟩) d
  obtain ⟨i, hi⟩ := bindOps_eq_singleton nArgs e d
  have hrun' : lsemStraightMem [i] m.prog.base = some st' := hi ▸ hrun
  have hstep : lsemStepMem i m.prog.base = some st' := by
    rw [lsemStraightMem_cons] at hrun'
    cases hs : lsemStepMem i m.prog.base with
    | none => rw [hs] at hrun'; cases hrun'
    | some b => rw [hs] at hrun'; exact hrun'
  obtain ⟨hl, hc, hm⟩ := hplain i (by rw [hi]; exact List.mem_singleton_self i)
  have hcode : (Exported.prepend (bindOps nArgs e d) rk).code = i :: rk.code := by
    simp only [Exported.prepend, hi, List.singleton_append]
  rw [hcode] at hbody
  have hfetch : P.body[pre.length]? = some i := by
    rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  obtain ⟨hs1, hat1⟩ := x86_steps_mem hat hfetch hl hc hm hstep
  have hAg' : StoreAgreesM nArgs (d + 1) st' (V.extend (e.denote V)) := hAg
  have hlab : ∀ l, n ≤ l → findLabelMem l (pre ++ [i]) = none := by
    intro l hl'
    rw [findLabelMem_eq_none_iff, labelsOf_append,
      labelsOf_of_isLopn (xs := [i]) (fun j hj => by
        rw [List.mem_singleton.mp hj]; exact hl),
      List.append_nil, ← findLabelMem_eq_none_iff]
    exact hpre l hl'
  have hK := hk (d + 1) n rk hrk
    (by rw [List.length_cons, hlen]) (by omega) P (pre ++ [i]) post hfn
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hlab
    fuel _ (setBase m (withALUFlags i m.prog.base st'))
    (by rw [List.length_append, List.length_singleton]; exact hat1)
    (StoreAgreesM.withALUFlags i m.prog.base hAg')
  have htree : treeAt pureReader tE fuel (NFProg.var e k) V
      = treeAt pureReader tE fuel k (V.extend (e.denote V)) := by
    simp only [treeAt, pureReader, Expr.denoteM_option_eq_some]
    rfl
  rw [htree]
  refine TSim.steps (steps_of_stepLe hI hs1) (TSim.mono (fun v m' hp => ?_) hK)
  obtain ⟨hat2, hres, hfr2⟩ := hp
  refine ⟨?_, hres, ((RegionFrame.of_writeFrame n hFr).withALUFlags i _).trans hfr2 (by omega)
    le_rfl⟩
  rw [hcode, List.length_cons]
  rw [List.length_append, List.length_singleton] at hat2
  rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]

/-- **The frame rule of a call with a word result** for call trees, at a tree call environment
    that performs the word-result calls. -/
theorem exportTSim_call (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {as ts : List JasminTy} (f : String) (args : HVector (fun t => Ctxt.Var Γ t) as)
    (k : NFProg jasminDialect ([JasminTy.reg 64] ++ Γ) ts)
    (has : ∀ t ∈ as, callArgTy t = true) (hc : TCallsSim I Site Q tE)
    (hk : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.call (rs := [JasminTy.reg 64]) f args k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  obtain ⟨-, rk, hrk, rfl⟩ := exportR_call_eq_some.mp h
  set i : LinstrRM := callI (regName d) f (exprArgsHV d nArgs argName (fun _ => none) args)
    with hi
  have hcode : (Exported.prepend [i] rk).code = i :: rk.code := rfl
  rw [hcode] at hbody
  have hfetch : P.body[pre.length]? = some i := by
    rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have hcall := hc.1 P f as has (Expr.lookupArgs args V) (regName d)
    (exprArgsHV d nArgs argName (fun _ => none) args) (.reg none) pre.length m hat hfetch
    (exprArgsHV_length d nArgs args)
    (argsRead_exprArgsHV hag has args (arrArgsOf as) 0 fun j => by rw [Nat.zero_add])
  have hlab : ∀ l, n ≤ l → findLabelMem l (pre ++ [i]) = none := by
    intro l hl'
    rw [findLabelMem_eq_none_iff, labelsOf_append,
      labelsOf_of_isLopn (xs := [i]) (fun j hj => by
        rw [List.mem_singleton.mp hj]; exact ⟨_, _, _, rfl⟩),
      List.append_nil, ← findLabelMem_eq_none_iff]
    exact hpre l hl'
  simp only [treeAt]
  refine TSim.obind (TSim.mono (fun res m1 hm1 => ?_) hcall)
  subst hm1
  have hat1 : atPc P (pre.length + 1) (retWord (regName d) (resWord res) m) :=
    ⟨hat.1, by simp [retWord, hat.2]⟩
  have hfr1 : RegionFrame d n m.prog.base (retWord (regName d) (resWord res) m).prog.base :=
    RegionFrame.of_cells rfl fun r hr _ => by
      simp [retWord, LstateN.setReg, hr d le_rfl]
  have hag0 := StoreAgreesM.of_regionFrame hlen hag hfr1
  have hag1 : StoreAgreesM nArgs (d + 1) (retWord (regName d) (resWord res) m).prog.base
      (hvAppend res V) :=
    storeAgreesM_append (cs := [JasminTy.reg 64]) (acc := res)
      (fun t ht => by rw [List.mem_singleton.mp ht]; rfl) harg hag0
      (fun {w} u => by
        cases u with
        | here =>
            cases res with
            | cons x xs =>
                simp only [retWord, resWord, List.length_cons, List.length_nil]
                exact JasminLsemMemSourceTieUncond.LstateM.getW_setReg_nextPc_same _ _ _
        | there u => cases u)
  have hK := hk (d + 1) n rk hrk
    (by simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega)
    (by omega) P (pre ++ [i]) post hfn
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hlab
    fuel _ _ (by rw [List.length_append, List.length_singleton]; exact hat1) hag1
  refine TSim.mono (fun v m' hp => ?_) hK
  obtain ⟨hat2, hres, hfr2⟩ := hp
  refine ⟨?_, hres, hfr1.trans hfr2 (by omega) le_rfl⟩
  rw [hcode, List.length_cons]
  rw [List.length_append, List.length_singleton] at hat2
  rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]

/-- **The frame rule of a call with an array result** for call trees. -/
theorem exportTSim_callArr (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {as ts : List JasminTy} {nr : Nat} (f : String) (args : HVector (fun t => Ctxt.Var Γ t) as)
    (k : NFProg jasminDialect ([JasminTy.stackArr 64 nr] ++ Γ) ts)
    (has : ∀ t ∈ as, callArgTy t = true) (hc : TCallsSim I Site Q tE)
    (hk : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.call (rs := [JasminTy.stackArr 64 nr]) f args k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  obtain ⟨-, rk, hrk, rfl⟩ := exportR_call_eq_some.mp h
  set i : LinstrRM := callI (regName d) f (exprArgsHV d nArgs argName (fun _ => none) args)
    with hi
  have hcode : (Exported.prepend [i] rk).code = i :: rk.code := rfl
  rw [hcode] at hbody
  have hfetch : P.body[pre.length]? = some i := by
    rw [hbody, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have hcall := hc.2 P f as nr has (Expr.lookupArgs args V) (regName d)
    (exprArgsHV d nArgs argName (fun _ => none) args) (.reg none) pre.length m hat hfetch
    (exprArgsHV_length d nArgs args)
    (argsRead_exprArgsHV hag has args (arrArgsOf as) 0 fun j => by rw [Nat.zero_add])
  have hlab : ∀ l, n ≤ l → findLabelMem l (pre ++ [i]) = none := by
    intro l hl'
    rw [findLabelMem_eq_none_iff, labelsOf_append,
      labelsOf_of_isLopn (xs := [i]) (fun j hj => by
        rw [List.mem_singleton.mp hj]; exact ⟨_, _, _, rfl⟩),
      List.append_nil, ← findLabelMem_eq_none_iff]
    exact hpre l hl'
  simp only [treeAt]
  refine TSim.obind (TSim.mono (fun res m1 hm1 => ?_) hcall)
  subst hm1
  have hat1 : atPc P (pre.length + 1) (LprogIsa.retArr (regName d) (resArr res) m) :=
    ⟨hat.1, by simp [LprogIsa.retArr, hat.2]⟩
  have hfr1 : RegionFrame d n m.prog.base
      (LprogIsa.retArr (regName d) (resArr res) m).prog.base :=
    ⟨fun r w _ _ => by simp [LprogIsa.retArr],
      fun r w m' hr _ => by
        simp only [LprogIsa.retArr, LstateM.getArr_nextPc]
        exact LstateM.getArr_setArr_other _ _ _ _ _ _ (hr d le_rfl)⟩
  have hag0 := StoreAgreesM.of_regionFrame hlen hag hfr1
  have hag1 : StoreAgreesM nArgs (d + 1)
      (LprogIsa.retArr (regName d) (resArr res) m).prog.base (hvAppend res V) :=
    storeAgreesM_append_arr (cs := [JasminTy.stackArr 64 nr]) (acc := res) harg hag0
      (fun {w} u => by cases u with | there u => cases u)
      (fun {w n'} u => by
        cases u with
        | here =>
            cases res with
            | cons x xs =>
                show ((m.prog.base.setArr (regName (d + 0)) x).nextPc).getArr
                  (regName (d + 0)) 64 nr = some x
                rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_same]
        | there u => cases u)
  have hK := hk (d + 1) n rk hrk
    (by simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega)
    (by omega) P (pre ++ [i]) post hfn
    (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append]) hlab
    fuel _ _ (by rw [List.length_append, List.length_singleton]; exact hat1) hag1
  refine TSim.mono (fun v m' hp => ?_) hK
  obtain ⟨hat2, hres, hfr2⟩ := hp
  refine ⟨?_, hres, hfr1.trans hfr2 (by omega) le_rfl⟩
  rw [hcode, List.length_cons]
  rw [List.length_append, List.length_singleton] at hat2
  rwa [show pre.length + (rk.code.length + 1) = pre.length + 1 + rk.code.length by omega]

/-- **The frame rule of a branch** for call trees. -/
theorem exportTSim_if (nArgs : Nat) (fn : String) {Γ rs : Ctxt jasminDialect}
    {ts : List JasminTy} (cond : Ctxt.Var Γ (JasminTy.reg 1))
    (thn els : NFProg jasminDialect Γ rs) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (hI : x86Isa.StepLe I) (htsim : ExportTSim nArgs fn thn I Site Q tE)
    (hesim : ExportTSim nArgs fn els I Site Q tE) (hksim : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.ifThenElse cond thn els k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, e, he, rk, hrk, rfl⟩ := h
  have hbody0 := hbody
  have hLT := exportR_labelsOK nArgs fn x86Data_guardsPlain thn _ _ _ ht
  have hLE := exportR_labelsOK nArgs fn x86Data_guardsPlain els _ _ _ he
  have hTle := hLT.le
  have hEle := hLE.le
  have htd := exportR_depth_le nArgs fn thn _ _ _ ht
  have hed := exportR_depth_le nArgs fn els _ _ _ he
  -- the condition
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) cond) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) cond = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg cond
  have hbit : m.prog.base.reg.lvm cn = ⟨1, cond.lookup V⟩ := by
    have := hag.1 cond
    rw [evalOperandN_resolveVar, ← hcn] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName cond
      (hlen ▸ JasminLsemSimulation.varIndex_lt cond) k hk
  -- the layout of the body
  obtain ⟨cmov, hcmov⟩ : ∃ cmov : LinstrRM, cmov = (.Lopn [.reg (regName d)]
      (withWidthTag 64 "CMOV") [.reg cn, .reg (regName d), .reg (regName (d + 1))], .reg none) :=
    ⟨_, rfl⟩
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (regName d)] (withWidthTag 64 "CMP")
      [.reg (regName d), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨TM, hTM⟩ : ∃ TM, TM = ifResMoves rs d (t.depth + rs.length) t.res := ⟨_, rfl⟩
  obtain ⟨EM, hEM⟩ : ∃ EM, EM = ifResMoves rs d (e.depth + rs.length) e.res := ⟨_, rfl⟩
  have hTMlab : labelsOf TM = [] := by rw [hTM]; exact labelsOf_ifResMoves _ _ _ _
  have hEMlab : labelsOf EM = [] := by rw [hEM]; exact labelsOf_ifResMoves _ _ _ _
  obtain ⟨J, hJ⟩ : ∃ J : List LinstrRM, J = [movImmI (regName (d + rs.length)) 1,
      guardI (.Lopn [.reg (regName (d + rs.length))] (withWidthTag 64 "CMP")
        [.reg (regName (d + rs.length)), .imm 0]), condI (.reg "NZ") (n + 2)] := ⟨_, rfl⟩
  have hJlab : labelsOf J = [] := by rw [hJ]; rfl
  have hF : ifFrame fn d n rs (.reg cn) t.code t.res t.depth e.code e.res e.depth
      = movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov :: cmp
        :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (J
        ++ labelI (n + 1) :: (e.code ++ (EM ++ [labelI (n + 2)]))))) := by
    rw [hcmov, hcmp, hTM, hEM, hJ]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, hF]
    at hbody
  have hbodyH : P.body = pre ++ (movImmI (regName d) 1 :: movImmI (regName (d + 1)) 0 :: cmov
      :: cmp :: condI (.reg "Z") (n + 1) :: labelI n :: (t.code ++ (TM ++ (J
      ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post))))))) := by
    rw [hbody]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov,
      cmp, condI (.reg "Z") (n + 1)] := ⟨_, rfl⟩
  have hbodyA : P.body = A ++ labelI n :: (t.code ++ (TM ++ (J
      ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post)))))) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = pre.length + 4 + 1 := by
    rw [hAd, List.length_append]
    rfl
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmov, hcmp, labelsOf_append]
    exact List.append_nil _
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = A ++ labelI n :: (t.code ++ (TM ++ J)) := ⟨_, rfl⟩
  have hbodyY : P.body = Y ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
      :: (rk.code ++ post))) := by
    rw [hbodyA, hYd]
    simp only [List.append_assoc, List.cons_append]
  have hYlabs : labelsOf Y = labelsOf pre ++ n :: labelsOf t.code := by
    simp only [hYd, labelsOf_append, hAlabs, labelsOf_cons_labelI, hJlab, hTMlab,
      List.append_nil]
  obtain ⟨X, hXd⟩ : ∃ X, X = Y ++ labelI (n + 1) :: (e.code ++ EM) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 2) :: (rk.code ++ post) := by
    rw [hbodyY, hXd]
    simp only [List.append_assoc, List.cons_append]
  have hXlabs : labelsOf X
      = labelsOf pre ++ n :: (labelsOf t.code ++ (n + 1) :: labelsOf e.code) := by
    simp only [hXd, labelsOf_append, hYlabs, labelsOf_cons_labelI, hEMlab, List.append_nil,
      List.append_assoc, List.cons_append]
  have hXlen : X.length = (Y ++ labelI (n + 1) :: e.code).length + EM.length := by
    rw [hXd]
    simp only [List.length_append, List.length_cons]
    omega
  have hpreL : ∀ l, n ≤ l → l ∉ labelsOf pre := fun l hl =>
    (findLabelMem_eq_none_iff l pre).mp (hpre l hl)
  have hYnot : ∀ l : Nat, n + 1 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf Y := by
    intro l hl ht' hm
    rw [hYlabs, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
  have hXnot : ∀ l : Nat, n + 2 ≤ l → l ∉ labelsOf t.code → l ∉ labelsOf e.code →
      l ∉ labelsOf X := by
    intro l hl ht' he' hm
    rw [hXlabs, List.mem_append, List.mem_cons, List.mem_append, List.mem_cons] at hm
    rcases hm with hm | hm | hm | hm | hm
    · exact hpreL l (by omega) hm
    · omega
    · exact ht' hm
    · omega
    · exact he' hm
  have hl1 : findLabelMem (n + 1) P.body = some Y.length := by
    rw [hbodyY]
    exact findLabelMem_append_labelI (n + 1) Y _
      (hYnot (n + 1) le_rfl fun hm => by have := hLT.range _ hm; omega)
  have hl2 : findLabelMem (n + 2) P.body = some X.length := by
    rw [hbodyX]
    exact findLabelMem_append_labelI (n + 2) X _
      (hXnot (n + 2) le_rfl (fun hm => by have := hLT.range _ hm; omega)
        fun hm => by have := hLE.range _ hm; omega)
  -- the head
  obtain ⟨t0, hs0, hat0, hz0, hfr0⟩ := ifHead_steps (d := d) (f := cn) pre _ m
    (bit := cond.lookup V) (by rw [hbodyH, hcmov, hcmp]) hat hcnk hbit
  have hz0' : t0.zf = !(HasBoolBit.toBool (d := jasminDialect) (cond.lookup V)) := hz0
  have hfetchZ : P.body[pre.length + 4]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ [movImmI (regName d) 1, movImmI (regName (d + 1)) 0, cmov, cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by rw [List.length_append]; rfl)
  -- the selected branch, to the counter after the join label
  have hjoin : TSim I P (Site P) (Q P)
      (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then
        treeAt pureReader tE fuel thn V else treeAt pureReader tE fuel els V) m
      fun rv mJ => atPc P (X.length + 1) mJ
      ∧ RegionFrame d n m.prog.base mJ.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var rs (.reg w)),
          mJ.prog.base.reg.getW (regName (d + (rs.length - 1 - varIndex u))) w
            = some (u.lookup rv))
      ∧ (∀ {w m' : Nat} (u : Ctxt.Var rs (.stackArr w m')),
          mJ.prog.base.getArr (regName (d + (rs.length - 1 - varIndex u))) w m'
            = some (u.lookup rv)) := by
    by_cases hbt : HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) = true
    · rw [ite_eq_left hbt]
      obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; decide)
      rw [← hAlen] at hat1
      obtain ⟨hs2, hat2⟩ := steps_label I (kind := .internal) (l := n) (tag := .reg none)
        hat1 (fetch_of_body hbodyA rfl)
      have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      have hT := htsim d (n + 3) t ht hlen harg P
        (A ++ [labelI n]) (TM ++ (J ++ labelI (n + 1) :: (e.code ++ (EM
          ++ labelI (n + 2) :: (rk.code ++ post))))) hfn
        (by rw [hbodyA]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hpreL l (by omega), fun he => by have : (l : Nat) = n := he; omega⟩)
        fuel V (next (next t0))
        (by rw [List.length_append, List.length_singleton]; exact hat2)
        (StoreAgreesM.of_regionFrame hlen hag hfr2)
      refine TSim.steps ((steps_of_stepLe hI (hs0.trans hs1)).trans hs2)
        (TSim.post (fun rv m3 hp => ?_) hT)
      obtain ⟨hat3, hres3, hfr3⟩ := hp
      have hat3' : atPc P (A ++ labelI n :: t.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show A.length + (t.code.length + 1) = A.length + 1 + t.code.length by omega]
      obtain ⟨m4, hs4, hat4, hfr4, hblk4, hblkA4⟩ := ifResMoves_steps (nArgs := nArgs)
        (d := d) (D := t.depth) (rs := rs) (ops := t.res) (A ++ labelI n :: t.code)
        (J ++ labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2)
          :: (rk.code ++ post)))) m3 (rv := rv)
        (by rw [hbodyA, hTM]; simp only [List.append_assoc, List.cons_append])
        hat3' htd hres3
      rw [← hTM] at hs4 hat4
      have hlen4 : (A ++ labelI n :: (t.code ++ TM)).length
          = (A ++ labelI n :: t.code).length + TM.length := by
        simp only [List.length_append, List.length_cons]
        omega
      rw [← hlen4] at hat4
      obtain ⟨m5, hs5, hat5, ha5, hm5⟩ := joinJump_steps (r := regName (d + rs.length))
        (l := n + 2) (A ++ labelI n :: (t.code ++ TM))
        (labelI (n + 1) :: (e.code ++ (EM ++ labelI (n + 2) :: (rk.code ++ post)))) m4
        (by rw [hbodyA, hJ]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        hat4 hl2
      exact ⟨_, m5, steps_of_stepLe hI (hs4.trans hs5), hat5,
        (((hfr2.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells ha5 fun r hr _ => hm5 r (hr _ (Nat.le_add_right _ _)))
          le_rfl le_rfl),
        fun {w} u => (getW_congr w (hm5 _ fun he => by
          have := JasminLsemSimulation.regName_injective he
          have := JasminLsemSimulation.varIndex_lt u
          omega)).trans (hblk4 u),
        fun {w m'} u => (getArr_of_larr_eq w m' (by rw [ha5])).trans (hblkA4 u)⟩
    · rw [ite_eq_right hbt]
      rw [Bool.not_eq_true] at hbt
      obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
        (by rw [hz0', hbt]; rfl) hl1
      have hfr1 : RegionFrame d n m.prog.base (goto t0 (Y.length + 1)).prog.base :=
        (hfr0 n).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      have hE := hesim d t.next e he hlen harg P
        (Y ++ [labelI (n + 1)]) (EM ++ labelI (n + 2) :: (rk.code ++ post)) hfn
        (by rw [hbodyY]; simp only [List.append_assoc, List.cons_append, List.nil_append])
        (fun l hl => by
          rw [findLabelMem_eq_none_iff, labelsOf_append]
          simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
            not_or]
          exact ⟨hYnot l (by omega) fun hm => by have := hLT.range l hm; omega,
            fun he => by have : (l : Nat) = n + 1 := he; omega⟩)
        fuel V (goto t0 (Y.length + 1))
        (by rw [List.length_append, List.length_singleton]; exact hat1)
        (StoreAgreesM.of_regionFrame hlen hag hfr1)
      refine TSim.steps (steps_of_stepLe hI (hs0.trans hs1))
        (TSim.post (fun rv m3 hp => ?_) hE)
      obtain ⟨hat3, hres3, hfr3⟩ := hp
      have hat3' : atPc P (Y ++ labelI (n + 1) :: e.code).length m3 := by
        rw [List.length_append, List.length_singleton] at hat3
        rw [List.length_append, List.length_cons]
        rwa [show Y.length + (e.code.length + 1) = Y.length + 1 + e.code.length by omega]
      obtain ⟨m4, hs4, hat4, hfr4, hblk4, hblkA4⟩ := ifResMoves_steps (nArgs := nArgs)
        (d := d) (D := e.depth) (rs := rs) (ops := e.res) (Y ++ labelI (n + 1) :: e.code)
        (labelI (n + 2) :: (rk.code ++ post)) m3 (rv := rv)
        (by rw [hbodyY, hEM]; simp only [List.append_assoc, List.cons_append])
        hat3' hed hres3
      rw [← hEM] at hs4 hat4
      rw [← hXlen] at hat4
      obtain ⟨hs5, hat5⟩ := steps_label I (kind := .internal) (l := n + 2)
        (tag := .reg none) hat4 (fetch_of_body hbodyX rfl)
      exact ⟨_, _, (steps_of_stepLe hI hs4).trans hs5, hat5,
        (((hfr1.trans hfr3 le_rfl (by omega)).trans (hfr4 n) le_rfl le_rfl).trans
          (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl),
        fun {w} u => hblk4 u, fun {w m'} u => hblkA4 u⟩
  simp only [treeAt]
  refine TSim.obind (TSim.mono (fun rv mJ hp => ?_) hjoin)
  obtain ⟨hatJ, hfrJ, hblkJ, hblkAJ⟩ := hp
  have hagJ : StoreAgreesM nArgs (d + rs.length) mJ.prog.base (hvAppend rv V) :=
    storeAgreesM_append_arr harg (StoreAgreesM.of_regionFrame hlen hag hfrJ)
      (fun {w} u => hblkJ u) (fun {w m'} u => hblkAJ u)
  -- the continuation
  have hK := hksim (d + rs.length) e.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P (X ++ [labelI (n + 2)]) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append]
      simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨hXnot l (by omega) (fun hm => by have := hLT.range l hm; omega)
          fun hm => by have := hLE.range l hm; omega,
        fun he => by have : (l : Nat) = n + 2 := he; omega⟩)
    fuel _ mJ (by rw [List.length_append, List.length_singleton]; exact hatJ) hagJ
  have hlenEq : pre.length + (Exported.prepend (ifFrame fn d n rs
      (resolveVar d nArgs argName (fun _ => none) cond) t.code t.res t.depth e.code e.res
      e.depth) rk).code.length = (X ++ [labelI (n + 2)]).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
    omega
  refine TSim.mono (fun v m' hp => ?_) hK
  obtain ⟨hatK, hresK, hfrK⟩ := hp
  exact ⟨by rw [hlenEq]; exact hatK, hresK, hfrJ.trans hfrK (by omega) (by omega)⟩

end Cases

/-! ## The exit-flag loop -/

section WhileLoop

variable {E : EventSig} {Site : LprogM → E.Event → LstateMF → Prop}
  {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
  {tE : TreeCallEnv E jasminDialect}
variable (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs)) (hcs : RegTys cs)
  {I : Isa} (hI : x86Isa.StepLe I)
  (hsim : ExportTSim nArgs fn body I Site Q tE) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + cs.length) (n + 1) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R Z : List LinstrRM} {fname : String} (hfn : P.lfn = fn)
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hfh : b.res.headD (.imm 0) = .reg fname)
  (hR : R = movImmI (regName (b.depth + cs.length)) 1
    :: movImmI (regName (b.depth + cs.length + 1)) 0
    :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
      [.reg fname, .reg (regName (b.depth + cs.length)),
        .reg (regName (b.depth + cs.length + 1))], .reg none)
    :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
      ++ guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
        [.reg (regName (b.depth + cs.length)), .imm 0]) :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hcs hI hsim hb hlen harg hfn hbody hfh hR hA in
/-- **One trip of an exit-flag loop** for call trees, from the counter after the label to the
    back-edge jump. The zero flag is the negation of the continue bit. -/
theorem whileLoop_tripT (acc : Ctxt.Valuation cs) (m : LstateMF)
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) :
    TSim I P (Site P) (Q P) (treeAt pureReader tE fuel body (hvAppend acc V)) m fun r t =>
      atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4) t
      ∧ RegionFrame d n m.prog.base t.prog.base
      ∧ t.zf = !(HasBoolBit.toBool (d := jasminDialect) r.head)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup r.tail)) := by
  have hag2 : StoreAgreesM nArgs (d + cs.length) m.prog.base (hvAppend acc V) :=
    storeAgreesM_append hcs harg hag hblk
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  have hT := hsim (d + cs.length) (n + 1) b hb
      (by rw [List.length_append, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ m
      (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  refine TSim.post (fun r m1 hp => ?_) hT
  obtain ⟨hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hr⟩, hfr1⟩ := hp
  subst hr
  cases vs with
  | cons v0 vrest =>
  have hops' : b.res = resolveVar b.depth nArgs argName (fun _ => none) v0
      :: exprArgsHV b.depth nArgs argName (fun _ => none) vrest := hops
  have hfh' : resolveVar b.depth nArgs argName (fun _ => none) v0 = .reg fname := by
    rw [hops'] at hfh
    exact hfh
  have hfname : fname = operandName (resolveVar b.depth nArgs argName (fun _ => none) v0) := by
    rw [hfh']
    rfl
  have hbit : m1.prog.base.reg.lvm fname = ⟨1, v0.lookup W⟩ := by
    have := hagW.1 v0
    rw [hfh'] at this
    exact getW_eq_some_iff.mp this
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, hle2, harr, hz, hblk', hoth⟩ :=
    whileTail_steps (d := d) (nCar := cs.length) (bD := b.depth) (ops := b.res.tail)
      (f := fname) (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (bit := v0.lookup W)
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append])
      hat1' (by rw [hops', List.tail_cons, exprArgsHV_length]) (by omega)
      (by rw [hops', List.tail_cons]; exact exprArgsHV_reg nArgs hΔ vrest)
      (fun k hk => by
        rw [hfname]
        exact resolveVar_operandName_ne_regName v0
          (hΔ ▸ JasminLsemSimulation.varIndex_lt v0) k hk)
      hbit
  refine ⟨k2, t, steps_of_stepLe hI hs2, hat2, ?_, hz, fun {w} u => ?_⟩
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_cells harr fun r hr _ => hoth r hr) le_rfl le_rfl
  · have hu := JasminLsemSimulation.varIndex_lt u
    rw [getW_of_lvm_eq w (hblk' (varIndex u) hu), hops', List.tail_cons, exprArgsHV_getD,
      ← evalOperandN_resolveVar]
    exact (hagW.1 (hvToHom vrest u)).trans (congrArg some (lookup_lookupArgs W vrest u).symm)

include hcs hI hsim hb hlen harg hfn hbody hfh hR hA in
/-- **The trips of an exit-flag loop** for call trees. From the counter after the label with
    the carried tuple in the carried block, the tree of the iteration of the body within `f`
    runs is related to the state, with the counter after the back-edge jump, the frame of the
    region and the returned tuple in the carried block as end condition. -/
theorem whileLoop_tripsT : ∀ (f : Nat) (acc : Ctxt.Valuation cs) (m : LstateMF),
    atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    TSim I P (Site P) (Q P)
      (owhileIter (fun acc => treeAt pureReader tE fuel body (hvAppend acc V)) f acc) m
      fun accN m' =>
      atPc P ((A ++ labelI n :: b.code).length + 2 * cs.length + 4 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hfetch : P.body[(A ++ labelI n :: b.code).length + 2 * cs.length + 4]?
      = some (condI (.reg "NZ") n) :=
    fetch_of_body (xs := (A ++ labelI n :: b.code)
        ++ [movImmI (regName (b.depth + cs.length)) 1,
          movImmI (regName (b.depth + cs.length + 1)) 0,
          (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
            [.reg fname, .reg (regName (b.depth + cs.length)),
              .reg (regName (b.depth + cs.length + 1))], .reg none)]
        ++ parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0])])
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, parMoves_length, carriedRegs_length, List.length_tail,
          hreslen, List.length_cons, List.length_nil]
        omega)
  have hl : findLabelMem n P.body = some A.length := by
    rw [hbody]
    exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
  intro f
  induction f with
  | zero => intro acc m _ _ _; trivial
  | succ f ih =>
      intro acc m hat hag hblk
      simp only [owhileIter]
      refine TSim.obind (TSim.mono (fun r t hp => ?_)
        (whileLoop_tripT nArgs fn body hcs hI hsim hb hlen harg hfn hbody hfh hR hA fuel V acc m
          hat hag hblk))
      obtain ⟨hat2, hfr, hz, hblk'⟩ := hp
      by_cases hbt : HasBoolBit.toBool (d := jasminDialect) r.head = true
      · rw [ite_eq_left hbt]
        obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 hfetch (by rw [hz, hbt]; rfl) hl
        have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
          hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        refine TSim.steps (steps_of_stepLe hI hs') (TSim.mono (fun accN m' hp => ?_)
          (ih r.tail (goto t (A.length + 1)) hat' (StoreAgreesM.of_regionFrame hlen hag hfr')
            (fun {w} u => hblk' u)))
        obtain ⟨hat'', hfr'', hblk''⟩ := hp
        exact ⟨hat'', hfr'.trans hfr'' le_rfl le_rfl, fun {w} u => hblk'' u⟩
      · rw [ite_eq_right hbt]
        obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch
          (by rw [hz, Bool.not_eq_true] at *; rw [hbt]; decide)
        exact TSim.steps (steps_of_stepLe hI hs') (TSim.ret ⟨hat', hfr, fun {w} u => hblk' u⟩)

end WhileLoop

section WhileFrame

variable {E : EventSig} {Site : LprogM → E.Event → LstateMF → Prop}
  {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
  {tE : TreeCallEnv E jasminDialect}

/-- **The frame rule of an exit-flag loop** for call trees. For carried types held in register
    cells, the statement for the body and for the continuation gives the statement for the
    loop. -/
theorem exportTSim_while (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
    {ts : List JasminTy} (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (JasminTy.reg 1 :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts) (hcs : RegTys cs)
    {I : Isa} (hI : x86Isa.StepLe I)
    (hbsim : ExportTSim nArgs fn body I Site Q tE) (hksim : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.whileLoop inits body k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  have hreslen := exportR_res_length nArgs fn body _ _ _ hb
  have hisreg := exportR_res_isReg nArgs fn body _ _ _ hb
  obtain ⟨fname, hfh⟩ : ∃ fname, b.res.headD (.imm 0) = .reg fname := by
    cases hres : b.res with
    | nil => rw [hres] at hreslen; simp at hreslen
    | cons o rest => exact ⟨operandName o, hisreg o (by rw [hres]; exact List.mem_cons_self)⟩
  have htail : b.res.tail.length = cs.length := by
    rw [List.length_tail, hreslen]
    rfl
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg := exprArgsHV_reg nArgs hlen inits
  rw [← hops] at hopsreg
  -- the layout of the body
  obtain ⟨T, hT⟩ : ∃ T, T = movImmI (regName (b.depth + cs.length)) 1
      :: movImmI (regName (b.depth + cs.length + 1)) 0
      :: (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMOV")
        [.reg fname, .reg (regName (b.depth + cs.length)),
          .reg (regName (b.depth + cs.length + 1))], .reg none)
      :: (parMoves b.depth (carriedRegs d cs.length) b.res.tail
        ++ [guardI (.Lopn [.reg (regName (b.depth + cs.length))] (withWidthTag 64 "CMP")
          [.reg (regName (b.depth + cs.length)), .imm 0]), condI (.reg "NZ") n]) := ⟨_, rfl⟩
  have hTlen : T.length = 2 * cs.length + 4 + 1 := by
    rw [hT]
    simp only [List.length_cons, List.length_append, parMoves_length, carriedRegs_length,
      htail, List.length_nil]
    omega
  have hTlabs : labelsOf T = [] := by
    rw [hT]
    show labelsOf (parMoves b.depth (carriedRegs d cs.length) b.res.tail ++ [_, _]) = []
    rw [labelsOf_append, labelsOf_parMoves]
    rfl
  have hF : whileFrame d n cs.length ops b.code (.reg fname) b.res.tail b.depth
      = seedMoves (carriedRegs d cs.length) ops ++ labelI n :: (b.code ++ T) := by
    rw [hT]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hfh, ← hops, hF]
    at hbody
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ seedMoves (carriedRegs d cs.length) ops := ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbody, hAd]
    simp only [List.append_assoc, List.cons_append]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, labelsOf_append, labelsOf_seedMoves, List.append_nil]
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  have hcar := carriedRegs_length d cs.length
  -- the seeds
  have hbodyS : P.body = pre ++ (List.range cs.length).map (fun j =>
      movI ((carriedRegs d cs.length).getD j "") (.reg (operandName (ops.getD j (.imm 0)))))
      ++ labelI n :: (b.code ++ (T ++ (rk.code ++ post))) := by
    rw [hbodyL, hAd, seedMoves_eq_range _ _ (by rw [hopslen, hcar])
      (fun o ho => (hopsreg o ho).1), hcar]
  obtain ⟨t0, hs0, hat0, ha0, hm0, ho0⟩ := steps_moves P
    (fun j => (carriedRegs d cs.length).getD j "")
    (fun j => operandName (ops.getD j (.imm 0))) cs.length pre _ m hbodyS hat
    (fun i j hij hj => getD_ne_of_nodup (carriedRegs_nodup _ _) hij (by rw [hcar]; exact hj))
    (fun i j hij hj he => by
      rw [carriedRegs_getD _ _ _ (by omega)] at he
      exact (hopsreg _ (getD_mem_of_lt _ (hopslen ▸ hj))).2 _ (by omega) he)
  have hAlen : A.length = pre.length + cs.length := by
    rw [hAd, List.length_append]
    simp only [seedMoves, List.length_map, List.length_zip, hcar, hopslen, Nat.min_self]
  rw [← hAlen] at hat0
  obtain ⟨hs1, hat1⟩ := steps_label I (kind := .internal) (l := n) (tag := .reg none)
    hat0 (fetch_of_body hbodyL rfl)
  have hfr1 : RegionFrame d n m.prog.base (next t0).prog.base :=
    RegionFrame.of_cells ha0 fun r hr _ => ho0 r fun j hj => by
      rw [carriedRegs_getD _ _ _ hj]
      exact hr _ (by omega)
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    have hu := JasminLsemSimulation.varIndex_lt u
    have h1 := hm0 (varIndex u) hu
    rw [carriedRegs_getD _ _ _ hu] at h1
    rw [show (next t0).prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w
        = t0.prog.base.reg.getW (regName (d + (cs.length - 1 - varIndex u))) w from rfl,
      getW_of_lvm_eq w h1, hops, exprArgsHV_getD, ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  -- the trips
  have hTr := whileLoop_tripsT nArgs fn body hcs hI hbsim hb hlen harg hfn hbodyL hfh
      (Z := rk.code ++ post) (by rw [hT]; simp only [List.append_assoc, List.cons_append,
        List.nil_append]) hAlab fuel V fuel (Expr.lookupArgs inits V) (next t0) hat1
      (StoreAgreesM.of_regionFrame hlen hag hfr1) (fun {w} u => hblkI u)
  have hnext := hLab.le
  have hlenEq : pre.length + (Exported.prepend (whileFrame d n cs.length
      (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
      b.res.tail b.depth) rk).code.length
      = (A ++ labelI n :: (b.code ++ T)).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyL] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  simp only [treeAt]
  refine TSim.steps ((steps_of_stepLe hI hs0).trans hs1)
    (TSim.obind (TSim.mono (fun accN m3 hp => ?_) hTr))
  obtain ⟨hat3, hfr3, hblk3⟩ := hp
  have hfrS : RegionFrame d n m.prog.base m3.prog.base := hfr1.trans hfr3 le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) m3.prog.base (hvAppend accN V) :=
    storeAgreesM_append hcs harg (StoreAgreesM.of_regionFrame hlen hag hfrS)
      (fun {w} u => hblk3 u)
  -- the continuation
  have hK := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (A ++ labelI n :: (b.code ++ T)) post hfn
    (by rw [hbodyL]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hAlabs, labelsOf_cons_labelI,
        labelsOf_append, hTlabs, List.append_nil]
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega)
    fuel _ m3
    (by
      simp only [List.length_append, List.length_cons, hTlen] at hat3 ⊢
      rwa [show A.length + (b.code.length + (2 * cs.length + 4 + 1) + 1)
        = A.length + (b.code.length + 1) + 2 * cs.length + 4 + 1 by omega])
    hagS
  refine TSim.mono (fun v m' hp => ?_) hK
  obtain ⟨hatK, hresK, hfrK⟩ := hp
  exact ⟨by rw [hlenEq]; exact hatK, hresK, hfrS.trans hfrK (by omega) (by omega)⟩

end WhileFrame

/-! ## The counted loop -/

section ForArrLoop

variable {E : EventSig} {Site : LprogM → E.Event → LstateMF → Prop}
  {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
  {tE : TreeCallEnv E jasminDialect}
variable (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
  (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
  {I : Isa} (hI : x86Isa.StepLe I)
  (hsim : ExportTSim nArgs fn body I Site Q tE) {d n : Nat} {b : Exported}
  (hb : exportR nArgs fn body (d + 1 + cs.length) (n + 2) = some b) (hlen : Γ.length = d)
  (harg : nArgs ≤ d) {P : LprogM} {A R T Z : List LinstrRM} (hfn : P.lfn = fn)
  {tp : List (JasminTy × String × String)}
  (htp : tp = carriedPairs cs (carriedRegs (d + 1) cs.length) b.res)
  (hT : T = movImmI (regName (b.depth + 1)) 0
      :: arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tp)
    ++ parMoves b.depth ((regPairs tp).map Prod.fst) ((regPairs tp).map fun p => .reg p.2))
  (hbody : P.body = A ++ labelI n :: (b.code ++ R))
  (hR : R = T ++ (advanceOps (regName d) (loopCtr n)
    ++ guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP") [.reg (loopCtr n), .imm 0])
      :: condI (.reg "NZ") n :: Z))
  (hA : ∀ l, n ≤ l → findLabelMem l A = none) (fuel : Nat) (V : Ctxt.Valuation Γ)

include hI hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **One trip of a counted loop** for call trees, from the counter after the top label to the
    back-edge jump. -/
theorem forArrLoop_tripT (i : Nat) (acc : Ctxt.Valuation cs) (m : LstateMF) (c : BitVec 64)
    (hat : atPc P (A.length + 1) m) (hag : StoreAgreesM nArgs d m.prog.base V)
    (hidx : m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩)
    (hctr : m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩)
    (hblk : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc))
    (hblkA : ∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      m.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup acc)) :
    TSim I P (Site P) (Q P) (treeAt pureReader tE fuel body
        (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V))) m fun acc1 t =>
      atPc P (A.length + 1 + b.code.length + T.length + 3) t
      ∧ RegionFrame d n m.prog.base t.prog.base ∧ t.zf = (c - 1#64 == 0#64)
      ∧ t.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i + 1#64⟩
      ∧ t.prog.base.reg.lvm (loopCtr n) = ⟨64, c - 1#64⟩
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          t.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup acc1))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          t.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup acc1)) := by
  have hag1 : StoreAgreesM nArgs (d + 1) m.prog.base
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ)) :=
    storeAgreesM_append (cs := [JasminTy.reg 64])
      (acc := (HVector.cons (BitVec.ofNat 64 i) HVector.nil :
        Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 64]))
      (fun t ht => by rw [List.mem_singleton.mp ht]; rfl) harg hag
      (fun {w} u => by
        cases u with
        | here => exact getW_of_lvm _ _ _ hidx
        | there u => cases u)
  have hag2 : StoreAgreesM nArgs (d + 1 + cs.length) m.prog.base (hvAppend acc
      (HVector.cons (BitVec.ofNat 64 i) V : Ctxt.Valuation (JasminTy.reg 64 :: Γ))) :=
    storeAgreesM_append_arr (by omega) hag1 hblk hblkA
  have hbd := exportR_depth_le nArgs fn body _ _ _ hb
  have hS := hsim (d + 1 + cs.length) (n + 2) b hb
      (by simp only [List.length_append, List.length_cons, hlen]; omega) (by omega) P
      (A ++ [labelI n]) R hfn
      (by rw [hbody]; simp only [List.append_assoc, List.cons_append, List.nil_append])
      (fun l hl => by
        rw [findLabelMem_eq_none_iff, labelsOf_append]
        simp only [labelsOf_cons_labelI, labelsOf_nil, List.mem_append, List.mem_singleton,
          not_or]
        exact ⟨(findLabelMem_eq_none_iff l A).mp (hA l (by omega)),
          fun he => by have : (l : Nat) = n := he; omega⟩)
      fuel _ m (by rw [List.length_append, List.length_singleton]; exact hat) hag2
  refine TSim.post (fun acc1 m1 hp => ?_) hS
  obtain ⟨hat1, ⟨Δ, W, vs, hΔ, hagW, hops, hacc⟩, hfr1⟩ := hp
  have hres_len : b.res.length = cs.length := by rw [hops, exprArgsHV_length]
  have hat1' : atPc P (A ++ labelI n :: b.code).length m1 := by
    rw [List.length_append, List.length_singleton] at hat1
    rw [List.length_append, List.length_cons]
    rwa [show A.length + (b.code.length + 1) = A.length + 1 + b.code.length by omega]
  obtain ⟨k2, t, hs2, hat2, hle2, hz, hidx', hctr', hR', hA', hothR, hothA⟩ :=
    forArrTail_steps (d := d) (n := n) (bD := b.depth) (ops := b.res) htp
      (A ++ labelI n :: b.code) (condI (.reg "NZ") n :: Z) m1 (x := BitVec.ofNat 64 i) (c := c)
      (by rw [hbody, hR, hT]; simp only [List.append_assoc, List.cons_append]) hat1' hres_len hbd
      (by rw [hops]; exact fun o ho => (exprArgsHV_reg nArgs hΔ vs o ho).2)
      (by
        rw [hfr1.lvm_eq _
          (fun k hk he => by have := JasminLsemSimulation.regName_injective he; omega)
          (fun l _ he => loopCtr_ne_regName l d he.symm)]
        exact hidx)
      (by
        rw [hfr1.lvm_eq _ (fun k _ => loopCtr_ne_regName n k)
          (fun l hl he => by have := loopCtr_injective he; omega)]
        exact hctr)
      (fun {w q} u => ⟨_, by rw [hops, exprArgsHV_getD]; exact hagW.2 (hvToHom vs u)⟩)
  refine ⟨k2, t, steps_of_stepLe hI hs2, ?_, ?_, hz, hidx', hctr',
    fun {w} u => ?_, fun {w q} u => ?_⟩
  · rw [hT]
    simp only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] at hat2 ⊢
    exact hat2
  · exact (hfr1.mono (by omega) (by omega)).trans
      (RegionFrame.of_lvm_larr (fun r hr hl => hothR r hr (hl n le_rfl)) hothA) le_rfl le_rfl
  · rw [getW_of_lvm_eq w (hR' u), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, hacc, lookup_lookupArgs]
    exact hagW.1 (hvToHom vs u)
  · rw [getArr_of_larr_eq w q (hA' u), hops, exprArgsHV_getD, hacc, lookup_lookupArgs]
    exact hagW.2 (hvToHom vs u)

include hI hsim hb hlen harg hfn htp hT hbody hR hA in
/-- **The trips of a counted loop** for call trees. From the counter after the top label with
    `rem + 1` trips left, the trip index `i` in its register and the carried tuple in the
    carried block, the tree of the fold of the remaining trips is related to the state, with the
    counter after the back-edge jump, the frame of the region, a word in the trip index and the
    tuple of the fold in the carried block as end condition. -/
theorem forArrLoop_tripsT : ∀ (rem i : Nat) (acc : Ctxt.Valuation cs) (m : LstateMF)
    (c : BitVec 64),
    c.toNat = rem + 1 → atPc P (A.length + 1) m → StoreAgreesM nArgs d m.prog.base V →
    m.prog.base.reg.lvm (regName d) = ⟨64, BitVec.ofNat 64 i⟩ →
    m.prog.base.reg.lvm (loopCtr n) = ⟨64, c⟩ →
    (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      m.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup acc)) →
    (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      m.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup acc)) →
    TSim I P (Site P) (Q P) (ofoldl (fun acc i => treeAt pureReader tE fuel body
        (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
        (List.range' i (rem + 1)) acc) m fun accN m' =>
      atPc P (A.length + 1 + b.code.length + T.length + 3 + 1) m'
      ∧ RegionFrame d n m.prog.base m'.prog.base
      ∧ (∃ x : BitVec 64, m'.prog.base.reg.lvm (regName d) = ⟨64, x⟩)
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          m'.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          m'.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup accN)) := by
  have hcc : flagCondCC? (condI (.reg "NZ") n) = some (false, n) := rfl
  have hfetch : P.body[A.length + 1 + b.code.length + T.length + 3]?
      = some (condI (.reg "NZ") n) :=
    fetch_of_body (xs := A ++ labelI n :: (b.code ++ (T ++ (advanceOps (regName d) (loopCtr n)
        ++ [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
          [.reg (loopCtr n), .imm 0])]))))
      (by rw [hbody, hR]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by
        simp only [List.length_append, List.length_cons, advanceOps, List.length_nil]
        omega)
  intro rem
  induction rem with
  | zero =>
      intro i acc m c hc hat hag hidx hctr hblk hblkA
      simp only [Nat.zero_add, List.range'_one, ofoldl]
      refine TSim.obind (TSim.mono (fun acc1 t hp => ?_)
        (forArrLoop_tripT nArgs fn body hI hsim hb hlen harg hfn htp hT hbody hR hA fuel V i acc
          m c hat hag hidx hctr hblk hblkA))
      obtain ⟨hat2, hfr, hz, hidx', _, hblk', hblkA'⟩ := hp
      have hc1 : c - 1#64 = 0#64 := by bv_omega
      obtain ⟨hs', hat'⟩ := steps_cc_fall hcc hat2 hfetch (by rw [hz, hc1]; decide)
      exact TSim.steps (steps_of_stepLe hI hs') (TSim.ret ⟨hat', hfr, ⟨_, hidx'⟩,
        fun {w} u => hblk' u, fun {w q} u => hblkA' u⟩)
  | succ rem ih =>
      intro i acc m c hc hat hag hidx hctr hblk hblkA
      rw [List.range'_succ]
      simp only [ofoldl]
      refine TSim.obind (TSim.mono (fun acc1 t hp => ?_)
        (forArrLoop_tripT nArgs fn body hI hsim hb hlen harg hfn htp hT hbody hR hA fuel V i acc
          m c hat hag hidx hctr hblk hblkA))
      obtain ⟨hat2, hfr, hz, hidx', hctr', hblk', hblkA'⟩ := hp
      have hc1 : c - 1#64 ≠ 0#64 := by bv_omega
      have hl : findLabelMem n P.body = some A.length := by
        rw [hbody]
        exact findLabelMem_append_labelI n A _ ((findLabelMem_eq_none_iff n A).mp (hA n le_rfl))
      obtain ⟨hs', hat'⟩ := steps_cc_taken hcc hat2 hfetch (by rw [hz]; simpa using hc1) hl
      have hfr' : RegionFrame d n m.prog.base (goto t (A.length + 1)).prog.base :=
        hfr.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
      refine TSim.steps (steps_of_stepLe hI hs') (TSim.mono (fun accN m' hp => ?_)
        (ih (i + 1) acc1 (goto t (A.length + 1)) (c - 1#64) (by bv_omega) hat'
          (StoreAgreesM.of_regionFrame hlen hag hfr')
          (by rw [BitVec.ofNat_add]; exact hidx') hctr' (fun {w} u => hblk' u)
          (fun {w q} u => hblkA' u)))
      obtain ⟨hat'', hfr'', hx'', hblk'', hblkA''⟩ := hp
      exact ⟨hat'', hfr'.trans hfr'' le_rfl le_rfl, hx'', fun {w} u => hblk'' u,
        fun {w q} u => hblkA'' u⟩

end ForArrLoop

section ForArrFrame

variable {E : EventSig} {Site : LprogM → E.Event → LstateMF → Prop}
  {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
  {tE : TreeCallEnv E jasminDialect}

/-- **The frame rule of a counted loop** for call trees, for a carried tuple of registers and
    stack arrays. -/
theorem exportTSim_for (nArgs : Nat) (fn : String) {Γ cs : Ctxt jasminDialect}
    {ts : List JasminTy} (count : Ctxt.Var Γ (JasminTy.reg 64))
    (inits : HVector (fun t => Ctxt.Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ JasminTy.reg 64 :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts) {I : Isa} (hI : x86Isa.StepLe I)
    (hbsim : ExportTSim nArgs fn body I Site Q tE) (hksim : ExportTSim nArgs fn k I Site Q tE) :
    ExportTSim nArgs fn (NFProg.forLoop count inits body k) I Site Q tE := by
  intro d n r h hlen harg P pre post hfn hbody hpre fuel V m hat hag
  simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rk, hrk, rfl⟩ := h
  have hbody0 := hbody
  have hLab := exportR_labelsOK nArgs fn x86Data_guardsPlain body _ _ _ hb
  -- the count and the seeds
  obtain ⟨cn, hcn⟩ : ∃ cn, cn = operandName (resolveVar d nArgs argName (fun _ => none) count) :=
    ⟨_, rfl⟩
  have hcreg : resolveVar d nArgs argName (fun _ => none) count = .reg cn := by
    rw [hcn]
    exact resolveVar_isReg count
  obtain ⟨cnt, hcd⟩ : ∃ cnt : BitVec 64, count.lookup V = cnt := ⟨_, rfl⟩
  have hcnt : m.prog.base.reg.lvm cn = ⟨64, cnt⟩ := by
    have := hag.1 count
    rw [evalOperandN_resolveVar, ← hcn, hcd] at this
    exact getW_eq_some_iff.mp this
  have hcnk : ∀ k, d ≤ k → cn ≠ regName k := fun k hk => by
    rw [hcn]
    exact resolveVar_operandName_ne_regName count
      (hlen ▸ JasminLsemSimulation.varIndex_lt count) k hk
  obtain ⟨ops, hops⟩ : ∃ ops, ops = exprArgsHV d nArgs argName (fun _ => none) inits := ⟨_, rfl⟩
  have hopslen : ops.length = cs.length := by rw [hops, exprArgsHV_length]
  have hopsreg : ∀ o ∈ ops, ∀ k, d ≤ k → operandName o ≠ regName k := by
    rw [hops]
    exact fun o ho => (exprArgsHV_reg nArgs hlen inits o ho).2
  -- the layout of the body
  obtain ⟨cmp, hcmp⟩ : ∃ cmp, cmp = guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]) := ⟨_, rfl⟩
  obtain ⟨tpI, htpI⟩ : ∃ tpI, tpI = carriedPairs cs (carriedRegs (d + 1) cs.length) ops :=
    ⟨_, rfl⟩
  obtain ⟨tpB, htpB⟩ : ∃ tpB, tpB = carriedPairs cs (carriedRegs (d + 1) cs.length) b.res :=
    ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) tpI := ⟨_, rfl⟩
  obtain ⟨Sh, hSh⟩ : ∃ Sh, Sh = movImmI (regName d) 0
      :: typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = movImmI (regName (b.depth + 1)) 0
        :: arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tpB)
      ++ parMoves b.depth ((regPairs tpB).map Prod.fst)
        ((regPairs tpB).map fun p => .reg p.2) := ⟨_, rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs, Zs = labelI (n + 1) :: (Sh ++ (rk.code ++ post)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = T
      ++ (advanceOps (regName d) (loopCtr n) ++ cmp :: condI (.reg "NZ") n :: Zs) := ⟨_, rfl⟩
  have hF : forArrFrame d n cs ops (.reg cn) b.code b.res b.depth
      = S0 ++ (movI (loopCtr n) (.reg cn) :: cmp
          :: condI (.reg "Z") (n + 1) :: labelI n :: (b.code
          ++ (movImmI (regName (b.depth + 1)) 0
          :: (arrParMoves (regName (b.depth + 1)) (regName b.depth) b.depth (arrPairs tpB)
          ++ (parMoves b.depth ((regPairs tpB).map Prod.fst)
            ((regPairs tpB).map fun p => .reg p.2)
          ++ (advanceOps (regName d) (loopCtr n) ++ (cmp :: condI (.reg "NZ") n
          :: labelI (n + 1) :: Sh))))))) := by
    rw [hcmp, hS0, hSh, htpI, htpB]
    rfl
  rw [show ∀ c, (Exported.prepend c rk).code = c ++ rk.code from fun _ => rfl, hcreg, ← hops, hF]
    at hbody
  have hbodyH : P.body = pre ++ S0
      ++ (movI (loopCtr n) (.reg cn) :: cmp
        :: (condI (.reg "Z") (n + 1) :: labelI n :: (b.code ++ R))) := by
    rw [hbody, hR, hZs, hT]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨A, hAd⟩ : ∃ A, A = pre ++ S0
      ++ [movI (loopCtr n) (.reg cn), cmp, condI (.reg "Z") (n + 1)] :=
    ⟨_, rfl⟩
  have hbodyL : P.body = A ++ labelI n :: (b.code ++ R) := by
    rw [hbodyH, hAd]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hAlen : A.length = (pre ++ S0).length + 2 + 1 := by
    rw [hAd]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hAlabs : labelsOf A = labelsOf pre := by
    rw [hAd, hcmp, hS0, labelsOf_append, labelsOf_append, labelsOf_cons_movImmI,
      labelsOf_typedMoves, List.append_nil]
    exact List.append_nil _
  have hAlab : ∀ l, n ≤ l → findLabelMem l A = none := fun l hl => by
    rw [findLabelMem_eq_none_iff, hAlabs, ← findLabelMem_eq_none_iff]
    exact hpre l hl
  obtain ⟨X, hX⟩ : ∃ X, X = A ++ labelI n :: (b.code
      ++ (T ++ (advanceOps (regName d) (loopCtr n) ++ [cmp, condI (.reg "NZ") n]))) := ⟨_, rfl⟩
  have hbodyX : P.body = X ++ labelI (n + 1) :: (Sh ++ (rk.code ++ post)) := by
    rw [hbodyL, hR, hZs, hX]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hXlen : X.length = A.length + 1 + b.code.length + T.length + 3 + 1 := by
    rw [hX]
    simp only [List.length_append, List.length_cons, advanceOps, List.length_nil]
    omega
  have hXlabs : labelsOf X = labelsOf pre ++ n :: labelsOf b.code := by
    rw [hX, hcmp, hT]
    simp only [labelsOf_append, hAlabs, labelsOf_cons_labelI, labelsOf_cons_movImmI,
      labelsOf_arrParMoves, labelsOf_parMoves, labelsOf_advanceOps, List.nil_append]
    rw [show labelsOf [guardI (.Lopn [.reg (loopCtr n)] (withWidthTag 64 "CMP")
      [.reg (loopCtr n), .imm 0]), condI (.reg "NZ") n] = [] from rfl, List.append_nil]
  have hl1 : findLabelMem (n + 1) P.body = some X.length := by
    rw [hbodyX]
    refine findLabelMem_append_labelI (n + 1) X _ ?_
    rw [hXlabs, List.mem_append, List.mem_cons, not_or, not_or]
    refine ⟨(findLabelMem_eq_none_iff _ pre).mp (hpre _ (by omega)), fun he => ?_, fun hm => ?_⟩
    · have : (n + 1 : Nat) = n := he
      omega
    · have := hLab.range _ hm
      omega
  -- the head
  obtain ⟨k0, t0, hs0, hat0, hle0, hz0, hidx0, hctr0, hR0, hA0, hothR0, hothA0⟩ :=
    forArrHead_steps (d := d) (n := n) (ops := ops) (cn := cn) htpI pre _ m (cnt := cnt)
      (by rw [hbodyH, hcmp, hS0]) hat hopslen hopsreg hcnk hcnt
      (fun {w q} u => ⟨_, by rw [hops, exprArgsHV_getD]; exact hag.2 (hvToHom inits u)⟩)
  rw [← hS0] at hat0 hle0
  rw [List.length_append] at hle0
  have hfr0 : RegionFrame d n m.prog.base t0.prog.base :=
    RegionFrame.of_lvm_larr (fun r hr hl => hothR0 r hr (hl n le_rfl)) hothA0
  have hblkI : ∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
      t0.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w} u => by
    rw [getW_of_lvm_eq w (hR0 u), hops, exprArgsHV_getD,
      ← evalOperandN_resolveVar, lookup_lookupArgs]
    exact hag.1 (hvToHom inits u)
  have hblkAI : ∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
      t0.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
        = some (u.lookup (Expr.lookupArgs inits V)) := fun {w q} u => by
    rw [getArr_of_larr_eq w q (hA0 u), hops, exprArgsHV_getD, lookup_lookupArgs]
    exact hag.2 (hvToHom inits u)
  have hfetchZ : P.body[(pre ++ S0).length + 2]? = some (condI (.reg "Z") (n + 1)) :=
    fetch_of_body (xs := pre ++ S0
        ++ [movI (loopCtr n) (.reg cn), cmp])
      (by rw [hbodyH]; simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl)
      (by simp only [List.length_append, List.length_cons, List.length_nil])
  -- the trips, to the counter after the exit label
  have hexit : TSim I P (Site P) (Q P) (ofoldl (fun acc i => treeAt pureReader tE fuel body
        (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
        (List.range cnt.toNat) (Expr.lookupArgs inits V)) m fun accN mE =>
      atPc P (X.length + 1) mE
      ∧ RegionFrame d n m.prog.base mE.prog.base
      ∧ (∀ {w : Nat} (u : Ctxt.Var cs (.reg w)),
          mE.prog.base.reg.getW (regName (d + 1 + (cs.length - 1 - varIndex u))) w
            = some (u.lookup accN))
      ∧ (∀ {w q : Nat} (u : Ctxt.Var cs (.stackArr w q)),
          mE.prog.base.getArr (regName (d + 1 + (cs.length - 1 - varIndex u))) w q
            = some (u.lookup accN)) := by
    cases hN : cnt.toNat with
    | zero =>
        have hc0 : cnt = 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_taken (pol := true) rfl hat0 hfetchZ
          (by rw [hz0, hc0]; rfl) hl1
        exact TSim.steps (steps_of_stepLe hI (hs0.trans hs1)) (TSim.ret ⟨hat1,
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl,
          fun {w} u => hblkI u, fun {w q} u => hblkAI u⟩)
    | succ rem =>
        rw [List.range_eq_range']
        have hc0 : cnt ≠ 0#64 := by bv_omega
        obtain ⟨hs1, hat1⟩ := steps_cc_fall (pol := true) rfl hat0 hfetchZ
          (by rw [hz0]; simpa using hc0)
        rw [← hAlen] at hat1
        obtain ⟨hs2, hat2⟩ := steps_label I (kind := .internal) (l := n) (tag := .reg none)
          hat1 (fetch_of_body hbodyL rfl)
        have hfr2 : RegionFrame d n m.prog.base (next (next t0)).prog.base :=
          hfr0.trans (RegionFrame.of_cells rfl fun _ _ _ => rfl) le_rfl le_rfl
        refine TSim.steps ((steps_of_stepLe hI (hs0.trans hs1)).trans hs2)
          (TSim.post (fun accN m3 hp => ?_)
            (forArrLoop_tripsT nArgs fn body hI hbsim hb hlen harg hfn htpB hT hbodyL
              (by rw [hR, hcmp]) hAlab fuel V rem 0 (Expr.lookupArgs inits V)
              (next (next t0)) cnt hN hat2
              (StoreAgreesM.of_regionFrame hlen hag hfr2) hidx0 hctr0 (fun {w} u => hblkI u)
              (fun {w q} u => hblkAI u)))
        obtain ⟨hat3, hfr3, -, hblk3, hblkA3⟩ := hp
        rw [← hXlen] at hat3
        obtain ⟨hs4, hat4⟩ := steps_label I (kind := .internal) (l := n + 1)
          (tag := .reg none) hat3 (fetch_of_body hbodyX rfl)
        exact ⟨_, _, hs4, hat4,
          (hfr2.trans hfr3 le_rfl le_rfl).trans (RegionFrame.of_cells rfl fun _ _ _ => rfl)
            le_rfl le_rfl,
          fun {w} u => hblk3 u, fun {w q} u => hblkA3 u⟩
  have hnext := hLab.le
  have hlenEq : pre.length + (Exported.prepend (forArrFrame d n cs
      (exprArgsHV d nArgs argName (fun _ => none) inits)
      (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth) rk).code.length
      = (X ++ labelI (n + 1) :: Sh).length + rk.code.length := by
    have h1 := congrArg List.length hbody0
    rw [hbodyX] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    omega
  have htree : treeAt pureReader tE fuel (NFProg.forLoop count inits body k) V
      = obind (ofoldl (fun acc i => treeAt pureReader tE fuel body
          (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)))
          (List.range cnt.toNat) (Expr.lookupArgs inits V))
        fun acc => treeAt pureReader tE fuel k (hvAppend acc V) := by
    rw [← hcd]
    rfl
  rw [htree]
  refine TSim.obind (TSim.mono (fun accN mE hp => ?_) hexit)
  obtain ⟨hatE, hfrE, hblkE, hblkAE⟩ := hp
  -- the shift of the carried block
  obtain ⟨mS, hsS, hatS, hRS, hAS, hoRS, hoAS⟩ := forArrShift_steps (d := d) (cs := cs)
    (X ++ [labelI (n + 1)]) (rk.code ++ post) mE
    (by rw [hbodyX, hSh]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (by rw [List.length_append, List.length_singleton]; exact hatE)
    (fun {w q} u => ⟨_, hblkAE u⟩)
  have hfrS : RegionFrame d n m.prog.base mS.prog.base :=
    hfrE.trans (RegionFrame.of_lvm_larr (fun r hr _ => hoRS r hr) hoAS) le_rfl le_rfl
  have hagS : StoreAgreesM nArgs (d + cs.length) mS.prog.base (hvAppend accN V) :=
    storeAgreesM_append_arr harg (StoreAgreesM.of_regionFrame hlen hag hfrS)
      (fun {w} u => by
        rw [getW_of_lvm_eq w (hRS u)]
        exact hblkE u)
      (fun {w q} u => by
        rw [getArr_of_larr_eq w q (hAS u)]
        exact hblkAE u)
  -- the continuation
  have hK := hksim (d + cs.length) b.next rk hrk
    (by rw [List.length_append, hlen]; omega) (by omega) P
    (X ++ labelI (n + 1) :: Sh) post hfn
    (by rw [hbodyX]; simp only [List.append_assoc, List.cons_append])
    (fun l hl => by
      rw [findLabelMem_eq_none_iff, labelsOf_append, hXlabs, labelsOf_cons_labelI, hSh,
        labelsOf_cons_movImmI, labelsOf_typedMoves]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨(findLabelMem_eq_none_iff l pre).mp (hpre l (by omega)), fun he => ?_,
        fun hm => ?_⟩, fun he => ?_⟩
      · have : (l : Nat) = n := he
        omega
      · have := hLab.range _ hm
        omega
      · have : (l : Nat) = n + 1 := he
        omega)
    fuel _ mS
    (by
      rw [show (X ++ labelI (n + 1) :: Sh).length = (X ++ [labelI (n + 1)]).length + 1
          + (typedMoves (regName d) (regName (d + 1 + cs.length)) (shiftPairs d cs)).length by
        rw [hSh]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega]
      exact hatS)
    hagS
  refine TSim.steps (steps_of_stepLe hI hsS) (TSim.mono (fun v m' hp => ?_) hK)
  obtain ⟨hatK, hresK, hfrK⟩ := hp
  exact ⟨by rw [hlenEq]; exact hatK, hresK, hfrS.trans hfrK (by omega) (by omega)⟩

end ForArrFrame

/-! ## Calls as events -/

section Events

/-- The state `u'` after a call of the result `v`, word or word array, written to the
    destination `dst` from the state `u`. -/
def CallOut (dst : String) :
    (rs : List JasminTy) → Ctxt.Valuation (d := jasminDialect) rs → LstateMF → LstateMF → Prop
  | [.reg 64], v, u, u' => u' = retWord dst (resWord v) u
  | [.stackArr 64 _], v, u, u' => u' = LprogIsa.retArr dst (resArr v) u
  | _, _, _, _ => False

/-- **A state at a call of the event `e`** in `P`: at the shadow instruction of a call of the
    symbol of `e` on as many operands as arguments, which read as the words of the arguments of
    `e`. -/
def CallSite (P : LprogM) (e : NFCall jasminDialect) (u : LstateMF) : Prop :=
  ∃ dst srcs tag k, atPc P k u ∧ P.body[k]? = some (callShadow dst e.name srcs, tag)
    ∧ srcs.length = e.argTys.length
    ∧ LprogIsa.argsRead (arrArgsOf e.argTys) u.prog.base 0 srcs = some (wordsOf e.args)

/-- **The state after the call of the event `e`** from the state `u` of `P` at the answer `a`:
    `a` is a value written to the destination of the shadow instruction at `u`. -/
def CallRet (P : LprogM) (e : NFCall jasminDialect) (u : LstateMF)
    (a : Option (Ctxt.Valuation (d := jasminDialect) e.resTys)) (u' : LstateMF) : Prop :=
  ∃ dst srcs tag k res, atPc P k u ∧ P.body[k]? = some (callShadow dst e.name srcs, tag)
    ∧ a = some res ∧ CallOut dst e.resTys res u u'

/-- **The tree call environment of the call events performs the calls**, at the call sites
    `CallSite` and the states after the calls `CallRet`, on every instruction set. -/
theorem tCallsSim_eventEnv (I : Isa) :
    TCallsSim (E := nfCallSig jasminDialect) I CallSite CallRet eventEnv := by
  refine ⟨?_, ?_⟩
  · intro P f as _ a dst srcs tag k s hat hf hlen hargs
    refine ⟨0, s, Steps.refl I P s, ⟨dst, srcs, tag, k, hat, hf, hlen, hargs⟩, ?_⟩
    rintro a' u' ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    obtain rfl : k' = k := hat'.2.symm.trans hat.2
    rw [hf] at hf'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf'
    obtain ⟨⟨rfl, -⟩, -⟩ := hf'
    exact TSim.ret hout
  · intro P f as nr _ a dst srcs tag k s hat hf hlen hargs
    refine ⟨0, s, Steps.refl I P s, ⟨dst, srcs, tag, k, hat, hf, hlen, hargs⟩, ?_⟩
    rintro a' u' ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    obtain rfl : k' = k := hat'.2.symm.trans hat.2
    rw [hf] at hf'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf'
    obtain ⟨⟨rfl, -⟩, -⟩ := hf'
    exact TSim.ret hout

end Events

/-! ## The simulation theorem for call trees -/

/-- **The simulation theorem of the region export for call trees.** On an instruction set that
    has the steps of the x86 flag machine, at a tree call environment that performs the calls of
    words and word arrays (`TCallsSim`), every program of `RegionExportable` satisfies the
    simulation statement for call trees. -/
theorem exportT_sim {E : EventSig} (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {p : NFProg jasminDialect Γ ts} {I : Isa}
    {Site : LprogM → E.Event → LstateMF → Prop}
    {Q : LprogM → (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop}
    {tE : TreeCallEnv E jasminDialect} (hI : x86Isa.StepLe I) (hc : TCallsSim I Site Q tE)
    (hp : RegionExportable p) : ExportTSim nArgs fn p I Site Q tE := by
  induction p with
  | ret vs => exact exportTSim_ret nArgs fn vs
  | var e k ih => exact exportTSim_var nArgs fn e k hp.1 hI (ih hp.2)
  | forLoop count inits body k ihb ihk =>
      exact exportTSim_for nArgs fn count inits body k hI (ihb hp.1) (ihk hp.2)
  | ifThenElse cond thn els k iht ihe ihk =>
      exact exportTSim_if nArgs fn cond thn els k hI (iht hp.1) (ihe hp.2.1) (ihk hp.2.2)
  | whileLoop inits body k ihb ihk =>
      exact exportTSim_while nArgs fn inits body k hp.1 hI (ihb hp.2.1) (ihk hp.2.2)
  | call f args k ih =>
      obtain ⟨has, rfl | ⟨nr, rfl⟩⟩ := wordSig_iff.mp hp.1
      · exact exportTSim_call nArgs fn f args k has hc (ih hp.2)
      · exact exportTSim_callArr nArgs fn f args k has hc (ih hp.2)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport
