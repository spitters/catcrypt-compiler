/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.IsaTextWP
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCall
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCallDemo
public import RefinementWP.Step

/-!
# Cut points and calls of texts, and procedure specifications as registered refinements

The weakest precondition of the text of a body follows from invariants at cut points with a
decreasing measure, and at a call it is the weakest precondition after the return step.

A bounded segment of a program, the run of at most a given number of steps to a given counter,
is a monotone predicate transformer, so segments are sequenced in a monad to which `wrp_step`
applies. A procedure with a specification `IsaCall.ProcSpec` is packaged as an `IsaCall.Proc`,
whose call at a counter is such a segment, registered as an instance of
`RefinementWP.RefinesCall` under the condition `Proc.Fits` at the call site.

## Main definitions

* `IsaCall.reachPT`: a bounded segment as a monotone predicate transformer.
* `IsaCall.Proc`, `Proc.callPT`, `Proc.Fits`: a specified procedure, its call at a counter, and
  the condition under which a call site implements an abstract update.

## Main results

* `refines_reachPT_iff`: refinement by a segment is a forward simulation by its steps.
* `procSpec_call`: the registration of a procedure specification.
* `wp_reachPT_bind`, `corresIsa_of_refines`: a refinement by a sequence of segments gives
  `CorresIsa` at the sum of their bounds.
* `Isa.Text.wp_whole_of_cutPoint`, `Isa.Text.wp_call`: the cut-point rule and the call rule for
  the weakest precondition of a text.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall

open Std.WP Lean.Order RefinementWP
open IsaCfg (atPc Steps)
open VIR.JasminLprogExport (LLabel)
open VIR.JasminLsemMem (MemTag)
open VIR.JasminLsemMemLoop (LprogM findLabelMem)
open VIR.JasminLsemMemFlagGuard (LstateMF)
open VIR.LprogIsa (Isa)

/-- The segment of `P` of at most `B` steps to the counter `k`, as a monotone predicate
    transformer. -/
def reachPT (I : Isa) (P : LprogM) (B k : Nat) : MonoPT LstateMF Unit where
  trans Q s := ∃ n u, n ≤ B ∧ Steps I P n s u ∧ atPc P k u ∧ Q () u
  mono _ _ h _ := fun ⟨n, u, hn, hs, hat, hq⟩ => ⟨n, u, hn, hs, hat, h () u hq⟩

/-- A procedure of `P` with its specification, the index of its label and its return. -/
structure Proc (I : Isa) (P : LprogM) (A : Type) where
  /-- The label of the procedure. -/
  lbl : LLabel
  /-- The index of the declaration of the label. -/
  declIdx : Nat
  /-- The counter of the return. -/
  kret : Nat
  /-- The tag of the return. -/
  tag : MemTag
  /-- The relation of the procedure. -/
  SR : LstateMF → A → Prop
  /-- The precondition. -/
  Pre : A → Prop
  /-- The abstract function. -/
  f : A → A
  /-- The frame. -/
  Frame : LstateMF → LstateMF → Prop
  /-- The bound on the steps of the procedure. -/
  bound : Nat
  /-- The specification. -/
  spec : ProcSpec I.withCalls P lbl kret SR Pre f Frame bound
  /-- The label is declared at `declIdx`. -/
  decl : findLabelMem lbl P.body = some declIdx
  /-- The instruction at `kret` is a return. -/
  ret : P.body[kret]? = some (.Lret, tag)

section Rules

variable {I : Isa} {P : LprogM} {A C : Type}

/-- The call of a procedure at the counter `k`: the segment to the counter `k + 1` within the
    bound of the procedure, the call step and the return step. -/
def Proc.callPT (p : Proc I P A) (k : Nat) : MonoPT LstateMF Unit :=
  reachPT I.withCalls P (p.bound + 2) (k + 1)

/-- The call site at `k` implements the update `g` of the caller by the procedure `p`: it holds
    a call of `p`, the caller relation gives the relation and the precondition of `p` after the
    call step, and the exit relation and the frame of `p` give the caller relation after the
    return step. -/
structure Proc.Fits (p : Proc I P A) (k : Nat) (SRc : LstateMF → C → Prop)
    (g : C → Option (Unit × C)) : Prop where
  /-- The instruction at `k` is a call of the procedure. -/
  instr : ∃ tag, P.body[k]? = some (.Lcall none (P.lfn, p.lbl), tag)
  /-- The return address is a word. -/
  lt : k + 1 < 2 ^ 64
  /-- The entry and the exit of the call. -/
  site : ∀ m c c', SRc m c → g c = some c' → atPc P k m ∧ ∃ v a,
    m.prog.base.reg.getW I.sp 64 = some v ∧ p.SR (callEntry I.sp v p.declIdx m) a ∧ p.Pre a ∧
      ∀ m₂, p.SR m₂ (p.f a) → p.Frame (callEntry I.sp v p.declIdx m) m₂ →
        atPc P (k + 1) (retState I.sp v (k + 1) m₂) → SRc (retState I.sp v (k + 1) m₂) c'.2

/-- Refinement of a partial update by a segment is the forward simulation by its steps. -/
theorem refines_reachPT_iff {B k : Nat} {SR : LstateMF → C → Prop}
    {g : C → Option (Unit × C)} :
    Refines top (Concretization.ofStateRel SR) (fun _ : Unit => bot) (reachPT I P B k) (optD g)
        (fun _ _ _ => True) ↔
      ∀ s c c', SR s c → g c = some c' →
        ∃ n u, n ≤ B ∧ Steps I P n s u ∧ atPc P k u ∧ SR u c'.2 := by
  refine (refines_optD_iff (Rv := fun _ _ => True)
    (T := fun s _ u => ∃ n, n ≤ B ∧ Steps I P n s u ∧ atPc P k u) (reachPT I P B k)
    fun Q s => ?_).trans ?_
  · constructor
    · rintro ⟨n, u, hn, hs, hat, hq⟩
      exact ⟨(), u, ⟨n, hn, hs, hat⟩, hq⟩
    · rintro ⟨_, u, ⟨n, hn, hs, hat⟩, hq⟩
      exact Exists.intro n ⟨u, hn, hs, hat, hq⟩
  · grind

/-- A procedure specification registers each call of the procedure as a refinement of every
    update of the caller that the call site implements. -/
instance procSpec_call (p : Proc I P A) (k : Nat) (SRc : LstateMF → C → Prop)
    (g : C → Option (Unit × C)) :
    RefinesCall (p.callPT k) (optD g) (Concretization.ofStateRel SRc) (fun _ : Unit => bot)
      (p.Fits k SRc g) (fun _ _ _ => True) where
  refines h := refines_reachPT_iff.2 fun m c c' hSR hg => by
    obtain ⟨tag, hi⟩ := h.instr
    obtain ⟨hat, v, a, hsp, hentry, hPre, hexit⟩ := h.site m c c' hSR hg
    obtain ⟨n, m₂, hn, hs, hat', hSR₂, hF⟩ :=
      steps_call I p.spec p.ret hat hi p.decl hsp h.lt hentry hPre
    exact ⟨n, _, hn, hs, hat', hexit m₂ hSR₂ hF hat'⟩

/-- A segment followed by a program below a second segment is below the segment with the sum
    of the bounds. -/
theorem wp_reachPT_bind {B B' k k' : Nat} {d : Unit → MonoPT LstateMF Unit}
    (h : ∀ Q s, wp (d ()) Q () s → wp (reachPT I P B' k') Q () s)
    (Q : Unit → LstateMF → Prop) (s : LstateMF) :
    wp (reachPT I P B k >>= d) Q () s → wp (reachPT I P (B + B') k') Q () s := by
  rintro ⟨n, u, hn, hs, _, hd⟩
  obtain ⟨n', u', hn', hs', hat, hq⟩ := h Q u hd
  exact ⟨n + n', u', by omega, hs.trans hs', hat, hq⟩

/-- A refinement of an abstract program that computes `fa` by a program below a segment that
    ends past the body gives the correspondence at the bound of the segment. -/
theorem corresIsa_of_refines {B k : Nat} {SR : LstateMF → C → Prop} {Pre : C → Prop}
    {fa : C → C} {c : MonoPT LstateMF Unit} {a : MonoPT C Unit} (hk : P.body.length ≤ k)
    (h : Refines top (Concretization.ofStateRel SR) (fun _ : Unit => bot) c a
      (fun _ _ _ => True))
    (hc : ∀ Q s, wp c Q () s → wp (reachPT I P B k) Q () s)
    (ha : ∀ x, Pre x → wp a (fun _ y => y = fa x) () x) :
    CorresIsa I P SR Pre fa B := by
  intro m x hSR hPre
  obtain ⟨n, u, hn, hs, hat, hq⟩ :=
    hc _ m (refines_top_iff.1 h (fun _ y => y = fa x) () m ⟨x, hSR, ha x hPre⟩)
  obtain ⟨_, _, y, hy, rfl⟩ := (Concretization.post_apply ..).1 hq
  refine ⟨u, ?_, hy⟩
  have hrun := IsaCfg.lsemFuelMemF_of_steps I P hs (IsaCfg.halted_of_atPc hat hk) (B - n)
  rwa [Nat.add_sub_cancel' hn] at hrun

end Rules

/-! ## The caller of `Demos.KrakenCallDemo` by `wrp_steps` -/

namespace CallExample

open Demos.KrakenCallDemo
open VIR.JasminLsemWidthN VIR.JasminLsemMem
open X86Backend.X86Isa (x86Isa)

/-- The doubling procedure of `callProg` with its specification. -/
def dblProc (fn : String) : Proc x86Isa (callProg fn) (BitVec 64) where
  lbl := 1
  declIdx := 3
  kret := 5
  tag := .reg none
  SR := dblSR
  Pre _ := True
  f a := a + a
  Frame := dblFrame
  bound := 1
  spec := dbl_procSpec fn
  decl := rfl
  ret := rfl

/-- The update of the caller by the call at `k`. -/
def callUpd (k : Nat) (a : BitVec 64 × BitVec 64 × Nat) :
    Option (Unit × BitVec 64 × BitVec 64 × Nat) :=
  if a.2.2 = k then some ((), a.1 + a.1, a.2.1, k + 1) else none

/-- The update of the caller by its jump to the end. -/
def endUpd (a : BitVec 64 × BitVec 64 × Nat) : Option (Unit × BitVec 64 × BitVec 64 × Nat) :=
  if a.2.2 = 2 then some ((), a.1, a.2.1, 7) else none

/-- A call site of `callProg` implements `callUpd`. -/
theorem dblProc_fits (fn : String) (sp : BitVec 64) {k : Nat}
    (hi : (callProg fn).body[k]? = some (.Lcall none ((callProg fn).lfn, 1), .reg none))
    (hk : k + 1 < 2 ^ 64) : (dblProc fn).Fits k (callSR fn sp) (callUpd k) := by
  refine ⟨⟨_, hi⟩, hk, ?_⟩
  rintro m ⟨x, y, pc⟩ c' ⟨hfn, hpc, hx, hy, hsp⟩ hg
  obtain ⟨rfl, rfl⟩ : pc = k ∧ c' = ((), x + x, y, k + 1) := by grind [callUpd]
  refine ⟨⟨hfn, hpc⟩, sp, x, IsaCfg.getW_of_lvm _ "RSP" sp hsp, ?_, trivial,
    fun m₂ hx₂ hF hat => ?_⟩
  · exact (callEntry_lvm_of_ne _ _ _ _ (by decide)).trans hx
  · refine ⟨hat.1, hat.2, ?_, ?_, retState_lvm_sp _ _ _ _⟩
    · exact (retState_lvm_of_ne _ _ _ _ (by decide)).trans hx₂
    · exact (retState_lvm_of_ne _ _ _ _ (by decide)).trans ((hF "y" (by decide)).trans
        ((callEntry_lvm_of_ne _ _ _ _ (by decide)).trans hy))

/-- The statement of `Demos.KrakenCallDemo.call_corresIsa`, proved with each call as one
    registered refinement. -/
example (fn : String) (sp : BitVec 64) :
    CorresIsa x86Isa.withCalls (callProg fn) (callSR fn sp) (fun a => a.2.2 = 0)
      (fun a => (a.1 + a.1 + (a.1 + a.1), a.2.1, 7)) (7 * (0 + 1)) := by
  refine corresIsa_of_refines (k := 7)
    (c := (dblProc fn).callPT 0 >>= fun _ => (dblProc fn).callPT 1 >>= fun _ =>
      reachPT x86Isa.withCalls (callProg fn) 1 7)
    (a := optD (callUpd 0) >>= fun _ => optD (callUpd 1) >>= fun _ => optD endUpd)
    (Nat.le_refl _) ?_
    (wp_reachPT_bind (B := 3) (B' := 3 + 1) (wp_reachPT_bind (B := 3) fun _ _ h => h)) ?_
  · wrp_steps
    · exact dblProc_fits fn sp rfl (by norm_num)
    · exact dblProc_fits fn sp rfl (by norm_num)
    · refine refines_reachPT_iff.2 ?_
      rintro m ⟨x, y, pc⟩ c' ⟨hfn, hpc, hregs⟩ hg
      obtain ⟨rfl, rfl⟩ : pc = 2 ∧ c' = ((), x, y, 7) := by grind [endUpd]
      exact ⟨1, _, Nat.le_refl _, (IsaCfg.steps_goto _ (q := 6) ⟨hfn, hpc⟩ rfl rfl).1,
        ⟨hfn, rfl⟩, hfn, rfl, hregs⟩
  · rintro ⟨x, y, pc⟩ rfl
    exact rfl

end CallExample

end CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall

/-! ## Cut points and calls of texts -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa.Text

open Std.WP Lean.Order
open JasminLprogExport (LLabel LabelKind)
open JasminLsemMem (MemTag)
open JasminLsemMemLoop (LprogM findLabelMem singletonProgM)
open JasminLsemMemFlagGuard (LstateMF)
open Ascent (CorresIsa)
open Ascent.IsaCfg (atPc Steps)
open Ascent.IsaCall (ProcSpec callEntry retState)

/-- Cut points: when from every invariant a segment of at most `B` steps reaches an exit of
    the body satisfying its postcondition or an invariant of smaller measure, every state
    satisfying an invariant satisfies the weakest precondition of the text of the body. -/
theorem wp_whole_of_cutPoint {L : Type} (I : Isa) (P : LprogM) (Inv : L → LstateMF → Prop)
    (μ : L → LstateMF → Nat) (B : Nat) {Q : Unit → LstateMF → Prop}
    {E : Nat → LstateMF → Prop}
    (hseg : ∀ l s, Inv l s → ∃ n s', n ≤ B ∧ Steps I P n s s' ∧
      ((P.body.length ≤ s'.prog.base.lpc ∧ (whole I P).exitPost Q E s') ∨
        ∃ l', Inv l' s' ∧ μ l' s' < μ l s))
    {l : L} {s : LstateMF} (hs : Inv l s) : wp (whole I P) Q E s := by
  let Exit (m : LstateMF) : Prop :=
    P.body.length ≤ m.prog.base.lpc ∧ (whole I P).exitPost Q E m
  have h : CorresIsa I P (fun m b => cond b (Exit m) (m = s)) (· = false) (fun _ => true)
      (B * (μ l s + 1)) := by
    refine Ascent.IsaCfg.corresIsa_of_cutPoint I P _ _ _ (fun _ _ => True)
      (fun _ _ _ _ _ => trivial) (fun l m _ => Inv l m) (fun (_ : Unit) m _ => Exit m)
      (fun l m _ => μ l m) B _ ?_ ?_ (fun _ _ _ h => halted_of_length_le h.1)
      (fun _ _ _ _ _ _ h => h)
    · rintro m b hm rfl
      obtain rfl : m = s := hm
      exact ⟨l, hs, Nat.le_refl _⟩
    · intro l m b hm
      obtain ⟨n, m', hn, hst, hd⟩ := hseg l m hm
      exact ⟨n, m', b, hn, hst, trivial, hd.imp_left fun he => ⟨(), he⟩⟩
  obtain ⟨u, hrun, hu⟩ := h s false rfl rfl
  exact runs_whole_iff.2 ⟨_, u, hrun, hu⟩

/-- Calls: in a text of the instruction set with calls that contains every counter of the
    body, the weakest precondition at a call of a procedure with a specification is the
    weakest precondition at the counter after the call in the return state of a specified
    exit state of the procedure. -/
theorem wp_call {A : Type} (I : Isa) {P : LprogM} {inside : Nat → Prop} {fall : Nat}
    (hcov : ∀ j, j < P.body.length → inside j) {k q kret : Nat} {l : LLabel}
    {tag tagr : MemTag} {v : BitVec 64} {m : LstateMF} {a : A}
    {SR : LstateMF → A → Prop} {Pre : A → Prop} {f : A → A}
    {Frame : LstateMF → LstateMF → Prop} {B : Nat}
    (hspec : ProcSpec I.withCalls P l kret SR Pre f Frame B)
    (hret : P.body[kret]? = some (.Lret, tagr)) (hat : atPc P k m)
    (hi : P.body[k]? = some (.Lcall none (P.lfn, l), tag))
    (hl : findLabelMem l P.body = some q)
    (hsp : m.prog.base.reg.getW I.sp 64 = some v) (hk : k + 1 < 2 ^ 64)
    (hSR : SR (callEntry I.sp v q m) a) (hPre : Pre a) :
    ∃ m₂, SR m₂ (f a) ∧ Frame (callEntry I.sp v q m) m₂ ∧
      atPc P (k + 1) (retState I.sp v (k + 1) m₂) ∧
      ∀ Q E, wp (⟨I.withCalls, P, inside, fall⟩ : Text) Q E m ↔
        wp (⟨I.withCalls, P, inside, fall⟩ : Text) Q E (retState I.sp v (k + 1) m₂) := by
  obtain ⟨n, m₂, _, hs, hat', hSR₂, hF⟩ :=
    Ascent.IsaCall.steps_call I hspec hret hat hi hl hsp hk hSR hPre
  exact ⟨m₂, hSR₂, hF, hat', fun Q E =>
    Runs.steps_iff (t := ⟨I.withCalls, P, inside, fall⟩) hcov hs⟩

/-- A body of one label satisfies the hypotheses of the cut-point rule. -/
example (I : Isa) (fn : String) (k : LabelKind) (l : LLabel) (tag : MemTag) (s : LstateMF)
    (hs : atPc (singletonProgM fn [(.Llabel k l, tag)]) 0 s) :
    wp (whole I (singletonProgM fn [(.Llabel k l, tag)]))
      (fun _ u => atPc (singletonProgM fn [(.Llabel k l, tag)]) 1 u) bot s := by
  refine wp_whole_of_cutPoint I _ (fun (_ : Unit) => atPc _ 0) (fun _ _ => 0) 1
    (fun _ u hu => ?_) (l := ()) hs
  obtain ⟨h₁, hat⟩ := Ascent.IsaCfg.steps_label I hu rfl
  refine ⟨1, _, Nat.le_refl _, h₁, .inl ⟨hat.2.ge, ?_⟩⟩
  simp only [exitPost, whole, singletonProgM, List.length_singleton, hat.2, Nat.zero_add,
    ite_true]
  exact hat

open Ascent.Demos.KrakenCallDemo X86Backend.X86Isa in
/-- The first call of `Demos.KrakenCallDemo.callProg` satisfies the hypotheses of `wp_call`. -/
example (fn : String) (m : LstateMF) (x y sp : BitVec 64) (h : callSR fn sp m (x, y, 0)) :
    ∃ m₂, dblSR m₂ (x + x) ∧ ∀ Q E,
      wp (whole x86Isa.withCalls (callProg fn)) Q E m ↔
        wp (whole x86Isa.withCalls (callProg fn)) Q E (retState "RSP" sp 1 m₂) := by
  obtain ⟨hfn, hpc, hx, -, hsp⟩ := h
  obtain ⟨m₂, hx₂, -, -, hwp⟩ := wp_call x86Isa (inside := (· < (callProg fn).body.length))
    (fall := (callProg fn).body.length) (fun _ h => h) (k := 0) (q := 3) (a := x)
    (dbl_procSpec fn) rfl ⟨hfn, hpc⟩ rfl rfl (Ascent.IsaCfg.getW_of_lvm _ "RSP" sp hsp)
    (by norm_num) ((Ascent.IsaCall.callEntry_lvm_of_ne _ _ _ _ (by decide)).trans hx) trivial
  exact ⟨m₂, hx₂, hwp⟩

open Ascent.Demos.KrakenCallDemo X86Backend.X86Isa in
/-- The caller of `Demos.KrakenCallDemo` satisfies the hypothesis of `corresIsaRun_iff_triple`,
    so its correspondence is a family of triples of the text of its body. -/
example (fn : String) (sp : BitVec 64) (a : BitVec 64 × BitVec 64 × Nat) (ha : a.2.2 = 0) :
    Triple (whole x86Isa.withCalls (callProg fn)) (callSR fn sp · a)
      (fun _ m => callSR fn sp m (a.1 + a.1 + (a.1 + a.1), a.2.1, 7)) bot :=
  (corresIsaRun_iff_triple (Pre := fun a => a.2.2 = 0)
    (fa := fun a => (a.1 + a.1 + (a.1 + a.1), a.2.1, 7)) fun _ _ _ h => h.2.1).1
    (Ascent.corresIsaRun_of_corresIsa (call_corresIsa fn sp)) a ha

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa.Text

end
