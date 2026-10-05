/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.BignumToJ
public import CatCrypt.Crypto.Jasmin.JazzToInstrR

@[expose] public section

set_option autoImplicit false

/-!
# Counted loops and calls in the bignum-to-`JInstr 64` translation

`BignumToJ.toJBlock` translates a straight-line body. A body that `bignumExecFuel` runs may
also contain counted loops (`Cfor`) and calls (`Ccall`). This module expands such a body to
a straight-line one with the same `bignumExecFuel` result, so that `toJBlock` and its
simulation apply to the expansion.

A `Cfor` is unrolled by `unrollFor`, which is how `bignumExecFuel` itself runs it. A `Ccall`
is inlined: the callee starts from a register file holding its arguments and `0` elsewhere,
and returns only its memory and its results, so its body runs under a renaming of every
variable `y` to the scratch name `scr p y = p ++ y`. The inlined code writes the arguments to
the scratch registers of the parameters, runs the renamed straight-line callee body, binds
the results, and sets the scratch registers the callee writes to `0`. Under the invariant
`Inv p` (every scratch register holds `0`) the inlined code computes the state the call
returns, and re-establishes the invariant. A callee whose body contains a call is not
inlined (`callCode` is `none` on it).

## Main definitions

* `flatI`, `flatB`: the expansion of a body with counted loops and no calls.
* `scr`, `isScr`, `pull`, `renP`, `renL`, `renI`: scratch names and renaming.
* `Inv`: the scratch registers hold `0`.
* `callCode`: the inlined code of one call.
* `inlI`, `inlB`: the expansion of a body with counted loops and calls.

## Main results

* `flatB_sound`: a body with counted loops runs as `flatB` of it.
* `execInstr_ren`, `bignumExec_ren`: renaming a translatable instruction or body.
* `bignumExec_regs_frame`: a register outside the destinations of a body's translation keeps
  its value.
* `callCode_sound`: the inlined code of a call computes the state the call returns.
* `inlB_sound`: a body with calls and counted loops runs as `inlB` of it.
* `flatB_runBlockA_sim`, `inlB_runBlockA_sim`: the simulation by `runBlockA`.
* `Add4.runBlockA_sim`, `Add4.caller_runBlockA_sim`: the `bignum_add_4` port, and a caller of
  it with a loop and calls.

@ascent-fixture theorems: runBlockA_sim, caller_runBlockA_sim
-/

namespace CatCrypt.Crypto.Jasmin.BignumToJCalls

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.BignumToJ
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## Sequencing -/

theorem bignumExec_append_eq (b1 b2 : List InstrR) (s : BignumState) :
    bignumExec (b1 ++ b2) s = (bignumExec b1 s).bind (bignumExec b2) := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, bignumExec]
    split
    · exact ih _
    · rfl

/-! ## Counted loops -/

mutual
/-- The straight-line expansion of one instruction: a `Cfor` unrolled by `unrollFor`, a
    `Cassgn` or `Copn` kept, every other shape `none`. -/
def flatI : InstrR → Option (List InstrR)
  | .Cfor v r b => (flatB b).map (unrollFor v r)
  | .Cassgn lv tg ty e => some [.Cassgn lv tg ty e]
  | .Copn lvs tg op es => some [.Copn lvs tg op es]
  | _ => none

/-- The straight-line expansion of a body. -/
def flatB : List InstrR → Option (List InstrR)
  | [] => some []
  | i :: is => do
      let a ← flatI i
      let b ← flatB is
      some (a ++ b)
end

theorem flatB_append (xs ys : List InstrR) :
    flatB (xs ++ ys) = (flatB xs).bind fun a => (flatB ys).map fun b => a ++ b := by
  induction xs with
  | nil =>
    simp only [List.nil_append, flatB, Option.bind_some]
    cases flatB ys <;> rfl
  | cons i is ih =>
    simp only [List.cons_append, flatB, ih]
    cases flatI i <;> cases flatB is <;> cases flatB ys <;> simp

theorem flatB_flatMap (L : List Nat) (c : Nat → InstrR) (b fb : List InstrR)
    (hc : ∀ k, flatI (c k) = some [c k]) (hb : flatB b = some fb) :
    flatB (L.flatMap fun k => c k :: b) = some (L.flatMap fun k => c k :: fb) := by
  induction L with
  | nil => rfl
  | cons k L ih =>
    simp only [List.flatMap_cons]
    rw [flatB_append, ih]
    simp [flatB, hc k, hb]

theorem flatB_unrollFor (v : VarI) (r : Range) (b fb : List InstrR) (hb : flatB b = some fb) :
    flatB (unrollFor v r b) = some (unrollFor v r fb) := by
  unfold unrollFor
  split
  · exact flatB_flatMap _ _ _ _ (fun _ => rfl) hb
  · exact flatB_flatMap _ _ _ _ (fun _ => rfl) hb

/-- A body with counted loops runs as its straight-line expansion. -/
theorem flatB_sound (reg : BignumRegistry) :
    ∀ (fuel : Nat) (body fb : List InstrR) (s s' : BignumState), flatB body = some fb →
      bignumExecFuel reg fuel body s = some s' → bignumExec fb s = some s' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ he; simp [bignumExecFuel] at he
  | succ f ihf =>
    intro body
    induction body with
    | nil =>
      intro fb s s' h he
      simp only [flatB, Option.some.injEq] at h
      simp only [bignumExecFuel, Option.some.injEq] at he
      subst h he
      rfl
    | cons i is ih =>
      intro fb s s' h he
      simp only [flatB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      cases i with
      | Cassgn lv tg ty e =>
        simp only [flatI, Option.some.injEq] at ha
        subst ha
        simp only [bignumExecFuel] at he
        rw [List.singleton_append]
        simp only [bignumExec]
        split at he
        · next s1 h1 => exact ih b s1 s' hb he
        · cases he
      | Copn lvs tg op es =>
        simp only [flatI, Option.some.injEq] at ha
        subst ha
        simp only [bignumExecFuel] at he
        rw [List.singleton_append]
        simp only [bignumExec]
        split at he
        · next s1 h1 => exact ih b s1 s' hb he
        · cases he
      | Cfor v r body =>
        simp only [flatI, Option.map_eq_some_iff] at ha
        obtain ⟨fbody, hfb, rfl⟩ := ha
        simp only [bignumExecFuel] at he
        have hflat : flatB (unrollFor v r body ++ is) = some (unrollFor v r fbody ++ b) := by
          rw [flatB_append, flatB_unrollFor v r body fbody hfb, hb]
          rfl
        exact ihf _ _ s s' hflat he
      | Cif _ _ _ => simp [flatI] at ha
      | Cwhile _ _ _ => simp [flatI] at ha
      | Ccall _ _ _ _ => simp [flatI] at ha

/-! ## Scratch names and renaming -/

/-- The scratch name of `y` under the prefix `p`. -/
def scr (p y : String) : String := p ++ y

/-- `x` begins with the prefix `p`. -/
def isScr (p x : String) : Bool := p.toList.isPrefixOf x.toList

theorem isScr_scr (p y : String) : isScr p (scr p y) = true := by
  simp [isScr, scr, String.toList_append, List.isPrefixOf_iff_prefix]

theorem ne_scr_of_isScr {p x : String} (h : isScr p x = false) (y : String) : x ≠ scr p y := by
  rintro rfl
  rw [isScr_scr] at h
  cases h

theorem scr_inj {p a b : String} : scr p a = scr p b ↔ a = b := by
  simp [scr]

/-- The state whose register `y` is the register `scr p y` of `t`, with the memory of `t`. -/
def pull (p : String) (t : BignumState) : BignumState where
  regs := fun y => t.regs (scr p y)
  mem := t.mem

theorem pull_setReg (p : String) (t : BignumState) (y : String) (v : BitVec 64) :
    pull p (setReg t (scr p y) v) = setReg (pull p t) y v := by
  simp only [pull, setReg, BignumState.mk.injEq, and_true]
  funext z
  simp only [scr_inj]

/-- `t'` is a run of renamed code from `t` whose pull is `s'`, and every register outside the
    scratch names keeps its value. -/
def RenOK (p : String) (t s' t' : BignumState) : Prop :=
  pull p t' = s' ∧ ∀ x, (∀ y, x ≠ scr p y) → t'.regs x = t.regs x

theorem renOK_setReg (p : String) (t : BignumState) (y : String) (v : BitVec 64) :
    RenOK p t (setReg (pull p t) y v) (setReg t (scr p y) v) := by
  refine ⟨pull_setReg p t y v, fun x hx => ?_⟩
  show (if x = scr p y then v else t.regs x) = t.regs x
  rw [if_neg (hx y)]

theorem renOK_trans {p : String} {t t1 t2 s1 : BignumState} {y : String} {v : BitVec 64}
    (h1 : RenOK p t s1 t1) (h2 : t2 = setReg t1 (scr p y) v) :
    RenOK p t (setReg s1 y v) t2 := by
  subst h2
  refine ⟨by rw [pull_setReg, h1.1], fun x hx => ?_⟩
  show (if x = scr p y then v else t1.regs x) = t.regs x
  rw [if_neg (hx y)]
  exact h1.2 x hx

theorem renOK_refl (p : String) (t : BignumState) : RenOK p t (pull p t) t :=
  ⟨rfl, fun _ _ => rfl⟩

/-- `x` with its name replaced by its scratch name. -/
def renV (p : String) (x : VarI) : VarI :=
  { x with var := { x.var with vname := scr p x.var.vname } }

/-- The renaming of an expression: every variable and load base to its scratch name. -/
def renP (p : String) : PExpr → PExpr
  | .Pvar g => .Pvar { g with gv := renV p g.gv }
  | .Pload ws x off => .Pload ws (renV p x) off
  | .Papp1 o e => .Papp1 o (renP p e)
  | .Papp2 o a b => .Papp2 o (renP p a) (renP p b)
  | e => e

/-- The renaming of an l-value. -/
def renL (p : String) : LVal → LVal
  | .Lvar x => .Lvar (renV p x)
  | .Lmem ws x off => .Lmem ws (renV p x) off
  | l => l

/-- The renaming of an assignment or operator instruction; other shapes are unchanged. -/
def renI (p : String) : InstrR → InstrR
  | .Cassgn lv tg ty e => .Cassgn (renL p lv) tg ty (renP p e)
  | .Copn lvs tg op es => .Copn (lvs.map (renL p)) tg op (es.map (renP p))
  | i => i

theorem resolveAddr_renV (p : String) (t : BignumState) (x : VarI) (off : PExpr) :
    resolveAddr t (renV p x) off = resolveAddr (pull p t) x off := by
  cases off <;> rfl

theorem evalPExpr_renP (p : String) (t : BignumState) :
    ∀ e, evalPExpr t (renP p e) = evalPExpr (pull p t) e
  | .Pconst _ => rfl
  | .Pbool _ => rfl
  | .Parr_init _ => rfl
  | .Pvar _ => rfl
  | .Pget .. => rfl
  | .Psub .. => rfl
  | .Pload ws x off => by
    cases ws <;> simp only [renP, evalPExpr, resolveAddr_renV] <;> rfl
  | .Papp1 o e => by
    cases o <;> simp only [renP, evalPExpr, evalPExpr_renP p t e]
  | .Papp2 o a b => by
    cases o <;> simp only [renP, evalPExpr, evalPExpr_renP p t a, evalPExpr_renP p t b]
  | .PappN .. => rfl
  | .Pif .. => rfl

/-! ### Renaming one instruction -/

theorem writeSubBundle_ren (p : String) (t : BignumState) (lvs : List LVal) (c v : BitVec 64)
    {s' : BignumState} (h : writeSubBundle (pull p t) lvs c v = some s') :
    ∃ t', writeSubBundle t (lvs.map (renL p)) c v = some t' ∧ RenOK p t s' t' := by
  unfold writeSubBundle at h
  split at h
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_setReg _ _ _ _) rfl⟩
  · cases h

theorem writeMulxBundle_ren (p : String) (t : BignumState) (lvs : List LVal) (c v : BitVec 64)
    {s' : BignumState} (h : writeMulxBundle (pull p t) lvs c v = some s') :
    ∃ t', writeMulxBundle t (lvs.map (renL p)) c v = some t' ∧ RenOK p t s' t' := by
  unfold writeMulxBundle at h
  split at h
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_setReg _ _ _ _) rfl⟩
  · cases h

theorem writeAdxBundle_ren (p : String) (t : BignumState) (lvs : List LVal) (c v : BitVec 64)
    {s' : BignumState} (h : writeAdxBundle (pull p t) lvs c v = some s') :
    ∃ t', writeAdxBundle t (lvs.map (renL p)) c v = some t' ∧ RenOK p t s' t' := by
  unfold writeAdxBundle at h
  split at h
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_setReg _ _ _ _) rfl⟩
  · cases h

theorem writeXorBundle_ren (p : String) (t : BignumState) (lvs : List LVal) (o c v : BitVec 64)
    {s' : BignumState} (h : writeXorBundle (pull p t) lvs o c v = some s') :
    ∃ t', writeXorBundle t (lvs.map (renL p)) o c v = some t' ∧ RenOK p t s' t' := by
  unfold writeXorBundle at h
  split at h
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_trans (renOK_setReg _ _ _ _) rfl) rfl⟩
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_setReg _ _ _ _) rfl⟩
  · cases h

theorem writeShiftBundle_ren (p : String) (t : BignumState) (lvs : List LVal) (v : BitVec 64)
    {s' : BignumState} (h : writeShiftBundle (pull p t) lvs v = some s') :
    ∃ t', writeShiftBundle t (lvs.map (renL p)) v = some t' ∧ RenOK p t s' t' := by
  unfold writeShiftBundle at h
  split at h
  · cases h
    exact ⟨_, rfl, renOK_setReg _ _ _ _⟩
  · cases h
    exact ⟨_, rfl, renOK_trans (renOK_setReg _ _ _ _) rfl⟩
  · cases h
    exact ⟨_, rfl, renOK_setReg _ _ _ _⟩
  · cases h

theorem ren_copn2 {p : String} {t s' : BignumState} {lvs : List LVal} {tg : AssgnTag}
    {op : AsmOp} {a b : PExpr}
    (W : BignumState → List LVal → BitVec 64 → BitVec 64 → Option BignumState)
    (hE : ∀ x lvs a b, execInstr x (.Copn lvs tg (.Oasm op) [a, b]) =
      (evalPExpr x a).bind fun va => (evalPExpr x b).bind fun vb => W x lvs va vb)
    (hW : ∀ va vb s', W (pull p t) lvs va vb = some s' →
      ∃ t', W t (lvs.map (renL p)) va vb = some t' ∧ RenOK p t s' t')
    (h : execInstr (pull p t) (.Copn lvs tg (.Oasm op) [a, b]) = some s') :
    ∃ t', execInstr t (renI p (.Copn lvs tg (.Oasm op) [a, b])) = some t' ∧ RenOK p t s' t' := by
  rw [hE] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨va, ha, vb, hb, hw⟩ := h
  obtain ⟨t', ht', hr⟩ := hW va vb s' hw
  refine ⟨t', ?_, hr⟩
  simp only [renI, List.map_cons, List.map_nil]
  rw [hE, evalPExpr_renP, evalPExpr_renP, ha, hb]
  exact ht'

theorem ren_copn3 {p : String} {t s' : BignumState} {lvs : List LVal} {tg : AssgnTag}
    {op : AsmOp} {a b c : PExpr}
    (W : BignumState → List LVal → BitVec 64 → BitVec 64 → BitVec 64 → Option BignumState)
    (hE : ∀ x lvs a b c, execInstr x (.Copn lvs tg (.Oasm op) [a, b, c]) =
      (evalPExpr x a).bind fun va => (evalPExpr x b).bind fun vb =>
        (evalPExpr x c).bind fun vc => W x lvs va vb vc)
    (hW : ∀ va vb vc s', W (pull p t) lvs va vb vc = some s' →
      ∃ t', W t (lvs.map (renL p)) va vb vc = some t' ∧ RenOK p t s' t')
    (h : execInstr (pull p t) (.Copn lvs tg (.Oasm op) [a, b, c]) = some s') :
    ∃ t', execInstr t (renI p (.Copn lvs tg (.Oasm op) [a, b, c])) = some t' ∧
      RenOK p t s' t' := by
  rw [hE] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨va, ha, vb, hb, vc, hc, hw⟩ := h
  obtain ⟨t', ht', hr⟩ := hW va vb vc s' hw
  refine ⟨t', ?_, hr⟩
  simp only [renI, List.map_cons, List.map_nil]
  rw [hE, evalPExpr_renP, evalPExpr_renP, evalPExpr_renP, ha, hb, hc]
  exact ht'

/-- The operator names and arities `opnJ` translates. -/
theorem opnJ_cases {name : String} {lvs : List LVal} {args : List PExpr}
    {js : List (JInstr 64)} (h : opnJ name lvs args = some js) :
    (∃ a b, args = [a, b] ∧ (name = "SUB_64" ∨ name = "ADD_64" ∨ name = "XOR_64" ∨
      name = "SHL_64" ∨ name = "SHR_64" ∨ name = "MULX")) ∨
    (∃ a b c, args = [a, b, c] ∧ (name = "SBB_64" ∨ name = "ADC_64" ∨ name = "SHLD_64" ∨
      name = "SHRD_64" ∨ name = "ADCX" ∨ name = "ADOX")) := by
  unfold opnJ at h
  split at h
  · unfold subBundleJ at h
    split at h
    · split_ifs at h <;>
        first | cases h | exact Or.inl ⟨_, _, rfl, by simp [*]⟩
    · split_ifs at h <;>
        first | cases h | exact Or.inr ⟨_, _, _, rfl, by simp [*]⟩
    · cases h
  · split at h
    · split_ifs at h with h1
      exact Or.inl ⟨_, _, rfl, by simp [h1.1]⟩
    · cases h
  · unfold shiftJ at h
    split at h
    · split_ifs at h <;>
        first | cases h | exact Or.inl ⟨_, _, rfl, by simp [*]⟩
    · split_ifs at h <;>
        first | cases h | exact Or.inr ⟨_, _, _, rfl, by simp [*]⟩
    · cases h
  · unfold pairJ at h
    split at h
    · split_ifs at h with h1
      exact Or.inl ⟨_, _, rfl, by simp [h1]⟩
    · split_ifs at h with h1
      rcases h1 with h1 | h1
      · exact Or.inr ⟨_, _, _, rfl, by simp [h1]⟩
      · exact Or.inr ⟨_, _, _, rfl, by simp [h1]⟩
    · cases h
  · unfold shiftJ at h
    split at h
    · split_ifs at h <;>
        first | cases h | exact Or.inl ⟨_, _, rfl, by simp [*]⟩
    · split_ifs at h <;>
        first | cases h | exact Or.inr ⟨_, _, _, rfl, by simp [*]⟩
    · cases h
  · cases h

/-- Renaming a translatable instruction: run on `t`, the renamed instruction computes the
    renamed result of the instruction run on `pull p t`, and leaves every register outside
    the scratch names unchanged. -/
theorem execInstr_ren (p : String) {i : InstrR} {js : List (JInstr 64)} (hj : toJ i = some js)
    (t : BignumState) {s' : BignumState} (h : execInstr (pull p t) i = some s') :
    ∃ t', execInstr t (renI p i) = some t' ∧ RenOK p t s' t' := by
  unfold toJ at hj
  split at hj
  · next x tg ty e =>
    simp only [execInstr, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨w, hw, rfl⟩ := h
    refine ⟨setReg t (scr p x.var.vname) w, ?_, renOK_setReg _ _ _ _⟩
    simp only [renI, renL, execInstr, evalPExpr_renP, hw, Option.bind_eq_bind, Option.bind_some]
    rfl
  · next b k tg ty g =>
    simp only [execInstr, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨w, hw, a, ha, rfl⟩ := h
    refine ⟨storeMem t a (UInt64.ofNat w.toNat), ?_, rfl, fun _ _ => rfl⟩
    simp only [renI, renL, execInstr, evalPExpr_renP, hw, resolveAddr_renV, ha,
      Option.bind_eq_bind, Option.bind_some]
  · next lvs tg op args =>
    rcases opnJ_cases hj with ⟨a, b, rfl, hn⟩ | ⟨a, b, c, rfl, hn⟩
    · rcases hn with hn | hn | hn | hn | hn | hn
      · exact ren_copn2 _ (fun x l a b => execInstr_SUB x l tg op a b hn)
          (fun _ _ _ hw => writeSubBundle_ren p t lvs _ _ hw) h
      · exact ren_copn2 _ (fun x l a b => execInstr_ADD x l tg op a b hn)
          (fun _ _ _ hw => writeSubBundle_ren p t lvs _ _ hw) h
      · exact ren_copn2 _ (fun x l a b => execInstr_XOR x l tg op a b hn)
          (fun _ _ _ hw => writeXorBundle_ren p t lvs _ _ _ hw) h
      · exact ren_copn2 _ (fun x l a b => execInstr_SHL x l tg op a b hn)
          (fun _ _ _ hw => writeShiftBundle_ren p t lvs _ hw) h
      · exact ren_copn2 _ (fun x l a b => execInstr_SHR x l tg op a b hn)
          (fun _ _ _ hw => writeShiftBundle_ren p t lvs _ hw) h
      · exact ren_copn2 _ (fun x l a b => execInstr_MULX x l tg op a b hn)
          (fun _ _ _ hw => writeMulxBundle_ren p t lvs _ _ hw) h
    · rcases hn with hn | hn | hn | hn | hn | hn
      · exact ren_copn3 _ (fun x l a b c => execInstr_SBB x l tg op a b c hn)
          (fun _ _ _ _ hw => writeSubBundle_ren p t lvs _ _ hw) h
      · exact ren_copn3 _ (fun x l a b c => execInstr_ADC x l tg op a b c hn)
          (fun _ _ _ _ hw => writeSubBundle_ren p t lvs _ _ hw) h
      · exact ren_copn3 _ (fun x l a b c => execInstr_SHLD x l tg op a b c hn)
          (fun _ _ _ _ hw => writeShiftBundle_ren p t lvs _ hw) h
      · exact ren_copn3 _ (fun x l a b c => execInstr_SHRD x l tg op a b c hn)
          (fun _ _ _ _ hw => writeShiftBundle_ren p t lvs _ hw) h
      · exact ren_copn3 _ (fun x l a b c => execInstr_ADCX x l tg op a b c hn)
          (fun _ _ _ _ hw => writeAdxBundle_ren p t lvs _ _ hw) h
      · exact ren_copn3 _ (fun x l a b c => execInstr_ADOX x l tg op a b c hn)
          (fun _ _ _ _ hw => writeAdxBundle_ren p t lvs _ _ hw) h
  · cases hj

/-- Renaming a translatable body. -/
theorem bignumExec_ren (p : String) :
    ∀ (body : List InstrR) (blk : List (JInstr 64)), toJBlock body = some blk →
      ∀ (t s' : BignumState), bignumExec body (pull p t) = some s' →
        ∃ t', bignumExec (body.map (renI p)) t = some t' ∧ RenOK p t s' t'
  | [], _, _, t, s', he => by
    simp only [bignumExec, Option.some.injEq] at he
    exact ⟨t, rfl, he ▸ renOK_refl p t⟩
  | i :: is, blk, h, t, s', he => by
    simp only [toJBlock, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨js, hjs, jss, hjss, -⟩ := h
    simp only [bignumExec] at he
    split at he
    · next s1 h1 =>
      obtain ⟨t1, ht1, hr1⟩ := execInstr_ren p hjs t h1
      rw [← hr1.1] at he
      obtain ⟨t2, ht2, hr2⟩ := bignumExec_ren p is jss hjss t1 s' he
      refine ⟨t2, ?_, hr2.1, fun x hx => (hr2.2 x hx).trans (hr1.2 x hx)⟩
      simp only [List.map_cons, bignumExec, ht1]
      exact ht2
    · cases he

/-! ## Registers a translated body does not write -/

/-- The address state with the registers of `s` and its defined bytes (`0` elsewhere). -/
def liftS (s : BignumState) : AState where
  regs := s.regs
  mem := fun a => match s.mem (UInt64.ofBitVec a) with
    | some b => b.toBitVec
    | none => 0

theorem bjCorr_liftS (s : BignumState) : BJCorr s (liftS s) := by
  refine ⟨rfl, fun a b h => ?_⟩
  simp only [liftS, UInt64.ofBitVec_toBitVec, h]

theorem runBlockA_regs_frame (x : String) :
    ∀ (blk : List (JInstr 64)) (sa : AState), x ∉ blk.flatMap dsts →
      (runBlockA sa blk).regs x = sa.regs x
  | [], _, _ => rfl
  | i :: is, sa, hx => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at hx
    rw [runBlockA_cons, runBlockA_regs_frame x is _ hx.2]
    exact evalInstr_regs_of_not_mem_dsts sa.view i x hx.1

/-- A register outside the destinations of a body's translation keeps its value. -/
theorem bignumExec_regs_frame {body : List InstrR} {blk : List (JInstr 64)}
    (h : toJBlock body = some blk) {s s' : BignumState} (he : bignumExec body s = some s')
    {x : String} (hx : x ∉ blk.flatMap dsts) : s'.regs x = s.regs x := by
  have hc := bignumExec_runBlockA_sim body blk s s' (liftS s) h (bjCorr_liftS s) he
  rw [hc.1, runBlockA_regs_frame x blk _ hx]
  rfl

/-- A register outside the destinations of an instruction's translation keeps its value. -/
theorem execInstr_regs_frame {i : InstrR} {js : List (JInstr 64)} (h : toJ i = some js)
    {s s' : BignumState} (he : execInstr s i = some s') {x : String}
    (hx : x ∉ js.flatMap dsts) : s'.regs x = s.regs x := by
  have hc := toJ_sim h (bjCorr_liftS s) he
  rw [hc.1, runBlockA_regs_frame x js _ hx]
  rfl

/-! ## Inlining a call -/

/-- The scratch registers hold `0`. -/
def Inv (p : String) (s : BignumState) : Prop := ∀ y, s.regs (scr p y) = 0

/-- Equal registers outside the scratch names, and equal memories. -/
def Agree (p : String) (a b : BignumState) : Prop :=
  (∀ x, (∀ y, x ≠ scr p y) → a.regs x = b.regs x) ∧ a.mem = b.mem

/-- An argument of an inlined call: a constant, or a variable outside the scratch names. -/
def argOK (p : String) : PExpr → Bool
  | .Pconst _ => true
  | .Pvar g => !isScr p g.gv.var.vname
  | _ => false

/-- The scratch register of `x` as an l-value. -/
def scrLv (p x : String) : LVal := .Lvar { var := { vname := scr p x, vtype := .sword .U64 } }

/-- The scratch register of `x` as an expression. -/
def scrPv (p x : String) : PExpr :=
  .Pvar { gv := { var := { vname := scr p x, vtype := .sword .U64 } }, gs := false }

/-- The arguments written to the scratch registers of the parameters; the first parameter is
    written last, so a repeated parameter name holds its first argument. -/
def paramCode (p : String) : List FunParam → List PExpr → List InstrR
  | q :: qs, e :: es =>
    paramCode p qs es ++ [.Cassgn (scrLv p q.var.var.vname) .AT_none (.sword .U64) e]
  | _, _ => []

/-- The binding of the callee results, read from their scratch registers, to the call's
    l-values; `none` on an l-value naming a scratch register. -/
def resultCode (p : String) : List LVal → List VarI → Option (List InstrR)
  | [], [] => some []
  | lv :: lvs, r :: rs =>
    match lv, resultCode p lvs rs with
    | .Lnone _ _, some rc => some rc
    | .Lvar x, some rc =>
      if isScr p x.var.vname then none
      else some (.Cassgn (.Lvar x) .AT_none (.sword .U64) (scrPv p r.var.vname) :: rc)
    | .Lmem .U64 b off, some rc =>
      if isScr p b.var.vname then none
      else some (.Cassgn (.Lmem .U64 b off) .AT_none (.sword .U64) (scrPv p r.var.vname) :: rc)
    | _, _ => none
  | _, _ => none

/-- The scratch registers of `names` set to `0`. -/
def zeroCode (p : String) (names : List String) : List InstrR :=
  names.map fun y => .Cassgn (scrLv p y) .AT_none (.sword .U64) (.Pconst 0)

/-- The inlined code of a call to `fd` with l-values `lvs` and arguments `args`: the arguments
    to the scratch registers of the parameters, the straight-line callee body under `renI p`,
    the results to the l-values, and the scratch registers the callee writes
    back to `0`. `none` unless the callee body expands to a translatable straight-line body
    and every argument is a constant or a variable outside the scratch names. -/
def callCode (p : String) (fd : FunDecl) (lvs : List LVal) (args : List PExpr) :
    Option (List InstrR) :=
  match flatB fd.body with
  | none => none
  | some fb =>
    match toJBlock fb with
    | none => none
    | some blk =>
      if args.all (argOK p) then
        (if lvs.isEmpty then some [] else resultCode p lvs fd.results).map fun rc =>
          paramCode p fd.params args ++ fb.map (renI p) ++ rc ++
            zeroCode p (fd.params.map (·.var.var.vname) ++ blk.flatMap dsts)
      else none

/-- The value of register `y` after the parameters `qs` receive the values `vs`, the first
    occurrence of a name taking precedence, and `d y` where no parameter names `y`. -/
def paramVal (qs : List FunParam) (vs : List (BitVec 64)) (d : String → BitVec 64)
    (y : String) : BitVec 64 :=
  match qs, vs with
  | q :: qs, v :: vs => if y = q.var.var.vname then v else paramVal qs vs d y
  | _, _ => d y

theorem paramVal_of_not_mem {d : String → BitVec 64} {y : String} :
    ∀ (qs : List FunParam) (vs : List (BitVec 64)), y ∉ qs.map (·.var.var.vname) →
      paramVal qs vs d y = d y
  | [], _, _ => by simp [paramVal]
  | _ :: _, [], _ => by simp [paramVal]
  | q :: qs, v :: vs, hy => by
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    simp only [paramVal, if_neg hy.1]
    exact paramVal_of_not_mem qs vs hy.2

/-- The callee register file `bignumExecFuel` builds for a call is `paramVal` over `0`. -/
theorem calleeRegs_eq (qs : List FunParam) (vs : List (BitVec 64)) :
    (fun name => match qs.findIdx? (·.var.var.vname = name) with
      | some idx => (vs[idx]?).getD 0
      | none => 0) = paramVal qs vs (fun _ => 0) := by
  funext name
  induction qs generalizing vs with
  | nil => cases vs <;> simp [paramVal]
  | cons q qs ih =>
    cases vs with
    | nil =>
      simp only [paramVal, List.getElem?_nil, Option.getD_none]
      split <;> rfl
    | cons v vs =>
      have := ih vs
      simp only [List.findIdx?_cons, paramVal]
      by_cases hq : name = q.var.var.vname
      · subst hq
        simp
      · have hq' : ¬ q.var.var.vname = name := fun h => hq h.symm
        simp only [hq', decide_false, Bool.false_eq_true, if_false, if_neg hq]
        rw [← this]
        cases List.findIdx? (fun x => decide (x.var.var.vname = name)) qs <;> simp

theorem bignumState_ext {a b : BignumState} (h1 : a.regs = b.regs) (h2 : a.mem = b.mem) :
    a = b := by
  cases a
  cases b
  simp_all

theorem evalPExpr_agree {p : String} {e : PExpr} (he : argOK p e = true) {t s : BignumState}
    (ha : Agree p t s) : evalPExpr t e = evalPExpr s e := by
  cases e <;> simp only [argOK, Bool.false_eq_true, Bool.not_eq_true'] at he
  · rfl
  · simp only [evalPExpr, ha.1 _ (ne_scr_of_isScr he)]

theorem paramCode_run (p : String) :
    ∀ (qs : List FunParam) (args : List PExpr) (vs : List (BitVec 64)) (s : BignumState),
      args.all (argOK p) = true → args.mapM (evalPExpr s) = some vs →
      ∃ t, bignumExec (paramCode p qs args) s = some t ∧ Agree p t s ∧
        ∀ y, t.regs (scr p y) = paramVal qs vs (fun y => s.regs (scr p y)) y
  | [], _, vs, s, _, _ => ⟨s, rfl, ⟨fun _ _ => rfl, rfl⟩, fun _ => by cases vs <;> rfl⟩
  | _ :: _, [], vs, s, _, hvs => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hvs
    subst hvs
    exact ⟨s, rfl, ⟨fun _ _ => rfl, rfl⟩, fun _ => rfl⟩
  | q :: qs, e :: es, vs, s, hargs, hvs => by
    simp only [List.all_cons, Bool.and_eq_true] at hargs
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hvs
    obtain ⟨v, hv, vs', hvs', rfl⟩ := hvs
    obtain ⟨t0, ht0, hag0, hsc0⟩ := paramCode_run p qs es vs' s hargs.2 hvs'
    refine ⟨setReg t0 (scr p q.var.var.vname) v, ?_, ⟨fun x hx => ?_, hag0.2⟩, fun y => ?_⟩
    · simp only [paramCode, bignumExec_append_eq, ht0, Option.bind_some, bignumExec, execInstr,
        scrLv, evalPExpr_agree hargs.1 hag0, hv, Option.bind_eq_bind]
    · show (if x = scr p q.var.var.vname then v else t0.regs x) = s.regs x
      rw [if_neg (hx _)]
      exact hag0.1 x hx
    · show (if scr p y = scr p q.var.var.vname then v else t0.regs (scr p y)) = _
      simp only [scr_inj, paramVal, hsc0]

theorem zeroCode_run (p : String) :
    ∀ (Z : List String) (t : BignumState), ∃ t', bignumExec (zeroCode p Z) t = some t' ∧
      Agree p t' t ∧ ∀ y, t'.regs (scr p y) = if y ∈ Z then 0 else t.regs (scr p y)
  | [], t => ⟨t, rfl, ⟨fun _ _ => rfl, rfl⟩, fun _ => by simp⟩
  | z :: Z, t => by
    obtain ⟨t', ht', hag, hsc⟩ := zeroCode_run p Z (setReg t (scr p z) 0)
    refine ⟨t', ?_, ⟨fun x hx => ?_, hag.2⟩, fun y => ?_⟩
    · show bignumExec (.Cassgn (scrLv p z) .AT_none (.sword .U64) (.Pconst 0) :: zeroCode p Z) t
        = some t'
      simp only [bignumExec, execInstr, scrLv, evalPExpr, Option.bind_eq_bind, Option.bind_some]
      simpa using ht'
    · rw [hag.1 x hx]
      show (if x = scr p z then 0 else t.regs x) = t.regs x
      rw [if_neg (hx z)]
    · rw [hsc y]
      show (if y ∈ Z then 0 else (if scr p y = scr p z then 0 else t.regs (scr p y))) = _
      simp only [scr_inj, List.mem_cons]
      by_cases h1 : y = z <;> by_cases h2 : y ∈ Z <;> simp [h1, h2]

theorem resultCode_run (p : String) (cf : BignumState) :
    ∀ (lvs : List LVal) (rs : List VarI) (rc : List InstrR) (sc t s2 : BignumState),
      resultCode p lvs rs = some rc → Agree p sc t → (∀ r, t.regs (scr p r) = cf.regs r) →
      bindResults sc cf lvs rs = some s2 →
      ∃ t', bignumExec rc t = some t' ∧ Agree p s2 t' ∧
        (∀ y, t'.regs (scr p y) = t.regs (scr p y)) ∧ (∀ y, s2.regs (scr p y) = sc.regs (scr p y))
  | [], [], rc, sc, t, s2, hrc, hag, _, hb => by
    simp only [resultCode, Option.some.injEq] at hrc
    simp only [bindResults, Option.some.injEq] at hb
    subst hrc hb
    exact ⟨t, rfl, hag, fun _ => rfl, fun _ => rfl⟩
  | lv :: lvs, r :: rs, rc, sc, t, s2, hrc, hag, hcf, hb => by
    simp only [resultCode] at hrc
    simp only [bindResults, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
    obtain ⟨s1, hs1, hb⟩ := hb
    split at hrc
    · next rc' hrc' =>
      cases hrc
      simp only [bindResult, Option.some.injEq] at hs1
      subst hs1
      exact resultCode_run p cf lvs rs rc sc t s2 hrc' hag hcf hb
    · next x rc' hrc' =>
      split at hrc
      · cases hrc
      · next hx =>
        cases hrc
        simp only [bindResult, Option.some.injEq] at hs1
        subst hs1
        have hx' := ne_scr_of_isScr (Bool.eq_false_iff.2 hx)
        have hag1 : Agree p (setReg sc x.var.vname (cf.regs r.var.vname))
            (setReg t x.var.vname (cf.regs r.var.vname)) := by
          refine ⟨fun z hz => ?_, hag.2⟩
          show (if z = x.var.vname then _ else sc.regs z) =
            (if z = x.var.vname then _ else t.regs z)
          split
          · rfl
          · exact hag.1 z hz
        have hcf1 : ∀ r', (setReg t x.var.vname (cf.regs r.var.vname)).regs (scr p r') =
            cf.regs r' := fun r' => by
          show (if scr p r' = x.var.vname then _ else t.regs (scr p r')) = _
          rw [if_neg (fun h => hx' r' h.symm)]
          exact hcf r'
        obtain ⟨t', ht', hag', hsc', hs2⟩ := resultCode_run p cf lvs rs rc' _ _ s2 hrc' hag1 hcf1 hb
        refine ⟨t', ?_, hag', fun y => ?_, fun y => ?_⟩
        · simp only [bignumExec, execInstr, scrPv, evalPExpr, hcf, Option.bind_eq_bind,
            Option.bind_some]
          exact ht'
        · rw [hsc' y]
          show (if scr p y = x.var.vname then _ else t.regs (scr p y)) = _
          rw [if_neg (fun h => hx' y h.symm)]
        · rw [hs2 y]
          show (if scr p y = x.var.vname then _ else sc.regs (scr p y)) = _
          rw [if_neg (fun h => hx' y h.symm)]
    · next b off rc' hrc' =>
      split at hrc
      · cases hrc
      · next hb' =>
        cases hrc
        have hb'' := ne_scr_of_isScr (Bool.eq_false_iff.2 hb')
        simp only [bindResult, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hs1
        obtain ⟨a, ha, rfl⟩ := hs1
        have ha' : resolveAddr t b off = some a := by
          rw [← ha]
          cases off <;> simp only [resolveAddr, hag.1 _ (hb'' ·)]
        have hag1 : Agree p (storeMem sc a (UInt64.ofNat (cf.regs r.var.vname).toNat))
            (storeMem t a (UInt64.ofNat (cf.regs r.var.vname).toNat)) :=
          ⟨hag.1, by simp only [storeMem, hag.2]⟩
        obtain ⟨t', ht', hag', hsc', hs2⟩ :=
          resultCode_run p cf lvs rs rc' _ _ s2 hrc' hag1 hcf hb
        refine ⟨t', ?_, hag', hsc', hs2⟩
        simp only [bignumExec, execInstr, scrPv, evalPExpr, hcf, ha', Option.bind_eq_bind,
          Option.bind_some]
        exact ht'
    · cases hrc
  | [], _ :: _, _, _, _, _, hrc, _, _, _ => by simp [resultCode] at hrc
  | _ :: _, [], _, _, _, _, hrc, _, _, _ => by simp [resultCode] at hrc

/-- The callee state `bignumExecFuel` builds for a call to `fd` with argument values `vs`
    from the memory of `s`. -/
def calleeInit (fd : FunDecl) (vs : List (BitVec 64)) (s : BignumState) : BignumState where
  regs := fun name => match fd.params.findIdx? (·.var.var.vname = name) with
    | some idx => (vs[idx]?).getD 0
    | none => 0
  mem := s.mem

/-- The caller state after a call returns the callee state `cf`. -/
def callResult (s cf : BignumState) (lvs : List LVal) (rs : List VarI) : Option BignumState :=
  if lvs.isEmpty then some { s with mem := cf.mem }
  else bindResults { s with mem := cf.mem } cf lvs rs

/-- **Inlining.** When the scratch registers hold `0`, the inlined code of a call runs from
    the caller state to the state the call returns, which again holds `0` in its scratch
    registers. -/
theorem callCode_sound (reg : BignumRegistry) (p : String) {fd : FunDecl} {lvs : List LVal}
    {args : List PExpr} {code : List InstrR} (hc : callCode p fd lvs args = some code)
    (fuel : Nat) {s : BignumState} (hinv : Inv p s) {vs : List (BitVec 64)}
    (hvs : args.mapM (evalPExpr s) = some vs) {cf : BignumState}
    (hrun : bignumExecFuel reg fuel fd.body (calleeInit fd vs s) = some cf) {s2 : BignumState}
    (hres : callResult s cf lvs fd.results = some s2) :
    bignumExec code s = some s2 ∧ Inv p s2 := by
  unfold callCode at hc
  split at hc
  · cases hc
  · next fb hfb =>
    split at hc
    · cases hc
    · next blk hblk =>
      by_cases hargs : args.all (argOK p) = true
      swap
      · rw [if_neg hargs] at hc
        cases hc
      rw [if_pos hargs] at hc
      obtain ⟨rc, hrc, rfl⟩ := Option.map_eq_some_iff.1 hc
      obtain ⟨t1, ht1, hag1, hsc1⟩ := paramCode_run p fd.params args vs s hargs hvs
      have hd : (fun y => s.regs (scr p y)) = fun _ => 0 := funext hinv
      rw [hd] at hsc1
      have hpull : pull p t1 = calleeInit fd vs s := by
        refine bignumState_ext ?_ hag1.2
        funext y
        show t1.regs (scr p y) = _
        rw [hsc1, ← calleeRegs_eq]
        rfl
      have hfbrun := flatB_sound reg fuel fd.body fb _ cf hfb hrun
      have hfbrun' := hfbrun
      rw [← hpull] at hfbrun'
      obtain ⟨t2, ht2, hr2⟩ := bignumExec_ren p fb blk hblk t1 cf hfbrun'
      have hcf2 : ∀ r, t2.regs (scr p r) = cf.regs r := fun r => by
        rw [← hr2.1]
        rfl
      have hag2 : Agree p { s with mem := cf.mem } t2 :=
        ⟨fun x hx => ((hr2.2 x hx).trans (hag1.1 x hx)).symm, by rw [← hr2.1]; rfl⟩
      have h3 : ∃ t3, bignumExec rc t2 = some t3 ∧ Agree p s2 t3 ∧
          (∀ y, t3.regs (scr p y) = t2.regs (scr p y)) ∧
          (∀ y, s2.regs (scr p y) = s.regs (scr p y)) := by
        unfold callResult at hres
        split_ifs at hrc hres
        · cases hrc
          cases hres
          exact ⟨t2, rfl, hag2, fun _ => rfl, fun _ => rfl⟩
        · obtain ⟨t3, h1, h2, h3, h4⟩ :=
            resultCode_run p cf lvs fd.results rc { s with mem := cf.mem } t2 s2 hrc hag2 hcf2 hres
          exact ⟨t3, h1, h2, h3, h4⟩
      obtain ⟨t3, ht3, hag3, hsc3, hs2⟩ := h3
      obtain ⟨t4, ht4, hag4, hsc4⟩ :=
        zeroCode_run p (fd.params.map (·.var.var.vname) ++ blk.flatMap dsts) t3
      have hinv2 : Inv p s2 := fun y => (hs2 y).trans (hinv y)
      refine ⟨?_, hinv2⟩
      simp only [bignumExec_append_eq, ht1, ht2, ht3, ht4, Option.bind_some]
      congr 1
      refine bignumState_ext ?_ (hag4.2.trans hag3.2.symm)
      funext x
      by_cases hx : ∃ y, x = scr p y
      · obtain ⟨y, rfl⟩ := hx
        rw [hsc4 y, hinv2 y]
        split
        · rfl
        · next hy =>
          simp only [List.mem_append, not_or] at hy
          rw [hsc3 y, hcf2 y, bignumExec_regs_frame hblk hfbrun hy.2]
          show (match fd.params.findIdx? (·.var.var.vname = y) with
            | some idx => (vs[idx]?).getD 0
            | none => 0) = 0
          rw [show (match fd.params.findIdx? (·.var.var.vname = y) with
            | some idx => (vs[idx]?).getD 0
            | none => 0) = paramVal fd.params vs (fun _ => 0) y from
              congrFun (calleeRegs_eq fd.params vs) y]
          exact paramVal_of_not_mem _ _ hy.1
      · push Not at hx
        exact (hag4.1 x hx).trans (hag3.1 x hx).symm

/-! ## Bodies with calls and counted loops -/

/-- An instruction of the caller kept as it is: it translates, and its translation writes no
    scratch register. -/
def okI (p : String) (i : InstrR) : Bool :=
  match toJ i with
  | some js => (js.flatMap dsts).all fun x => !isScr p x
  | none => false

mutual
/-- The straight-line expansion of one caller instruction: a `Cfor` unrolled, a `Ccall`
    inlined by `callCode` under the prefix `p`, an `okI` instruction kept. -/
def inlI (reg : BignumRegistry) (p : String) : InstrR → Option (List InstrR)
  | .Cfor v r b => if isScr p v.var.vname then none else (inlB reg p b).map (unrollFor v r)
  | .Ccall _ lvs fn args =>
    match reg fn.name with
    | some fd => callCode p fd lvs args
    | none => none
  | .Cassgn lv tg ty e =>
    if okI p (.Cassgn lv tg ty e) then some [.Cassgn lv tg ty e] else none
  | .Copn lvs tg op es => if okI p (.Copn lvs tg op es) then some [.Copn lvs tg op es] else none
  | _ => none

/-- The straight-line expansion of a caller body. -/
def inlB (reg : BignumRegistry) (p : String) : List InstrR → Option (List InstrR)
  | [] => some []
  | i :: is => do
      let a ← inlI reg p i
      let b ← inlB reg p is
      some (a ++ b)
end

theorem inlB_append (reg : BignumRegistry) (p : String) (xs ys : List InstrR) :
    inlB reg p (xs ++ ys) =
      (inlB reg p xs).bind fun a => (inlB reg p ys).map fun b => a ++ b := by
  induction xs with
  | nil =>
    simp only [List.nil_append, inlB, Option.bind_some]
    cases inlB reg p ys <;> rfl
  | cons i is ih =>
    simp only [List.cons_append, inlB, ih]
    cases inlI reg p i <;> cases inlB reg p is <;> cases inlB reg p ys <;> simp

theorem inlB_unrollFor (reg : BignumRegistry) (p : String) (v : VarI) (r : Range)
    (hv : isScr p v.var.vname = false) (b fb : List InstrR) (hb : inlB reg p b = some fb) :
    inlB reg p (unrollFor v r b) = some (unrollFor v r fb) := by
  have hc : ∀ k, inlI reg p (mkSetVarConst v k) = some [mkSetVarConst v k] := fun k => by
    simp [inlI, okI, mkSetVarConst, toJ, assignJ, dsts, hv]
  have key : ∀ (L : List Nat) (c : Nat → Nat),
      inlB reg p (L.flatMap fun k => mkSetVarConst v (c k) :: b) =
        some (L.flatMap fun k => mkSetVarConst v (c k) :: fb) := by
    intro L c
    induction L with
    | nil => rfl
    | cons k L ih =>
      simp only [List.flatMap_cons]
      rw [inlB_append, ih]
      simp [inlB, hc, hb]
  unfold unrollFor
  split
  · exact key _ (fun k => r.lo + k)
  · exact key _ (fun k => r.hi - 1 - k)

/-- An `okI` instruction preserves `Inv`. -/
theorem inv_execInstr {p : String} {i : InstrR} (hi : okI p i = true) {s s' : BignumState}
    (hinv : Inv p s) (he : execInstr s i = some s') : Inv p s' := by
  unfold okI at hi
  split at hi
  · next js hjs =>
    intro y
    rw [execInstr_regs_frame hjs he, hinv y]
    intro hy
    have := List.all_eq_true.1 hi _ hy
    rw [isScr_scr] at this
    cases this
  · cases hi

/-- **Calls and counted loops.** When the scratch registers hold `0`, a body runs under
    `bignumExecFuel` as its straight-line expansion `inlB` runs under `bignumExec`. -/
theorem inlB_sound (reg : BignumRegistry) (p : String) :
    ∀ (fuel : Nat) (body flat : List InstrR) (s s' : BignumState), Inv p s →
      inlB reg p body = some flat → bignumExecFuel reg fuel body s = some s' →
      bignumExec flat s = some s' ∧ Inv p s' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ he; simp [bignumExecFuel] at he
  | succ f ihf =>
    intro body
    induction body with
    | nil =>
      intro fb s s' hinv h he
      simp only [inlB, Option.some.injEq] at h
      simp only [bignumExecFuel, Option.some.injEq] at he
      subst h he
      exact ⟨rfl, hinv⟩
    | cons i is ih =>
      intro fb s s' hinv h he
      simp only [inlB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      cases i with
      | Cassgn lv tg ty e =>
        simp only [inlI] at ha
        split_ifs at ha with hok
        cases ha
        simp only [bignumExecFuel] at he
        rw [List.singleton_append]
        simp only [bignumExec]
        split at he
        · next s1 h1 => exact ih b s1 s' (inv_execInstr hok hinv h1) hb he
        · cases he
      | Copn lvs tg op es =>
        simp only [inlI] at ha
        split_ifs at ha with hok
        cases ha
        simp only [bignumExecFuel] at he
        rw [List.singleton_append]
        simp only [bignumExec]
        split at he
        · next s1 h1 => exact ih b s1 s' (inv_execInstr hok hinv h1) hb he
        · cases he
      | Cfor v r body =>
        simp only [inlI] at ha
        split_ifs at ha with hv
        obtain ⟨fbody, hfb, rfl⟩ := Option.map_eq_some_iff.1 ha
        simp only [bignumExecFuel] at he
        have hflat : inlB reg p (unrollFor v r body ++ is) = some (unrollFor v r fbody ++ b) := by
          rw [inlB_append, inlB_unrollFor reg p v r (Bool.eq_false_iff.2 hv) body fbody hfb, hb]
          rfl
        exact ihf _ _ s s' hinv hflat he
      | Ccall ii lvs fn args =>
        simp only [inlI] at ha
        split at ha
        · next fd hfd =>
          simp only [bignumExecFuel, hfd] at he
          split at he
          · cases he
          · next vs hvs =>
            split at he
            · cases he
            · next cf hcf =>
              have key : ∀ s2, callResult s cf lvs fd.results = some s2 →
                  bignumExecFuel reg (f + 1) is s2 = some s' →
                  bignumExec (a ++ b) s = some s' ∧ Inv p s' := by
                intro s2 hs2 hrest
                obtain ⟨hcode, hinv2⟩ := callCode_sound reg p ha f hinv hvs hcf hs2
                obtain ⟨hb', hinv'⟩ := ih b s2 s' hinv2 hb hrest
                refine ⟨?_, hinv'⟩
                rw [bignumExec_append_eq, hcode]
                exact hb'
              split at he
              · next hl => exact key _ (by simp [callResult, hl]) he
              · next hl =>
                split at he
                · cases he
                · next s2 hs2 => exact key s2 (by simp [callResult, hl, hs2]) he
        · cases ha
      | Cif _ _ _ => simp [inlI] at ha
      | Cwhile _ _ _ => simp [inlI] at ha

/-! ## Simulation by the address machine -/

/-- A body with counted loops is simulated by the translation of its straight-line
    expansion. -/
theorem flatB_runBlockA_sim (reg : BignumRegistry) (fuel : Nat) {body fb : List InstrR}
    {blk : List (JInstr 64)} (hf : flatB body = some fb) (hblk : toJBlock fb = some blk)
    {s s' : BignumState} {sa : AState} (hc : BJCorr s sa)
    (he : bignumExecFuel reg fuel body s = some s') : BJCorr s' (runBlockA sa blk) :=
  bignumExec_runBlockA_sim fb blk s s' sa hblk hc (flatB_sound reg fuel body fb s s' hf he)

/-- A body with calls and counted loops, started with its scratch registers at `0`, is
    simulated by the translation of its inlined straight-line expansion. -/
theorem inlB_runBlockA_sim (reg : BignumRegistry) (p : String) (fuel : Nat)
    {body flat : List InstrR} {blk : List (JInstr 64)} (hf : inlB reg p body = some flat)
    (hblk : toJBlock flat = some blk) {s s' : BignumState} {sa : AState} (hinv : Inv p s)
    (hc : BJCorr s sa) (he : bignumExecFuel reg fuel body s = some s') :
    BJCorr s' (runBlockA sa blk) :=
  bignumExec_runBlockA_sim flat blk s s' sa hblk hc
    (inlB_sound reg p fuel body flat s s' hinv hf he).1

/-! ## The `bignum_add_4` port -/

namespace Add4

open CatCrypt.Crypto.Jasmin.JazzToInstrR.RoundTrip

/-- The body of the `bignum_add_4` port. -/
abbrev body : List InstrR := bignumAdd4Fd.body

theorem toJBlock_isSome : (toJBlock body).isSome = true := by decide

/-- The translation of the `bignum_add_4` body. -/
def blk : List (JInstr 64) := (toJBlock body).getD []

theorem toJBlock_eq : toJBlock body = some blk := by
  have h := toJBlock_isSome
  revert h
  unfold blk
  cases toJBlock body <;> simp

/-- `bignum_add_4` is simulated by the address machine. -/
theorem runBlockA_sim {s s' : BignumState} {sa : AState} (hc : BJCorr s sa)
    (he : bignumExec body s = some s') : BJCorr s' (runBlockA sa blk) :=
  bignumExec_runBlockA_sim body blk s s' sa toJBlock_eq hc he

/-- From the address state `sa`, `bignum_add_4` runs, and its result is related to the
    address machine's run of the translation. -/
theorem runBlockA_of_liftA (sa : AState) :
    ∃ s', bignumExec body (liftA sa) = some s' ∧ BJCorr s' (runBlockA sa blk) := by
  obtain ⟨s', he, -⟩ := bignumExec_progress body blk (liftA sa) toJBlock_eq (memTotal_liftA sa)
  exact ⟨s', he, runBlockA_sim (bjCorr_liftA sa) he⟩

/-- `bignum_add_4` as the only callee. -/
def registry : BignumRegistry := fun n => if n = "bignum_add_4" then some bignumAdd4Fd else none

/-- A variable of type `u64`. -/
def pv (x : String) : PExpr :=
  .Pvar { gv := { var := { vname := x, vtype := .sword .U64 } }, gs := false }

/-- A caller that adds twice in a counted loop through calls to `bignum_add_4`. -/
def caller : List InstrR :=
  [.Cfor { var := { vname := "i", vtype := .sword .U64 } } { dir := .UpTo, lo := 0, hi := 2 }
    [.Ccall .DoNotInline [] { name := "bignum_add_4" } [pv "op", pv "ap", pv "bp"]]]

theorem inlB_isSome : (inlB registry "add4." caller).isSome = true := by decide

/-- The inlined straight-line expansion of the caller. -/
def callerFlat : List InstrR := (inlB registry "add4." caller).getD []

theorem inlB_eq : inlB registry "add4." caller = some callerFlat := by
  have h := inlB_isSome
  revert h
  unfold callerFlat
  cases inlB registry "add4." caller <;> simp

theorem toJBlock_callerFlat_isSome : (toJBlock callerFlat).isSome = true := by decide +kernel

/-- The translation of the inlined caller. -/
def callerBlk : List (JInstr 64) := (toJBlock callerFlat).getD []

theorem toJBlock_callerFlat : toJBlock callerFlat = some callerBlk := by
  have h := toJBlock_callerFlat_isSome
  revert h
  unfold callerBlk
  cases toJBlock callerFlat <;> simp

/-- The caller, with its loop and its calls, is simulated by the address machine from a
    state whose scratch registers hold `0`. -/
theorem caller_runBlockA_sim (fuel : Nat) {s s' : BignumState} {sa : AState}
    (hinv : Inv "add4." s) (hc : BJCorr s sa)
    (he : bignumExecFuel registry fuel caller s = some s') :
    BJCorr s' (runBlockA sa callerBlk) :=
  inlB_runBlockA_sim registry "add4." fuel inlB_eq toJBlock_callerFlat hinv hc he

end Add4

end CatCrypt.Crypto.Jasmin.BignumToJCalls
