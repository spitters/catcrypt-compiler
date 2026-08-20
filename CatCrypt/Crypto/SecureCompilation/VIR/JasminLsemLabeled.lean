/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# Labeled, program-indexed, fuel-bounded jasmin linear semantics — increments 4a/4b

This module extends the **straight-line** linear-semantics foundation of
`JasminLsem.lean` (increment 1: `Lstate`, `lsemStep`, `lsem1`, `lsemStraight`)
to the **labeled, program-indexed, fuel-bounded** linear semantics that jasmin's
`proofs/lang/linear_sem.v` defines: `find_label`, `eval_jump`, `find_instr`, the
program `step`, `lsem1`, and the reflexive-transitive closure `lsem`. This is the
control-flow foundation that loops/branches need (the backend's
`LprogControlFlow.loopLcmd` shape `Llabel top ; <body> ; CMP ; Lcond NZ→top`).

This file is **purely additive**: it does not modify increment 1's
`lsemStep`/`lsemStraight`. The labeled layer is built **alongside**, reusing
increment 1's `Lstate` (lvm/lmem/lpc), `lsemStep` (for the straight-line and
`Llabel`/`Lalign` arms), and `evalOperand`.

## Fidelity to `linear_sem.v` (and `linear.v` for `find_label`/`is_label`)

* **`find_label`** (Coq `linear.v` l.39–41):
  ```
  Definition find_label (lbl : label) (c : seq linstr) :=
    let idx := seq.find (is_label lbl) c in
    if idx < size c then ok idx else type_error.
  ```
  with `is_label lbl i := match li_i i with Llabel _ lbl' => lbl == lbl' | _ => false`
  (`linear.v` l.32–36) — so `is_label` matches a `Llabel` of **either** kind
  (`InternalLabel`/`ExternalLabel`). `seq.find` returns the index of the first
  matching element, and `size c` when none matches. Our `findLabel` mirrors this:
  it returns the first pc whose instruction is `Llabel _ lbl`, and `none`
  (= Coq `type_error`) when there is no such label.

* **`eval_jump`** (Coq `linear_sem.v` l.84–92):
  ```
  Definition eval_jump d s :=
    let: (fn, lbl) := d in
    Let body := if get_fundef (lp_funcs P) fn is Some fd then ok (lfd_body fd) else type_error in
    Let pc := find_label lbl body in
    ok (setcpc s fn pc.+1).
  ```
  It resolves the *target function* `fn` (by `get_fundef` over `lp_funcs P`),
  finds the label's pc in that function's body, and sets `(lfn, lpc) := (fn,
  pc+1)`. **Note the `pc.+1`**: control resumes at the instruction *after* the
  label. Our `evalJump` mirrors this exactly (including the `+1`).

* **`find_instr`** (Coq `linear_sem.v` l.94–96):
  ```
  Definition find_instr (s:lstate) :=
    let%opt fd := get_fundef (lp_funcs P) s.(lfn) in oseq.onth (lfd_body fd) s.(lpc).
  ```
  Look up the current function `lfn` in `lp_funcs P`, then the instruction at
  `lpc`. Our `findInstr` mirrors this.

* **`eval_instr`** (Coq `linear_sem.v` l.112–173), program-relevant arms:
  - `Lgoto d => eval_jump d s1`
  - `Lcond e lbl => Let b := sem_fexpr … in if b then eval_jump (lfn,lbl) s1 else lnext_pc s1`
  - `Lalign => lnext_pc s1`, `Llabel _ _ => lnext_pc s1`
  - `Lopn … => … lnext_pc …` (straight-line; delegated to increment 1)
  Our `evalInstrP` mirrors these. The boolean condition of `Lcond` is modeled as
  "the condition operand reads a non-zero word" (`evalOperand s cond ≠ 0`) — the
  faithful surface model of `sem_fexpr … >>= to_bool` for the comparison-register
  condition the backend's `Lcond NZ→top` emits.

* **`step`** (Coq `linear_sem.v` l.175–178):
  `step s = if find_instr s is Some i then eval_instr i s else type_error`.
  Our `lsemStepP P s` mirrors this.

* **`lsem1`/`lsem`** (Coq `linear_sem.v` l.180–183):
  `lsem1 s1 s2 := step s1 = ok s2`; `lsem := clos_refl_trans lstate lsem1`.
  We model `lsem` constructively as `∃ fuel, lsemFuel P fuel s1 = some s2`
  (fuel-bounded iteration of `lsemStepP`, short-circuiting on `none`/halt). This
  is the standard fuel encoding of the reflexive-transitive closure of a
  partial-function step relation (the same relation, exhibited by an explicit
  iteration count rather than a `clos_refl_trans` derivation).

## Modeling choices (trust-critical)

1. **Program context as a parameter, not a state field.** Coq's `Section
   Context (P : lprog)` makes `find_instr`/`step`/`eval_jump`/`lsem` all
   implicitly `P`-parametric. We thread `P : Lprog` as an explicit parameter of
   `findInstr`/`evalJump`/`lsemStepP`/`lsemFuel`/`lsem` (matching the `Section`
   variable). This keeps the state minimal and the dependence on `P` explicit.

2. **`lfn` lives on a new program-level state `LstateP`.** Increment 1's
   `Lstate` deliberately dropped Coq's `lfn` (current function name) because the
   straight-line fold never needs it. The program-indexed `find_instr` *does*
   (it indexes `lp_funcs` by `lfn`). Rather than mutate `Lstate`, we add a thin
   wrapper `LstateP` = `Lstate` + `lfn`, with `toLstate`/`ofLstate` coercions.
   The straight-line arms delegate to increment 1's `lsemStep` on the `Lstate`
   projection and then carry `lfn` through unchanged.

3. **Fuel + halting.** `lsemFuel P fuel s` iterates `lsemStepP P` up to `fuel`
   times, short-circuiting to `some s` when the machine has **halted**: a state
   is halted (Coq `lsem_final`, l.266–268) when `lpc` has reached the end of the
   current function's body (`find_instr` returns `none`). On an error
   (`find_instr` finds an instruction but `evalInstrP` returns `none` — an
   unmodeled op or a failed jump) `lsemFuel` returns `none`. Running out of fuel
   before halting also returns `none`. So `lsemFuel P fuel s = some t` means "the
   machine halted at `t` within `fuel` steps".

## Covered vs. deferred control-flow arms

* **Covered** (modeled faithfully): `Lgoto` (via `evalJump`), `Lcond` (condition
  + `evalJump`/`lnext_pc`), `Llabel` (pc bump, and as a `findLabel` target),
  `Lalign`, and all straight-line `Lopn` arms (delegated to increment 1).
* **Deferred** (`none`, out of scope — they read the whole-program
  label *encoding* table / memory / syscall oracle, increment 5+):
  `Lcall`, `Lret`, `Lsyscall`, `Ligoto`, `LstoreLabel`.

## Bridge: conservative extension of increment 1

`lsemFuel_straightline` proves that for a **jump-free** body (no `Lgoto`/`Lcond`
that ever leaves the straight-line path), `lsemFuel` with enough fuel agrees with
increment 1's `lsemStraight`. This is the lemma that makes 4a/4b a *conservative*
extension: every existing straight-line simulation over `lsemStraight` lifts to
the program-level `lsem`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-! ## 1. `find_label`: search a body for a label's pc

Mirror of Coq `find_label` (`linear.v` l.39–41) + `is_label` (l.32–36). -/

/-- `is_label lbl i` (Coq `linear.v` l.32–36): an instruction is the label `lbl`
    iff it is `Llabel _ lbl` for *either* label kind. -/
def isLabel (lbl : LLabel) (i : LinstrR) : Bool :=
  match i with
  | .Llabel _ lbl' => lbl == lbl'
  | _ => false

/-- `find_label lbl body` (Coq `linear.v` l.39–41): the pc of the first
    instruction in `body` that is `Llabel _ lbl`, or `none` (Coq `type_error`)
    when no such label exists. Coq computes `idx := seq.find (is_label lbl) body`
    and returns `ok idx` iff `idx < size body` — i.e. exactly when a matching
    label was found; `findIdx?` returns `none` in the no-match case, which is the
    `none`/`type_error` branch. -/
def findLabel (lbl : LLabel) (body : List LinstrR) : Option Nat :=
  body.findIdx? (isLabel lbl)

/-- **`find_label` soundness**: if `findLabel lbl body = some pc`, then the
    instruction at `pc` in `body` is a `Llabel _ lbl` (the label really is at the
    returned pc). The faithful analogue of the Coq fact that
    `is_label lbl (onth body idx)` holds at the index `seq.find` returns. -/
theorem findLabel_sound (lbl : LLabel) (body : List LinstrR) (pc : Nat)
    (h : findLabel lbl body = some pc) :
    ∃ k, body[pc]? = some k ∧ isLabel lbl k := by
  unfold findLabel at h
  have hlt : pc < body.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
  have hmatch := List.of_findIdx?_eq_some h
  refine ⟨body[pc]'hlt, List.getElem?_eq_getElem hlt, ?_⟩
  rw [List.getElem?_eq_getElem hlt] at hmatch
  simpa using hmatch

/-- The pc returned by `findLabel` is within the body (Coq's `idx < size c`
    guard). -/
theorem findLabel_lt_length (lbl : LLabel) (body : List LinstrR) (pc : Nat)
    (h : findLabel lbl body = some pc) : pc < body.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1

/-! ## 2. The program-level state `LstateP`

Increment 1's `Lstate` (lvm/lmem/lpc) plus Coq's `lfn` (current function name),
which the program-indexed `find_instr` needs. -/

/-- The program-level linear state: increment 1's `Lstate` plus the current
    function name `lfn` (Coq `lstate.lfn`). The state machinery is otherwise the
    increment-1 `Lstate`; `lfn` only indexes `find_instr`. -/
structure LstateP (w : Nat) where
  /-- The straight-line state (lvm/lmem/lpc). -/
  base : Lstate w
  /-- `lfn : funname` — the current function name (indexes `lp_funcs`). -/
  lfn : String

/-- `setcpc s fn pc` (Coq `linear_sem.v` l.52): set the function and pc. -/
def LstateP.setcpc {w : Nat} (s : LstateP w) (fn : String) (pc : Nat) : LstateP w :=
  { s with base := { s.base with lpc := pc }, lfn := fn }

/-- `lnext_pc` at the program level: advance the base pc, keep `lfn`. -/
def LstateP.nextPc {w : Nat} (s : LstateP w) : LstateP w :=
  { s with base := s.base.nextPc }

@[simp] theorem LstateP.base_nextPc {w : Nat} (s : LstateP w) :
    s.nextPc.base = s.base.nextPc := rfl

@[simp] theorem LstateP.lfn_nextPc {w : Nat} (s : LstateP w) : s.nextPc.lfn = s.lfn := rfl

@[simp] theorem LstateP.lpc_nextPc {w : Nat} (s : LstateP w) :
    s.nextPc.base.lpc = s.base.lpc + 1 := rfl

@[simp] theorem LstateP.base_setcpc {w : Nat} (s : LstateP w) (fn : String) (pc : Nat) :
    (s.setcpc fn pc).base = { s.base with lpc := pc } := rfl

@[simp] theorem LstateP.lfn_setcpc {w : Nat} (s : LstateP w) (fn : String) (pc : Nat) :
    (s.setcpc fn pc).lfn = fn := rfl

/-! ## 3. `get_fundef` / `find_instr`

Program lookup, faithful to Coq `get_fundef = assoc` and `find_instr`. -/

/-- `get_fundef (lp_funcs P) fn` (Coq `var.v` l.33–34, `= assoc`): look up the
    function body named `fn` in the program's function list. -/
def getFundef (P : Lprog) (fn : String) : Option Lfundef :=
  (P.lp_funcs.find? (fun p => p.1 == fn)).map Prod.snd

/-- `find_instr s` (Coq `linear_sem.v` l.94–96): the instruction at `lpc` in the
    current function's body, or `none` (machine halted / out of range / unknown
    function). -/
def findInstr (P : Lprog) {w : Nat} (s : LstateP w) : Option LinstrR :=
  match getFundef P s.lfn with
  | some fd => (fd.lfd_body[s.base.lpc]?).map Linstr.li_i
  | none => none

/-! ## 4. `eval_jump`: resolve a remote label and set `(lfn, lpc)`

Mirror of Coq `eval_jump` (`linear_sem.v` l.84–92). -/

/-- `eval_jump (fn, lbl) s` (Coq `linear_sem.v` l.84–92): resolve the target
    function `fn` in `P`, find label `lbl`'s pc in its body, and jump to the
    instruction **after** the label (`setcpc s fn (pc+1)`). `none` if the target
    function is unknown (Coq `type_error`) or the label is absent (Coq
    `find_label = type_error`). -/
def evalJump (P : Lprog) {w : Nat} (d : String × LLabel) (s : LstateP w) :
    Option (LstateP w) :=
  let (fn, lbl) := d
  match getFundef P fn with
  | some fd =>
      match findLabel lbl (fd.lfd_body.map Linstr.li_i) with
      | some pc => some (s.setcpc fn (pc + 1))
      | none => none
  | none => none

/-! ## 5. `eval_instr` (program arms) and the program `step`

Mirror of Coq `eval_instr` (`linear_sem.v` l.112–173) — the control-flow and
straight-line arms in scope — followed by `step` (l.175–178). The straight-line
and `Llabel`/`Lalign` arms delegate to increment 1's `lsemStep` (on the base
state), so the word-op model is shared verbatim. -/

/-- `eval_instr i s` restricted to the in-scope arms (Coq `linear_sem.v`
    l.112–173):

    * `Lgoto d` → `evalJump P d s` (Coq l.159).
    * `Lcond cond lbl` → if `cond` reads a non-zero word, `evalJump P (lfn,lbl) s`,
      else `lnext_pc s` (Coq l.168–172, modeling `sem_fexpr … >>= to_bool` as the
      non-zero-word test on the condition operand).
    * `Llabel`/`Lalign`/`Lopn …` (straight-line) → delegate to increment 1's
      `lsemStep` on the base state, then carry `lfn` through (these arms only
      touch lvm/lmem/lpc; `lsemStep` already does `lnext_pc`).

    Deferred (`none`): `Lcall`, `Lret`, `Lsyscall`, `Ligoto`,
    `LstoreLabel` (out of scope — read the label-encoding table / memory /
    syscall oracle). -/
def evalInstrP (P : Lprog) {w : Nat} (i : LinstrR) (s : LstateP w) :
    Option (LstateP w) :=
  match i with
  | .Lgoto d => evalJump P d s
  | .Lcond cond lbl =>
      if evalOperand s.base cond ≠ 0 then evalJump P (s.lfn, lbl) s
      else some s.nextPc
  -- straight-line + Llabel/Lalign: delegate to increment 1 on the base state.
  | .Lopn dsts opn srcs =>
      (lsemStep (.Lopn dsts opn srcs) s.base).map (fun b => { s with base := b })
  | .Llabel k l => (lsemStep (.Llabel k l) s.base).map (fun b => { s with base := b })
  | .Lalign => (lsemStep .Lalign s.base).map (fun b => { s with base := b })
  -- Deferred (out of scope for 4a/4b).
  | .Ligoto _ => none
  | .Lcall _ _ => none
  | .Lret => none
  | .LstoreLabel _ _ => none
  | .Lsyscall _ => none

/-- `step s` (Coq `linear_sem.v` l.175–178): fetch the instruction at `lpc` via
    `find_instr`, then `eval_instr` it. `none` when there is no instruction (the
    machine has halted — Coq `step = type_error` on `find_instr = None`, which is
    the terminal/`lsem_final` case rather than an error). -/
def lsemStepP (P : Lprog) {w : Nat} (s : LstateP w) : Option (LstateP w) :=
  match findInstr P s with
  | some i => evalInstrP P i s
  | none => none

/-- `lsem1 P s1 s2` (Coq `linear_sem.v` l.180–181): `step s1 = ok s2`. -/
def lsem1P (P : Lprog) {w : Nat} (s1 s2 : LstateP w) : Prop := lsemStepP P s1 = some s2

/-- `lsem1` is deterministic — the program step is a function (Coq `lsem1_fun`,
    `linear_sem.v` l.226–232). -/
theorem lsem1P_deterministic (P : Lprog) {w : Nat} (s1 s2 s3 : LstateP w)
    (h12 : lsem1P P s1 s2) (h13 : lsem1P P s1 s3) : s2 = s3 := by
  rw [lsem1P] at h12 h13; rw [h12] at h13; exact Option.some.inj h13

/-! ## 6. `lsemFuel` / `lsem`: fuel-bounded iteration and its closure

`lsemFuel` iterates `lsemStepP` up to `fuel` times, **halting** (returning the
current state) when `findInstr` returns `none` (Coq `lsem_final`: lpc past the
body end). `lsem P s t := ∃ fuel, lsemFuel P fuel s = some t` is the constructive
encoding of Coq's `clos_refl_trans lstate lsem1`. -/

/-- `lsemFuel P fuel s`: iterate the program step up to `fuel` times.

    * If the machine has **halted** at `s` (`findInstr P s = none`, i.e. `lpc` is
      past the end of the current body — Coq `lsem_final`), return `some s`
      (reflexive/terminal).
    * Otherwise, if `lsemStepP P s = some s'`, recurse with one less fuel.
    * On an error (`findInstr` finds an instruction but `evalInstrP`
      returns `none`) or fuel exhaustion before halting, return `none`. -/
def lsemFuel (P : Lprog) {w : Nat} : Nat → LstateP w → Option (LstateP w)
  | 0, s => match findInstr P s with
            | none => some s   -- already halted: terminal
            | some _ => none   -- still running but out of fuel
  | fuel + 1, s =>
      match findInstr P s with
      | none => some s         -- halted (Coq lsem_final)
      | some i =>
          match evalInstrP P i s with
          | some s' => lsemFuel P fuel s'
          | none => none

/-- `lsem P s1 s2` (Coq `lsem := clos_refl_trans lstate lsem1`, `linear_sem.v`
    l.183): there is some fuel for which `lsemFuel` drives `s1` to a halted `s2`.
    The constructive (fuel-witnessed) encoding of the reflexive-transitive
    closure of the deterministic program step `lsem1`. -/
def lsem (P : Lprog) {w : Nat} (s1 s2 : LstateP w) : Prop :=
  ∃ fuel, lsemFuel P fuel s1 = some s2

/-! ## 7. Determinism and monotonicity of `lsemFuel` -/

/-- **Determinism**: same fuel ⇒ same result. Immediate, since `lsemFuel` is a
    function. (The analogue of Coq `lsem1_fun` lifted to the iteration.) -/
theorem lsemFuel_deterministic (P : Lprog) {w : Nat} (fuel : Nat) (s t1 t2 : LstateP w)
    (h1 : lsemFuel P fuel s = some t1) (h2 : lsemFuel P fuel s = some t2) : t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-- A halted state (`findInstr = none`) takes no step: `lsemFuel` returns it
    unchanged at every fuel (Coq `lsem_final_nostep` / `lsem_final_stutter`,
    `linear_sem.v` l.270–285). -/
theorem lsemFuel_halt (P : Lprog) {w : Nat} (fuel : Nat) (s : LstateP w)
    (h : findInstr P s = none) : lsemFuel P fuel s = some s := by
  cases fuel with
  | zero => simp [lsemFuel, h]
  | succ n => simp [lsemFuel, h]

/-- **Monotonicity**: once `lsemFuel` reaches a (halted) result with some fuel,
    any larger fuel reaches the *same* result. The Coq fact that the terminal
    state is a fixpoint of `step` (`lsem_final_stutter`), so extra fuel is a
    no-op. -/
theorem lsemFuel_mono (P : Lprog) {w : Nat} :
    ∀ (fuel : Nat) (s t : LstateP w),
      lsemFuel P fuel s = some t → lsemFuel P (fuel + 1) s = some t := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      rw [lsemFuel] at h
      cases hf : findInstr P s with
      | none =>
          rw [hf] at h
          have hst : s = t := Option.some.inj h
          subst hst
          exact lsemFuel_halt P 1 s hf
      | some i => rw [hf] at h; exact absurd h (by simp)
  | succ n ih =>
      intro s t h
      rw [lsemFuel] at h
      rw [lsemFuel]
      cases hf : findInstr P s with
      | none => rw [hf] at h; exact h
      | some i =>
          rw [hf] at h
          simp only [] at h ⊢
          cases he : evalInstrP P i s with
          | none => rw [he] at h; exact absurd h (by simp)
          | some s' => rw [he] at h; exact ih s' t h

/-- More fuel never changes a reached result: `lsemFuel P fuel s = some t`
    implies `lsemFuel P (fuel + k) s = some t` for every `k`. -/
theorem lsemFuel_mono_add (P : Lprog) {w : Nat} (fuel : Nat) (s t : LstateP w)
    (h : lsemFuel P fuel s = some t) : ∀ k, lsemFuel P (fuel + k) s = some t := by
  intro k
  induction k with
  | zero => simpa using h
  | succ n ih =>
      have : fuel + (n + 1) = (fuel + n) + 1 := by omega
      rw [this]
      exact lsemFuel_mono P (fuel + n) s t ih

/-! ## 8. Bridge: straight-line consistency (conservative extension)

For a **jump-free** body — one with no `Lgoto`/`Lcond` (so control flow stays on
the straight-line path) and whose only `Llabel`s are inert markers — the
program-level `lsemFuel` agrees with increment 1's `lsemStraight`. This makes
4a/4b a conservative extension: straight-line simulations over `lsemStraight`
lift to `lsem`.

We state the bridge over a single-function program whose body is exactly the
list `body`, executed from `lpc = 0`. The key is that `evalInstrP` on a
non-jump instruction equals increment 1's `lsemStep` on the base state (carrying
`lfn`), and the program `step` fetches instructions sequentially because every
non-jump arm advances `lpc` by one. -/

/-- A `LinstrR` is **jump-free** (stays on the straight-line path): not a
    control-transfer / deferred arm. The `evalInstrP` of such an instruction is
    increment 1's `lsemStep` on the base state. -/
def IsStraightLine (i : LinstrR) : Bool :=
  match i with
  | .Lopn _ _ _ => true
  | .Llabel _ _ => true
  | .Lalign => true
  | _ => false

/-- On a jump-free instruction, `evalInstrP` is increment 1's `lsemStep` lifted
    over the base state (carrying `lfn` unchanged). The per-instruction fidelity
    tie between the program layer and the straight-line foundation. -/
theorem evalInstrP_straightLine (P : Lprog) {w : Nat} (i : LinstrR) (s : LstateP w)
    (hi : IsStraightLine i) :
    evalInstrP P i s = (lsemStep i s.base).map (fun b => { s with base := b }) := by
  cases i <;> simp_all [IsStraightLine, evalInstrP]

/-- A single program-build helper: the one-function program whose sole function
    `fn` has body `body`. Used to state the straight-line bridge. -/
def singletonProg (fn : String) (body : List LinstrR) : Lprog :=
  { lp_funcs := [(fn, { lfd_body := body.map (fun ir => ⟨0, ir⟩) })] }

@[simp] theorem getFundef_singleton (fn : String) (body : List LinstrR) :
    getFundef (singletonProg fn body) fn =
      some { lfd_body := body.map (fun ir => ⟨0, ir⟩) } := by
  simp [getFundef, singletonProg]

/-- `findInstr` on a singleton program reads the `pc`-th element of `body`. -/
theorem findInstr_singleton (fn : String) (body : List LinstrR) {w : Nat}
    (s : LstateP w) (hfn : s.lfn = fn) :
    findInstr (singletonProg fn body) s = body[s.base.lpc]? := by
  rw [findInstr, hfn, getFundef_singleton]
  show Option.map Linstr.li_i (List.map (fun ir => (⟨0, ir⟩ : Linstr)) body)[s.base.lpc]?
      = body[s.base.lpc]?
  rw [List.getElem?_map, Option.map_map]
  cases body[s.base.lpc]? with
  | none => rfl
  | some ir => rfl

/-- Every successful straight-line `lsemStep` advances the pc by exactly one
    (`lnext_pc`): if `lsemStep i s = some b` for a jump-free `i`, then
    `b.lpc = s.lpc + 1`. The `lnext_pc` invariant the program/straight-line
    lockstep relies on. -/
theorem lsemStep_lpc_succ {w : Nat} (i : LinstrR) (s b : Lstate w)
    (hi : IsStraightLine i) (h : lsemStep i s = some b) : b.lpc = s.lpc + 1 := by
  cases i with
  | Lopn dsts opn srcs =>
      cases dsts with
      | nil => simp [lsemStep] at h
      | cons d ds =>
          cases d with
          | reg dst =>
              cases ds with
              | cons _ _ => simp [lsemStep] at h
              | nil =>
                  cases srcs with
                  | nil =>
                      simp only [lsemStep] at h
                      cases happ : applyOpn (stripWidthTag opn)
                          (List.map (evalOperand s) ([] : List LOperand)) with
                      | none => rw [happ] at h; simp at h
                      | some v =>
                          rw [happ] at h
                          simp only [Option.some.injEq] at h
                          rw [← h]; rfl
                  | cons hd rest =>
                      cases hd with
                      | reg r =>
                          rw [lsemStep_reg_srcs dst opn (LOperand.reg r :: rest) s
                            (by intro b i sc rst; simp)] at h
                          cases happ : applyOpn (stripWidthTag opn)
                              (List.map (evalOperand s) (LOperand.reg r :: rest)) with
                          | none => rw [happ] at h; simp at h
                          | some v =>
                              rw [happ] at h
                              simp only [Option.some.injEq] at h
                              rw [← h]; rfl
                      | imm im =>
                          rw [lsemStep_reg_srcs dst opn (LOperand.imm im :: rest) s
                            (by intro b i sc rst; simp)] at h
                          cases happ : applyOpn (stripWidthTag opn)
                              (List.map (evalOperand s) (LOperand.imm im :: rest)) with
                          | none => rw [happ] at h; simp at h
                          | some v =>
                              rw [happ] at h
                              simp only [Option.some.injEq] at h
                              rw [← h]; rfl
                      | arr a o =>
                          rw [lsemStep_reg_srcs dst opn (LOperand.arr a o :: rest) s
                            (by intro b i sc rst; simp)] at h
                          cases happ : applyOpn (stripWidthTag opn)
                              (List.map (evalOperand s) (LOperand.arr a o :: rest)) with
                          | none => rw [happ] at h; simp at h
                          | some v =>
                              rw [happ] at h
                              simp only [Option.some.injEq] at h
                              rw [← h]; rfl
                      | arrIdx base idx scale =>
                          simp only [lsemStep] at h
                          by_cases hL : opn = "LOADIDX"
                          · rw [if_pos hL] at h
                            simp only [Option.some.injEq] at h
                            rw [← h]; rfl
                          · rw [if_neg hL] at h
                            by_cases hS : opn = "STOREIDX"
                            · rw [if_pos hS] at h
                              cases rest with
                              | nil => simp at h
                              | cons val vrest =>
                                  cases vrest with
                                  | nil =>
                                      simp only [Option.some.injEq] at h
                                      rw [← h]; rfl
                                  | cons _ _ => simp at h
                            · rw [if_neg hS] at h
                              cases happ : applyOpn (stripWidthTag opn)
                                  (List.map (evalOperand s)
                                    (LOperand.arrIdx base idx scale :: rest)) with
                              | none => rw [happ] at h; simp at h
                              | some v =>
                                  rw [happ] at h
                                  simp only [Option.some.injEq] at h
                                  rw [← h]; rfl
          | imm _ => simp [lsemStep] at h
          | arr _ _ => simp [lsemStep] at h
          | arrIdx _ _ _ => simp [lsemStep] at h
  | Lalign => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Llabel k l => simp only [lsemStep, Option.some.injEq] at h; rw [← h]; rfl
  | Lgoto _ => simp [IsStraightLine] at hi
  | Lcond _ _ => simp [IsStraightLine] at hi
  | Ligoto _ => simp [IsStraightLine] at hi
  | Lcall _ _ => simp [IsStraightLine] at hi
  | Lret => simp [IsStraightLine] at hi
  | LstoreLabel _ _ => simp [IsStraightLine] at hi
  | Lsyscall _ => simp [IsStraightLine] at hi

/-- `findInstr` past the end of a singleton body is `none` (the machine has
    halted — Coq `lsem_final`). -/
theorem findInstr_singleton_halt (fn : String) (body : List LinstrR) {w : Nat}
    (s : LstateP w) (hfn : s.lfn = fn) (hpc : body.length ≤ s.base.lpc) :
    findInstr (singletonProg fn body) s = none := by
  rw [findInstr_singleton fn body s hfn]
  exact List.getElem?_eq_none hpc

/-- **Straight-line consistency (suffix form).** Executing an all-straight-line
    `suffix` of a singleton program's `body` via the program-level `lsemFuel`
    (from the program position `body.length - suffix.length`, with exactly
    `suffix.length` fuel) agrees with increment 1's `lsemStraight` over that
    suffix on the base state — provided every step advances the program counter
    in lockstep with `lsemStraight`'s implicit `lnext_pc`.

    The invariant threaded through the induction: the program's `lpc` equals the
    length of the already-executed prefix (`pre.length`), so `findInstr` fetches
    exactly the next suffix instruction, and `evalInstrP` reduces (via
    `evalInstrP_straightLine`) to `lsemStep` on the base — advancing `lpc` by one
    and re-establishing the invariant for the tail. -/
theorem lsemFuel_straightline_suffix (fn : String) {w : Nat}
    (pre suffix : List LinstrR)
    (hsl : ∀ i ∈ suffix, IsStraightLine i) :
    ∀ (s : LstateP w), s.lfn = fn → s.base.lpc = pre.length →
      lsemFuel (singletonProg fn (pre ++ suffix)) suffix.length s
        = (lsemStraight suffix s.base).map (fun b => { s with base := b }) := by
  induction suffix generalizing pre with
  | nil =>
      intro s hfn hpc
      -- zero fuel; the program is at lpc = pre.length = (pre++[]).length, so halted.
      simp only [lsemFuel, lsemStraight_nil, Option.map_some]
      have hhalt : findInstr (singletonProg fn (pre ++ [])) s = none := by
        apply findInstr_singleton_halt fn (pre ++ []) s hfn
        simp [hpc]
      rw [hhalt]
  | cons i is ih =>
      intro s hfn hpc
      have hi : IsStraightLine i := hsl i (by simp)
      have his : ∀ j ∈ is, IsStraightLine j := fun j hj => hsl j (by simp [hj])
      -- fetch: the instruction at lpc = pre.length is `i`.
      have hfetch : findInstr (singletonProg fn (pre ++ i :: is)) s = some i := by
        rw [findInstr_singleton fn (pre ++ i :: is) s hfn, hpc]
        simp
      rw [List.length_cons, lsemFuel, hfetch]
      simp only []
      rw [evalInstrP_straightLine _ i s hi]
      -- now case on the straight-line step.
      cases hstep : lsemStep i s.base with
      | none =>
          simp only [Option.map_none]
          rw [lsemStraight_cons, hstep]
          rfl
      | some b =>
          simp only [Option.map_some]
          rw [lsemStraight_cons, hstep]
          -- the tail state: base := b, lpc advanced to pre.length + 1.
          have hb_lpc : b.lpc = (pre ++ [i]).length := by
            rw [lsemStep_lpc_succ i s.base b hi hstep, hpc]; simp
          have htail :
              lsemFuel (singletonProg fn ((pre ++ [i]) ++ is)) is.length
                  { s with base := b }
                = (lsemStraight is b).map (fun b' => { s with base := b' }) := by
            have := ih (pre ++ [i]) his { s with base := b } hfn hb_lpc
            simpa using this
          rw [show pre ++ i :: is = (pre ++ [i]) ++ is by simp] at *
          rw [htail]

/-- **Straight-line consistency (the bridge).** For a **jump-free** `body` (every
    instruction `IsStraightLine`), the program-level `lsemFuel` over the singleton
    program with that body, run from `lpc = 0` with `body.length` fuel, agrees
    with increment 1's `lsemStraight body`. This is the conservative-extension
    bridge: every existing straight-line simulation over `lsemStraight` lifts to
    the program-level `lsem` of increment 4a/4b. -/
theorem lsemFuel_straightline (fn : String) {w : Nat} (body : List LinstrR)
    (hsl : ∀ i ∈ body, IsStraightLine i) (s : LstateP w)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0) :
    lsemFuel (singletonProg fn body) body.length s
      = (lsemStraight body s.base).map (fun b => { s with base := b }) := by
  have := lsemFuel_straightline_suffix fn [] body hsl s hfn (by simpa using hpc)
  simpa using this

/-- The bridge as a `lsem` statement: a jump-free body's straight-line execution
    is a `lsem` derivation (some fuel drives `s` to the folded state). -/
theorem lsem_of_straightline (fn : String) {w : Nat} (body : List LinstrR)
    (hsl : ∀ i ∈ body, IsStraightLine i) (s t : LstateP w)
    (hfn : s.lfn = fn) (hpc : s.base.lpc = 0)
    (hstraight : lsemStraight body s.base = some t.base)
    (htfn : t.lfn = s.lfn) :
    lsem (singletonProg fn body) s t := by
  refine ⟨body.length, ?_⟩
  rw [lsemFuel_straightline fn body hsl s hfn hpc, hstraight]
  simp only [Option.map_some]
  cases t with
  | mk tbase tlfn =>
      cases s with
      | mk sbase slfn =>
          simp only at hstraight htfn ⊢
          subst htfn
          rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
