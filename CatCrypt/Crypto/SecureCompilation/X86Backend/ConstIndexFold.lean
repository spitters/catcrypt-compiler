/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# Constant-index folding of register-indexed loads and stores

`Com.toLprogPhysAbi` exports a table read at an index bound in the body as the
register-indexed form `LOADIDX [.arrIdx B x 8]`, rendered
`movq (%B,%x,8), %d`, even when `x` holds a literal. This module gives an opt-in
`Lprog → Lprog` pass that rewrites such a load (and the matching `STOREIDX`) to
the compile-time-displacement form `LOAD [.arr B (8·k)]` (`STORE [.arr B (8·k), v]`)
whenever a forward analysis knows that `x` holds `k`.

## The machine model

The value semantics is `Jasmin.runBlock` over the `JInstr 64` gather, the model
`MachineConstantTime.blockLeak` is stated over. `gatherPrinted` is
`GatherImmForms.gatherJBlock6` with one arm changed: a register rebind
`SHL:0:64 [d] [s]` with `d ≠ s` lowers to `mov d, s`, which is what
`LprogAsmPrinter` prints for it. `gatherJBlock6` lowers the same instruction to
`shl d, $0`, which keeps the old value of `d`; the front emits one such rebind per
scalar binding, and the constant index reaches the load register through one.

## The analysis

`KEnv` maps register names to known 64-bit values. `stepK` updates it across one
gathered instruction: an immediate `mov` records its constant, a register `mov`
copies a known value, a memory load forgets its destination, a memory store keeps
everything, and every other instruction forgets everything. `foldCore` threads the
environment through the body, reading the gathered block of each instruction.

## Main results

* `evalInstr_loadMemIdx_const`, `evalInstr_storeMemIdx_const`: an indexed access
  whose index register holds `v` is the direct access at displacement
  `scale · v`.
* `gatherPrinted_constIndexFoldBody`: the folded body gathers whenever the input
  does, and its block runs to the same machine state from every initial state.
* `constIndexFoldBody_lcmdDirect`: if every register-indexed instruction of the
  body is foldable (`Covers`) and the frame guard holds, the folded body is
  `lcmdDirect`; `gatherPrinted_constIndexFoldBody_constant_time` then gives the
  machine constant-time property of its gathered block.
* `spellLprog`: the printable spelling of the folded forms as the `mem.<B>.<off>`
  `MOVQ` operands that `LprogAsmPrinter` and `LprogBytes` render and encode.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (lowerCov6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 qsaveBytesFor)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave isGpName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (linstrRDirect lcmdDirect lcmdDirect_iff lowerCov6_direct mapM_flatten_direct)

/-! ## 1. The gather with printed register rebinds -/

/-- Lower one instruction: a register rebind `SHL:0:64 [d] [s]` between two
    register names is `mov d, s` (nothing when `d = s`); every other instruction
    is lowered by `lowerCov6`. -/
def lowerPrinted (frame spillW qsaveB : Nat) : LinstrR → Option (List (JInstr 64))
  | .Lopn [.reg d] "SHL:0:64" [.reg s] =>
      if isSpillOrQsave d || isSpillOrQsave s then
        lowerCov6 frame spillW (.Lopn [.reg d] "SHL:0:64" [.reg s]) qsaveB
      else if d = s then some [] else some [.mov d (.reg s)]
  | i => lowerCov6 frame spillW i qsaveB

/-- The frame parameters `gatherJBlock6` reads off a body: frame size, spill
    width, qsave block size. -/
def bodyParams (body : Lcmd) : Nat × Nat × Nat :=
  (frameSize body, if bodyIsU64 body then 64 else 32, qsaveBytesFor body)

/-- `gatherJBlock6` with `lowerPrinted` in place of `lowerCov6`. -/
def gatherPrinted (body : Lcmd) : Option (List (JInstr 64)) :=
  let p := bodyParams body
  ((body.filter (fun i => !isLret i)).mapM
    (fun i => lowerPrinted p.1 p.2.1 p.2.2 i.li_i)).map List.flatten

theorem lowerPrinted_direct {frame spillW qsaveB : Nat} {i : LinstrR}
    {js : List (JInstr 64)} (hi : linstrRDirect i = true)
    (h : lowerPrinted frame spillW qsaveB i = some js) : allDirect js = true := by
  unfold lowerPrinted at h
  split at h
  · split at h
    · exact lowerCov6_direct hi h
    · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact AllocCTPreservation.allDirect_of_forall
          (by simp [MachineConstantTime.IsDirect])
  · exact lowerCov6_direct hi h

/-- The printed gather of an index-free body is `allDirect`. -/
theorem gatherPrinted_allDirect {body : Lcmd} {g : List (JInstr 64)}
    (hd : lcmdDirect body = true) (h : gatherPrinted body = some g) :
    allDirect g = true := by
  simp only [gatherPrinted, Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, rfl⟩ := h
  refine mapM_flatten_direct (f := fun i => lowerPrinted _ _ _ i.li_i) ?_ _ ?_ ls hls
  · intro i hi js hj
    exact lowerPrinted_direct hi hj
  · intro i hi
    exact (lcmdDirect_iff body).mp hd i (List.mem_of_mem_filter hi)

/-! ## 2. The lowered forms of the indexed and the direct accesses -/

theorem lowerPrinted_loadIdx (frame spillW qsaveB : Nat) (d B x : String) (sc : Nat) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "LOADIDX" [.arrIdx B x sc])
      = some [.loadMemIdx d B x sc] := rfl

theorem lowerPrinted_load (frame spillW qsaveB : Nat) (d B : String) (off : Nat) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "LOAD" [.arr B off])
      = some [.loadMem d B off] := rfl

theorem lowerPrinted_storeIdx (frame spillW qsaveB : Nat) (d B x : String) (sc : Nat)
    (v : LOperand) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, v])
      = some [.storeMemIdx B x sc (LoweringExtended.lowerJOperand v)] := rfl

theorem lowerPrinted_store (frame spillW qsaveB : Nat) (d B : String) (off : Nat)
    (v : LOperand) :
    lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "STORE" [.arr B off, v])
      = some [.storeMem B off (LoweringExtended.lowerJOperand v)] := rfl

/-! ## 3. One access at a known index -/

/-- An indexed load whose index register holds `v` is the direct load at
    displacement `sc · v`. -/
theorem evalInstr_loadMemIdx_const (s : JState 64) (d B x : String) (sc : Nat)
    {v : BitVec 64} (h : s.get x = v) :
    evalInstr s (.loadMemIdx d B x sc) = evalInstr s (.loadMem d B ((sc * v.toNat : Nat) : Int)) := by
  simp only [evalInstr, JState.loadIdx, h, Nat.cast_mul]

/-- An indexed store whose index register holds `v` is the direct store at
    displacement `sc · v`. -/
theorem evalInstr_storeMemIdx_const (s : JState 64) (B x : String) (sc : Nat)
    (src : JOperand) {v : BitVec 64} (h : s.get x = v) :
    evalInstr s (.storeMemIdx B x sc src)
      = evalInstr s (.storeMem B ((sc * v.toNat : Nat) : Int) src) := by
  simp only [evalInstr, JState.storeIdx, h, Nat.cast_mul]

/-! ## 4. The known-register analysis -/

/-- Registers with a known 64-bit value; the first entry for a name wins. -/
abbrev KEnv : Type := List (String × BitVec 64)

/-- The known value of register `r`. -/
def KEnv.find : KEnv → String → Option (BitVec 64)
  | [], _ => none
  | (a, v) :: t, r => if a = r then some v else KEnv.find t r

/-- Forget register `r`. -/
def KEnv.kill (env : KEnv) (r : String) : KEnv := env.filter (fun p => !(p.1 == r))

/-- Every recorded value is the value of its register in `s`. -/
def KEnv.Holds (s : JState 64) (env : KEnv) : Prop :=
  ∀ r v, env.find r = some v → s.get r = v

theorem KEnv.find_kill (env : KEnv) (d r : String) :
    (env.kill d).find r = if d = r then none else env.find r := by
  induction env with
  | nil => simp [KEnv.kill, KEnv.find]
  | cons p t ih =>
      obtain ⟨a, v⟩ := p
      by_cases had : a = d
      · subst had
        have hk : KEnv.kill ((a, v) :: t) a = KEnv.kill t a := by
          simp [KEnv.kill]
        rw [hk, ih]
        by_cases har : a = r <;> simp [KEnv.find, har]
      · have hk : KEnv.kill ((a, v) :: t) d = (a, v) :: KEnv.kill t d := by
          simp [KEnv.kill, had]
        rw [hk]
        simp only [KEnv.find]
        rw [ih]
        by_cases hdr : d = r
        · subst hdr; simp [had]
        · simp [hdr]

theorem KEnv.Holds.nil (s : JState 64) : KEnv.Holds s [] := by
  intro r v h; simp [KEnv.find] at h

theorem JState.get_setReg' (s : JState 64) (d r : String) (w : BitVec 64) :
    (s.setReg d w).get r = if r = d then w else s.get r := by
  simp [JState.setReg]

theorem KEnv.Holds.setReg_kill {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (d : String) (w : BitVec 64) : KEnv.Holds (s.setReg d w) (env.kill d) := by
  intro r v hr
  rw [KEnv.find_kill] at hr
  rw [JState.get_setReg']
  by_cases hdr : d = r
  · simp [hdr] at hr
  · rw [if_neg hdr] at hr
    rw [if_neg (Ne.symm hdr)]
    exact h r v hr

theorem KEnv.Holds.setReg_cons {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (d : String) (w : BitVec 64) : KEnv.Holds (s.setReg d w) ((d, w) :: env.kill d) := by
  intro r v hr
  simp only [KEnv.find] at hr
  by_cases hdr : d = r
  · subst hdr
    simp only [if_true, Option.some.injEq] at hr
    subst hr
    simp [JState.setReg]
  · rw [if_neg hdr] at hr
    exact h.setReg_kill d w r v hr

/-- The analysis step across one gathered instruction. -/
def stepK (env : KEnv) : JInstr 64 → KEnv
  | .mov d (.imm k) => (d, BitVec.ofNat 64 k) :: env.kill d
  | .mov d (.reg x) =>
      match env.find x with
      | some v => (d, v) :: env.kill d
      | none => env.kill d
  | .loadMem d _ _ => env.kill d
  | .loadMemIdx d _ _ _ => env.kill d
  | .storeMem _ _ _ => env
  | .storeMemIdx _ _ _ _ => env
  | _ => []

/-- The analysis step across a gathered block. -/
def stepKs (env : KEnv) (js : List (JInstr 64)) : KEnv := js.foldl stepK env

theorem KEnv.Holds.stepK {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (i : JInstr 64) : KEnv.Holds (evalInstr s i) (ConstIndexFold.stepK env i) := by
  cases i with
  | mov d src =>
      cases src with
      | imm k => exact h.setReg_cons d _
      | reg x =>
          simp only [ConstIndexFold.stepK, evalInstr]
          cases hx : env.find x with
          | none => exact h.setReg_kill d _
          | some v =>
              have hv : (JOperand.reg x).eval s = v := h x v hx
              rw [hv]
              exact h.setReg_cons d v
  | loadMem d _ _ => exact h.setReg_kill d _
  | loadMemIdx d _ _ _ => exact h.setReg_kill d _
  | storeMem B off src =>
      intro r v hr
      exact h r v hr
  | storeMemIdx B x sc src =>
      intro r v hr
      exact h r v hr
  | _ => exact KEnv.Holds.nil _

theorem runBlock_append' (s : JState 64) (l₁ l₂ : List (JInstr 64)) :
    runBlock s (l₁ ++ l₂) = runBlock (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

theorem KEnv.Holds.stepKs {s : JState 64} {env : KEnv} (h : KEnv.Holds s env)
    (js : List (JInstr 64)) : KEnv.Holds (runBlock s js) (ConstIndexFold.stepKs env js) := by
  induction js generalizing s env with
  | nil => exact h
  | cons i is ih => exact ih (h.stepK i)

/-! ## 5. The fold -/

/-- The fold applies to a 64-bit (`scale = 8`) access through a tabulated GP base
    whose displacement fits a signed 32-bit field. -/
def foldOK (B : String) (sc : Nat) (v : BitVec 64) : Bool :=
  sc == 8 && isGpName B && decide (sc * v.toNat < 2 ^ 31)

/-- The direct form of an indexed load or store whose index register is known
    in `env`; `none` for every other instruction. -/
def foldTarget? (env : KEnv) : LinstrR → Option LinstrR
  | .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc] =>
      match env.find x with
      | some v =>
          if foldOK B sc v then some (.Lopn [.reg d] "LOAD" [.arr B (sc * v.toNat)])
          else none
      | none => none
  | .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn] =>
      match env.find x with
      | some v =>
          if foldOK B sc v then
            some (.Lopn [.reg d] "STORE" [.arr B (sc * v.toNat), .reg vn])
          else none
      | none => none
  | _ => none

/-- Rewrite one instruction under `env`. -/
def foldInstr (env : KEnv) (i : LinstrR) : LinstrR := (foldTarget? env i).getD i

/-- The environment after instruction `i`: the analysis step across its gathered
    block, and the empty environment after a return or an instruction the gather
    does not lower. -/
def nextEnv (p : Nat × Nat × Nat) (env : KEnv) (i : Linstr) : KEnv :=
  if isLret i then []
  else
    match lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
    | some js => stepKs env js
    | none => []

/-- The fold over a body at frame parameters `p`, from environment `env`. -/
def foldCore (p : Nat × Nat × Nat) : KEnv → Lcmd → Lcmd
  | _, [] => []
  | env, i :: is => { i with li_i := foldInstr env i.li_i } :: foldCore p (nextEnv p env i) is

/-- The fold of a body: `foldCore` at the body's own frame parameters, kept only
    when the folded body has the same frame parameters. -/
def constIndexFoldBody (body : Lcmd) : Lcmd :=
  let b' := foldCore (bodyParams body) [] body
  if bodyParams b' = bodyParams body then b' else body

/-- The fold applied to every function of a program. -/
def constIndexFold (lp : Lprog) : Lprog :=
  let fs := lp.lp_funcs.map
    (fun f => (f.1, { f.2 with lfd_body := constIndexFoldBody f.2.lfd_body }))
  { lp with lp_funcs := fs }

/-- Every register-indexed instruction of the body is folded: each instruction is
    index-free or has a direct form under the environment reaching it. -/
def covers (p : Nat × Nat × Nat) : KEnv → Lcmd → Bool
  | _, [] => true
  | env, i :: is =>
      (linstrRDirect i.li_i || (foldTarget? env i.li_i).isSome) && covers p (nextEnv p env i) is

theorem foldTarget?_spec {env : KEnv} {i i' : LinstrR} (h : foldTarget? env i = some i') :
    (∃ d B x sc v, i = .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc]
        ∧ i' = .Lopn [.reg d] "LOAD" [.arr B (sc * v.toNat)] ∧ env.find x = some v)
    ∨ (∃ d B x sc vn v, i = .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn]
        ∧ i' = .Lopn [.reg d] "STORE" [.arr B (sc * v.toNat), .reg vn]
        ∧ env.find x = some v) := by
  unfold foldTarget? at h
  split at h
  · left
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, _, _, _, _, rfl, h.symm, by assumption⟩
      · simp at h
    · simp at h
  · right
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨_, _, _, _, _, _, rfl, h.symm, by assumption⟩
      · simp at h
    · simp at h
  · simp at h

theorem foldTarget?_direct {env : KEnv} {i i' : LinstrR} (h : foldTarget? env i = some i') :
    linstrRDirect i' = true := by
  rcases foldTarget?_spec h with ⟨_, _, _, _, _, -, rfl, -⟩ | ⟨_, _, _, _, _, _, -, rfl, -⟩ <;>
    simp [linstrRDirect, AllocCTPreservation.isIndexed]

theorem isLret_foldInstr (env : KEnv) (i : Linstr) :
    isLret { i with li_i := foldInstr env i.li_i } = isLret i := by
  unfold foldInstr
  cases h : foldTarget? env i.li_i with
  | none => rfl
  | some i' =>
      rcases foldTarget?_spec h with ⟨_, _, _, _, _, hi, rfl, -⟩ | ⟨_, _, _, _, _, _, hi, rfl, -⟩ <;>
        simp [isLret, hi]

/-- A folded instruction lowers to a block that runs like the original block from
    every state the environment describes. -/
theorem foldInstr_lower (p : Nat × Nat × Nat) {env : KEnv} {i : LinstrR}
    {js : List (JInstr 64)} (h : lowerPrinted p.1 p.2.1 p.2.2 i = some js) :
    ∃ js', lowerPrinted p.1 p.2.1 p.2.2 (foldInstr env i) = some js'
      ∧ ∀ s, KEnv.Holds s env → runBlock s js' = runBlock s js := by
  unfold foldInstr
  cases hf : foldTarget? env i with
  | none => exact ⟨js, h, fun _ _ => rfl⟩
  | some i' =>
      rcases foldTarget?_spec hf with
        ⟨d, B, x, sc, v, rfl, rfl, hx⟩ | ⟨d, B, x, sc, vn, v, rfl, rfl, hx⟩
      · rw [lowerPrinted_loadIdx] at h
        cases h
        refine ⟨_, lowerPrinted_load _ _ _ d B _, fun s hs => ?_⟩
        simp only [runBlock_cons, runBlock_nil]
        exact (evalInstr_loadMemIdx_const s d B x sc (hs x v hx)).symm
      · rw [lowerPrinted_storeIdx] at h
        cases h
        refine ⟨_, lowerPrinted_store _ _ _ d B _ _, fun s hs => ?_⟩
        simp only [runBlock_cons, runBlock_nil]
        exact (evalInstr_storeMemIdx_const s B x sc _ (hs x v hx)).symm

/-- The lowering applied to the non-return instructions of a body. -/
abbrev gatherList (p : Nat × Nat × Nat) (body : Lcmd) : Option (List (List (JInstr 64))) :=
  (body.filter (fun i => !isLret i)).mapM (fun i => lowerPrinted p.1 p.2.1 p.2.2 i.li_i)

/-- **Block agreement at fixed frame parameters.** If the body gathers, the folded
    body gathers, and from every state the environment describes the two blocks
    run to the same machine state. -/
theorem foldCore_gather (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (env : KEnv) (s : JState 64) (ls : List (List (JInstr 64))),
      KEnv.Holds s env → gatherList p body = some ls →
      ∃ ls', gatherList p (foldCore p env body) = some ls'
        ∧ runBlock s ls'.flatten = runBlock s ls.flatten := by
  intro body
  induction body with
  | nil =>
      intro env s ls _ h
      refine ⟨ls, h, rfl⟩
  | cons i is ih =>
      intro env s ls hs h
      by_cases hr : isLret i = true
      · have hr' : isLret { i with li_i := foldInstr env i.li_i } = true := by
          rw [isLret_foldInstr]; exact hr
        have h' : gatherList p is = some ls := by
          simpa [gatherList, List.filter_cons, hr] using h
        obtain ⟨ls', h1, h2⟩ := ih (nextEnv p env i) s ls (by
          simp only [nextEnv, hr, if_true]; exact KEnv.Holds.nil s) h'
        refine ⟨ls', ?_, h2⟩
        simpa [gatherList, foldCore, List.filter_cons, hr'] using h1
      · have hr' : isLret { i with li_i := foldInstr env i.li_i } = false := by
          rw [isLret_foldInstr]; simpa using hr
        have hr0 : isLret i = false := by simpa using hr
        simp only [gatherList, List.filter_cons, hr0, Bool.not_false, if_true,
          List.mapM_cons] at h
        cases hi : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
        | none => simp [hi] at h
        | some js =>
            cases hrest : gatherList p is with
            | none => simp [gatherList, hi] at h hrest; simp [hrest] at h
            | some rest =>
                simp only [gatherList] at hrest
                simp only [hi, hrest, Option.bind_eq_bind, Option.bind_some,
                  Option.pure_def, Option.some.injEq] at h
                subst h
                obtain ⟨js', hj', hrun⟩ := foldInstr_lower p (env := env) hi
                have henv : nextEnv p env i = stepKs env js := by
                  simp [nextEnv, hr0, hi]
                obtain ⟨rest', h1, h2⟩ :=
                  ih (nextEnv p env i) (runBlock s js) rest
                    (by rw [henv]; exact hs.stepKs js) hrest
                refine ⟨js' :: rest', ?_, ?_⟩
                · simp only [gatherList] at h1
                  simp only [gatherList, foldCore, List.filter_cons, hr', Bool.not_false,
                    if_true, List.mapM_cons, hj', h1, Option.bind_eq_bind,
                    Option.bind_some, Option.pure_def]
                · simp only [List.flatten_cons, runBlock_append', hrun s hs, h2]

theorem foldCore_lcmdDirect (p : Nat × Nat × Nat) :
    ∀ (body : Lcmd) (env : KEnv), covers p env body = true →
      lcmdDirect (foldCore p env body) = true := by
  intro body
  induction body with
  | nil => intro _ _; rfl
  | cons i is ih =>
      intro env h
      simp only [covers, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hi, hrest⟩ := h
      have hd : linstrRDirect (foldInstr env i.li_i) = true := by
        unfold foldInstr
        cases hf : foldTarget? env i.li_i with
        | none =>
            rcases hi with hi | hi
            · exact hi
            · simp [hf] at hi
        | some i' => exact foldTarget?_direct hf
      have := ih _ hrest
      simp only [lcmdDirect, foldCore, List.all_cons, Bool.and_eq_true] at this ⊢
      exact ⟨hd, this⟩

/-! ## 6. The fold of a body -/

/-- **Semantic agreement.** If a body gathers under `gatherPrinted`, its fold
    gathers, and the two blocks run to the same machine state from every initial
    state. -/
theorem gatherPrinted_constIndexFoldBody {body : Lcmd} {g : List (JInstr 64)}
    (h : gatherPrinted body = some g) :
    ∃ g', gatherPrinted (constIndexFoldBody body) = some g'
      ∧ ∀ s, runBlock s g' = runBlock s g := by
  unfold constIndexFoldBody
  dsimp only
  split
  · rename_i hp
    simp only [gatherPrinted, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    have s0 : JState 64 := { regs := fun _ => 0 }
    obtain ⟨ls', h1, -⟩ :=
      foldCore_gather (bodyParams body) body [] s0 ls (KEnv.Holds.nil s0) hls
    refine ⟨ls'.flatten, ?_, fun s => ?_⟩
    · simp only [gatherPrinted, hp]
      simp only [gatherList] at h1
      simp [h1]
    · obtain ⟨ls'', h2, h3⟩ :=
        foldCore_gather (bodyParams body) body [] s ls (KEnv.Holds.nil s) hls
      rw [h1] at h2
      cases h2
      exact h3
  · exact ⟨g, h, fun _ => rfl⟩

/-- **Directness.** When every register-indexed instruction of the body is folded
    and the frame guard of `constIndexFoldBody` holds, the fold is index-free. -/
theorem constIndexFoldBody_lcmdDirect {body : Lcmd}
    (hc : covers (bodyParams body) [] body = true)
    (hg : bodyParams (foldCore (bodyParams body) [] body) = bodyParams body) :
    lcmdDirect (constIndexFoldBody body) = true := by
  simp only [constIndexFoldBody, hg, if_true]
  exact foldCore_lcmdDirect _ body [] hc

/-- **Constant time.** Under the hypotheses of `constIndexFoldBody_lcmdDirect`,
    the gathered block of the fold has the same machine leakage trace from any two
    initial states. -/
theorem gatherPrinted_constIndexFoldBody_constant_time {body : Lcmd}
    {g : List (JInstr 64)}
    (hc : covers (bodyParams body) [] body = true)
    (hg : bodyParams (foldCore (bodyParams body) [] body) = bodyParams body)
    (h : gatherPrinted (constIndexFoldBody body) = some g) (s₁ s₂ : JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  ConstantTimeCoverage.allDirect_constant_time g
    (gatherPrinted_allDirect (constIndexFoldBody_lcmdDirect hc hg) h) s₁ s₂

/-! ## 7. The printable spelling

`LprogAsmPrinter` and `LprogBytes` render a compile-time-displacement memory
operand as the register-shaped name `mem.<B>.<off>` under `MOVQ`, the form the
array-ABI orchestration emits; they do not render the `.arr` operand. `spellInstr`
maps the two folded forms to that spelling and leaves every other instruction
unchanged. -/

/-- `LOAD [d] [.arr B off]` is `MOVQ [d] [mem.B.off]`; `STORE [_] [.arr B off, v]`
    is `MOVQ [mem.B.off] [v]`. -/
def spellInstr : LinstrR → LinstrR
  | .Lopn [.reg d] "LOAD" [.arr B off] => .Lopn [.reg d] "MOVQ" [.reg (memName B off)]
  | .Lopn [.reg _] "STORE" [.arr B off, .reg vn] =>
      .Lopn [.reg (memName B off)] "MOVQ" [.reg vn]
  | i => i

/-- The spelling applied to every instruction of every function. -/
def spellLprog (lp : Lprog) : Lprog :=
  let spell : Lcmd → Lcmd := List.map (fun i => { i with li_i := spellInstr i.li_i })
  let fs := lp.lp_funcs.map (fun f => (f.1, { f.2 with lfd_body := spell f.2.lfd_body }))
  { lp with lp_funcs := fs }

end CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
