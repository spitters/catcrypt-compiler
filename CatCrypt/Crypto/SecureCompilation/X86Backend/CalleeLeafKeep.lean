/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig

/-!
# The keep check of a System V red-zone leaf kernel

A System V leaf kernel need not move the stack register: it may store to the red zone, the
`128` bytes below its entry `%rsp`, and return. The decoded block of such a kernel has the form
`body ; ret`; it calls nothing, never writes `%rsp`, and stores only to the red zone of a store
policy `P` and to the out windows of `P`. `keepCheckLeafAtB` is the Boolean check of that
form; it runs the provenance analysis of `CalleeSig` at the frame `0` (`kstepS P 0`), so a
store into an out window goes through a register that holds the entry value of the window's
base register.

The check has the conclusion of the framed check `keepCheckAtB` (`keepCheckLeafAtB_sound`),
and `keepCheckAnyAtB`, the disjunction of the two checks, has it too
(`keepCheckAnyAtB_sound`). The check accepts exactly the class `RedZoneLeaf` of red-zone leaf
blocks (`keepCheckLeafAtB_iff`).

## Main results

* `StoreAddrLeaf`, `StoreLeaf`, `InstrLeaf`, `RedZoneLeaf`: the red-zone leaf blocks as a
  proposition.
* `bodyOkLB`, `instrOkLB`, `keepCheckLB`, `keepCheckLeafAtB`: the check of a red-zone leaf
  block.
* `keepCheck_invL`, `keepCheck_soundL`, `not_call_mem_of_keepCheckLB`: the invariant along a
  run of a checked leaf block and its soundness.
* `keepCheckLeafAtB_sound`: a block accepted by `keepCheckLeafAtB` holds no `call`, and every
  leaky run of it restores the stack register, keeps the registers outside the clobber set and
  keeps the bytes outside the room of `G` bytes below the entry `%rsp` and the out windows.
* `keepCheckLB_iff`, `keepCheckLeafAtB_iff`: completeness, the check holds exactly at the
  red-zone leaf blocks of an admissible policy.
* `keepCheckAnyAtB`, `keepCheckAnyAtB_sound`, `keepCheckAnyAtB_of_keepCheckAtB`,
  `keepCheckAnyAtB_of_keepCheckLeafAtB`: the framed check or the leaf check, and its soundness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Callee

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## The class of red-zone leaf blocks -/

/-- A store at the base register `b` and the displacement `o` is allowed in a red-zone leaf
    under the policy `P` with the provenance facts `A`: a word of the red zone, at `%rsp` with
    `-P.red ≤ o` and `o + 8 ≤ 0`, or a word of an out window of `P` through a register that
    holds, by `A`, the entry value of the window's base register. -/
def StoreAddrLeaf (P : StorePol) (A : List KFact) (b : String) (o : Int) : Prop :=
  (b = "%rsp" ∧ -(P.red : Int) ≤ o ∧ o + 8 ≤ 0)
    ∨ ∃ w ∈ P.wins, (KLoc.reg b, w.1) ∈ A ∧ w.2.1 ≤ o ∧ o + 8 ≤ w.2.2

/-- A store of the instruction, if any, is allowed in a red-zone leaf (`StoreAddrLeaf`); an
    indexed store is not. -/
def StoreLeaf (P : StorePol) (A : List KFact) : JInstr 64 → Prop
  | .storeMem b o _ => StoreAddrLeaf P A b o
  | .addToMem b o _ => StoreAddrLeaf P A b o
  | .storeMemIdx .. => False
  | _ => True

/-- An instruction before the final `ret` of a red-zone leaf block of length `n`: an `op` that
    writes only registers of `clob` other than `%rsp` and stores as `StoreLeaf` allows, or a
    branch with its target inside the block; no `ret`, `push`, `pop` or `call`. -/
def InstrLeaf (n : Nat) (clob : String → Bool) (P : StorePol) (A : List KFact) : RInstr → Prop
  | .op i => (∀ d ∈ dsts i, d ≠ "%rsp" ∧ clob d = true) ∧ StoreLeaf P A i
  | .jcc _ t => t < n
  | _ => False

/-- **The System V red-zone leaf blocks** at the clobber set `clob` and the store policy `P`:
    the last instruction is `ret`, every other instruction satisfies `InstrLeaf` with the
    provenance facts of the analysis at the frame `0` (`kFactsBy (kstepS P 0)`), and the table
    of those facts passes the flow check. -/
structure RedZoneLeaf (q : List RInstr) (clob : String → Bool) (P : StorePol) : Prop where
  /-- The last instruction is `ret`. -/
  last : q.getLast? = some .ret
  /-- Every instruction before the last is a leaf instruction. -/
  body : ∀ k ri, q[k]? = some ri → k + 1 < q.length →
    InstrLeaf q.length clob P (kFactsBy (kstepS P 0) q clob P k) ri
  /-- The table of provenance facts passes the flow check. -/
  flow : kFlowOkBy (kstepS P 0) q (kFactsBy (kstepS P 0) q clob P) = true

/-! ## The check -/

/-- The check of an instruction before the final `ret` of a red-zone leaf block of length
    `n` with the facts `A`: the Boolean form of `InstrLeaf`. -/
def bodyOkLB (n : Nat) (clob : String → Bool) (P : StorePol) (A : List KFact) : RInstr → Bool
  | .op i => (dsts i).all (fun d => d != "%rsp" && clob d) && storeOkWB 0 P A i
  | .jcc _ t => decide (t < n)
  | _ => false

/-- The check of the instruction at index `k` of a red-zone leaf block of length `n` with the
    table of facts `T`: index `n - 1` is `ret`, every other index satisfies `bodyOkLB`. -/
def instrOkLB (n : Nat) (clob : String → Bool) (P : StorePol) (T : Nat → List KFact)
    (k : Nat) (ri : RInstr) : Bool :=
  if k + 1 = n then (match ri with | .ret => true | _ => false)
  else bodyOkLB n clob P (T k) ri

/-- **The keep check of a red-zone leaf block** under the store policy `P`: the block is not
    empty, `P` satisfies `winsOkB`, the facts of the analysis at the frame `0` pass the flow
    check, and every instruction satisfies `instrOkLB`. -/
def keepCheckLB (q : List RInstr) (clob : String → Bool) (P : StorePol) : Bool :=
  let T := kFactsBy (kstepS P 0) q clob P
  decide (1 ≤ q.length) && winsOkB clob P && kFlowOkBy (kstepS P 0) q T
    && allFrom (instrOkLB q.length clob P T) 0 q

/-- **The keep check of a System V red-zone leaf kernel in a room of `G` bytes**: the red zone
    of `P` lies within the room, and the block passes `keepCheckLB`. -/
def keepCheckLeafAtB (q : List RInstr) (clob : String → Bool) (G : Nat) (P : StorePol) :
    Bool :=
  decide (P.red ≤ G) && keepCheckLB q clob P

/-- **The keep check of a framed block or of a red-zone leaf block**: `keepCheckAtB` or
    `keepCheckLeafAtB`. -/
def keepCheckAnyAtB (q : List RInstr) (clob : String → Bool) (G : Nat) (P : StorePol) :
    Bool :=
  keepCheckAtB q clob G P || keepCheckLeafAtB q clob G P

/-! ## Soundness -/

/-- The invariant of a run of a red-zone leaf block with the table of facts `T`, entered in
    the state `e`: the stack register is that of `e`, a register outside `clob` other than the
    stack register and a byte outside the footprint `KeepFoot P 0 e.regs` are those of `e`, and
    every fact of `T pc` holds. -/
def KeepInvL (clob : String → Bool) (P : StorePol) (T : Nat → List KFact) (e : AState)
    (pc : Nat) (s : AState) : Prop :=
  s.regs "%rsp" = e.regs "%rsp"
    ∧ (∀ r, r ≠ "%rsp" → clob r = false → s.regs r = e.regs r)
    ∧ (∀ x, ¬ KeepFoot P 0 e.regs x → s.mem x = e.mem x)
    ∧ ∀ f ∈ T pc, f.Holds e s

/-- **The invariant along a run of a red-zone leaf block.** A leaky run of a block accepted by
    `keepCheckLB` at the policy `P`, from an index and a state that satisfy `KeepInvL` for the
    entry state `e`, whose out windows are disjoint from the red zone of `e`, returns in a state
    with the stack register of `e`, the registers of `e` outside `clob` and the bytes of `e`
    outside the footprint `KeepFoot P 0 e.regs`. -/
theorem keepCheck_invL {q : List RInstr} {clob : String → Bool} {P : StorePol}
    (hk : keepCheckLB q clob P = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    (e : AState) (hsep : WinSep P P.red e.regs) {pc : Nat} {s : AState} {t : List CTLeak}
    {s' : AState} (h : RunL r ok q pc s t s')
    (hI : KeepInvL clob P (kFactsBy (kstepS P 0) q clob P) e pc s) :
    s'.regs "%rsp" = e.regs "%rsp"
      ∧ (∀ r', r' ≠ "%rsp" → clob r' = false → s'.regs r' = e.regs r')
      ∧ ∀ x, ¬ KeepFoot P 0 e.regs x → s'.mem x = e.mem x := by
  simp only [keepCheckLB, Bool.and_eq_true, decide_eq_true_eq] at hk
  generalize kFactsBy (kstepS P 0) q clob P = T at hk hI
  obtain ⟨⟨_, hfl⟩, hall⟩ := hk
  simp only [kFlowOkBy, Bool.and_eq_true] at hfl
  have hsep0 : WinSep P (0 + P.red) e.regs := by rwa [Nat.zero_add]
  have hat : ∀ {pc : Nat} {ri : RInstr}, q[pc]? = some ri →
      instrOkLB q.length clob P T pc ri = true := fun {pc ri} hq => by
    simpa using allFrom_getElem? q 0 pc ri hall hq
  have hfop : ∀ {pc : Nat} {i : JInstr 64}, q[pc]? = some (.op i) →
      ∀ f ∈ T (pc + 1), f ∈ kstepS P 0 (T pc) i := fun {pc i} hq f hf => by
    have := allFrom_getElem? q 0 pc _ hfl.2 hq
    simp only [Nat.zero_add, List.all_eq_true, List.contains_iff_mem] at this
    exact this f hf
  have hfjcc : ∀ {pc cc tg : Nat}, q[pc]? = some (.jcc cc tg) →
      (∀ f ∈ T tg, f ∈ T pc) ∧ ∀ f ∈ T (pc + 1), f ∈ T pc := fun {pc cc tg} hq => by
    have := allFrom_getElem? q 0 pc _ hfl.2 hq
    simpa only [Nat.zero_add, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
      using this
  induction h with
  | ret _ => exact ⟨hI.1, hI.2.1, hI.2.2.1⟩
  | @op pc s i t s' hq _ _ ih =>
    have hc := hat hq
    obtain ⟨h1, h2, h3, h4⟩ := hI
    have hb : s.regs "%rsp" = e.regs "%rsp" + BitVec.ofInt 64 (-((0 : Nat) : Int)) := by
      simp [h1]
    have hbody : bodyOkLB q.length clob P (T pc) (.op i) = true := by
      unfold instrOkLB at hc
      split at hc
      · simp at hc
      · exact hc
    simp only [bodyOkLB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at hbody
    obtain ⟨hd, hst⟩ := hbody
    apply ih
    refine ⟨?_, fun r' hr' hcl => ?_, fun x hx => ?_, fun f hf => ?_⟩
    · exact (evalInstr_regs_of_not_mem_dsts s.view i _ (fun hm => (hd _ hm).1 rfl)).trans h1
    · refine (evalInstr_regs_of_not_mem_dsts s.view i _ (fun hm => ?_)).trans (h2 r' hr' hcl)
      have := (hd _ hm).2
      rw [hcl] at this
      cases this
    · rw [evalInstrA_mem_of_storeOkW hst hb (fun r b hm => h4 _ hm) x hx]
      exact h3 x hx
    · exact kstepS_sound hsep0 (fun _ => hb) h4 f (hfop hq f hf)
  | @jcc pc s cc tgt c t s' hq _ _ ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hI
    obtain ⟨hjt, hjn⟩ := hfjcc hq
    apply ih
    refine ⟨h1, h2, h3, ?_⟩
    split
    · exact fun f hf => h4 f (hjt f hf)
    · exact fun f hf => h4 f (hjn f hf)
  | @stack pc s ri ops t s' hq hops _ _ _ =>
    have hc := hat hq
    exfalso
    cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq] at hops <;>
      simp [instrOkLB, bodyOkLB] at hc
  | @call pc tgt s sc tc tr s' hq _ _ _ _ _ _ =>
    have hc := hat hq
    exfalso
    simp [instrOkLB, bodyOkLB] at hc

/-- **Soundness of the keep check of a red-zone leaf block.** Every leaky run of a block
    accepted by `keepCheckLB` at the policy `P`, from its first index to its `ret`, from an
    entry state whose out windows are disjoint from its red zone, restores the stack register,
    keeps every register outside `clob` and keeps every byte outside the footprint
    `KeepFoot P 0` of the entry register file. -/
theorem keepCheck_soundL {q : List RInstr} {clob : String → Bool} {P : StorePol}
    (hk : keepCheckLB q clob P = true) {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {s : AState} {t : List CTLeak} {s' : AState} (h : RunL r ok q 0 s t s')
    (hsep : WinSep P P.red s.regs) :
    s'.regs "%rsp" = s.regs "%rsp"
      ∧ (∀ r', clob r' = false → s'.regs r' = s.regs r')
      ∧ ∀ x, ¬ KeepFoot P 0 s.regs x → s'.mem x = s.mem x := by
  have h0 : ∀ f ∈ kFactsBy (kstepS P 0) q clob P 0, f.Holds s s := by
    simp only [keepCheckLB, kFlowOkBy, Bool.and_eq_true, List.all_eq_true,
      beq_iff_eq] at hk
    intro f hf
    simp only [KFact.Holds, hk.1.2.1 f hf]
  obtain ⟨h1, h2, h3⟩ := keepCheck_invL hk s hsep h
    ⟨rfl, fun _ _ _ => rfl, fun _ _ => rfl, h0⟩
  refine ⟨h1, fun r' hcl => ?_, h3⟩
  by_cases hr : r' = "%rsp"
  · rw [hr, h1]
  · exact h2 r' hr hcl

/-- A block accepted by `keepCheckLB` holds no `call`. -/
theorem not_call_mem_of_keepCheckLB {q : List RInstr} {clob : String → Bool} {P : StorePol}
    (hk : keepCheckLB q clob P = true) (tg : Nat) : RInstr.call tg ∉ q := by
  simp only [keepCheckLB, Bool.and_eq_true] at hk
  intro hm
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  have hc : instrOkLB q.length clob P (kFactsBy (kstepS P 0) q clob P) j (.call tg) = true := by
    simpa using allFrom_getElem? q 0 j _ hk.2 hj
  simp [instrOkLB, bodyOkLB] at hc

/-- **Soundness of `keepCheckLeafAtB`.** A block accepted by `keepCheckLeafAtB` at a room of
    `G` bytes and the policy `P` holds no `call`, and every leaky run of it from its first index
    to its `ret`, from an entry state whose out windows of `P` are disjoint from the `G` bytes
    below its stack register, restores the stack register, keeps every register outside
    `clob`, and keeps every byte outside those `G` bytes and the out windows of `P` at the entry
    values of their base registers. The conclusion is that of `keepCheckAtB_sound`. -/
theorem keepCheckLeafAtB_sound {q : List RInstr} {clob : String → Bool} {G : Nat}
    {P : StorePol} (hk : keepCheckLeafAtB q clob G P = true) :
    (∀ tg, RInstr.call tg ∉ q) ∧ ∀ {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
      {s : AState} {t : List CTLeak} {s' : AState}, RunL r ok q 0 s t s' →
      WinSep P G s.regs →
      s'.regs "%rsp" = s.regs "%rsp" ∧ (∀ r', clob r' = false → s'.regs r' = s.regs r')
        ∧ ∀ x, ¬ KeepFoot ⟨0, P.wins⟩ G s.regs x → s'.mem x = s.mem x := by
  simp only [keepCheckLeafAtB, Bool.and_eq_true, decide_eq_true_eq] at hk
  refine ⟨not_call_mem_of_keepCheckLB hk.2, fun h hsep => ?_⟩
  obtain ⟨h1, h2, h3⟩ := keepCheck_soundL hk.2 h (hsep.mono hk.1)
  exact ⟨h1, h2, fun x hx => h3 x fun hf => hx (keepFoot_le (by omega) hf)⟩

/-- **Soundness of `keepCheckAnyAtB`**, with the conclusion of `keepCheckAtB_sound`. -/
theorem keepCheckAnyAtB_sound {q : List RInstr} {clob : String → Bool} {G : Nat}
    {P : StorePol} (hk : keepCheckAnyAtB q clob G P = true) :
    (∀ tg, RInstr.call tg ∉ q) ∧ ∀ {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
      {s : AState} {t : List CTLeak} {s' : AState}, RunL r ok q 0 s t s' →
      WinSep P G s.regs →
      s'.regs "%rsp" = s.regs "%rsp" ∧ (∀ r', clob r' = false → s'.regs r' = s.regs r')
        ∧ ∀ x, ¬ KeepFoot ⟨0, P.wins⟩ G s.regs x → s'.mem x = s.mem x := by
  simp only [keepCheckAnyAtB, Bool.or_eq_true] at hk
  rcases hk with hk | hk
  · exact keepCheckAtB_sound hk
  · exact keepCheckLeafAtB_sound hk

/-- A block accepted by the framed check `keepCheckAtB` is accepted by `keepCheckAnyAtB`. -/
theorem keepCheckAnyAtB_of_keepCheckAtB {q : List RInstr} {clob : String → Bool} {G : Nat}
    {P : StorePol} (hk : keepCheckAtB q clob G P = true) : keepCheckAnyAtB q clob G P = true := by
  simp [keepCheckAnyAtB, hk]

/-- A block accepted by the leaf check `keepCheckLeafAtB` is accepted by `keepCheckAnyAtB`. -/
theorem keepCheckAnyAtB_of_keepCheckLeafAtB {q : List RInstr} {clob : String → Bool}
    {G : Nat} {P : StorePol} (hk : keepCheckLeafAtB q clob G P = true) :
    keepCheckAnyAtB q clob G P = true := by
  simp [keepCheckAnyAtB, hk]

/-! ## Completeness -/

/-- `allFrom f k l` holds exactly when `f (k + j)` holds at the instruction at each index `j`
    of `l`. -/
theorem allFrom_iff {f : Nat → RInstr → Bool} :
    ∀ (l : List RInstr) (k : Nat),
      allFrom f k l = true ↔ ∀ j ri, l[j]? = some ri → f (k + j) ri = true
  | [], k => by simp [allFrom]
  | x :: l, k => by
    rw [allFrom, Bool.and_eq_true, allFrom_iff l (k + 1)]
    constructor
    · rintro ⟨h0, hl⟩ (_ | j) ri hj
      · grind
      · have := hl j ri (by simpa using hj)
        rwa [show k + 1 + j = k + (j + 1) by omega] at this
    · intro h
      refine ⟨by simpa using h 0 x rfl, fun j ri hj => ?_⟩
      have := h (j + 1) ri (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this

/-- The store check at the frame `0` is `StoreAddrLeaf`. -/
theorem storeWinB_zero_iff {P : StorePol} {A : List KFact} {b : String} {o : Int} :
    storeWinB 0 P A b o = true ↔ StoreAddrLeaf P A b o := by
  simp [storeWinB, StoreAddrLeaf, and_assoc]

/-- The store check of an instruction at the frame `0` is `StoreLeaf`. -/
theorem storeOkWB_zero_iff {P : StorePol} {A : List KFact} (i : JInstr 64) :
    storeOkWB 0 P A i = true ↔ StoreLeaf P A i := by
  cases i <;> simp [storeOkWB, StoreLeaf, storeWinB_zero_iff]

/-- `bodyOkLB` is `InstrLeaf`. -/
theorem bodyOkLB_iff {n : Nat} {clob : String → Bool} {P : StorePol} {A : List KFact}
    (ri : RInstr) : bodyOkLB n clob P A ri = true ↔ InstrLeaf n clob P A ri := by
  cases ri <;> simp [bodyOkLB, InstrLeaf, storeOkWB_zero_iff, List.all_eq_true]

/-- **Completeness of `keepCheckLB`**: the check holds exactly at the red-zone leaf blocks of a
    policy whose red zone has at most `128` bytes and whose out windows are not based at the
    stack register. -/
theorem keepCheckLB_iff {q : List RInstr} {clob : String → Bool} {P : StorePol} :
    keepCheckLB q clob P = true ↔
      P.red ≤ 128 ∧ (∀ w ∈ P.wins, w.1 ≠ "%rsp") ∧ RedZoneLeaf q clob P := by
  have hw : (P.wins.all fun w => w.1 != "%rsp") = true ↔ ∀ w ∈ P.wins, w.1 ≠ "%rsp" := by
    simp only [List.all_eq_true, bne_iff_ne]
  simp only [keepCheckLB, winsOkB, Bool.and_eq_true, decide_eq_true_eq, hw, allFrom_iff,
    Nat.zero_add]
  constructor
  · rintro ⟨⟨⟨hlen, hred, hwin⟩, hfl⟩, hall⟩
    refine ⟨hred, hwin, ⟨?_, fun k ri hk hlt => ?_, hfl⟩⟩
    · rw [List.getLast?_eq_getElem?]
      obtain ⟨ri, hri⟩ : ∃ ri, q[q.length - 1]? = some ri :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have := hall _ ri hri
      simp only [instrOkLB, show q.length - 1 + 1 = q.length by omega, ↓reduceIte] at this
      rw [hri]
      cases ri <;> simp_all
    · have := hall k ri hk
      simpa only [instrOkLB, show ¬(k + 1 = q.length) by omega, ↓reduceIte, bodyOkLB_iff]
        using this
  · rintro ⟨hred, hwin, ⟨hlast, hbody, hfl⟩⟩
    have hlen : 1 ≤ q.length := by
      cases q with
      | nil => simp at hlast
      | cons _ _ => simp
    refine ⟨⟨⟨hlen, hred, hwin⟩, hfl⟩, fun k ri hk => ?_⟩
    have hlt : k < q.length := (List.getElem?_eq_some_iff.1 hk).1
    unfold instrOkLB
    split
    · rw [List.getLast?_eq_getElem?, show q.length - 1 = k by omega, hk] at hlast
      cases hlast
      rfl
    · rw [bodyOkLB_iff]
      exact hbody k ri hk (by omega)

/-- **Completeness of `keepCheckLeafAtB`**: the check at a room of `G` bytes holds exactly at
    the System V red-zone leaf blocks of a policy whose red zone lies within the room and has
    at most `128` bytes, and whose out windows are not based at the stack register. -/
theorem keepCheckLeafAtB_iff {q : List RInstr} {clob : String → Bool} {G : Nat}
    {P : StorePol} :
    keepCheckLeafAtB q clob G P = true ↔
      P.red ≤ G ∧ P.red ≤ 128 ∧ (∀ w ∈ P.wins, w.1 ≠ "%rsp") ∧ RedZoneLeaf q clob P := by
  simp only [keepCheckLeafAtB, Bool.and_eq_true, decide_eq_true_eq, keepCheckLB_iff]

end CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
