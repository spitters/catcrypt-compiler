/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
import CatCrypt.Crypto.Optimizer.SpillReloadBlockSound
import CatCrypt.Crypto.Optimizer.FootprintValidatedPass

/-!
# Footprint-relative soundness of the whole-block spill/reload materialization

`FootprintValidatedPass.witness_footprint` proves the footprint certificate
(`agreeExcept D`) on the single-spill witness block; `SpillingRegAlloc.lean` §6
lists the two structural invariants a general lifting needs. This module discharges
the general multi-spill case: for a `SpillWellFormed` block whose reads are all
predefined and whose program instructions never address the spill base, the
materialized block `spillReloadBlock decisions spillBase block` agrees with the
original block on every register, every flag, and every memory cell outside the
dead spill cells `deadCells spillBase decisions`.

## The reload-agreement invariant

Each inserted reload `loadMem n spillBase off` is a no-op precisely when the spill
cell `(spillBase, off)` already holds register `n`'s value (`SpillValid`). The
whole-block statement threads this as an invariant over the fold:

* `SpillInvAt decisions spillBase blk s` — every spilled name that is not (re)written
  in the remaining block `blk` has its cell in sync with its register in `s`.

The invariant is established vacuously at entry (each spilled name is written exactly
once, so none is initially "already defined"), maintained across each rewritten
instruction (the def-store re-establishes it; distinct offsets and single-def keep it
for the others), and consumed at each reload.

## The hypotheses beyond `SpillWellFormed`

* `readsAfterDef decisions block` — every spilled name read by an instruction has its
  unique def strictly earlier (its reload therefore reads the store, not an
  uninitialized cell). This is the def-before-use / SSA-dominance condition; it is not
  implied by `SpillWellFormed` and is exactly the reload-agreement content.
* `blockAvoids (deadCells spillBase decisions) block` — no program instruction reads a
  spill cell through a memory base (covers a `loadSym` whose symbol equals the spill
  base, which the register-name disjointness of `SpillWellFormed` does not).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SpillFootprintGeneral

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc
open CatCrypt.Crypto.Optimizer.SpillReloadBlockSound
open CatCrypt.Crypto.Optimizer.FootprintValidated

/-! ## 1. Slot-lookup arithmetic: offsets, names, injectivity -/

/-- One-step reduction of `spillSlotOf` over a `cons`. -/
theorem spillSlotOf_cons (decisions : List (String × Slot)) (k : String) (v : Slot)
    (n : String) :
    spillSlotOf ((k, v) :: decisions) n
      = if n == k then (match v with | .spilled off => some off | _ => none)
        else spillSlotOf decisions n := by
  simp only [spillSlotOf, List.lookup]
  cases h : n == k <;> cases v <;> simp

/-- One-step reduction of `spilledOffsets` over a `cons`. -/
theorem spilledOffsets_cons (k : String) (v : Slot) (ds : List (String × Slot)) :
    spilledOffsets ((k, v) :: ds)
      = (match v with | .spilled off => off :: spilledOffsets ds | _ => spilledOffsets ds) := by
  unfold spilledOffsets
  rw [List.filterMap_cons]
  cases v <;> rfl

/-- One-step reduction of `spilledNames` over a `cons`. -/
theorem spilledNames_cons (k : String) (v : Slot) (ds : List (String × Slot)) :
    spilledNames ((k, v) :: ds)
      = (match v with | .spilled _ => k :: spilledNames ds | _ => spilledNames ds) := by
  unfold spilledNames
  rw [List.filterMap_cons]
  cases v <;> rfl

/-- A spilled name's offset is recorded in `spilledOffsets`. -/
theorem mem_spilledOffsets_of_spillSlotOf (decisions : List (String × Slot)) (n : String)
    (off : Int) (h : spillSlotOf decisions n = some off) : off ∈ spilledOffsets decisions := by
  induction decisions with
  | nil => simp [spillSlotOf, List.lookup] at h
  | cons kv ds ih =>
    obtain ⟨k, v⟩ := kv
    rw [spillSlotOf_cons] at h
    rw [spilledOffsets_cons]
    by_cases hk : n == k
    · simp only [hk, if_true] at h
      cases v with
      | resident r => simp at h
      | spilled o => simp only [Option.some.injEq] at h; subst h; simp
    · simp only [hk, Bool.false_eq_true, if_false] at h
      have := ih h
      cases v with
      | resident r => exact this
      | spilled o => exact List.mem_cons_of_mem _ this

/-- A spilled name is recorded in `spilledNames`. -/
theorem mem_spilledNames_of_spillSlotOf (decisions : List (String × Slot)) (n : String)
    (off : Int) (h : spillSlotOf decisions n = some off) : n ∈ spilledNames decisions := by
  induction decisions with
  | nil => simp [spillSlotOf, List.lookup] at h
  | cons kv ds ih =>
    obtain ⟨k, v⟩ := kv
    rw [spillSlotOf_cons] at h
    rw [spilledNames_cons]
    by_cases hk : n == k
    · have hnk : n = k := by simpa using hk
      subst hnk
      simp only [hk, if_true] at h
      cases v with
      | resident r => simp at h
      | spilled o => simp
    · simp only [hk, Bool.false_eq_true, if_false] at h
      have := ih h
      cases v with
      | resident r => exact this
      | spilled o => exact List.mem_cons_of_mem _ this

/-- Distinct spilled offsets force spill decisions to be injective on names: two names
    mapped to the same spill cell coincide. -/
theorem spillSlot_inj (decisions : List (String × Slot))
    (hnd : (spilledOffsets decisions).Nodup) {n1 n2 : String} {off : Int}
    (h1 : spillSlotOf decisions n1 = some off) (h2 : spillSlotOf decisions n2 = some off) :
    n1 = n2 := by
  induction decisions with
  | nil => simp [spillSlotOf, List.lookup] at h1
  | cons kv ds ih =>
    obtain ⟨k, v⟩ := kv
    rw [spillSlotOf_cons] at h1 h2
    rw [spilledOffsets_cons] at hnd
    by_cases hk1 : n1 == k
    · have e1 : n1 = k := by simpa using hk1
      by_cases hk2 : n2 == k
      · have e2 : n2 = k := by simpa using hk2
        rw [e1, e2]
      · exfalso
        simp only [hk1, if_true] at h1
        simp only [hk2, Bool.false_eq_true, if_false] at h2
        cases v with
        | resident r => simp at h1
        | spilled o =>
          simp only [Option.some.injEq] at h1; subst h1
          rw [List.nodup_cons] at hnd
          exact hnd.1 (mem_spilledOffsets_of_spillSlotOf ds n2 o h2)
    · by_cases hk2 : n2 == k
      · exfalso
        simp only [hk2, if_true] at h2
        simp only [hk1, Bool.false_eq_true, if_false] at h1
        cases v with
        | resident r => simp at h2
        | spilled o =>
          simp only [Option.some.injEq] at h2; subst h2
          rw [List.nodup_cons] at hnd
          exact hnd.1 (mem_spilledOffsets_of_spillSlotOf ds n1 o h1)
      · simp only [hk1, Bool.false_eq_true, if_false] at h1
        simp only [hk2, Bool.false_eq_true, if_false] at h2
        cases v with
        | resident r => exact ih hnd h1 h2
        | spilled o =>
          rw [List.nodup_cons] at hnd
          exact ih hnd.2 h1 h2

/-! ## 2. Per-instruction frame lemmas over `evalInstr` -/

/-- `evalInstr` does not change a register the instruction does not write. -/
theorem evalInstr_get_of_not_written {i : JInstr 64} {s : JState 64} {n : String}
    (h : n ∉ writtenNames i) : (evalInstr s i).get n = s.get n := by
  cases i <;>
    simp_all [evalInstr, writtenNames, JState.get, JState.setReg, JState.writeB5W,
      JState.store, JState.storeIdx, x86_MOV, JOperand.eval, JState.loadIdx, JState.load,
      List.mem_cons, List.not_mem_nil]

/-- `evalInstr` does not change the memory at a base the instruction never names. -/
theorem evalInstr_load_of_not_jinstrName {i : JInstr 64} {s : JState 64} {sb : String}
    (h : sb ∉ jinstrNames i) (off : Int) : (evalInstr s i).load sb off = s.load sb off := by
  cases i
  case storeMem base o' src =>
    simp only [jinstrNames, List.mem_cons, not_or] at h
    simp only [evalInstr, JState.load, JState.store, x86_MOV, JOperand.eval]
    rw [if_neg (fun hc => h.1 hc.1)]
  case storeMemIdx base idx sc src =>
    simp only [jinstrNames, List.mem_cons, not_or] at h
    simp only [evalInstr, JState.load, JState.storeIdx, JState.store, x86_MOV, JOperand.eval]
    rw [if_neg (fun hc => h.1 hc.1)]
  case loadSym dst sym =>
    simp only [jinstrNames, List.mem_singleton] at h
    simp only [evalInstr, JState.load]
    rw [if_neg h]
  all_goals
    simp [evalInstr, JState.load, JOperand.eval, x86_MOV, JState.flagB, JState.get,
      JState.setReg, JState.writeB5W]

/-! ## 3. Reloads are no-ops under the invariant -/

/-- A block of reload loads that are each `SpillValid` at a fixed state is a no-op. -/
theorem runBlock_reloads_noop (spillBase : String) (s : JState 64) :
    ∀ (rl : List (JInstr 64)),
      (∀ instr ∈ rl, ∃ n off, instr = JInstr.loadMem n spillBase off
        ∧ SpillValid spillBase off n s) → runBlock s rl = s := by
  intro rl
  induction rl with
  | nil => intro _; rfl
  | cons instr rest ih =>
    intro h
    obtain ⟨n, off, rfl, hsv⟩ := h instr (List.mem_cons_self ..)
    rw [runBlock_cons, evalInstr_reload_noop hsv]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The reloads `spillRewriteInstr` prepends for one instruction are a no-op, provided
    every spilled read-name's cell holds its register. -/
theorem reloadsOf_noop (decisions : List (String × Slot)) (spillBase : String)
    (i : JInstr 64) (s : JState 64)
    (h : ∀ n off, n ∈ readNames i → spillSlotOf decisions n = some off →
      SpillValid spillBase off n s) :
    runBlock s (reloadsOf decisions spillBase i) = s := by
  apply runBlock_reloads_noop
  intro instr hin
  rw [reloadsOf, List.mem_filterMap] at hin
  obtain ⟨n, hn, hmap⟩ := hin
  cases hs : spillSlotOf decisions n with
  | none => rw [hs] at hmap; simp at hmap
  | some off =>
    rw [hs] at hmap
    simp only [Option.map_some, Option.some.injEq] at hmap
    exact ⟨n, off, hmap.symm, h n off hn hs⟩

/-! ## 4. The spill stores: register and memory footprint

`storeList` is the list of spill stores `storesOf` emits for a set of names — every
element is `storeMem spillBase _ (.reg _)`. It writes only the spill cells; the
originating instruction's `storesOf` is `storeList` over its written names. -/

/-- The stores emitted for a list of names. -/
def storeList (decisions : List (String × Slot)) (spillBase : String)
    (ns : List String) : List (JInstr 64) :=
  ns.filterMap (fun n => (spillSlotOf decisions n).map (fun off =>
    JInstr.storeMem spillBase off (.reg n)))

/-- `storesOf` is `storeList` over the instruction's written names. -/
theorem storesOf_eq_storeList (decisions : List (String × Slot)) (spillBase : String)
    (i : JInstr 64) :
    storesOf decisions spillBase i = storeList decisions spillBase (writtenNames i) := rfl

/-- One-step reduction of `storeList` over a `cons`. -/
theorem storeList_cons (decisions : List (String × Slot)) (spillBase : String)
    (n : String) (ns : List String) :
    storeList decisions spillBase (n :: ns)
      = (match spillSlotOf decisions n with
         | some off => JInstr.storeMem spillBase off (.reg n) :: storeList decisions spillBase ns
         | none => storeList decisions spillBase ns) := by
  unfold storeList
  rw [List.filterMap_cons]
  cases spillSlotOf decisions n <;> rfl

/-- Spill stores never touch registers. -/
theorem storeList_regs (decisions : List (String × Slot)) (spillBase : String)
    (ns : List String) : ∀ s : JState 64,
    (runBlock s (storeList decisions spillBase ns)).regs = s.regs := by
  induction ns with
  | nil => intro s; rfl
  | cons n ns ih =>
    intro s
    rw [storeList_cons]
    cases hs : spillSlotOf decisions n with
    | none => exact ih s
    | some off =>
      rw [runBlock_cons, ih (evalInstr s (.storeMem spillBase off (.reg n)))]
      simp [evalInstr, JState.store]

/-- A spill cell not stored by any name in `ns` is untouched by the stores. -/
theorem storeList_load_notMem (decisions : List (String × Slot)) (spillBase : String)
    (ns : List String) (off' : Int) :
    ∀ s : JState 64, (∀ n ∈ ns, spillSlotOf decisions n ≠ some off') →
    (runBlock s (storeList decisions spillBase ns)).load spillBase off' = s.load spillBase off' := by
  induction ns with
  | nil => intro s _; rfl
  | cons n ns ih =>
    intro s h
    rw [storeList_cons]
    cases hs : spillSlotOf decisions n with
    | none => exact ih s (fun m hm => h m (List.mem_cons_of_mem _ hm))
    | some off =>
      have hoff : off ≠ off' := fun he => h n (List.mem_cons_self ..) (by rw [hs, he])
      rw [runBlock_cons, ih (evalInstr s (.storeMem spillBase off (.reg n)))
        (fun m hm => h m (List.mem_cons_of_mem _ hm))]
      exact evalInstr_spillStore_mem spillBase off' (fun hc => hoff hc.2.symm)

/-- After the stores, a spilled name's cell holds that name's register value. -/
theorem storeList_load_target (decisions : List (String × Slot)) (spillBase : String)
    (ns : List String) (off' : Int) (n' : String)
    (hinj : ∀ m, spillSlotOf decisions m = some off' → m = n')
    (hn' : spillSlotOf decisions n' = some off') :
    ∀ s : JState 64, n' ∈ ns →
    (runBlock s (storeList decisions spillBase ns)).load spillBase off' = s.get n' := by
  induction ns with
  | nil => intro s hmem; simp at hmem
  | cons n ns ih =>
    intro s hmem
    rw [storeList_cons]
    cases hs : spillSlotOf decisions n with
    | none =>
      have hne : n ≠ n' := by
        rintro rfl; rw [hn'] at hs; simp at hs
      exact ih s ((List.mem_cons.mp hmem).resolve_left (fun he => hne he.symm))
    | some off =>
      rw [runBlock_cons]
      by_cases hnn : n = n'
      · subst hnn
        have hoe : off = off' := by rw [hs] at hn'; exact Option.some.inj hn'
        subst hoe
        by_cases hmem2 : n ∈ ns
        · rw [ih (evalInstr s (.storeMem spillBase off (.reg n))) hmem2]
          simp [evalInstr, JState.store, JState.get, x86_MOV, JOperand.eval]
        · rw [storeList_load_notMem decisions spillBase ns off
              (evalInstr s (.storeMem spillBase off (.reg n)))
              (fun m hm hcon => hmem2 (hinj m hcon ▸ hm))]
          have hsv := spillStore_establishes (sb := spillBase) (off := off) (r := n) (s := s)
          unfold SpillValid at hsv
          rw [hsv]
          simp [evalInstr, JState.store, JState.get, x86_MOV, JOperand.eval]
      · have hmem' : n' ∈ ns := (List.mem_cons.mp hmem).resolve_left (fun he => hnn he.symm)
        rw [ih (evalInstr s (.storeMem spillBase off (.reg n))) hmem']
        simp [evalInstr, JState.store, JState.get]

/-! ## 5. `agreeExcept` survives the spill stores -/

/-- Storing to a dead cell preserves agreement modulo the dead set. -/
theorem agreeExcept_store_dead {D : List (String × Int)} {sb : String} {off : Int}
    {v : BitVec 64} {s t : JState 64} (hmem : (sb, off) ∈ D)
    (h : agreeExcept D s t) : agreeExcept D (s.store sb off v) t := by
  obtain ⟨hr, hf, hm⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [JState.regs_store]; exact hr
  · rw [JState.flags_store]; exact hf
  · intro b o hbo
    have hne : ¬ (b = sb ∧ o = off) := by rintro ⟨rfl, rfl⟩; exact hbo hmem
    calc (s.store sb off v).mem b o = (s.store sb off v).load b o := rfl
      _ = s.load b o := JState.load_store_other s sb off v b o hne
      _ = s.mem b o := rfl
      _ = t.mem b o := hm b o hbo

/-- The whole spill-store list preserves agreement modulo the dead set (every store
    targets a dead cell). -/
theorem agreeExcept_storeList_dead (decisions : List (String × Slot)) (spillBase : String)
    (ns : List String) : ∀ (s t : JState 64),
    agreeExcept (deadCells spillBase decisions) s t →
    agreeExcept (deadCells spillBase decisions) (runBlock s (storeList decisions spillBase ns)) t := by
  induction ns with
  | nil => intro s t h; exact h
  | cons n ns ih =>
    intro s t h
    rw [storeList_cons]
    cases hs : spillSlotOf decisions n with
    | none => exact ih s t h
    | some off =>
      rw [runBlock_cons]
      apply ih
      have hmemD : (spillBase, off) ∈ deadCells spillBase decisions := by
        simp only [deadCells, List.mem_map]
        exact ⟨off, mem_spilledOffsets_of_spillSlotOf decisions n off hs, rfl⟩
      have hstore : evalInstr s (.storeMem spillBase off (.reg n)) = s.store spillBase off (s.get n) := by
        simp [evalInstr, x86_MOV, JOperand.eval]
      rw [hstore]
      exact agreeExcept_store_dead hmemD h

/-! ## 6. The reload-agreement invariant and its step -/

/-- `SpillInvAt decisions spillBase blk s`: every spilled name that is not written in
    the remaining block `blk` has its spill cell in sync with its register in `s`. -/
def SpillInvAt (decisions : List (String × Slot)) (spillBase : String)
    (blk : List (JInstr 64)) (s : JState 64) : Prop :=
  ∀ n off, spillSlotOf decisions n = some off → defCount blk n = 0 →
    SpillValid spillBase off n s

/-- `readsAfterDef decisions block`: every spilled name read by an instruction has its
    unique def strictly earlier (it is not written from that instruction onward). -/
def readsAfterDef (decisions : List (String × Slot)) : List (JInstr 64) → Bool
  | [] => true
  | i :: rest =>
      (readNames i).all (fun n =>
        match spillSlotOf decisions n with
        | some _ => defCount (i :: rest) n == 0
        | none => true)
      && readsAfterDef decisions rest

/-- `defCount` over a `cons`. -/
theorem defCount_cons (i : JInstr 64) (rest : List (JInstr 64)) (n : String) :
    defCount (i :: rest) n
      = (if (writtenNames i).contains n = true then 1 else 0) + defCount rest n := by
  unfold defCount
  rw [List.filter_cons]
  by_cases h : (writtenNames i).contains n = true
  · rw [if_pos h, if_pos h, List.length_cons]; omega
  · rw [if_neg h, if_neg h]; omega

/-- Peel `readsAfterDef` over a `cons`. -/
theorem readsAfterDef_cons {decisions : List (String × Slot)} {i : JInstr 64}
    {rest : List (JInstr 64)} (h : readsAfterDef decisions (i :: rest) = true) :
    (∀ n ∈ readNames i, ∀ off, spillSlotOf decisions n = some off → defCount (i :: rest) n = 0)
      ∧ readsAfterDef decisions rest = true := by
  simp only [readsAfterDef, Bool.and_eq_true] at h
  refine ⟨fun n hn off hslot => ?_, h.2⟩
  have hx := (List.all_eq_true.mp h.1) n hn
  simp only [hslot] at hx
  exact eq_of_beq hx

/-- The invariant is maintained across one rewritten instruction: run `i` then its
    spill stores, and every spilled name not written in `rest` stays in sync. -/
theorem spillInvAt_step (decisions : List (String × Slot)) (spillBase : String)
    (i : JInstr 64) (rest : List (JInstr 64)) (s : JState 64)
    (hnd : (spilledOffsets decisions).Nodup) (hbase : spillBase ∉ jinstrNames i)
    (hinv : SpillInvAt decisions spillBase (i :: rest) s) :
    SpillInvAt decisions spillBase rest
      (runBlock (evalInstr s i) (storesOf decisions spillBase i)) := by
  intro n' off' hslot hdc0
  rw [storesOf_eq_storeList]
  by_cases hw : (writtenNames i).contains n' = true
  · have hmemw : n' ∈ writtenNames i := by simpa using hw
    have hinj : ∀ m, spillSlotOf decisions m = some off' → m = n' :=
      fun m hm => spillSlot_inj decisions hnd hm hslot
    unfold SpillValid
    have hreg : (runBlock (evalInstr s i) (storeList decisions spillBase (writtenNames i))).get n'
        = (evalInstr s i).get n' := by
      simp only [JState.get]; rw [storeList_regs]
    rw [hreg, storeList_load_target decisions spillBase (writtenNames i) off' n' hinj hslot
      (evalInstr s i) hmemw]
  · have hnw : n' ∉ writtenNames i := fun hmem => hw (by simpa using hmem)
    have hdc : defCount (i :: rest) n' = 0 := by
      have hc := defCount_cons i rest n'
      rw [if_neg hw] at hc
      omega
    have hsv : SpillValid spillBase off' n' s := hinv n' off' hslot hdc
    have hoff_notin : ∀ m ∈ writtenNames i, spillSlotOf decisions m ≠ some off' := by
      intro m hm hcon
      exact hnw (spillSlot_inj decisions hnd hcon hslot ▸ hm)
    unfold SpillValid at hsv ⊢
    have hreg : (runBlock (evalInstr s i) (storeList decisions spillBase (writtenNames i))).get n'
        = (evalInstr s i).get n' := by
      simp only [JState.get]; rw [storeList_regs]
    rw [hreg, storeList_load_notMem decisions spillBase (writtenNames i) off'
      (evalInstr s i) hoff_notin, evalInstr_load_of_not_jinstrName hbase off',
      evalInstr_get_of_not_written hnw]
    exact hsv

/-! ## 7. The lockstep induction -/

/-- **Lockstep soundness.** Running the materialized block on `s` and the original
    block on `t`, starting from `agreeExcept D`-related states with the reload
    invariant in force, lands in `agreeExcept D`-related states — the observable
    output outside the dead spill cells is equal. -/
theorem agreeExcept_spillReloadBlock_aux (decisions : List (String × Slot))
    (spillBase : String) :
    ∀ (blk : List (JInstr 64)) (s t : JState 64),
      (spilledOffsets decisions).Nodup →
      (∀ i ∈ blk, spillBase ∉ jinstrNames i) →
      (∀ i ∈ blk, instrAvoids (deadCells spillBase decisions) i) →
      readsAfterDef decisions blk = true →
      SpillInvAt decisions spillBase blk s →
      agreeExcept (deadCells spillBase decisions) s t →
      agreeExcept (deadCells spillBase decisions)
        (runBlock s (spillReloadBlock decisions spillBase blk)) (runBlock t blk) := by
  intro blk
  induction blk with
  | nil => intro s t _ _ _ _ _ hag; simpa [spillReloadBlock] using hag
  | cons i rest ih =>
    intro s t hnd hbase havoid hrd hinv hag
    have hpeel : spillReloadBlock decisions spillBase (i :: rest)
        = spillRewriteInstr decisions spillBase i ++ spillReloadBlock decisions spillBase rest := by
      simp [spillReloadBlock, List.flatMap_cons]
    have hreloads : runBlock s (reloadsOf decisions spillBase i) = s :=
      reloadsOf_noop decisions spillBase i s (fun n off hn hslot =>
        hinv n off hslot ((readsAfterDef_cons hrd).1 n hn off hslot))
    have hu : agreeExcept (deadCells spillBase decisions) (evalInstr s i) (evalInstr t i) :=
      agreeExcept_evalInstr i hag (havoid i (List.mem_cons_self ..))
    have hag' : agreeExcept (deadCells spillBase decisions)
        (runBlock (evalInstr s i) (storesOf decisions spillBase i)) (evalInstr t i) := by
      rw [storesOf_eq_storeList]
      exact agreeExcept_storeList_dead decisions spillBase (writtenNames i) _ _ hu
    have hinv' := spillInvAt_step decisions spillBase i rest s hnd
      (hbase i (List.mem_cons_self ..)) hinv
    have hrd' : readsAfterDef decisions rest = true := (readsAfterDef_cons hrd).2
    have hgoal := ih (runBlock (evalInstr s i) (storesOf decisions spillBase i)) (evalInstr t i)
      hnd (fun j hj => hbase j (List.mem_cons_of_mem _ hj))
      (fun j hj => havoid j (List.mem_cons_of_mem _ hj)) hrd' hinv' hag'
    rw [hpeel, SpillingRegAlloc.runBlock_append, spillRewriteInstr_eq,
      SpillingRegAlloc.runBlock_append, hreloads, runBlock_cons, runBlock_cons]
    exact hgoal

/-! ## 8. The general footprint-soundness theorem -/

/-- Reflect `SpillWellFormed` into its three components. -/
theorem spillWellFormed_parts {decisions : List (String × Slot)} {spillBase : String}
    {block : List (JInstr 64)} (hwf : SpillWellFormed decisions spillBase block = true) :
    (spilledOffsets decisions).Nodup ∧ spillBase ∉ blockNames block
      ∧ ∀ n ∈ spilledNames decisions, defCount block n = 1 := by
  simp only [SpillWellFormed, Bool.and_eq_true] at hwf
  obtain ⟨⟨hnd, hcont⟩, hall⟩ := hwf
  refine ⟨of_decide_eq_true hnd, ?_, ?_⟩
  · intro hmem
    have : (blockNames block).contains spillBase = true := by simpa using hmem
    rw [this] at hcont; simp at hcont
  · intro n hn
    exact eq_of_beq ((List.all_eq_true.mp hall) n hn)

/-- An element of the accumulator survives the dedup fold. -/
theorem mem_foldl_dedup_acc {α : Type*} [DecidableEq α] (x : α) :
    ∀ (L acc : List α), x ∈ acc →
      x ∈ L.foldl (fun a m => if a.contains m then a else a ++ [m]) acc := by
  intro L
  induction L with
  | nil => intro acc h; exact h
  | cons hd tl ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    by_cases hc : acc.contains hd = true
    · simp only [hc, if_true]; exact h
    · simp only [hc, Bool.false_eq_true, if_false]; exact List.mem_append_left _ h

/-- Contains reflects membership. -/
theorem mem_of_contains {α : Type*} [DecidableEq α] {a : α} {l : List α}
    (h : l.contains a = true) : a ∈ l := by simpa using h

/-- An element of the input list survives the dedup fold. -/
theorem mem_foldl_dedup_of_mem {α : Type*} [DecidableEq α] (x : α) :
    ∀ (L acc : List α), x ∈ L →
      x ∈ L.foldl (fun a m => if a.contains m then a else a ++ [m]) acc := by
  intro L
  induction L with
  | nil => intro acc h; simp at h
  | cons hd tl ih =>
    intro acc h
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · apply mem_foldl_dedup_acc
      by_cases hc : acc.contains x = true
      · simp only [hc, if_true]; exact mem_of_contains hc
      · simp only [hc, Bool.false_eq_true, if_false]
        exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact ih _ h'

/-- Membership in `blockNames` collects membership in each instruction's `jinstrNames`. -/
theorem mem_blockNames_of_mem_jinstrNames (block : List (JInstr 64)) {i : JInstr 64}
    {n : String} (hi : i ∈ block) (hn : n ∈ jinstrNames i) : n ∈ blockNames block := by
  unfold blockNames
  exact mem_foldl_dedup_of_mem n (block.flatMap jinstrNames) []
    (List.mem_flatMap.mpr ⟨i, hi, hn⟩)

/-! ## 9. The deliverable -/

/-- **General footprint soundness of the spill/reload materialization.** For a
    `SpillWellFormed` block whose reads are all predefined (`readsAfterDef`) and whose
    program instructions never address the spill base (`blockAvoids`), the materialized
    block agrees with the original block on every register, every flag, and every memory
    cell outside the dead spill cells `deadCells spillBase decisions`. -/
theorem spillReloadBlock_footprintSound_general (decisions : List (String × Slot))
    (spillBase : String) (block : List (JInstr 64))
    (hwf : SpillWellFormed decisions spillBase block = true)
    (hrd : readsAfterDef decisions block = true)
    (havoid : blockAvoids (deadCells spillBase decisions) block = true) :
    ∀ s : JState 64,
      agreeExcept (deadCells spillBase decisions)
        (runBlock s (spillReloadBlock decisions spillBase block)) (runBlock s block) := by
  intro s
  obtain ⟨hnd, hspillBase, hdc1⟩ := spillWellFormed_parts hwf
  have hbaseAll : ∀ i ∈ block, spillBase ∉ jinstrNames i := fun i hi hmem =>
    hspillBase (mem_blockNames_of_mem_jinstrNames block hi hmem)
  have havoidAll : ∀ i ∈ block, instrAvoids (deadCells spillBase decisions) i :=
    instrAvoids_of_blockAvoids havoid
  have hinv0 : SpillInvAt decisions spillBase block s := by
    intro n off hslot hdc0
    exact absurd (hdc1 n (mem_spilledNames_of_spillSlotOf decisions n off hslot))
      (by rw [hdc0]; decide)
  exact agreeExcept_spillReloadBlock_aux decisions spillBase block s s hnd hbaseAll havoidAll
    hrd hinv0 (agreeExcept_refl _ _)

/-- The general soundness, packaged as a `FootprintSound` certificate gated to the
    well-formed block. -/
theorem spillReloadBlock_footprintSound_general_packaged (decisions : List (String × Slot))
    (spillBase : String) (block : List (JInstr 64))
    (hwf : SpillWellFormed decisions spillBase block = true)
    (hrd : readsAfterDef decisions block = true)
    (havoid : blockAvoids (deadCells spillBase decisions) block = true) :
    FootprintSound (spillReloadBlock decisions spillBase) (fun b => decide (b = block))
      (deadCells spillBase decisions) := by
  intro b hb s
  rw [show b = block from of_decide_eq_true hb]
  exact spillReloadBlock_footprintSound_general decisions spillBase block hwf hrd havoid s

end CatCrypt.Crypto.Optimizer.SpillFootprintGeneral
