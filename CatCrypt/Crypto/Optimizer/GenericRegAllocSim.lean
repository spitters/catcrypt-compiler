/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# Register-allocation soundness with an auxiliary (flags + memory) simulation relation

`GenericRegAlloc.RegMachine`'s renaming theorem (`renameBlock_runBlock`) is
**register-only**: its `writes_rename` field supplies just register read-agreement
(`get t (ρ a) = get s a` for `a ∈ readNames i`). That is exactly right for
register-to-register ISAs (RISC-V `RInst`, the AVX/AVX-512 vector backends), but x86
scalar instructions also *read* non-register state — the condition flags
(`adc`/`adcx`/`adox`/`cmov`/`setc`) and frame memory (`loadMem`/`mulxMem`/`loadMemIdx`).
For those, the renamed instruction's written *value* cannot be shown equal to the
original's without also assuming flag and memory agreement.

This file adds the standard fix — the same one CompCert's and Jasmin's allocation
proofs use, and the one the bespoke x86 `JInstrRegAllocScoped.StateRelOn` (flags +
`memOn`) carries by hand: a **simulation relation that also tracks the auxiliary
state**. `RegMachineSim` is `RegMachine`'s data plus an abstract, ρ-aware `aux`
relation and two laws — `writes_rename_sim` (the write-list agreement may assume
`aux`) and `aux_step` (a step preserves `aux`). The main theorem `renameBlock_runBlock_sim`
threads `Reindexed ∧ aux` through the block and exposes the register conclusion
(`Reindexed`). Taking `aux := fun _ _ _ => True` recovers the register-only theorem, so
this is a conservative extension; the x86 `JInstr` instance takes `aux ρ s t :=`
flags-equal `∧` memory-agree-under-ρ.

It is a deliberate sibling of `RegMachine` (it re-declares the shared register fields
rather than `extends RegMachine`, because the register-only `writes_rename` is *not*
provable for the flag/memory-reading x86 ops — that is the whole point). The shared
`setMany` register machinery is re-derived here over `RegMachineSim` as `setManyS*`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I : Type} {S : Type}

/-! ## 1. The simulation-relation-carrying machine -/

/-- A register machine whose per-instruction step may also read/write **non-register**
    state (x86 condition flags, frame memory). Identical to `RegMachine` except the
    register-only `writes_rename` is replaced by an abstract ρ-aware auxiliary relation
    `aux` and the two laws `writes_rename_sim` / `aux_step`. With `aux := fun _ _ _ =>
    True` this is exactly `RegMachine`; with `aux` = flags+memory agreement it admits the
    full x86 scalar instruction set. The CompCert/Jasmin full-state allocation relation,
    made a typeclass parameter. -/
class RegMachineSim (I : Type) (S : Type) extends MachineModel I where
  /-- Straight-line block semantics (left fold of the step). -/
  runBlock : S → List I → S
  /-- The register/cell value type. -/
  Val : Type
  /-- Read a register. -/
  get : S → String → Val
  /-- Write a register. -/
  set : S → String → Val → S
  /-- The `(name, value)` pairs an instruction writes (one per destination). -/
  writes : S → I → List (String × Val)
  /-- Apply a renaming to an instruction. -/
  renameInst : (String → String) → I → I
  /-- The discard-register predicate. -/
  isDiscard : String → Bool
  /-- **The auxiliary (non-register) state agreement under renaming ρ.** Flags + frame
      memory for x86; `fun _ _ _ => True` for register-to-register ISAs. -/
  aux : (String → String) → S → S → Prop
  /-- Reading any two discard registers gives the same fixed value. -/
  get_discard : ∀ (s s' : S) (r r' : String),
    isDiscard r = true → isDiscard r' = true → get s r = get s' r'
  /-- Reading back a just-written non-discard register returns the written value. -/
  get_set_same : ∀ (s : S) (r : String) (v : Val), isDiscard r = false → get (set s r v) r = v
  /-- Writing one register leaves the others unchanged. -/
  get_set_other : ∀ (s : S) (r r' : String) (v : Val), r' ≠ r → get (set s r' v) r = get s r
  /-- The step is the fold of `set` over `writes`, **as observed on the register file**. -/
  evalInst_eq_set : ∀ (s : S) (i : I) (r : String),
    get (runBlock s [i]) r = get ((writes s i).foldl (fun st p => set st p.1 p.2) s) r
  /-- The empty block is a no-op. -/
  runBlock_nil : ∀ (s : S), runBlock s [] = s
  /-- `runBlock` is the left fold. -/
  runBlock_append : ∀ (s : S) (xs ys : List I),
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys
  /-- The written names are exactly `writtenNames i`. -/
  writes_names : ∀ (s : S) (i : I),
    (writes s i).map Prod.fst = MachineModel.writtenNames i
  /-- **Write-list agreement, with the auxiliary relation available.** Under register
      read-agreement on the read-names AND `aux ρ s t`, the renamed instruction writes the
      same values to the ρ-renamed destinations. -/
  writes_rename_sim : ∀ (ρ : String → String) (s t : S) (i : I),
    (∀ a ∈ MachineModel.readNames i, get t (ρ a) = get s a) → aux ρ s t →
    writes t (renameInst ρ i) = (writes s i).map (fun p => (ρ p.1, p.2))
  /-- **A single step preserves `aux`**, given register read-agreement on its read-names,
      an injective ρ, and `aux` on the inputs. -/
  aux_step : ∀ (ρ : String → String) (s t : S) (i : I),
    Function.Injective ρ →
    (∀ a ∈ MachineModel.readNames i, get t (ρ a) = get s a) → aux ρ s t →
    aux ρ (runBlock s [i]) (runBlock t [renameInst ρ i])

/-! ## 2. The register transport (re-derived over `RegMachineSim`)

`Reindexed`/`rmDisc`/`reindexed_src` from `GenericRegAlloc` are stated over
`RegMachine`; here we re-state the minimal register machinery over `RegMachineSim`. The
proofs are the `setMany_reindexed` ones, verbatim, against `RegMachineSim`'s register
fields. -/

/-- The discard predicate, `RegMachineSim` form. -/
abbrev smDisc (I S : Type) [RegMachineSim I S] (r : String) : Bool := RegMachineSim.isDiscard I S r

/-- Read a register, `RegMachineSim` form. -/
abbrev smGet (I : Type) [RegMachineSim I S] (s : S) (r : String) : RegMachineSim.Val I S :=
  RegMachineSim.get (I := I) s r

/-- Apply a renaming to a block. -/
def renameBlockS [RegMachineSim I S] (ρ : String → String) (block : List I) : List I :=
  block.map (RegMachineSim.renameInst (S := S) ρ)

/-- The reindex relation over `RegMachineSim`'s register file. -/
def ReindexedS (I : Type) [RegMachineSim I S] (ρ : String → String) (s t : S) : Prop :=
  ∀ n, smDisc I S (ρ n) = false → smGet I t (ρ n) = smGet I s n

/-- Renamed source read = original read (the `reindexed_src` analogue). -/
theorem reindexedS_src (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hρd : ∀ r, smDisc I S r = true → smDisc I S (ρ r) = true)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false)
    (s t : S) (h : ReindexedS I ρ s t) (a : String) :
    smGet I t (ρ a) = smGet I s a := by
  by_cases ha : smDisc I S a = true
  · exact RegMachineSim.get_discard t s (ρ a) a (hρd a ha) ha
  · exact h a (hρnd a (by simpa using ha))

/-- Fold `set` over a write-list, `RegMachineSim` form. -/
def setManyS (I : Type) [RegMachineSim I S] (s : S)
    (pairs : List (String × RegMachineSim.Val I S)) : S :=
  pairs.foldl (fun st p => RegMachineSim.set (I := I) st p.1 p.2) s

@[simp] theorem setManyS_cons (I : Type) [RegMachineSim I S] (s : S)
    (p : String × RegMachineSim.Val I S) (ps : List (String × RegMachineSim.Val I S)) :
    setManyS I s (p :: ps) = setManyS I (RegMachineSim.set (I := I) s p.1 p.2) ps := rfl

/-- A single `set` preserves `ReindexedS`. -/
theorem set_step_reindexedS (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hinj : Function.Injective ρ)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false)
    (s t : S) (n : String) (v : RegMachineSim.Val I S)
    (hz : smDisc I S n = false) (h : ReindexedS I ρ s t) :
    ReindexedS I ρ (RegMachineSim.set (I := I) s n v) (RegMachineSim.set (I := I) t (ρ n) v) := by
  intro m hm
  show RegMachineSim.get _ _ = RegMachineSim.get _ _
  have hzρ : smDisc I S (ρ n) = false := hρnd _ hz
  by_cases hd : m = n
  · subst hd
    rw [RegMachineSim.get_set_same _ _ _ hzρ, RegMachineSim.get_set_same _ _ _ hz]
  · have hne : ρ n ≠ ρ m := fun hc => hd (hinj hc.symm)
    rw [RegMachineSim.get_set_other _ _ _ _ hne, RegMachineSim.get_set_other _ _ _ _ (Ne.symm hd)]
    exact h m hm

/-- A whole write-list preserves `ReindexedS` (iterate the single-write step). -/
theorem setManyS_reindexed (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hinj : Function.Injective ρ)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false) :
    ∀ (pairs : List (String × RegMachineSim.Val I S)),
      (∀ p ∈ pairs, smDisc I S p.1 = false) →
      ∀ (s t : S), ReindexedS I ρ s t →
        ReindexedS I ρ (setManyS I s pairs)
          (setManyS I t (pairs.map (fun p => (ρ p.1, p.2)))) := by
  intro pairs
  induction pairs with
  | nil => intro _ s t h; exact h
  | cons p ps ih =>
    intro hz s t h
    have hstep := set_step_reindexedS I ρ hinj hρnd s t p.1 p.2 (hz p (List.mem_cons_self ..)) h
    have hrest := ih (fun q hq => hz q (List.mem_cons_of_mem _ hq))
      (RegMachineSim.set (I := I) s p.1 p.2) (RegMachineSim.set (I := I) t (ρ p.1) p.2) hstep
    simpa [setManyS_cons, List.map_cons] using hrest

/-! ## 3. The simulation theorem -/

/-- One step preserves `ReindexedS` (the register half), using the auxiliary relation to
    discharge `writes_rename_sim`. -/
theorem evalInstS_rename_preserves (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hinj : Function.Injective ρ) (hρd : ∀ r, smDisc I S r = true → smDisc I S (ρ r) = true)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false)
    (s t : S) (i : I) (hz : ∀ n ∈ MachineModel.writtenNames i, smDisc I S n = false)
    (h : ReindexedS I ρ s t) (ha : RegMachineSim.aux (I := I) ρ s t) :
    ReindexedS I ρ (RegMachineSim.runBlock s [i])
      (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i]) := by
  intro n hn
  show RegMachineSim.get (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i]) (ρ n)
     = RegMachineSim.get (RegMachineSim.runBlock s [i]) n
  rw [RegMachineSim.evalInst_eq_set t (RegMachineSim.renameInst (S := S) ρ i) (ρ n),
      RegMachineSim.evalInst_eq_set s i n,
      RegMachineSim.writes_rename_sim ρ s t i
        (fun a _ => reindexedS_src I ρ hρd hρnd s t h a) ha]
  have hsub : ∀ p ∈ RegMachineSim.writes s i, smDisc I S p.1 = false := by
    intro p hp
    apply hz
    have hpn : p.1 ∈ (RegMachineSim.writes s i).map Prod.fst := List.mem_map_of_mem hp
    rwa [RegMachineSim.writes_names s i] at hpn
  exact setManyS_reindexed I ρ hinj hρnd (RegMachineSim.writes s i) hsub s t h n hn

/-- **Simulation theorem (registers + aux).** Threading `ReindexedS ∧ aux` through the
    block: an injective discard-preserving renaming whose written names are all
    non-discard commutes with `runBlock` on the register file, given the auxiliary
    relation holds at entry. Conclusion exposes the register agreement; `aux` is the
    maintained invariant that makes the flag/memory-reading instructions go through. -/
theorem renameBlock_runBlock_sim (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hinj : Function.Injective ρ) (hρd : ∀ r, smDisc I S r = true → smDisc I S (ρ r) = true)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false)
    (block : List I) (hz : ∀ i ∈ block, ∀ n ∈ MachineModel.writtenNames i, smDisc I S n = false)
    (s t : S) (h : ReindexedS I ρ s t) (ha : RegMachineSim.aux (I := I) ρ s t) :
    ReindexedS I ρ (RegMachineSim.runBlock s block)
      (RegMachineSim.runBlock t (renameBlockS (S := S) ρ block))
    ∧ RegMachineSim.aux (I := I) ρ (RegMachineSim.runBlock s block)
      (RegMachineSim.runBlock t (renameBlockS (S := S) ρ block)) := by
  induction block generalizing s t with
  | nil =>
    rw [show renameBlockS (S := S) ρ [] = [] from rfl,
      RegMachineSim.runBlock_nil, RegMachineSim.runBlock_nil]
    exact ⟨h, ha⟩
  | cons i is ih =>
    have hcons1 : RegMachineSim.runBlock s (i :: is)
        = RegMachineSim.runBlock (RegMachineSim.runBlock s [i]) is := by
      have := RegMachineSim.runBlock_append (I := I) s [i] is; simpa using this
    have hcons2 : RegMachineSim.runBlock t (renameBlockS (S := S) ρ (i :: is))
        = RegMachineSim.runBlock
            (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i])
            (renameBlockS (S := S) ρ is) := by
      have := RegMachineSim.runBlock_append (I := I) t
        [RegMachineSim.renameInst (S := S) ρ i] (renameBlockS (S := S) ρ is)
      simpa [renameBlockS, List.map_cons] using this
    rw [hcons1, hcons2]
    -- register read-agreement on i's read-names (from `h` via reindexedS_src)
    have hstepR : ReindexedS I ρ (RegMachineSim.runBlock s [i])
        (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i]) :=
      evalInstS_rename_preserves I ρ hinj hρd hρnd s t i
        (hz i (List.mem_cons_self ..)) h ha
    have hstepA : RegMachineSim.aux (I := I) ρ (RegMachineSim.runBlock s [i])
        (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i]) :=
      RegMachineSim.aux_step ρ s t i hinj
        (fun a _ => reindexedS_src I ρ hρd hρnd s t h a) ha
    exact ih (fun j hj => hz j (List.mem_cons_of_mem _ hj))
      (RegMachineSim.runBlock s [i])
      (RegMachineSim.runBlock t [RegMachineSim.renameInst (S := S) ρ i]) hstepR hstepA

/-- The register conclusion alone (the usual allocation-soundness statement). -/
theorem renameBlock_runBlock_sim_reindexed (I : Type) [RegMachineSim I S] (ρ : String → String)
    (hinj : Function.Injective ρ) (hρd : ∀ r, smDisc I S r = true → smDisc I S (ρ r) = true)
    (hρnd : ∀ r, smDisc I S r = false → smDisc I S (ρ r) = false)
    (block : List I) (hz : ∀ i ∈ block, ∀ n ∈ MachineModel.writtenNames i, smDisc I S n = false)
    (s t : S) (h : ReindexedS I ρ s t) (ha : RegMachineSim.aux (I := I) ρ s t) :
    ReindexedS I ρ (RegMachineSim.runBlock s block)
      (RegMachineSim.runBlock t (renameBlockS (S := S) ρ block)) :=
  (renameBlock_runBlock_sim I ρ hinj hρd hρnd block hz s t h ha).1

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
