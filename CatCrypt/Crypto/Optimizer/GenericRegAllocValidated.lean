/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# Validated renaming + no-alias checker, generically over `RegMachine`

`GenericRegAlloc.renameBlock_runBlock` proves register-renaming soundness assuming
the renaming `ρ` is **globally** injective. That is the right shape for an abstract
"validated renaming", but the concrete allocation map a backend's printer/encoder
uses is typically *not* globally injective (e.g. it returns distinct
`<UNALLOCATED:n>` sentinels off-domain, and the discard register is a fixed point).
What an aliasing-free allocation actually guarantees is injectivity on the **register
names the block uses**.

This file weakens the soundness keystone to that hypothesis, **once**, over any
`[RegMachine I S]` — so every backend with a `RegMachine` instance (ARM `AInst`,
RISC-V `RInst`, …) inherits it — and adds a **decidable no-alias checker**
(`noAliasOn`) whose `= true` result discharges the hypothesis. The result is the
translation-validation discipline (untrusted allocator + a checked renaming) of
CompCert/Jasmin, realised generically:

* `RenInjOn ns ρ` — `ρ` injective on the name list `ns` (decidable);
* `ReindexedOn I ns ρ s t` — the rename relation scoped to `ns`;
* `renameBlock_runBlock_on` — soundness needing only `RenInjOn` over the block names;
* `noAliasOn ρ block` — the decidable checker; `renameBlock_runBlock_checked`
  combines it with the keystone.

The `RegMachine.writes_rename` law is already stated with a *per-read-name*
hypothesis, so the class is set up for exactly this scoping.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.GenericRegAlloc

variable {I : Type} {S : Type}

/-! ## 1. Injective-on-a-name-list, and the block's names -/

/-- `ρ` is injective on the name list `ns` (the no-alias condition, on the names that
    matter). Decidable, so it doubles as a checkable certificate. -/
def RenInjOn (ns : List String) (ρ : String → String) : Prop :=
  ∀ a ∈ ns, ∀ b ∈ ns, ρ a = ρ b → a = b

instance (ns : List String) (ρ : String → String) : Decidable (RenInjOn ns ρ) := by
  unfold RenInjOn; infer_instance

/-- The register names one instruction mentions (written names then read names). -/
def bNamesG [MachineModel I] (i : I) : List String :=
  MachineModel.writtenNames i ++ MachineModel.readNames i

/-- Every register name a block mentions. -/
def blockNamesG [MachineModel I] (block : List I) : List String :=
  block.flatMap bNamesG

/-! ## 2. The scoped rename relation and soundness keystone -/

/-- `Reindexed` scoped to a name list `ns`: the renamed state agrees at `ρ n` with the
    source at `n`, for every `n ∈ ns` whose image is not a discard register. -/
def ReindexedOn (I : Type) [RegMachine I S] (ns : List String) (ρ : String → String)
    (s t : S) : Prop :=
  ∀ n ∈ ns, rmDisc I S (ρ n) = false → rmGet I t (ρ n) = rmGet I s n

/-- Renamed read = source read, on `ns`. (Discard reads agree by `get_discard`; otherwise
    `ReindexedOn` applies, using `a ∈ ns`.) -/
theorem reindexedOn_src (I : Type) [RegMachine I S] (ns : List String) (ρ : String → String)
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (h : ReindexedOn I ns ρ s t) (a : String) (ha : a ∈ ns) :
    rmGet I t (ρ a) = rmGet I s a := by
  by_cases hx : rmDisc I S a = true
  · exact RegMachine.get_discard t s (ρ a) a (hρd a hx) hx
  · exact h a ha (hρnd a (by simpa using hx))

/-- **A single `set` preserves `ReindexedOn`**, scoped to `ns` (injective only on `ns`).
    The per-write atom the scoped multi-output step iterates. -/
theorem set_step_reindexedOn (I : Type) [RegMachine I S] (ns : List String)
    (ρ : String → String) (hinj : RenInjOn ns ρ)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (n : String) (v : RegMachine.Val I S)
    (hnns : n ∈ ns) (hz : rmDisc I S n = false) (h : ReindexedOn I ns ρ s t) :
    ReindexedOn I ns ρ (RegMachine.set (I := I) s n v) (RegMachine.set (I := I) t (ρ n) v) := by
  intro m hmns hm
  show RegMachine.get _ _ = RegMachine.get _ _
  have hzρ : rmDisc I S (ρ n) = false := hρnd _ hz
  by_cases hd : m = n
  · subst hd
    rw [RegMachine.get_set_same _ _ _ hzρ, RegMachine.get_set_same _ _ _ hz]
  · have hne : ρ n ≠ ρ m := fun hc => hd (hinj m hmns n hnns hc.symm)
    rw [RegMachine.get_set_other _ _ _ _ hne, RegMachine.get_set_other _ _ _ _ (Ne.symm hd)]
    exact h m hmns hm

/-- **A whole list of writes preserves `ReindexedOn`** — iterate `set_step_reindexedOn`,
    each written name lying in `ns`. -/
theorem setMany_reindexedOn (I : Type) [RegMachine I S] (ns : List String)
    (ρ : String → String) (hinj : RenInjOn ns ρ)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false) :
    ∀ (pairs : List (String × RegMachine.Val I S)),
      (∀ p ∈ pairs, p.1 ∈ ns) → (∀ p ∈ pairs, rmDisc I S p.1 = false) →
      ∀ (s t : S), ReindexedOn I ns ρ s t →
        ReindexedOn I ns ρ (setMany I s pairs)
          (setMany I t (pairs.map (fun p => (ρ p.1, p.2)))) := by
  intro pairs
  induction pairs with
  | nil => intro _ _ s t h; exact h
  | cons p ps ih =>
    intro hns hz s t h
    have hstep := set_step_reindexedOn I ns ρ hinj hρnd s t p.1 p.2
      (hns p (List.mem_cons_self ..)) (hz p (List.mem_cons_self ..)) h
    have hrest := ih (fun q hq => hns q (List.mem_cons_of_mem _ hq))
      (fun q hq => hz q (List.mem_cons_of_mem _ hq))
      (RegMachine.set (I := I) s p.1 p.2) (RegMachine.set (I := I) t (ρ p.1) p.2) hstep
    simpa [setMany_cons, List.map_cons] using hrest

/-- One step preserves `ReindexedOn` when `ρ` is injective on `ns`, preserves the discard
    set, every destination is non-discard, and the instruction's names lie in `ns`. Over
    the multi-output write-list, this is `setMany_reindexedOn` on `writes s i`. -/
theorem evalInst_rename_preservesOn (I : Type) [RegMachine I S] (ns : List String)
    (ρ : String → String) (hinj : RenInjOn ns ρ)
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (s t : S) (i : I) (hwn : ∀ n ∈ MachineModel.writtenNames i, n ∈ ns)
    (hrn : ∀ a ∈ MachineModel.readNames i, a ∈ ns)
    (hz : ∀ n ∈ MachineModel.writtenNames i, rmDisc I S n = false)
    (h : ReindexedOn I ns ρ s t) :
    ReindexedOn I ns ρ (rmRun I s [i]) (rmRun I t [rmRename S ρ i]) := by
  intro n hnns hn
  show RegMachine.get (RegMachine.runBlock t [rmRename S ρ i]) (ρ n)
     = RegMachine.get (RegMachine.runBlock s [i]) n
  rw [RegMachine.evalInst_eq_set t (rmRename S ρ i) (ρ n),
      RegMachine.evalInst_eq_set s i n,
      RegMachine.writes_rename ρ s t i
        (fun a ha => reindexedOn_src I ns ρ hρd hρnd s t h a (hrn a ha))]
  have hsubns : ∀ p ∈ RegMachine.writes s i, p.1 ∈ ns := by
    intro p hp
    apply hwn
    have hpn : p.1 ∈ (RegMachine.writes s i).map Prod.fst := List.mem_map_of_mem hp
    rwa [RegMachine.writes_names s i] at hpn
  have hsubz : ∀ p ∈ RegMachine.writes s i, rmDisc I S p.1 = false := by
    intro p hp
    apply hz
    have hpn : p.1 ∈ (RegMachine.writes s i).map Prod.fst := List.mem_map_of_mem hp
    rwa [RegMachine.writes_names s i] at hpn
  exact setMany_reindexedOn I ns ρ hinj hρnd (RegMachine.writes s i) hsubns hsubz s t h n hnns hn

/-- **Scoped resident-path soundness.** For `ρ` injective on a name list `ns` that
    contains every name the block mentions, running the renamed block preserves
    `ReindexedOn` — the validated-renaming keystone needing only the *no-alias on the
    block's names* property, recovered once for every `RegMachine` backend. -/
theorem renameBlock_runBlock_on (I : Type) [RegMachine I S] (ns : List String)
    (ρ : String → String) (hinj : RenInjOn ns ρ)
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (block : List I) (hsub : ∀ n ∈ blockNamesG block, n ∈ ns)
    (hz : ∀ i ∈ block, ∀ n ∈ MachineModel.writtenNames i, rmDisc I S n = false)
    (s t : S) (h : ReindexedOn I ns ρ s t) :
    ReindexedOn I ns ρ (rmRun I s block) (rmRun I t (renameBlock (S := S) ρ block)) := by
  induction block generalizing s t with
  | nil =>
    rw [show renameBlock (S := S) ρ [] = [] from rfl, rmRun_nil, rmRun_nil]; exact h
  | cons i is ih =>
    have hin : ∀ n ∈ bNamesG i, n ∈ ns := fun n hn =>
      hsub n (by simp only [blockNamesG, List.flatMap_cons, List.mem_append]; exact Or.inl hn)
    have his : ∀ n ∈ blockNamesG is, n ∈ ns := fun n hn =>
      hsub n (by simp only [blockNamesG, List.flatMap_cons, List.mem_append]; exact Or.inr hn)
    have hwn : ∀ n ∈ MachineModel.writtenNames i, n ∈ ns := fun n hn =>
      hin n (by simp only [bNamesG, List.mem_append]; exact Or.inl hn)
    have hrn : ∀ a ∈ MachineModel.readNames i, a ∈ ns := fun a ha =>
      hin a (by simp only [bNamesG, List.mem_append]; exact Or.inr ha)
    rw [renameBlock_cons, rmRun_cons I s i is,
      rmRun_cons I t (rmRename S ρ i) (renameBlock (S := S) ρ is)]
    exact ih his (fun j hj => hz j (List.mem_cons_of_mem _ hj)) (rmRun I s [i])
      (rmRun I t [rmRename S ρ i])
      (evalInst_rename_preservesOn I ns ρ hinj hρd hρnd s t i hwn hrn
        (hz i (List.mem_cons_self ..)) h)

/-! ## 3. The decidable no-alias checker -/

/-- **The no-alias checker.** Decides whether the renaming `ρ` is injective on the
    block's register names — i.e. no two live names share a target register. A
    backend's untrusted allocator produces `ρ`; this checks it. -/
def noAliasOn [MachineModel I] (ρ : String → String) (block : List I) : Bool :=
  decide (RenInjOn (blockNamesG block) ρ)

/-- The checker is sound: passing it yields the no-alias certificate on the block names. -/
theorem noAliasOn_sound [MachineModel I] (ρ : String → String) (block : List I)
    (h : noAliasOn ρ block = true) : RenInjOn (blockNamesG block) ρ := by
  unfold noAliasOn at h; exact of_decide_eq_true h

/-- **Validated renaming, checked.** With the no-alias checker passing on the block,
    a discard-preserving renaming with all destinations non-discard is sound: the
    renamed block computes at `ρ n` what the original computes at `n`, for the block's
    names. The translation-validation statement — untrusted allocator, checked output. -/
theorem renameBlock_runBlock_checked (I : Type) [RegMachine I S] (ρ : String → String)
    (hρd : ∀ r, rmDisc I S r = true → rmDisc I S (ρ r) = true)
    (hρnd : ∀ r, rmDisc I S r = false → rmDisc I S (ρ r) = false)
    (block : List I) (hchk : noAliasOn ρ block = true)
    (hz : ∀ i ∈ block, ∀ n ∈ MachineModel.writtenNames i, rmDisc I S n = false)
    (s t : S) (h : ReindexedOn I (blockNamesG block) ρ s t) :
    ReindexedOn I (blockNamesG block) ρ (rmRun I s block)
      (rmRun I t (renameBlock (S := S) ρ block)) :=
  renameBlock_runBlock_on I (blockNamesG block) ρ (noAliasOn_sound ρ block hchk)
    hρd hρnd block (fun _ hn => hn) hz s t h

end CatCrypt.Crypto.Optimizer.GenericRegAlloc
