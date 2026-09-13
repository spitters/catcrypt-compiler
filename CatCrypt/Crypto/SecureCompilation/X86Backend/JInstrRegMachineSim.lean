/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAllocSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine

/-!
# The full `RegMachineSim (JInstr 64) (JState 64)` instance (the x86 flags+memory sim)

`GenericRegAlloc.RegMachineSim` is `RegMachine`'s register data plus an abstract,
ρ-aware auxiliary relation `aux` and the two laws `writes_rename_sim` /`aux_step`. The
x86 backend's `JInstrRegMachine` file already supplies, for `JInstr 64`/`JState 64`,
every register field (`writesJ`, `evalInst_eq_setJ`, `writesJ_names`,
`instMachineModelJInstr`) and the conditional renaming-commutation `writesJ_rename`
with its two extra hypotheses (`hflag : t.flags = s.flags`,
`hmem : ∀ b o, t.mem (ρ b) o = s.mem b o`). This file closes the loop: it takes

```
auxJ ρ s t := t.flags = s.flags ∧ (∀ b o, t.mem (ρ b) o = s.mem b o)
```

— exactly the two hypotheses `writesJ_rename` consumes — and proves `aux_step`
(`auxJ` is preserved by a renamed step), so the full instance `instRegMachineSimJInstr`
elaborates and the generic theorem `renameBlock_runBlock_sim_reindexed` applies to x86.

## `aux_step`, the only new proof

`auxJ` has two clauses; a renamed `evalInstr` step preserves each:

* **Flags.** Flags are written by the `writeB5W` ALU arms, by the flag-only `test`/`cmp`
  (a `writeB5`), by the rotates `rol`/`ror` (a `writeB2W`, which sets `of`/`cf` and
  carries `sf`/`pf`/`zf` over), by `adcx`/`adox` (which set `cf`/`of` to the
  `x86_ADCX` carry-out), by `inc`/`dec` (four flags, `cf` kept), by the multiplies
  `imulri`/`mul`/`imulWide`, the double shifts `shld`/`shrd`, the carry rotates
  `rcl`/`rcr`, the flag-only `testN`/`bt`, and by `btr`/`bts` (`cf` only); every other
  arm of `evalInstr` leaves `flags` untouched. On the
  flag-writing arms both sides compute the *same* flags: the data inputs agree by the
  register read-agreement on the read-names (the destination — for `test`/`cmp`, the
  first operand; for `andn`, the two sources — and the source operand), and for
  `adc`/`sbb`/`adcx`/`adox`/`rol`/`ror` the *incoming* flags agree because `auxJ` carries
  `t.flags = s.flags`. The arms that touch no flag close on `hflag` alone.

* **Memory (agree-under-ρ).** `s.mem` changes only on `storeMem`/`storeMemIdx` (loads
  write a *register*, and `test` only flags) and on `loadSym` (which aliases the
  destination's bank onto the symbol's). Every other arm leaves `mem` untouched, so
  `auxJ.2` carries through verbatim. On the stores both sides write the *same* value (register
  read-agreement on the stored source) at the *same* slot under ρ (the base register is
  renamed and agrees by read-agreement); on `loadSym` injectivity of ρ turns
  `ρ b = ρ d ↔ b = d` and the aliased read `t.mem (ρ sym) o = s.mem sym o` is the `sym`
  instance of `auxJ.2`. So the memory clause is preserved per-arm using `Injective ρ`
  and `auxJ.2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachineSim

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-! ## 1. The auxiliary relation -/

/-- The x86 auxiliary (non-register) simulation relation: the renamed state `t` and the
    source state `s` have **equal flags** and **memory agreeing under ρ** (cell `(ρ b, o)`
    of `t` equals cell `(b, o)` of `s`). These are *exactly* the two extra hypotheses
    `writesJ_rename` consumes (`hflag`/`hmem`), so `writes_rename_sim` is just
    `writesJ_rename` fed `auxJ`'s two projections. -/
def auxJ (ρ : String → String) (s t : JState 64) : Prop :=
  t.flags = s.flags ∧ (∀ b o, t.mem (ρ b) o = s.mem b o)

/-! ## 2. `aux_step`: a renamed step preserves `auxJ` -/

/-- The register read-agreement form used throughout: reading register `a` in `t` at
    `ρ a` equals reading it in `s` at `a`, for every read-name `a` of `i`. -/
abbrev ReadAgree (ρ : String → String) (s t : JState 64) (i : JInstr 64) : Prop :=
  ∀ a ∈ MachineModel.readNames i, t.get (ρ a) = s.get a

/-- **`auxJ` is preserved by a renamed step.** Given `ρ` injective, register
    read-agreement on `i`'s read-names, and `auxJ ρ s t`, the step
    `runBlock s [i]` / `runBlock t [renameInstr ρ i]` again satisfies `auxJ`. Proved
    clause-by-clause (flags, memory) over every constructor. -/
theorem aux_stepJ (ρ : String → String) (s t : JState 64) (i : JInstr 64)
    (hinj : Function.Injective ρ) (h : ReadAgree ρ s t i) (ha : auxJ ρ s t) :
    auxJ ρ (runBlock s [i]) (runBlock t [renameInstr ρ i]) := by
  obtain ⟨hflag, hmem⟩ := ha
  simp only [runBlock_cons, runBlock_nil]
  refine ⟨?_, ?_⟩
  · -- Flags clause: `(evalInstr t (renameInstr ρ i)).flags = (evalInstr s i).flags`.
    -- The `writeB5W`/ADX arms set flags from the inputs, so they need the operand and
    -- carry-flag agreement (`hd`/`hs`, `hflag` via `flagB`); the rest leave flags
    -- untouched and close on `hflag` alone.
    have hcf : t.flagB (·.cf) = s.flagB (·.cf) := by simp [JState.flagB, hflag]
    have hof : t.flagB (·.of) = s.flagB (·.of) := by simp [JState.flagB, hflag]
    cases i with
    | add d src | sub d src | imul d src | and_ d src | or_ d src | xor_ d src
    | shl d src | shr d src | sar d src =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, JState.writeB5W, hs, hd]
    | test d src =>
      -- `test`'s read-names are its first operand `d` and the source operand; it writes
      -- the five flags through `writeB5` and no register.
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, JState.writeB5, hs, hd]
    | adc d src | sbb d src =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, JState.writeB5W, hs, hd, hcf]
    | neg d =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      simp only [renameInstr, evalInstr, JState.writeB5W, hd]
    | adcx d src =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, hs, hd, hcf, hflag]
    | adox d src =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, hs, hd, hof, hflag]
    | cmp a src =>
      -- `cmp`'s read-names are its first operand `a` and the source operand; it writes the
      -- five flags through `writeB5` and no register.
      have hd : t.get (ρ a) = s.get a := h a (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [renameInstr, evalInstr, JState.writeB5, hs, hd]
    | andn d a b =>
      -- BMI1 `andn` is non-destructive in both sources: its read-names are `a` and `b`.
      have ha : t.get (ρ a) = s.get a := h a (List.mem_cons_self ..)
      have hb : t.get (ρ b) = s.get b := h b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp only [renameInstr, evalInstr, JState.writeB5W, ha, hb]
    | rol d amt | ror d amt =>
      -- The rotates write `OF`/`CF` from the inputs and carry `SF`/`PF`/`ZF` over from the
      -- incoming flag map, so both the input agreement and `hflag` are needed.
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ amt).eval t = amt.eval s :=
        renameOperand_eval_rename amt (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [renameInstr, evalInstr, JState.writeB2W, hs, hd, hflag]
    | inc d | dec d =>
      -- `inc`/`dec` write `OF`/`SF`/`PF`/`ZF` from the operand and keep `CF`.
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      simp only [renameInstr, evalInstr, JState.writeB4W, hd, hflag]
    | imulri d src imm =>
      have hs : t.get (ρ src) = s.get src := h src (List.mem_cons_self ..)
      simp only [renameInstr, evalInstr, JState.writeB5W, hs]
    | mul dh lo src | imulWide dh lo src =>
      have hl : t.get (ρ lo) = s.get lo := h lo (List.mem_cons_self ..)
      have hs : t.get (ρ src) = s.get src :=
        h src (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp only [renameInstr, evalInstr, JState.writeB5W2, hl, hs]
    | shld d src amt | shrd d src amt =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hsr : t.get (ρ src) = s.get src :=
        h src (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hs : (renameOperand ρ amt).eval t = amt.eval s :=
        renameOperand_eval_rename amt (fun x hx =>
          h x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      simp only [renameInstr, evalInstr, JState.writeB5W, hs, hd, hsr]
    | rcl d amt | rcr d amt =>
      -- The carry rotates read the incoming `CF` and carry `SF`/`PF`/`ZF` over.
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ amt).eval t = amt.eval s :=
        renameOperand_eval_rename amt (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [renameInstr, evalInstr, JState.writeB2W, hs, hd, hcf, hflag]
    | testN sz a b | bt a b =>
      have ha : t.get (ρ a) = s.get a := h a (List.mem_cons_self ..)
      have hs : (renameOperand ρ b).eval t = b.eval s :=
        renameOperand_eval_rename b (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [renameInstr, evalInstr, JState.writeB5N, hs, ha, hflag]
    | btr d b | bts d b =>
      have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
      have hs : (renameOperand ρ b).eval t = b.eval s :=
        renameOperand_eval_rename b (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [renameInstr, evalInstr, JState.writeCFW, hs, hd, hflag]
    | _ =>
      simp only [renameInstr, evalInstr, JState.setReg, JState.setRegMerge, JState.store,
        JState.storeIdx, hflag]
  · -- Memory clause: `∀ b o, (evalInstr t (renameInstr ρ i)).mem (ρ b) o
    --                       = (evalInstr s i).mem b o`.
    intro b o
    cases i with
    | storeMem base off src =>
      have hbase : t.get (ρ base) = s.get base := h base (List.mem_cons_self ..)
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [renameInstr, evalInstr, JState.store, hs, x86_MOV]
      by_cases hbb : b = base
      · subst hbb
        by_cases ho : o = off
        · subst ho; simp
        · rw [if_neg (fun hc => ho hc.2), if_neg (fun hc => ho hc.2)]; exact hmem b o
      · have hne : ρ b ≠ ρ base := fun he => hbb (hinj he)
        rw [if_neg (fun hc => hne hc.1), if_neg (fun hc => hbb hc.1)]; exact hmem b o
    | storeMemIdx base idx scale src =>
      have hbase : t.get (ρ base) = s.get base := h base (List.mem_cons_self ..)
      have hidxR : t.regs (ρ idx) = s.regs idx :=
        h idx (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hs : (renameOperand ρ src).eval t = src.eval s :=
        renameOperand_eval_rename src (fun a ha =>
          h a (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)))
      -- normalise both stores to the SAME effective offset `scale * (s.regs idx).toNat`.
      simp only [renameInstr, evalInstr, JState.storeIdx, JState.store, hs, JState.get, hidxR,
        x86_MOV]
      by_cases hbb : b = base
      · subst hbb
        by_cases ho : o = ((scale : Int) * ((s.regs idx).toNat : Int))
        · subst ho; simp
        · simp only [ho, and_false, ↓reduceIte]; exact hmem b o
      · have hne : ρ b ≠ ρ base := fun he => hbb (hinj he)
        simp only [hne, hbb, false_and, ↓reduceIte]; exact hmem b o
    | test a src =>
      -- `test` writes only the five flags, so both sides keep their own memory.
      simp only [renameInstr, evalInstr, JState.writeB5]
      exact hmem b o
    | loadSym d sym =>
      simp only [renameInstr, evalInstr]
      by_cases hbd : b = d
      · subst hbd; simpa using hmem sym o
      · have hne : ρ b ≠ ρ d := fun he => hbd (hinj he)
        simp only [if_neg hne, if_neg hbd]; exact hmem b o
    | _ =>
      simp only [renameInstr, evalInstr, JState.setReg, JState.writeB5W, JState.writeB5,
        JState.writeB2W]
      exact hmem b o

/-! ## 3. The full instance -/

/-- **The full `RegMachineSim (JInstr 64) (JState 64)` instance.** Wires the already-built
    x86 register data (`writesJ`/`evalInst_eq_setJ`/`writesJ_names`/`instMachineModelJInstr`)
    plus the auxiliary relation `auxJ`, its `writes_rename_sim` (= `writesJ_rename` fed
    `auxJ`'s two projections), and `aux_step` (= `aux_stepJ`). This is the x86
    register-allocation soundness instance with a flags+memory simulation relation; the
    generic theorem `renameBlock_runBlock_sim_reindexed` then gives resident-path
    soundness for the full x86 scalar instruction set. -/
instance instRegMachineSimJInstr : RegMachineSim (JInstr 64) (JState 64) where
  toMachineModel := instMachineModelJInstr
  runBlock := runBlock
  Val := BitVec 64
  get := JState.get
  set := JState.setReg
  writes := writesJ
  renameInst := renameInstr
  isDiscard := fun _ => false
  aux := auxJ
  get_discard := by intro _ _ _ _ h; simp at h
  get_set_same := by intro s r v _; exact JState.get_setReg_same s r v
  get_set_other := by intro s r r' v h; exact JState.get_setReg_other s r' r v (Ne.symm h)
  evalInst_eq_set := evalInst_eq_setJ
  runBlock_nil := runBlock_nil
  runBlock_append := fun s xs ys =>
    CatCrypt.Crypto.Optimizer.SpillingRegAlloc.runBlock_append (s := s) xs ys
  writes_names := writesJ_names
  writes_rename_sim := fun ρ s t i hread haux => writesJ_rename ρ s t i hread haux.1 haux.2
  aux_step := aux_stepJ

/-! ## 4. Sanity: the x86 resident-path soundness through the generic theorem -/

/-- **x86 resident-path register-allocation soundness.** Instantiating the generic
    simulation theorem `renameBlock_runBlock_sim_reindexed` at `JInstr 64`/`JState 64`:
    for an injective, discard-preserving renaming whose written names are all non-discard,
    if the source and renamed states are register-`ReindexedS`-related and satisfy `auxJ`
    at entry, then they remain `ReindexedS`-related after running the original vs renamed
    block. The `auxJ` (flags + memory) invariant is what carries the flag- and
    memory-reading x86 instructions through. -/
theorem jinstr_renameBlock_sound (ρ : String → String) (hinj : Function.Injective ρ)
    (hρd : ∀ r, smDisc (JInstr 64) (JState 64) r = true →
      smDisc (JInstr 64) (JState 64) (ρ r) = true)
    (hρnd : ∀ r, smDisc (JInstr 64) (JState 64) r = false →
      smDisc (JInstr 64) (JState 64) (ρ r) = false)
    (block : List (JInstr 64))
    (hz : ∀ i ∈ block, ∀ n ∈ MachineModel.writtenNames i,
      smDisc (JInstr 64) (JState 64) n = false)
    (s t : JState 64) (h : ReindexedS (JInstr 64) ρ s t)
    (ha : RegMachineSim.aux (I := JInstr 64) ρ s t) :
    ReindexedS (JInstr 64) ρ (RegMachineSim.runBlock s block)
      (RegMachineSim.runBlock t (renameBlockS (S := JState 64) ρ block)) :=
  renameBlock_runBlock_sim_reindexed (JInstr 64) ρ hinj hρd hρnd block hz s t h ha

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachineSim
