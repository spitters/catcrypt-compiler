/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Verified store-to-load forwarding: recover register-residence on a frame-resident
  straight-line body (#412)

`RandomizedRegAlloc.lean` (#386) is a **renaming** pass: a register-allocation
choice is a bijection `ρ` of the SSA virtual-register names a `JInstr` block uses.
Renaming is exactly the degree of freedom of register *allocation* — but it is the
wrong lever for the X25519 monolithic ladder body (#411). That body is
**frame-resident**: each inlined field op loads its operands from a frame buffer
(`loadMem fp off`), computes in registers, and stores its result back to the frame
(`storeMem fp off`). The cross-op state lives in **memory**, round-tripped op to op.

A whole-body rename cannot help: the body has 176 distinct register names against a
13-slot GP pool, so a bijection cannot fit (it is not a spiller — `allocOverflow`
reports 162 names over budget). A per-op rename cannot help either: renaming an op's
scratch leaves its `loadMem`/`storeMem` instructions **in place**, so the frame
round-trip survives any renaming. The residual is the round-trip itself, not the
allocation: 96 `loadMem` + 68 `storeMem` = 164 frame accesses per ladder step, many
of which reload a value the *previous* op's `storeMem` just wrote to the same cell.

The lever that recovers residence is **store-to-load forwarding** (a classic
peephole, the dual of the renaming move): when op N stores a register `r` to frame
cell `(fp, off)` and op N+1 reloads that same cell into `d`, with no intervening
write to either the cell or `r`, the reload `loadMem d fp off` denotes the same
value as the register move `mov d r` — because memory at `(fp, off)` still holds
what `r` held. Rewriting the load to the move keeps the value **register-resident**
(the load becomes a register-to-register copy the renamer/scheduler can then often
elide entirely) and drops the dependence on the memory subsystem for that hop.

## What is proved (sorry-free)

`storeToLoadForward` is a forward scan carrying a small environment `held` mapping
each frame cell to the register currently known to hold its value. The soundness
theorem `forward_runBlock` is **fully general**: for any block, running the
forwarded block from any state lands in the *same* `runBlock` final state as the
original — the rewrite is denotation-preserving against the validated `JasminModel`
(`evalInstr`/`runBlock`), so it composes through `X86Dialect.lowerBlock_denote_closed`
exactly as the field leaves do. The held-environment invariant
(`HeldValid`: every recorded `(cell ↦ r)` actually has `s.mem cell = s.regs r`) is
the loop invariant carried through the scan; it is what makes the `loadMem → mov`
rewrite value-preserving at each forwarded site.

This is the in-Lean translation-validation certificate for the **forwarding**
dimension, the companion to `RandomizedRegAlloc.regalloc_runBlock_sound` for the
**renaming** dimension. Together they are the two CryptOpt-class moves (allocation
+ memory-traffic elimination) on a frame-resident body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.StoreToLoadForward

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. The held environment

`Held` maps a frame cell `(base, off)` to the register name currently known to hold
its value. We use a plain association list; `lookup`/`insert`/`invalidate` keep it
sound under the scan. A cell is **forwardable** to `r` when `(base, off) ↦ r` and
neither the cell nor `r` has been written since the store. -/

/-- The forwarding environment: frame cell `(base, off)` ↦ register holding it. -/
abbrev Held := List ((String × Int) × String)

/-- Look up the register currently holding frame cell `(base, off)`. -/
def Held.find (h : Held) (base : String) (off : Int) : Option String :=
  (h.lookup (base, off))

/-- Drop every entry whose **held register** is `r` (called when a register `r` is
    written: a cell forwardable to `r` stops being forwardable once `r` changes). -/
def Held.killReg (h : Held) (r : String) : Held :=
  h.filter (fun e => e.2 ≠ r)

/-- Drop the entry for cell `(base, off)` (called when that cell is overwritten by a
    store of a value we do not track as a single register, or conservatively on any
    memory write to it). -/
def Held.killCell (h : Held) (base : String) (off : Int) : Held :=
  h.filter (fun e => e.1 ≠ (base, off))

/-- Record that frame cell `(base, off)` now holds register `r` (a `storeMem` of
    `.reg r`, or a forwarded `loadMem` into `r`). First drop any stale entry for the
    same cell, then add the new binding. -/
def Held.set (h : Held) (base : String) (off : Int) (r : String) : Held :=
  (h.killCell base off) ++ [((base, off), r)]

/-! ## 2. The forwarding scan

`forwardStep held i` returns the (possibly rewritten) instruction together with the
updated environment. The only rewrite is `loadMem d base off → mov d (.reg r)` when
`held.find base off = some r` and `r ≠ d`. Every instruction updates `held` to
preserve the invariant: a register write `kills` that register's entries; a
`storeMem (.reg r)` `sets` the cell to `r` (after killing the cell); any other
memory or unknown write is handled conservatively (kill the affected cell). -/

/-- The registers an instruction writes, used to invalidate stale held entries.
    `mulx`/`mulxMem`, `mul`/`imulWide` (high and low word) and `xchg` (both
    operands) write two; the flag-only instructions write none. -/
def writtenRegs : JInstr 64 → List String
  | .mov d _ | .add d _ | .sub d _ | .adc d _ | .sbb d _ | .imul d _ | .neg d | .setc d
  | .and_ d _ | .or_ d _ | .xor_ d _ | .shl d _ | .shr d _ | .sar d _
  | .cmove d _ | .cmovne d _ | .cmovb d _ | .adcx d _ | .adox d _ | .loadMem d _ _
  | .loadMemIdx d _ _ _ | .loadSym d _
  | .not_ d | .andn d _ _ | .rol d _ | .ror d _ | .rorx d _ _
  | .shlx d _ _ | .shrx d _ _ | .sarx d _ _
  | .movzx d _ _ | .movsx d _ _ | .lea d _ _ _ _ => [d]
  | .mulx dh dl _ _ => [dh, dl]
  | .mulxMem dh dl _ _ _ => [dh, dl]
  | .storeMem _ _ _ | .storeMemIdx _ _ _ _ => []
  -- `test` and `cmp` write the five flags only, so they invalidate no held register.
  | .test _ _ => []
  | .cmp _ _ => []
  | .inc d | .dec d | .imulri d _ _ | .shld d _ _ | .shrd d _ _ | .rcl d _ | .rcr d _
  | .cmovcc _ d _ | .setcc _ d | .btr d _ | .bts d _ => [d]
  | .xchg a b => [a, b]
  | .mul dh dl _ | .imulWide dh dl _ => [dh, dl]
  -- `clc`, `stc`, `testN` and `bt` write flags only.
  | .clc | .stc | .testN _ _ _ | .bt _ _ => []

/-- Kill every written register's held entries (one `Held.killReg` per dst). -/
def killWritten (h : Held) (i : JInstr 64) : Held :=
  (writtenRegs i).foldl Held.killReg h

/-- One forwarding step: rewrite a `loadMem` to a `mov` when its cell is forwardable,
    then update the environment. Returns `(rewritten instruction, new held env)`. -/
def forwardStep (h : Held) : JInstr 64 → (JInstr 64 × Held)
  | .loadMem d base off =>
      match h.find base off with
      | some r =>
          if r = d then
            -- the load would reload exactly the register we are about to clobber;
            -- still a valid forward (mov d r is a no-op), but record d holds cell.
            (.mov d (.reg r), (killWritten h (.loadMem d base off)).set base off d)
          else
            (.mov d (.reg r), (killWritten h (.loadMem d base off)).set base off d)
      | none =>
          (.loadMem d base off, (killWritten h (.loadMem d base off)).set base off d)
  | .storeMem base off (.reg r) =>
      -- after the store, cell (base,off) holds register r
      (.storeMem base off (.reg r), (h.killCell base off).set base off r)
  | .storeMem base off (.imm v) =>
      -- storing an immediate: we do not track an immediate as a register, kill cell
      (.storeMem base off (.imm v), h.killCell base off)
  | .storeMemIdx base idx scale src =>
      -- a dynamic-index store `[base+idx·scale]` may alias ANY held cell, and we
      -- cannot resolve the address statically: conservatively forget every binding.
      (.storeMemIdx base idx scale src, [])
  | .loadSym d sym =>
      -- `leaq sym(%rip), %d` re-points the base register `d` at the `.rodata` table
      -- `sym`: in the `evalInstr` model it re-aliases the memory bank at base `d`
      -- (so a later `loadMemIdx _ d i scale` reads `sym[i]`). Any held binding whose
      -- cell is based at `d` is thereby invalidated. As we cannot resolve which
      -- cells alias statically, conservatively forget every binding (mirroring the
      -- dynamic-index store). The instruction itself is not rewritten.
      (.loadSym d sym, [])
  | i =>
      -- any other instruction (incl. `loadMemIdx`, which writes a GP and reads —
      -- but does not write — memory): kill the registers it writes; cell bindings
      -- survive (no static-cell memory write).
      (i, killWritten h i)

/-- Run the forwarding scan over a whole block (threading `held`). -/
def forwardAux : Held → List (JInstr 64) → List (JInstr 64)
  | _, [] => []
  | h, i :: is =>
      let (i', h') := forwardStep h i
      i' :: forwardAux h' is

/-- **The store-to-load forwarding pass.** Start with an empty held environment
    (nothing known to be in a register). -/
def storeToLoadForward (block : List (JInstr 64)) : List (JInstr 64) :=
  forwardAux [] block

@[simp] theorem forwardAux_nil (h : Held) : forwardAux h [] = [] := rfl

@[simp] theorem forwardAux_cons (h : Held) (i : JInstr 64) (is : List (JInstr 64)) :
    forwardAux h (i :: is) =
      (forwardStep h i).1 :: forwardAux (forwardStep h i).2 is := by
  simp [forwardAux]

theorem forwardAux_length (h : Held) (block : List (JInstr 64)) :
    (forwardAux h block).length = block.length := by
  induction block generalizing h with
  | nil => rfl
  | cons i is ih => simp [forwardAux_cons, ih]

@[simp] theorem storeToLoadForward_length (block : List (JInstr 64)) :
    (storeToLoadForward block).length = block.length := forwardAux_length [] block

/-! ## 3. The held-environment invariant and the translation-validation theorem

`HeldValid h s` says every recorded binding `(base, off) ↦ r` is **true** in `s`:
the memory cell `(base, off)` holds exactly what register `r` holds. This is the
loop invariant the scan maintains, and exactly the fact that makes the
`loadMem d base off → mov d (.reg r)` rewrite value-preserving: the load reads
`s.mem base off`, the move reads `s.regs r`, and the invariant says they are equal. -/

/-- A `lookup`/`find` hit is a member of the list with that key/value. -/
theorem find_mem {h : Held} {base : String} {off : Int} {r : String}
    (hf : h.find base off = some r) : ((base, off), r) ∈ h := by
  unfold Held.find at hf
  induction h with
  | nil => simp [List.lookup] at hf
  | cons e es ih =>
    obtain ⟨ekey, eval⟩ := e
    rw [List.lookup] at hf
    by_cases hk : ((base, off) == ekey) = true
    · rw [hk] at hf
      have hke : (base, off) = ekey := by simpa using hk
      have hre : eval = r := by simpa using hf
      subst hke; subst hre
      exact List.mem_cons_self
    · simp only [Bool.not_eq_true] at hk
      rw [hk] at hf
      exact List.mem_cons_of_mem _ (ih hf)

/-- Every binding in `h` is realised by the state `s`: the cell holds the register.
    Stated on **membership** (not `find`) so it is monotone under `filter` — a kill
    can only shrink `h`, so it never breaks the invariant. -/
def HeldValid (h : Held) (s : JState 64) : Prop :=
  ∀ e ∈ h, s.load e.1.1 e.1.2 = s.get e.2

/-- The `find`-level consequence used at a forwarding site: a `find` hit yields the
    cell/reg equality. -/
theorem heldValid_find {h : Held} {s : JState 64} (hv : HeldValid h s)
    {base : String} {off : Int} {r : String} (hf : h.find base off = some r) :
    s.load base off = s.get r := by
  have := hv _ (find_mem hf); simpa using this

/-- `killReg`/`killCell` only drop entries, so a binding of the killed env was a
    binding of the original — the invariant transfers along membership. -/
theorem HeldValid.filter {h : Held} {s : JState 64} (hv : HeldValid h s)
    (p : ((String × Int) × String) → Bool) : HeldValid (h.filter p) s := by
  intro e he; exact hv e (List.mem_filter.mp he).1

theorem HeldValid.killReg {h : Held} {s : JState 64} (hv : HeldValid h s) (r : String) :
    HeldValid (h.killReg r) s := hv.filter _

theorem HeldValid.killCell {h : Held} {s : JState 64} (hv : HeldValid h s)
    (base : String) (off : Int) : HeldValid (h.killCell base off) s := hv.filter _

/-! ### Invariant transfer across one instruction step

An instruction that writes only registers `{ds}` (never memory) preserves
`HeldValid` of the `ds`-killed environment: surviving entries hold a register
`≠ any d`, so their register value is unchanged, and their cell value is unchanged
(no memory write). The `setReg`/`writeB5W`/`adc`-record/`mulx` arms of `evalInstr`
are all register-only writes; only `storeMem` writes memory. -/

/-- A member of `foldl killReg h ws` is a member of `h` whose held register is not
    any element of `ws`. -/
theorem mem_foldl_killReg {e : (String × Int) × String} :
    ∀ (ws : List String) (h : Held), e ∈ ws.foldl Held.killReg h →
      e ∈ h ∧ e.2 ∉ ws := by
  intro ws
  induction ws with
  | nil => intro h he; exact ⟨he, by simp⟩
  | cons w ws ih =>
    intro h he
    simp only [List.foldl_cons] at he
    obtain ⟨hmem', hnin⟩ := ih (h.killReg w) he
    have hkr := hmem'
    unfold Held.killReg at hkr
    rw [List.mem_filter] at hkr
    refine ⟨hkr.1, ?_⟩
    intro hin
    rcases List.mem_cons.mp hin with hw | hw
    · have hne : e.2 ≠ w := by simpa using hkr.2
      exact hne hw
    · exact hnin hw

theorem heldValid_regWrite {h : Held} {s : JState 64} (i : JInstr 64)
    (hv : HeldValid h s)
    (hmem : ∀ b o, (evalInstr s i).load b o = s.load b o)
    (hreg : ∀ ρ, ρ ∉ writtenRegs i → (evalInstr s i).get ρ = s.get ρ) :
    HeldValid (killWritten h i) (evalInstr s i) := by
  intro e he
  obtain ⟨hmemh, hnin⟩ := mem_foldl_killReg _ _ he
  have hval := hv e hmemh
  rw [hmem e.1.1 e.1.2, hreg e.2 hnin]
  exact hval

/-! ### The per-step soundness lemma

`forwardStep h i = (i', h')` with `HeldValid h s` implies:
* `evalInstr s i' = evalInstr s i` — the rewritten instruction has the *same*
  effect (the only rewrite, `loadMem → mov`, is value-preserving by the invariant);
* `HeldValid h' (evalInstr s i)` — the updated environment is valid in the new
  state (so the scan can continue).

The `loadMem`-forward case is the interesting one: `evalInstr s (.mov d (.reg r))`
sets `d := s.get r`, while `evalInstr s (.loadMem d base off)` sets `d := s.load
base off`; the invariant `heldValid_find` gives `s.load base off = s.get r`, so the
two states are equal. -/

/-- Memory is untouched by every non-`storeMem`, non-`loadSym` instruction. The
    register/flag writers (`setReg`, `writeB5W`, the explicit ADCX/ADOX records, the
    MULX double write) all leave `s.mem` literally unchanged. `loadSym` is excluded
    because its `evalInstr` re-aliases the memory bank at its base register (so a
    later indexed load reads the `.rodata` table), which changes `.load`. -/
theorem load_evalInstr_nonstore {s : JState 64} (i : JInstr 64)
    (h : ∀ b o v, i ≠ .storeMem b o v)
    (h2 : ∀ b idx sc v, i ≠ .storeMemIdx b idx sc v)
    (h3 : ∀ d sym, i ≠ .loadSym d sym) (b : String) (o : Int) :
    (evalInstr s i).load b o = s.load b o := by
  cases i with
  | storeMem b' o' v => exact absurd rfl (h b' o' v)
  | storeMemIdx b idx sc src => exact absurd rfl (h2 b idx sc src)
  | loadSym d sym => exact absurd rfl (h3 d sym)
  | mulx dh dl a c => simp only [evalInstr, JState.setReg, JState.load]
  | mulxMem dh dl a base off => simp only [evalInstr, JState.setReg, JState.load]
  | adcx d s' => simp only [evalInstr, JState.load]
  | adox d s' => simp only [evalInstr, JState.load]
  -- `test` and `cmp` write through `writeB5`, and the rotates through `writeB2W`;
  -- neither shape is covered by the other arms' `writeB5W`.
  | test a s' => simp only [evalInstr, JState.writeB5, JState.load]
  | cmp a s' => simp only [evalInstr, JState.writeB5, JState.load]
  | rol d amt => simp only [evalInstr, JState.writeB2W, JState.load]
  | ror d amt => simp only [evalInstr, JState.writeB2W, JState.load]
  | _ => simp only [evalInstr, JState.setReg, JState.writeB5W, JState.writeB4W,
      JState.writeB5W2, JState.writeB5N, JState.writeB2W, JState.writeCFW,
      JState.setRegMerge, JState.load]

/-- A non-`storeMem` instruction leaves every register it does not write unchanged. -/
theorem get_evalInstr_unwritten {s : JState 64} (i : JInstr 64)
    (hns : ∀ b o v, i ≠ .storeMem b o v)
    (ρ : String) (hρ : ρ ∉ writtenRegs i) : (evalInstr s i).get ρ = s.get ρ := by
  have hsingle : ∀ (d : String), ρ ∉ [d] → ρ ≠ d := by
    intro d hd; simpa using hd
  cases i with
  | mov d s'  => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | cmove d s'  => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | cmovne d s' => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | cmovb d s'  => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | loadMem d base off => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | loadMemIdx d base idx scale => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | loadSym d sym =>
      -- `loadSym` writes only register `d` (an inline `if r' = d` reg update); `ρ ≠ d`
      -- (from `hρ`) resolves the conditional to `s.regs ρ = s.get ρ`. Memory aliasing
      -- does not affect `get`.
      have := hsingle d hρ; simp [evalInstr, JState.get, this]
  | add d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | sub d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | adc d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | sbb d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | imul d s' => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | neg d     => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | setc d    => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | and_ d s' => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  -- `test` and `cmp` write only flags, so *every* register is unchanged (no
  -- hypothesis used).
  | test a b  => simp [evalInstr, JState.writeB5, JState.get]
  | cmp a b   => simp [evalInstr, JState.writeB5, JState.get]
  | not_ d    => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | andn d a c => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  -- the rotates write their destination through `writeB2W`.
  | rol d amt => have := hsingle d hρ; simp [evalInstr, JState.writeB2W, JState.get, this]
  | ror d amt => have := hsingle d hρ; simp [evalInstr, JState.writeB2W, JState.get, this]
  | rorx d src amt => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | shlx d src c   => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | shrx d src c   => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | sarx d src c   => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | movzx d sw src => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | movsx d sw src => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | lea d bs ix sc dsp => exact JState.get_setReg_other s _ _ _ (hsingle d hρ)
  | or_ d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | xor_ d s' => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | shl d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | shr d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | sar d s'  => have := hsingle d hρ; simp [evalInstr, JState.writeB5W, JState.get, this]
  | mulx dh dl a b =>
      have hne : ρ ≠ dh ∧ ρ ≠ dl := by
        simp only [writtenRegs, List.mem_cons, List.not_mem_nil, or_false] at hρ
        exact ⟨fun h => hρ (Or.inl h), fun h => hρ (Or.inr h)⟩
      simp [evalInstr, JState.setReg, JState.get, hne.1, hne.2]
  | mulxMem dh dl a base off =>
      have hne : ρ ≠ dh ∧ ρ ≠ dl := by
        simp only [writtenRegs, List.mem_cons, List.not_mem_nil, or_false] at hρ
        exact ⟨fun h => hρ (Or.inl h), fun h => hρ (Or.inr h)⟩
      simp [evalInstr, JState.setReg, JState.get, hne.1, hne.2]
  | adcx d s' =>
      have := hsingle d hρ; simp [evalInstr, JState.get, this]
  | adox d s' =>
      have := hsingle d hρ; simp [evalInstr, JState.get, this]
  | storeMem b o v => exact absurd rfl (hns b o v)
  | storeMemIdx base idx scale src =>
    simp [evalInstr]
  | inc _ | dec _ | clc | stc | xchg _ _ | imulri _ _ _ | mul _ _ _ | imulWide _ _ _
  | shld _ _ _ | shrd _ _ _ | rcl _ _ | rcr _ _ | cmovcc _ _ _ | setcc _ _
  | testN _ _ _ | bt _ _ | btr _ _ | bts _ _ =>
    simp_all [writtenRegs, evalInstr, JState.get, JState.setReg, JState.writeB4W,
      JState.writeB5W, JState.writeB5W2, JState.writeB5N, JState.writeB2W,
      JState.writeCFW, JState.setRegMerge, x86_XCHG]

/-- The non-`storeMem`/`storeMemIdx`/`loadSym` instructions, packaged: their
    `evalInstr` neither writes memory nor (for `ρ` outside `writtenRegs`) the register
    `ρ`. Lets `heldValid_regWrite` fire on such an instruction. `loadSym` is excluded
    because it re-aliases the memory bank (handled directly by `forwardStep_sound`). -/
theorem heldValid_killWritten_nonstore {h : Held} {s : JState 64} (i : JInstr 64)
    (hv : HeldValid h s) (hns : ∀ b o v, i ≠ .storeMem b o v)
    (hns2 : ∀ b idx sc v, i ≠ .storeMemIdx b idx sc v)
    (hns3 : ∀ d sym, i ≠ .loadSym d sym) :
    HeldValid (killWritten h i) (evalInstr s i) :=
  heldValid_regWrite i hv (load_evalInstr_nonstore i hns hns2 hns3)
    (fun ρ hρ => get_evalInstr_unwritten i hns ρ hρ)

/-- A new cell binding `(base, off) ↦ r` added after a register write to `r` (a
    forwarded load `mov r ← [base+off]`): the cell `(base, off)` is unchanged by a
    register write and the just-written register `r` holds `s.load base off`, so the
    binding is valid in the post-state. -/
theorem heldValid_loadForward {h : Held} {s : JState 64} (d base : String) (off : Int)
    (hv : HeldValid h s) :
    HeldValid (((killWritten h (.loadMem d base off)).set base off d))
      (evalInstr s (.loadMem d base off)) := by
  have hns : ∀ b o v, (JInstr.loadMem d base off) ≠ JInstr.storeMem (w := 64) b o v := by
    intro b o v h; cases h
  have hns2 : ∀ b idx sc v, (JInstr.loadMem d base off) ≠ JInstr.storeMemIdx (w := 64) b idx sc v := by
    intro b idx sc v h; cases h
  have hns3 : ∀ d' sym, (JInstr.loadMem d base off) ≠ JInstr.loadSym (w := 64) d' sym := by
    intro d' sym h; cases h
  have hkill := (heldValid_killWritten_nonstore (.loadMem d base off) hv hns hns2 hns3).killCell base off
  intro e he
  rw [Held.set, List.mem_append] at he
  rcases he with he | he
  · -- e is in the killed env: valid by heldValid_regWrite (loadMem is non-store)
    exact hkill e he
  · -- e is the new binding ((base,off), d)
    simp only [List.mem_singleton] at he
    subst he
    -- goal: (evalInstr s _).load base off = (evalInstr s _).get d
    have hmem : (evalInstr s (.loadMem d base off)).load base off = s.load base off :=
      load_evalInstr_nonstore (.loadMem d base off) hns hns2 hns3 base off
    have hreg : (evalInstr s (.loadMem d base off)).get d = s.load base off := by
      simp [evalInstr, x86_MOV, JState.setReg, JState.get]
    show (evalInstr s (.loadMem d base off)).load base off
       = (evalInstr s (.loadMem d base off)).get d
    rw [hmem, hreg]

/-- A new cell binding `(base, off) ↦ r` after a `storeMem base off (.reg r)`: the
    cell now literally holds `s.get r` and the register `r` is untouched by a memory
    store, so the binding is valid in the post-state. The killed-cell remainder is
    valid because a store changes only the written cell and no registers. -/
theorem heldValid_storeReg {h : Held} {s : JState 64} (base : String) (off : Int)
    (r : String) (hv : HeldValid h s) :
    HeldValid ((h.killCell base off).set base off r)
      (evalInstr s (.storeMem base off (.reg r))) := by
  have hstore : evalInstr s (.storeMem base off (.reg r)) = s.store base off (s.get r) := by
    simp [evalInstr, x86_MOV, JOperand.eval]
  intro e he
  rw [Held.set, List.mem_append] at he
  rcases he with he | he
  · -- killed-cell entry: its cell ≠ (base,off), so unchanged; regs unchanged
    rw [Held.killCell, List.mem_filter] at he
    have hcell : e.1 ≠ (base, off) := by simpa using he.2
    have hval := (hv.killCell base off) e he.1
    rw [hstore]
    have : (s.store base off (s.get r)).load e.1.1 e.1.2 = s.load e.1.1 e.1.2 := by
      apply JState.load_store_other
      intro hcon; exact hcell (by rw [Prod.ext_iff]; exact ⟨hcon.1, hcon.2⟩)
    rw [this]; simpa [JState.store, JState.get] using hval
  · simp only [List.mem_singleton] at he
    subst he
    rw [hstore]
    simp [JState.store, JState.get]

/-! ### Per-step soundness and the whole-block translation validation -/

/-- **One forwarding step is denotation-preserving + invariant-preserving.** Under
    `HeldValid h s`, the rewritten instruction `(forwardStep h i).1` has the *same*
    `evalInstr` effect as `i`, and the updated environment `(forwardStep h i).2` is
    valid in the resulting state. -/
theorem forwardStep_sound {h : Held} {s : JState 64} (hv : HeldValid h s) (i : JInstr 64) :
    evalInstr s (forwardStep h i).1 = evalInstr s i
      ∧ HeldValid (forwardStep h i).2 (evalInstr s i) := by
  cases i with
  | loadMem d base off =>
    -- the only rewriting case: the rewritten body and the new env both depend on
    -- `h.find base off`.  The new env is `heldValid_loadForward` regardless; the
    -- effect equality is `rfl` (find=none) or via the invariant (find=some r).
    cases hf : h.find base off with
    | none =>
      have hstep : forwardStep h (.loadMem d base off)
          = (.loadMem d base off, (killWritten h (.loadMem d base off)).set base off d) := by
        simp [forwardStep, hf]
      rw [hstep]
      exact ⟨rfl, heldValid_loadForward d base off hv⟩
    | some r =>
      have hval : s.load base off = s.get r := heldValid_find hv hf
      have heff : evalInstr s (.mov d (.reg r)) = evalInstr s (.loadMem d base off) := by
        show s.setReg d (x86_MOV ((JOperand.reg r).eval s)) = s.setReg d (x86_MOV (s.load base off))
        rw [hval]; rfl
      have hfst : (forwardStep h (.loadMem d base off)).1 = .mov d (.reg r) := by
        simp only [forwardStep, hf]; split <;> rfl
      have hsnd : (forwardStep h (.loadMem d base off)).2
          = (killWritten h (.loadMem d base off)).set base off d := by
        simp only [forwardStep, hf]; split <;> rfl
      rw [hfst, hsnd]
      exact ⟨heff, heldValid_loadForward d base off hv⟩
  | storeMem base off src =>
    cases src with
    | reg r =>
      have hstep : forwardStep h (.storeMem base off (.reg r))
          = (.storeMem base off (.reg r), (h.killCell base off).set base off r) := by
        simp [forwardStep]
      rw [hstep]
      exact ⟨rfl, heldValid_storeReg base off r hv⟩
    | imm v =>
      have hstep : forwardStep h (.storeMem base off (.imm v))
          = (.storeMem base off (.imm v), h.killCell base off) := by
        simp [forwardStep]
      rw [hstep]
      refine ⟨rfl, ?_⟩
      -- killCell of a store: surviving cells are other cells, unchanged by the store
      have hstore : evalInstr s (.storeMem base off (.imm v))
          = s.store base off (BitVec.ofNat 64 v) := by
        simp [evalInstr, x86_MOV, JOperand.eval]
      intro e he
      rw [Held.killCell, List.mem_filter] at he
      have hcell : e.1 ≠ (base, off) := by simpa using he.2
      have hval := hv e he.1
      rw [hstore]
      have : (s.store base off (BitVec.ofNat 64 v)).load e.1.1 e.1.2 = s.load e.1.1 e.1.2 := by
        apply JState.load_store_other
        intro hcon; exact hcell (by rw [Prod.ext_iff]; exact ⟨hcon.1, hcon.2⟩)
      rw [this]; simpa [JState.store, JState.get] using hval
  | mov d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | add d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | sub d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | adc d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | sbb d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | imul d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | neg d     => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | setc d    => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | and_ d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  -- `test` and `cmp` kill nothing (`writtenRegs = []`), so `killWritten h i = h`.
  | test a b  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | cmp a b   => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | not_ d    => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | andn d a c => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | rol d amt => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | ror d amt => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | rorx d src amt => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | shlx d src c => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | shrx d src c => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | sarx d src c => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | movzx d sw src => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | movsx d sw src => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  -- `lea` writes a register and touches no memory, so no cell binding is invalidated.
  | lea d bs ix sc dsp => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | or_ d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | xor_ d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | shl d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | shr d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | sar d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | cmove d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | cmovne d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | cmovb d s'  => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | mulx dh dl a b => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | mulxMem dh dl a base off =>
      exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | adcx d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | adox d s' => exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h) (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩
  | storeMemIdx base idx scale src =>
    have hstep : forwardStep h (.storeMemIdx base idx scale src)
        = (.storeMemIdx base idx scale src, []) := by
      simp [forwardStep]
    rw [hstep]
    refine ⟨rfl, ?_⟩
    intro e he
    simp at he
  | loadSym d sym =>
    -- `loadSym` conservatively forgets every binding (it re-aliases the memory bank
    -- at base `d`): `forwardStep` returns `[]`, so the effect is unchanged (`rfl`)
    -- and `HeldValid []` is vacuous — exactly the `storeMemIdx` shape.
    have hstep : forwardStep h (.loadSym d sym) = (.loadSym d sym, []) := by
      simp [forwardStep]
    rw [hstep]
    refine ⟨rfl, ?_⟩
    intro e he
    simp at he
  | loadMemIdx d base idx scale =>
    have hns : ∀ b o v, (JInstr.loadMemIdx d base idx scale) ≠ JInstr.storeMem (w := 64) b o v := by
      intro b o v h; cases h
    have hns2 : ∀ b idx' sc v, (JInstr.loadMemIdx d base idx scale) ≠ JInstr.storeMemIdx (w := 64) b idx' sc v := by
      intro b idx' sc v h; cases h
    have hns3 : ∀ d' sym, (JInstr.loadMemIdx d base idx scale) ≠ JInstr.loadSym (w := 64) d' sym := by
      intro d' sym h; cases h
    exact ⟨rfl, heldValid_killWritten_nonstore _ hv hns hns2 hns3⟩
  -- the remaining instructions write registers and flags only, and are not rewritten.
  | inc _ | dec _ | clc | stc | xchg _ _ | imulri _ _ _ | mul _ _ _ | imulWide _ _ _
  | shld _ _ _ | shrd _ _ _ | rcl _ _ | rcr _ _ | cmovcc _ _ _ | setcc _ _
  | testN _ _ _ | bt _ _ | btr _ _ | bts _ _ =>
    exact ⟨rfl, heldValid_killWritten_nonstore _ hv (by intro b o v h; cases h)
      (by intro b idx sc v h; cases h) (by intro d sym h; cases h)⟩

/-- **Whole-block translation validation.** Running the forwarded block from any
    state with a valid held environment lands in the *same* `runBlock` final state
    as the original block — the store-to-load forwarding pass is denotation-preserving
    against the validated `JasminModel`. -/
theorem forwardAux_runBlock {h : Held} {s : JState 64} (hv : HeldValid h s)
    (block : List (JInstr 64)) :
    runBlock s (forwardAux h block) = runBlock s block := by
  induction block generalizing h s with
  | nil => rfl
  | cons i is ih =>
    rw [forwardAux_cons, runBlock_cons, runBlock_cons]
    obtain ⟨heff, hvalid⟩ := forwardStep_sound hv i
    rw [heff]
    exact ih hvalid

/-- **The store-to-load forwarding pass is denotation-preserving** (started from the
    empty held environment, which is vacuously valid). For every state, the forwarded
    block's `runBlock` equals the original's — the in-Lean translation-validation
    certificate for the forwarding dimension, the companion to
    `RandomizedRegAlloc.regalloc_runBlock_sound`. -/
theorem storeToLoadForward_runBlock (block : List (JInstr 64)) (s : JState 64) :
    runBlock s (storeToLoadForward block) = runBlock s block :=
  forwardAux_runBlock (h := []) (by intro e he; simp at he) block

/-- **Dialect-level form.** Through `X86Dialect.lowerBlock_denote_closed`, the lowered
    `Com` of the forwarded block denotes exactly the lowered `Com` of the original on
    every state — the forwarding pass preserves denotation against the validated x86
    model. -/
theorem storeToLoadForward_lowering (block : List (JInstr 64)) (s : JState 64) :
    (lowerBlock (Γ := []) (storeToLoadForward block)).denote (.cons s .nil)
      = (lowerBlock (Γ := []) block).denote (.cons s .nil) := by
  rw [lowerBlock_denote_closed (storeToLoadForward block) s, lowerBlock_denote_closed block s]
  exact storeToLoadForward_runBlock block s

end CatCrypt.Crypto.Optimizer.StoreToLoadForward
