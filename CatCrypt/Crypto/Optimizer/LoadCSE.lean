/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# `loadCSE`: cross-register redundant-load elimination on the post-RA `Lprog` body

`LprogStoreToLoad.elimReloads` drops a reload `MOV R ← K` when the **same**
register `R` already holds slot `K` (no intervening write) — the same-register
case of redundant-load elimination, a pure drop.

This module is the **cross-register** companion: the load-CSE move under
register pressure.  When slot `K` was loaded into register `R₁` and is loaded
*again* later into a **different** register `R₂` — with no write to `K` or `R₁`
in between — the second load

```
  mov R₂, K        ; movq <off>(%rsp), %r14   — a memory LOAD (AGU + LSU + Load port)
```

denotes the same value as the register-to-register move

```
  mov R₂, R₁       ; movq %r15, %r14          — a register MOVE (ALU only, no LSU)
```

because `R₁` still holds slot `K`'s value.  Rewriting the second load to the
register move keeps the value **register-resident** for that hop and removes the
load from the memory subsystem — the lever the Keccak measurement identified as
the binding resource (`Zn4LSU` on znver4 is saturated by the m[] state-lane
reload traffic).

It is the `Lprog`-IR sibling of `StoreToLoadForward` and `elimReloads`, and
composes with `elimReloads` (run `elimReloads` first to drop the same-register
reloads, then `loadCSE` to redirect the cross-register ones onto the surviving
register).

## Operand width

The recognizer `asWideReload` accepts exactly the two 64-bit move mnemonics
`MOV:64` and `MOVQ`, and the rewrite re-emits the mnemonic of the instruction it
replaces.  `LprogAsmPrinter.mnemWidth` reads an operand width off the mnemonic
(`MOV:64` / `MOVQ` ↦ 64 ↦ `movq`; a bare `MOV` ↦ 32 ↦ `movl`, which
zero-extends), so an emitted mnemonic equal to the input's is an emitted width
equal to the input's.  A bare `MOV` is outside the recognizer: it neither fires
the rewrite nor enters the environment, so a 64-bit reload is never sourced from
a register that a 32-bit move wrote.  `loadCSE_mnems` states the mnemonic
equality position by position and `loadCSE_widths` transports it along any
mnemonic-to-width assignment.

## Results

1. `loadCSE_length` — the output has the same length as the input: the pass never
   adds, drops, or reorders an instruction; it only rewrites the source operand
   of a redundant load (memory slot → register holding it).
2. `loadCSE_mnems` — the output's mnemonic sequence equals the input's, so the
   pass emits no mnemonic outside the input's and no operand width outside the
   input's (`loadCSE_widths`).
3. `loadCSEAux_pointwise` — every instruction the pass *changes* is a 64-bit
   reload `MOV d ← s` rewritten to `MOV d ← r` under the same mnemonic, where
   the environment certifies that `r` holds slot `s`; `loadCSEAux_pointwise_reg`
   adds that `r` is a register name on a body with no move between two memory names.
4. `loadCSE_lsemStraight` — under `JasminLsem.lsemStraight` the rewritten body
   reaches exactly the same state as the original, from every start state.
   `EnvSound` — every recorded binding `k ↦ r` has `lvm r = lvm k` — is the loop
   invariant that carries the induction; it is established at the empty
   environment and preserved by every kill and by the recorded reload.

`JasminLsem.lsemStraight` is width-uniform (`lvm : String → BitVec w`), so it
constrains the value the rewrite computes but not the width at which the printer
renders it; the width statement is item 2.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.LoadCSE

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
  (writtenNames mem_of_find mem_set lsemStep_lvm_of_not_written)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-! ## 1. The held environment: slot ↦ register currently holding it

`elimReloads` keys its environment by *register* (`reg ↦ slot`, to detect a
register reloading a slot it already holds).  `loadCSE` keys by *slot*
(`slot ↦ register`, to find a register that already holds a slot a fresh load
wants), so the two passes are duals on the same carrier.  `LoadEnv` is a fresh
association list keeping the keying explicit. -/

/-- The load-CSE environment: source slot name ↦ a register currently known to
    hold that slot's value.  A reload `MOV R ← K` records `K ↦ R`. -/
abbrev LoadEnv := List (String × String)

/-- Find a register currently holding slot `k` (the candidate to reuse). -/
def LoadEnv.find (h : LoadEnv) (k : String) : Option String := h.lookup k

/-- Record that slot `k` is held in register `r` (after `MOV r ← k`): drop any
    stale binding for `k`, then add `k ↦ r`. -/
def LoadEnv.set (h : LoadEnv) (k r : String) : LoadEnv :=
  (h.filter (fun e => e.1 ≠ k)) ++ [(k, r)]

/-- Drop every binding whose **slot** is `k` (called when slot/cell `k` is written:
    any register recorded as holding `k`'s value is stale). -/
def LoadEnv.killSlot (h : LoadEnv) (k : String) : LoadEnv :=
  h.filter (fun e => e.1 ≠ k)

/-- Drop every binding whose **held register** is `r` (called when register `r` is
    written: it holds a different value from the slot it was recorded against). -/
def LoadEnv.killReg (h : LoadEnv) (r : String) : LoadEnv :=
  h.filter (fun e => e.2 ≠ r)

/-! ### Membership under the environment operations

`LoadEnv` is an instance of the register-keyed association list
`LprogStoreToLoad.HeldOf`, keyed here by slot, so `LoadEnv.find`/`LoadEnv.set` are
`HeldOf.find`/`HeldOf.set` and `LoadEnv.killSlot` is `HeldOf.killReg`.  The
`find`/`set` membership lemmas are taken verbatim from there; the kill lemmas and
their folds keep the name matching this module's keying. -/

theorem mem_killReg {h : LoadEnv} {p : String × String} {r : String}
    (hp : p ∈ h.killReg r) : p ∈ h ∧ p.2 ≠ r := by
  rw [LoadEnv.killReg, List.mem_filter] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

theorem mem_killSlot {h : LoadEnv} {p : String × String} {k : String}
    (hp : p ∈ h.killSlot k) : p ∈ h ∧ p.1 ≠ k :=
  CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_killReg hp

theorem mem_foldl_killReg (ws : List String) (h : LoadEnv) (p : String × String)
    (hp : p ∈ ws.foldl LoadEnv.killReg h) : p ∈ h ∧ p.2 ∉ ws := by
  induction ws generalizing h with
  | nil => exact ⟨hp, by simp⟩
  | cons a rest ih =>
    rw [List.foldl_cons] at hp
    obtain ⟨hmem, hnot⟩ := ih (h.killReg a) hp
    obtain ⟨hh, hne⟩ := mem_killReg hmem
    exact ⟨hh, by simp only [List.mem_cons, not_or]; exact ⟨hne, hnot⟩⟩

theorem mem_foldl_killSlot (ws : List String) (h : LoadEnv) (p : String × String)
    (hp : p ∈ ws.foldl LoadEnv.killSlot h) : p ∈ h ∧ p.1 ∉ ws :=
  CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_foldl_killReg ws h p hp

/-! ## 2. The 64-bit reload recognizer

The rewrite replaces a load's source operand, so the emitted instruction must
carry the operand width of the load it replaces.  The recognizer is keyed on the
64-bit move mnemonics and the rewrite re-emits the recognized mnemonic; a move
at any other width is declined and passes through the write-kill arm. -/

/-- The two 64-bit move mnemonics of the owned exporter.  `LprogAsmPrinter.mnemWidth`
    maps both to 64 and the printer renders them `movq`. -/
def isMov64Mnem (mn : String) : Bool := mn == "MOV:64" || mn == "MOVQ"

/-- A 64-bit reload `MOV d ← s`: a single-destination, single-source `Lopn` with a
    bare register destination `d`, a bare named source `s` (a spill slot `k.N`, an
    ABI save `qsave.X`, a memory name `mem.<base>.<off>`, or a register), and a
    64-bit move mnemonic.  Returns `(d, s, mn)`.  Two-address binops, immediate
    moves, and moves at any other width are rejected. -/
def asWideReload : LinstrR → Option (String × String × String)
  | .Lopn [.reg d] mn [.reg s] => if isMov64Mnem mn then some (d, s, mn) else none
  | _ => none

/-- The instruction shape and mnemonic class of a recognized reload. -/
theorem asWideReload_eq {i : LinstrR} {d s mn : String}
    (h : asWideReload i = some (d, s, mn)) :
    i = .Lopn [.reg d] mn [.reg s] ∧ isMov64Mnem mn = true := by
  unfold asWideReload at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hc⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognized reload's mnemonic copies its single source word under
    `JasminLsem.applyOpn`. -/
theorem applyOpn_of_isMov64Mnem {w : Nat} {mn : String} (hm : isMov64Mnem mn = true)
    (a : BitVec w) : applyOpn (w := w) (stripWidthTag mn) [a] = some a := by
  simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · rw [show stripWidthTag "MOV:64" = "MOV" from by decide +kernel]; rfl
  · rw [stripWidthTag_MOVQ]; rfl

/-- A memory-class operand name: a spill slot `k.N`, an ABI save slot `qsave.X`,
    or a frame reference `mem.<base>.<off>`, the names the printer renders as a
    memory operand.  The same class as `X86Backend.LcmdReloadElim.isSlotName`. -/
def isMemName (n : String) : Bool :=
  "k.".isPrefixOf n || "qsave.".isPrefixOf n || "mem.".isPrefixOf n

/-- A 64-bit move whose destination and source are both memory names. -/
def isMemToMemMov (i : LinstrR) : Bool :=
  match asWideReload i with
  | some (d, s, _) => isMemName d && isMemName s
  | none => false

/-! ## 3. The forwarding scan

`stepLoad held i` returns the (possibly rewritten) instruction together with the
updated environment.  The only rewrite: a 64-bit reload `MOV R₂ ← K` whose slot
`K` is held in a register `R₁ ≠ R₂` becomes `MOV R₂ ← R₁` under the same
mnemonic, provided `R₂` and `R₁` are not both memory names (a memory-to-memory
move has no x86 encoding) and `R₁` is a register name whenever `K` is (the redirect
of a register move onto a memory holder would replace a move by a load).

Environment update:
* A recognized reload `MOV R ← K` (kept or rewritten): writing register `R` kills
  `R`'s bindings (`killReg R`) and any binding *of* `R` as a key (`killSlot R` —
  if `R` itself names a cell, that cell's holders are stale); then record
  `K ↦ R`.  A load reads `K` and does not write it, so other registers holding
  `K` survive.
* Any other instruction, including a move at a width outside the recognizer,
  writes its destination names: kill every written register's binding and every
  slot-binding whose key is a written name. -/

/-- One step: `(rewrittenInstr, newEnv)`.  The instruction is returned unchanged
    unless it is a cross-register redundant 64-bit load whose destination and
    holding register are not both memory names and whose holding register is a
    register name when its source is, in which case its source operand is
    redirected to the holding register under the same mnemonic. -/
def stepLoad (h : LoadEnv) (i : Linstr) : Linstr × LoadEnv :=
  match asWideReload i.li_i with
  | some (d, s, mn) =>
      match h.find s with
      | some r =>
          if r = d then
            -- the same-register case `elimReloads` drops; keep verbatim, refresh.
            (i, ((h.killReg d).killSlot d).set s d)
          else if isMemName d = true ∧ isMemName r = true then
            -- the redirect would be memory-to-memory; keep verbatim, refresh.
            (i, ((h.killReg d).killSlot d).set s d)
          else if isMemName s = false ∧ isMemName r = true then
            -- the redirect would turn a register move into a load; keep verbatim, refresh.
            (i, ((h.killReg d).killSlot d).set s d)
          else
            -- cross-register hit: redirect the source onto the holding register.
            ({ i with li_i := .Lopn [.reg d] mn [.reg r] },
              ((h.killReg d).killSlot d).set s d)
      | none =>
          -- first load of s into d: keep, record s ↦ d.
          (i, ((h.killReg d).killSlot d).set s d)
  | none =>
      -- kill every written register and every slot whose cell is written.
      let ws := writtenNames i.li_i
      let h1 := ws.foldl LoadEnv.killReg h
      let h2 := ws.foldl LoadEnv.killSlot h1
      (i, h2)

/-- Run the forward scan over a body, threading the load environment and
    redirecting every cross-register redundant load onto its holding register. -/
def loadCSEAux : LoadEnv → List Linstr → List Linstr
  | _, [] => []
  | h, i :: is =>
      let (i', h') := stepLoad h i
      i' :: loadCSEAux h' is

/-- Tail-recursive runtime image of `loadCSEAux` (accumulate in reverse, then
    reverse once), substituted for it by `@[implemented_by]`.  The structural
    `loadCSEAux` exhausts the interpreter stack on the ~15 k-instruction Keccak
    body; the spec stays the cons-recursion the proofs are about. -/
def loadCSEAuxTR (acc : List Linstr) : LoadEnv → List Linstr → List Linstr
  | _, [] => acc.reverse
  | h, i :: is =>
      let (i', h') := stepLoad h i
      loadCSEAuxTR (i' :: acc) h' is

@[implemented_by loadCSEAuxTR]
def loadCSEAuxImpl (acc : List Linstr) (h : LoadEnv) (is : List Linstr) : List Linstr :=
  acc.reverse ++ loadCSEAux h is

/-- The tail-recursive runtime image computes its spec, so the interpreted and
    native runs agree with the structural `loadCSEAux` the soundness theorems are
    about. -/
theorem loadCSEAuxTR_eq (acc : List Linstr) (h : LoadEnv) (is : List Linstr) :
    loadCSEAuxTR acc h is = acc.reverse ++ loadCSEAux h is := by
  induction is generalizing acc h with
  | nil => simp [loadCSEAuxTR, loadCSEAux]
  | cons i is ih =>
    show loadCSEAuxTR ((stepLoad h i).1 :: acc) (stepLoad h i).2 is
      = acc.reverse ++ ((stepLoad h i).1 :: loadCSEAux (stepLoad h i).2 is)
    rw [ih]
    simp

/-- **The cross-register load-CSE pass.**  Start from the empty environment. -/
def loadCSE (body : List Linstr) : List Linstr :=
  loadCSEAuxImpl [] [] body

/-- The pass equals the structural scan: `loadCSE body = loadCSEAux [] body`. -/
theorem loadCSE_eq (body : List Linstr) : loadCSE body = loadCSEAux [] body := by
  simp [loadCSE, loadCSEAuxImpl]

@[simp] theorem loadCSEAux_nil (h : LoadEnv) : loadCSEAux h [] = [] := rfl

theorem loadCSEAux_cons (h : LoadEnv) (i : Linstr) (is : List Linstr) :
    loadCSEAux h (i :: is) =
      (stepLoad h i).1 :: loadCSEAux (stepLoad h i).2 is := by
  simp only [loadCSEAux]

/-! ## 4. Structural soundness — same length, characterised rewrites -/

/-- The scan preserves length: every instruction maps to exactly one. -/
theorem loadCSEAux_length (h : LoadEnv) (body : List Linstr) :
    (loadCSEAux h body).length = body.length := by
  induction body generalizing h with
  | nil => rfl
  | cons i is ih => rw [loadCSEAux_cons]; simp [ih]

/-- **Length preservation.**  `loadCSE` neither adds nor drops an instruction; it
    only rewrites source operands. -/
theorem loadCSE_length (body : List Linstr) :
    (loadCSE body).length = body.length := by
  rw [loadCSE_eq]; exact loadCSEAux_length [] body

/-- A `stepLoad` either returns the instruction **verbatim**, or rewrites a
    recognized 64-bit reload `MOV d ← s` (with `s` held in a register `r ≠ d`, `d`
    and `r` not both memory names, and `r` a register name when `s` is) to the
    move `MOV d ← r` under the reload's own mnemonic. -/
theorem stepLoad_cases (h : LoadEnv) (i : Linstr) :
    (stepLoad h i).1 = i ∨
      ∃ d s r mn, asWideReload i.li_i = some (d, s, mn) ∧ h.find s = some r ∧
        (r ≠ d ∧ ¬ (isMemName d = true ∧ isMemName r = true) ∧
          ¬ (isMemName s = false ∧ isMemName r = true)) ∧
        (stepLoad h i).1 = { i with li_i := .Lopn [.reg d] mn [.reg r] } := by
  cases hr : asWideReload i.li_i with
  | none => left; simp only [stepLoad, hr]
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    cases hf : h.find s with
    | none => left; simp only [stepLoad, hr, hf]
    | some r =>
      by_cases hrd : r = d
      · subst hrd; left; simp only [stepLoad, hr, hf, ite_eq_left]
      · by_cases hmm : isMemName d = true ∧ isMemName r = true
        · left; simp only [stepLoad, hr, hf, hrd, ite_false, ite_eq_left hmm]
        · by_cases hsr : isMemName s = false ∧ isMemName r = true
          · left; simp only [stepLoad, hr, hf, hrd, ite_false, ite_eq_right hmm, ite_eq_left hsr]
          · right
            refine ⟨d, s, r, mn, rfl, hf, ⟨hrd, hmm, hsr⟩, ?_⟩
            simp only [stepLoad, hr, hf, hrd, ite_false, ite_eq_right hmm, ite_eq_right hsr]

/-- **Rewrite characterisation.**  Whenever `loadCSE` emits an instruction that
    differs from the input, that input was a 64-bit reload `MOV d ← s` whose slot
    `s` the environment recorded as held in a *different* register `r`, `d` and
    `r` are not both memory names, `r` is a register name when `s` is, and the
    emitted instruction is the move `MOV d ← r` under the same mnemonic. -/
theorem stepLoad_rewrite_is_held_load (h : LoadEnv) (i : Linstr)
    (hne : (stepLoad h i).1 ≠ i) :
    ∃ d s r mn, asWideReload i.li_i = some (d, s, mn) ∧ h.find s = some r ∧
      (r ≠ d ∧ ¬ (isMemName d = true ∧ isMemName r = true) ∧
        ¬ (isMemName s = false ∧ isMemName r = true)) ∧
      (stepLoad h i).1 = { i with li_i := .Lopn [.reg d] mn [.reg r] } := by
  rcases stepLoad_cases h i with hid | hrw
  · exact absurd hid hne
  · exact hrw

/-- An instruction outside the recognizer, or a recognized reload whose every
    cross-register hit is between two memory names or from a register name onto a
    memory name, is emitted verbatim. -/
theorem stepLoad_unchanged_of_no_cross (h : LoadEnv) (i : Linstr)
    (hno : ∀ d s r mn, asWideReload i.li_i = some (d, s, mn) → h.find s = some r →
      r ≠ d → (isMemName d = true ∧ isMemName r = true) ∨
        (isMemName s = false ∧ isMemName r = true)) :
    (stepLoad h i).1 = i := by
  rcases stepLoad_cases h i with hid | ⟨d, s, r, mn, ha, hf, ⟨hrd, hmm, hsr⟩, _⟩
  · exact hid
  · rcases hno d s r mn ha hf hrd with h1 | h1
    · exact absurd h1 hmm
    · exact absurd h1 hsr

/-! ## 5. Width: the emitted mnemonic is the input's

The printer derives the AT&T size suffix from the mnemonic
(`LprogAsmPrinter.mnemWidth` / `sizeSuffix`), so equality of mnemonics is
equality of rendered operand widths.  `loadCSE_mnems` gives that equality
position by position and `loadCSE_widths` transports it along an arbitrary
mnemonic-to-width assignment, the printer's included. -/

/-- The mnemonic of an `Lopn`; `none` for a non-`Lopn` instruction. -/
def mnemOf : LinstrR → Option String
  | .Lopn _ mn _ => some mn
  | _ => none

/-- A rewritten instruction carries the mnemonic of the instruction it replaces. -/
theorem stepLoad_mnem (h : LoadEnv) (i : Linstr) :
    mnemOf (stepLoad h i).1.li_i = mnemOf i.li_i := by
  rcases stepLoad_cases h i with hid | ⟨d, s, r, mn, ha, _, _, heq⟩
  · rw [hid]
  · obtain ⟨hi, _⟩ := asWideReload_eq ha
    rw [heq, hi]
    rfl

/-- The scan's output carries the input's mnemonic at every position. -/
theorem loadCSEAux_mnems (h : LoadEnv) (body : List Linstr) :
    (loadCSEAux h body).map (fun i => mnemOf i.li_i)
      = body.map (fun i => mnemOf i.li_i) := by
  induction body generalizing h with
  | nil => rfl
  | cons i is ih =>
    rw [loadCSEAux_cons]
    simp only [List.map_cons, stepLoad_mnem, ih]

/-- **Mnemonic preservation.**  `loadCSE` emits, at every position, the mnemonic
    the input carried there; in particular it emits no mnemonic outside the
    input's. -/
theorem loadCSE_mnems (body : List Linstr) :
    (loadCSE body).map (fun i => mnemOf i.li_i)
      = body.map (fun i => mnemOf i.li_i) := by
  rw [loadCSE_eq]; exact loadCSEAux_mnems [] body

/-- Position-wise form of `loadCSE_mnems`. -/
theorem loadCSE_mnem_getElem? (body : List Linstr) (n : Nat) :
    ((loadCSE body)[n]?).map (fun i => mnemOf i.li_i)
      = (body[n]?).map (fun i => mnemOf i.li_i) := by
  rw [← List.getElem?_map, ← List.getElem?_map, loadCSE_mnems]

/-- Every mnemonic in the output occurs in the input. -/
theorem loadCSE_mnem_mem (body : List Linstr) (i : Linstr) (hi : i ∈ loadCSE body) :
    ∃ j ∈ body, mnemOf j.li_i = mnemOf i.li_i := by
  have h : mnemOf i.li_i ∈ body.map (fun j => mnemOf j.li_i) := by
    rw [← loadCSE_mnems]
    exact List.mem_map_of_mem hi
  obtain ⟨j, hj, hje⟩ := List.mem_map.1 h
  exact ⟨j, hj, hje⟩

/-- **Width preservation.**  Any assignment of an operand width to a mnemonic —
    `LprogAsmPrinter.mnemWidth` among them — takes the same value on the output
    as on the input, at every position. -/
theorem loadCSE_widths (widthOf : String → Nat) (body : List Linstr) :
    (loadCSE body).map (fun i => (mnemOf i.li_i).map widthOf)
      = body.map (fun i => (mnemOf i.li_i).map widthOf) := by
  have h := loadCSE_mnems body
  calc (loadCSE body).map (fun i => (mnemOf i.li_i).map widthOf)
      = ((loadCSE body).map (fun i => mnemOf i.li_i)).map (Option.map widthOf) := by
        simp [List.map_map, Function.comp_def]
    _ = (body.map (fun i => mnemOf i.li_i)).map (Option.map widthOf) := by rw [h]
    _ = body.map (fun i => (mnemOf i.li_i).map widthOf) := by
        simp [List.map_map, Function.comp_def]

/-- The rewrite of a recognized reload is itself a recognized reload with the same
    mnemonic, so the pass maps the 64-bit reload class into itself. -/
theorem rewritten_asWideReload (d r mn : String) (ii : Nat)
    (hm : isMov64Mnem mn = true) :
    asWideReload (Linstr.li_i { li_ii := ii, li_i := .Lopn [.reg d] mn [.reg r] })
      = some (d, r, mn) := by
  show (if isMov64Mnem mn then some (d, r, mn) else none) = some (d, r, mn)
  rw [ite_eq_left hm]

/-! ## 6. Whole-body rewrite-set characterisation -/

/-- **Per-position characterisation.**  For every position in the body, the
    emitted instruction is either the original or a held-load register move.  In
    the rewrite case the original was a 64-bit reload `asWideReload = some
    (d, s, mn)`, the environment `h'` reaching that position recorded slot `s` as
    held in `r ≠ d`, `d` and `r` are not both memory names, `r` is a register
    name when `s` is, and the emitted instruction is `MOV d ← r` under the same
    mnemonic `mn`. -/
theorem loadCSEAux_pointwise (h : LoadEnv) (body : List Linstr) (n : Nat) :
    (loadCSEAux h body)[n]? = body[n]? ∨
      ∃ (i : Linstr) (d s r mn : String) (h' : LoadEnv),
        body[n]? = some i ∧ asWideReload i.li_i = some (d, s, mn) ∧
        h'.find s = some r ∧ (r ≠ d ∧ ¬ (isMemName d = true ∧ isMemName r = true) ∧
          ¬ (isMemName s = false ∧ isMemName r = true)) ∧
        (loadCSEAux h body)[n]? =
          some { li_ii := i.li_ii, li_i := .Lopn [.reg d] mn [.reg r] } := by
  induction body generalizing h n with
  | nil => left; simp
  | cons i is ih =>
    rw [loadCSEAux_cons]
    cases n with
    | zero =>
      rcases stepLoad_cases h i with hid | ⟨d, s, r, mn, ha, hf, hrd, heq⟩
      · left; simp [hid]
      · right
        exact ⟨i, d, s, r, mn, h, rfl, ha, hf, hrd, by simp [heq]⟩
    | succ m =>
      rcases ih (stepLoad h i).2 m with hverb | ⟨i', d, s, r, mn, h', hb, ha, hf, hrd, he⟩
      · left; simpa using hverb
      · right
        exact ⟨i', d, s, r, mn, h', by simpa using hb, ha, hf, hrd, by simpa using he⟩

/-- A `stepLoad` emits a memory-to-memory move only where its input was one. -/
theorem stepLoad_isMemToMemMov (h : LoadEnv) (i : Linstr)
    (hi : isMemToMemMov i.li_i = false) : isMemToMemMov (stepLoad h i).1.li_i = false := by
  rcases stepLoad_cases h i with hid | ⟨d, s, r, mn, ha, _, ⟨_, hmm, _⟩, heq⟩
  · rw [hid]; exact hi
  · obtain ⟨_, hm⟩ := asWideReload_eq ha
    rw [heq]
    have hw := rewritten_asWideReload d r mn i.li_ii hm
    simp only [isMemToMemMov, hw, Bool.and_eq_false_iff]
    cases hd : isMemName d <;> cases hr : isMemName r <;> simp_all

/-- **No memory-to-memory moves introduced.**  If no instruction of the body is a
    64-bit move between two memory names, no instruction of `loadCSE body` is. -/
theorem loadCSE_noMemToMemMov (body : List Linstr)
    (hb : ∀ i ∈ body, isMemToMemMov i.li_i = false) :
    ∀ i ∈ loadCSE body, isMemToMemMov i.li_i = false := by
  rw [loadCSE_eq]
  suffices ∀ (h : LoadEnv) (b : List Linstr), (∀ i ∈ b, isMemToMemMov i.li_i = false) →
      ∀ i ∈ loadCSEAux h b, isMemToMemMov i.li_i = false from this [] body hb
  intro h b
  induction b generalizing h with
  | nil => intro _ i hi; simp at hi
  | cons j js ih =>
    intro hjs i hi
    rw [loadCSEAux_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact stepLoad_isMemToMemMov h j (hjs j List.mem_cons_self)
    · exact ih _ (fun k hk => hjs k (List.mem_cons_of_mem j hk)) i hi

/-! ## 7. Semantics: the rewritten body reaches the same state

`JasminLsem.lsemStep` renders a memory cell as a `.reg`-named `lvm` entry, so a
slot and a register live in the same store and the environment's claim "register
`r` holds slot `k`" is the state predicate `lvm r = lvm k`.  `EnvSound` is that
predicate over every recorded binding; it holds at the empty environment, every
kill only shrinks the binding set, and the reload arm records exactly the binding
its own step establishes. -/

/-- The load environment agrees with a machine state: every recorded binding
    `k ↦ r` has register `r` holding the same word as cell `k`. -/
def EnvSound {w : Nat} (h : LoadEnv) (s : Lstate w) : Prop :=
  ∀ k r : String, (k, r) ∈ h → s.lvm r = s.lvm k

theorem EnvSound.mono {w : Nat} {h h' : LoadEnv} {s : Lstate w}
    (hs : EnvSound h s) (hsub : ∀ p ∈ h', p ∈ h) : EnvSound h' s :=
  fun k r hk => hs k r (hsub (k, r) hk)

theorem envSound_nil {w : Nat} (s : Lstate w) : EnvSound ([] : LoadEnv) s := by
  intro k r hk; simp at hk

/-- The environment after a recognized reload, in every branch of the reload
    arm. -/
theorem stepLoad_env_of_wideReload (h : LoadEnv) (i : Linstr) {d sn mn : String}
    (hr : asWideReload i.li_i = some (d, sn, mn)) :
    (stepLoad h i).2 = ((h.killReg d).killSlot d).set sn d := by
  simp only [stepLoad, hr]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- The environment after an instruction outside the recognizer. -/
theorem stepLoad_env_of_not_wideReload (h : LoadEnv) (i : Linstr)
    (hr : asWideReload i.li_i = none) :
    (stepLoad h i).2 =
      (writtenNames i.li_i).foldl LoadEnv.killSlot
        ((writtenNames i.li_i).foldl LoadEnv.killReg h) := by
  simp only [stepLoad, hr]

/-- **The rewritten instruction steps to the same state.**  Under `EnvSound` the
    holding register carries the slot's word, so redirecting the source operand
    onto it leaves `lsemStep` unchanged. -/
theorem stepLoad_lsemStep {w : Nat} (h : LoadEnv) (i : Linstr) (s : Lstate w)
    (hs : EnvSound h s) :
    lsemStep (w := w) (stepLoad h i).1.li_i s = lsemStep (w := w) i.li_i s := by
  rcases stepLoad_cases h i with hid | ⟨d, sn, r, mn, ha, hf, hrd, heq⟩
  · rw [hid]
  · obtain ⟨hi, _⟩ := asWideReload_eq ha
    have hval : s.lvm r = s.lvm sn := hs sn r (mem_of_find hf)
    rw [heq, hi]
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hval]

/-- **The environment invariant is preserved.**  Every kill only drops bindings
    whose register or cell the instruction writes, and the reload arm records the
    binding its own step establishes. -/
theorem stepLoad_envSound {w : Nat} (h : LoadEnv) (i : Linstr) (s s' : Lstate w)
    (hs : EnvSound h s) (hstep : lsemStep (w := w) i.li_i s = some s') :
    EnvSound (stepLoad h i).2 s' := by
  cases hr : asWideReload i.li_i with
  | some dsm =>
    obtain ⟨d, sn, mn⟩ := dsm
    obtain ⟨hi, hm⟩ := asWideReload_eq hr
    have hs' : s' = (s.setReg d (s.lvm sn)).nextPc := by
      rw [hi] at hstep
      simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
        applyOpn_of_isMov64Mnem hm] at hstep
      exact (Option.some.inj hstep).symm
    intro k r hk
    rw [stepLoad_env_of_wideReload h i hr] at hk
    rcases mem_set hk with ⟨hmem, _⟩ | hpair
    · obtain ⟨hmem1, hkd⟩ := mem_killSlot hmem
      obtain ⟨hmem0, hrd⟩ := mem_killReg hmem1
      have hkr : s.lvm r = s.lvm k := hs k r hmem0
      subst hs'
      simp [Lstate.setReg, Lstate.nextPc, hrd, hkd, hkr]
    · have hk1 : k = sn := congrArg Prod.fst hpair
      have hr1 : r = d := congrArg Prod.snd hpair
      subst hk1; subst hr1
      subst hs'
      simp [Lstate.setReg, Lstate.nextPc]
  | none =>
    intro k r hk
    rw [stepLoad_env_of_not_wideReload h i hr] at hk
    obtain ⟨hk1, hkw⟩ := mem_foldl_killSlot _ _ _ hk
    obtain ⟨hk0, hrw⟩ := mem_foldl_killReg _ _ _ hk1
    rw [lsemStep_lvm_of_not_written hstep hrw, lsemStep_lvm_of_not_written hstep hkw]
    exact hs k r hk0

/-- The scan preserves straight-line execution from every state its environment
    agrees with. -/
theorem loadCSEAux_lsemStraight {w : Nat} (h : LoadEnv) (body : List Linstr)
    (s : Lstate w) (hs : EnvSound h s) :
    lsemStraight ((loadCSEAux h body).map Linstr.li_i) s
      = lsemStraight (body.map Linstr.li_i) s := by
  induction body generalizing h s with
  | nil => rfl
  | cons i is ih =>
    rw [loadCSEAux_cons]
    simp only [List.map_cons, lsemStraight_cons, stepLoad_lsemStep h i s hs]
    cases hst : lsemStep (w := w) i.li_i s with
    | none => rfl
    | some s' => exact ih (stepLoad h i).2 s' (stepLoad_envSound h i s s' hs hst)

/-- **Semantic soundness.**  On every body and every start state, the rewritten
    body's `lsemStraight` result is the original's — the same register map, the
    same memory, the same program counter.  The side condition is discharged, not
    assumed: the pass starts from the empty environment, which agrees with every
    state. -/
theorem loadCSE_lsemStraight {w : Nat} (body : List Linstr) (s : Lstate w) :
    lsemStraight ((loadCSE body).map Linstr.li_i) s
      = lsemStraight (body.map Linstr.li_i) s := by
  rw [loadCSE_eq]
  exact loadCSEAux_lsemStraight [] body s (envSound_nil s)

/-! ### The holder of a redirect is a register name

A binding `k ↦ r` is recorded by a 64-bit move `MOV r ← k` of the input. When no input move is
between two memory names, a binding with a memory-name holder has a register-name key, and
`stepLoad` declines the redirect from a register name onto a memory name, so every redirect
reads a register name. -/

/-- Every binding of the environment whose holder is a memory name has a register-name
    key. -/
def MemHolderRegKey (h : LoadEnv) : Prop :=
  ∀ k r : String, (k, r) ∈ h → isMemName r = true → isMemName k = false

theorem memHolderRegKey_nil : MemHolderRegKey ([] : LoadEnv) := by
  intro k r hk; simp at hk

/-- A step at an instruction that is no move between two memory names keeps
    `MemHolderRegKey`. -/
theorem stepLoad_memHolderRegKey (h : LoadEnv) (i : Linstr) (hh : MemHolderRegKey h)
    (hi : isMemToMemMov i.li_i = false) : MemHolderRegKey (stepLoad h i).2 := by
  cases hr : asWideReload i.li_i with
  | none =>
    rw [stepLoad_env_of_not_wideReload h i hr]
    intro k r hk
    exact hh k r (mem_foldl_killReg _ _ _ (mem_foldl_killSlot _ _ _ hk).1).1
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    rw [stepLoad_env_of_wideReload h i hr]
    intro k r hk hrm
    rcases mem_set hk with ⟨hmem, _⟩ | hpair
    · exact hh k r (mem_killReg (mem_killSlot hmem).1).1 hrm
    · have hk1 : k = s := congrArg Prod.fst hpair
      have hr1 : r = d := congrArg Prod.snd hpair
      subst hk1; subst hr1
      simp only [isMemToMemMov, hr, Bool.and_eq_false_iff] at hi
      rcases hi with h1 | h1
      · rw [h1] at hrm; cases hrm
      · exact h1

/-- Under `MemHolderRegKey`, a holder `r` of `s` that `stepLoad` redirects onto is a register
    name. -/
theorem holder_not_mem {h : LoadEnv} (hh : MemHolderRegKey h) {s r : String}
    (hf : h.find s = some r) (hsr : ¬ (isMemName s = false ∧ isMemName r = true)) :
    isMemName r = false := by
  cases hr : isMemName r with
  | false => rfl
  | true => exact absurd ⟨hh s r (mem_of_find hf) hr, hr⟩ hsr

/-- **The redirects read register names.**  On a body with no 64-bit move between two memory
    names, every instruction the scan changes is a 64-bit reload `MOV d ← s` rewritten to
    `MOV d ← r` under the same mnemonic, with `r ≠ d` a register name. -/
theorem loadCSEAux_pointwise_reg (h : LoadEnv) (body : List Linstr) (hh : MemHolderRegKey h)
    (hb : ∀ i ∈ body, isMemToMemMov i.li_i = false) (n : Nat) :
    (loadCSEAux h body)[n]? = body[n]? ∨
      ∃ (i : Linstr) (d s r mn : String),
        body[n]? = some i ∧ asWideReload i.li_i = some (d, s, mn) ∧ r ≠ d ∧
        isMemName r = false ∧
        (loadCSEAux h body)[n]? =
          some { li_ii := i.li_ii, li_i := .Lopn [.reg d] mn [.reg r] } := by
  induction body generalizing h n with
  | nil => left; simp
  | cons i is ih =>
    rw [loadCSEAux_cons]
    cases n with
    | zero =>
      rcases stepLoad_cases h i with hid | ⟨d, s, r, mn, ha, hf, ⟨hrd, _, hsr⟩, heq⟩
      · left; simp [hid]
      · right
        exact ⟨i, d, s, r, mn, rfl, ha, hrd, holder_not_mem hh hf hsr, by simp [heq]⟩
    | succ m =>
      rcases ih (stepLoad h i).2
          (stepLoad_memHolderRegKey h i hh (hb i List.mem_cons_self))
          (fun j hj => hb j (List.mem_cons_of_mem i hj)) m with
        hverb | ⟨i', d, s, r, mn, hb', ha, hrd, hr, he⟩
      · left; simpa using hverb
      · right
        exact ⟨i', d, s, r, mn, by simpa using hb', ha, hrd, hr, by simpa using he⟩

/-! ## 8. Applying the pass to an `Lprog`

`loadCSELfundef` runs the pass on one function's body, leaving every other field
intact; `loadCSELprog` maps it over every function — the entry point an emitter
calls after `elimReloadsLprog` and before `renderLprogAtt`. -/

/-- Run the cross-register load-CSE pass on one function's body. -/
def loadCSELfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := loadCSE f.lfd_body }

/-- Run the cross-register load-CSE pass on every function body in an `Lprog`.
    Every non-`lfd_body` field is preserved. -/
def loadCSELprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, loadCSELfundef f)) }

/-- Per-function: the rewritten body has exactly the same length. -/
theorem loadCSELfundef_body_length (f : Lfundef) :
    (loadCSELfundef f).lfd_body.length = f.lfd_body.length :=
  loadCSE_length f.lfd_body

/-- Per-function: the rewritten body carries the input's mnemonic at every
    position. -/
theorem loadCSELfundef_mnems (f : Lfundef) :
    (loadCSELfundef f).lfd_body.map (fun i => mnemOf i.li_i)
      = f.lfd_body.map (fun i => mnemOf i.li_i) :=
  loadCSE_mnems f.lfd_body

/-- Per-function: the rewritten body reaches the same state. -/
theorem loadCSELfundef_lsemStraight {w : Nat} (f : Lfundef) (s : Lstate w) :
    lsemStraight ((loadCSELfundef f).lfd_body.map Linstr.li_i) s
      = lsemStraight (f.lfd_body.map Linstr.li_i) s :=
  loadCSE_lsemStraight f.lfd_body s

/-- Load-CSE preserves the function signature (args / types / result / frame):
    only `lfd_body` changes. -/
theorem loadCSELfundef_sig (f : Lfundef) :
    (loadCSELfundef f).lfd_arg = f.lfd_arg ∧
    (loadCSELfundef f).lfd_tyin = f.lfd_tyin ∧
    (loadCSELfundef f).lfd_res = f.lfd_res ∧
    (loadCSELfundef f).lfd_tyout = f.lfd_tyout :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Load-CSE preserves the function list and its symbol names. -/
theorem loadCSELprog_names (p : Lprog) :
    (loadCSELprog p).lp_funcs.map Prod.fst = p.lp_funcs.map Prod.fst := by
  simp [loadCSELprog, List.map_map, Function.comp_def]

/-! ## 9. Static rewrite count (for the bench report)

`countRewrites` reports how many loads `loadCSE` redirects to a register move on
a body — the loads that become register moves, removing one memory load from the
LSU per hit. -/

/-- Was this step a cross-register rewrite? (`asWideReload` hit, slot held in a
    different register, the two not both memory names.)  Mirrors the rewrite
    branch of `stepLoad`. -/
def stepIsRewrite (h : LoadEnv) (i : Linstr) : Bool :=
  match asWideReload i.li_i with
  | some (d, s, _) => match h.find s with
                      | some r => decide (r ≠ d) && !(isMemName d && isMemName r)
                      | none => false
  | none => false

/-- Count the cross-register redundant loads `loadCSE` rewrites, threading the
    same environment as `loadCSEAux`. -/
def countRewritesAux : LoadEnv → List Linstr → Nat
  | _, [] => 0
  | h, i :: is =>
      (if stepIsRewrite h i then 1 else 0) + countRewritesAux (stepLoad h i).2 is

/-- Tail-recursive runtime image of `countRewritesAux` (accumulate), avoiding the
    deep non-tail recursion on the ~15 k-instruction Keccak body. -/
def countRewritesAuxTR (acc : Nat) : LoadEnv → List Linstr → Nat
  | _, [] => acc
  | h, i :: is =>
      countRewritesAuxTR (acc + (if stepIsRewrite h i then 1 else 0)) (stepLoad h i).2 is

@[implemented_by countRewritesAuxTR]
def countRewritesAuxImpl (acc : Nat) (h : LoadEnv) (is : List Linstr) : Nat :=
  acc + countRewritesAux h is

/-- The tail-recursive runtime count computes its spec. -/
theorem countRewritesAuxTR_eq (acc : Nat) (h : LoadEnv) (is : List Linstr) :
    countRewritesAuxTR acc h is = acc + countRewritesAux h is := by
  induction is generalizing acc h with
  | nil => simp [countRewritesAuxTR, countRewritesAux]
  | cons i is ih =>
    show countRewritesAuxTR (acc + (if stepIsRewrite h i then 1 else 0)) (stepLoad h i).2 is
      = acc + ((if stepIsRewrite h i then 1 else 0) + countRewritesAux (stepLoad h i).2 is)
    rw [ih]; omega

/-- The number of cross-register redundant loads `loadCSE` rewrites on a body. -/
def countRewrites (body : List Linstr) : Nat :=
  countRewritesAuxImpl 0 [] body

/-- The static rewrite-count of a whole program (sum over functions). -/
def countRewritesLprog (p : Lprog) : Nat :=
  (p.lp_funcs.map (fun (_, f) => countRewrites f.lfd_body)).foldl (· + ·) 0

/-! ## 10. Firing / non-firing pins (`#guard`, evaluated at elaboration)

The bodies below are compared through `movShape`, the `(destination, mnemonic,
source)` view of a single-source register move, so each pin names the mnemonic it
asserts.  Each fails the build on a regression. -/

/-- The `(destination, mnemonic, source)` triple of a single-destination,
    single-source register `Lopn`; `none` for any other instruction. -/
def movShape (i : Linstr) : Option (String × String × String) :=
  match i.li_i with
  | .Lopn [.reg d] mn [.reg s] => some (d, mn, s)
  | _ => none

/-- Two `MOV:64` loads of one slot into different registers. -/
def demoWideHit : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOV:64" [.reg "k.5"]⟩ ]

-- The second load is redirected onto the holding register.
#guard (loadCSE demoWideHit).map movShape
  = [some ("R15", "MOV:64", "k.5"), some ("R14", "MOV:64", "R15")]

-- Every emitted mnemonic is the 64-bit one; no 32-bit `MOV` is emitted.
#guard (loadCSE demoWideHit).map (fun i => mnemOf i.li_i)
  = [some "MOV:64", some "MOV:64"]

/-- The same pair at the `MOVQ` mnemonic. -/
def demoMovqHit : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOVQ" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOVQ" [.reg "k.5"]⟩ ]

-- `MOVQ` fires and is re-emitted as `MOVQ`.
#guard (loadCSE demoMovqHit).map movShape
  = [some ("R15", "MOVQ", "k.5"), some ("R14", "MOVQ", "R15")]

/-- The same pair at the bare 32-bit `MOV` mnemonic. -/
def demoNarrow : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOV" [.reg "k.5"]⟩ ]

-- The bare `MOV` is outside the recognizer and is left alone.
#guard (loadCSE demoNarrow).map movShape = demoNarrow.map movShape

/-- A `MOV:64` load of a slot that a bare `MOV` loaded earlier. -/
def demoMixedWidth : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOV:64" [.reg "k.5"]⟩ ]

-- A 32-bit move records nothing, so the 64-bit load keeps its memory source.
#guard (loadCSE demoMixedWidth).map movShape = demoMixedWidth.map movShape

/-- A store to the cached slot between the two loads. -/
def demoSlotWritten : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "k.5"] "MOV:64" [.reg "R13"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOV:64" [.reg "k.5"]⟩ ]

-- Writing the cell drops its binding.
#guard (loadCSE demoSlotWritten).map movShape = demoSlotWritten.map movShape

/-- A write to the holding register between the two loads. -/
def demoRegWritten : List Linstr :=
  [ ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.5"]⟩,
    ⟨0, .Lopn [.reg "R15"] "ADD:64" [.reg "R15", .reg "R13"]⟩,
    ⟨0, .Lopn [.reg "R14"] "MOV:64" [.reg "k.5"]⟩ ]

-- Writing the holding register drops its binding.
#guard (loadCSE demoRegWritten).map movShape = demoRegWritten.map movShape

end CatCrypt.Crypto.Optimizer.LoadCSE
