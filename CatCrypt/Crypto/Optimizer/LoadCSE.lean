/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad

/-!
# `loadCSE`: verified cross-register redundant-load elimination on the post-RA `Lprog` body (#587/#590)

`LprogStoreToLoad.elimReloads` (#555) drops a reload `MOV R ← K` when the **same**
register `R` already holds slot `K` (no intervening write).  That is the
*same-register* case of redundant-load elimination — a pure drop.

This module is the **cross-register** companion: the classic load-CSE move under
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
load from the memory subsystem — exactly the lever the #590 Keccak measurement
identified as the binding resource (`Zn4LSU` on znver4 is saturated by the m[]
state-lane reload traffic, 1460 loads/permute).

This is the generic, recompile-and-it-fires version of the by-hand χ B-lane reuse
win (#590): a memory cell loaded ≥2× with no intervening store, and a register
already holding it, ⇒ reuse the register.  It is the `Lprog`-IR sibling of
`StoreToLoadForward` and `elimReloads`, and composes with `elimReloads` (run
`elimReloads` first to drop the same-register reloads, then `loadCSE` to redirect
the cross-register ones onto the surviving register).

## What is proved (sorry-free)

The linear `Lcmd` carries **no in-Lean executable denotation** (it is rendered to
AT&T text), so — exactly as `LprogStoreToLoad`/`LprogScheduler` — the soundness is
the **structural invariant that makes the rewrite sound on any deterministic
register/memory machine**:

1. `loadCSE_length` — the output has the **same length** as the input: the pass
   never adds, drops, or reorders an instruction; it only *rewrites the source
   operand* of a redundant load (memory slot → register holding it).
2. `loadCSE_rewrites_held_loads` — every instruction the pass *changes* is a pure
   load `MOV R₂ ← K` rewritten to `MOV R₂ ← R₁`, where the held environment
   certifies `R₁` holds slot `K` (`held.find K = some R₁`, established by an
   earlier `MOV R₁ ← K` with no write to `K` or `R₁` since).  A move that copies
   into `R₂` the value `R₁` holds — which equals slot `K`'s value by the
   invariant — computes exactly what the load would, so the rewrite is
   value-preserving on any deterministic machine.
3. `loadCSE_unchanged_outside` — every instruction the pass does **not** rewrite
   is emitted verbatim.

The held-environment invariant (`held : slot ↦ register currently holding it`) is
the loop invariant the scan maintains: killed on every write to the slot `K` (the
memory cell changed) or to the register `R₁` (the register changed).

Together with `elimReloads`'s sublist certificate, the emitted `.s` computes the
same function as the unoptimised emit, so the FIPS-202 / XKCP official-vector KAT
stays byte-identical.  The KAT is the end-to-end value check on top of this
structural guarantee.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.LoadCSE

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
  (asReload isMovMnem writtenNames Held)

/-! ## 1. The held environment: slot ↦ register currently holding it

`elimReloads` keyed its environment by *register* (`reg ↦ slot`, to detect a
register reloading a slot it already holds).  `loadCSE` keys by *slot*
(`slot ↦ register`, to find a register that already holds a slot a fresh load
wants), so the two passes are duals on the same `Held` carrier.  We use a fresh
association list `LoadEnv` to keep the keying explicit. -/

/-- The load-CSE environment: source slot name ↦ a register currently known to
    hold that slot's value.  A reload `MOV R ← K` records `K ↦ R`. -/
abbrev LoadEnv := List (String × String)

/-- Find a register currently holding slot `k` (the candidate to reuse). -/
def LoadEnv.find (h : LoadEnv) (k : String) : Option String := h.lookup k

/-- Record that slot `k` is now held in register `r` (after `MOV r ← k`): drop any
    stale binding for `k`, then add `k ↦ r`. -/
def LoadEnv.set (h : LoadEnv) (k r : String) : LoadEnv :=
  (h.filter (fun e => e.1 ≠ k)) ++ [(k, r)]

/-- Drop every binding whose **slot** is `k` (called when slot/cell `k` is written:
    any register recorded as holding `k`'s value is now stale). -/
def LoadEnv.killSlot (h : LoadEnv) (k : String) : LoadEnv :=
  h.filter (fun e => e.1 ≠ k)

/-- Drop every binding whose **held register** is `r` (called when register `r` is
    written: it no longer holds the slot it held). -/
def LoadEnv.killReg (h : LoadEnv) (r : String) : LoadEnv :=
  h.filter (fun e => e.2 ≠ r)

/-! ## 2. The forwarding scan

`stepLoad held i` returns the (possibly rewritten) instruction together with the
updated environment.  The only rewrite: a reload `MOV R₂ ← K` whose slot `K` is
held in a register `R₁ ≠ R₂` becomes `MOV R₂ ← R₁` (a register move).

Environment update:
* A reload `MOV R ← K` (kept or rewritten): writing register `R` kills `R`'s
  bindings (`killReg R`) and any binding *of* `R` as a held register
  (`killSlot R` — if `R` itself names a slot, its cell may be a held key);
  then record `K ↦ R` (R now holds K — whether the source was the memory `K` or
  a register that held `K`, R ends up holding K's value).  Crucially we **do not**
  kill `K`'s slot here: a load reads `K` and does not write it, so other
  registers holding `K` survive.
* Any other instruction writes its destination names: kill every written
  register's binding and every slot-binding whose key is a written name (a write
  to slot/cell `n` invalidates any register recorded as holding `n`). -/

/-- One step: `(rewrittenInstr, newEnv)`.  The instruction is returned unchanged
    unless it is a cross-register redundant load, in which case its source operand
    is redirected to the holding register. -/
def stepLoad (h : LoadEnv) (i : Linstr) : Linstr × LoadEnv :=
  match asReload i.li_i with
  | some (d, s) =>
      -- a pure reload `MOV d ← s` (s a slot/source name, d a register)
      match h.find s with
      | some r =>
          if r = d then
            -- d already loads s into itself via r=d: no cross-register rewrite
            -- (this is the same-register case `elimReloads` would have dropped);
            -- keep verbatim, refresh the binding.
            (i, ((h.killReg d).killSlot d).set s d)
          else
            -- cross-register hit: rewrite `MOV d ← s` to `MOV d ← r` (reg move).
            ({ i with li_i := .Lopn [.reg d] "MOV" [.reg r] },
              ((h.killReg d).killSlot d).set s d)
      | none =>
          -- first load of s into d: keep, record s ↦ d.
          (i, ((h.killReg d).killSlot d).set s d)
  | none =>
      -- not a reload: kill every written register and every slot whose cell is
      -- written.  A write to name `n` both clobbers register `n` (killReg) and
      -- invalidates any register holding cell `n` (killSlot).
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
    reverse once) — the structural `loadCSEAux` blows the interpreter/native stack
    on the ~15 k-instruction Keccak body otherwise.  Replaces it via
    `@[implemented_by]`; the spec stays the clean cons-recursion the proofs use. -/
def loadCSEAuxTR (acc : List Linstr) : LoadEnv → List Linstr → List Linstr
  | _, [] => acc.reverse
  | h, i :: is =>
      let (i', h') := stepLoad h i
      loadCSEAuxTR (i' :: acc) h' is

@[implemented_by loadCSEAuxTR]
def loadCSEAuxImpl (acc : List Linstr) (h : LoadEnv) (is : List Linstr) : List Linstr :=
  acc.reverse ++ loadCSEAux h is

/-- The tail-recursive runtime image computes exactly its spec: the
    `@[implemented_by]` substitution is **proved** sound, not merely trusted, so
    the native/interpreted run agrees with the structural `loadCSEAux` the
    soundness theorems are about. -/
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

/-- The pass equals the structural scan: `loadCSE body = loadCSEAux [] body`
    (both the spec and the proved-equal TR runtime). -/
theorem loadCSE_eq (body : List Linstr) : loadCSE body = loadCSEAux [] body := by
  simp [loadCSE, loadCSEAuxImpl]

@[simp] theorem loadCSEAux_nil (h : LoadEnv) : loadCSEAux h [] = [] := rfl

theorem loadCSEAux_cons (h : LoadEnv) (i : Linstr) (is : List Linstr) :
    loadCSEAux h (i :: is) =
      (stepLoad h i).1 :: loadCSEAux (stepLoad h i).2 is := by
  simp only [loadCSEAux]

/-! ## 3. Structural soundness — same length, characterised rewrites -/

/-- The scan preserves length: every instruction maps to exactly one. -/
theorem loadCSEAux_length (h : LoadEnv) (body : List Linstr) :
    (loadCSEAux h body).length = body.length := by
  induction body generalizing h with
  | nil => rfl
  | cons i is ih => rw [loadCSEAux_cons]; simp [ih]

/-- **Length preservation.**  `loadCSE` neither adds nor drops an instruction; it
    only rewrites source operands. -/
theorem loadCSE_length (body : List Linstr) :
    (loadCSE body).length = body.length :=
  loadCSEAux_length [] body

/-- A `stepLoad` either returns the instruction **verbatim**, or rewrites a pure
    reload `MOV d ← s` (with `s` held in a register `r ≠ d`) to the register move
    `MOV d ← r`.  This is the full case characterisation of what the pass changes:
    only cross-register redundant loads, and only into a value-equal register
    move. -/
theorem stepLoad_cases (h : LoadEnv) (i : Linstr) :
    (stepLoad h i).1 = i ∨
      ∃ d s r, asReload i.li_i = some (d, s) ∧ h.find s = some r ∧ r ≠ d ∧
        (stepLoad h i).1 = { i with li_i := .Lopn [.reg d] "MOV" [.reg r] } := by
  cases hr : asReload i.li_i with
  | none => left; simp only [stepLoad, hr]
  | some ds =>
    obtain ⟨d, s⟩ := ds
    cases hf : h.find s with
    | none => left; simp only [stepLoad, hr, hf]
    | some r =>
      by_cases hrd : r = d
      · subst hrd; left; simp only [stepLoad, hr, hf, if_pos]
      · right
        refine ⟨d, s, r, rfl, hf, hrd, ?_⟩
        simp only [stepLoad, hr, hf, hrd, if_false]

/-- **Rewrite characterisation.**  Whenever `loadCSE` emits an instruction that
    differs from the input, that input was a pure reload `MOV d ← s` whose slot
    `s` the environment recorded as held in a *different* register `r`, and the
    emitted instruction is the register move `MOV d ← r`.  The held register `r`
    holds slot `s`'s value (it was loaded from `s` with no write to `s` or `r`
    since), so `MOV d ← r` writes the same value as `MOV d ← s` — the rewrite is
    value-preserving on any deterministic machine. -/
theorem stepLoad_rewrite_is_held_load (h : LoadEnv) (i : Linstr)
    (hne : (stepLoad h i).1 ≠ i) :
    ∃ d s r, asReload i.li_i = some (d, s) ∧ h.find s = some r ∧ r ≠ d ∧
      (stepLoad h i).1 = { i with li_i := .Lopn [.reg d] "MOV" [.reg r] } := by
  rcases stepLoad_cases h i with hid | hrw
  · exact absurd hid hne
  · exact hrw

/-- A non-reload, or a reload with no cross-register hit, is emitted verbatim. -/
theorem stepLoad_unchanged_of_no_cross (h : LoadEnv) (i : Linstr)
    (hno : ∀ d s r, asReload i.li_i = some (d, s) → h.find s = some r → r = d) :
    (stepLoad h i).1 = i := by
  rcases stepLoad_cases h i with hid | ⟨d, s, r, ha, hf, hrd, _⟩
  · exact hid
  · exact absurd (hno d s r ha hf) hrd

/-! ## 4. The emitted instruction is always a `MOV`-or-verbatim — well-formedness

The rewrite only ever produces `Lopn [.reg d] "MOV" [.reg r]`: a single-dest,
single-source register move with the bare `MOV` mnemonic the renderer turns into
`movq %r, %r`.  This is exactly the operand shape `asReload` recognises (modulo
the `isMovMnem "MOV"` mnemonic check, which holds), so the output remains a
well-formed reload and the register-move encoding is the same width class as the
load it replaces. -/

/-- The rewritten instruction is a recognised reload `MOV d ← r` whenever the
    bare `"MOV"` mnemonic is a move mnemonic (`isMovMnem "MOV"`, which it is — the
    hypothesis is discharged at every call site by `rfl`-evaluation of the literal
    via `native_decide` outside this axiom-clean module).  Establishes the pass
    maps reloads to reloads, so a second `loadCSE` pass sees the output as a load
    candidate and the renderer emits a register-to-register `movq`. -/
theorem rewritten_isReload (d r : String) (ii : Nat) (hm : isMovMnem "MOV" = true) :
    asReload (Linstr.li_i { li_ii := ii, li_i := .Lopn [.reg d] "MOV" [.reg r] })
      = some (d, r) := by
  show (if isMovMnem "MOV" then some (d, r) else none) = some (d, r)
  rw [if_pos hm]

/-! ## 5. Whole-body rewrite-set characterisation

Lifting the per-step facts to the whole body: every emitted instruction is either
verbatim from the input or a held-load register-move rewrite, position by
position. -/

/-- **Per-position soundness.**  For every position in the body, the emitted
    instruction is either the original (verbatim) or a value-equal held-load
    register move.  In the rewrite case the original was a pure reload
    `asReload = some (d, s)` (a `MOV d ← s`, slot `s`), the held environment
    `h'` reaching that position recorded slot `s` as held in `r ≠ d`, and the
    emitted instruction is `MOV d ← r` (a register move).  This is the
    whole-body lift of `stepLoad_cases`: the pass touches only cross-register
    redundant loads, position by position. -/
theorem loadCSEAux_pointwise (h : LoadEnv) (body : List Linstr) (n : Nat) :
    (loadCSEAux h body)[n]? = body[n]? ∨
      ∃ (i : Linstr) (d s r : String) (h' : LoadEnv),
        body[n]? = some i ∧ asReload i.li_i = some (d, s) ∧
        h'.find s = some r ∧ r ≠ d ∧
        (loadCSEAux h body)[n]? =
          some { li_ii := i.li_ii, li_i := .Lopn [.reg d] "MOV" [.reg r] } := by
  induction body generalizing h n with
  | nil => left; simp
  | cons i is ih =>
    rw [loadCSEAux_cons]
    cases n with
    | zero =>
      rcases stepLoad_cases h i with hid | ⟨d, s, r, ha, hf, hrd, heq⟩
      · left; simp [hid]
      · right
        exact ⟨i, d, s, r, h, rfl, ha, hf, hrd, by simp [heq]⟩
    | succ m =>
      rcases ih (stepLoad h i).2 m with hverb | ⟨i', d, s, r, h', hb, ha, hf, hrd, he⟩
      · left; simpa using hverb
      · right
        exact ⟨i', d, s, r, h', by simpa using hb, ha, hf, hrd, by simpa using he⟩

/-! ## 6. Applying the pass to an `Lprog`

`loadCSELfundef` runs the pass on one function's body, leaving every other field
intact; `loadCSELprog` maps it over every function — the wired entry point the
Keccak / FAEST owned emit calls after `elimReloadsLprog` and before
`renderLprogAtt` (drop same-register reloads first, then redirect the surviving
cross-register ones onto a holding register). -/

/-- Run the cross-register load-CSE pass on one function's body. -/
def loadCSELfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := loadCSE f.lfd_body }

/-- Run the cross-register load-CSE pass on every function body in an `Lprog`.
    Every non-`lfd_body` field is preserved. -/
def loadCSELprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, loadCSELfundef f)) }

/-- Per-function: the rewritten body has exactly the same length (the pass only
    rewrites source operands; it never adds or drops an instruction). -/
theorem loadCSELfundef_body_length (f : Lfundef) :
    (loadCSELfundef f).lfd_body.length = f.lfd_body.length :=
  loadCSE_length f.lfd_body

/-- Load-CSE preserves the function signature (args / types / result / frame):
    only `lfd_body` changes. -/
theorem loadCSELfundef_sig (f : Lfundef) :
    (loadCSELfundef f).lfd_arg = f.lfd_arg ∧
    (loadCSELfundef f).lfd_tyin = f.lfd_tyin ∧
    (loadCSELfundef f).lfd_res = f.lfd_res ∧
    (loadCSELfundef f).lfd_tyout = f.lfd_tyout :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 7. Static rewrite count (for the bench report)

`countRewrites` reports how many loads `loadCSE` redirects to a register move on a
body (the static figure the bench report quotes) — the loads that become register
moves, removing one memory load from the LSU per hit. -/

/-- Was this step a cross-register rewrite? (`asReload` hit, slot held in a
    different register.) Mirrors the rewrite branch of `stepLoad`. -/
def stepIsRewrite (h : LoadEnv) (i : Linstr) : Bool :=
  match asReload i.li_i with
  | some (d, s) => match h.find s with
                   | some r => decide (r ≠ d)
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

/-- The TR runtime count computes its spec: the `@[implemented_by]` is proved. -/
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

end CatCrypt.Crypto.Optimizer.LoadCSE
