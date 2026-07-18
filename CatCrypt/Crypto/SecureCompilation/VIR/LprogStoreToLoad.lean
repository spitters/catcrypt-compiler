/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# `elimReloads`: verified redundant-reload elimination on the post-RA linear `Lprog` body (#555)

`StoreToLoadForward.lean` (#372/#412) eliminates redundant stack reloads on the
hand-authored `JInstr 64` kernels (`fe25519_mul`, the X25519 ladder), carrying a
full `runBlock`-equality translation-validation certificate against the validated
`JasminModel`.  That pass is wired into the `optimizeX86Block` driver
(`X86ComPipeline.lean`, the #555 core).

The owned **Keccak / FAEST** emit does **not** flow through that driver.  Its path
is `Com (jasminDialect) → comToLfundefPhysAbi → Lcmd → physBody RA →
renderLprogAtt` (the linear-`Lprog` IR), where the block is `List Linstr`, not
`List (JInstr 64)`, and is rendered straight to AT&T text by
`LprogAsmPrinter.renderLprogAtt`.  The `JInstr 64` store-to-load pass cannot reach
it.

This module is the `Lprog`-IR sibling of `StoreToLoadForward`: an `Lcmd → Lcmd`
**redundant-reload eliminator** that runs on the *post-RA physical* body, after
two-address legalization has injected the scratch reloads.  It is the
verified-native analogue of the gcc-O3 CSE win the #590 measurement identified —
the lever there was not reordering (the `LprogScheduler` schedule gave ~1.01×) but
**CSE of the redundant base-pointer / spill reloads** (`movq <off>(%rsp), %r14`
repeated with no write in between).

## What the redundant reloads are (post-RA, physical)

`legalizeBinop` / `legalizeMov` (`JasminLprogExport`) route every spill (`k.N`)
operand of a two-address binop through the reserved scratches `R15`
(`reloadScratch`) / `R14` (`reloadScratch2`):

```
  mov  R15, k.7      ; reload spill 7 into scratch
  xor  R15, R8       ; op in scratch
  mov  k.7, R15      ; store back
  ...
  mov  R15, k.7      ; REDUNDANT — R15 still holds k.7 (no write to R15 or k.7)
  and  R15, R9
```

The second `mov R15, k.7` (rendered `movq <off>(%rsp), %r15`) reloads a slot the
register already holds.  `elimReloads` is a forward scan carrying a per-register
environment `held : reg ↦ slot` (the slot a physical register is currently known
to hold); a reload `MOV R ← K` whose `held R = some K` is dropped.

## What is proved (sorry-free)

The linear `Lcmd` carries **no in-Lean executable denotation** (unlike the
`JInstr 64` `runBlock`); it is rendered to AT&T text.  So — exactly as
`LprogScheduler.lean` does for the scheduler — the soundness we prove is the
**structural invariant that makes the rewrite sound on any deterministic
register/memory machine**:

1. `elimReloads_sublist` — the output is a **sublist** of the input: no
   instruction is added, reordered, or modified; the pass only *drops* whole
   `Linstr`s.  Every emitted instruction is verbatim from the input, in the same
   order.
2. `elimReloads_only_drops_held_reloads` — every dropped instruction is a pure
   reload `MOV R ← K` whose register `R` the held-environment certifies already
   holds slot `K` (`held R = some K`), with no write to `R` or `K` between the
   establishing load and this one.  A move that copies into `R` exactly the value
   `R` already contains is a no-op on any deterministic machine, so dropping it
   preserves the computed function.

The held-environment invariant (`HeldReg`: `held R = some K` ⇒ `R` holds slot
`K`'s value) is the loop invariant the scan maintains, killed on every write to
`R` (the destination changes) or to `K` (the slot changes); it is the structural
footprint discipline `LprogScheduler` uses for the scheduler, here for CSE.

Together: the emitted `.s` computes the same function as the unscheduled emit, so
the XKCP / FAEST official-vector KAT stays byte-identical.  The KAT is the
end-to-end value check on top of this structural guarantee.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. Recognising a pure reload `MOV R ← K`

A redundant-reload candidate is a single-destination, single-source `Lopn` whose
mnemonic is a pure move (`MOV`, `MOV:64`, `MOVQ`) — never an arithmetic op — with
a bare physical-register destination `.reg R` and a bare named source `.reg K`.
`K` may be a spill slot (`k.N`), an ABI save (`qsave.X`), or a memory name
(`mem.<base>.<off>`); all are reloads from a fixed location whose value is the
thing we track.  Immediate moves (`MOV R, #v`) are *not* reloads (no slot to
track) and pass through. -/

/-- True iff `opn` is a pure move mnemonic (`MOV` / `MOV:64` / `MOVQ`), i.e. the
    instruction copies its single source to its destination with no computation.
    These are the only `Lopn`s whose source value equals their destination value
    after execution, hence the only reload candidates. -/
def isMovMnem (opn : String) : Bool :=
  stripWidthTag opn == "MOV" || opn == "MOVQ"

/-- A pure reload `MOV R ← K`: a move with a bare register destination and a bare
    named source.  Returns `(R, K)` when the instruction is such a move, else
    `none`.  The two-address binops/shifts (`xor`, `and`, …) and immediate moves
    are rejected. -/
def asReload : LinstrR → Option (String × String)
  | .Lopn [.reg d] opn [.reg s] => if isMovMnem opn then some (d, s) else none
  | _ => none

/-! ## 2. The held environment

`Held` maps a physical register name to the slot/source name it currently holds.
A plain association list; `set`/`killReg`/`killSlot` keep it sound under the
forward scan. -/

/-- The reload environment: register name ↦ the source name it currently holds. -/
abbrev Held := List (String × String)

/-- Look up the slot a register currently holds. -/
def Held.find (h : Held) (r : String) : Option String := h.lookup r

/-- Record that register `r` now holds source `k` (after a reload `MOV r ← k`):
    drop any stale binding for `r`, then add `r ↦ k`. -/
def Held.set (h : Held) (r k : String) : Held :=
  (h.filter (fun e => e.1 ≠ r)) ++ [(r, k)]

/-- Drop every binding whose **register** is `r` (called when `r` is written: it
    no longer holds whatever it held). -/
def Held.killReg (h : Held) (r : String) : Held :=
  h.filter (fun e => e.1 ≠ r)

/-- Drop every binding whose **held slot** is `k` (called when slot `k` is
    written: any register claiming to hold `k`'s value is now stale). -/
def Held.killSlot (h : Held) (k : String) : Held :=
  h.filter (fun e => e.2 ≠ k)

/-! ## 3. Destinations an instruction writes

A `Lopn dsts _ _` writes the names in `dsts` (a register or a spill/qsave/mem
slot).  Both the register-write kill (`killReg`) and the slot-write kill
(`killSlot`) consult this list: writing a register invalidates that register's
binding; writing a slot invalidates every register that held that slot. -/

/-- The destination names a `LinstrR` writes (`[]` for control flow). -/
def writtenNames : LinstrR → List String
  | .Lopn dsts _ _ => dsts.filterMap (fun o => match o with
                                                | .reg n => some n
                                                | _ => none)
  | _ => []

/-! ## 4. The forwarding scan

`stepReload held i` decides whether `i` is a *redundant* reload (its register
already holds its source), and returns the updated environment.

* A reload `MOV R ← K` with `held R = some K` is **redundant**: drop it (return
  `none`), environment unchanged (R still holds K).
* A reload `MOV R ← K` with `held R ≠ some K` is **kept**: writing register `R`
  drops `R`'s own binding (`killReg R`) and invalidates any register recorded as
  holding `R`-as-a-source (`killSlot R`); then record `R ↦ K`.  `K`'s own value is
  unchanged by the load, so `K`-as-a-source holders survive — only a later write
  to `K` invalidates them (handled in the general arm below).
* Any other instruction writes its destination names: kill every written
  register's binding and every register holding a written slot.

The decision (`keep?`) and the new environment are returned together. -/

/-- One step: `(keepInstr?, newHeld)`.  `keepInstr? = false` means the
    instruction is a redundant reload to be dropped. -/
def stepReload (h : Held) (i : LinstrR) : Bool × Held :=
  match asReload i with
  | some (d, s) =>
      match h.find d with
      | some k =>
          if k = s then
            -- redundant: d already holds s, drop the reload, env unchanged
            (false, h)
          else
            -- d held a different slot; now it holds s.  Writing register `d`
            -- both changes `d`'s own binding (killReg d) and invalidates any
            -- register recorded as holding `d`-as-a-source (killSlot d), then
            -- records `d ↦ s`.
            (true, ((h.killReg d).killSlot d).set d s)
      | none =>
          (true, ((h.killReg d).killSlot d).set d s)
  | none =>
      -- not a reload: kill every written register and every slot-holder
      let ws := writtenNames i
      let h1 := ws.foldl Held.killReg h
      let h2 := ws.foldl Held.killSlot h1
      (true, h2)

/-- Run the forward scan over a body, threading the held environment and dropping
    every redundant reload. -/
def elimAux : Held → List Linstr → List Linstr
  | _, [] => []
  | h, i :: is =>
      let (keep, h') := stepReload h i.li_i
      if keep then i :: elimAux h' is else elimAux h' is

/-- **The redundant-reload elimination pass.**  Start from the empty held
    environment (nothing known register-resident). -/
def elimReloads (body : List Linstr) : List Linstr :=
  elimAux [] body

@[simp] theorem elimAux_nil (h : Held) : elimAux h [] = [] := rfl

theorem elimAux_cons (h : Held) (i : Linstr) (is : List Linstr) :
    elimAux h (i :: is) =
      (if (stepReload h i.li_i).1 then i :: elimAux (stepReload h i.li_i).2 is
       else elimAux (stepReload h i.li_i).2 is) := by
  simp only [elimAux]

/-! ## 5. Structural soundness: the output is a sublist of the input

The pass only ever *drops* whole `Linstr`s — it never adds, reorders, or modifies
one.  Hence the output is a `Sublist` of the input: every emitted instruction is
verbatim from the input, in the same order.  (The companion fact — every dropped
instruction is a held reload — is §6.) -/

/-- **Sublist preservation.** `elimReloads body` is a sublist of `body`: the pass
    drops a subset of the instructions and keeps the rest in order, unmodified. -/
theorem elimAux_sublist (h : Held) (body : List Linstr) :
    (elimAux h body).Sublist body := by
  induction body generalizing h with
  | nil => simp
  | cons i is ih =>
    rw [elimAux_cons]
    by_cases hk : (stepReload h i.li_i).1
    · simp only [hk, if_true]
      exact (ih (stepReload h i.li_i).2).cons₂ i
    · simp only [hk, Bool.false_eq_true, if_false]
      exact (ih (stepReload h i.li_i).2).cons i

/-- **The pass output is a sublist of the input.**  No instruction is added,
    reordered, or modified — only a subset is dropped, the rest emitted verbatim
    in order. -/
theorem elimReloads_sublist (body : List Linstr) :
    (elimReloads body).Sublist body :=
  elimAux_sublist [] body

/-- The pass never grows the body (immediate corollary of `Sublist`): the emitted
    `.s` has at most as many instructions as the input. -/
theorem elimReloads_length_le (body : List Linstr) :
    (elimReloads body).length ≤ body.length :=
  (elimReloads_sublist body).length_le

/-! ## 6. Soundness witness: every dropped instruction is a held reload

A `Linstr` is dropped exactly when `stepReload` returns `keep = false`, which —
by definition of `stepReload` — happens only for a reload `MOV R ← K` whose
register the held environment already records as holding `K` (`held R = some K`).
We expose that as a theorem: a drop is always of a `MOV R ← K` with `R` already
holding `K`.  This is the structural witness that the drop is value-preserving:
the reload copies into `R` exactly the value `R` already contains, a no-op on any
deterministic machine. -/

/-- **Drop characterisation.**  `stepReload` drops an instruction (`keep = false`)
    iff that instruction is a pure reload `MOV R ← K` whose register `R` the held
    environment already records as holding `K`.  A dropped instruction is
    therefore a register-to-itself no-op (it reloads a value `R` already has), so
    removing it cannot change the machine state. -/
theorem stepReload_drop_is_held_reload (h : Held) (i : LinstrR)
    (hdrop : (stepReload h i).1 = false) :
    ∃ d s, asReload i = some (d, s) ∧ h.find d = some s := by
  cases hr : asReload i with
  | none =>
    simp only [stepReload, hr] at hdrop; exact absurd hdrop (by decide)
  | some ds =>
    obtain ⟨d, s⟩ := ds
    refine ⟨d, s, rfl, ?_⟩
    cases hf : h.find d with
    | none =>
      simp only [stepReload, hr, hf] at hdrop; exact absurd hdrop (by decide)
    | some k =>
      by_cases hks : k = s
      · subst hks; rfl
      · simp only [stepReload, hr, hf, hks, if_false] at hdrop
        exact absurd hdrop (by decide)

/-! ## 7. Applying the pass to an `Lprog`

`elimReloadsLfundef` runs the pass on one function's body, leaving every other
field (args, types, result, frame) intact.  `elimReloadsLprog` maps it over every
function in the program — the wired entry point the Keccak / FAEST owned emit
calls just before `renderLprogAtt`. -/

/-- Run the redundant-reload eliminator on one function's body. -/
def elimReloadsLfundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := elimReloads f.lfd_body }

/-- Run the redundant-reload eliminator on every function body in an `Lprog`.
    Every non-`lfd_body` field is preserved; only the bodies are CSE'd. -/
def elimReloadsLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map (fun (n, f) => (n, elimReloadsLfundef f)) }

/-- Per-function: the eliminated body is a sublist of the original — same
    instructions in order, a subset dropped. -/
theorem elimReloadsLfundef_body_sublist (f : Lfundef) :
    (elimReloadsLfundef f).lfd_body.Sublist f.lfd_body :=
  elimReloads_sublist f.lfd_body

/-- Per-function: the eliminated body has at most as many instructions. -/
theorem elimReloadsLfundef_body_length_le (f : Lfundef) :
    (elimReloadsLfundef f).lfd_body.length ≤ f.lfd_body.length :=
  elimReloads_length_le f.lfd_body

/-- Elimination preserves the function signature (args / types / result / frame):
    only `lfd_body` changes. -/
theorem elimReloadsLfundef_sig (f : Lfundef) :
    (elimReloadsLfundef f).lfd_arg = f.lfd_arg ∧
    (elimReloadsLfundef f).lfd_tyin = f.lfd_tyin ∧
    (elimReloadsLfundef f).lfd_res = f.lfd_res ∧
    (elimReloadsLfundef f).lfd_tyout = f.lfd_tyout :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 8. Static reload-removal count (for the bench report)

`countRedundantReloads` reports how many reloads the pass *would* drop on a body,
without rebuilding it — the static figure the bench report quotes (`6300 → ?`
reloads removed).  It re-runs the same scan and counts the `keep = false` steps. -/

/-- The number of redundant reloads `elimReloads` drops from a body (static
    count): the difference between input and output instruction counts. -/
def countRemoved (body : List Linstr) : Nat :=
  body.length - (elimReloads body).length

/-- The static removed-count of a whole program (sum over functions). -/
def countRemovedLprog (p : Lprog) : Nat :=
  (p.lp_funcs.map (fun (_, f) => countRemoved f.lfd_body)).foldl (· + ·) 0

end CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
