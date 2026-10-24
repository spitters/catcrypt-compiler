/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-!
# `elimReloads`: verified redundant-reload elimination on the post-RA linear `Lprog` body

`StoreToLoadForward.lean` eliminates redundant stack reloads on the
hand-authored `JInstr 64` kernels (`fe25519_mul`, the X25519 ladder), carrying a
full `runBlock`-equality translation-validation certificate against the validated
`JasminModel`.  That pass is wired into the `optimizeX86Block` driver
(`X86ComPipeline.lean`).

The owned **Keccak / FAEST** emit does **not** flow through that driver.  Its path
is `Com (jasminDialect) → comToLfundefPhysAbi → Lcmd → physBody RA →
renderLprogAtt` (the linear-`Lprog` IR), where the block is `List Linstr`, not
`List (JInstr 64)`, and is rendered straight to AT&T text by
`LprogAsmPrinter.renderLprogAtt`.  The `JInstr 64` store-to-load pass cannot reach
it.

This module is the `Lprog`-IR sibling of `StoreToLoadForward`: an `Lcmd → Lcmd`
**redundant-reload eliminator** that runs on the *post-RA physical* body, after
two-address legalization has injected the scratch reloads.  It performs,
with a verified certificate, the gcc-O3 optimization that matters on this
body: not reordering (the `LprogScheduler` schedule gives ~1.01×) but
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
environment `held : reg ↦ (slot, mnemonic)` (the slot a physical register is
currently known to hold, and the mnemonic of the move that loaded it); a reload
`MOV R ← K` under mnemonic `m` whose `held R = some (K, m)` is dropped.  The
mnemonic fixes the operand width (`MOV` is a 32-bit move that zero-extends,
`MOV:64` and `MOVQ` are 64-bit moves), so a dropped reload has the width of the
move that established the binding.

## What is proved

Structurally:

1. `elimReloads_sublist` — the output is a **sublist** of the input: no
   instruction is added, reordered, or modified; the pass only *drops* whole
   `Linstr`s.  Every emitted instruction is verbatim from the input, in the same
   order.  `elimReloads_attr_sublist` transports that to an arbitrary
   per-instruction attribute, so no mnemonic — and hence no rendered operand
   width — is rewritten.
2. `stepReload_drop_is_held_reload` — every dropped instruction is a pure
   reload `MOV R ← K` whose register `R` the held-environment records as already
   holding `K`, loaded by a move of the same mnemonic.

Semantically, against `JasminLsem.lsemStraight` (the straight-line linear
machine at uniform word width, whose `applyOpn` models the single-source
`MOV`/`MOVQ` a reload is; the width-tagged `JasminLsemWidthN.lsemStepN` has no
arm for a single-register-source `Lopn` and so does not model a reload):

3. `elimReloads_lsemStraight` — from any start state, the eliminated body and the
   original body reach the same **store** (`stateStore`: the register map paired
   with memory).  The two program counters differ by the number of dropped
   instructions, which is why the statement compares stores rather than whole
   states.  `HeldSound` — every recorded binding `R ↦ K` satisfies
   `lvm R = lvm K` — is the loop invariant, discharged from the empty initial
   environment rather than assumed, and re-established at each kept step from
   the frame lemma `lsemStep_lvm_of_not_written`.

`isStraightNoLabel` / `IsStraightBody` name the side condition under which the
result reads as a statement about the machine: `lsemStraight` executes the
fall-through path only, so a body that declares a label carries an incoming
control edge the model does not see, along which the held environment need not
hold.  `elimReloads_isStraightBody` records that the pass maps a straight-line
body to a straight-line body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

export CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust (stateStore)

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

/-- The mnemonic of an `Lopn`; `none` for a non-`Lopn` instruction. -/
def mnemOf : LinstrR → Option String
  | .Lopn _ opn _ => some opn
  | _ => none

/-- The mnemonic a reload is recorded under: the mnemonic of the instruction, and the
    empty string for an instruction that is no `Lopn`. -/
def reloadMnem (i : LinstrR) : String := (mnemOf i).getD ""

/-! ## 2. The held environment

`Held` maps a physical register name to the slot/source name it currently holds,
together with the mnemonic of the move that established the binding; the mnemonic
carries the operand width (`MOV` is a 32-bit move, `MOV:64` and `MOVQ` are 64-bit
moves).  A plain association list keyed by register (`HeldOf`);
`set`/`killReg`/`killSlot` keep it sound under the forward scan. -/

/-- An association list keyed by register name. -/
abbrev HeldOf (β : Type) := List (String × β)

/-- The reload environment: register name ↦ the source name it currently holds and the
    mnemonic of the move that loaded it. -/
abbrev Held := HeldOf (String × String)

/-- Look up the value recorded for a register. -/
def HeldOf.find {β : Type} (h : HeldOf β) (r : String) : Option β := h.lookup r

/-- Record the value `k` for register `r`: drop any stale binding for `r`, then add
    `r ↦ k`. -/
def HeldOf.set {β : Type} (h : HeldOf β) (r : String) (k : β) : HeldOf β :=
  (h.filter (fun e => e.1 ≠ r)) ++ [(r, k)]

/-- Drop every binding whose **register** is `r`: a write to `r` invalidates the
    binding recorded for it. -/
def HeldOf.killReg {β : Type} (h : HeldOf β) (r : String) : HeldOf β :=
  h.filter (fun e => e.1 ≠ r)

/-- Drop every binding whose **held slot** is `k` (called when slot `k` is
    written: any register claiming to hold `k`'s value is now stale). -/
def HeldOf.killSlot (h : HeldOf (String × String)) (k : String) : HeldOf (String × String) :=
  h.filter (fun e => e.2.1 ≠ k)

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
already holds its source, loaded by a move of the same mnemonic), and returns the
updated environment.

* A reload `MOV R ← K` under mnemonic `m` with `held R = some (K, m)` is
  **redundant**: drop it, environment unchanged (R still holds K, loaded by a move
  of the same width).
* Any other reload `MOV R ← K` under mnemonic `m` is **kept**: writing register
  `R` drops `R`'s own binding (`killReg R`) and invalidates any register recorded
  as holding `R`-as-a-source (`killSlot R`); then record `R ↦ (K, m)`.  `K`'s own
  value is unchanged by the load, so `K`-as-a-source holders survive — only a
  later write to `K` invalidates them (handled in the general arm below).
* Any other instruction writes its destination names: kill every written
  register's binding and every register holding a written slot.

The decision (`keep?`) and the new environment are returned together. -/

/-- One step: `(keepInstr?, newHeld)`.  `keepInstr? = false` means the
    instruction is a redundant reload to be dropped. -/
def stepReload (h : Held) (i : LinstrR) : Bool × Held :=
  match asReload i with
  | some (d, s) =>
      if h.find d = some (s, reloadMnem i) then
        (false, h)
      else
        (true, ((h.killReg d).killSlot d).set d (s, reloadMnem i))
  | none =>
      let ws := writtenNames i
      let h1 := ws.foldl HeldOf.killReg h
      let h2 := ws.foldl HeldOf.killSlot h1
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
    · simp only [hk, ite_true]
      exact (ih (stepReload h i.li_i).2).cons_cons i
    · simp only [hk, Bool.false_eq_true, ite_false]
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
register the held environment already records as holding `K`, loaded by a move of
the same mnemonic (`held R = some (K, m)`).  We expose that as a theorem.  This is
the structural witness that the drop is value-preserving: the reload copies into
`R` exactly the value `R` already contains, at the width of the move that loaded
it, a no-op on any deterministic machine. -/

/-- **Drop characterisation.**  `stepReload` drops an instruction (`keep = false`)
    only if that instruction is a pure reload `MOV R ← K` whose register `R` the held
    environment already records as holding `K`, loaded by a move of the same
    mnemonic, hence of the same width.  A dropped instruction is therefore a
    register-to-itself no-op (it reloads a value `R` already has), so removing it
    cannot change the machine state. -/
theorem stepReload_drop_is_held_reload (h : Held) (i : LinstrR)
    (hdrop : (stepReload h i).1 = false) :
    ∃ d s, asReload i = some (d, s) ∧ h.find d = some (s, reloadMnem i) := by
  cases hr : asReload i with
  | none =>
    simp only [stepReload, hr] at hdrop; exact absurd hdrop (by decide)
  | some ds =>
    obtain ⟨d, s⟩ := ds
    refine ⟨d, s, rfl, ?_⟩
    by_cases hf : h.find d = some (s, reloadMnem i)
    · exact hf
    · simp only [stepReload, hr, hf, ite_false] at hdrop
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

/-! ## 9. The straight-line side condition

`JasminLsem.lsemStraight` executes a body along its fall-through path.  A body
that declares a label is a jump target, and the forward scan's environment at
that point is the environment of the fall-through predecessor only, so the
semantic results below read as statements about the machine on bodies that
declare no label and transfer no control. -/

/-- An instruction that transfers no control and declares no label: an `Lopn` or
    an `Lalign`. -/
def isStraightNoLabel : LinstrR → Bool
  | .Lopn _ _ _ => true
  | .Lalign => true
  | _ => false

/-- Every instruction of a body transfers no control and declares no label. -/
def IsStraightBody (body : List Linstr) : Prop :=
  ∀ i ∈ body, isStraightNoLabel i.li_i = true

/-- The eliminated body of a straight-line body is straight-line: the pass emits
    a sublist of its input. -/
theorem elimReloads_isStraightBody {body : List Linstr} (h : IsStraightBody body) :
    IsStraightBody (elimReloads body) :=
  fun i hi => h i ((elimReloads_sublist body).subset hi)

/-- Any per-instruction attribute of the output is a sublist of the same
    attribute of the input.  Instantiated at a mnemonic-to-width assignment this
    is the statement that the pass rewrites no operand width. -/
theorem elimReloads_attr_sublist {α : Type} (attr : Linstr → α) (body : List Linstr) :
    ((elimReloads body).map attr).Sublist (body.map attr) :=
  (elimReloads_sublist body).map attr

-- A duplicated 64-bit reload loses its second copy and the survivor keeps the
-- `MOV:64` mnemonic, so the rendered operand width is unchanged.
#guard ((elimReloads [⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩,
                      ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩]).map
          (fun i => mnemOf i.li_i)) == [some "MOV:64"]

/-! ## 10. The held environment against a machine state

`HeldOf` is an association list; `HeldOf.find` reads its first binding for a key,
and every entry of a list found this way is a member of it (`mem_of_find`).  The
`killReg` / `killSlot` / `set` operations are filters and an append, so
membership in the updated environment implies membership in the original
together with the inequality the filter enforces. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-- A `find` hit is a binding of the association list. -/
theorem mem_of_find {β : Type} {h : HeldOf β} {d : String} {k : β} (hf : h.find d = some k) :
    (d, k) ∈ h := by
  induction h with
  | nil => simp [HeldOf.find] at hf
  | cons e rest ih =>
    obtain ⟨d', k'⟩ := e
    by_cases hd : d = d'
    · subst hd
      simp only [HeldOf.find, List.lookup_cons, BEq.rfl] at hf
      simp only [Option.some.injEq] at hf
      subst hf
      exact List.mem_cons_self
    · simp only [HeldOf.find, List.lookup_cons, beq_eq_false_iff_ne.2 hd] at hf
      exact List.mem_cons_of_mem _ (ih hf)

/-- A binding surviving `killReg r` was already present and does not bind `r`. -/
theorem mem_killReg {β : Type} {h : HeldOf β} {p : String × β} {r : String}
    (hp : p ∈ h.killReg r) : p ∈ h ∧ p.1 ≠ r := by
  rw [HeldOf.killReg, List.mem_filter] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- A binding surviving `killSlot k` was already present and does not hold `k`. -/
theorem mem_killSlot {h : Held} {p : String × String × String} {k : String}
    (hp : p ∈ h.killSlot k) : p ∈ h ∧ p.2.1 ≠ k := by
  rw [HeldOf.killSlot, List.mem_filter] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- A binding of `set r k` is either an old binding of a register other than `r`,
    or the new binding `(r, k)`. -/
theorem mem_set {β : Type} {h : HeldOf β} {p : String × β} {r : String} {k : β}
    (hp : p ∈ h.set r k) : (p ∈ h ∧ p.1 ≠ r) ∨ p = (r, k) := by
  rw [HeldOf.set, List.mem_append] at hp
  rcases hp with hf | hl
  · rw [List.mem_filter] at hf
    exact Or.inl ⟨hf.1, by simpa using hf.2⟩
  · exact Or.inr (by simpa using hl)

/-- A binding surviving a fold of `killReg` binds none of the killed registers. -/
theorem mem_foldl_killReg {β : Type} (ws : List String) (h : HeldOf β) (p : String × β)
    (hp : p ∈ ws.foldl HeldOf.killReg h) : p ∈ h ∧ p.1 ∉ ws := by
  induction ws generalizing h with
  | nil => exact ⟨hp, by simp⟩
  | cons a rest ih =>
    rw [List.foldl_cons] at hp
    obtain ⟨hmem, hnot⟩ := ih (h.killReg a) hp
    obtain ⟨hh, hne⟩ := mem_killReg hmem
    exact ⟨hh, by simp only [List.mem_cons, not_or]; exact ⟨hne, hnot⟩⟩

/-- A binding surviving a fold of `killSlot` holds none of the killed slots. -/
theorem mem_foldl_killSlot (ws : List String) (h : Held) (p : String × String × String)
    (hp : p ∈ ws.foldl HeldOf.killSlot h) : p ∈ h ∧ p.2.1 ∉ ws := by
  induction ws generalizing h with
  | nil => exact ⟨hp, by simp⟩
  | cons a rest ih =>
    rw [List.foldl_cons] at hp
    obtain ⟨hmem, hnot⟩ := ih (h.killSlot a) hp
    obtain ⟨hh, hne⟩ := mem_killSlot hmem
    exact ⟨hh, by simp only [List.mem_cons, not_or]; exact ⟨hne, hnot⟩⟩

/-! ### The environment `stepReload` produces, per branch -/

/-- On a kept reload the scan records the loaded slot and the mnemonic of the reload,
    after killing the destination register's own binding and every binding holding
    it. -/
theorem stepReload_env_of_reload {h : Held} {i : LinstrR} {d k : String}
    (hr : asReload i = some (d, k)) (hkeep : (stepReload h i).1 = true) :
    (stepReload h i).2 = ((h.killReg d).killSlot d).set d (k, reloadMnem i) := by
  simp only [stepReload, hr] at hkeep ⊢
  by_cases hf : h.find d = some (k, reloadMnem i)
  · simp [hf] at hkeep
  · simp [hf]

/-- Outside the reload recognizer the scan kills every written register and every
    binding holding a written name. -/
theorem stepReload_env_of_notReload {h : Held} {i : LinstrR} (hr : asReload i = none) :
    (stepReload h i).2 =
      (writtenNames i).foldl HeldOf.killSlot ((writtenNames i).foldl HeldOf.killReg h) := by
  simp [stepReload, hr]

/-- A dropped instruction leaves the environment unchanged. -/
theorem stepReload_env_of_drop {h : Held} {i : LinstrR}
    (hdrop : (stepReload h i).1 = false) : (stepReload h i).2 = h := by
  obtain ⟨d, k, hr, hf⟩ := stepReload_drop_is_held_reload h i hdrop
  simp [stepReload, hr, hf]

/-! ### What a reload is, and what it does

`asReload` accepts exactly a single-destination, single-register-source `Lopn`
whose mnemonic strips to `MOV` or is `MOVQ`.  `applyOpn` gives both mnemonics the
single-source copy semantics, so such an instruction steps by writing the source
register's word to the destination. -/

/-- A recognized reload is a bare register-to-register move under a move
    mnemonic. -/
theorem asReload_shape {i : LinstrR} {d k : String} (h : asReload i = some (d, k)) :
    ∃ opn, isMovMnem opn = true ∧ i = .Lopn [.reg d] opn [.reg k] := by
  unfold asReload at h
  split at h
  · rename_i d' opn k'
    split at h
    · rename_i hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨opn, hm, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognized reload is determined by its destination, its source and the
    mnemonic it is recorded under. -/
theorem asReload_eq_reloadMnem {i : LinstrR} {d k : String} (h : asReload i = some (d, k)) :
    i = .Lopn [.reg d] (reloadMnem i) [.reg k] := by
  obtain ⟨opn, -, rfl⟩ := asReload_shape h
  rfl

/-- A move mnemonic copies its single source word under `applyOpn`. -/
theorem applyOpn_isMovMnem {w : Nat} {opn : String} (hm : isMovMnem opn = true)
    (a : BitVec w) : applyOpn (w := w) (stripWidthTag opn) [a] = some a := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with h | h
  · rw [h]; rfl
  · subst h
    rw [show stripWidthTag "MOVQ" = "MOVQ" from by decide +kernel]; rfl

/-- A recognized reload writes the source register's word to its destination. -/
theorem lsemStep_asReload {w : Nat} {i : LinstrR} {d k : String}
    (hr : asReload i = some (d, k)) (s : Lstate w) :
    lsemStep i s = some ((s.setReg d (s.lvm k)).nextPc) := by
  obtain ⟨opn, hm, rfl⟩ := asReload_shape hr
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, applyOpn_isMovMnem hm]

/-- A recognized reload writes exactly its destination register. -/
theorem writtenNames_asReload {i : LinstrR} {d k : String}
    (hr : asReload i = some (d, k)) : writtenNames i = [d] := by
  obtain ⟨opn, _, rfl⟩ := asReload_shape hr
  rfl

/-- **Frame lemma.**  A step writes only the names `writtenNames` lists, so a
    register outside that list reads the same before and after. -/
theorem lsemStep_lvm_of_not_written {w : Nat} {i : LinstrR} {s s' : Lstate w}
    (hstep : lsemStep i s = some s') {n : String} (hn : n ∉ writtenNames i) :
    s'.lvm n = s.lvm n := by
  unfold lsemStep at hstep
  repeat' split at hstep
  all_goals simp_all [writtenNames]
  all_goals (subst hstep; simp_all [Lstate.setReg, Lstate.nextPc])

/-! ## 11. Store preservation

A deletion shortens the program, so the two runs' program counters differ.  The
comparison is therefore on the **store** — the register map paired with memory —
which the pc does not influence: `lsemStep` reads the pc nowhere, so states with
equal stores step to states with equal stores. -/

/-- The step's store image does not depend on the program counter. -/
theorem lsemStep_stateStore_pc {w : Nat} (i : LinstrR) (m : String → BitVec w)
    (mem : String → Int → BitVec w) (p q : Nat) :
    Option.map stateStore (lsemStep i { lvm := m, lmem := mem, lpc := p }) =
      Option.map stateStore (lsemStep i { lvm := m, lmem := mem, lpc := q }) := by
  have hev : evalOperand ({ lvm := m, lmem := mem, lpc := p } : Lstate w)
      = evalOperand ({ lvm := m, lmem := mem, lpc := q } : Lstate w) := by
    funext o; cases o <;> rfl
  unfold lsemStep
  simp only [hev]
  repeat' split
  all_goals rfl

/-- States with equal stores step to states with equal stores. -/
theorem lsemStep_stateStore_congr {w : Nat} (i : LinstrR) (s1 s2 : Lstate w)
    (h : stateStore s1 = stateStore s2) :
    Option.map stateStore (lsemStep i s1) = Option.map stateStore (lsemStep i s2) :=
  JasminLsemRobust.lsemStep_stateStore i h

/-- Straight-line execution from states with equal stores reaches equal stores. -/
theorem lsemStraight_stateStore_congr {w : Nat} (l : List LinstrR) (s1 s2 : Lstate w)
    (h : stateStore s1 = stateStore s2) :
    Option.map stateStore (lsemStraight l s1) = Option.map stateStore (lsemStraight l s2) := by
  induction l generalizing s1 s2 with
  | nil => simpa using h
  | cons i is ih =>
    have hstep := lsemStep_stateStore_congr i s1 s2 h
    cases h1 : lsemStep i s1 with
    | none =>
      rw [h1] at hstep
      cases h2 : lsemStep i s2 with
      | none => simp [lsemStraight, h1, h2]
      | some t2 => rw [h2] at hstep; simp at hstep
    | some t1 =>
      rw [h1] at hstep
      cases h2 : lsemStep i s2 with
      | none => rw [h2] at hstep; simp at hstep
      | some t2 =>
        rw [h2] at hstep
        simp only [Option.map_some, Option.some.injEq] at hstep
        simp only [lsemStraight, h1, h2]
        exact ih t1 t2 hstep

/-- The held environment agrees with a machine state: every recorded binding
    `R ↦ K` has `R` and `K` holding the same word. -/
def HeldSound {w : Nat} (h : Held) (s : Lstate w) : Prop :=
  ∀ p ∈ h, s.lvm p.1 = s.lvm p.2.1

/-- The empty environment agrees with every state. -/
theorem heldSound_nil {w : Nat} (s : Lstate w) : HeldSound ([] : Held) s := by
  intro p hp; simp at hp

/-- **Invariant preservation.**  A kept step carries the environment agreement
    from the state before to the state after. -/
theorem heldSound_step {w : Nat} {h : Held} {i : LinstrR} {s t : Lstate w}
    (hs : HeldSound h s) (hstep : lsemStep i s = some t)
    (hkeep : (stepReload h i).1 = true) : HeldSound (stepReload h i).2 t := by
  cases hr : asReload i with
  | none =>
    rw [stepReload_env_of_notReload hr]
    intro p hp
    obtain ⟨hp1, hn2⟩ := mem_foldl_killSlot _ _ p hp
    obtain ⟨hp2, hn1⟩ := mem_foldl_killReg _ _ p hp1
    rw [lsemStep_lvm_of_not_written hstep hn1, lsemStep_lvm_of_not_written hstep hn2]
    exact hs p hp2
  | some dk =>
    obtain ⟨d, k⟩ := dk
    rw [stepReload_env_of_reload hr hkeep]
    have ht : t = (s.setReg d (s.lvm k)).nextPc := by
      rw [lsemStep_asReload hr s] at hstep
      exact (Option.some.inj hstep).symm
    subst ht
    intro p hp
    rcases mem_set hp with ⟨hph, hp1⟩ | rfl
    · obtain ⟨hph', hp2⟩ := mem_killSlot hph
      obtain ⟨hph'', _⟩ := mem_killReg hph'
      simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, ite_eq_right hp1, ite_eq_right hp2]
      exact hs p hph''
    · by_cases hkd : k = d <;> simp [hkd]

/-- The scan preserves the store under `lsemStraight`, from any environment that
    agrees with the start state. -/
theorem elimAux_lsemStraight {w : Nat} : ∀ (h : Held) (body : List Linstr) (s : Lstate w),
    HeldSound h s →
    Option.map stateStore (lsemStraight ((elimAux h body).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) := by
  intro h body
  induction body generalizing h with
  | nil => intro s _; rfl
  | cons i is ih =>
    intro s hs
    rw [elimAux_cons]
    by_cases hk : (stepReload h i.li_i).1 = true
    · rw [ite_eq_left hk]
      simp only [List.map_cons, lsemStraight]
      cases hstep : lsemStep i.li_i s with
      | none => rfl
      | some t => exact ih _ t (heldSound_step hs hstep hk)
    · have hdrop : (stepReload h i.li_i).1 = false := by simpa using hk
      rw [ite_eq_right hk, stepReload_env_of_drop hdrop]
      obtain ⟨d, k, hr, hf⟩ := stepReload_drop_is_held_reload h i.li_i hdrop
      rw [ih h s hs]
      simp only [List.map_cons, lsemStraight, lsemStep_asReload hr s]
      refine lsemStraight_stateStore_congr _ s _ ?_
      have hdk : s.lvm d = s.lvm k := hs _ (mem_of_find hf)
      simp only [stateStore, Lstate.lvm_nextPc, Lstate.lvm_setReg, Prod.mk.injEq]
      refine ⟨?_, rfl⟩
      funext r
      by_cases hrd : r = d
      · subst hrd; simp [hdk]
      · simp [hrd]

/-- **Store preservation.**  The eliminated body and the original body reach the
    same register map and memory from any start state; the program counters
    differ by the number of dropped instructions. -/
theorem elimReloads_lsemStraight {w : Nat} (body : List Linstr) (s : Lstate w) :
    Option.map stateStore (lsemStraight ((elimReloads body).map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (body.map Linstr.li_i) s) :=
  elimAux_lsemStraight [] body s (heldSound_nil s)

/-- Per-function store preservation. -/
theorem elimReloadsLfundef_lsemStraight {w : Nat} (f : Lfundef) (s : Lstate w) :
    Option.map stateStore
        (lsemStraight ((elimReloadsLfundef f).lfd_body.map Linstr.li_i) s)
      = Option.map stateStore (lsemStraight (f.lfd_body.map Linstr.li_i) s) :=
  elimReloads_lsemStraight f.lfd_body s

/-- Every function of the transformed program is the eliminated function of the
    source program under the same name. -/
theorem elimReloadsLprog_funcs (p : Lprog) :
    (elimReloadsLprog p).lp_funcs
      = p.lp_funcs.map (fun nf => (nf.1, elimReloadsLfundef nf.2)) := rfl

/-! ## 12. The leakage trace

`JasminLsemRobust.linstrLeak` emits one `LLeak.opn` event per `Lopn`, carrying
the opcode and the operand *shapes*; it reads no register value, no address, and
no branch outcome.  Constant-timeness at this model is therefore independence of
the start state, which `lsemLeak_of_run` shows every completing body has and the
pass keeps (`elimReloads_lsemLeak_state_indep`).

Trace *equality* between input and output does not hold: a reload is an `Lopn`,
so it leaks, and dropping it drops its event.  What holds is that the eliminated
body's trace is the original's with the dropped reloads' events removed — a
`Sublist` (`elimReloads_lsemLeak`).  The two `#guard`s below exhibit an input
whose trace goes from two events to one. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-- **The pass keeps constant-timeness at this model.**  Whenever the eliminated
    body runs to completion from two start states, it leaks the same trace from
    both. -/
theorem elimReloads_lsemLeak_state_indep {w : Nat} (body : List Linstr)
    (s t s₂ t₂ : Lstate w)
    (hs : lsemStraight ((elimReloads body).map Linstr.li_i) s = some s₂)
    (ht : lsemStraight ((elimReloads body).map Linstr.li_i) t = some t₂) :
    lsemLeak ((elimReloads body).map Linstr.li_i) s
      = lsemLeak ((elimReloads body).map Linstr.li_i) t := by
  rw [lsemLeak_of_run _ s s₂ hs, lsemLeak_of_run _ t t₂ ht]

/-- The leakage trace depends on the state only through the store: each
    instruction's contribution is syntactic, and whether the trace continues is
    decided by `lsemStep`, which reads only the store. -/
theorem lsemLeak_stateStore_congr {w : Nat} (l : List LinstrR) (s1 s2 : Lstate w)
    (h : stateStore s1 = stateStore s2) : lsemLeak l s1 = lsemLeak l s2 := by
  induction l generalizing s1 s2 with
  | nil => rfl
  | cons i is ih =>
    have hstep := lsemStep_stateStore_congr i s1 s2 h
    cases h1 : lsemStep i s1 with
    | none =>
      rw [h1] at hstep
      cases h2 : lsemStep i s2 with
      | none => simp [lsemLeak, h1, h2]
      | some t2 => rw [h2] at hstep; simp at hstep
    | some t1 =>
      rw [h1] at hstep
      cases h2 : lsemStep i s2 with
      | none => rw [h2] at hstep; simp at hstep
      | some t2 =>
        rw [h2] at hstep
        simp only [Option.map_some, Option.some.injEq] at hstep
        simp only [lsemLeak, h1, h2]
        rw [ih t1 t2 hstep]

/-- The scan's leakage trace is a sublist of the input's: every kept instruction
    contributes the same event in the same position, and each dropped reload
    contributes an event only to the input's trace. -/
theorem elimAux_lsemLeak {w : Nat} : ∀ (h : Held) (body : List Linstr) (s : Lstate w),
    HeldSound h s →
    (lsemLeak ((elimAux h body).map Linstr.li_i) s).Sublist
      (lsemLeak (body.map Linstr.li_i) s) := by
  intro h body
  induction body generalizing h with
  | nil => intro s _; simp
  | cons i is ih =>
    intro s hs
    rw [elimAux_cons]
    by_cases hk : (stepReload h i.li_i).1 = true
    · rw [ite_eq_left hk]
      simp only [List.map_cons, lsemLeak]
      cases hstep : lsemStep i.li_i s with
      | none => simp
      | some t => exact (List.Sublist.refl _).append (ih _ t (heldSound_step hs hstep hk))
    · have hdrop : (stepReload h i.li_i).1 = false := by simpa using hk
      rw [ite_eq_right hk, stepReload_env_of_drop hdrop]
      obtain ⟨d, k, hr, hf⟩ := stepReload_drop_is_held_reload h i.li_i hdrop
      have hst : stateStore ((s.setReg d (s.lvm k)).nextPc) = stateStore s := by
        have hdk : s.lvm d = s.lvm k := hs _ (mem_of_find hf)
        simp only [stateStore, Lstate.lvm_nextPc, Lstate.lvm_setReg, Prod.mk.injEq]
        refine ⟨?_, rfl⟩
        funext r
        by_cases hrd : r = d
        · subst hrd; simp [hdk]
        · simp [hrd]
      simp only [List.map_cons, lsemLeak, lsemStep_asReload hr s,
        lsemLeak_stateStore_congr (is.map Linstr.li_i) _ s hst]
      exact (ih h s hs).trans (List.sublist_append_right _ _)

/-- **Leakage containment.**  The eliminated body's leakage trace is a sublist of
    the original's: the pass removes the dropped reloads' events and changes no
    other event.  It is not an equality — a reload is an `Lopn` and therefore
    leaks. -/
theorem elimReloads_lsemLeak {w : Nat} (body : List Linstr) (s : Lstate w) :
    (lsemLeak ((elimReloads body).map Linstr.li_i) s).Sublist
      (lsemLeak (body.map Linstr.li_i) s) :=
  elimAux_lsemLeak [] body s (heldSound_nil s)

-- A duplicated reload leaks twice before the pass and once after, so leakage
-- equality fails on the shape the pass fires on.
#guard
  (lsemLeak ([⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩,
              ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩].map Linstr.li_i)
      ({ lvm := fun _ => 0 } : Lstate 64)).length == 2

#guard
  (lsemLeak ((elimReloads [⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩,
                           ⟨0, .Lopn [.reg "R15"] "MOV:64" [.reg "k.7"]⟩]).map Linstr.li_i)
      ({ lvm := fun _ => 0 } : Lstate 64)).length == 1

end CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
