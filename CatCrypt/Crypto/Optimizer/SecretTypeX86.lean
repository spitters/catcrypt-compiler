/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.StoreToLoadForward
public import CatCrypt.Crypto.Optimizer.SecretType
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline

/-!
# A fourth pass for the compositional-CT taint story: the owned-x86 store-to-load
  forwarding / mem2reg block rewrite (#594 ↔ #555)

`Optimizer/SecretType.lean` seeds *constant-time as a compositional typing
invariant* — a secret/public taint qualifier flows along the typed
`Com jasminDialect` let-chain — and shows two passes keep it well-formed
(peephole *preserves* per-binder taint; the egraph *declassifies
monotonically*). `Optimizer/SecretTypeScheduler.lean` adds a third pass — the
ILP scheduler over `List BBStmt` — which *exactly* preserves the block taint
summary `blockMaxTaint`.

This file adds the **owned-x86 backend pass** (#555-C): the
store-to-load-forwarding / mem2reg block rewrite `optimizeX86Block`
(`X86ComPipeline`), which operates on the owned `List (JInstr 64)` machine-IR
the field/bignum leaves emit. Like the egraph pass it is *not* a pure reorder,
but unlike it the relevant guarantee is a **preservation** rather than
mere monotonicity: forwarding a store→load copies a value to where it was
already flowing, so a cell's taint is reproduced exactly at the register that
already holds it.

## The representation gap and how we bridge it

`storeToLoadForward` operates on `List (JInstr 64)` over **string-named
registers** and **frame cells** `(base, off)`, not the De-Bruijn `Com
jasminDialect` of `SecretType` nor the `List BBStmt` of `SecretTypeScheduler`.
So — exactly as `SecretTypeScheduler` does for `BBStmt` — we define the taint
summary at the representation the pass actually uses, reusing `SecretType`'s
`SecretLevel` lattice:

* a **register** taint env `RegTaint := String → SecretLevel`,
* a **cell** taint env `CellTaint := (String × Int) → SecretLevel`,
* `instrTaint R C i` : the taint of instruction `i`'s output — the join of the
  taints of the registers/cells it reads (data-flow taint),
* `stepRegTaint` / `stepCellTaint` : threading an instruction updates the
  register it writes (to `instrTaint`) and, for a `storeMem (.reg r)`, records
  that the stored cell now carries register `r`'s taint,
* `blockMaxTaintX R C b` : the running join of every instruction's output taint
  down the threaded envs — the `List (JInstr 64)` analogue of
  `comMaxTaint`/`blockMaxTaint`.

## The forwarding invariant and what we prove

The pass's only rewrite is `loadMem d base off → mov d (.reg r)` when the
held-environment records `(base, off) ↦ r`. The denotational soundness rests on
the held-environment invariant `HeldValid` (`StoreToLoadForward`): the cell
`(base, off)` *holds* register `r`. The taint analogue `HeldTaintValid h C R`
says the cell carries the **same taint** as the register that holds it:
`C (base, off) = R r` for every `(base, off) ↦ r` in `h`. Under it,
`loadMem`'s output taint (the cell's) equals `mov d (.reg r)`'s (the
register's), so the forward is taint-**preserving** — and threading the
rewritten step re-establishes the invariant.

`storeToLoadForward_blockMaxTaintX_eq` proves the forwarding stage preserves the
summary **exactly** from the empty (vacuously valid) held env. The driver's other
three stages — the identity-mov drop, redundant spill-reload elimination, and the
guarded MUL→MULX fusion — each delete an instruction whose contribution to the
running join is dropped while the threaded envs stay fixed, so each is stated in
the `⊑ₛ` form. The headline `optimizeX86Block_blockMaxTaintX_le` (≤, the
declassification form shared with the egraph and the `#555` driver's gated
nature) chains the four: the driver never **raises** the block taint summary.

All goals closed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.SecretTypeX86

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.SecretType (SecretLevel)
open CatCrypt.Crypto.Optimizer.StoreToLoadForward
open CatCrypt.Crypto.Optimizer.GraphColoringCoalesce (isIdMov dropIdMovs)
open CatCrypt.Crypto.Optimizer.RedundantReloadElim
  (consDrop dropReloads defaultSpillBases dropReloads_cons eq_of_isRedundantReload)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFlagLiveness
  (fuseMulxGuarded isRedundantLowMul_some isWideningMul_some)

open CatCrypt.Crypto.Optimizer.SecretType.SecretLevel (join leq)

/-! ## 1. Register- and cell-taint environments over the owned-x86 IR

`storeToLoadForward`'s instructions name registers and frame cells with
`String`/`(String × Int)`, so the taint assignment is a pair of total functions
(the owned-x86 analogue of `SecretType.Taint Γ` and
`SecretTypeScheduler.BBTaint`). -/

/-- A taint assignment over named registers. -/
abbrev RegTaint := String → SecretLevel

/-- A taint assignment over frame cells `(base, off)`. -/
abbrev CellTaint := (String × Int) → SecretLevel

/-- The taint contributed by reading an operand: a register's recorded taint, a
constant (`imm`) is `pub`. -/
def operandTaint (R : RegTaint) : JOperand → SecretLevel
  | .reg r => R r
  | .imm _ => .pub

/-- The output taint of an instruction: the join of the taints of everything it
reads (registers via `R`, frame cells via `C`). Two-address arithmetic reads
its destination as source 0, so `dst`'s current taint joins in. The owned-x86
analogue of `exprTaint` / `stmtTaint`. -/
def instrTaint (R : RegTaint) (C : CellTaint) : JInstr 64 → SecretLevel
  | .mov _ src      => operandTaint R src
  | .add dst src | .sub dst src | .adc dst src | .sbb dst src | .imul dst src
  | .and_ dst src | .or_ dst src | .xor_ dst src | .shl dst src | .shr dst src
  | .sar dst src    => R dst ⊔ₛ operandTaint R src
  | .neg dst        => R dst
  -- `test` reads both operands and joins their taints into the five flags. It
  -- writes no register, so `writtenRegs` keeps `stepRegTaint` from binding this
  -- level anywhere; the level is what the flag state carries.
  | .test a src     => R a ⊔ₛ operandTaint R src
  -- `cmp` reads both operands into the five flags and writes no register, so
  -- `writtenRegs` keeps `stepRegTaint` from binding this level anywhere.
  | .cmp a src      => R a ⊔ₛ operandTaint R src
  | .setc _         => .pub
  | .not_ dst       => R dst
  | .andn _ a b     => R a ⊔ₛ R b
  | .rol dst amt | .ror dst amt => R dst ⊔ₛ operandTaint R amt
  | .rorx _ src amt => R src ⊔ₛ operandTaint R amt
  | .shlx _ src cnt | .shrx _ src cnt | .sarx _ src cnt => R src ⊔ₛ R cnt
  | .movzx _ _ src | .movsx _ _ src => R src
  -- `lea` computes an address from its two registers; it reads no cell.
  | .lea _ base idx _ _ => R base ⊔ₛ R idx
  | .cmove dst src | .cmovne dst src | .cmovb dst src => R dst ⊔ₛ operandTaint R src
  | .mulx _ _ a b   => operandTaint R a ⊔ₛ operandTaint R b
  | .mulxMem _ _ a base off => operandTaint R a ⊔ₛ C (base, off)
  | .adcx dst src | .adox dst src => R dst ⊔ₛ operandTaint R src
  | .loadMem _ base off     => C (base, off)
  | .storeMem _ _ src       => operandTaint R src
  | .loadMemIdx _ _ _ _     => .sec
  | .storeMemIdx _ _ _ _    => .pub
  -- `leaq sym(%rip), %dst`: `sym` is a public `.rodata` label, so the loaded
  -- table-base address is a PUBLIC constant (like `loadImm`), never secret.
  | .loadSym _ _            => .pub
  | .inc dst | .dec dst     => R dst
  -- `clc`/`stc` write a constant flag and read nothing.
  | .clc | .stc             => .pub
  -- `xchg` writes both operands; `stepRegTaint` binds both to the join.
  | .xchg a b               => R a ⊔ₛ R b
  | .imulri _ src _         => R src
  | .mul _ lo src | .imulWide _ lo src => R lo ⊔ₛ R src
  | .shld dst src amt | .shrd dst src amt => R dst ⊔ₛ R src ⊔ₛ operandTaint R amt
  | .testN _ a b | .bt a b  => R a ⊔ₛ operandTaint R b
  | .btr dst b | .bts dst b => R dst ⊔ₛ operandTaint R b
  -- `rcl`/`rcr` read `CF`, and `cmovcc`/`setcc` read the flags of their condition.
  -- The environments record no flag taint, so the flag input is joined as `.sec`.
  | .rcl dst amt | .rcr dst amt => R dst ⊔ₛ operandTaint R amt ⊔ₛ .sec
  | .cmovcc _ dst src       => R dst ⊔ₛ operandTaint R src ⊔ₛ .sec
  | .setcc _ dst            => R dst ⊔ₛ .sec

/-- Threading an instruction through the register-taint env: bind every register
it writes (`writtenRegs`) to the instruction's output taint. -/
def stepRegTaint (R : RegTaint) (C : CellTaint) (i : JInstr 64) : RegTaint :=
  fun y => if y ∈ writtenRegs i then instrTaint R C i else R y

/-- Threading an instruction through the cell-taint env: a `storeMem (.reg r)`
records that cell `(base, off)` now carries register `r`'s taint; any other
single-cell store records that cell's stored taint; everything else leaves the
cell env unchanged (loads and register ops do not write a statically-known
cell). -/
def stepCellTaint (R : RegTaint) (C : CellTaint) (i : JInstr 64) : CellTaint :=
  fun y =>
    match i with
    | .storeMem base off src => if y = (base, off) then operandTaint R src else C y
    | _ => C y

/-- The block taint summary: the running join of every instruction's output
taint down the threaded register/cell envs. The `List (JInstr 64)` analogue of
`comMaxTaint` / `blockMaxTaint`. -/
def blockMaxTaintX (R : RegTaint) (C : CellTaint) : List (JInstr 64) → SecretLevel
  | []      => .pub
  | i :: is => instrTaint R C i ⊔ₛ
      blockMaxTaintX (stepRegTaint R C i) (stepCellTaint R C i) is

/-! ## 2. The taint-level held invariant

`HeldTaintValid h C R` is the taint analogue of `StoreToLoadForward.HeldValid`:
every recorded binding `(base, off) ↦ r` carries, at the taint level, the same
secrecy as the register that holds it: `C (base, off) = R r`. This is exactly
the fact that makes the `loadMem d base off → mov d (.reg r)` rewrite
taint-preserving — the load reads the cell, the move reads the register, and the
invariant says they have equal taint. Like `HeldValid` it is stated on
**membership** (monotone under `filter`, so the `kill*` ops preserve it). -/

/-- Every binding in `h` carries equal cell- and register-taint. -/
def HeldTaintValid (h : Held) (C : CellTaint) (R : RegTaint) : Prop :=
  ∀ e ∈ h, C e.1 = R e.2

/-- `find`-level consequence at a forwarding site. -/
theorem heldTaintValid_find {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) {base : String} {off : Int} {r : String}
    (hf : h.find base off = some r) : C (base, off) = R r :=
  hv _ (find_mem hf)

/-- `filter` only drops entries, so the invariant transfers along membership. -/
theorem HeldTaintValid.filter {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (p : ((String × Int) × String) → Bool) :
    HeldTaintValid (h.filter p) C R :=
  fun e he => hv e (List.mem_filter.mp he).1

theorem HeldTaintValid.killReg {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (r : String) :
    HeldTaintValid (h.killReg r) C R := hv.filter _

theorem HeldTaintValid.killCell {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (base : String) (off : Int) :
    HeldTaintValid (h.killCell base off) C R := hv.filter _

/-- `loadMem` does not write a cell, so `stepCellTaint` is the identity on it. -/
@[simp] theorem stepCellTaint_loadMem (R : RegTaint) (C : CellTaint)
    (d base : String) (off : Int) :
    stepCellTaint R C (.loadMem d base off) = C := rfl

/-- After a non-`storeMem` instruction the cell env is unchanged. -/
theorem stepCellTaint_nonstore (R : RegTaint) (C : CellTaint) (i : JInstr 64)
    (h : ∀ b o v, i ≠ .storeMem b o v) : stepCellTaint R C i = C := by
  cases i with
  | storeMem b o v => exact absurd rfl (h b o v)
  | _ => rfl

/-- A member of `foldl killReg h ws` is a member of `h` (the held register is not
in `ws`, but here we need only membership). Reuses
`StoreToLoadForward.mem_foldl_killReg`. -/
theorem HeldTaintValid.killWrittenMem {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (i : JInstr 64) :
    HeldTaintValid (killWritten h i) C R := by
  intro e he
  exact hv e (mem_foldl_killReg _ _ he).1

/-- **The killed env stays valid under the *threaded* register env.** A surviving
held entry's register is not in `writtenRegs i`, so `stepRegTaint R C i` leaves
its taint at `R`; the cell env is unchanged for a non-store instruction. So
`killWritten h i` is `HeldTaintValid` under `(stepCellTaint R C i, stepRegTaint
R C i)` whenever `i` writes no static cell. -/
theorem HeldTaintValid.killWrittenStep {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (i : JInstr 64)
    (hns : ∀ b o v, i ≠ .storeMem b o v) :
    HeldTaintValid (killWritten h i) (stepCellTaint R C i) (stepRegTaint R C i) := by
  rw [stepCellTaint_nonstore R C i hns]
  intro e he
  obtain ⟨hmem, hnin⟩ := mem_foldl_killReg _ _ he
  have : stepRegTaint R C i e.2 = R e.2 := by simp [stepRegTaint, hnin]
  rw [this]; exact hv e hmem

/-! ## 3. The taint envs the scan threads agree with `stepRegTaint`/`stepCellTaint`

The forwarding scan threads the *concrete* `Held` env; the taint invariant must
be re-established against the **same** register/cell taint update that
`blockMaxTaintX` uses. We show the post-step envs `stepRegTaint`/`stepCellTaint`
keep `HeldTaintValid` for the env the scan computes. -/

/-- The register env after a write to the registers of `i` agrees with `R` off
those registers; a held entry whose register survived a `killWritten` is not
written, so its register taint is unchanged. -/
theorem stepRegTaint_apply_unwritten (R : RegTaint) (C : CellTaint)
    (i : JInstr 64) {r : String} (hr : r ∉ writtenRegs i) :
    stepRegTaint R C i r = R r := by
  simp [stepRegTaint, hr]

/-! ## 4. Per-step taint soundness of the forwarding scan

`forwardStep h i = (i', h')` with `HeldTaintValid h C R` implies, threading the
*same* register/cell taint envs `R`/`C`:
* `instrTaint R C i' = instrTaint R C i` — the rewritten instruction has the
  same output taint (the only rewrite, `loadMem → mov`, preserves it by the
  invariant);
* `HeldTaintValid h' (stepCellTaint R C i) (stepRegTaint R C i)` — the updated
  held env is valid in the post-step taint envs (so the scan continues).

This is the taint analogue of `StoreToLoadForward.forwardStep_sound`. -/

/-- Re-establishing the invariant after a forwarded/plain `loadMem`. -/
theorem heldTaintValid_loadForward {h : Held} {C : CellTaint} {R : RegTaint}
    (d base : String) (off : Int) (hv : HeldTaintValid h C R) :
    HeldTaintValid (((killWritten h (.loadMem d base off)).set base off d))
      (stepCellTaint R C (.loadMem d base off))
      (stepRegTaint R C (.loadMem d base off)) := by
  rw [stepCellTaint_loadMem]
  intro e he
  rw [Held.set, List.mem_append] at he
  -- The post-step register env: `d` is written (to the load's output taint,
  -- which is `C (base, off)`); everything else is `R`.
  have hwritten : writtenRegs (JInstr.loadMem d base off) = [d] := rfl
  rcases he with he | he
  · -- e was in the killed env: its register ≠ d, so its register taint survives.
    rw [Held.killCell, List.mem_filter] at he
    obtain ⟨hmem, hnin⟩ := mem_foldl_killReg _ _ he.1
    have hne : e.2 ≠ d := by rw [hwritten] at hnin; simpa using hnin
    have : stepRegTaint R C (.loadMem d base off) e.2 = R e.2 := by
      simp [stepRegTaint, hwritten, hne]
    rw [this]; exact hv e hmem
  · -- e is the new binding ((base,off), d): the cell carries C (base,off), and
    -- d's new register taint is instrTaint R C (loadMem …) = C (base,off).
    simp only [List.mem_singleton] at he
    subst he
    have : stepRegTaint R C (.loadMem d base off) d = C (base, off) := by
      simp [stepRegTaint, hwritten, instrTaint]
    rw [this]

/-- The interesting taint-preservation step: a forwarded `loadMem → mov`. -/
theorem instrTaint_forward_load {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) {d base : String} {off : Int} {r : String}
    (hf : h.find base off = some r) :
    instrTaint R C (.mov d (.reg r)) = instrTaint R C (.loadMem d base off) := by
  show operandTaint R (.reg r) = C (base, off)
  rw [heldTaintValid_find hv hf]; rfl

/-- **One forwarding step preserves output taint + the held-taint invariant.** -/
theorem forwardStep_taint_sound {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (i : JInstr 64) :
    instrTaint R C (forwardStep h i).1 = instrTaint R C i
      ∧ HeldTaintValid (forwardStep h i).2
          (stepCellTaint R C i) (stepRegTaint R C i) := by
  cases i with
  | loadMem d base off =>
    cases hf : h.find base off with
    | none =>
      have hstep : forwardStep h (.loadMem d base off)
          = (.loadMem d base off,
              (killWritten h (.loadMem d base off)).set base off d) := by
        simp [forwardStep, hf]
      rw [hstep]
      exact ⟨rfl, heldTaintValid_loadForward d base off hv⟩
    | some r =>
      have hfst : (forwardStep h (.loadMem d base off)).1 = .mov d (.reg r) := by
        simp only [forwardStep, hf]; split <;> rfl
      have hsnd : (forwardStep h (.loadMem d base off)).2
          = (killWritten h (.loadMem d base off)).set base off d := by
        simp only [forwardStep, hf]; split <;> rfl
      rw [hfst, hsnd]
      exact ⟨instrTaint_forward_load hv hf, heldTaintValid_loadForward d base off hv⟩
  | storeMem base off src =>
    cases src with
    | reg r =>
      have hstep : forwardStep h (.storeMem base off (.reg r))
          = (.storeMem base off (.reg r), (h.killCell base off).set base off r) := by
        simp [forwardStep]
      rw [hstep]
      refine ⟨rfl, ?_⟩
      intro e he
      rw [Held.set, List.mem_append] at he
      have hcell : stepCellTaint R C (.storeMem base off (.reg r))
          = fun y => if y = (base, off) then R r else C y := by
        funext y; simp [stepCellTaint, operandTaint]
      have hreg : stepRegTaint R C (.storeMem base off (.reg r)) = R := by
        funext y; simp [stepRegTaint, writtenRegs]
      rw [hcell, hreg]
      rcases he with he | he
      · -- killed-cell entry: cell ≠ (base,off), so cell-taint unchanged.
        simp only [Held.killCell, List.mem_filter] at he
        have hne : e.1 ≠ (base, off) := by simpa using he.2
        show (if e.1 = (base, off) then R r else C e.1) = R e.2
        rw [if_neg hne]
        exact hv e he.1.1
      · simp only [List.mem_singleton] at he
        subst he
        show (if (base, off) = (base, off) then R r else C (base, off)) = R r
        rw [if_pos rfl]
    | imm v =>
      have hstep : forwardStep h (.storeMem base off (.imm v))
          = (.storeMem base off (.imm v), h.killCell base off) := by
        simp [forwardStep]
      rw [hstep]
      refine ⟨rfl, ?_⟩
      intro e he
      rw [Held.killCell, List.mem_filter] at he
      have hne : e.1 ≠ (base, off) := by simpa using he.2
      have hcell : stepCellTaint R C (.storeMem base off (.imm v)) e.1 = C e.1 := by
        simp [stepCellTaint, hne]
      have hreg : stepRegTaint R C (.storeMem base off (.imm v)) e.2 = R e.2 := by
        simp [stepRegTaint, writtenRegs]
      rw [hcell, hreg]
      exact hv e he.1
  | storeMemIdx base idx scale src =>
    have hstep : forwardStep h (.storeMemIdx base idx scale src)
        = (.storeMemIdx base idx scale src, []) := by
      simp [forwardStep]
    rw [hstep]
    exact ⟨rfl, by intro e he; simp at he⟩
  | loadSym d sym =>
    -- `forwardStep` forgets every binding on `loadSym` (it re-aliases the memory
    -- bank), so the effect is unchanged (`rfl`) and `HeldTaintValid []` is vacuous —
    -- the `storeMemIdx` shape.
    have hstep : forwardStep h (.loadSym d sym) = (.loadSym d sym, []) := by
      simp [forwardStep]
    rw [hstep]
    exact ⟨rfl, by intro e he; simp at he⟩
  | mov d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.mov d s') (by intro b o v hc; nomatch hc)⟩
  | add d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.add d s') (by intro b o v hc; nomatch hc)⟩
  | sub d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.sub d s') (by intro b o v hc; nomatch hc)⟩
  | adc d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.adc d s') (by intro b o v hc; nomatch hc)⟩
  | sbb d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.sbb d s') (by intro b o v hc; nomatch hc)⟩
  | imul d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.imul d s') (by intro b o v hc; nomatch hc)⟩
  | neg d     => exact ⟨rfl, hv.killWrittenStep (JInstr.neg d) (by intro b o v hc; nomatch hc)⟩
  | setc d    => exact ⟨rfl, hv.killWrittenStep (JInstr.setc d) (by intro b o v hc; nomatch hc)⟩
  | and_ d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.and_ d s') (by intro b o v hc; nomatch hc)⟩
  | test a s' => exact ⟨rfl, hv.killWrittenStep (JInstr.test a s') (by intro b o v hc; nomatch hc)⟩
  | cmp a s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.cmp a s') (by intro b o v hc; nomatch hc)⟩
  | not_ d    => exact ⟨rfl, hv.killWrittenStep (JInstr.not_ d) (by intro b o v hc; nomatch hc)⟩
  | andn d a c => exact ⟨rfl, hv.killWrittenStep (JInstr.andn d a c) (by intro b o v hc; nomatch hc)⟩
  | rol d amt => exact ⟨rfl, hv.killWrittenStep (JInstr.rol d amt) (by intro b o v hc; nomatch hc)⟩
  | ror d amt => exact ⟨rfl, hv.killWrittenStep (JInstr.ror d amt) (by intro b o v hc; nomatch hc)⟩
  | rorx d src amt =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.rorx d src amt) (by intro b o v hc; nomatch hc)⟩
  | shlx d src c =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.shlx d src c) (by intro b o v hc; nomatch hc)⟩
  | shrx d src c =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.shrx d src c) (by intro b o v hc; nomatch hc)⟩
  | sarx d src c =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.sarx d src c) (by intro b o v hc; nomatch hc)⟩
  | movzx d sw src =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.movzx d sw src) (by intro b o v hc; nomatch hc)⟩
  | movsx d sw src =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.movsx d sw src) (by intro b o v hc; nomatch hc)⟩
  | lea d bs ix sc dsp =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.lea d bs ix sc dsp) (by intro b o v hc; nomatch hc)⟩
  | or_ d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.or_ d s') (by intro b o v hc; nomatch hc)⟩
  | xor_ d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.xor_ d s') (by intro b o v hc; nomatch hc)⟩
  | shl d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.shl d s') (by intro b o v hc; nomatch hc)⟩
  | shr d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.shr d s') (by intro b o v hc; nomatch hc)⟩
  | sar d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.sar d s') (by intro b o v hc; nomatch hc)⟩
  | cmove d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.cmove d s') (by intro b o v hc; nomatch hc)⟩
  | cmovne d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.cmovne d s') (by intro b o v hc; nomatch hc)⟩
  | cmovb d s'  => exact ⟨rfl, hv.killWrittenStep (JInstr.cmovb d s') (by intro b o v hc; nomatch hc)⟩
  | mulx dh dl a b => exact ⟨rfl, hv.killWrittenStep (JInstr.mulx dh dl a b) (by intro b o v hc; nomatch hc)⟩
  | mulxMem dh dl a base off => exact ⟨rfl, hv.killWrittenStep (JInstr.mulxMem dh dl a base off) (by intro b o v hc; nomatch hc)⟩
  | adcx d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.adcx d s') (by intro b o v hc; nomatch hc)⟩
  | adox d s' => exact ⟨rfl, hv.killWrittenStep (JInstr.adox d s') (by intro b o v hc; nomatch hc)⟩
  | loadMemIdx d base idx scale =>
      exact ⟨rfl, hv.killWrittenStep (JInstr.loadMemIdx d base idx scale) (by intro b o v hc; nomatch hc)⟩
  | inc _ | dec _ | clc | stc | xchg _ _ | imulri _ _ _ | mul _ _ _ | imulWide _ _ _
  | shld _ _ _ | shrd _ _ _ | rcl _ _ | rcr _ _ | cmovcc _ _ _ | setcc _ _
  | testN _ _ _ | bt _ _ | btr _ _ | bts _ _ =>
      exact ⟨rfl, hv.killWrittenStep _ (by intro b o v hc; nomatch hc)⟩

/-! ### The rewritten step threads the taint envs identically

For `blockMaxTaintX` to be preserved we also need the rewritten instruction
`(forwardStep h i).1` to **thread the register/cell taint envs the same way** as
`i`. The only rewrite, `loadMem d base off → mov d (.reg r)`, writes `d` to the
moved register's taint `R r` vs. the cell's taint `C (base, off)`; the invariant
`HeldTaintValid` makes those equal, so the threaded envs coincide. For every
other instruction the rewrite is the identity, so the envs are literally the
same. -/

/-- The forwarded step threads the **register** taint env identically. -/
theorem forwardStep_stepRegTaint_eq {h : Held} {C : CellTaint} {R : RegTaint}
    (hv : HeldTaintValid h C R) (i : JInstr 64) :
    stepRegTaint R C (forwardStep h i).1 = stepRegTaint R C i := by
  cases i with
  | loadMem d base off =>
    cases hf : h.find base off with
    | none => simp [forwardStep, hf]
    | some r =>
      have hfst : (forwardStep h (.loadMem d base off)).1 = .mov d (.reg r) := by
        simp only [forwardStep, hf]; split <;> rfl
      rw [hfst]
      funext y
      simp only [stepRegTaint, writtenRegs]
      by_cases hy : y = d
      · subst hy; simp only [List.mem_singleton]
        show operandTaint R (.reg r) = C (base, off)
        rw [heldTaintValid_find hv hf]; rfl
      · simp [hy]
  | storeMem base off src => cases src <;> simp [forwardStep]
  | storeMemIdx base idx scale src => simp [forwardStep]
  | _ => rfl

/-- The forwarded step threads the **cell** taint env identically. -/
theorem forwardStep_stepCellTaint_eq {h : Held} {C : CellTaint} {R : RegTaint}
    (i : JInstr 64) :
    stepCellTaint R C (forwardStep h i).1 = stepCellTaint R C i := by
  cases i with
  | loadMem d base off =>
    cases hf : h.find base off with
    | none => simp [forwardStep, hf]
    | some r =>
      have hfst : (forwardStep h (.loadMem d base off)).1 = .mov d (.reg r) := by
        simp only [forwardStep, hf]; split <;> rfl
      rw [hfst]; rfl
  | storeMem base off src => cases src <;> simp [forwardStep]
  | storeMemIdx base idx scale src => simp [forwardStep]
  | _ => rfl

/-! ## 5. The block-level theorem: forwarding preserves the taint summary

By induction on the block, threading the held env. Each step has the same output
taint (`forwardStep_taint_sound`) and threads the register/cell envs identically
(`forwardStep_stepRegTaint_eq`/`forwardStep_stepCellTaint_eq`), and the updated
held env stays valid, so the running join is preserved verbatim. -/

/-- **Forwarding preserves the block taint summary exactly**, from any valid held
env: the `List (JInstr 64)` analogue of `bubble_blockMaxTaint_eq`. -/
theorem forwardAux_blockMaxTaintX_eq :
    ∀ {h : Held} {C : CellTaint} {R : RegTaint} (_ : HeldTaintValid h C R)
      (block : List (JInstr 64)),
      blockMaxTaintX R C (forwardAux h block) = blockMaxTaintX R C block := by
  intro h C R hv block
  induction block generalizing h C R with
  | nil => rfl
  | cons i is ih =>
    rw [forwardAux_cons]
    obtain ⟨htaint, hvalid⟩ := forwardStep_taint_sound hv i
    simp only [blockMaxTaintX]
    rw [htaint, forwardStep_stepRegTaint_eq hv i, forwardStep_stepCellTaint_eq i]
    rw [ih hvalid]

/-- **The store-to-load forwarding pass preserves the block taint summary
exactly.** Started from the empty (vacuously valid) held env. The owned-x86
analogue of `peepCom_wellTainted` / `scheduleBlock_blockMaxTaint_eq`: the fourth,
#555 backend pass of the compositional-CT story preserves taint *exactly*. -/
theorem storeToLoadForward_blockMaxTaintX_eq (R : RegTaint) (C : CellTaint)
    (block : List (JInstr 64)) :
    blockMaxTaintX R C (storeToLoadForward block) = blockMaxTaintX R C block :=
  forwardAux_blockMaxTaintX_eq (h := []) (by intro e he; simp at he) block

/-! ## 6. The two shrinking peepholes of the driver pipeline

`optimizeX86Block` runs store-to-load forwarding, then the identity-mov drop,
then the flag-liveness-guarded MUL→MULX fusion. Forwarding preserves the summary
exactly (§5). The two shrinking stages delete an instruction each and are
therefore stated in the `⊑ₛ` (declassification) form: deleting an instruction can
only remove a contribution from the running join, never add one. In both cases
the deletion leaves the threaded register/cell taint envs unchanged, so the
tail's summary is computed against the same envs on both sides. -/

/-- Both branches of a join sit below a common upper bound. -/
theorem join_leq {x y z : SecretLevel} (hx : x ⊑ₛ z) (hy : y ⊑ₛ z) : (x ⊔ₛ y) ⊑ₛ z := by
  cases x <;> cases y <;> cases z <;> simp_all [SecretLevel.leq, SecretLevel.join]

/-- The join is monotone in its right argument. -/
theorem join_mono_right {x y y' : SecretLevel} (h : y' ⊑ₛ y) : (x ⊔ₛ y') ⊑ₛ (x ⊔ₛ y) :=
  join_leq (SecretLevel.leq_join_left _ _)
    (SecretLevel.leq_trans h (SecretLevel.leq_join_right _ _))

/-- A self-move `mov r (.reg r)` rebinds `r` to the taint it already carries, so
threading it leaves the register-taint env unchanged. -/
theorem stepRegTaint_idMov (R : RegTaint) (C : CellTaint) (r : String) :
    stepRegTaint R C (.mov r (.reg r)) = R := by
  funext y
  simp only [stepRegTaint, writtenRegs, List.mem_singleton, instrTaint, operandTaint]
  by_cases hy : y = r <;> simp [hy]

/-- **The identity-mov drop never raises the block taint summary.** Each deleted
`mov r (.reg r)` contributes `R r` to the running join and leaves the threaded
envs fixed, so removing it drops one join component and keeps the rest. -/
theorem dropIdMovs_blockMaxTaintX_le (block : List (JInstr 64)) :
    ∀ (R : RegTaint) (C : CellTaint),
      blockMaxTaintX R C (dropIdMovs block) ⊑ₛ blockMaxTaintX R C block := by
  induction block with
  | nil => intro R C; exact SecretLevel.leq_refl _
  | cons i is ih =>
    intro R C
    unfold dropIdMovs
    rw [List.filter_cons]
    by_cases h : isIdMov i = true
    · simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
      match i, h with
      | .mov d (.reg r), h =>
        simp only [isIdMov, beq_iff_eq] at h
        subst h
        have htail := ih R C
        unfold dropIdMovs at htail
        simp only [blockMaxTaintX, stepRegTaint_idMov]
        exact SecretLevel.leq_trans htail (SecretLevel.leq_join_right _ _)
    · rw [if_pos (by simp [h] : (! isIdMov i) = true)]
      have htail := ih (stepRegTaint R C i) (stepCellTaint R C i)
      unfold dropIdMovs at htail
      simp only [blockMaxTaintX]
      exact join_mono_right htail

/-- A store writes no register, so threading it leaves the register-taint env
unchanged. -/
theorem stepRegTaint_storeMem (R : RegTaint) (C : CellTaint) (base : String)
    (off : Int) (src : JOperand) :
    stepRegTaint R C (.storeMem base off src) = R := by
  funext y; simp [stepRegTaint, writtenRegs]

/-- Threading a register-to-memory store records the stored register's taint at the
stored cell and leaves every other cell alone. -/
theorem stepCellTaint_storeMem_reg (R : RegTaint) (C : CellTaint) (base : String)
    (off : Int) (r : String) :
    stepCellTaint R C (.storeMem base off (.reg r))
      = fun y => if y = (base, off) then R r else C y := by
  funext y; simp [stepCellTaint, operandTaint]

/-- **Deleting a reload of a cell that already carries the destination register's
taint never raises the summary.** The reload's output taint is the cell's, which is
the register's, so threading it rebinds `r` to the level it already has and leaves
the cell env alone: the tail is summarised against the same envs on both sides, and
the reload's own contribution is the only difference. -/
theorem blockMaxTaintX_dropReload_le {base : String} {off : Int} {r : String}
    (R : RegTaint) (C : CellTaint) (h : C (base, off) = R r) (t : List (JInstr 64)) :
    blockMaxTaintX R C t ⊑ₛ blockMaxTaintX R C (.loadMem r base off :: t) := by
  have hR : stepRegTaint R C (.loadMem r base off) = R := by
    funext y
    simp only [stepRegTaint, writtenRegs, List.mem_singleton, instrTaint]
    by_cases hy : y = r <;> simp [hy, h]
  simp only [blockMaxTaintX, stepCellTaint_loadMem, hR]
  exact SecretLevel.leq_join_right _ _

/-- One `consDrop` step never raises the summary: the only deletion is the reload of
a cell the preceding store has just filled from the reloaded register. -/
theorem consDrop_blockMaxTaintX_le (bases : List String) (i : JInstr 64)
    (k : List (JInstr 64)) (R : RegTaint) (C : CellTaint) :
    blockMaxTaintX R C (consDrop bases i k) ⊑ₛ blockMaxTaintX R C (i :: k) := by
  cases k with
  | nil => exact SecretLevel.leq_refl _
  | cons j rest =>
    rw [consDrop]
    split
    · rename_i hred
      obtain ⟨b0, o0, r0, hi, hj⟩ := eq_of_isRedundantReload hred
      subst hi; subst hj
      have hcell : stepCellTaint R C (.storeMem b0 o0 (.reg r0)) (b0, o0)
          = stepRegTaint R C (.storeMem b0 o0 (.reg r0)) r0 := by
        rw [stepRegTaint_storeMem, stepCellTaint_storeMem_reg]; simp
      simp only [blockMaxTaintX]
      exact join_mono_right (blockMaxTaintX_dropReload_le _ _ hcell rest)
    · exact SecretLevel.leq_refl _

/-- **Redundant spill-reload elimination never raises the block taint summary.** Each
deleted reload reads a cell the immediately preceding store filled from the reloaded
register, so it contributes a level the register already carries and leaves the
threaded envs fixed. -/
theorem dropReloads_blockMaxTaintX_le (bases : List String) (block : List (JInstr 64)) :
    ∀ (R : RegTaint) (C : CellTaint),
      blockMaxTaintX R C (dropReloads bases block) ⊑ₛ blockMaxTaintX R C block := by
  induction block with
  | nil => intro R C; exact SecretLevel.leq_refl _
  | cons i rest ih =>
    intro R C
    rw [dropReloads_cons]
    refine SecretLevel.leq_trans (consDrop_blockMaxTaintX_le bases i _ R C) ?_
    simp only [blockMaxTaintX]
    exact join_mono_right (ih _ _)

/-- **The guarded MUL→MULX fusion never raises the block taint summary.** Where
the guard fires, the dropped low `imul lo, b` writes `lo` the taint
`R lo ⊔ₛ R b`, and the surviving `mulx hi, lo, a, b` overwrites `lo` (and `hi`)
with `R a ⊔ₛ R b` reading only `a`, `b`, which the fusion's freshness keeps
distinct from `lo`. So both sides thread the same post-envs and the fused block's
summary is the original's minus the dropped `imul`'s contribution. -/
theorem fuseMulxGuarded_blockMaxTaintX_le (body : List (JInstr 64)) :
    ∀ (R : RegTaint) (C : CellTaint),
      blockMaxTaintX R C (fuseMulxGuarded body) ⊑ₛ blockMaxTaintX R C body := by
  fun_induction fuseMulxGuarded body with
  | case1 => intro R C; exact SecretLevel.leq_refl _
  | case2 i₁ i₂ rest lo b mHi mLo mA mB hWide hLow hcond ih =>
      intro R C
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcond
      obtain ⟨⟨⟨⟨hloeq, hbeq⟩, hane⟩, hbne⟩, _hdead⟩ := hcond
      have hi₁ : i₁ = .imul lo (.reg b) := isRedundantLowMul_some hLow
      have hi₂ : i₂ = .mulx mHi lo (.reg mA) (.reg b) := by
        rw [isWideningMul_some hWide, ← hloeq, ← hbeq]
      subst hi₁; subst hi₂
      -- Neither multiply writes a statically-known cell, so the cell env is fixed.
      have hcellImul : stepCellTaint R C (.imul lo (.reg b)) = C := rfl
      have hcellMulx : ∀ T : RegTaint,
          stepCellTaint T C (.mulx mHi lo (.reg mA) (.reg b)) = C := fun _ => rfl
      -- The register env after `imul` agrees with `R` on the multiplier's sources.
      have hR1 : stepRegTaint R C (.imul lo (.reg b))
          = fun y => if y = lo then (R lo ⊔ₛ R b) else R y := by
        funext y
        simp only [stepRegTaint, writtenRegs, List.mem_singleton, instrTaint, operandTaint]
      have hthread : stepRegTaint (stepRegTaint R C (.imul lo (.reg b))) C
            (.mulx mHi lo (.reg mA) (.reg b))
          = stepRegTaint R C (.mulx mHi lo (.reg mA) (.reg b)) := by
        funext y
        simp only [stepRegTaint, writtenRegs, List.mem_cons,
          List.not_mem_nil, or_false, instrTaint, operandTaint, if_neg hane, if_neg hbne]
        by_cases h1 : y = mHi
        · simp [h1]
        · by_cases h2 : y = lo <;> simp [h1, h2]
      have hhead : instrTaint (stepRegTaint R C (.imul lo (.reg b))) C
            (.mulx mHi lo (.reg mA) (.reg b))
          = instrTaint R C (.mulx mHi lo (.reg mA) (.reg b)) := by
        simp only [instrTaint, operandTaint, hR1, if_neg hane, if_neg hbne]
      simp only [blockMaxTaintX, hcellImul, hcellMulx, hhead, hthread]
      refine join_leq ?_ ?_
      · exact SecretLevel.leq_trans (SecretLevel.leq_join_left _ _)
          (SecretLevel.leq_join_right _ _)
      · exact SecretLevel.leq_trans (ih _ C)
          (SecretLevel.leq_trans (SecretLevel.leq_join_right _ _)
            (SecretLevel.leq_join_right _ _))
  | case3 i₁ i₂ rest lo b mHi mLo mA mB hWide hLow hcond ih =>
      intro R C
      simp only [blockMaxTaintX]
      exact join_mono_right (ih _ _)
  | case4 i₁ i₂ rest hmatch ih =>
      intro R C
      simp only [blockMaxTaintX]
      exact join_mono_right (ih _ _)
  | case5 i => intro R C; exact SecretLevel.leq_refl _

/-! ## 7. The driver form and the headline `≤` (declassification) statement

`optimizeX86Block` (`X86ComPipeline`) is `applyX86Pipeline defaultX86Pipeline`,
i.e. store-to-load forwarding, the identity-mov drop, redundant spill-reload
elimination, and the guarded MUL→MULX fusion. The first preserves the summary
exactly and the other three lower it, so the driver never **raises** it — the `≤`
(declassification) form shared with the egraph pass and the gated `#555` driver,
the compositional-CT guarantee at the owned-x86 layer. -/

/-- **The owned-x86 optimizer driver never raises the block taint summary.** The
declassification (`⊑ₛ`) form of the compositional-CT invariant at the owned-x86
backend layer, matching the egraph pass's `saturateCom_comMaxTaint_le` and the
#555 driver's gated nature. -/
theorem optimizeX86Block_blockMaxTaintX_le (R : RegTaint) (C : CellTaint)
    (block : List (JInstr 64)) :
    blockMaxTaintX R C
        (CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block block)
      ⊑ₛ blockMaxTaintX R C block := by
  show blockMaxTaintX R C
      (fuseMulxGuarded (dropReloads defaultSpillBases
        (dropIdMovs (storeToLoadForward block)))) ⊑ₛ _
  refine SecretLevel.leq_trans (fuseMulxGuarded_blockMaxTaintX_le _ R C) ?_
  refine SecretLevel.leq_trans (dropReloads_blockMaxTaintX_le _ _ R C) ?_
  refine SecretLevel.leq_trans (dropIdMovs_blockMaxTaintX_le _ R C) ?_
  rw [storeToLoadForward_blockMaxTaintX_eq]
  exact SecretLevel.leq_refl _

/-! ## 8. Self-contained validation

A two-instruction frame round-trip: store register `r` to cell `(fp, 0)`, then
reload that cell into `d`. With `r` marked `sec` the store carries `sec` into the
cell; the reload would read it back as `sec`. After forwarding, the reload
becomes `mov d (.reg r)`, reading `r` directly — same `sec` taint. The block
summary is `sec` and is preserved by the pass. -/

-- @bench-only: the `List (JInstr _)` block below is a fixture exercising this
-- secret-type analysis; this module emits no deployed `.s` artifact.
/-- Demo block: store `r` to `(fp, 0)`, then load `(fp, 0)` into `d`. -/
def demoFrameBlock : List (JInstr 64) :=
  [ .storeMem "fp" 0 (.reg "r"), .loadMem "d" "fp" 0 ]

/-- Register taint marking `r` secret, everything else public. -/
def demoRegTaint : RegTaint := fun x => if x = "r" then .sec else .pub

/-- Cell taint: all cells public initially. -/
def demoCellTaint : CellTaint := fun _ => .pub

/-- The demo block's overall taint is `sec` (the secret `r` is stored, then the
load reads that cell). -/
example : blockMaxTaintX demoRegTaint demoCellTaint demoFrameBlock = .sec := by
  decide

/-- **Forwarding preserves the demo block's taint summary exactly** — the reload
is rewritten to a register move reading the same secret `r`. Via
`storeToLoadForward_blockMaxTaintX_eq`. -/
example :
    blockMaxTaintX demoRegTaint demoCellTaint (storeToLoadForward demoFrameBlock)
      = blockMaxTaintX demoRegTaint demoCellTaint demoFrameBlock :=
  storeToLoadForward_blockMaxTaintX_eq demoRegTaint demoCellTaint demoFrameBlock

/-- **The driver never raises the demo block's taint summary.** Via
`optimizeX86Block_blockMaxTaintX_le`. -/
example :
    blockMaxTaintX demoRegTaint demoCellTaint
        (CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline.optimizeX86Block
          demoFrameBlock)
      ⊑ₛ blockMaxTaintX demoRegTaint demoCellTaint demoFrameBlock :=
  optimizeX86Block_blockMaxTaintX_le demoRegTaint demoCellTaint demoFrameBlock
