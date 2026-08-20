/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86OptPipelineComposed
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem

/-!
# `lsemStraight` of an `Lcmd` against `runBlock` of its gathered `JInstr` block

The emit path builds `Lprog`/`Lcmd = List Linstr` and renders it; the verified
x86 optimizer runs on `List (JInstr 64)`. `GatherImmForms.gatherJBlock6` maps the
first onto the second. This module states and proves that the map preserves
meaning on a named fragment, so an optimizer certificate about the gathered block
is a statement about the source `Lcmd`.

## The statement

`gatherJBlock6_lsem_agree`: for a body whose every instruction satisfies
`tiedInstr`, the gather succeeds, `lsemStraight` of the body runs to completion
from any `Lstate 64` corresponding to a `JState 64`, and the resulting states
again correspond (`LJCorr`, register-file equality). `optimized_lsem_agree` is the
same statement with `X86ComPipeline.optimizeX86Block` applied to the gathered
block, obtained from `optimizeX86Block_runBlock`.

## The fragment (`tiedInstr`)

* two-address ALU `Lopn [.reg d] m [s0, s1]` with `m` one of `ADD:64`, `SUB:64`,
  `MUL:64`, `AND:64`, `OR:64`, `XOR:64`, both operands a register or an
  immediate, and `s0 = .reg d ∨ s1 ≠ .reg d`;
* register/immediate `Lopn [.reg d] "MOV:64" [src]`.

The side condition on the two-source arm is a real one. When `s0 ≠ .reg d` the
gather emits the SSA split `[mov d s0; OP d s1]`, and the second instruction
reads `s1` *after* the materialising move; if `s1 = .reg d` the move has already
overwritten it, so the split computes `f s0 s0` where `lsemStraight` computes
`f s0 d`. `tiedInstr` rejects that shape rather than proving a false equation.

## What the tie does not cover, and why

* **Flags.** `Lstate` has no flag component and `applyOpn` has no `CMP`/`TEST`
  arm, so a compare has no `lsem` denotation at all: `lsemStep` returns `none` on
  `CMP:64`. The tie is stated over the flag-free fragment because that is the
  fragment on which the `Lcmd` side has a denotation, not as a convenience.
  `ADC:64`/`SBB:64`/`ADCX:64`/`ADOX:64`/`SETC` are outside for the same reason.
  Giving them one means adding flags to `Lstate` and flag arms to `applyOpn`,
  which changes the semantics that the whole `VIR/JasminLsem*` faithfulness tree
  is stated against. The designated-register carry scheme in
  `RunBlockLsemAgree` (`JLstateCorrF`) is the flag axis worked out over the
  richer `LstateM` state, in the opposite direction.
* **Shifts.** `applyOpn "SHL" [a, b] = a <<< b.toNat` is unmasked, while
  `x86_SHL` masks the count (`shiftCount`), so the two disagree for counts
  `≥ 64`. The count-in-tag forms `SHL:<n>:64` / `SHR:<n>:64` / `SAR:<n>:64` that
  the exporter actually emits have no `applyOpn` arm at all.
* **Memory.** `applyOpn` has no `LOAD`/`STORE` arm, so the memory ops
  (`LOAD`/`STORE`/`LOADIDX`/`STOREIDX`) have no `lsem` denotation.
* **Spill slots.** A `MOVQ qsave.X, X` is an `lvm` register copy for `lsem` and
  an `off(%rsp)` store for the gather (`SpillSlotEncode.lowerCov5`). Tying them
  needs a slot-name-to-offset correspondence carrying `spillQsaveOff`
  injectivity; `tiedInstr` excludes `MOVQ`.
* **Control flow.** `lsemStep` returns `none` on `Lgoto`/`Lcond`/`Lcall`/`Lret`
  and `JInstr` is straight-line by construction.

## Why this is a forward simulation and not a `ParamTransfer` triple transfer

`Transfer.Param.RComp Rα c c'` relates two computations *in one monad* `M` at one
`PostShape`; `triple_transfer` moves a `Std.Do.Triple` along such a witness. The
two sides here are `StateM (JState 64)` and `StateT (Lstate 64) Option`, at
different `PostShape`s, so `RComp` cannot be applied to the pair. A Tier-1
`@[spec]` morphism lemma `wp⟦θ x⟧ Q = wp⟦x⟧ (θ# Q)` would need a monad morphism
`θ`, and none exists: `lsemStraight` advances `lpc` once per `Linstr` while the
gather is one-to-many (`ADD:64` with `s0 ≠ .reg d` lowers to two `JInstr`s), so no
`θ` commutes with both semantics. `LJCorr` is `lpc`-oblivious for exactly that
reason. The lens used here is therefore the machine-Hoare / forward-simulation
one already carrying `RunBlockLsemAgree.JLstateCorr`. `lsem_of_runBlock_property`
is the seam to the `Std.Do` kernel: it consumes exactly the register-file
postcondition that `Ascent.RunBlockMvcgen.runBlockM_triple_iff` produces from an
`mvcgen`-proved triple over `runBlockM`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (lowerCov6 lowerCov6L gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode (lowerCov5)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody (lowerLinstrExtCov4)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
  (lowerLinstrExtCov3 lowerAluJ2InPlace)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage (lowerLinstrExtCov)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar (lowerLinstrExtCov2)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
  (lowerLinstrExt2 lowerAluJ lowerJOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
  (optimizeX86Block optimizeX86Block_runBlock)

/-! ## 1. The state correspondence

`Lstate 64` carries `lvm` (registers), `lmem` (compile-time-offset memory) and
`lpc`; `JState 64` carries `regs`, `mem` and `flags`. On the tied fragment no
instruction touches memory on either side and neither side's memory is read, so
the correspondence is register-file equality. It does not mention `lpc` (the
`JState` side has no program counter) or `flags` (the `Lstate` side has none). -/

/-- The `Lstate`-`JState` correspondence used by the tie: the two register files
    agree pointwise at width 64. -/
def LJCorr (ls : Lstate 64) (s : JState 64) : Prop := ∀ r : String, ls.lvm r = s.regs r

/-- The correspondence is preserved by a matched register write. -/
theorem LJCorr_setReg {ls : Lstate 64} {s : JState 64} (h : LJCorr ls s)
    (d : String) (v : BitVec 64) : LJCorr ((ls.setReg d v).nextPc) (s.setReg d v) := by
  intro r
  show (if r = d then v else ls.lvm r) = (if r = d then v else s.regs r)
  by_cases hr : r = d
  · simp [hr]
  · simp [hr, h r]

/-! ## 2. The tied fragment -/

/-- A register or immediate operand: the operand shapes whose `evalOperand`
    reads only `lvm` and whose `lowerJOperand` image is the matching
    `JOperand`. -/
def tiedOperand : LOperand → Bool
  | .reg _ => true
  | .imm _ => true
  | _ => false

/-- Whether an operand is the register `d`. -/
def isRegNamed (d : String) : LOperand → Bool
  | .reg r => r == d
  | _ => false

/-- The width-tagged two-address ALU mnemonics of the tie: the six whose base
    opcode `applyOpn` models with the same word function the matching `JInstr`
    constructor writes. -/
def tiedBinMnem (m : String) : Bool :=
  m == "ADD:64" || m == "SUB:64" || m == "MUL:64" || m == "AND:64" || m == "OR:64" ||
    m == "XOR:64"

/-- The tied instruction shapes. See the module header for what is excluded and
    why. -/
def tiedInstrR : LinstrR → Bool
  | .Lopn [.reg d] m [s0, s1] =>
      tiedBinMnem m && tiedOperand s0 && tiedOperand s1 &&
        (isRegNamed d s0 || !isRegNamed d s1)
  | .Lopn [.reg _] "MOV:64" [src] => tiedOperand src
  | _ => false

/-- The tied predicate on a positioned `Linstr`. -/
def tiedInstr (i : Linstr) : Bool := tiedInstrR i.li_i

/-! ## 3. Operand agreement -/

/-- Under the correspondence a tied operand evaluates to the same word on both
    sides. -/
theorem evalOperand_agree {ls : Lstate 64} {s : JState 64} (h : LJCorr ls s)
    (op : LOperand) (hop : tiedOperand op = true) :
    evalOperand ls op = (lowerJOperand op).eval s := by
  cases op with
  | reg r => exact h r
  | imm v => rfl
  | arr _ _ => simp [tiedOperand] at hop
  | arrIdx _ _ _ => simp [tiedOperand] at hop

/-- A tied operand that is not the register `d` reads the same after a write to
    `d`. -/
theorem eval_stable {s : JState 64} (d : String) (v : BitVec 64) (op : LOperand)
    (hop : tiedOperand op = true) (hne : isRegNamed d op = false) :
    (lowerJOperand op).eval (s.setReg d v) = (lowerJOperand op).eval s := by
  cases op with
  | reg r =>
    have : ¬ (r = d) := by simpa [isRegNamed] using hne
    simp [lowerJOperand, JOperand.eval, JState.get, JState.setReg, this]
  | imm v => rfl
  | arr _ _ => simp [tiedOperand] at hop
  | arrIdx _ _ _ => simp [tiedOperand] at hop

/-! ## 4. The gather's shape on the tied mnemonics

`lower_bin` and `lower_un` walk the `lowerCov6` dispatch chain (`lowerCov5` →
`lowerLinstrExtCov4` → `lowerLinstrExtCov3` → `lowerLinstrExtCov2` →
`lowerLinstrExtCov` → `lowerLinstrExt2`) for a *variable* mnemonic, taking as
hypotheses the literal disequalities the earlier head patterns need (including the
`SAR:<n>` literals `lowerLinstrExtCov2` intercepts) and the `lowerAluJ` table
lookup.
The `stripWidthTag` computation on each concrete mnemonic is a closed fact and is
supplied by the `strip_*` lemmas; it does not reduce inside `rfl`. -/

/-! The tag strips of the tied mnemonics. -/

theorem strip_ADD : stripWidthTag "ADD:64" = "ADD" := by decide +kernel
theorem strip_SUB : stripWidthTag "SUB:64" = "SUB" := by decide +kernel
theorem strip_MUL : stripWidthTag "MUL:64" = "MUL" := by decide +kernel
theorem strip_AND : stripWidthTag "AND:64" = "AND" := by decide +kernel
theorem strip_OR : stripWidthTag "OR:64" = "OR" := by decide +kernel
theorem strip_XOR : stripWidthTag "XOR:64" = "XOR" := by decide +kernel
theorem strip_MOV : stripWidthTag "MOV:64" = "MOV" := by decide +kernel

/-- The gather's image of a two-source ALU `Lopn` whose tag-stripped mnemonic is
    in the `lowerAluJ` table: the in-place op when the first source is the
    destination, the SSA split otherwise. -/
theorem lower_bin (frame spillW : Nat) (d opn : String) (s0 s1 : LOperand) (i : JInstr 64)
    (h1 : opn ≠ "MULXHI:64") (h2 : opn ≠ "STORE") (h3 : opn ≠ "STOREIDX")
    (halu : lowerAluJ d (stripWidthTag opn) (lowerJOperand s1) = some i) :
    lowerCov6 frame spillW (.Lopn [.reg d] opn [s0, s1])
      = some (if lowerJOperand s0 = JOperand.reg d then [i]
              else [JInstr.mov d (lowerJOperand s0), i]) := by
  unfold lowerCov6
  split <;> simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerAluJ2InPlace]

/-- The gather's image of a single-source `Lopn` over a register or immediate
    whose tag-stripped mnemonic is in the `lowerAluJ` table. -/
theorem lower_un (frame spillW : Nat) (d opn : String) (src : LOperand) (i : JInstr 64)
    (hsrc : tiedOperand src = true) (h1 : opn ≠ "MOVQ")
    (hs1 : opn ≠ "SAR:63:64") (hs2 : opn ≠ "SAR:23:64") (hs3 : opn ≠ "SAR:31")
    (hsh : CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended.parseShiftMnem opn = none)
    (hsar : CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar.sarCountOf opn = none)
    (halu : lowerAluJ d (stripWidthTag opn) (lowerJOperand src) = some i) :
    lowerCov6 frame spillW (.Lopn [.reg d] opn [src]) = some [i] := by
  cases src with
  | reg r =>
    unfold lowerCov6
    split <;>
      simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerLinstrExtCov2,
        lowerLinstrExtCov, lowerLinstrExt2]
  | imm v =>
    unfold lowerCov6
    split <;>
      simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerLinstrExtCov2,
        lowerLinstrExtCov, lowerLinstrExt2]
  | arr _ _ => simp [tiedOperand] at hsrc
  | arrIdx _ _ _ => simp [tiedOperand] at hsrc

theorem pshift_MOV :
    CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended.parseShiftMnem "MOV:64"
      = none := by decide +kernel

/-! ## 5. Per-instruction agreement -/

/-- The correspondence after a matched register write, stated against a `JState`
    given only by its register file. -/
theorem LJCorr_write {ls : Lstate 64} {s : JState 64} (h : LJCorr ls s)
    (d : String) (v : BitVec 64) (t : JState 64)
    (ht : ∀ r, t.regs r = if r = d then v else s.regs r) :
    LJCorr ((ls.setReg d v).nextPc) t := by
  intro r
  show (if r = d then v else ls.lvm r) = t.regs r
  rw [ht r]
  by_cases hr : r = d
  · simp [hr]
  · simp [hr, h r]

/-- **One tied two-source ALU instruction.** The gather succeeds, the `lsem` step
    succeeds, and the two results correspond. `f` is the shared word function:
    `applyOpn` computes it on the `Lcmd` side (`happly`) and the `JInstr`
    constructor writes it on the machine side (`hev`). -/
theorem bin_case (frame spillW : Nat) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s)
    (d opn : String) (s0 s1 : LOperand) (mk : String → JOperand → JInstr 64)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hne1 : opn ≠ "MULXHI:64") (hne2 : opn ≠ "STORE") (hne3 : opn ≠ "STOREIDX")
    (halu : ∀ op : JOperand, lowerAluJ d (stripWidthTag opn) op = some (mk d op))
    (h0 : tiedOperand s0 = true) (h1 : tiedOperand s1 = true)
    (hguard : isRegNamed d s0 = true ∨ isRegNamed d s1 = false)
    (happly : ∀ a b : BitVec 64, applyOpn (stripWidthTag opn) [a, b] = some (f a b))
    (hev : ∀ (t : JState 64) (src : JOperand) (r : String),
      (evalInstr t (mk d src)).regs r = if r = d then f (t.regs d) (src.eval t) else t.regs r) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] opn [s0, s1]) = some g ∧
      lsemStep (.Lopn [.reg d] opn [s0, s1]) ls = some ls' ∧ LJCorr ls' (runBlock s g) := by
  have hlow := lower_bin frame spillW d opn s0 s1 (mk d (lowerJOperand s1))
    hne1 hne2 hne3 (halu (lowerJOperand s1))
  have hstep : lsemStep (.Lopn [.reg d] opn [s0, s1]) ls
      = some ((ls.setReg d (f (evalOperand ls s0) (evalOperand ls s1))).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, happly]
  refine ⟨_, _, hlow, hstep, ?_⟩
  rw [evalOperand_agree hc s0 h0, evalOperand_agree hc s1 h1]
  by_cases hd : lowerJOperand s0 = JOperand.reg d
  · rw [if_pos hd]
    refine LJCorr_write hc d _ _ (fun r => ?_)
    show (evalInstr s (mk d (lowerJOperand s1))).regs r = _
    rw [hev s (lowerJOperand s1) r, hd]
    rfl
  · rw [if_neg hd]
    have hs1 : isRegNamed d s1 = false := by
      rcases hguard with hg | hg
      · exact absurd (by cases s0 with
          | reg r => simp only [isRegNamed, beq_iff_eq] at hg; simp [lowerJOperand, hg]
          | imm v => simp [isRegNamed] at hg
          | arr _ _ => simp [isRegNamed] at hg
          | arrIdx _ _ _ => simp [isRegNamed] at hg) hd
      · exact hg
    refine LJCorr_write hc d _ _ (fun r => ?_)
    show (evalInstr (evalInstr s (JInstr.mov d (lowerJOperand s0))) (mk d (lowerJOperand s1))).regs r
      = _
    rw [hev _ (lowerJOperand s1) r]
    have hmov : evalInstr s (JInstr.mov d (lowerJOperand s0))
        = s.setReg d ((lowerJOperand s0).eval s) := rfl
    rw [hmov, eval_stable d _ s1 h1 hs1]
    have hdd : (s.setReg d ((lowerJOperand s0).eval s)).regs d = (lowerJOperand s0).eval s := by
      simp [JState.setReg]
    rw [hdd]
    by_cases hr : r = d
    · simp [hr]
    · simp [hr, JState.setReg]

/-- **One tied `MOV:64`.** The gather emits a single `mov`; both sides write the
    evaluated source to the destination. -/
theorem mov_case (frame spillW : Nat) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s)
    (d : String) (src : LOperand) (hsrc : tiedOperand src = true) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] "MOV:64" [src]) = some g ∧
      lsemStep (.Lopn [.reg d] "MOV:64" [src]) ls = some ls' ∧ LJCorr ls' (runBlock s g) := by
  have halu : lowerAluJ d (stripWidthTag "MOV:64") (lowerJOperand src)
      = some (JInstr.mov d (lowerJOperand src)) := by rw [strip_MOV]; rfl
  have hlow := lower_un frame spillW d "MOV:64" src (JInstr.mov d (lowerJOperand src))
    hsrc (by decide) (by decide) (by decide) (by decide) pshift_MOV
    (by rfl) halu
  have hstep : lsemStep (.Lopn [.reg d] "MOV:64" [src]) ls
      = some ((ls.setReg d (evalOperand ls src)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, strip_MOV, applyOpn]
  refine ⟨_, _, hlow, hstep, ?_⟩
  rw [evalOperand_agree hc src hsrc]
  refine LJCorr_write hc d _ _ (fun r => ?_)
  show (evalInstr s (JInstr.mov d (lowerJOperand src))).regs r = _
  by_cases hr : r = d
  · simp [hr, evalInstr, x86_MOV, JState.setReg]
  · simp [hr, evalInstr, x86_MOV, JState.setReg]

/-! ## 6. The dispatch over the tied fragment -/

theorem instr_agree (frame spillW : Nat) (i : Linstr) (hi : tiedInstr i = true)
    {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s) :
    ∃ g ls', lowerCov6L frame spillW i = some g ∧
      lsemStep i.li_i ls = some ls' ∧ LJCorr ls' (runBlock s g) := by
  obtain ⟨p, ir⟩ := i
  simp only [tiedInstr, tiedInstrR] at hi
  split at hi
  · rename_i d m s0 s1
    simp only [Bool.and_eq_true] at hi
    obtain ⟨⟨⟨hm, h0⟩, h1⟩, hg⟩ := hi
    have hguard : isRegNamed d s0 = true ∨ isRegNamed d s1 = false := by
      simpa [Bool.or_eq_true, Bool.not_eq_true] using hg
    simp only [tiedBinMnem, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.add (· + ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_ADD]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_ADD]; rfl) (fun _ _ _ => rfl)
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.sub (· - ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_SUB]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_SUB]; rfl) (fun _ _ _ => rfl)
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.imul (· * ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_MUL]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_MUL]; rfl) (fun _ _ _ => rfl)
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.and_ (· &&& ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_AND]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_AND]; rfl) (fun _ _ _ => rfl)
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.or_ (· ||| ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_OR]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_OR]; rfl) (fun _ _ _ => rfl)
    · exact bin_case frame spillW hc d _ s0 s1 JInstr.xor_ (· ^^^ ·)
        (by decide) (by decide) (by decide) (fun op => by rw [strip_XOR]; rfl)
        h0 h1 hguard (fun a b => by rw [strip_XOR]; rfl) (fun _ _ _ => rfl)
  · rename_i d src
    exact mov_case frame spillW hc d src hi
  · simp at hi

/-! ## 7. The block lift -/

/-- `runBlock` distributes over concatenation. -/
theorem runBlock_append (s : JState 64) (b1 b2 : List (JInstr 64)) :
    runBlock s (b1 ++ b2) = runBlock (runBlock s b1) b2 := by
  induction b1 generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons, ih]

/-- The per-instruction lowering flattened over a whole body: the gather without
    the `Lret` filter and with the frame parameters supplied. -/
def gatherWith (frame spillW : Nat) (body : List Linstr) : Option (List (JInstr 64)) :=
  (body.mapM (lowerCov6L frame spillW)).map List.flatten

/-- **Block agreement.** A body whose every instruction is tied gathers, runs to
    completion under `lsemStraight`, and the resulting `Lstate` corresponds to the
    `runBlock` of the gathered block. -/
theorem block_agree (frame spillW : Nat) (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstr i = true) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s) :
    ∃ g ls', gatherWith frame spillW body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧ LJCorr ls' (runBlock s g) := by
  induction body generalizing ls s with
  | nil => exact ⟨[], ls, rfl, rfl, hc⟩
  | cons i is ih =>
    obtain ⟨g1, ls1, hg1, hstep1, hc1⟩ :=
      instr_agree frame spillW i (hb i (List.mem_cons_self ..)) hc
    obtain ⟨g2, ls2, hg2, hstep2, hc2⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) hc1
    refine ⟨g1 ++ g2, ls2, ?_, ?_, ?_⟩
    · unfold gatherWith at hg2 ⊢
      cases hgm : is.mapM (lowerCov6L frame spillW) with
      | none => rw [hgm] at hg2; simp at hg2
      | some gs =>
        rw [hgm] at hg2
        simp only [Option.map_some, Option.some.injEq] at hg2
        simp [List.mapM_cons, hg1, hgm, ← hg2]
    · simp only [List.map_cons, lsemStraight_cons, hstep1, hstep2]
    · rw [runBlock_append]; exact hc2

/-! ## 8. The headline: the gather used by the emit path -/

/-- A tied instruction is not the `Lret` terminator, so the gather's `Lret`
    filter is the identity on a tied body. -/
theorem filter_isLret_id (body : List Linstr) (hb : ∀ i ∈ body, tiedInstr i = true) :
    body.filter (fun i => !isLret i) = body := by
  refine List.filter_eq_self.2 (fun i hi => ?_)
  have := hb i hi
  obtain ⟨p, ir⟩ := i
  cases ir <;> simp_all [isLret, tiedInstr, tiedInstrR]

/-- **The gather preserves meaning.** For a body whose every instruction is tied,
    `GatherImmForms.gatherJBlock6` succeeds, `lsemStraight` of the body runs to
    completion from any corresponding `Lstate`, and the two final states again
    correspond on the register file. This is the statement that makes an
    optimizer certificate about the gathered `JInstr` block a statement about the
    source `Lcmd`. -/
theorem gatherJBlock6_lsem_agree (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstr i = true) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧ LJCorr ls' (runBlock s g) := by
  obtain ⟨g, ls', hg, hstep, hc'⟩ :=
    block_agree
      (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.frameSize body)
      (if CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.bodyIsU64 body then 64
        else 32) body hb hc
  refine ⟨g, ls', ?_, hstep, hc'⟩
  unfold gatherJBlock6
  rw [filter_isLret_id body hb]
  exact hg

/-- **The optimizer runs on the emit path with a certificate.** Composing the tie
    with `X86ComPipeline.optimizeX86Block_runBlock`: the optimized gathered block
    lands in the same register file the source `Lcmd`'s `lsemStraight` reaches. -/
theorem gatherJBlock6_optimized_lsem_agree (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstr i = true) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧
      LJCorr ls' (runBlock s (optimizeX86Block g)) := by
  obtain ⟨g, ls', hg, hstep, hc'⟩ := gatherJBlock6_lsem_agree body hb hc
  exact ⟨g, ls', hg, hstep, by rw [optimizeX86Block_runBlock]; exact hc'⟩

/-- **The validated optimizer pipeline runs on the emit path.** Composing the tie
    with `X86OptPipelineComposed.defaultValidatedPipeline_sound`: the block that the
    graph-coloring register allocator, mem2reg and spill-slot-reuse pipeline
    produces from the gathered body lands in the same register file the source
    `Lcmd`'s `lsemStraight` reaches. The pipeline soundness is an unconditional
    `runBlock`-equality, so the tie carries over with `tiedInstr` on the body as its
    only side condition. -/
theorem gatherJBlock6_composeValidated_lsem_agree (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstr i = true) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s)
    (prot : List (String × Int))
    (pinned : CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter.GpAlloc)
    (frameBase : Int) (spillBase : String) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧
      LJCorr ls' (runBlock s
        (X86OptPipelineComposed.composeValidated
          (X86OptPipelineComposed.defaultValidatedPipeline prot pinned frameBase spillBase) g)) := by
  obtain ⟨g, ls', hg, hstep, hc'⟩ := gatherJBlock6_lsem_agree body hb hc
  exact ⟨g, ls', hg, hstep, by
    rw [X86OptPipelineComposed.defaultValidatedPipeline_sound]; exact hc'⟩

/-- Every instruction of the body is tied. The decidable entry point for
    measuring how much of a real emitted body the tie covers. -/
def tiedBody (body : List Linstr) : Bool := body.all tiedInstr

/-- `tiedBody` unfolded to the membership form the theorems take. -/
theorem tiedBody_mem {body : List Linstr} (h : tiedBody body = true) :
    ∀ i ∈ body, tiedInstr i = true := by
  intro i hi
  exact (List.all_eq_true.1 h) i hi

/-- **Property transport.** Any property of the gathered block's final register
    file holds of the register bank the source `Lcmd` reaches. This is the shape
    a machine-Hoare postcondition takes after
    `Ascent.RunBlockMvcgen.runBlockM_triple_iff` collapses a `Std.Do` triple over
    `runBlockM` into a `runBlock` statement, so an `mvcgen`-proved property of the
    gathered block is a property of the source `Lcmd`. -/
theorem lsem_of_runBlock_property (body : List Linstr) (hb : tiedBody body = true)
    (g : List (JInstr 64)) (hg : gatherJBlock6 body = some g)
    (Q : (String → BitVec 64) → Prop) {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s)
    (hQ : Q (runBlock s g).regs) :
    ∃ ls', lsemStraight (body.map (·.li_i)) ls = some ls' ∧ Q ls'.lvm := by
  obtain ⟨g', ls', hg', hstep, hc'⟩ := gatherJBlock6_lsem_agree body (tiedBody_mem hb) hc
  rw [hg] at hg'
  cases Option.some.inj hg'
  exact ⟨ls', hstep, by rwa [funext hc']⟩

/-! ## 9. A worked body in the exporter's shape

The four-instruction body `demoBody` is in the shape `Com.toLprogPhysAbi` emits
for a destructive two-address compute core: a `MOV:64` materialise, two in-place
two-source ops (`s0 = .reg d`), and one SSA split (`s0 ≠ .reg d`, `s1 ≠ .reg d`). -/

/-- A tied body: `RAX := RDI`, `RAX ^= RSI`, `RCX := RAX & RDX`, `RAX += RCX`. -/
def demoBody : List Linstr :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .reg "RSI"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "AND:64" [.reg "RAX", .reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .reg "RCX"]⟩ ]

theorem demoBody_tied : tiedBody demoBody = true := by decide

/-- The tie instantiated on `demoBody`. -/
theorem demoBody_agree {ls : Lstate 64} {s : JState 64} (hc : LJCorr ls s) :
    ∃ g ls', gatherJBlock6 demoBody = some g ∧
      lsemStraight (demoBody.map (·.li_i)) ls = some ls' ∧
      LJCorr ls' (runBlock s (optimizeX86Block g)) :=
  gatherJBlock6_optimized_lsem_agree demoBody (tiedBody_mem demoBody_tied) hc

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
