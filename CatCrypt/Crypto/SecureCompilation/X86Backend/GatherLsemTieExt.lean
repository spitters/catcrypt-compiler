/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassSetccValueTie

/-!
# The gather tie on the materialised compare, immediate shifts and indexed memory

`GatherLsemTie.gatherJBlock6_lsem_agree` relates `lsemStraight` of an `Lcmd` body
to `runBlock` of its `GatherImmForms.gatherJBlock6` block on the register-only
fragment `tiedInstr` (two-address ALU and `MOV:64`). This module widens the
fragment to `tiedInstrX`, adding

* the materialised comparison `SET<cc>:64 d, a, s1`, which `lsem` denotes as one
  fused word op (`applyOpn`'s `SET<cc>` arm, the dialect's `cmpBit`) and the gather
  lowers to the three-instruction `cmp a s1; mov d 0; setcc c d` over `JState`
  flags; the value agreement is `FlagClassSetccValueTie.flagClass_setcc_value_tie`;
* the count-in-mnemonic immediate shifts `SHL:<n>[:64]`, `SHR:<n>[:64]` and the
  tagged `SAR:<n>:64` at counts below `64`, over a register or immediate source,
  in the four block shapes the gather produces (`shiftBlockReg`, `movShiftBlock`);
* the register-indexed memory ops `LOADIDX [base[idx*scale]]` and
  `STOREIDX [base[idx*scale], val]`, whose two memories `Lstate.lmem` and
  `JState.mem` are related pointwise (`MemRel`).

The state correspondence `LJCorrM` is `GatherLsemTie.LJCorr` (register-file
equality) together with `MemRel`. `JState.flags` and `Lstate.lpc` are not
mentioned: the `Lstate` has no flags and the `JState` no program counter.

## The parse hypothesis

`lsemStep` evaluates a count-in-mnemonic shift through
`JasminLprogExport.parseImmShiftMnem`, which is written over `String.splitOn` and
reduces neither symbolically nor on a closed mnemonic, while the gather reads the
count through the list-level `LoweringExtended.parseShiftMnem` and
`LoweringCoverageCmovSar.sarCountOf`, which do reduce. `ShiftParseAgrees m` states
that the two readings of a mnemonic agree; the widened tie takes it per body
instruction (`BodyParseAgrees`). Once `parseImmShiftMnem` is defined over the
list-level split, `ShiftParseAgrees` is a lemma and the hypothesis is discharged
generically; `tiedInstr_parseAgrees` already discharges it on the register-only
fragment, where no instruction is a shift.

## Not covered

* Loop back-edges. `lsemStep` returns `none` on `Lcond`/`Lgoto`/`Llabel` targets
  and `runBlock` is straight-line; a tie for a loop body needs the labelled
  program semantics (`find_label`/`eval_jump`, as `FrontWhileLsem` models the
  front's loop) on the `Lcmd` side and `runXLoop` on the machine side, related
  once per iteration through this straight-line tie.
* `ROR:<n>`/`ROL:<n>`: the gather chain under `GatherImmForms.lowerCov6` has no
  arm for them (`lowerAluJ` and `parseShiftMnem` decline the mnemonic), so the
  gather returns `none`.
* Spill-slot `MOVQ`, `ADC`/`SBB`/`ADCX`/`ADOX`, variable-count shifts, `CMP:64`
  as a bare flag write (no `lsem` denotation) and narrow `MOV:8`/`MOV:16`.

## Main results

* `MemRel`, `LJCorrM` — the memory relation and the widened correspondence.
* `tiedInstrX`, `tiedInstr_le_tiedInstrX` — the widened fragment and the
  inclusion of the register-only one.
* `immShiftOf`, `ShiftParseAgrees`, `BodyParseAgrees` — the shift the gather
  reads, and the agreement with the `lsem` reading.
* `setcc_case`, `shift_case`, `movShift_case`, `loadidx_case`, `storeidx_case` —
  the per-instruction agreements of the new arms.
* `instr_agreeX`, `block_agreeX` — the dispatch and the block lift.
* `gatherJBlock6_lsem_agreeX` — the widened tie; `gatherJBlock6_lsem_agreeM_of_tied`
  is its restriction to the register-only fragment, and
  `gatherJBlock6_optimized_lsem_agreeX` composes it with
  `X86ComPipeline.optimizeX86Block_runBlock`.
* `demoBodyX`, `demoBodyX_tied`, `demoBodyX_agree` — a body with a `MOV:64`, an
  in-place `SHL:3:64`, a `SETB:64`, a `LOADIDX` and a `STOREIDX`, run both ways.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTieExt

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTie
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (lowerCov6 lowerCov6L gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode (lowerCov5)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
  (lowerLinstrExtCov4 lowerFlagClassJ setccCondOf isPlainGp cmpSrcOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
  (lowerLinstrExtCov3 lowerAluJ2InPlace)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage (lowerLinstrExtCov)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
  (lowerLinstrExtCov2 sarCountOf lowerSarJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
  (lowerLinstrExt2 lowerAluJ lowerJOperand parseShiftMnem lowerShiftImmJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
  (optimizeX86Block optimizeX86Block_runBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FlagClassSetccValueTie

/-! ## 1. The widened state correspondence -/

/-- The two memories agree pointwise: `Lstate.lmem` and `JState.mem` are both
    `(base, byte offset) ↦ word` maps at width 64. -/
def MemRel (ls : Lstate 64) (s : JState 64) : Prop := ∀ b o, ls.lmem b o = s.mem b o

/-- The widened correspondence: register-file equality and memory equality. -/
def LJCorrM (ls : Lstate 64) (s : JState 64) : Prop := LJCorr ls s ∧ MemRel ls s

theorem Lstate.lmem_setReg (ls : Lstate 64) (d : String) (v : BitVec 64) :
    (ls.setReg d v).lmem = ls.lmem := rfl

/-- A matched register write against a `JState` given by its register file, with
    the machine memory unchanged, preserves the widened correspondence. -/
theorem LJCorrM_write {ls : Lstate 64} {s : JState 64} (h : LJCorrM ls s)
    (d : String) (v : BitVec 64) (t : JState 64)
    (ht : ∀ r, t.regs r = if r = d then v else s.regs r) (hm : t.mem = s.mem) :
    LJCorrM ((ls.setReg d v).nextPc) t :=
  ⟨LJCorr_write h.1 d v t ht, fun b o => by
    rw [Lstate.lmem_nextPc, Lstate.lmem_setReg, hm]; exact h.2 b o⟩

/-- A word-op step over non-indexed sources leaves `lmem` unchanged. -/
theorem lsemStep_lmem {d opn : String} {srcs : List LOperand} {ls ls' : Lstate 64}
    (h0 : ∀ base idx scale rest, srcs ≠ LOperand.arrIdx base idx scale :: rest)
    (h : lsemStep (.Lopn [.reg d] opn srcs) ls = some ls') : ls'.lmem = ls.lmem := by
  rw [lsemStep_reg_srcs d opn srcs ls h0] at h
  split at h
  · cases Option.some.inj h; rfl
  · exact absurd h (by simp)

/-! ## 2. The widened fragment -/

/-- A register-indexed memory operand. -/
def isArrIdx : LOperand → Bool
  | .arrIdx _ _ _ => true
  | _ => false

/-- The three immediate shifts the tie covers. -/
inductive ShiftKind where
  | shl | shr | sar
  deriving DecidableEq, Repr

/-- The AT&T direction `parseImmShiftMnem` reports for a shift kind. -/
def ShiftKind.att : ShiftKind → String
  | .shl => "shl"
  | .shr => "shr"
  | .sar => "sar"

/-- The word function of a shift kind at count `n`. -/
def ShiftKind.word : ShiftKind → Nat → BitVec 64 → BitVec 64
  | .shl, n, a => a <<< n
  | .shr, n, a => a >>> n
  | .sar, n, a => BitVec.sshiftRight a n

/-- The immediate-count `JInstr` of a shift kind. -/
def ShiftKind.jinstr : ShiftKind → String → Nat → JInstr 64
  | .shl, d, n => .shl d (.imm n)
  | .shr, d, n => .shr d (.imm n)
  | .sar, d, n => .sar d (.imm n)

/-- The immediate shift the gather reads off a one-source mnemonic: the
    `SHL:<n>`/`SHR:<n>` reading of `parseShiftMnem` when `sarCountOf` declines,
    the `SAR:<n>:64` reading of `sarCountOf` when `parseShiftMnem` declines,
    `none` otherwise. -/
def immShiftOf (m : String) : Option (ShiftKind × Nat) :=
  match parseShiftMnem m, sarCountOf m with
  | some (true, n), none => some (.shl, n)
  | some (false, n), none => some (.shr, n)
  | none, some n => some (.sar, n)
  | _, _ => none

/-- The register-only two-source ALU arm of `GatherLsemTie.tiedInstrR`. -/
def tiedBin (d m : String) (s0 s1 : LOperand) : Bool :=
  tiedBinMnem m && tiedOperand s0 && tiedOperand s1 && (isRegNamed d s0 || !isRegNamed d s1)

/-- A materialised comparison over the operands `lowerFlagClassJ` admits. -/
def tiedSetcc (d m : String) (s0 s1 : LOperand) : Bool :=
  (setccCondOf m).isSome && isPlainGp d &&
    (match s0 with | .reg a => isPlainGp a | _ => false) && cmpSrcOk s1

/-- A register-indexed store of a register or immediate value. -/
def tiedStoreIdx (m : String) (s0 s1 : LOperand) : Bool :=
  m == "STOREIDX" && isArrIdx s0 && tiedOperand s1

/-- A register-indexed load. -/
def tiedLoadIdx (m : String) (src : LOperand) : Bool := m == "LOADIDX" && isArrIdx src

/-- An immediate shift at a count below the word width over a register or
    immediate source. -/
def tiedShift (m : String) (src : LOperand) : Bool :=
  tiedOperand src && match immShiftOf m with
    | some (_, n) => decide (n < 64)
    | none => false

/-- The widened tied shapes. -/
def tiedInstrXR : LinstrR → Bool
  | .Lopn [.reg d] m [s0, s1] => tiedBin d m s0 s1 || tiedSetcc d m s0 s1 || tiedStoreIdx m s0 s1
  | .Lopn [.reg _] m [src] => (m == "MOV:64" && tiedOperand src) || tiedLoadIdx m src || tiedShift m src
  | _ => false

/-- The widened tied predicate on a positioned `Linstr`. -/
def tiedInstrX (i : Linstr) : Bool := tiedInstrXR i.li_i

/-- The register-only fragment is inside the widened one. -/
theorem tiedInstr_le_tiedInstrX (i : Linstr) (h : tiedInstr i = true) : tiedInstrX i = true := by
  obtain ⟨p, ir⟩ := i
  simp only [tiedInstr, tiedInstrR] at h
  split at h
  · simp [tiedInstrX, tiedInstrXR, tiedBin, h]
  · simp [tiedInstrX, tiedInstrXR, h]
  · simp at h

/-! ## 3. The parse hypothesis -/

/-- The mnemonic of an `Lopn`, the empty string on any other instruction. -/
def mnemOf (i : Linstr) : String :=
  match i.li_i with
  | .Lopn _ m _ => m
  | _ => ""

/-- The `lsem` reading of a shift mnemonic agrees with the gather's:
    `parseImmShiftMnem` on the tag-stripped mnemonic reports the direction and
    count `immShiftOf` reads. -/
def ShiftParseAgrees (m : String) : Prop :=
  ∀ k n, immShiftOf m = some (k, n) →
    ∃ wd, parseImmShiftMnem (stripWidthTag m) = some (k.att, n, wd)

/-- `ShiftParseAgrees` on every mnemonic of a body. -/
def BodyParseAgrees (body : List Linstr) : Prop := ∀ i ∈ body, ShiftParseAgrees (mnemOf i)

theorem immShiftOf_ADD : immShiftOf "ADD:64" = none := by decide +kernel
theorem immShiftOf_SUB : immShiftOf "SUB:64" = none := by decide +kernel
theorem immShiftOf_MUL : immShiftOf "MUL:64" = none := by decide +kernel
theorem immShiftOf_AND : immShiftOf "AND:64" = none := by decide +kernel
theorem immShiftOf_OR : immShiftOf "OR:64" = none := by decide +kernel
theorem immShiftOf_XOR : immShiftOf "XOR:64" = none := by decide +kernel
theorem immShiftOf_MOV : immShiftOf "MOV:64" = none := by decide +kernel
theorem immShiftOf_MOVQ : immShiftOf "MOVQ" = none := by decide +kernel
theorem immShiftOf_SAR31 : immShiftOf "SAR:31" = none := by decide +kernel

/-- No instruction of the register-only fragment is a shift, so the parse
    hypothesis holds on it. -/
theorem tiedInstr_parseAgrees (i : Linstr) (h : tiedInstr i = true) :
    ShiftParseAgrees (mnemOf i) := by
  obtain ⟨p, ir⟩ := i
  simp only [tiedInstr, tiedInstrR] at h
  split at h
  · rename_i d m s0 s1
    simp only [Bool.and_eq_true, tiedBinMnem, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hm, -⟩, -⟩, -⟩ := h
    intro k n hk
    simp only [mnemOf] at hk
    rcases hm with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;>
      simp only [immShiftOf_ADD, immShiftOf_SUB, immShiftOf_MUL, immShiftOf_AND, immShiftOf_OR,
        immShiftOf_XOR] at hk <;> cases hk
  · intro k n hk
    simp only [mnemOf, immShiftOf_MOV] at hk
    cases hk
  · simp at h

/-! ## 4. Shift words -/

theorem shiftCount_ofNat_lt {n : Nat} (h : n < 64) : shiftCount (BitVec.ofNat 64 n) = n := by
  have h64 : n < 2 ^ 64 := by omega
  simp only [shiftCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, VIR.shiftMask_of_lt h]

/-- The data word of an immediate-count `shl`/`shr`/`sar` at a count below `64`
    is the plain shift. -/
theorem shift_word_ofNat (k : ShiftKind) {n : Nat} (h : n < 64) (v : BitVec 64) :
    (match k with
      | .shl => (x86_SHL v (BitVec.ofNat 64 n)).word
      | .shr => (x86_SHR v (BitVec.ofNat 64 n)).word
      | .sar => (x86_SAR v (BitVec.ofNat 64 n)).word) = k.word n v := by
  have hmin : min 64 n = n := by omega
  cases k <;> simp only [x86_SHL, x86_SHR, x86_SAR, shiftCount_ofNat_lt h, ShiftKind.word] <;>
    by_cases h0 : n = 0
  all_goals first
    | (subst h0; simp [rflags_None])
    | simp only [if_neg h0, rflags_OF, wshl, wshr, wsar, hmin]

theorem ShiftKind.word_zero (k : ShiftKind) (a : BitVec 64) : k.word 0 a = a := by
  cases k <;> simp [ShiftKind.word]

/-- The register file after an immediate shift instruction. -/
theorem shift_regs (k : ShiftKind) {n : Nat} (hn : n < 64) (t : JState 64) (d r : String) :
    (evalInstr t (k.jinstr d n)).regs r = if r = d then k.word n (t.regs d) else t.regs r := by
  have := shift_word_ofNat k hn (t.regs d)
  cases k <;> simp only [ShiftKind.jinstr, evalInstr, JState.writeB5W, JOperand.eval,
    JState.get] at this ⊢ <;> rw [this]

theorem shift_mem (k : ShiftKind) (n : Nat) (t : JState 64) (d : String) :
    (evalInstr t (k.jinstr d n)).mem = t.mem := by
  cases k <;> rfl

theorem mov_regs (t : JState 64) (d : String) (o : JOperand) (r : String) :
    (evalInstr t (.mov d o)).regs r = if r = d then o.eval t else t.regs r := rfl

theorem mov_mem (t : JState 64) (d : String) (o : JOperand) :
    (evalInstr t (.mov d o)).mem = t.mem := rfl

/-! ## 5. The `lsem` value of a count-in-mnemonic shift -/

/-- `applyOpn` on a one-source mnemonic outside the named one-source opcodes is
    the shift or rotate `parseImmShiftMnem` decodes, at a count below `64`. -/
theorem applyOpn_one_of_parse (opn att : String) (k wd : Nat) (hk : k < 64)
    (hne : opn ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"])
    (hp : parseImmShiftMnem opn = some (att, k, wd)) (a : BitVec 64) :
    applyOpn opn [a]
      = some (if att = "shl" then a <<< k
          else if att = "sar" then BitVec.sshiftRight a k
          else if att = "rol" then a.rotateLeft k
          else if att = "ror" then a.rotateRight k
          else a >>> k) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  unfold applyOpn
  split <;> simp_all [Nat.mod_eq_of_lt hk]

/-- A mnemonic `parseShiftMnem` reads begins, after the tag strip, with `SHL:` or
    `SHR:`, so its stripped form is none of the named one-source opcodes. -/
theorem strip_not_unary_of_parseShift {m : String} {isL : Bool} {n : Nat}
    (hp : parseShiftMnem m = some (isL, n)) :
    stripWidthTag m ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"] := by
  unfold parseShiftMnem at hp
  dsimp only at hp
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h <;> rw [h] at hp <;> simp [hasPrefix] at hp

/-- The stripped form of a mnemonic `sarCountOf` reads begins with `SAR:`. -/
theorem strip_toList_of_sarCountOf {m : String} {n : Nat} (hs : sarCountOf m = some n) :
    ['S', 'A', 'R', ':'].isPrefixOf (stripWidthTag m).toList = true := by
  unfold sarCountOf at hs
  dsimp only at hs
  split_ifs at hs with hsuf hpre
  unfold stripWidthTag
  split
  · obtain ⟨t, ht⟩ := (List.isPrefixOf_iff_prefix.mp hpre).trans (List.take_prefix _ _)
    rw [String.toList_ofList, ← ht,
      List.takeWhile_append_of_pos (bne_at_of_not_mem (by decide))]
    simp_all
  rw [if_pos (show hasSuffix m ":64" = true from hsuf), String.toList_ofList]
  have hl : m.toList.dropLast.dropLast.dropLast = m.toList.take (m.toList.length - 3) := by
    simp only [List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1
    omega
  rw [hl]
  exact hpre

theorem strip_not_unary_of_sarCountOf {m : String} {n : Nat} (hs : sarCountOf m = some n) :
    stripWidthTag m ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"] := by
  have h := strip_toList_of_sarCountOf hs
  intro hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)

theorem strip_not_unary_of_immShiftOf {m : String} {k : ShiftKind} {n : Nat}
    (h : immShiftOf m = some (k, n)) :
    stripWidthTag m ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"] := by
  unfold immShiftOf at h
  split at h
  · exact strip_not_unary_of_parseShift (by assumption)
  · exact strip_not_unary_of_parseShift (by assumption)
  · exact strip_not_unary_of_sarCountOf (by assumption)
  · exact absurd h (by simp)

/-- The `lsem` value of a tied shift mnemonic on one source word, under the parse
    hypothesis. -/
theorem applyOpn_immShift {m : String} {k : ShiftKind} {n : Nat}
    (h : immShiftOf m = some (k, n)) (hn : n < 64) (hpa : ShiftParseAgrees m) (a : BitVec 64) :
    applyOpn (stripWidthTag m) [a] = some (k.word n a) := by
  obtain ⟨wd, hp⟩ := hpa k n h
  rw [applyOpn_one_of_parse _ _ _ _ hn (strip_not_unary_of_immShiftOf h) hp]
  cases k <;> simp [ShiftKind.att, ShiftKind.word]

/-- `lsemStep` on a one-source `Lopn` over a register or immediate is the word-op
    arm: it writes the `applyOpn` value and advances the pc. -/
theorem lsemStep_one (d opn : String) (src : LOperand) (hsrc : tiedOperand src = true)
    (ls : Lstate 64) (v : BitVec 64)
    (h : applyOpn (stripWidthTag opn) [evalOperand ls src] = some v) :
    lsemStep (.Lopn [.reg d] opn [src]) ls = some ((ls.setReg d v).nextPc) := by
  rw [lsemStep_reg_srcs]
  · simp only [List.map_cons, List.map_nil, h]
  · intro base idx scale rest h
    cases src <;> simp_all [tiedOperand]

/-! ## 6. The gather's shape on the new arms -/

/-- The block the gather emits for a `SHL:<n>`/`SHR:<n>` over a register source
    `s` into `d`: the shift alone when `s = d`, a materialising `mov` first
    otherwise, and no shift at count `0`. -/
def shiftBlockReg (k : ShiftKind) (d s : String) (n : Nat) : List (JInstr 64) :=
  if s = d then (if n = 0 then [] else [k.jinstr d n])
  else if n = 0 then [JInstr.mov d (.reg s)] else [JInstr.mov d (.reg s), k.jinstr d n]

/-- The two-instruction materialise-then-shift block. -/
def movShiftBlock (k : ShiftKind) (d : String) (o : JOperand) (n : Nat) : List (JInstr 64) :=
  [JInstr.mov d o, k.jinstr d n]

theorem ne_MOVQ_of_immShiftOf {m : String} {k : ShiftKind} {n : Nat}
    (h : immShiftOf m = some (k, n)) : m ≠ "MOVQ" := by
  rintro rfl; rw [immShiftOf_MOVQ] at h; cases h

theorem ne_SAR31_of_immShiftOf {m : String} {k : ShiftKind} {n : Nat}
    (h : immShiftOf m = some (k, n)) : m ≠ "SAR:31" := by
  rintro rfl; rw [immShiftOf_SAR31] at h; cases h

/-- The gather's image of a `SHL:<n>`/`SHR:<n>` over a register source. -/
theorem lower_shift_reg (frame spillW qsaveB : Nat) (d m s : String) (isL : Bool) (n : Nat)
    (hp : parseShiftMnem m = some (isL, n)) (hsar : sarCountOf m = none)
    (h1 : m ≠ "MOVQ") (h2 : m ≠ "SAR:31") :
    lowerCov6 frame spillW (.Lopn [.reg d] m [.reg s]) qsaveB
      = some (shiftBlockReg (if isL then .shl else .shr) d s n) := by
  by_cases hsd : s = d <;> by_cases hn : n = 0 <;> cases isL <;>
    unfold lowerCov6 <;> split <;>
    simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerLinstrExtCov2,
      lowerLinstrExtCov, lowerLinstrExt2, lowerShiftImmJ, lowerJOperand, shiftBlockReg,
      ShiftKind.jinstr]

/-- The gather's image of a `SHL:<n>`/`SHR:<n>` over an immediate source. -/
theorem lower_shift_imm (frame spillW qsaveB : Nat) (d m : String) (v : Nat) (isL : Bool) (n : Nat)
    (hp : parseShiftMnem m = some (isL, n)) (hsar : sarCountOf m = none)
    (h1 : m ≠ "MOVQ") (h2 : m ≠ "SAR:31") :
    lowerCov6 frame spillW (.Lopn [.reg d] m [.imm v]) qsaveB
      = some (movShiftBlock (if isL then .shl else .shr) d (.imm v) n) := by
  cases isL <;> unfold lowerCov6 <;> split <;>
    simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerLinstrExtCov2,
      lowerLinstrExtCov, lowerLinstrExt2, lowerShiftImmJ, lowerJOperand, movShiftBlock,
      ShiftKind.jinstr]

/-- The gather's image of a tagged `SAR:<n>:64` over a register or immediate. -/
theorem lower_sar (frame spillW qsaveB : Nat) (d m : String) (src : LOperand) (n : Nat)
    (hsrc : tiedOperand src = true) (hp : parseShiftMnem m = none) (hsar : sarCountOf m = some n)
    (h1 : m ≠ "MOVQ") (h2 : m ≠ "SAR:31") :
    lowerCov6 frame spillW (.Lopn [.reg d] m [src]) qsaveB
      = some (movShiftBlock .sar d (lowerJOperand src) n) := by
  cases src <;> simp only [tiedOperand] at hsrc <;> unfold lowerCov6 <;> split <;>
    simp_all [lowerCov5, lowerLinstrExtCov4, lowerLinstrExtCov3, lowerLinstrExtCov2,
      lowerSarJ, movShiftBlock, ShiftKind.jinstr]

/-- The gather's image of a materialised comparison is `lowerFlagClassJ`'s block. -/
theorem lower_setcc (frame spillW qsaveB : Nat) (d opn a : String) (s1 : LOperand) (c : Condt)
    (hcc : setccCondOf opn = some c) :
    lowerCov6 frame spillW (.Lopn [.reg d] opn [.reg a, s1]) qsaveB
      = lowerFlagClassJ d opn (.reg a) s1 := by
  obtain ⟨jc, rfl, -⟩ := exists_cmp_of_setccCondOf hcc
  cases jc <;> cases s1 <;> rfl

/-- The gather's image of a register-indexed load. -/
theorem lower_loadidx (frame spillW qsaveB : Nat) (d b i : String) (sc : Nat) :
    lowerCov6 frame spillW (.Lopn [.reg d] "LOADIDX" [.arrIdx b i sc]) qsaveB
      = some [JInstr.loadMemIdx d b i sc] := rfl

/-- The gather's image of a register-indexed store. -/
theorem lower_storeidx (frame spillW qsaveB : Nat) (d b i : String) (sc : Nat) (val : LOperand) :
    lowerCov6 frame spillW (.Lopn [.reg d] "STOREIDX" [.arrIdx b i sc, val]) qsaveB
      = some [JInstr.storeMemIdx b i sc (lowerJOperand val)] := rfl

/-! ## 7. Per-instruction agreement -/

/-- The register file and memory after `movShiftBlock`. -/
theorem movShiftBlock_regs (k : ShiftKind) {n : Nat} (hn : n < 64) (s : JState 64)
    (d : String) (o : JOperand) (r : String) :
    (runBlock s (movShiftBlock k d o n)).regs r
      = if r = d then k.word n (o.eval s) else s.regs r := by
  simp only [movShiftBlock, runBlock_cons, runBlock_nil, shift_regs k hn, mov_regs]
  by_cases hr : r = d <;> simp [hr]

theorem movShiftBlock_mem (k : ShiftKind) (n : Nat) (s : JState 64) (d : String) (o : JOperand) :
    (runBlock s (movShiftBlock k d o n)).mem = s.mem := by
  simp only [movShiftBlock, runBlock_cons, runBlock_nil, shift_mem, mov_mem]

/-- The register file and memory after `shiftBlockReg`. -/
theorem shiftBlockReg_regs (k : ShiftKind) {n : Nat} (hn : n < 64) (s : JState 64)
    (d src : String) (r : String) :
    (runBlock s (shiftBlockReg k d src n)).regs r
      = if r = d then k.word n (s.regs src) else s.regs r := by
  unfold shiftBlockReg
  by_cases hsd : src = d <;> by_cases hn0 : n = 0 <;>
    simp only [hsd, hn0, if_true, if_false, runBlock_cons, runBlock_nil, shift_regs k hn,
      mov_regs, ShiftKind.word_zero, JOperand.eval, JState.get] <;>
    by_cases hr : r = d <;> simp [hr]

theorem shiftBlockReg_mem (k : ShiftKind) (n : Nat) (s : JState 64) (d src : String) :
    (runBlock s (shiftBlockReg k d src n)).mem = s.mem := by
  unfold shiftBlockReg
  by_cases hsd : src = d <;> by_cases hn0 : n = 0 <;>
    simp only [hsd, hn0, if_true, if_false, runBlock_cons, runBlock_nil, shift_mem, mov_mem]

/-- **One materialised comparison.** The gather emits the `cmp`/`mov`/`setcc`
    triple, the `lsem` step writes the fused `cmpBit` word, and the two results
    correspond. -/
theorem setcc_case (frame spillW qsaveB : Nat) {ls : Lstate 64} {s : JState 64}
    (hc : LJCorrM ls s) (d opn a : String) (s1 : LOperand) (c : Condt)
    (hcc : setccCondOf opn = some c) (hd : isPlainGp d = true) (ha : isPlainGp a = true)
    (hs1 : cmpSrcOk s1 = true) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] opn [.reg a, s1]) qsaveB = some g ∧
      lsemStep (.Lopn [.reg d] opn [.reg a, s1]) ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  have hlowF : lowerFlagClassJ d opn (.reg a) s1
      = some [JInstr.cmp a (lowerJOperand s1), JInstr.mov d (JOperand.imm 0),
              JInstr.setcc c d] := by
    simp [lowerFlagClassJ, hd, hcc, ha, hs1]
  have hlow := (lower_setcc frame spillW qsaveB d opn a s1 c hcc).trans hlowF
  have hval := flagClass_setcc_value_tie (fun r => (hc.1 r).symm) hcc hlowF
  have hstep : lsemStep (.Lopn [.reg d] opn [.reg a, s1]) ls
      = some ((ls.setReg d ((runBlock s [JInstr.cmp a (lowerJOperand s1),
          JInstr.mov d (JOperand.imm 0), JInstr.setcc c d]).regs d)).nextPc) := by
    rw [lsemStep_reg_cons2 d opn (.reg a) s1 ls (by simp)]
    rw [show evalOperand ls (.reg a) = ls.lvm a from rfl, hval]
  refine ⟨_, _, hlow, hstep, LJCorrM_write hc d _ _ (fun r => ?_) ?_⟩
  · by_cases hr : r = d
    · simp [hr]
    · rw [if_neg hr]
      exact flagClass_setcc_other_reg hcc hlowF hr
  · simp [runBlock_cons, runBlock_nil, evalInstr, JState.setRegMerge, JState.setReg,
      JState.writeB5]

/-- **One immediate shift over a register source** (`SHL:<n>`/`SHR:<n>`, or
    `SAR:<n>:64` through `movShift_case`). -/
theorem shift_case (frame spillW qsaveB : Nat) {ls : Lstate 64} {s : JState 64}
    (hc : LJCorrM ls s) (d m : String) (src : LOperand) (k : ShiftKind) (n : Nat)
    (hsrc : tiedOperand src = true) (hk : immShiftOf m = some (k, n)) (hn : n < 64)
    (hpa : ShiftParseAgrees m) (g : List (JInstr 64))
    (hlow : lowerCov6 frame spillW (.Lopn [.reg d] m [src]) qsaveB = some g)
    (hg : ∀ r, (runBlock s g).regs r
      = if r = d then k.word n ((lowerJOperand src).eval s) else s.regs r)
    (hgm : (runBlock s g).mem = s.mem) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] m [src]) qsaveB = some g ∧
      lsemStep (.Lopn [.reg d] m [src]) ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  have hstep : lsemStep (.Lopn [.reg d] m [src]) ls
      = some ((ls.setReg d (k.word n (evalOperand ls src))).nextPc) := by
    exact lsemStep_one d m src hsrc ls _ (applyOpn_immShift hk hn hpa _)
  refine ⟨g, _, hlow, hstep, ?_⟩
  rw [evalOperand_agree hc.1 src hsrc]
  exact LJCorrM_write hc d _ _ hg hgm

/-- The dispatch of `shift_case` over the three gather shapes. -/
theorem immShift_case (frame spillW qsaveB : Nat) {ls : Lstate 64} {s : JState 64}
    (hc : LJCorrM ls s) (d m : String) (src : LOperand) (k : ShiftKind) (n : Nat)
    (hsrc : tiedOperand src = true) (hk : immShiftOf m = some (k, n)) (hn : n < 64)
    (hpa : ShiftParseAgrees m) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] m [src]) qsaveB = some g ∧
      lsemStep (.Lopn [.reg d] m [src]) ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  have h1 := ne_MOVQ_of_immShiftOf hk
  have h2 := ne_SAR31_of_immShiftOf hk
  have hk' := hk
  unfold immShiftOf at hk'
  split at hk'
  · -- SHL over a register or an immediate
    rename_i hp hsar
    cases Option.some.inj hk'
    cases src with
    | reg s0 =>
      exact shift_case frame spillW qsaveB hc d m (.reg s0) .shl n hsrc hk hn hpa _
        (by simpa using lower_shift_reg frame spillW qsaveB d m s0 true n hp hsar h1 h2)
        (fun r => by rw [shiftBlockReg_regs .shl hn]; rfl) (shiftBlockReg_mem _ _ _ _ _)
    | imm v =>
      exact shift_case frame spillW qsaveB hc d m (.imm v) .shl n hsrc hk hn hpa _
        (by simpa using lower_shift_imm frame spillW qsaveB d m v true n hp hsar h1 h2)
        (fun r => by rw [movShiftBlock_regs .shl hn]; rfl) (movShiftBlock_mem _ _ _ _ _)
    | arr _ _ => simp [tiedOperand] at hsrc
    | arrIdx _ _ _ => simp [tiedOperand] at hsrc
  · -- SHR over a register or an immediate
    rename_i hp hsar
    cases Option.some.inj hk'
    cases src with
    | reg s0 =>
      exact shift_case frame spillW qsaveB hc d m (.reg s0) .shr n hsrc hk hn hpa _
        (by simpa using lower_shift_reg frame spillW qsaveB d m s0 false n hp hsar h1 h2)
        (fun r => by rw [shiftBlockReg_regs .shr hn]; rfl) (shiftBlockReg_mem _ _ _ _ _)
    | imm v =>
      exact shift_case frame spillW qsaveB hc d m (.imm v) .shr n hsrc hk hn hpa _
        (by simpa using lower_shift_imm frame spillW qsaveB d m v false n hp hsar h1 h2)
        (fun r => by rw [movShiftBlock_regs .shr hn]; rfl) (movShiftBlock_mem _ _ _ _ _)
    | arr _ _ => simp [tiedOperand] at hsrc
    | arrIdx _ _ _ => simp [tiedOperand] at hsrc
  · -- SAR:<n>:64
    rename_i hp hsar
    cases Option.some.inj hk'
    exact shift_case frame spillW qsaveB hc d m src .sar n hsrc hk hn hpa _
      (lower_sar frame spillW qsaveB d m src n hsrc hp hsar h1 h2)
      (fun r => by rw [movShiftBlock_regs .sar hn]) (movShiftBlock_mem _ _ _ _ _)
  · exact absurd hk' (by simp)

/-- **One register-indexed load.** Both sides read the cell at
    `scale · ⟦idx⟧` of `base` into the destination. -/
theorem loadidx_case (frame spillW qsaveB : Nat) {ls : Lstate 64} {s : JState 64}
    (hc : LJCorrM ls s) (d b i : String) (sc : Nat) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] "LOADIDX" [.arrIdx b i sc]) qsaveB = some g ∧
      lsemStep (.Lopn [.reg d] "LOADIDX" [.arrIdx b i sc]) ls = some ls' ∧
      LJCorrM ls' (runBlock s g) := by
  refine ⟨_, _, lower_loadidx frame spillW qsaveB d b i sc, rfl, ?_⟩
  refine LJCorrM_write hc d _ _ (fun r => ?_) rfl
  show (s.setReg d (x86_MOV (s.loadIdx b i sc))).regs r = _
  simp only [JState.setReg, x86_MOV, JState.loadIdx, JState.load, JState.get, hc.1 i,
    hc.2 b, Int.ofNat_eq_natCast, Nat.cast_mul]

/-- **One register-indexed store.** Both sides write the evaluated value to the
    cell at `scale · ⟦idx⟧` of `base` and no register. -/
theorem storeidx_case (frame spillW qsaveB : Nat) {ls : Lstate 64} {s : JState 64}
    (hc : LJCorrM ls s) (d b i : String) (sc : Nat) (val : LOperand)
    (hval : tiedOperand val = true) :
    ∃ g ls', lowerCov6 frame spillW (.Lopn [.reg d] "STOREIDX" [.arrIdx b i sc, val]) qsaveB
        = some g ∧
      lsemStep (.Lopn [.reg d] "STOREIDX" [.arrIdx b i sc, val]) ls = some ls' ∧
      LJCorrM ls' (runBlock s g) := by
  refine ⟨_, _, lower_storeidx frame spillW qsaveB d b i sc val, rfl, ?_⟩
  refine ⟨fun r => ?_, fun b' o => ?_⟩
  · show ls.lvm r = (s.storeIdx b i sc (x86_MOV ((lowerJOperand val).eval s))).regs r
    rw [JState.regs_storeIdx]; exact hc.1 r
  · show (if b' = b then (if o = Int.ofNat (sc * (ls.lvm i).toNat) then evalOperand ls val
        else ls.lmem b' o) else ls.lmem b' o)
      = (s.storeIdx b i sc (x86_MOV ((lowerJOperand val).eval s))).mem b' o
    simp only [JState.storeIdx, JState.store, JState.get, x86_MOV, hc.1 i,
      evalOperand_agree hc.1 val hval, Int.ofNat_eq_natCast, Nat.cast_mul]
    by_cases hb : b' = b
    · subst hb
      by_cases ho : o = ((sc : Int) * ((s.regs i).toNat : Int))
      · simp [ho]
      · simp only [ho, if_false]; exact hc.2 _ _
    · simp only [hb, if_false]; exact hc.2 _ _

/-! ## 8. The register-only arms carried over with memory -/

/-- The memory of the machine block a two-address ALU `Lopn` gathers to is
    unchanged. -/
theorem bin_mem (frame spillW qsaveB : Nat) (s : JState 64) (d m : String) (s0 s1 : LOperand)
    (hbin : tiedBin d m s0 s1 = true) (g : List (JInstr 64))
    (hg : lowerCov6 frame spillW (.Lopn [.reg d] m [s0, s1]) qsaveB = some g) :
    (runBlock s g).mem = s.mem := by
  simp only [tiedBin, Bool.and_eq_true, tiedBinMnem, Bool.or_eq_true, beq_iff_eq] at hbin
  obtain ⟨⟨⟨hm, -⟩, -⟩, -⟩ := hbin
  have key : ∀ (mk : String → JOperand → JInstr 64),
      (∀ (t : JState 64) src, (evalInstr t (mk d src)).mem = t.mem) →
      g = (if lowerJOperand s0 = JOperand.reg d then [mk d (lowerJOperand s1)]
           else [JInstr.mov d (lowerJOperand s0), mk d (lowerJOperand s1)]) →
      (runBlock s g).mem = s.mem := by
    intro mk hmk hg'
    subst hg'
    split <;> simp only [runBlock_cons, runBlock_nil, hmk, mov_mem]
  rcases hm with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
  · exact key JInstr.add (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_ADD]; exact LoweringExtended.lowerShiftRegJ_ADD _ _ _)
        (by rw [strip_ADD]; rfl))))
  · exact key JInstr.sub (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_SUB]; exact LoweringExtended.lowerShiftRegJ_SUB _ _ _)
        (by rw [strip_SUB]; rfl))))
  · exact key JInstr.imul (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_MUL]; exact LoweringExtended.lowerShiftRegJ_MUL _ _ _)
        (by rw [strip_MUL]; rfl))))
  · exact key JInstr.and_ (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_AND]; exact LoweringExtended.lowerShiftRegJ_AND _ _ _)
        (by rw [strip_AND]; rfl))))
  · exact key JInstr.or_ (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_OR]; exact LoweringExtended.lowerShiftRegJ_OR _ _ _)
        (by rw [strip_OR]; rfl))))
  · exact key JInstr.xor_ (fun _ _ => rfl) (Option.some.inj (hg.symm.trans
      (lower_bin _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
        (by rw [strip_XOR]; exact LoweringExtended.lowerShiftRegJ_XOR _ _ _)
        (by rw [strip_XOR]; rfl))))

/-- The gather's image of a `MOV:64` over a register or immediate. -/
theorem lower_mov (frame spillW qsaveB : Nat) (d : String) (src : LOperand)
    (hsrc : tiedOperand src = true) :
    lowerCov6 frame spillW (.Lopn [.reg d] "MOV:64" [src]) qsaveB
      = some [JInstr.mov d (lowerJOperand src)] :=
  lower_un frame spillW qsaveB d "MOV:64" src (JInstr.mov d (lowerJOperand src))
    hsrc (by decide) (by decide) (by decide) (by decide) pshift_MOV (by rfl)
    (by rw [strip_MOV]; rfl)

/-! ## 9. The dispatch and the block lift -/

theorem instr_agreeX (frame spillW qsaveB : Nat) (i : Linstr) (hi : tiedInstrX i = true)
    (hpa : ShiftParseAgrees (mnemOf i)) {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', lowerCov6L frame spillW i qsaveB = some g ∧
      lsemStep i.li_i ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  obtain ⟨p, ir⟩ := i
  simp only [tiedInstrX, tiedInstrXR] at hi
  split at hi
  · rename_i d m s0 s1
    simp only [Bool.or_eq_true] at hi
    rcases hi with (hbin | hset) | hst
    · -- two-address ALU: registers from `GatherLsemTie.instr_agree`, memory untouched
      have hold : tiedInstr ⟨p, .Lopn [.reg d] m [s0, s1]⟩ = true := by
        simpa [tiedInstr, tiedInstrR, tiedBin] using hbin
      obtain ⟨g, ls', hg, hstep, hc'⟩ := instr_agree frame spillW qsaveB _ hold hc.1
      have h0 : tiedOperand s0 = true := by
        simp only [tiedBin, Bool.and_eq_true] at hbin; exact hbin.1.1.2
      refine ⟨g, ls', hg, hstep, hc', fun b o => ?_⟩
      rw [lsemStep_lmem (fun base idx scale rest h => by
            cases s0 <;> simp_all [tiedOperand]) hstep,
        bin_mem frame spillW qsaveB s d m s0 s1 hbin g hg]
      exact hc.2 b o
    · simp only [tiedSetcc, Bool.and_eq_true, Option.isSome_iff_exists] at hset
      obtain ⟨⟨⟨⟨c, hcc⟩, hd⟩, ha⟩, hs1⟩ := hset
      cases s0 with
      | reg a => exact setcc_case frame spillW qsaveB hc d m a s1 c hcc hd ha hs1
      | imm _ => simp at ha
      | arr _ _ => simp at ha
      | arrIdx _ _ _ => simp at ha
    · simp only [tiedStoreIdx, Bool.and_eq_true, beq_iff_eq] at hst
      obtain ⟨⟨rfl, hidx⟩, hval⟩ := hst
      cases s0 with
      | arrIdx b i sc => exact storeidx_case frame spillW qsaveB hc d b i sc s1 hval
      | reg _ => simp [isArrIdx] at hidx
      | imm _ => simp [isArrIdx] at hidx
      | arr _ _ => simp [isArrIdx] at hidx
  · rename_i d m src
    simp only [Bool.or_eq_true] at hi
    rcases hi with (hmov | hld) | hsh
    · simp only [Bool.and_eq_true, beq_iff_eq] at hmov
      obtain ⟨rfl, hsrc⟩ := hmov
      obtain ⟨g, ls', hg, hstep, hc'⟩ := mov_case frame spillW qsaveB hc.1 d src hsrc
      have hg' : g = [JInstr.mov d (lowerJOperand src)] :=
        Option.some.inj (hg.symm.trans (lower_mov frame spillW qsaveB d src hsrc))
      refine ⟨g, ls', hg, hstep, hc', fun b o => ?_⟩
      rw [lsemStep_lmem (fun base idx scale rest h => by
            cases src <;> simp_all [tiedOperand]) hstep, hg', runBlock_cons, runBlock_nil,
        mov_mem]
      exact hc.2 b o
    · simp only [tiedLoadIdx, Bool.and_eq_true, beq_iff_eq] at hld
      obtain ⟨rfl, hidx⟩ := hld
      cases src with
      | arrIdx b i sc => exact loadidx_case frame spillW qsaveB hc d b i sc
      | reg _ => simp [isArrIdx] at hidx
      | imm _ => simp [isArrIdx] at hidx
      | arr _ _ => simp [isArrIdx] at hidx
    · simp only [tiedShift, Bool.and_eq_true] at hsh
      obtain ⟨hsrc, hk⟩ := hsh
      split at hk
      · rename_i k n hkn
        exact immShift_case frame spillW qsaveB hc d m src k n hsrc hkn
          (by simpa using hk) hpa
      · exact absurd hk (by simp)
  · simp at hi

/-- **Block agreement on the widened fragment.** -/
theorem block_agreeX (frame spillW qsaveB : Nat) (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstrX i = true) (hpa : BodyParseAgrees body)
    {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', gatherWith frame spillW qsaveB body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  induction body generalizing ls s with
  | nil => exact ⟨[], ls, rfl, rfl, hc⟩
  | cons i is ih =>
    obtain ⟨g1, ls1, hg1, hstep1, hc1⟩ :=
      instr_agreeX frame spillW qsaveB i (hb i (List.mem_cons_self ..))
        (hpa i (List.mem_cons_self ..)) hc
    obtain ⟨g2, ls2, hg2, hstep2, hc2⟩ :=
      ih (fun j hj => hb j (List.mem_cons_of_mem i hj))
        (fun j hj => hpa j (List.mem_cons_of_mem i hj)) hc1
    refine ⟨g1 ++ g2, ls2, ?_, ?_, ?_⟩
    · unfold gatherWith at hg2 ⊢
      cases hgm : is.mapM (fun i => lowerCov6L frame spillW i qsaveB) with
      | none => rw [hgm] at hg2; simp at hg2
      | some gs =>
        rw [hgm] at hg2
        simp only [Option.map_some, Option.some.injEq] at hg2
        simp [List.mapM_cons, hg1, hgm, ← hg2]
    · simp only [List.map_cons, lsemStraight_cons, hstep1, hstep2]
    · rw [GatherLsemTie.runBlock_append]; exact hc2

/-- A widened-tied instruction is not the `Lret` terminator. -/
theorem filter_isLret_idX (body : List Linstr) (hb : ∀ i ∈ body, tiedInstrX i = true) :
    body.filter (fun i => !isLret i) = body := by
  refine List.filter_eq_self.2 (fun i hi => ?_)
  have := hb i hi
  obtain ⟨p, ir⟩ := i
  cases ir <;> simp_all [isLret, tiedInstrX, tiedInstrXR]

/-! ## 10. The widened tie -/

/-- **The widened gather tie.** For a body whose every instruction is in
    `tiedInstrX` and whose shift mnemonics satisfy the parse hypothesis,
    `GatherImmForms.gatherJBlock6` succeeds, `lsemStraight` runs to completion from
    any `Lstate` corresponding to a `JState` on registers and memory, and the two
    final states again correspond on registers and memory. -/
theorem gatherJBlock6_lsem_agreeX (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstrX i = true) (hpa : BodyParseAgrees body)
    {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧ LJCorrM ls' (runBlock s g) := by
  obtain ⟨g, ls', hg, hstep, hc'⟩ :=
    block_agreeX
      (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.frameSize body)
      (if CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.bodyIsU64 body then 64
        else 32)
      (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.qsaveBytesFor body)
      body hb hpa hc
  refine ⟨g, ls', ?_, hstep, hc'⟩
  unfold gatherJBlock6
  rw [filter_isLret_idX body hb]
  exact hg

/-- The widened tie restricted to the register-only fragment: the conclusion of
    `GatherLsemTie.gatherJBlock6_lsem_agree`, with memory agreement added on both
    sides and no parse hypothesis. -/
theorem gatherJBlock6_lsem_agreeM_of_tied (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstr i = true) {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧ LJCorrM ls' (runBlock s g) :=
  gatherJBlock6_lsem_agreeX body (fun i hi => tiedInstr_le_tiedInstrX i (hb i hi))
    (fun i hi => tiedInstr_parseAgrees i (hb i hi)) hc

/-- The widened tie composed with `X86ComPipeline.optimizeX86Block_runBlock`. -/
theorem gatherJBlock6_optimized_lsem_agreeX (body : List Linstr)
    (hb : ∀ i ∈ body, tiedInstrX i = true) (hpa : BodyParseAgrees body)
    {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', gatherJBlock6 body = some g ∧
      lsemStraight (body.map (·.li_i)) ls = some ls' ∧
      LJCorrM ls' (runBlock s (optimizeX86Block g)) := by
  obtain ⟨g, ls', hg, hstep, hc'⟩ := gatherJBlock6_lsem_agreeX body hb hpa hc
  exact ⟨g, ls', hg, hstep, by rw [optimizeX86Block_runBlock]; exact hc'⟩

/-- Every instruction of the body is in the widened fragment. -/
def tiedBodyX (body : List Linstr) : Bool := body.all tiedInstrX

theorem tiedBodyX_mem {body : List Linstr} (h : tiedBodyX body = true) :
    ∀ i ∈ body, tiedInstrX i = true := fun i hi => (List.all_eq_true.1 h) i hi

/-! ## 11. A worked body

`demoBodyX` is `RAX := RDI; RAX <<= 3; RCX := (RAX <ᵤ RSI); RDX := RDI[RCX*8];
RDI[RCX*8] := RAX`, one instruction of each new arm beside a `MOV:64`. -/

/-- A body with a move, an in-place shift, a materialised compare, an indexed
    load and an indexed store. -/
def demoBodyX : List Linstr :=
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SHL:3:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "RCX"] "SETB:64" [.reg "RAX", .reg "RSI"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "LOADIDX" [.arrIdx "RDI" "RCX" 8]⟩,
    ⟨0, .Lopn [.reg "arr"] "STOREIDX" [.arrIdx "RDI" "RCX" 8, .reg "RAX"]⟩ ]

theorem demoBodyX_tied : tiedBodyX demoBodyX = true := by decide +kernel

/-- The parse hypothesis of `demoBodyX` reduces to the one shift mnemonic. -/
theorem demoBodyX_parseAgrees
    (hp : ∃ wd, parseImmShiftMnem "SHL:3" = some ("shl", 3, wd)) :
    BodyParseAgrees demoBodyX := by
  intro i hi
  simp only [demoBodyX, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> intro k n hk <;> simp only [mnemOf] at hk
  · rw [immShiftOf_MOV] at hk; cases hk
  · have h3 : immShiftOf "SHL:3:64" = some (.shl, 3) := by decide +kernel
    rw [h3] at hk
    cases hk
    have hs : stripWidthTag "SHL:3:64" = "SHL:3" := by decide +kernel
    show ∃ wd, parseImmShiftMnem (stripWidthTag "SHL:3:64") = some (ShiftKind.shl.att, 3, wd)
    rw [hs]
    exact hp
  · have : immShiftOf "SETB:64" = none := by decide +kernel
    rw [this] at hk; cases hk
  · have : immShiftOf "LOADIDX" = none := by decide +kernel
    rw [this] at hk; cases hk
  · have : immShiftOf "STOREIDX" = none := by decide +kernel
    rw [this] at hk; cases hk

/-- The widened tie on `demoBodyX`. -/
theorem demoBodyX_agree (hp : ∃ wd, parseImmShiftMnem "SHL:3" = some ("shl", 3, wd))
    {ls : Lstate 64} {s : JState 64} (hc : LJCorrM ls s) :
    ∃ g ls', gatherJBlock6 demoBodyX = some g ∧
      lsemStraight (demoBodyX.map (·.li_i)) ls = some ls' ∧ LJCorrM ls' (runBlock s g) :=
  gatherJBlock6_lsem_agreeX demoBodyX (tiedBodyX_mem demoBodyX_tied) (demoBodyX_parseAgrees hp) hc

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherLsemTieExt
