/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote

/-!
# Source→machine bridge: the CONSTANT-TIME conditional SELECT (`RSelect` → `cmov`)

This module extends the `LowCT`→`JInstr` constant-time bridge
(`LowCTToJInstrCT.lean` for scalar arith, `LowCTMemDenote.lean` for the
memory/array fragment) to the **branchless conditional**: the `LowCT` source
node

  `RSelect dst sel src0 src1`  —  `dst := if sel = 0 then src0 else src1`

(`LowCT.lean`'s Phase-H constructor; `RustExec.selectFalse`/`selectTrue` give
its operational semantics, and `cmdCT`'s `RSelect` arm gives the source CT
verdict).  This rounds out **control flow** on the bounded fragment.

## Why this is the constant-time conditional

`RSelect` is the *constant-time SELECT*: both source values are read regardless
of `sel`, and the choice is made by a data-flow `cmov`, not a branch.  We lower
it to a **branchless** machine schedule built from `mov`/`and_`/`cmove` — there
is **no secret-dependent control flow**, which is exactly the CT-correct way to
compile a conditional in cryptographic code.

General branching (`RIfNz` with real `jcc`/`jmp`) would need branch
instructions absent from the modeled `JInstr` subset, and on a secret condition
would be non-constant-time anyway.  `RSelect`/`cmov` is the CT-discipline
conditional and the right compilation target.

## The branchless schedule

For `dst := if sel = 0 then src0 else src1`, with registers `ρ`:

```
  mov   ρdst, ρsrc1     -- default: dst := src1
  and_  ρsel, ρsel      -- set ZF = (sel == 0); value of ρsel unchanged (r &&& r = r)
  cmove ρdst, ρsrc0     -- if ZF (i.e. sel == 0) then dst := src0, else keep src1
```

The middle `and_ r r` is the flag-setter: `x86_AND r r = r &&& r = r` leaves the
data word of `ρsel` unchanged but sets `ZF = ZF_of_word r = decide(r.toNat = 0)`,
i.e. `ZF` is true iff `sel = 0` (under the in-range guard `sel < 2^64`).  The
machine `cmove dst src` is `Ox86_CMOVcc` reading `ZF`:
`if ZF then dst := src else dst unchanged` (`evalInstr` arm at
`JasminModel.lean`).  Composing them realises the source `RSelect` exactly.

Every emitted instruction is `IsDirect` (no `loadMemIdx`/`storeMemIdx`), so the
machine constant-time obligation is the straight-line `allDirect_constant_time`
case — the branchless property the whole exercise is about.

## What is proved

* `SelectSrc.toLowCT` — the embedding into the **real** `LowCT.RSelect` node,
  with `cmdCT_iff` recording the source CT verdict (all three tower slots
  `Public`).
* `lowerSelect` — the branchless `mov; and_; cmove` schedule.
* `lowerSelect_allDirect` / `lowerSelect_constant_time` — machine constant-time
  (the easy genuine half): branchless ⇒ no branch-channel leakage.
* `selectFlag_zf` — **the flag crux**: after `and_ r r`, `ZF` is
  `decide ((s.get r).toNat = 0)`, and `r`'s value is unchanged.
* `lowerSelect_denote` — denotation preservation: under register/tower
  correspondence (`StateMatch` for the scalar `sel`, `LocMatch` for the
  single-word tower slots `dst`/`src0`/`src1`), an injectivity/disjointness WF
  condition, and the in-range guard `sel < 2^64`, the machine run of the
  lowering computes `dst := if sel = 0 then src0 else src1` at the word level,
  matching the source `RustExec.RSelect` post-state.  Cases on `sel = 0`.
* `lowerSelect_denote_rustExec` — the tie to the real `RustExec` operational
  semantics (`selectFalse`/`selectTrue`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTSelectCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTMemDenote
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 1. The select source fragment (a faithful `LowCT` subset)

A single conditional select on **single-word tower slots** of the same tower
type `t`: `dst := if sel = 0 then src0 else src1`.  The slots are modeled at the
word level via `LowCTMemDenote.valWord` (byte offset `0`), exactly as the
memory-fragment bridge models the `mov`-into-data-register value. -/

/-- The conditional-select source fragment: `dst := if sel = 0 then src0 else
    src1`, where `dst`, `src0`, `src1` are single-word tower slots of a common
    tower type `t`, and `sel` is a scalar slot.  A faithful subset of
    `LowCT.RSelect`. -/
structure SelectSrc where
  /-- The common tower type of the three value slots. -/
  t    : TowerType
  dst  : String
  sel  : String
  src0 : String
  src1 : String

/-- The destination `Located`. -/
def SelectSrc.dstLoc (p : SelectSrc) : Located := ⟨p.dst, p.t⟩
/-- The `sel = 0` branch `Located`. -/
def SelectSrc.src0Loc (p : SelectSrc) : Located := ⟨p.src0, p.t⟩
/-- The `sel ≠ 0` branch `Located`. -/
def SelectSrc.src1Loc (p : SelectSrc) : Located := ⟨p.src1, p.t⟩

/-! ## 2. Embedding into real `LowCT` -/

/-- **The embedding into real `LowCT`.**  A `SelectSrc` is the genuine
    `LowCT.RSelect dst sel src0 src1` node.  This is what makes the fragment
    non-toy: the source object whose CT we analyse and whose semantics we track
    is a real `LowCT` command, with the real `cmdCT` verdict and the real
    `RustExec` step. -/
def SelectSrc.toLowCT (p : SelectSrc) : LowCT :=
  .RSelect p.dstLoc p.sel p.src0Loc p.src1Loc

/-- The source CT verdict for a `SelectSrc`, via the **real** `cmdCT`.  As the
    Phase-J analyser records, `RSelect` is CT *by construction* (a `cmov`: both
    branch values are read regardless of `sel`), so the verdict checks only that
    the three tower slots `dst`, `src0`, `src1` are `Public`; crucially it does
    **not** require `sel` public — the choice never becomes a branch. -/
theorem SelectSrc.cmdCT_iff (p : SelectSrc) (lt : LevelTable) (leafCT : LeafCTTable) :
    cmdCT p.toLowCT lt leafCT = true ↔
      (lt p.dst == .Public) ∧ (lt p.src0 == .Public) ∧ (lt p.src1 == .Public) := by
  simp only [SelectSrc.toLowCT, cmdCT_RSelect, SelectSrc.dstLoc, SelectSrc.src0Loc,
    SelectSrc.src1Loc, Bool.and_eq_true, and_assoc]

/-! ## 3. The branchless lowering to `JInstr 64` -/

/-- **The branchless lowering.**  `dst := if sel = 0 then src0 else src1` lowers
    to the three-instruction *branchless* schedule
    `mov ρdst ρsrc1 ; and_ ρsel ρsel ; cmove ρdst ρsrc0`.  No `jcc`/`jmp`: the
    conditional is realised by `cmov` reading `ZF` set from `sel`.  Memory-free:
    only register `mov`/`and_`/`cmove` — no `loadMemIdx`/`storeMemIdx`. -/
def lowerSelect (ρ : RegMap) (p : SelectSrc) : List (JInstr 64) :=
  [ .mov   (ρ p.dst) (.reg (ρ p.src1))
  , .and_  (ρ p.sel) (.reg (ρ p.sel))
  , .cmove (ρ p.dst) (.reg (ρ p.src0)) ]

/-! ## 4. Machine constant-time (the easy genuine half) -/

/-- Every emitted instruction of the lowering is `IsDirect` (only
    `loadMemIdx`/`storeMemIdx` are non-direct, and the branchless schedule emits
    neither).  Hence the schedule is *branchless* in the machine-CT sense: its
    leakage channel carries no branch. -/
theorem lowerSelect_allDirect (ρ : RegMap) (p : SelectSrc) :
    allDirect (lowerSelect ρ p) = true := by
  cases p; rfl

/-- **Source→machine constant-time.**  The branchless lowering of *any* select
    source command produces the **same** machine leakage trace from any two
    initial states: there is no secret-dependent control flow (the `cmov`
    schedule takes no branch), so the observable trace is a function of the
    program text alone.  Delivered by the machine keystone
    `allDirect_constant_time`. -/
theorem lowerSelect_constant_time (ρ : RegMap) (p : SelectSrc) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSelect ρ p) = blockLeak s₂ (lowerSelect ρ p) :=
  allDirect_constant_time (lowerSelect ρ p) (lowerSelect_allDirect ρ p) s₁ s₂

/-- `mov d (.reg src)` reads `src` into `d`: any other register `r ≠ d` is
    unchanged. -/
theorem mov_get_other (s : JState 64) (d src r : String) (h : r ≠ d) :
    (evalInstr s (.mov d (.reg src))).get r = s.get r := by
  simp only [evalInstr, JOperand.eval, x86_MOV, JState.get_setReg_other _ _ _ _ h]

/-- `mov d (.reg src)` writes `src`'s value into `d`. -/
theorem mov_get_same (s : JState 64) (d src : String) :
    (evalInstr s (.mov d (.reg src))).get d = s.get src := by
  simp only [evalInstr, JOperand.eval, x86_MOV, JState.get_setReg_same]

/-! ## 5. The flag crux: `and_ r r` sets `ZF = (r == 0)` and preserves `r` -/

/-- **The flag-setter, value side.**  `and_ r r` leaves `r`'s data word
    unchanged: `x86_AND r r = r &&& r = r`. -/
theorem selectFlag_value (s : JState 64) (r : String) :
    (evalInstr s (.and_ r (.reg r))).get r = s.get r := by
  simp only [evalInstr, JOperand.eval, JState.get_writeB5W_same, x86_AND,
    rflags_of_bwop, BitVec.and_self]

/-- **The flag-setter, value side (other registers).**  `and_ r r` writes only
    `r`; any other register `r' ≠ r` is unchanged. -/
theorem selectFlag_value_other (s : JState 64) (r r' : String) (h : r' ≠ r) :
    (evalInstr s (.and_ r (.reg r))).get r' = s.get r' := by
  simp only [evalInstr, JOperand.eval]
  simp [JState.writeB5W, JState.get, h]

/-- **The flag-setter, value side (any register).**  `and_ r r` is value-pure:
    it preserves the data word of *every* register (including `r` itself, since
    `r &&& r = r`).  Only the flags change.  This is what lets the flag-setter be
    inserted between the `mov` and the `cmove` without disturbing any value. -/
theorem selectFlag_value_any (s : JState 64) (r r' : String) :
    (evalInstr s (.and_ r (.reg r))).get r' = s.get r' := by
  by_cases h : r' = r
  · rw [h]; exact selectFlag_value s r
  · exact selectFlag_value_other s r r' h

/-- **The flag crux.**  After `and_ r r`, the zero flag is exactly
    `decide ((s.get r).toNat = 0)` — true iff `r`'s value is zero.  This is the
    flag the subsequent `cmove` reads to realise the select. -/
theorem selectFlag_zf (s : JState 64) (r : String) :
    (evalInstr s (.and_ r (.reg r))).flagB (·.zf)
      = decide ((s.get r).toNat = 0) := by
  simp only [evalInstr, JOperand.eval, JState.flagB, JState.writeB5W_flags,
    x86_AND, rflags_of_bwop, ZF_of_word, BitVec.and_self, Option.getD_some]

/-! ## 6. State correspondence and denotation preservation

The scalar `sel` is tracked by the imported `StateMatch` (machine register
`ρ sel` holds the 64-bit truncation of `rs.rsScalar sel`).  The three tower
slots `dst`/`src0`/`src1` are tracked at the word level by `LocMatch`: the
machine register `ρ loc.locVar` holds `valWord` of the source tower value. -/

/-- **Single-word tower correspondence.**  The machine register `ρ loc.locVar`
    holds the word-0 value (`valWord`) of the source tower slot `loc`, whenever
    that slot is present.  The single-register analogue of `LowCTMemDenote`'s
    `MemMatch` for a scalar (non-array) tower slot — what `cmov`'s single-register
    move operates on. -/
def LocMatch (ρ : RegMap) (loc : Located) (rs : RustState) (js : JState 64) : Prop :=
  ∀ v : RustVal loc.locDst, locatedLookup rs loc = some v →
    js.get (ρ loc.locVar) = valWord v

/-- `valWord` is invariant under the `RustExec` type cast `h ▸ v`: both read the
    little-endian word at byte offset `0`, independent of the tower-type index. -/
theorem valWord_cast {t₁ t₂ : TowerType} (h : t₁ = t₂) (v : RustVal t₁) :
    valWord (h ▸ v) = valWord v := by
  subst h; rfl

/-- After the branchless schedule, the destination register holds the selected
    word.  This is the machine-side denotation; `lowerSelect_denote` ties it to
    the source `RustExec` post-state.

    Hypotheses (register-allocation well-formedness + the in-range guard):
    * `ρ` injective — distinct source slots get distinct machine registers;
    * `p.sel ≠ p.dst`, `p.src0 ≠ p.dst` — the flag-set and the cmov source are
      not the destination, so the `mov` priming `ρdst := ρsrc1` survives;
    * `selV < 2^64` — the source `sel` value is in machine range, so
      `ZF = (sel = 0)` matches the source `sel = 0` test exactly. -/
theorem lowerSelect_denote_reg (ρ : RegMap) (p : SelectSrc) (js : JState 64)
    (selV : Nat) (w0 w1 : BitVec 64)
    (hsel : js.get (ρ p.sel) = BitVec.ofNat 64 selV) (hselR : selV < 2 ^ 64)
    (hs0 : js.get (ρ p.src0) = w0) (hs1 : js.get (ρ p.src1) = w1)
    (hρ : Function.Injective ρ) (hseld : p.sel ≠ p.dst) (hs0d : p.src0 ≠ p.dst) :
    (runBlock js (lowerSelect ρ p)).get (ρ p.dst)
      = (if selV = 0 then w0 else w1) := by
  -- register disequalities from injectivity
  have hseldR : ρ p.sel ≠ ρ p.dst := fun h => hseld (hρ h)
  have hs0dR : ρ p.src0 ≠ ρ p.dst := fun h => hs0d (hρ h)
  -- abbreviations for the two intermediate states
  let s1 : JState 64 := evalInstr js (.mov (ρ p.dst) (.reg (ρ p.src1)))
  let s2 : JState 64 := evalInstr s1 (.and_ (ρ p.sel) (.reg (ρ p.sel)))
  have hrun : runBlock js (lowerSelect ρ p)
      = evalInstr s2 (.cmove (ρ p.dst) (.reg (ρ p.src0))) := rfl
  rw [hrun]
  -- ZF after `and_ ρsel ρsel`, evaluated at s2, equals `decide (selV = 0)`.
  have hsel1 : s1.get (ρ p.sel) = BitVec.ofNat 64 selV := by
    show (evalInstr js (.mov (ρ p.dst) (.reg (ρ p.src1)))).get (ρ p.sel) = _
    rw [mov_get_other _ _ _ _ hseldR]; exact hsel
  have hzf : s2.flagB (·.zf) = decide (selV = 0) := by
    show (evalInstr s1 (.and_ (ρ p.sel) (.reg (ρ p.sel)))).flagB (·.zf) = _
    rw [selectFlag_zf, hsel1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hselR]
  -- src0 register value at s2 (untouched by both `mov` and `and_`)
  have hsrc0_s2 : s2.get (ρ p.src0) = w0 := by
    show (evalInstr s1 (.and_ (ρ p.sel) (.reg (ρ p.sel)))).get (ρ p.src0) = w0
    rw [selectFlag_value_any]
    show (evalInstr js (.mov (ρ p.dst) (.reg (ρ p.src1)))).get (ρ p.src0) = w0
    rw [mov_get_other _ _ _ _ hs0dR]; exact hs0
  -- dst register value at s2 (set by `mov` to w1, untouched by `and_`)
  have hdst_s2 : s2.get (ρ p.dst) = w1 := by
    show (evalInstr s1 (.and_ (ρ p.sel) (.reg (ρ p.sel)))).get (ρ p.dst) = w1
    rw [selectFlag_value_any]
    show (evalInstr js (.mov (ρ p.dst) (.reg (ρ p.src1)))).get (ρ p.dst) = w1
    rw [mov_get_same]; exact hs1
  -- evaluate the cmove: dst := if ZF then src0 else dst-so-far
  show (evalInstr s2 (.cmove (ρ p.dst) (.reg (ρ p.src0)))).get (ρ p.dst) = _
  simp only [evalInstr, JOperand.eval, x86_CMOVcc, JState.get_setReg_same, hzf]
  rw [hsrc0_s2, hdst_s2]
  by_cases hz : selV = 0 <;> simp [hz]

/-! ## 7. Denotation against the real `RustExec` post-state

`lowerSelect_denote_rustExec` ties `lowerSelect_denote_reg` to the genuine
`LowCT.RSelect` operational semantics (`RustExec.selectFalse`/`selectTrue`):
the machine run of the branchless schedule lands the destination register on
`valWord` of the source post-state's `dst` slot — i.e. the lowered `cmov`
schedule realises `dst := if sel = 0 then src0 else src1` exactly. -/

/-- A located lookup recovers the value just written to the same slot. -/
theorem locatedLookup_locatedUpdate_self (rs : RustState) (loc : Located)
    (v : RustVal loc.locDst) :
    locatedLookup (locatedUpdate rs loc v) loc = some v := by
  unfold locatedLookup
  rw [locatedUpdate_dest]
  simp

/-- **Denotation preservation, against the real `RustExec` (the hard half).**
    Under the register/tower correspondence (`StateMatch` for the scalar `sel`,
    `LocMatch` for the single-word value slots `src0`/`src1`), the
    register-allocation WF conditions (`ρ` injective, `sel ≠ dst`, `src0 ≠ dst`),
    and the in-range guard `rs.rsScalar p.sel < 2^64`, the machine run of the
    branchless lowering ends with the destination register holding `valWord` of
    the source post-state's `dst` slot — for the unique post-state `rs'` the real
    `RustExec` reaches on `p.toLowCT`.  This is the source-operational-semantics
    ⇒ machine-run correspondence: the `cmov` schedule computes the select. -/
theorem lowerSelect_denote_rustExec (N : Nat) (leafSpec : LeafSpec)
    (ρ : RegMap) (p : SelectSrc) (rs rs' : RustState) (js : JState 64)
    (srcV0 : RustVal p.src0Loc.locDst) (srcV1 : RustVal p.src1Loc.locDst)
    (hρ : Function.Injective ρ) (hseld : p.sel ≠ p.dst) (hs0d : p.src0 ≠ p.dst)
    (hselR : rs.rsScalar p.sel < 2 ^ 64)
    (hmatchSel : StateMatch ρ rs js)
    (hlook0 : locatedLookup rs p.src0Loc = some srcV0)
    (hlook1 : locatedLookup rs p.src1Loc = some srcV1)
    (hmatch0 : js.get (ρ p.src0) = valWord srcV0)
    (hmatch1 : js.get (ρ p.src1) = valWord srcV1)
    (hexec : RustExec N leafSpec p.toLowCT rs rs') :
    LocMatch ρ p.dstLoc rs' (runBlock js (lowerSelect ρ p)) := by
  -- the register-level computation: dst := if selV = 0 then valWord srcV0 else valWord srcV1
  have hreg := lowerSelect_denote_reg ρ p js (rs.rsScalar p.sel)
    (valWord srcV0) (valWord srcV1) (hmatchSel p.sel) hselR hmatch0 hmatch1
    hρ hseld hs0d
  -- read off rs' from the operational step
  intro v hv
  cases hexec with
  | selectFalse dst sel src0 src1 _rs h srcV hsel0 hslook =>
    -- `sel = 0` branch: rs' = locatedUpdate rs dstLoc (h ▸ srcV), srcV = srcV0
    have hsrcEq : srcV = srcV0 := Option.some.inj (hslook.symm.trans hlook0)
    rw [locatedLookup_locatedUpdate_self] at hv
    have hvEq : v = h ▸ srcV := Option.some.inj hv.symm
    show (runBlock js (lowerSelect ρ p)).get (ρ p.dst) = _
    rw [hvEq, hsrcEq, hreg, if_pos hsel0]; exact valWord_cast h srcV0
  | selectTrue dst sel src0 src1 _rs h vv srcV hselv hvne hslook =>
    -- `sel ≠ 0` branch: rs' = locatedUpdate rs dstLoc (h ▸ srcV), srcV = srcV1
    have hsrcEq : srcV = srcV1 := Option.some.inj (hslook.symm.trans hlook1)
    rw [locatedLookup_locatedUpdate_self] at hv
    have hvEq : v = h ▸ srcV := Option.some.inj hv.symm
    have hne : rs.rsScalar p.sel ≠ 0 := by rw [hselv]; exact hvne
    show (runBlock js (lowerSelect ρ p)).get (ρ p.dst) = _
    rw [hvEq, hsrcEq, hreg, if_neg hne]; exact valWord_cast h srcV1

/-- **Denotation preservation (the hard half), against the explicit select
    post-state.**  Specialises `lowerSelect_denote_rustExec` to the canonical
    post-state of `dst := if sel = 0 then src0 else src1`: the destination slot is
    updated with `src0`'s value when `sel = 0`, with `src1`'s value otherwise.
    The machine run of the branchless lowering lands `ρ dst` on `valWord` of that
    updated slot. -/
theorem lowerSelect_denote (N : Nat) (leafSpec : LeafSpec)
    (ρ : RegMap) (p : SelectSrc) (rs : RustState)
    (js : JState 64) (h : p.src0Loc.locDst = p.dstLoc.locDst)
    (h' : p.src1Loc.locDst = p.dstLoc.locDst)
    (srcV0 : RustVal p.src0Loc.locDst) (srcV1 : RustVal p.src1Loc.locDst)
    (hρ : Function.Injective ρ) (hseld : p.sel ≠ p.dst) (hs0d : p.src0 ≠ p.dst)
    (hselR : rs.rsScalar p.sel < 2 ^ 64)
    (hmatchSel : StateMatch ρ rs js)
    (hlook0 : locatedLookup rs p.src0Loc = some srcV0)
    (hlook1 : locatedLookup rs p.src1Loc = some srcV1)
    (hmatch0 : js.get (ρ p.src0) = valWord srcV0)
    (hmatch1 : js.get (ρ p.src1) = valWord srcV1) :
    LocMatch ρ p.dstLoc
      (locatedUpdate rs p.dstLoc
        (if _hz : rs.rsScalar p.sel = 0 then h ▸ srcV0 else h' ▸ srcV1))
      (runBlock js (lowerSelect ρ p)) := by
  by_cases hz : rs.rsScalar p.sel = 0
  · -- `sel = 0`: the real `RustExec.selectFalse` step reaches this post-state.
    have hexec : RustExec N leafSpec p.toLowCT rs
        (locatedUpdate rs p.dstLoc (h ▸ srcV0)) :=
      RustExec.selectFalse p.dstLoc p.sel p.src0Loc p.src1Loc rs h srcV0 hz hlook0
    have := lowerSelect_denote_rustExec N leafSpec ρ p rs _ js
      srcV0 srcV1 hρ hseld hs0d hselR hmatchSel hlook0 hlook1 hmatch0 hmatch1 hexec
    simpa [hz] using this
  · -- `sel ≠ 0`: the real `RustExec.selectTrue` step reaches this post-state.
    have hexec : RustExec N leafSpec p.toLowCT rs
        (locatedUpdate rs p.dstLoc (h' ▸ srcV1)) :=
      RustExec.selectTrue p.dstLoc p.sel p.src0Loc p.src1Loc rs h'
        (rs.rsScalar p.sel) srcV1 rfl hz hlook1
    have := lowerSelect_denote_rustExec N leafSpec ρ p rs _ js
      srcV0 srcV1 hρ hseld hs0d hselR hmatchSel hlook0 hlook1 hmatch0 hmatch1 hexec
    simpa [hz] using this

/-! ## 8. Source CT verdict ⇒ machine constant-time, end to end

A `SelectSrc` whose `cmdCT` verdict is `true` lowers to a machine block that is
constant-time (same leakage trace from any two states).  As in the scalar-arith
and memory bridges, the `cmdCT` hypothesis is consumed on the source side; the
machine-CT conclusion is unconditional for this branchless fragment — the whole
point of `RSelect` being the CT conditional. -/

/-- **Source CT verdict ⇒ machine constant-time.**  If the source command
    `p.toLowCT` passes the real source CT analyser `cmdCT` (all three value slots
    `Public`; `sel` need not be — the choice never becomes a branch), its
    branchless lowering is constant-time at the machine level. -/
theorem lowerSelect_source_to_machine_CT (ρ : RegMap) (p : SelectSrc)
    (lt : LevelTable) (leafCT : LeafCTTable)
    (_hsrc : cmdCT p.toLowCT lt leafCT = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerSelect ρ p) = blockLeak s₂ (lowerSelect ρ p) :=
  lowerSelect_constant_time ρ p s₁ s₂
