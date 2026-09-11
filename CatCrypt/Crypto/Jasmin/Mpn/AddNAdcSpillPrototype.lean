/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

@[expose] public section

set_option autoImplicit false

/-!
# ADC-spill carry variant of the verified `mpn_add_n` loop

**EXPERIMENTAL FILE.**  Companion to `Mpn.AddPrototype.lean` and
`Mpn.AddOpenCarryPrototype.lean`.  Same verified `mpn_add_n` (add two
equal-length limb arrays with carry), but the loop body uses the real x86
`#ADC_64` intrinsic with an explicit carry-spill through a GPR `cc` across
the `while (n != 0)` back-edge.

## The carry-spill, in InstrR

The committed `Mpn.AddPrototype.body` runs the carry through `#ADC_64(t, s, cf)`,
threading the architectural CF flag across the back-edge.  `jasminc`'s
register allocator rejects this — the carry-out and the live carry-in cannot
both occupy the architectural CF register across the loop merge.  The
standard remedy is to spill the carry to a general-purpose register between
iterations.  This file **embeds that spill in the InstrR AST itself** rather
than as a textual `.jazz` post-process.

The loop body becomes (with `cc : reg u64` initialized to `0` before the
loop):

```
t  := [:u64 ap + 0]
s  := [:u64 bp + 0]
_, cf, _, _, _, cc := #ADD_64(cc, 0xFFFFFFFFFFFFFFFF)   -- reload: cf := (cc != 0)
_, cf, _, _, _, r  := #ADC_64(t, s, cf)                  -- the real ADC
cc := 0
_, cf, _, _, _, cc := #ADC_64(cc, cc, cf)                -- spill: cc := cf as a value
[:u64 op + 0] := r
ap += 8; bp += 8; op += 8; n -= 1
```

At loop entry of iteration `i`, `cc` holds the carry-in for limb `i` (as a
`BitVec 64`, value 0 or 1).  The reload-CF sequence reconstructs CF from
`cc` (since for `cc ∈ {0,1}`, `addCarry cc (-1)` gives `cf = cc`).  The real
ADC then updates `r` and sets CF; the spill-CF sequence captures CF back
into `cc` (since `addCarryIn 0 0 cf = (0, cf)` for `cf ∈ {0,1}`).  Net
effect per iteration: `(r, cc') = (a[i] + b[i] + cc) split at 2^64` —
exactly the `addCarryIn` semantics.

## Why this exists

The previous three bench directories (`bench/gmp_diff/`, `bench/gmp_bench/`,
`bench/gmp_perf/` via a textually-spliced `fixupAdcSpill`) materialized the
spill as a string-level post-process at the `.jazz` boundary, which is
*not* machine-verified.  This file moves the spill into the InstrR AST so
the bridge `MpnAddNAdcSpillJasminRefines` is a verified denotation
preservation result: the emitted `.jazz` (produced by `emitFunDecl`
unchanged) refines the pure `mpnAddN` reference.

The on-chip effect is unchanged: one real `adcq` per limb with the carry
threaded through a GPR across the back-edge — the same `~37%` per-limb
cost drop versus the open-coded `MpnAddOpenCarryPrototype` form.

## Reuse from `MpnAddPrototype`

Everything *except* the per-iteration step lemma is reused: the limb-list
denotation `toNat`, the pure reference `mpnAddN`, the carry-chain spec
`mpnAddN_spec`, the memory algebra (`load64Mem_store64_*`), the ADC bridge
(`addCarryIn_sum` / `addCarryIn_carry`), and all of §8–§9's loop-guard /
fuel rules.  The new content is one bridge fact about the spill triple
(`spill_triple_eq_adc`) and the per-iteration step lemma adapted to the
extra straight-line instructions.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.AddNAdcSpillPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-! ## §1  The ADC-spill Jasmin `mpn_add_n` body -/

/-- `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]`. -/
def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- Memory store `[:u64 base + 0] := src`. -/
def storeAt0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst 0)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r += k` / `r -= k` scalar update. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- The standard SUB/ADD/ADC 6-LVal flag bundle, with only the carry-out
    slot (position 1) and the destination (position 5) named.  Used for
    every `#ADD_64`/`#ADC_64` in the spill body. -/
def subBundle (cfName dstName : String) : List LVal :=
  [.Lnone {} (.sword .U64),
   .Lvar { var := vr cfName },
   .Lnone {} (.sword .U64),
   .Lnone {} (.sword .U64),
   .Lnone {} (.sword .U64),
   .Lvar { var := vr dstName }]

/-- `_, cf, _, _, _, cc := #ADD_64(cc, -1)` — the reload-CF sequence.
    Adds `-1 = 0xFF..FF` to `cc`; the carry-out `cf` ends up `1` iff
    `cc ≠ 0` (i.e., `cf = cc` when `cc ∈ {0,1}`).  `cc` is also
    overwritten but the next instruction resets it. -/
def reloadCf : InstrR :=
  .Copn (subBundle "cf" "cc") .AT_none (.Oasm ⟨"ADD_64"⟩)
        [pv "cc", .Pconst (-1)]

/-- `_, cf, _, _, _, r := #ADC_64(t, s, cf)` — the real ADC. -/
def adcCore : InstrR :=
  .Copn (subBundle "cf" "r") .AT_none (.Oasm ⟨"ADC_64"⟩)
        [pv "t", pv "s", pv "cf"]

/-- `cc := 0` — clear `cc` before the spill. -/
def clearCc : InstrR :=
  .Cassgn (.Lvar { var := vr "cc" }) .AT_none (.sword .U64) (.Pconst 0)

/-- `_, cf, _, _, _, cc := #ADC_64(cc, cc, cf)` — the spill-CF sequence.
    With `cc = 0` (from `clearCc`) and `cf ∈ {0,1}`, this computes
    `cc := 0 + 0 + cf = cf` — capturing the architectural carry into
    a GPR for the next iteration. -/
def spillCf : InstrR :=
  .Copn (subBundle "cf" "cc") .AT_none (.Oasm ⟨"ADC_64"⟩)
        [pv "cc", pv "cc", pv "cf"]

/-- One ADC-spill loop iteration. -/
def loopBody : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , reloadCf
  , adcCore
  , clearCc
  , spillCf
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body: `cc := 0; while (n != 0) { <loopBody> }`. -/
def body : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "cc" }) .AT_none (.sword .U64) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody ]

/-- `mpn_add_n(op, ap, bp, n)` as a `FunDecl`, ADC-spill carry. -/
def mpnAddNAdcSpillFd : FunDecl where
  name := { name := "mpn_add_n_adc" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := body
  results := []

/-- The loop is constant-time-shaped: the guard depends only on the public
    length `n`. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body = true := by decide

/-- Emit the real `.jazz` source. -/
def emitted : Option String := emitFunDecl mpnAddNAdcSpillFd

#eval match emitted with | some s => s | none => "EMIT FAILED"

/-! ## §2  The spill-triple bridge: `(reload, adc, clearCc, spill)` ≡ ADC

The four extra ops fuse to the pure `addCarryIn` semantics: starting from
`cc = ofNat (carryNat cin)` (i.e., `cc ∈ {0,1}`), the four-step sequence
produces the same `(r, cc')` as a single `#ADC_64(t, s, cin)` would
produce — `r = adcStep t s cin`'s sum and `cc' = adcStep`'s carry-out.

We prove the bridge in `BitVec` arithmetic directly: with `cc ∈ {0,1}`,
the reload `#ADD_64(cc, -1)` produces `cf = cc` exactly; the spill
`#ADC_64(0, 0, cf)` produces `cc' = cf, cf' = 0`.  Both are closed by
`bv_decide`. -/

/-- Reload step: `addCarry cc (-1)` produces carry-out `= cc` exactly when
    `cc` is one bit (`cc &&& 1 = cc`).  Pure `BitVec`, closed by
    `bv_decide`. -/
theorem reload_cf_eq (cc : BitVec 64) (hcc : cc &&& 1 = cc) :
    (addCarry cc (-1)).1 = cc := by
  unfold addCarry
  bv_decide

/-- Unconditional spill: `addCarryIn 0 0 cf = (0, cf &&& 1)`.  Pure
    `BitVec`, closed by `bv_decide`. -/
theorem spill_step_raw (cf : BitVec 64) :
    addCarryIn 0 0 cf = (0, cf &&& 1) := by
  unfold addCarryIn
  refine Prod.ext ?_ ?_ <;> bv_decide

/-- Spill step: `addCarryIn 0 0 cf` produces `(0, cf)` when `cf` is one
    bit (`cf &&& 1 = cf`).  Corollary of `spill_step_raw`. -/
theorem spill_step_eq (cf : BitVec 64) (hcf : cf &&& 1 = cf) :
    addCarryIn 0 0 cf = (0, cf) := by
  rw [spill_step_raw, hcf]

/-- `BitVec.ofNat 64 (carryNat c)` is always a one-bit value
    (`x &&& 1 = x`). -/
theorem carryNat_bv_one_bit (c : Bool) :
    (BitVec.ofNat 64 (carryNat c)) &&& 1 = BitVec.ofNat 64 (carryNat c) := by
  unfold carryNat
  cases c <;> bv_decide

/-- Alias matching the `if cin then 1 else 0` form of the carry encoding
    used at loop entry (which is definitionally `carryNat cin`). -/
theorem carryNat_bv_one_bit_alt (c : Bool) :
    (BitVec.ofNat 64 (if c then 1 else 0)) &&& 1
      = BitVec.ofNat 64 (if c then 1 else 0) := by
  cases c <;> bv_decide

/-! ## §3  One ADC-spill iteration as an explicit state update

Mirror of `Mpn.AddPrototype.bignumExec_loopBody_step`, for the ADC-spill
body.  The carry register threaded across iterations is `cc` (a `u64`
GPR), not `cf` (the architectural flag).  Final-state observation: the
stored sum at `op` matches `adcStep`'s sum; `cc` holds `carryNat` of
`adcStep`'s carry-out. -/

/-- Helper lemma: the spill triple's net effect equals one `addCarryIn`
    step.  Given `cc_in` is a one-bit value, the four operations
    `#ADD_64(cc, -1)`, `#ADC_64(t, s, cf)`, `cc := 0`, `#ADC_64(cc, cc, cf)`
    produce sum-register `(adcStep a b cin).1` and carry-register
    `BitVec.ofNat 64 (carryNat (adcStep a b cin).2)`. -/
theorem spill_triple_bridge (a b : BitVec 64) (cin : Bool) :
    let cc_in : BitVec 64 := BitVec.ofNat 64 (if cin then 1 else 0)
    let cf_reload : BitVec 64 := (addCarry cc_in (-1)).1
    let r_adc : BitVec 64 := (addCarryIn a b cf_reload).2
    let cf_adc : BitVec 64 := (addCarryIn a b cf_reload).1
    let cc_spill : BitVec 64 := (addCarryIn 0 0 cf_adc).2
    r_adc = (adcStep a b cin).1 ∧
    cc_spill = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) := by
  intro cc_in cf_reload r_adc cf_adc cc_spill
  have hcc_one : cc_in &&& 1 = cc_in := carryNat_bv_one_bit_alt cin
  have hreload : cf_reload = cc_in := reload_cf_eq cc_in hcc_one
  have hadc_sum : r_adc = (adcStep a b cin).1 := by
    simp only [r_adc, hreload]; exact addCarryIn_sum a b cin
  have hadc_carry : cf_adc = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) := by
    simp only [cf_adc, hreload]; exact addCarryIn_carry a b cin
  have hcf_one_bit :
      BitVec.ofNat 64 (carryNat (adcStep a b cin).2) &&& 1
        = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) :=
    carryNat_bv_one_bit (adcStep a b cin).2
  have hspill : cc_spill = cf_adc := by
    simp only [cc_spill, hadc_carry]
    have := spill_step_eq
      (BitVec.ofNat 64 (carryNat (adcStep a b cin).2)) hcf_one_bit
    rw [this]
  refine ⟨hadc_sum, ?_⟩
  rw [hspill, hadc_carry]

/-! ### Forward append join for `bignumExec`

Reverse direction of `bignumExec_append`: composing two successful runs
gives a successful run of the concatenation.  Inlined here (a copy of
the lemma in `LowCTBorrowCheckInPlace.lean::bignumExec_append_some_local`)
to avoid importing that very large file just for this 10-line proof. -/

theorem bignumExec_append_some_local
    (b1 b2 : List InstrR) (s s_mid s' : BignumState)
    (h1 : bignumExec b1 s = some s_mid)
    (h2 : bignumExec b2 s_mid = some s') :
    bignumExec (b1 ++ b2) s = some s' := by
  induction b1 generalizing s with
  | nil =>
    simp [bignumExec] at h1
    rw [← h1] at h2; simp; exact h2
  | cons i b1' ih =>
    simp [bignumExec] at h1
    cases h_step : execInstr s i with
    | none => rw [h_step] at h1; cases h1
    | some s1 =>
      rw [h_step] at h1
      simp [bignumExec, h_step]
      exact ih s1 h1

/-! ### Chunked execution: split the 11-instruction `loopBody`

The kernel hits a deep-recursion when reducing the entire `loopBody` in a
single goal — too many nested `setReg`/`storeMem` projections.  We split
the body into four chunks and assemble via `bignumExec_append`:

* `chunkLoad`  – the two memory loads `t`, `s`.
* `chunkSpill` – the spill triple (reload, ADC, clear, spill).
* `chunkStore` – the store `[op + 0] = r`.
* `chunkAdv`   – the four pointer/counter advances.

Each chunk's per-step effect is computed individually; the spill-triple
bridge (`spill_triple_bridge`) does the math for `chunkSpill`. -/

/-- The two-load chunk. -/
def chunkLoad : List InstrR :=
  [ loadAt0 "t" "ap", loadAt0 "s" "bp" ]

/-- The spill triple chunk. -/
def chunkSpill : List InstrR :=
  [ reloadCf, adcCore, clearCc, spillCf ]

/-- The output store. -/
def chunkStore : List InstrR := [ storeAt0 "op" "r" ]

/-- The four pointer/counter advances. -/
def chunkAdv : List InstrR :=
  [ binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

theorem loopBody_eq_chunks :
    loopBody = chunkLoad ++ chunkSpill ++ chunkStore ++ chunkAdv := by
  rfl

/-- Effect of one `loadAt0 x base` instruction.  Produces a state with
    `x` set to the loaded value (after `BitVec ↔ UInt64` round-trip),
    memory unchanged. -/
theorem execInstr_loadAt0 (s : BignumState) (x base : String) (v : BitVec 64)
    (hv : load64Mem s.mem (UInt64.ofNat (s.regs base).toNat)
            = some (UInt64.ofNat v.toNat)) :
    execInstr s (loadAt0 x base) = some (setReg s x v) := by
  simp only [loadAt0, execInstr, evalPExpr, pv, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 0 = 0 from rfl]
  rw [show s.regs base + 0 = s.regs base from by bv_decide, hv]
  simp only [bv_uint_roundtrip, bind, Option.bind, Option.bind_some]

/-- Effect of the load chunk.  The load addresses are
    `s.regs "ap"` / `s.regs "bp"` (i.e. `regAddr s _`, after `+0`). -/
theorem chunkLoad_step (s : BignumState) (a b : BitVec 64)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    bignumExec chunkLoad s = some (setReg (setReg s "t" a) "s" b) := by
  have ha' : load64Mem s.mem (UInt64.ofNat (s.regs "ap").toNat)
              = some (UInt64.ofNat a.toNat) := ha
  have hb' : load64Mem s.mem (UInt64.ofNat (s.regs "bp").toNat)
              = some (UInt64.ofNat b.toNat) := hb
  -- Step the two loads via the helper.
  have h0 := execInstr_loadAt0 s "t" "ap" a ha'
  -- After step 0, the bp-load needs the bp register address on `setReg s "t" a`,
  -- which equals `s.regs "bp"` (the "t" set doesn't disturb "bp").
  have hbp_t : (setReg s "t" a).regs "bp" = s.regs "bp" := by simp [setReg]
  have hmem_t : (setReg s "t" a).mem = s.mem := rfl
  have h1 : execInstr (setReg s "t" a) (loadAt0 "s" "bp") =
      some (setReg (setReg s "t" a) "s" b) := by
    apply execInstr_loadAt0
    rw [hbp_t, hmem_t]; exact hb'
  -- Compose via bignumExec definition.
  simp only [chunkLoad, bignumExec, h0, h1]

/-- Each individual instruction in `chunkSpill` evaluates as a single
    `setReg`-chain effect.  Spelled out per op so we never reduce the
    full chunk in one go (which trips the kernel's recursion limit). -/
theorem execInstr_reloadCf (s : BignumState) :
    execInstr s reloadCf = some
      (setReg (setReg s "cf" (addCarry (s.regs "cc") (-1)).1)
        "cc" (addCarry (s.regs "cc") (-1)).2) := by
  simp only [reloadCf, subBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeSubBundle,
             show (BitVec.ofInt 64 (-1) : BitVec 64) = (-1 : BitVec 64) from by bv_decide]

theorem execInstr_adcCore (s : BignumState) :
    execInstr s adcCore = some
      (setReg (setReg s "cf" (addCarryIn (s.regs "t") (s.regs "s") (s.regs "cf")).1)
        "r" (addCarryIn (s.regs "t") (s.regs "s") (s.regs "cf")).2) := by
  simp only [adcCore, subBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeSubBundle]

theorem execInstr_clearCc (s : BignumState) :
    execInstr s clearCc = some (setReg s "cc" 0) := by
  simp only [clearCc, execInstr, evalPExpr, vr,
             show BitVec.ofInt 64 0 = 0 from rfl,
             Option.bind_some, bind, Option.bind]

theorem execInstr_spillCf (s : BignumState) :
    execInstr s spillCf = some
      (setReg (setReg s "cf" (addCarryIn (s.regs "cc") (s.regs "cc") (s.regs "cf")).1)
        "cc" (addCarryIn (s.regs "cc") (s.regs "cc") (s.regs "cf")).2) := by
  simp only [spillCf, subBundle, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind, writeSubBundle]

/-- The witness state at the end of `chunkSpill`, as an explicit
    `setReg`-chain on the input.  Spelled out so the kernel sees a
    bounded term, not a 4-deep chain of `set` bindings. -/
def spillExitState (s : BignumState) : BignumState :=
  -- After reloadCf.
  let s1 := setReg (setReg s "cf" (addCarry (s.regs "cc") (-1)).1)
                   "cc" (addCarry (s.regs "cc") (-1)).2
  -- After adcCore.
  let s2 := setReg (setReg s1 "cf"
              (addCarryIn (s1.regs "t") (s1.regs "s") (s1.regs "cf")).1)
              "r" (addCarryIn (s1.regs "t") (s1.regs "s") (s1.regs "cf")).2
  -- After clearCc.
  let s3 := setReg s2 "cc" 0
  -- After spillCf.
  setReg (setReg s3 "cf"
        (addCarryIn (s3.regs "cc") (s3.regs "cc") (s3.regs "cf")).1)
        "cc" (addCarryIn (s3.regs "cc") (s3.regs "cc") (s3.regs "cf")).2

/-- `chunkSpill` runs to `spillExitState`. -/
theorem chunkSpill_exec (s : BignumState) :
    bignumExec chunkSpill s = some (spillExitState s) := by
  -- chunkSpill = [reloadCf, adcCore, clearCc, spillCf]; the cons rule
  -- of `bignumExec` evaluates each step via `execInstr`. We use
  -- `bignumExec_append_some_local` to chain four single-instruction runs.
  -- Each single-instr run is `bignumExec [i] s = some (effect i s)`.
  have step (i : InstrR) (s' s'' : BignumState)
      (hi : execInstr s' i = some s'') :
      bignumExec [i] s' = some s'' := by
    simp only [bignumExec, hi]
  -- Define the 4 intermediates inline (matching `spillExitState`).
  let s1 := setReg (setReg s "cf" (addCarry (s.regs "cc") (-1)).1)
                  "cc" (addCarry (s.regs "cc") (-1)).2
  let s2 := setReg (setReg s1 "cf"
              (addCarryIn (s1.regs "t") (s1.regs "s") (s1.regs "cf")).1)
              "r" (addCarryIn (s1.regs "t") (s1.regs "s") (s1.regs "cf")).2
  let s3 := setReg s2 "cc" 0
  let s4 := setReg (setReg s3 "cf"
              (addCarryIn (s3.regs "cc") (s3.regs "cc") (s3.regs "cf")).1)
              "cc" (addCarryIn (s3.regs "cc") (s3.regs "cc") (s3.regs "cf")).2
  have h1 := step reloadCf s s1 (execInstr_reloadCf s)
  have h2 := step adcCore s1 s2 (execInstr_adcCore s1)
  have h3 := step clearCc s2 s3 (execInstr_clearCc s2)
  have h4 := step spillCf s3 s4 (execInstr_spillCf s3)
  have e12 : bignumExec ([reloadCf] ++ [adcCore]) s = some s2 :=
    bignumExec_append_some_local [reloadCf] [adcCore] s s1 s2 h1 h2
  have e123 : bignumExec ([reloadCf] ++ [adcCore] ++ [clearCc]) s = some s3 :=
    bignumExec_append_some_local _ [clearCc] s s2 s3 e12 h3
  have e1234 : bignumExec ([reloadCf] ++ [adcCore] ++ [clearCc] ++ [spillCf]) s = some s4 :=
    bignumExec_append_some_local _ [spillCf] s s3 s4 e123 h4
  -- chunkSpill = [reloadCf, adcCore, clearCc, spillCf] = above concatenation.
  have hchunk : chunkSpill = [reloadCf] ++ [adcCore] ++ [clearCc] ++ [spillCf] := rfl
  rw [hchunk]
  rw [e1234]
  rfl

/-- The spill chunk threads the carry value from `cc` (one-bit) through
    a `#ADD_64`/`#ADC_64`/clear/`#ADC_64` quadruple, producing `r =
    adcStep` sum and `cc = adcStep` carry-out in the named registers. -/
theorem chunkSpill_step (s : BignumState) (t s_op : BitVec 64) (cin : Bool)
    (ht : s.regs "t" = t) (hs : s.regs "s" = s_op)
    (hcc : s.regs "cc" = BitVec.ofNat 64 (if cin then 1 else 0)) :
    bignumExec chunkSpill s = some (spillExitState s) ∧
    (spillExitState s).mem = s.mem ∧
    (spillExitState s).regs "r" = (adcStep t s_op cin).1 ∧
    (spillExitState s).regs "cc" = BitVec.ofNat 64 (carryNat (adcStep t s_op cin).2) ∧
    (∀ x, x ≠ "r" → x ≠ "cc" → x ≠ "cf" → (spillExitState s).regs x = s.regs x) := by
  have ⟨hsum_eq, hcry_eq⟩ := spill_triple_bridge t s_op cin
  refine ⟨chunkSpill_exec s, ?_, ?_, ?_, ?_⟩
  · -- memory.  `spillExitState` only does `setReg`s, which preserve `.mem`.
    show (spillExitState s).mem = s.mem
    simp only [spillExitState, setReg]
  · -- r-register.
    show (spillExitState s).regs "r" = (adcStep t s_op cin).1
    simp only [spillExitState, setReg_regs, String.reduceEq, ↓reduceIte, reduceIte,
               if_true, if_false, ht, hs, hcc, hsum_eq]
  · -- cc-register.
    show (spillExitState s).regs "cc"
          = BitVec.ofNat 64 (carryNat (adcStep t s_op cin).2)
    simp only [spillExitState, setReg_regs, String.reduceEq, ↓reduceIte, reduceIte,
               if_true, if_false, ht, hs, hcc, hcry_eq]
  · -- Frame.
    intro x hxr hxcc hxcf
    show (spillExitState s).regs x = s.regs x
    simp only [spillExitState, setReg_regs, hxr, hxcc, hxcf,
               ↓reduceIte, if_false]

/-- The store chunk: writes `s.regs "r"` to `[op + 0]`.  Only memory
    changes; the result register state is unchanged. -/
theorem chunkStore_step (s : BignumState) :
    bignumExec chunkStore s = some (storeMem s (regAddr s "op")
      (UInt64.ofNat (s.regs "r").toNat)) := by
  show bignumExec [storeAt0 "op" "r"] s = _
  simp only [bignumExec, storeAt0, execInstr, evalPExpr, vr,
             resolveAddr, Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 0 = 0 from rfl]
  show some (storeMem s
        (UInt64.ofNat (s.regs "op" + 0).toNat) (UInt64.ofNat (s.regs "r").toNat))
      = some (storeMem s (regAddr s "op") (UInt64.ofNat (s.regs "r").toNat))
  rw [show s.regs "op" + 0 = s.regs "op" from by bv_decide]
  rfl

/-- The advance chunk: `ap += 8`, `bp += 8`, `op += 8`, `n -= 1`. -/
theorem chunkAdv_step (s : BignumState) :
    bignumExec chunkAdv s = some
      (setReg (setReg (setReg (setReg s
        "ap" (s.regs "ap" + 8)) "bp" (s.regs "bp" + 8))
        "op" (s.regs "op" + 8)) "n" (s.regs "n" - 1)) := by
  show bignumExec [binImm "ap" (.Oadd .U64) 8,
                    binImm "bp" (.Oadd .U64) 8,
                    binImm "op" (.Oadd .U64) 8,
                    binImm "n"  (.Osub .U64) 1] s = _
  simp only [bignumExec, binImm, execInstr, evalPExpr, pv, vr,
             Option.bind_some, bind, Option.bind,
             show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
             show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl,
             setReg_regs, String.reduceEq, ↓reduceIte, reduceIte]

set_option maxHeartbeats 1200000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_spillLoopBody_step (s : BignumState) (a b : BitVec 64) (cin : Bool)
    (hcc : s.regs "cc" = BitVec.ofNat 64 (if cin then 1 else 0))
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec loopBody s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (adcStep a b cin).1.toNat) ∧
      s'.regs "cc" = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Compose the four chunks.
  -- Step 1: chunkLoad.
  have h1 := chunkLoad_step s a b ha hb
  set s1 : BignumState := setReg (setReg s "t" a) "s" b with hs1def
  -- Step 2: chunkSpill on s1.
  have ht1 : s1.regs "t" = a := by simp [hs1def, setReg]
  have hs_reg1 : s1.regs "s" = b := by simp [hs1def, setReg]
  have hcc1 : s1.regs "cc" = BitVec.ofNat 64 (if cin then 1 else 0) := by
    rw [hs1def]; simp [setReg, hcc]
  set s2 : BignumState := spillExitState s1 with hs2def
  have ⟨h2, h2_mem, h2_r, h2_cc, h2_frame⟩ :=
    chunkSpill_step s1 a b cin ht1 hs_reg1 hcc1
  -- Step 3: chunkStore on s2.
  have h3 := chunkStore_step s2
  have h2_r' : s2.regs "r" = (adcStep a b cin).1 := h2_r
  have h2_op : s2.regs "op" = s.regs "op" := by
    rw [h2_frame "op" (by decide) (by decide) (by decide), hs1def]
    simp [setReg]
  set s3 : BignumState := storeMem s2 (regAddr s2 "op")
        (UInt64.ofNat (s2.regs "r").toNat) with hs3def
  have h2_s_mem : s2.mem = s.mem := by
    show (spillExitState s1).mem = s.mem
    rw [h2_mem, hs1def]; simp [setReg]
  have hs3_mem : s3.mem = s.mem.store64 (regAddr s "op")
      (UInt64.ofNat (adcStep a b cin).1.toNat) := by
    rw [hs3def]
    simp only [storeMem_mem, h2_s_mem, h2_r', regAddr, h2_op]
  -- Step 4: chunkAdv on s3.
  have h4 := chunkAdv_step s3
  -- Frame for ap, bp, n: they are unchanged through chunks 2 and 3.
  have h2_ap : s2.regs "ap" = s.regs "ap" := by
    rw [h2_frame "ap" (by decide) (by decide) (by decide), hs1def]
    simp [setReg]
  have h2_bp : s2.regs "bp" = s.regs "bp" := by
    rw [h2_frame "bp" (by decide) (by decide) (by decide), hs1def]
    simp [setReg]
  have h2_n : s2.regs "n" = s.regs "n" := by
    rw [h2_frame "n" (by decide) (by decide) (by decide), hs1def]
    simp [setReg]
  have h2_cc' : s2.regs "cc" = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) := h2_cc
  have h3_ap : s3.regs "ap" = s.regs "ap" := by rw [hs3def]; simpa using h2_ap
  have h3_bp : s3.regs "bp" = s.regs "bp" := by rw [hs3def]; simpa using h2_bp
  have h3_op : s3.regs "op" = s.regs "op" := by rw [hs3def]; simpa using h2_op
  have h3_n  : s3.regs "n"  = s.regs "n"  := by rw [hs3def]; simpa using h2_n
  have h3_cc : s3.regs "cc" = BitVec.ofNat 64 (carryNat (adcStep a b cin).2) := by
    rw [hs3def]; simpa using h2_cc'
  have h3_mem : s3.mem = s.mem.store64 (regAddr s "op")
      (UInt64.ofNat (adcStep a b cin).1.toNat) := hs3_mem
  -- Combine all four chunks via bignumExec_append-style chaining.
  have hcombined : bignumExec loopBody s = some
      (setReg (setReg (setReg (setReg s3
        "ap" (s3.regs "ap" + 8)) "bp" (s3.regs "bp" + 8))
        "op" (s3.regs "op" + 8)) "n" (s3.regs "n" - 1)) := by
    rw [loopBody_eq_chunks]
    -- Three-way chained: (chunkLoad ++ chunkSpill) ++ chunkStore ++ chunkAdv
    have e12 : bignumExec (chunkLoad ++ chunkSpill) s = some s2 :=
      bignumExec_append_some_local chunkLoad chunkSpill s s1 s2 h1 h2
    have e123 : bignumExec ((chunkLoad ++ chunkSpill) ++ chunkStore) s = some s3 :=
      bignumExec_append_some_local _ chunkStore s s2 s3 e12 (by rw [hs3def]; exact h3)
    exact bignumExec_append_some_local _ chunkAdv s s3 _ e123 h4
  refine ⟨_, hcombined, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- memory at the final state: same as s3.mem since chunkAdv doesn't write memory.
    simp only [setReg_mem, h3_mem]
  · -- cc-register at final state: same as s3.regs "cc" (chunkAdv doesn't touch cc).
    simp only [setReg_regs, String.reduceEq, ↓reduceIte, reduceIte, h3_cc]
  · -- ap-register at final state: s3.regs "ap" + 8 = s.regs "ap" + 8.
    simp only [setReg_regs, String.reduceEq, ↓reduceIte, reduceIte, h3_ap]
  · -- bp-register.
    simp only [setReg_regs, String.reduceEq, ↓reduceIte, reduceIte, h3_bp]
  · -- op-register.
    simp only [setReg_regs, String.reduceEq, ↓reduceIte, reduceIte, h3_op]
  · -- n-register.
    simp only [setReg_regs, String.reduceEq, ↓reduceIte, reduceIte, h3_n]

/-- `loopBody` is straight-line (`Cassgn`/`Copn` only). -/
theorem loopBody_straightLine : InstrR.bodyIsStraightLine loopBody := by
  simp only [loopBody, loadAt0, reloadCf, adcCore, clearCc, spillCf, storeAt0,
             binImm, InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `loopBody` is non-control. -/
theorem loopBody_nonControl : ∀ i ∈ loopBody, i.isNonControl := by
  intro i hi
  simp only [loopBody, loadAt0, reloadCf, adcCore, clearCc, spillCf, storeAt0,
             binImm, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- **Forward one-iteration rule for the ADC-spill loop.**  Mirror of
    `Mpn.AddPrototype.bignumExecFuel_loop_step` retargeted at this file's
    `loopBody`. -/
theorem bignumExecFuel_spillLoop_step (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec loopBody s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond loopBody] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond loopBody] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) loopBody s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f loopBody s loopBody_straightLine]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
    show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) loopBody [.Cwhile [] cond loopBody]
        loopBody_nonControl s s_mid s' hsl hrec]

/-! ## §4  The ADC-spill loop, by induction on the limb list

A clone of `Mpn.AddPrototype.mpnAddN_loop` with `bignumExec_spillLoopBody_step`
in place of `bignumExec_loopBody_step`.  The threaded carry register is
`cc` instead of `cf`. -/

theorem mpnAddN_spillLoop :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (cin : Bool) (extra : Nat),
      as.length = bs.length →
      s.regs "cc" = BitVec.ofNat 64 (if cin then 1 else 0) →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "bp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (mpnAddN as bs cin).1 ∧
        s'.regs "cc" = BitVec.ofNat 64 (carryNat (mpnAddN as bs cin).2) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s cin extra _ hcc hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ loopBody s
        (evalPExpr_loopCond_false s hn0)
    · simp [mpnAddN, memHoldsLimbs]
    · simpa [mpnAddN, carryNat] using! hcc
    · intro b _; rfl
  | cons a as ih =>
    intro bs s cin extra hlen hcc hn hap hbp hdoa hdob
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hpos : 0 < 8 * (as.length + 1) := by omega
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- One ADC-spill iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_cc, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_spillLoopBody_step s a b cin hcc hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (adcStep a b cin).1.toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "bp" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "bp" + 8) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "bp") (8 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hcc1 : s1.regs "cc" = BitVec.ofNat 64 (if (adcStep a b cin).2 then 1 else 0) := by
        rw [hs1_cc]; simp [carryNat]
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_cc, hs'_frame⟩ :=
        ih bs s1 (adcStep a b cin).2 extra hlen' hcc1 hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_spillLoop_step emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_loopCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
          range_op_head_tail_disjoint op0 as.length (by omega)
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load64Mem_store64_same s.mem op0 (UInt64.ofNat (adcStep a b cin).1.toNat)
          rw [hread]
          rfl
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · rw [hs'_cc]; simp only [mpnAddN]
      · intro bb hbb
        rw [hmem1] at hs'_frame
        have hbb_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "op") (8 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_shift_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_head_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §5  Assembly: `MpnAddNAdcSpillJasminRefines`

The full bridge for the ADC-spill variant: `body = [cc := 0; while (n != 0) { … }]`.
The prelude zeroes the GPR carry; the loop is `mpnAddN_spillLoop`. -/

/-- Bridge statement: from a state holding `as` at `ap`, `bs` at `bp`,
    `n = |as|`, with the `op` output region disjoint from the `ap`/`bp`
    input regions, running the ADC-spill `body` lands in a state whose
    memory at `op` holds `(mpnAddN as bs false).1` and whose GPR carry
    register `cc` holds the carry-out. -/
def MpnAddNAdcSpillRefinesStmt : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel body s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAddN as bs false).1 ∧
      s'.regs "cc" = BitVec.ofNat 64 (carryNat (mpnAddN as bs false).2)

/-- **The ADC-spill bridge, fully proved.**  `body` (`cc := 0;
    while (n != 0) { spill-loopBody }`) refines `mpnAddN` over byte memory.
    The `cc := 0` prelude makes the first iteration's carry-in `false`;
    the loop is `mpnAddN_spillLoop`. -/
theorem MpnAddNAdcSpillJasminRefines : MpnAddNAdcSpillRefinesStmt := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  set s0 : BignumState := setReg s "cc" 0 with hs0
  have hexec0 : execInstr s
      (.Cassgn (.Lvar { var := vr "cc" }) .AT_none (.sword .U64) (.Pconst 0))
      = some s0 := by
    simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
      show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcc0 : s0.regs "cc" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cc" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cc" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; exact hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]; exact hbp
  have hdoa0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; exact hdoa
  have hdob0 : MemoryModel.Disjoint (range (regAddr s0 "op") (8 * as.length))
      (range (regAddr s0 "bp") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]; exact hdob
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cc, _⟩ :=
    mpnAddN_spillLoop as bs s0 false extra hlen hcc0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hbody : bignumExecFuel emptyRegistry (F + 1) body s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s0 := by
      conv_lhs => rw [body]
      simp only [bignumExecFuel, hexec0]
    rw [hF, hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem
    exact hs'_mem
  · exact hs'_cc

end CatCrypt.Crypto.Jasmin.Mpn.AddNAdcSpillPrototype
