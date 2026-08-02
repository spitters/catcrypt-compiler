/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
import Std.Tactic.BVDecide

set_option autoImplicit false

/-!
# ADX carry-chain fuser — dropping the `setc`/`movzbq`/`bt` round-trip

The carry-chain-selection front (`Dialects/CarryChainSelect.translateDialectCarrySelect`)
emits **value-threaded** ADX carry chains: each limb's carry-out is materialised
into a data register/spill slot (`ADCXHI` → `setc %cyb ; movzbq %cyb, %cy`) and the
next limb re-injects it into the CPU carry flag (`ADCX`'s explicit `reg 1`
carry-in → `bt $0, %cy`). So a two-limb thread renders as

```
    adcxq %s0, %d0        ; producer: CF := carry-out
    setc  %cyb            ; ADCXHI: materialise CF into a data value cy …
    movzbq %cyb, %cy      ;   … zero-extended
    movq  %a1, %d1        ; consumer setup (flag-safe)
    btq   $0, %cy         ; consumer: CF := bit0(cy)  — re-inject the carry
    adcxq %s1, %d1        ; consumer: d1 := a1 + s1 + CF
```

When the producer's carry-out feeds *directly* into the consumer's carry-in and
the materialised value `cy` has **no other reader**, the `setc → movzbq → bt`
round-trip is dead: the CPU carry flag the producer's `adcx` already left in `CF`
is exactly the bit `bt` would restore. This module's `fuseAdxChain` drops that
round-trip, leaving the carry in the flag across the fused `adcx` chain (~5
instructions per limb → 1), closing the residual gap the selection pass left
(the `c0cc042e7` follow-up).

## What the pass does (`fuseAdxChain : Lprog → Lprog`)

Mirrors `FheMontMulEmit.fuseMulHiLprog`: it maps each `Lfundef` body. In a
body it recognises the adjacent triple

* `p`  — an `ADCX` **data** op (`Lopn [d] ADCX [a, s, cin]`, three sources), which
  leaves its carry-out in `CF`;
* `hi` — the matching `ADCXHI` carry-out binding (`Lopn [cout] ADCXHI _`), which
  materialises `CF` into the value `cout`;
* `c`  — the next `ADCX` data op whose carry-in (third source) **is** `cout`.

The rewrite fires only when `cout` is read **nowhere else** (`coutDeadAfter`:
after `c`, the first mention of `cout` is a write, or none) and `c` reads `cout`
*only* as its carry-in (`cout ∉ {a, s}` of `c`). It then **drops** `hi` and
**retags** `c`'s carry-in to `LprogAsmPrinter.cfCarrySentinel`, so the printer's
`ADCX` arm emits no `bt $0, cin` — the flow is the live flag. `c` (now fused)
becomes the producer for the next limb, so a whole chain collapses limb by limb.
The seed carry-in of the first limb (materialised `0`/`1`, not an `ADCXHI`
carry-out) is never a `cout`, so it is preserved.

No intervening flag-clobber check is needed: the only op between the producer's
`CF`-write and the consumer's `CF`-read is the `ADCXHI` `hi`, whose render
(`setc`/`movzbq`, or `movq $0,slot; setc slot`) is flag-preserving on `CF`, as is
the consumer's own setup `movq`.

## What is proved (the carry-flag identity)

The `.s` layer is not executable in Lean (as with `fuseMulHiLprog`, its
whole-body value-correctness is gated by the orchestrator's byte-KAT against the
AUCurves Rust tower). The central content — that the fused live-flag carry
computes *the same* carry as the materialised-bit round-trip — is proved against
the faithful `JasminModel` machine semantics:

* `carryBit_roundtrip` — the `bv_decide` core: reading bit 0 back out of the
  `setc`-materialised word `(if c then 1 else 0)` recovers the carry bit `c`.
* `btCF_setc_restores_cf` — the model round-trip: `setc cout` then a `bt $0,cout`
  flag-read leaves `CF` exactly as the producer left it.
* `fuseAdxStep_sound` — the **block-level** statement: the unfused fragment
  `[setc cout ; bt cout ; adcx d' src']` and the fused `[adcx d' src']` land the
  **same** data word in `d'` and the **same** carry-out in `CF` (the dropped
  `cout` register is the only difference, and it is dead by the recognition
  side-condition). This is the model-level denotation preservation of one fusion.

## Constant-time preservation

The fusion only drops (`setc`/`bt`) and keeps register-only ALU ops. Every
instruction it can emit is `MachineConstantTime.IsDirect` (no register-indexed
memory access), so a fused fragment stays in the constant-time class by the
existing `ConstantTimeCoverage.allDirect_constant_time` — the same predicate the
owned carry-chain leaves use (`fuseAdx_allDirect`). The schedule edit is
data-independent (it removes a fixed pair of instructions on a fixed position),
so it preserves the leak trace.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (cfCarrySentinel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

-- Structural equality on the `Lprog` instruction AST (`JasminLprogExport` derives
-- only `Repr`); needed to evaluate the demo-fire equalities by `native_decide`.
deriving instance DecidableEq for LinstrR
deriving instance DecidableEq for Linstr

/-! ## 1. The `Lprog` fusion pass -/

/-- Boolean operand equality (`LOperand` derives `DecidableEq`). -/
def lopEq (a b : LOperand) : Bool := decide (a = b)

/-- Recognise an `ADCX` **data** op `Lopn [d] ADCX(:64) [a, s, cin]` (three
    sources: the dst self-source, the data source, and the `reg 1` carry-in).
    Returns `(d, srcs)`. -/
def isAdcxDataInstr (i : Linstr) : Option (LOperand × List LOperand) :=
  match i.li_i with
  | .Lopn [d] opn srcs =>
      if stripWidthTag opn == "ADCX" && srcs.length == 3 then some (d, srcs) else none
  | _ => none

/-- Recognise an `ADCXHI` carry-out binding `Lopn [cout] ADCXHI(:64) _`, the op
    that materialises the producer's `CF` into the value `cout`. Returns `cout`. -/
def isAdcxHiInstr (i : Linstr) : Option LOperand :=
  match i.li_i with
  | .Lopn [cout] opn _ => if stripWidthTag opn == "ADCXHI" then some cout else none
  | _ => none

/-- The `ADCXHI`/`ADOXHI`/`MULXHI` carry-out / high-word **binding** ops carry a
    *vestigial* source list — they share the arg list of their paired `ADCX`/`MULX`
    (`addCarryLo`/`addCarryHi` are one `Com` op-pair over the same sources), but
    the printer renders them as `setc dst` (resp. drops them), reading **none** of
    those sources. So an operand appearing in a binding op's `src` list is not a
    read. -/
def isVestigialSrcInstr (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn _ opn _ =>
      let b := stripWidthTag opn
      b == "ADCXHI" || b == "ADOXHI" || b == "MULXHI"
  | _ => false

/-- Does instruction `i` **read** `cout` as a source? The vestigial
    source list of a carry-out / mulx-hi binding is *not* a read (its render emits
    no operand read), so those ops never count. -/
def mentionsSrc (cout : LOperand) (i : Linstr) : Bool :=
  if isVestigialSrcInstr i then false
  else match i.li_i with | .Lopn _ _ srcs => srcs.any (lopEq cout) | _ => false

/-- Does instruction `i` write `cout` (as a destination)? -/
def mentionsDst (cout : LOperand) (i : Linstr) : Bool :=
  match i.li_i with | .Lopn dsts _ _ => dsts.any (lopEq cout) | _ => false

/-- **Single-use side-condition.** Scanning the instructions *after* the consumer,
    the first mention of `cout` is a write (`cout` redefined — its old
    value is dead) or there is none: then dropping the `ADCXHI` that materialised
    `cout` loses no live value. A read before any rewrite means `cout` is
    live elsewhere, so the fusion must not fire. (Vestigial binding-op sources are
    not reads — see `mentionsSrc`.) -/
def coutDeadAfter (cout : LOperand) : Lcmd → Bool
  | [] => true
  | i :: rest =>
      if mentionsSrc cout i then false
      else if mentionsDst cout i then true
      else coutDeadAfter cout rest

/-- Retag consumer `c`'s carry-in (third source) to `cfCarrySentinel`, keeping its
    destination, mnemonic, and first two sources. -/
def retagCin (c : Linstr) : Linstr :=
  { c with li_i :=
      match c.li_i with
      | .Lopn dsts opn (a :: s :: _) => .Lopn dsts opn [a, s, .reg cfCarrySentinel]
      | other => other }

/-- A **flag-safe, carry-neutral** `MOV` that may sit between the `ADCXHI` and its
    consumer (the per-limb constant loads of the trial-subtract chains). `MOV`
    never writes `CF`, so the producer's carry-out survives across it; requiring it
    to neither read nor write `cout` keeps the materialised carry's single-use
    invariant. Only `MOV`/`MOVQ` qualify — any other op (another `ADCX`/`ADCXHI`,
    or a flag-writing ALU op) stops the scan, so the fuser never crosses a flag
    clobber or a different carry chain. -/
def isMovSkippable (cout : LOperand) (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [d] opn srcs =>
      let b := stripWidthTag opn
      (b == "MOV" || b == "MOVQ") && !lopEq d cout && !srcs.any (lopEq cout)
  | _ => false

/-- Locate the consumer `ADCX` whose carry-in is `cout`, skipping a run of
    flag-safe `MOV`s (the constant loads between an `ADCXHI` and the next limb).
    Returns `(skipped, consumer, rest)`. Stops (no fusion) at the first non-`MOV`
    that is not the consumer, so a different chain's `ADCX` or any flag-writing op
    ends the scan. The consumer must read `cout` **only** as its carry-in
    (`cout ∉ {a, s}`). -/
def findConsumer (cout : LOperand) : Lcmd → Option (Lcmd × Linstr × Lcmd)
  | [] => none
  | i :: rest =>
      match isAdcxDataInstr i with
      | some (_, srcs) =>
          match srcs with
          | [a, s, cin] =>
              if lopEq cin cout && !lopEq a cout && !lopEq s cout then
                some ([], i, rest)
              else none
          | _ => none
      | none =>
          if isMovSkippable cout i then
            match findConsumer cout rest with
            | some (sk, c, r) => some (i :: sk, c, r)
            | none => none
          else none

/-- The tail `findConsumer` returns is strictly shorter than its input: it drops
    at least the consumer. Discharges `fuseAdxChainBody`'s termination. -/
theorem findConsumer_length (cout : LOperand) (xs : Lcmd) :
    ∀ sk c r, findConsumer cout xs = some (sk, c, r) → r.length < xs.length := by
  induction xs with
  | nil => intro sk c r h; simp [findConsumer] at h
  | cons i rest ih =>
      intro sk c r h
      rw [findConsumer] at h
      split at h
      · -- isAdcxDataInstr i = some (_, srcs)
        split at h
        · -- srcs = [a, s, cin]
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, _, hr⟩ := h; subst hr
            simp [List.length_cons]
          · simp at h
        · simp at h
      · -- isAdcxDataInstr i = none
        split at h
        · -- isMovSkippable i
          split at h
          · next hrec =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, _, hr⟩ := h; subst hr
              have hlt := ih _ _ _ hrec
              simp only [List.length_cons]; omega
          · simp at h
        · simp at h

set_option linter.unusedVariables false in  -- `hf` is used only in `decreasing_by`
/-- **The fusion worker over a body.** Anchor a producer `ADCX` immediately
    followed by its `ADCXHI cout`; locate the consumer `ADCX` (carry-in = `cout`),
    skipping flag-safe `MOV`s in between; if `cout` is dead after the consumer,
    **drop the `ADCXHI`**, keep the skipped `MOV`s in place, and retag the
    consumer's carry-in to the live-flag sentinel. The retagged consumer is re-fed
    as the next producer, so a whole chain collapses limb by limb (the first limb's
    seed carry-in — a materialised constant, never an `ADCXHI` cout — is
    preserved). Any non-matching head passes through. -/
def fuseAdxChainBody : Lcmd → Lcmd
  | p :: hi :: rest0 =>
      match isAdcxDataInstr p, isAdcxHiInstr hi with
      | some _, some cout =>
          match hf : findConsumer cout rest0 with
          | some (skipped, c, rest) =>
              if coutDeadAfter cout rest then
                p :: (skipped ++ fuseAdxChainBody (retagCin c :: rest))
              else
                p :: fuseAdxChainBody (hi :: rest0)
          | none => p :: fuseAdxChainBody (hi :: rest0)
      | _, _ => p :: fuseAdxChainBody (hi :: rest0)
  | body => body
  termination_by body => body.length
  decreasing_by
    all_goals first
      | (have := findConsumer_length cout rest0 skipped c rest hf
         simp only [List.length_cons]; omega)
      | simp_wf

/-- Fuse the ADX carry chains in one function body. -/
def fuseAdxChainFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := fuseAdxChainBody f.lfd_body }

/-- **The pass.** Apply the ADX carry-chain fusion to every function body of an
    `Lprog`. Sibling of `FheMontMulEmit.fuseMulHiLprog`; plugs into the owned
    pipeline at the same stage (after physical lowering, before the AT&T printer). -/
def fuseAdxChain (p : Lprog) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) => (n, fuseAdxChainFundef f)) }

/-! ## 2. The carry-flag identity (model semantics)

The fusion drops the `ADCXHI` `setc` materialisation and the consumer's `bt`
re-injection. Its soundness is the fact that this `setc → bt` round-trip is the
identity on the carry that reaches the consumer — proved against the faithful
`JasminModel` (`evalInstr`, `x86_ADCX`, `JState`). -/

/-- The flag effect of a `bt $0, name`: set `CF` to bit 0 of the operand `name`,
    leaving registers, memory, and the other flags untouched. (`bt` writes only
    `CF`; the emitted carry idiom always uses `bt $0, cin`.) -/
def btCF {w : Nat} (s : JState w) (name : String) : JState w :=
  { s with flags := { s.flags with cf := some ((s.get name).getLsbD 0) } }

/-- **The `bv_decide` core.** Reading bit 0 back out of the `setc`-materialised
    word `(if c then 1 else 0)` recovers the carry bit `c`: the flag→GPR→flag
    round-trip is the identity on the carry. -/
theorem carryBit_roundtrip (c : Bool) :
    (if c then (1 : BitVec 64) else 0).getLsbD 0 = c := by
  bv_decide

/-- `setc cout` leaves the flag map unchanged (it only writes the GPR `cout`). -/
@[simp] theorem setc_flags {w : Nat} (s : JState w) (cout : String) :
    (evalInstr s (.setc cout)).flags = s.flags := by
  simp [evalInstr, JState.setReg]

/-- **A flag-safe `MOV` preserves `CF`.** The trial-subtract chains interleave a
    per-limb constant-load `MOV` between the `ADCXHI` and its consumer; `MOV` writes
    a register and touches no flag, so the producer's carry-out survives across it
    into the fused consumer's `adcx`. This licenses the `findConsumer` `MOV`-skip. -/
@[simp] theorem mov_preserves_cf {w : Nat} (s : JState w) (dst : String)
    (src : JOperand) : (evalInstr s (.mov dst src)).flags.cf = s.flags.cf := by
  simp [evalInstr, JState.setReg]

/-- **The model round-trip.** With `CF = some b` (the producer's carry-out), the
    materialise-then-reinject sequence `setc cout ; bt $0, cout` leaves `CF`
    exactly `some b` — the value the producer's `adcx` already put there. -/
theorem btCF_setc_restores_cf (s : JState 64) (cout : String) (b : Bool)
    (hcf : s.flags.cf = some b) :
    (btCF (evalInstr s (.setc cout)) cout).flags.cf = s.flags.cf := by
  have hb : s.flagB (·.cf) = b := by simp [JState.flagB, hcf]
  have hval : (evalInstr s (.setc cout)).regs cout = (if b then (1 : BitVec 64) else 0) := by
    simp [evalInstr, JState.setReg, hb]
  simp only [btCF, JState.get]
  rw [hval, carryBit_roundtrip, hcf]

/-! ## 3. Block-level soundness of one fusion step

On the post-producer state `s` (`CF = some b`, `b` = the producer's carry-out),
the unfused `[setc cout ; bt cout ; adcx d' src']` and the fused `[adcx d' src']`
compute the same data word in `d'` and the same carry-out in `CF`. The recognition
side-conditions supply the freshness `cout ≠ d'` and `cout ∉ src'`. -/

/-- `adcx`'s data output: `d' := (x86_ADCX (d', src', CF)).2`. -/
theorem adcx_get_self (t : JState 64) (d' : String) (src' : JOperand) :
    (evalInstr t (.adcx d' src')).get d'
      = (x86_ADCX (t.get d') (src'.eval t) (t.flagB (·.cf))).2 := by
  simp [evalInstr, JState.get]

/-- `adcx`'s carry-out flag: `CF := (x86_ADCX (d', src', CF)).1`. -/
theorem adcx_cf_self (t : JState 64) (d' : String) (src' : JOperand) :
    (evalInstr t (.adcx d' src')).flags.cf
      = (x86_ADCX (t.get d') (src'.eval t) (t.flagB (·.cf))).1 := by
  simp [evalInstr, JState.get]

/-- **The fusion step is value-sound.** The dropped `setc cout ; bt cout` prefix
    does not change what the consumer `adcx d' src'` computes: it lands the same
    `d'` and the same carry-out `CF` as the fused op reading the live flag. The
    dead `cout` register is the only state difference (unobserved by the side
    condition). -/
theorem fuseAdxStep_sound (s : JState 64) (cout d' : String) (src' : JOperand)
    (b : Bool) (hcf : s.flags.cf = some b) (hne : cout ≠ d')
    (hsrc : ∀ r, src' = .reg r → r ≠ cout) :
    (evalInstr (btCF (evalInstr s (.setc cout)) cout) (.adcx d' src')).get d'
        = (evalInstr s (.adcx d' src')).get d'
    ∧ (evalInstr (btCF (evalInstr s (.setc cout)) cout) (.adcx d' src')).flags.cf
        = (evalInstr s (.adcx d' src')).flags.cf := by
  -- the round-trip state agrees with `s` on `d'`, on `src'`, and on `CF`
  have hd'ne : d' ≠ cout := fun h => hne h.symm
  have hd' : (btCF (evalInstr s (.setc cout)) cout).get d' = s.get d' := by
    simp only [btCF, JState.get, evalInstr, JState.setReg]
    rw [if_neg hd'ne]
  have hsrc' : src'.eval (btCF (evalInstr s (.setc cout)) cout) = src'.eval s := by
    cases src' with
    | imm v => simp [JOperand.eval]
    | reg r =>
        have hr : r ≠ cout := hsrc r rfl
        simp only [JOperand.eval, btCF, JState.get, evalInstr, JState.setReg]
        rw [if_neg hr]
  have hcf3 : (btCF (evalInstr s (.setc cout)) cout).flagB (·.cf) = b := by
    have hround := btCF_setc_restores_cf s cout b hcf
    simp only [JState.flagB, hround, hcf, Option.getD_some]
  have hcfs : s.flagB (·.cf) = b := by simp [JState.flagB, hcf]
  refine ⟨?_, ?_⟩
  · rw [adcx_get_self, adcx_get_self, hd', hsrc', hcf3, hcfs]
  · rw [adcx_cf_self, adcx_cf_self, hd', hsrc', hcf3, hcfs]

/-! ## 4. Constant-time preservation

Every instruction the fusion drops or keeps is register-only (`IsDirect`), so a
fused fragment stays in the constant-time class by the existing
`ConstantTimeCoverage.allDirect_constant_time`. -/

/-- `setc` is a direct (register/flag-only) op. -/
theorem setc_isDirect (cout : String) : IsDirect (w := 64) (.setc cout) := by trivial

/-- `adcx` is a direct (register/flag-only) op. -/
theorem adcx_isDirect (d : String) (src : JOperand) :
    IsDirect (w := 64) (.adcx d src) := by trivial

/-- **CT preservation of one fusion step.** Both the unfused fragment
    `[setc cout, adcx d' src']` and the fused fragment `[adcx d' src']` are
    entirely direct, hence constant-time by `allDirect_constant_time`. The fusion
    only removes register-only ops on a fixed (data-independent) schedule. -/
theorem fuseAdx_allDirect (cout d' : String) (src' : JOperand) :
    (∀ i ∈ [(.setc cout : JInstr 64), .adcx d' src'], IsDirect i)
    ∧ (∀ i ∈ [(.adcx d' src' : JInstr 64)], IsDirect i) := by
  refine ⟨?_, ?_⟩ <;> intro i hi <;> simp only [List.mem_cons,
    List.not_mem_nil, or_false] at hi
  · rcases hi with h | h <;> subst h
    · exact setc_isDirect cout
    · exact adcx_isDirect d' src'
  · subst hi; exact adcx_isDirect d' src'

/-! ## 5. Full-chain demos on the real emitted `Lprog` shapes

Two ≥4-limb chains lifted verbatim from the BN254 `Fp2_add` owned `Lprog`
(`Bn254TowerFrontEmit`, dumped body indices 61–67 and 70–79): a strict
`ADCX`/`ADCXHI` ripple, and a trial-subtract ripple that interleaves a per-limb
constant-load `MOV` between each `ADCXHI` and its consumer. Both must collapse
**whole** — every inner `ADCXHI` dropped, every `ADCX` kept, every consumer
carry-in retagged to the sentinel, and (subtract) every intervening `MOV`
preserved. The counts guard against silent under-firing regression. -/

/-- Count `Lopn` ops whose (width-stripped) mnemonic is `name`. -/
def countOpn (name : String) (body : Lcmd) : Nat :=
  (body.filter (fun i =>
    match i.li_i with | .Lopn _ opn _ => stripWidthTag opn == name | _ => false)).length

/-- Count ops carrying the live-flag sentinel as a source (fused carry-ins). -/
def countSentinelCin (body : Lcmd) : Nat :=
  (body.filter (fun i =>
    match i.li_i with
    | .Lopn _ _ srcs => srcs.any (lopEq (.reg cfCarrySentinel)) | _ => false)).length

/-- The strict 4-limb `ADCX`/`ADCXHI` ripple (indices 61–67), carry threaded
    `R12`(seed=0) → `k.0` → `R8` → `R9`; each carry-out read only by the next
    limb, then redefined. -/
def demoAddChain : Lcmd :=
  [ ⟨0, .Lopn [.reg "R13"] "ADCX:64"   [.reg "RAX", .reg "R8",  .reg "R12"]⟩,
    ⟨0, .Lopn [.reg "k.0"] "ADCXHI:64" [.reg "RAX", .reg "R8",  .reg "R12"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADCX:64"   [.reg "RSI", .reg "R9",  .reg "k.0"]⟩,
    ⟨0, .Lopn [.reg "R8"]  "ADCXHI:64" [.reg "RSI", .reg "R9",  .reg "k.0"]⟩,
    ⟨0, .Lopn [.reg "RSI"] "ADCX:64"   [.reg "RDI", .reg "R10", .reg "R8"]⟩,
    ⟨0, .Lopn [.reg "R9"]  "ADCXHI:64" [.reg "RDI", .reg "R10", .reg "R8"]⟩,
    ⟨0, .Lopn [.reg "RDI"] "ADCX:64"   [.reg "RBP", .reg "R11", .reg "R9"]⟩ ]

/-- **The strict ripple collapses whole:** all 3 inner `ADCXHI` dropped, all 4
    `ADCX` kept, 3 consumer carry-ins retagged to the sentinel (limb 0 keeps its
    seed carry-in `R12`). -/
theorem demoAddChain_collapses :
    countOpn "ADCXHI" (fuseAdxChainBody demoAddChain) = 0
    ∧ countOpn "ADCX" (fuseAdxChainBody demoAddChain) = 4
    ∧ countSentinelCin (fuseAdxChainBody demoAddChain) = 3 := by native_decide

/-- The trial-subtract 4-limb ripple (indices 70–79): a per-limb constant-load
    `MOV RBP, imm` sits between each `ADCXHI` and its consumer `ADCX`. -/
def demoSubChain : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"]  "ADCX:64"   [.reg "R13", .reg "RBP", .reg "R8"]⟩,
    ⟨0, .Lopn [.reg "R10"] "ADCXHI:64" [.reg "R13", .reg "RBP", .reg "R8"]⟩,
    ⟨0, .Lopn [.reg "RBP"] "MOV:64"    [.imm 7529619929231668594]⟩,
    ⟨0, .Lopn [.reg "R8"]  "ADCX:64"   [.reg "RAX", .reg "RBP", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "R11"] "ADCXHI:64" [.reg "RAX", .reg "RBP", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "RBP"] "MOV:64"    [.imm 5165552122434856866]⟩,
    ⟨0, .Lopn [.reg "R10"] "ADCX:64"   [.reg "RSI", .reg "RBP", .reg "R11"]⟩,
    ⟨0, .Lopn [.reg "R12"] "ADCXHI:64" [.reg "RSI", .reg "RBP", .reg "R11"]⟩,
    ⟨0, .Lopn [.reg "RBP"] "MOV:64"    [.imm 0]⟩,
    ⟨0, .Lopn [.reg "R11"] "ADCX:64"   [.reg "RDI", .reg "RBP", .reg "R12"]⟩ ]

/-- **The MOV-interleaved ripple collapses whole:** all 3 inner `ADCXHI` dropped,
    all 4 `ADCX` kept, all 3 intervening `MOV`s preserved, and 3 consumer carry-ins
    retagged to the sentinel (FIX 2 — the `findConsumer` `MOV`-skip fires). -/
theorem demoSubChain_collapses :
    countOpn "ADCXHI" (fuseAdxChainBody demoSubChain) = 0
    ∧ countOpn "ADCX" (fuseAdxChainBody demoSubChain) = 4
    ∧ countOpn "MOV" (fuseAdxChainBody demoSubChain) = 3
    ∧ countSentinelCin (fuseAdxChainBody demoSubChain) = 3 := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse
