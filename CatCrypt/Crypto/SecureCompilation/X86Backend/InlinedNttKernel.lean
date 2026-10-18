/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLeafFusion
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLeafFusion

/-!
# Per-leaf ABI tax of a two-butterfly NTT composition

`BarrettButterflyKernel` lowers the Barrett NTT butterfly body through the
in-Lean x86 backend. This module is a demonstration over a small
**two-butterfly composition** (one feeds the other), showing that

1. composing the two butterflies **as separate leaves** pays a per-leaf ABI
   copy-out/copy-in tax — the producer stores its result word to a buffer and
   the consumer reloads it as an argument across the call boundary; while
2. the **inlined** form, in which the producer's result stays
   register-resident and feeds the consumer directly, has no boundary store +
   reload.

Two complementary levels:

* **`Com jasminDialect` level.** A one-call `JForProg` whose `update` body is
  one `extCall` to a registered NTT-layer wrapper leaf; the leaves have opaque
  external semantics. `inline_denote_eq_boundary` states that
  `ComInline.inline` preserves its denotation. The `jasminExtSem` arm for
  `[stackArr 16 _] → stackArr 16 _` returns its argument whatever the leaf
  name, so the registry consistency this rests on holds by `rfl`.
  The allocation content at this level is `inlinedRA_slotOfInjectiveOnLive`.
  This program is not the Part B blocks, which are written as `JInstr` lists.

* **`List (JInstr 64)` level.** Two concrete butterfly blocks chained through
  the x86 backend: `abiBoundaryBlock` routes the producer's `o0` through memory (a
  `storeMem` then a `loadMem` reload), while `inlinedMergedBlock` forwards `o0`
  in a register. Both lower via `lowerBlock_denote_closed`. Their observable
  output words agree on two fixed inputs (`abi_eq_inlined_outputs_kat`,
  `abi_eq_inlined_outputs_kat2`). `emitMain` writes both to `.s` for the bench
  harness, which compares their outputs and reports cyc/op for each.

## Main results

* `inline_denote_eq_boundary` — the inlined program denotes the boundary
  program on every initial accumulator, under `nttRegistry_consistent`.
* `inlinedRA_slotOfInjectiveOnLive` — the linear scan assigns distinct slots to
  simultaneously live binders of the inlined body.
* `abi_boundary_lowering_correct` / `inlined_merged_lowering_correct` — both
  JInstr blocks lower denotation-preservingly through the x86 backend
  (instances of `lowerBlock_denote_closed`).
* `abi_eq_inlined_outputs_kat` / `abi_eq_inlined_outputs_kat2` — equal
  observable output words on two fixed inputs (`native_decide`).
* `abiTaxInstrs_eq : abiTaxInstrs = 4` — the boundary block has four more
  instructions: the store and reload of `o0` and of `o1`.
* `allocations_complete` — `livenessAllocGp` assigns every name of both blocks
  a pool register. No theorem relates `livenessAllocGp` to `runBlock`.

Axioms: `inlinedRA_slotOfInjectiveOnLive` uses `Classical.choice`; the
`native_decide` numeric pins add `Lean.ofReduceBool`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.InlinedNttKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)
open CatCrypt.Crypto.SecureCompilation.VIR.ComInline
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLeafFusion (callU callU_denote)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel
  (muN pN)

/-! ## Part A — inlining at the `Com jasminDialect` level

The call boundary between two composed leaves is an `extCall`. The composition
is modelled as a single accumulator-update body that calls one registered
NTT-layer wrapper leaf. Inlining replaces the call with the wrapper's body, and
`ComInline.inline_preserves_denote` gives denotation preservation. Part C
allocates registers independently with `livenessAllocGp` over the `JInstr`
block. -/

/-- The accumulator type: a length-8 BabyBear coefficient array (an NTT layer's
    worth of values), keyed at the `stackArr 16 8` dialect type so it routes
    through `jasminExtSem`'s unary array arm. -/
abbrev nttAcc : JasminTy := .stackArr 16 8

/-- The wrapper-leaf name (the call boundary that inlining removes). -/
def wrapperName : String := "plonky3_ntt_layer8_wrapper"

/-- The primitive-leaf name the wrapper forwards to (the inlined body). -/
def primName : String := "plonky3_ntt_layer8_prim"

/-- The registered wrapper body: a single `extCall` to the primitive leaf, on
    the formal. Same `[nttAcc] → nttAcc` signature, so its denotation is the
    `jasminExtSem` unary-array identity — equal to the wrapper `extCall`'s. -/
def wrapperBody : SingleExprBody [nttAcc] nttAcc :=
  { defExpr := callU primName (Γ := [nttAcc]) (tf := nttAcc) .here }

/-- The NTT-layer inlining registry: `wrapperName ↦ wrapperBody`, else none. -/
def nttRegistry : FuncRegistry := fun n =>
  if n = wrapperName then
    some { argTys := [nttAcc], retTy := nttAcc, body := wrapperBody }
  else none

/-- **Registry consistency for the NTT-layer registry.** The wrapper body's
    defining expression (an `extCall` to `primName`) denotes equally to the
    wrapper `extCall`'s opaque external semantics. Both are `[nttAcc] → nttAcc`
    `extCall`s, so both reduce to `jasminExtSem`'s unary-`stackArr` identity arm
    on the same argument — equal by `rfl`. -/
theorem nttRegistry_consistent : RegistryConsistent nttRegistry := by
  intro name fb hfb V
  -- Only `wrapperName` is registered; extract `fb`.
  by_cases h : name = wrapperName
  · rw [nttRegistry, if_pos h, Option.some.injEq] at hfb
    subst hfb; subst h
    -- `wrapperBody.defExpr.denote V = callU primName .here |>.denote V`
    --   = jasminExtSem primName [nttAcc] nttAcc (lookupArgs …)
    -- and `jasminExtSem wrapperName [nttAcc] nttAcc V` — both the unary
    -- stackArr arm (name-independent identity), hence equal once the singleton
    -- valuation is destructured.
    cases V
    rfl
  · rw [nttRegistry, if_neg h] at hfb
    exact absurd hfb (by simp)

/-- The accumulator-update body: one `extCall` to the wrapper leaf (the call
    boundary), returning its result. This is the "two butterflies composed as
    separate leaves" shape: the body does its work behind a single call. -/
def boundaryUpdate : Com jasminDialect [nttAcc] nttAcc :=
  .var (callU wrapperName (Γ := [nttAcc]) (tf := nttAcc) .here) (.ret .here)

/-- The boundary program (one NTT layer applied once). -/
def boundaryProg : JForProg nttAcc := { n := 1, update := boundaryUpdate }

/-- The inlined update body: `ComInline.inline` over the NTT registry replaces
    the wrapper `extCall` with the primitive `extCall` (the registered body),
    eliminating the call boundary. -/
def inlinedUpdate : Com jasminDialect [nttAcc] nttAcc :=
  inline nttRegistry boundaryUpdate

/-- The inlined program. -/
def inlinedProg : JForProg nttAcc := { n := 1, update := inlinedUpdate }

/-- The `linearScanRA` allocation of the inlined program. Its `slotOf` is the
    identity (`RegisterAllocation.linearScanRA_slotOf_eq_id`); its linear-scan
    slots are in `seqOf`. -/
def inlinedRA : RegisterAllocation :=
  RegisterAllocation.linearScanRA inlinedProg

/-- Inlining the wrapper leaf preserves the denotation: the inlined program
    denotes the boundary program on every initial accumulator
    (`ComInline.inline_preserves_denote` under `nttRegistry_consistent`). -/
theorem inline_denote_eq_boundary (init : ⟦nttAcc⟧) :
    inlinedProg.denote init = boundaryProg.denote init := by
  simp only [JForProg.denote, JForProg.step, inlinedProg, boundaryProg,
    inlinedUpdate, List.range_one, List.foldl_cons, List.foldl_nil]
  exact inline_preserves_denote nttRegistry nttRegistry_consistent boundaryUpdate
    (.cons init .nil)

/-- Simultaneously live binders of the inlined body receive distinct slots under
    the linear scan (`linearScanRA_real_slotOfInjectiveOnLive`). -/
theorem inlinedRA_slotOfInjectiveOnLive :
    RegisterAllocation.SlotOfInjectiveOnLive inlinedProg :=
  RegisterAllocation.linearScanRA_real_slotOfInjectiveOnLive inlinedProg

/-- The inlined body is not syntactically the boundary body: the pass
    eliminates the boundary `extCall name = wrapperName` and splices in the
    registered primitive call. -/
theorem inline_changed_the_call :
    inlinedUpdate
      = .var (callU primName (Γ := [nttAcc]) (tf := nttAcc) .here) (.ret .here) := by
  rfl

/-! ## Part B — the measured ABI-tax delta at the `List (JInstr 64)` level

The tax, on the x86 backend. Two BabyBear NTT butterflies
are chained: butterfly 1 maps `(a, b, w) ↦ (o0, o1)` with
`o0 = a + ω·b`, `o1 = a − ω·b`; butterfly 2 consumes `o0` as its `a`-input,
with fresh `(b2, w2)`, producing `(o0', o1')`. The composition's observable
output is the three words `(o0', o1', o1)`.

`butterflyBody dst a b w` is the butterfly word arithmetic (the
`BarrettButterflyKernel.butterflyBlock` Barrett+csub sequence) writing its two
results into the named registers `dst.1` (= `a + ω·b`) and `dst.2`
(= `a − ω·b`), reading inputs from the named registers `a, b, w`. It uses NO
memory ops — pure register arithmetic — so chaining is a question of where the
producer's `o0` lives between the two butterflies. -/

/-- The Barrett butterfly *word arithmetic* as a register-to-register block:
    reads inputs from registers `ra, rb, rw`; writes `a + ω·b` to register
    `oLo` and `a − ω·b` to register `oHi`. Scratch registers are name-prefixed
    by `p` so two instances don't collide. This is the
    `BarrettButterflyKernel.butterflyBlock` body with the memory `loadMem`/
    `storeMem` ABI shell stripped (the args are already in registers, the
    results stay in registers). -/
def butterflyBody (p : String) (ra rb rw oLo oHi : String) : List (JInstr 64) :=
  let mu := p ++ "MU"; let x := p ++ "x"; let q := p ++ "q"
  let wb := p ++ "wb"; let m := p ++ "m"
  [ .mov mu (.imm muN)
    -- x = w * b
  , .mov x (.reg rw)
  , .imul x (.reg rb)
    -- q = ((x>>30)*MU>>32)*p
  , .mov q (.reg x)
  , .shr q (.imm 30)
  , .imul q (.reg mu)
  , .shr q (.imm 32)
  , .imul q (.imm pN)
    -- x = x - q
  , .sub x (.reg q)
    -- wb = csub(x)
  , .mov wb (.reg x)
  , .sub wb (.imm pN)
  , .mov m (.reg wb)
  , .shr m (.imm 63)
  , .neg m
  , .and_ m (.imm pN)
  , .add wb (.reg m)
    -- oHi = bbSub a wb
  , .mov oHi (.reg ra)
  , .sub oHi (.reg wb)
  , .mov m (.reg oHi)
  , .shr m (.imm 63)
  , .neg m
  , .and_ m (.imm pN)
  , .add oHi (.reg m)
    -- oLo = bbAdd a wb
  , .mov oLo (.reg ra)
  , .add oLo (.reg wb)
  , .sub oLo (.imm pN)
  , .mov m (.reg oLo)
  , .shr m (.imm 63)
  , .neg m
  , .and_ m (.imm pN)
  , .add oLo (.reg m) ]

/-- The number of instructions in one butterfly body. -/
theorem butterflyBody_length (p ra rb rw oLo oHi : String) :
    (butterflyBody p ra rb rw oLo oHi).length = 31 := by
  simp only [butterflyBody, List.length_cons, List.length_nil]

/-! ### B.1 The ABI-boundary composition (two separate leaves)

When the two butterflies are emitted as **separate leaf functions** and
composed, the producer (butterfly 1) writes its result words out to its result
buffer (the reg-ptr ABI's copy-out), and the consumer (butterfly 2) reads its
argument back from a buffer (the reg-ptr ABI's copy-in). The forwarded value
`o0` therefore takes a **store-then-reload** round trip through memory — the
per-leaf ABI tax. We model the chained pair as one block where that round trip
is explicit. -/

/-- The ABI-boundary chained block. Butterfly 1 loads `a, b, w` from `inp`,
    computes into registers `o0, o1`, then **stores both results out** (the
    leaf's copy-out: `o0 → [scratch+0]`, `o1 → [scratch+8]`). Butterfly 2
    **reloads its `a`-argument** from `[scratch+0]` (the next leaf's copy-in),
    loads its own `b2, w2` from `inp`, computes into `o0', o1'`, and stores the
    three observable outputs to `out`. The `storeMem o0` + `loadMem a2` pair
    across the boundary is the ABI tax. -/
def abiBoundaryBlock : List (JInstr 64) :=
  -- butterfly 1 args in
  [ .loadMem "a" "inp" 0
  , .loadMem "b" "inp" 8
  , .loadMem "w" "inp" 16 ]
  ++ butterflyBody "p1" "a" "b" "w" "o0" "o1"
  -- leaf-1 copy-out (ABI): store both result words to the buffer
  ++ [ .storeMem "scratch" 0 (.reg "o0")
     , .storeMem "scratch" 8 (.reg "o1") ]
  -- leaf-2 copy-in (ABI): reload the forwarded a-argument + load own b2, w2
  ++ [ .loadMem "a2" "scratch" 0
     , .loadMem "b2" "inp" 24
     , .loadMem "w2" "inp" 32 ]
  ++ butterflyBody "p2" "a2" "b2" "w2" "o0p" "o1p"
  -- store the three observable outputs
  ++ [ .storeMem "out" 0 (.reg "o0p")
     , .storeMem "out" 8 (.reg "o1p")
     , .loadMem "o1tmp" "scratch" 8       -- carry o1 through (was copied out)
     , .storeMem "out" 16 (.reg "o1tmp") ]

/-! ### B.2 The inlined-merged composition (one fused body)

Without the leaf boundary, butterfly 1's result `o0` is already in a register,
so butterfly 2 reads it directly, with no copy-out and no reload. The block is
written by hand in this form; it is not the output of `ComInline.inline` or of a
register allocator. The `storeMem o0` and the `loadMem a2` of the boundary form
are absent; `o1` stays in a register until the final store. -/

/-- The inlined-merged chained block. Butterfly 1 computes into registers
    `o0, o1`; butterfly 2 reads `o0` **directly from the register** as its
    `a`-input (no store, no reload), reading its own `b2, w2` from `inp`. The
    two boundary memory instructions of `abiBoundaryBlock` are eliminated. -/
def inlinedMergedBlock : List (JInstr 64) :=
  [ .loadMem "a" "inp" 0
  , .loadMem "b" "inp" 8
  , .loadMem "w" "inp" 16 ]
  ++ butterflyBody "p1" "a" "b" "w" "o0" "o1"
  -- no copy-out / reload: o0 feeds butterfly 2 directly from its register
  ++ [ .loadMem "b2" "inp" 24
     , .loadMem "w2" "inp" 32 ]
  ++ butterflyBody "p2" "o0" "b2" "w2" "o0p" "o1p"
  -- store the three observable outputs (o1 was register-resident throughout)
  ++ [ .storeMem "out" 0 (.reg "o0p")
     , .storeMem "out" 8 (.reg "o1p")
     , .storeMem "out" 16 (.reg "o1") ]

/-- The per-leaf ABI tax this inlining closes: the boundary `storeMem o0`
    (leaf-1 copy-out of the forwarded value) plus the `loadMem a2` (leaf-2
    copy-in reload). Two memory instructions, plus the spurious `o1` round-trip
    (`storeMem o1` / `loadMem o1tmp`). Counted as the instruction-count
    difference between the two blocks. -/
def abiTaxInstrs : Nat := abiBoundaryBlock.length - inlinedMergedBlock.length

/-- The ABI-boundary block is 4 instructions longer than the inlined one: the
    forwarded `o0`'s store + reload, and the `o1` store + reload that the
    register-resident form avoids. -/
theorem abiTaxInstrs_eq : abiTaxInstrs = 4 := by native_decide

/-! ### B.2b Constant time: both compositions

Removing the leaf boundary changes which memory accesses happen, not whether
any of them is secret-indexed. Both blocks address `inp`/`out`/`scratch` only
through literal displacements and reduce with branch-free sign-mask arithmetic,
so both are in the direct-addressing class and both have a machine leakage
trace fixed by the program text. -/

/-- One butterfly body is register ALU only, whatever names it is instantiated
    at. -/
theorem butterflyBody_allDirect (p ra rb rw oLo oHi : String) :
    allDirect (butterflyBody p ra rb rw oLo oHi) = true := by
  simp [allDirect, butterflyBody, IsDirect]; rfl

/-- The ABI-boundary chained block is in the direct-addressing class: the
    copy-out/copy-in round trip uses literal `scratch` displacements. -/
theorem abiBoundaryBlock_allDirect : allDirect abiBoundaryBlock = true := by
  simp [allDirect, abiBoundaryBlock, butterflyBody, IsDirect]; rfl

/-- **Constant time.** The ABI-boundary composition produces the same machine
    leakage trace from any two starting states. -/
theorem abiBoundaryBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ abiBoundaryBlock = blockLeak s₂ abiBoundaryBlock :=
  allDirect_constant_time abiBoundaryBlock abiBoundaryBlock_allDirect s₁ s₂

/-- The inlined-merged block is in the direct-addressing class. -/
theorem inlinedMergedBlock_allDirect : allDirect inlinedMergedBlock = true := by
  simp [allDirect, inlinedMergedBlock, butterflyBody, IsDirect]; rfl

/-- **Constant time.** The inlined-merged composition produces the same machine
    leakage trace from any two starting states — eliminating the boundary
    store/reload keeps the block in the constant-time class. -/
theorem inlinedMergedBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ inlinedMergedBlock = blockLeak s₂ inlinedMergedBlock :=
  allDirect_constant_time inlinedMergedBlock inlinedMergedBlock_allDirect s₁ s₂

/-! ### B.3 Both blocks lower denotation-preservingly through the x86 backend -/

/-- The shared input state: `inp[0,8,16] = a,b,w`; `inp[24,32] = b2,w2`. The
    `inp`/`out`/`scratch` pointer registers only key the memory map. -/
def initState2 (a b w b2 w2 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "inp" then
        if off = 0 then a else if off = 8 then b else if off = 16 then w
        else if off = 24 then b2 else if off = 32 then w2 else 0
      else 0 }

/-- **Lowering correctness for the ABI-boundary block** (an instance of
    `lowerBlock_denote_closed`): lowering to `Com (x86Dialect 64)` and denoting
    on the init state equals `runBlock` on the source block. -/
theorem abi_boundary_lowering_correct (a b w b2 w2 : BitVec 64) :
    (lowerBlock (Γ := []) abiBoundaryBlock).denote (.cons (initState2 a b w b2 w2) .nil)
      = runBlock (initState2 a b w b2 w2) abiBoundaryBlock :=
  lowerBlock_denote_closed abiBoundaryBlock (initState2 a b w b2 w2)

/-- **Lowering correctness for the inlined-merged block** (an instance of
    `lowerBlock_denote_closed`). -/
theorem inlined_merged_lowering_correct (a b w b2 w2 : BitVec 64) :
    (lowerBlock (Γ := []) inlinedMergedBlock).denote (.cons (initState2 a b w b2 w2) .nil)
      = runBlock (initState2 a b w b2 w2) inlinedMergedBlock :=
  lowerBlock_denote_closed inlinedMergedBlock (initState2 a b w b2 w2)

/-! ### B.4 The two forms compute identical observable outputs

The ABI round-trip and the register forwarding are observationally
transparent: both blocks store the same three words to `out`. The structural
reason: after the (identical) first butterfly, register `o0` holds value `V0`
and `o1` holds `V1` in *both* blocks. The ABI form routes `V0` to butterfly 2's
`a`-input through `[scratch+0]` (store then reload) and `V1` to `out[16]`
through `[scratch+8]`; the inlined form feeds `o0`/`o1` directly. Either way
butterfly 2 sees the same `(V0, b2, w2)` and `out[16]` gets `V1`.

We pin this in-Lean as a KAT on a representative input of canonical BabyBear
residues `(a,b,w,b2,w2) = (7, 11, 13, 17, 19)` (all `< p`): `native_decide`
runs both blocks through the compiled `runBlock`/`evalInstr` evaluator and
checks the three stored words are bit-identical. The bench harness re-checks
this equality on the C side (fixed + random vectors) against the same Lean
reference. -/

/-- **KAT: the two forms compute the same observable output words.** On a
    representative canonical input, the ABI-boundary block and the
    inlined-merged block store identical words to `out[0]`, `out[8]`, `out[16]`
    — the inlining only removes the memory round-trip of the forwarded value,
    it does not change the computed result. Pinned via the compiled
    `runBlock` evaluator (the same semantics the lowering theorems use). -/
theorem abi_eq_inlined_outputs_kat :
    let a : BitVec 64 := 7; let b : BitVec 64 := 11; let w : BitVec 64 := 13
    let b2 : BitVec 64 := 17; let w2 : BitVec 64 := 19
    let sa := runBlock (initState2 a b w b2 w2) abiBoundaryBlock
    let si := runBlock (initState2 a b w b2 w2) inlinedMergedBlock
    sa.load "out" 0 = si.load "out" 0
      ∧ sa.load "out" 8 = si.load "out" 8
      ∧ sa.load "out" 16 = si.load "out" 16 := by
  native_decide

/-- A second KAT on a different canonical input (`(1, 2, 3, 4, 5)`), guarding
    against an accidental coincidence on the first vector. -/
theorem abi_eq_inlined_outputs_kat2 :
    let a : BitVec 64 := 1; let b : BitVec 64 := 2; let w : BitVec 64 := 3
    let b2 : BitVec 64 := 4; let w2 : BitVec 64 := 5
    let sa := runBlock (initState2 a b w b2 w2) abiBoundaryBlock
    let si := runBlock (initState2 a b w b2 w2) inlinedMergedBlock
    sa.load "out" 0 = si.load "out" 0
      ∧ sa.load "out" 8 = si.load "out" 8
      ∧ sa.load "out" 16 = si.load "out" 16 := by
  native_decide

/-! ## Part C — liveness-aware register allocation, then emit

The asm printer's default `AsmPrinter.allocGp` is naive first-fit: it gives each
distinct name its own pool register *forever*, never reusing a register after
its value dies. Two full butterflies' working sets exceed the 14-register GP
pool under that scheme — the emit would alias overflow names onto `%rax`. This
is exactly the gap a **liveness-aware register allocation re-run** closes: a
register is freed when its name's last use has passed, so dead scratch/input
registers from butterfly 1 are reused by butterfly 2.

`livenessAllocGp` is the linear-scan allocator (the JInstr-name analogue of
`RegisterAllocation.linearScanAssign`): compute each name's last-use index in
the block, walk the block freeing registers whose owner's last use is behind
us, and assign each newly-seen name the lowest free pool register. It reads the
`JInstr` block only and takes no `RegisterAllocation`; it is independent of
Part A. -/

/-! ### C.1 The liveness-aware allocator -/

/-- All register names of a block, in first-seen order (the names to allocate). -/
def orderedNames {w : Nat} (block : List (JInstr w)) : List String :=
  blockNames block

/-- The last instruction index (0-based) at which `name` is read or written in
    `block`. `none` if it never appears. -/
def lastUseIdx {w : Nat} (block : List (JInstr w)) (name : String) : Option Nat :=
  (block.zipIdx).foldl
    (fun acc (p : JInstr w × Nat) =>
      if (jinstrNames p.1).contains name then some p.2 else acc) none

/-- Linear-scan walker state: `out` is the accumulated name→reg map (each name
    appears once, retained for the whole block — the printer maps names to a
    single physical register); `pool` is the currently-free register list;
    `active` is the list of `(name, reg)` currently live (a register returns to
    `pool` when its active name's last use passes). A register can be reused by
    a *later, non-overlapping* name; the retained `out` records every name. -/
structure ScanSt where
  out : GpAlloc
  pool : List String
  active : GpAlloc

/-- Linear-scan over the block: at each instruction index, return to the pool
    the registers whose active name's last use is strictly before this index,
    then assign each newly-seen name the lowest free pool register, recording it
    permanently in `out` and adding it to `active`. Reuse of a freed register by
    a non-overlapping later name is safe and is what fits two butterflies in the
    14-register pool. `lastUse name` gives the final index `name` is touched. -/
def livenessAllocAux {w : Nat} (lastUse : String → Option Nat) :
    Nat → List (JInstr w) → ScanSt → ScanSt
  | _, [], st => st
  | idx, instr :: rest, st =>
      -- Expire active names whose last use is before idx; return their regs.
      let (stillActive, expired) := st.active.partition (fun pr =>
        match lastUse pr.1 with
        | some lu => decide (lu ≥ idx)
        | none => true)
      let pool := st.pool ++ expired.map Prod.snd
      -- Allocate any not-yet-recorded name touched here (read or written).
      let st' := (jinstrNames instr).foldl
        (fun (s : ScanSt) (n : String) =>
          if (s.out.lookup n).isSome then s   -- already has a permanent reg
          else match s.pool with
            | [] => s                          -- pool exhausted: leave to spill
            | r :: rs =>
                { out := s.out ++ [(n, r)]
                  pool := rs
                  active := s.active ++ [(n, r)] })
        { out := st.out, pool := pool, active := stillActive }
      livenessAllocAux lastUse (idx + 1) rest st'

/-- The liveness-aware allocation: pinned names fixed first (their registers
    removed from the working pool *and* kept active for the whole block so they
    are never reused), then linear-scan with register reuse over the block. The
    returned `GpAlloc` is fed to `AsmPrinter.renderBlockBody`. -/
def livenessAllocGp {w : Nat} (pinned : GpAlloc) (block : List (JInstr w)) :
    GpAlloc :=
  let usedByPinned := pinned.map Prod.snd
  let pool := gpPool.filter (fun r => ¬ usedByPinned.contains r)
  let lu : String → Option Nat := fun n =>
    -- Pinned pointers stay live for the whole block (never expire / reuse).
    if (pinned.lookup n).isSome then some block.length else lastUseIdx block n
  (livenessAllocAux lu 0 block
    { out := pinned, pool := pool, active := pinned }).out

/-! ### C.2 Pins + bodies under the liveness-aware allocator

The ABI-boundary form pins `out → %rdi`, `inp → %rsi`, `scratch → %rdx`; the
inlined form needs no scratch pointer. -/

/-- Register pinning for the ABI-boundary leaf (three pointers). -/
def abiPinned : GpAlloc := [("out", "%rdi"), ("inp", "%rsi"), ("scratch", "%rdx")]

/-- Register pinning for the inlined-merged leaf (two pointers — no scratch). -/
def inlinedPinned : GpAlloc := [("out", "%rdi"), ("inp", "%rsi")]

/-- The ABI-boundary allocation (liveness-aware: reuses dead bf1 regs in bf2). -/
def abiAlloc : GpAlloc := livenessAllocGp abiPinned abiBoundaryBlock

/-- The inlined-merged allocation (liveness-aware). -/
def inlinedAlloc : GpAlloc := livenessAllocGp inlinedPinned inlinedMergedBlock

/-- The ABI-boundary AT&T body. -/
def abiAsmBody : List String := renderBlockBody abiAlloc abiBoundaryBlock

/-- The inlined-merged AT&T body. -/
def inlinedAsmBody : List String := renderBlockBody inlinedAlloc inlinedMergedBlock

/-- **The liveness-aware allocation fits both blocks in the GP pool.** Every
    distinct name of each block (24 for the ABI form, 21 for the inlined form)
    is assigned a pool register — none collapses to the `%rax` spill fallback.
    The naive first-fit `allocGp` would overflow (two butterflies' working sets
    exceed 14 registers); `livenessAllocGp` reuses butterfly 1's dead
    input/scratch registers in butterfly 2. The statement is completeness of
    the assignment only; no theorem relates the allocation to `runBlock`. -/
theorem allocations_complete :
    (orderedNames abiBoundaryBlock).all (fun n => (abiAlloc.lookup n).isSome) = true
      ∧ (orderedNames inlinedMergedBlock).all
          (fun n => (inlinedAlloc.lookup n).isSome) = true := by native_decide

/-- The full ABI-boundary `.s` leaf. The boundary store/reload prints as real
    memory traffic through `%rdx` (scratch). Callee-saved regs pushed/popped. -/
def abiAsm : String :=
  renderLeafFn "plonky3_ntt_bf2chain_abi"
    ["\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"]
    abiAsmBody
    ["\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret"]

/-- The full inlined-merged `.s` leaf (no scratch pointer; the forwarded value
    stays register-resident). -/
def inlinedAsm : String :=
  renderLeafFn "plonky3_ntt_bf2chain_inlined"
    ["\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"]
    inlinedAsmBody
    ["\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret"]

/-- The ABI form has two more memory body lines than the inlined form (the
    boundary store + reload of `o0`, plus the `o1` round-trip). -/
theorem abiAsmBody_longer :
    abiAsmBody.length = inlinedAsmBody.length + 4 := by native_decide

/-- Count the memory instructions (`loadMem`/`storeMem`) of a block — the ABI
    traffic the reg-ptr convention pays. -/
def memOpCount : List (JInstr 64) → Nat
  | [] => 0
  | i :: is =>
      (match i with | .loadMem .. => 1 | .storeMem .. => 1 | _ => 0) + memOpCount is

/-- **The ABI tax in memory traffic.** The ABI-boundary block issues 4 more
    memory instructions than the inlined-merged block: the forwarded `o0`'s
    copy-out store + copy-in reload, and the `o1` store + reload that the
    register-resident inlined form avoids. -/
theorem abi_memops_exceed_inlined :
    memOpCount abiBoundaryBlock = memOpCount inlinedMergedBlock + 4 := by native_decide

/- The ABI form's emitted body references the scratch pointer's register for
    the boundary store/reload; the boundary store line is present in the ABI
    text and absent from the inlined text. -/
#guard (BarrettButterflyKernel.hasSub abiAsm ", 0(%rdx)") && !(BarrettButterflyKernel.hasSub inlinedAsm ", 0(%rdx)")

/-- Emit driver: write both `.s` files for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/ntt_bf2chain_abi.s" abiAsm
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/ntt_bf2chain_inlined.s" inlinedAsm
  IO.println "wrote gen_com/ntt_bf2chain_{abi,inlined}.s (W3 backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.InlinedNttKernel
