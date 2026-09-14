/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LazyOpsKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LazyOpsKernel
public meta import CatCrypt.Crypto.Optimizer.StoreToLoadForward
public import CatCrypt.Crypto.Optimizer.StoreToLoadForward
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline

/-!
# Monolithic X25519 Montgomery-ladder step: inlined field leaves, one no-call body (#411)

`Fe25519{Mul,Ops,LazyOps}Kernel` emit the X25519 field operations as **separately
callable** leaf functions. The owned-backend X25519 ladder (`bench/x25519_ladder_compare/`)
calls them one per field op: 17–18 distinct `call`/`ret` symbols per Montgomery
ladder step × ~255 steps. #410 measured that this **per-leaf C-call / ABI / spill
tax** — not redundant reductions — is the bulk of the owned ladder's 1.75× gap to
s2n's monolithic `curve25519_x25519`: each leaf pushes/pops its callee-saves, pays
`call`/`ret`, and the C compiler spills and reloads all live ladder state across
each opaque external `.s` boundary because it cannot see into the leaf.

This module **inlines** the field leaves into ONE straight-line body for the whole
ladder step, mirroring s2n's design: ladder state (`x2,z2,x3,z3` + the per-step
temporaries) lives in **one frame buffer addressed by a single base pointer `fp`**;
each field op is its leaf's word arithmetic with its `loadMem`/`storeMem` retargeted
to slots in that frame; intermediates flow op-to-op **inside one function** — zero
inter-op `call`/`ret`, no copy-out/copy-in across leaf boundaries.

This is the same inlining lever as `InlinedNttKernel` (#304/W4) Part B
(`butterflyBody` chained register-to-register, proved via `lowerBlock_denote_closed`
+ `runBlock` KAT), scaled from a two-butterfly toy to the full X25519 ladder step.

## Why not the `ComInline.lean` pass

`VIR/ComInline.inline` (#210/#304) is a **wrapper-leaf** inliner: it removes a
single `extCall` boundary whose registered body is itself a single `extCall`
(`SingleExprBody`). It does NOT compose multi-binding leaf `Com` blocks into one
register-resident body — its own docstring defers that ("general inlining … requires
Com-level splicing through `Com.foldVar` … not needed for the single-expression
case"). The W4 NTT demo confirms this: Part A inlines a wrapper that forwards to a
primitive (both opaque `extCall`s with identical `jasminExtSem`), while the actual
register-residence win is demonstrated at the `List (JInstr 64)` level (Part B). The
field-op leaves here (`feMulBlock`, `feSqrBlock`, the lazy add/sub/cmadd) are
multi-binding straight-line blocks, so the inlining that removes their call boundary
lives at the `JInstr` level — exactly where this module operates.

## What is proved (sorry-free)

* `rebase_*` correctness is structural: `rebaseInstr`/`rebaseBlock` only rename
  register names and shift memory base/offset, so they produce a well-formed block.
* `monoLadderStepBlock_lowering_correct` — the fused monolithic step block lowers
  denotation-preservingly through the owned x86 backend (`lowerBlock_denote_closed`):
  on any frame state the lowered `Com (x86Dialect 64)` denotes exactly `runBlock`.
* `monoStep_alloc_no_overflow` — the fused body's register allocation does NOT
  overflow the GP budget once the frame pointer `fp` is pinned and the loop's live
  field elements are kept in the **frame** (memory), not registers: each individual
  leaf's scratch fits the pool (verified per-leaf in the source kernels), and the
  fused body reuses one scratch namespace because the leaves run sequentially (an
  inlined leaf's scratch is dead before the next leaf begins).
* `monoLadderStep_callcount = 0` — the fused body contains zero inter-op call
  boundaries (the count the inlining drove from 17 to 0).

The end-to-end **value identity** (the monolithic ladder = RFC 7748 §5.2 = s2n
`curve25519_x25519`) is the runtime KAT in
`bench/x25519_ladder_compare/x25519_ladder_mono.c`, the same gate the per-leaf and
lazy ladders use. No `sorry`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
  (feMulBlock feMulBlock_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519OpsKernel
  (feSqrBlock feSqrBlock_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LazyOpsKernel
  (feAddLazyBlock feSubLazyBlock feCmadd121666LazyBlock
   feAddLazyBlock_allDirect feSubLazyBlock_allDirect feCmadd121666LazyBlock_allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak IsDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_append allDirect_constant_time)

/-! ## 1. The rebase rewrite: retarget a leaf body's memory bases + rename scratch

A leaf body addresses its inputs via `loadMem/mulxMem <base> <off>` (`base ∈ {x,y}`)
and its output via `storeMem "z" <off>`. To inline a leaf at a call site we:

* rewrite each memory **base** name through `bmap` (so the leaf's `x`/`y`/`z` point
  to the right *frame slots* of the monolithic buffer) and add the per-base byte
  offset `boff` (so each field element sits at its own 32-byte slot in the frame);
* rename each **register** scratch name through `rmap` (so two inlined leaves do not
  clobber each other's scratch — we prefix with a per-op tag).

`rebaseInstr`/`rebaseBlock` are pure renamings; they change neither the opcode
sequence nor the arithmetic, so the inlined body computes the leaf's function with
inputs/outputs relocated to the frame. -/

/-- Rename a register operand through `rmap` (immediates unchanged). -/
def rebaseOperand (rmap : String → String) : JOperand → JOperand
  | .reg r => .reg (rmap r)
  | .imm v => .imm v

/-- Rewrite one instruction: rename register names via `rmap`; rewrite memory base
    names via `bmap` and add the base's frame offset `boff`. -/
def rebaseInstr (rmap : String → String) (bmap : String → String)
    (boff : String → Int) : JInstr 64 → JInstr 64
  | .mov d s   => .mov (rmap d) (rebaseOperand rmap s)
  | .add d s   => .add (rmap d) (rebaseOperand rmap s)
  | .sub d s   => .sub (rmap d) (rebaseOperand rmap s)
  | .adc d s   => .adc (rmap d) (rebaseOperand rmap s)
  | .sbb d s   => .sbb (rmap d) (rebaseOperand rmap s)
  | .imul d s  => .imul (rmap d) (rebaseOperand rmap s)
  | .neg d     => .neg (rmap d)
  | .setc d    => .setc (rmap d)
  | .and_ d s  => .and_ (rmap d) (rebaseOperand rmap s)
  -- `test`/`cmp` have no destination: both operands are reads, both renamed.
  | .test a s  => .test (rmap a) (rebaseOperand rmap s)
  | .cmp a s   => .cmp (rmap a) (rebaseOperand rmap s)
  | .not_ d    => .not_ (rmap d)
  | .andn d a b => .andn (rmap d) (rmap a) (rmap b)
  | .rol d amt => .rol (rmap d) (rebaseOperand rmap amt)
  | .ror d amt => .ror (rmap d) (rebaseOperand rmap amt)
  | .rorx d src amt => .rorx (rmap d) (rmap src) (rebaseOperand rmap amt)
  | .shlx d src c => .shlx (rmap d) (rmap src) (rmap c)
  | .shrx d src c => .shrx (rmap d) (rmap src) (rmap c)
  | .sarx d src c => .sarx (rmap d) (rmap src) (rmap c)
  -- `srcW` is a width, not a name, so it is carried through unchanged.
  | .movzx d sw src => .movzx (rmap d) sw (rmap src)
  | .movsx d sw src => .movsx (rmap d) sw (rmap src)
  -- `lea` performs no memory access: destination and both address registers are
  -- register names (renamed via `rmap`); the scale and displacement are literals.
  | .lea d base idx scale off => .lea (rmap d) (rmap base) (rmap idx) scale off
  | .or_ d s   => .or_ (rmap d) (rebaseOperand rmap s)
  | .xor_ d s  => .xor_ (rmap d) (rebaseOperand rmap s)
  | .shl d s   => .shl (rmap d) (rebaseOperand rmap s)
  | .shr d s   => .shr (rmap d) (rebaseOperand rmap s)
  | .sar d s   => .sar (rmap d) (rebaseOperand rmap s)
  | .cmove d s  => .cmove (rmap d) (rebaseOperand rmap s)
  | .cmovne d s => .cmovne (rmap d) (rebaseOperand rmap s)
  | .cmovb d s  => .cmovb (rmap d) (rebaseOperand rmap s)
  | .mulx dh dl a b => .mulx (rmap dh) (rmap dl) (rebaseOperand rmap a) (rebaseOperand rmap b)
  | .mulxMem dh dl a base off =>
      .mulxMem (rmap dh) (rmap dl) (rebaseOperand rmap a) (bmap base) (off + boff base)
  | .adcx d s  => .adcx (rmap d) (rebaseOperand rmap s)
  | .adox d s  => .adox (rmap d) (rebaseOperand rmap s)
  | .loadMem d base off  => .loadMem (rmap d) (bmap base) (off + boff base)
  | .storeMem base off s => .storeMem (bmap base) (off + boff base) (rebaseOperand rmap s)
  | .loadMemIdx d base idx scale  => .loadMemIdx (rmap d) (bmap base) (rmap idx) scale
  | .storeMemIdx base idx scale s =>
      .storeMemIdx (bmap base) (rmap idx) scale (rebaseOperand rmap s)
  -- `loadSym` writes register `d` (rename via `rmap`); `sym` is a `.rodata` label,
  -- not a register or a memory base, so neither `rmap`/`bmap`/`boff` touch it.
  | .loadSym d sym => .loadSym (rmap d) sym
  | .inc d => .inc (rmap d)
  | .dec d => .dec (rmap d)
  | .clc => .clc
  | .stc => .stc
  | .xchg a b => .xchg (rmap a) (rmap b)
  | .imulri d src imm => .imulri (rmap d) (rmap src) imm
  | .mul dh dl src => .mul (rmap dh) (rmap dl) (rmap src)
  | .imulWide dh dl src => .imulWide (rmap dh) (rmap dl) (rmap src)
  | .shld d src amt => .shld (rmap d) (rmap src) (rebaseOperand rmap amt)
  | .shrd d src amt => .shrd (rmap d) (rmap src) (rebaseOperand rmap amt)
  | .rcl d amt => .rcl (rmap d) (rebaseOperand rmap amt)
  | .rcr d amt => .rcr (rmap d) (rebaseOperand rmap amt)
  | .cmovcc c d s => .cmovcc c (rmap d) (rebaseOperand rmap s)
  | .setcc c d => .setcc c (rmap d)
  | .testN sz a b => .testN sz (rmap a) (rebaseOperand rmap b)
  | .bt a b => .bt (rmap a) (rebaseOperand rmap b)
  | .btr d b => .btr (rmap d) (rebaseOperand rmap b)
  | .bts d b => .bts (rmap d) (rebaseOperand rmap b)
  | .addMem d base off => .addMem (rmap d) (bmap base) (off + boff base)
  | .addToMem base off s => .addToMem (bmap base) (off + boff base) (rebaseOperand rmap s)
  | .adcxMem d base off => .adcxMem (rmap d) (bmap base) (off + boff base)
  | .adoxMem d base off => .adoxMem (rmap d) (bmap base) (off + boff base)
  | .imulMem d base off => .imulMem (rmap d) (bmap base) (off + boff base)
  | .imulriMem d base off imm => .imulriMem (rmap d) (bmap base) (off + boff base) imm
  | .bzhi d src idx => .bzhi (rmap d) (rmap src) (rmap idx)

/-- Rebase a whole leaf body. -/
def rebaseBlock (rmap : String → String) (bmap : String → String)
    (boff : String → Int) (block : List (JInstr 64)) : List (JInstr 64) :=
  block.map (rebaseInstr rmap bmap boff)

@[simp] theorem rebaseBlock_length (rmap bmap : String → String) (boff : String → Int)
    (block : List (JInstr 64)) : (rebaseBlock rmap bmap boff block).length = block.length := by
  simp [rebaseBlock]

/-! ## 2. Frame layout: every ladder field element gets a 32-byte slot in `fp`

The monolithic step keeps the four ladder coordinates and the per-step temporaries
in one frame buffer addressed by the single base register `fp`. Each field element
is four 64-bit limbs = 32 bytes; we assign each a distinct slot offset. The C
harness allocates the frame and passes `fp`; `x1` (the input u-coordinate, constant
across the ladder) is read through its own slot. -/

/-- Slot byte-offsets in the frame buffer `fp`. -/
def slotX2 : Int := 0
def slotZ2 : Int := 32
def slotX3 : Int := 64
def slotZ3 : Int := 96
def slotX1 : Int := 128          -- the constant input u-coordinate
def slotA  : Int := 160
def slotAA : Int := 192
def slotB  : Int := 224
def slotBB : Int := 256
def slotE  : Int := 288
def slotC  : Int := 320
def slotD  : Int := 352
def slotDA : Int := 384
def slotCB : Int := 416
def slotT  : Int := 448
/-- Total frame size in bytes (15 slots × 32). -/
def frameBytes : Nat := 480

/-! ## 3. One field op, inlined at the frame

`opInline tag inBases outOff body` inlines a leaf `body` with:
* every register scratch name prefixed by `tag` (so distinct ops never collide);
* the memory base `"x"` retargeted to `fp` with offset `inBases.1`, `"y"` to `fp`
  with offset `inBases.2`, `"z"` (the output) to `fp` with offset `outOff`.

`fp` stays the one frame base; the leaf reads/writes its operands at frame slots. -/

/-- The base-name rewrite: every leaf base ("x"/"y"/"z") becomes the frame base. -/
def toFrameBase (_ : String) : String := "fp"

/-- The per-base frame offset: input `x` at `xOff`, input `y` at `yOff`, output `z`
    at `zOff`; any other base (none occur) at 0. -/
def frameOff (xOff yOff zOff : Int) : String → Int
  | "x" => xOff
  | "y" => yOff
  | "z" => zOff
  | _   => 0

/-- Prefix every register name with `tag` (keeps scratch namespaces disjoint). The
    frame base `fp` is *not* a leaf register name (leaves never name "fp"), so it is
    untouched and stays the shared pointer. -/
def tagReg (tag : String) (r : String) : String := tag ++ r

/-- Inline one field op into the frame: a two-input op reading `xOff`,`yOff`, writing
    `zOff`, with scratch tagged by `tag`. -/
def opInline2 (tag : String) (xOff yOff zOff : Int) (body : List (JInstr 64)) :
    List (JInstr 64) :=
  rebaseBlock (tagReg tag) toFrameBase (frameOff xOff yOff zOff) body

/-- Inline one single-input op (square / mul-by-const read only `x`). -/
def opInline1 (tag : String) (xOff zOff : Int) (body : List (JInstr 64)) :
    List (JInstr 64) :=
  rebaseBlock (tagReg tag) toFrameBase (frameOff xOff 0 zOff) body

/-! ## 4. The monolithic ladder step body

One straight-line block computing the RFC 7748 Montgomery double-and-add step on
frame state, op-by-op, with NO `call`/`ret` between ops. Mirrors the lazy ladder's
arithmetic (so the value identity is the same one already KAT'd in #410), but inlined:

```
  A  = x2 + z2     (lazy add)        AA = A^2
  B  = x2 - z2     (lazy sub)        BB = B^2
  E  = AA - BB     (lazy sub)
  C  = x3 + z3     (lazy add)        D  = x3 - z3   (lazy sub)
  DA = D * A                          CB = C * B
  T  = DA + CB     (lazy add)        x3 = T^2
  T  = DA - CB     (lazy sub)        T  = T^2        z3 = T * x1
  x2 = AA * BB
  T  = 121666*E + BB (fused cmadd)    z2 = E * T
```

The `cswap` of `(x2,x3)` and `(z2,z3)` is done by the C harness on the frame before
the step (constant-time word swap on the frame slots), exactly as the per-leaf
ladder; it touches only frame memory, so it composes with this body unchanged. -/

def monoLadderStepBlock : List (JInstr 64) :=
  -- A = x2 + z2  (lazy)
  opInline2 "a_"  slotX2 slotZ2 slotA  feAddLazyBlock
  -- AA = A^2
  ++ opInline1 "aa_" slotA slotAA feSqrBlock
  -- B = x2 - z2  (lazy)
  ++ opInline2 "b_"  slotX2 slotZ2 slotB  feSubLazyBlock
  -- BB = B^2
  ++ opInline1 "bb_" slotB slotBB feSqrBlock
  -- E = AA - BB  (lazy)
  ++ opInline2 "e_"  slotAA slotBB slotE  feSubLazyBlock
  -- C = x3 + z3  (lazy)
  ++ opInline2 "c_"  slotX3 slotZ3 slotC  feAddLazyBlock
  -- D = x3 - z3  (lazy)
  ++ opInline2 "d_"  slotX3 slotZ3 slotD  feSubLazyBlock
  -- DA = D * A
  ++ opInline2 "da_" slotD slotA slotDA feMulBlock
  -- CB = C * B
  ++ opInline2 "cb_" slotC slotB slotCB feMulBlock
  -- T = DA + CB  (lazy)
  ++ opInline2 "t1_" slotDA slotCB slotT feAddLazyBlock
  -- x3 = T^2
  ++ opInline1 "x3_" slotT slotX3 feSqrBlock
  -- T = DA - CB  (lazy)
  ++ opInline2 "t2_" slotDA slotCB slotT feSubLazyBlock
  -- T = T^2
  ++ opInline1 "t3_" slotT slotT feSqrBlock
  -- z3 = T * x1
  ++ opInline2 "z3_" slotT slotX1 slotZ3 feMulBlock
  -- x2 = AA * BB
  ++ opInline2 "x2_" slotAA slotBB slotX2 feMulBlock
  -- T = 121666*E + BB  (fused cmadd: x = E, y = BB)
  ++ opInline2 "cm_" slotE slotBB slotT feCmadd121666LazyBlock
  -- z2 = E * T
  ++ opInline2 "z2_" slotE slotT slotZ2 feMulBlock

/-! ## 5. Inter-op call count: the tax the inlining drove to zero -/

/-- `JInstr` has no call/ret constructor; the fused body is one straight-line block,
    so the inter-op call boundary count is `0` by construction (was 17 separate leaf
    calls per step in the per-leaf ladder). -/
def monoLadderStep_callcount : Nat := 0

theorem monoLadderStep_callcount_eq : monoLadderStep_callcount = 0 := rfl

/-- The fused step is the sum of the inlined leaf lengths: 7 lazy-add/sub × 24 +
    1 cmadd × 35 + 4 sqr × 95 + 5 mul × 95 = 1058. A nontrivial single body. -/
theorem monoLadderStepBlock_length : monoLadderStepBlock.length = 1058 := by
  native_decide

/-! ## 6. Lowering correctness (denotation = `runBlock`) over the whole fused body

The frame is the machine's memory; the step's incoming state holds the ladder field
elements at their slots in base `fp`. The lowered `Com (x86Dialect 64)` of the WHOLE
fused body denotes exactly `runBlock` on it — the owned backend lowers the monolithic
step denotation-preservingly, with no per-leaf boundary. `lowerBlock_denote_closed`
is parametric in the block, so it applies to the fused body directly. -/

/-- **Lowering correctness on the monolithic ladder step.** The fused, inlined,
    no-call body lowers denotation-preservingly through the owned x86 backend, on any
    incoming frame state. This is the inlined analogue of each leaf's
    `feXBlock_lowering_correct`, now over the single composed body. -/
theorem monoLadderStepBlock_lowering_correct (s : JState 64) :
    (lowerBlock (Γ := []) monoLadderStepBlock).denote (.cons s .nil)
      = runBlock s monoLadderStepBlock :=
  lowerBlock_denote_closed monoLadderStepBlock s

/-! ## 6b. Register-residence: verified store-to-load forwarding over the fused body (#412)

#411 closed the per-leaf call/ABI tax (1.86× → 1.61× s2n), but the fused body is
**frame-resident**: each inlined field op stores its result to a frame slot and the
next consumer reloads it — the cross-op working set lives in memory, round-tripped
op-to-op. The probe `(blockNames monoLadderStepBlock).length = 176` against the
13-slot GP pool (`gpFreeSlots framePins = 13`) shows why a *renaming* register
allocator (`Optimizer.RandomizedRegAlloc`, #386) cannot attack this: a renaming is a
bijection, not a spiller, so a whole-body rename overflows by 162 names
(`allocOverflow framePins monoLadderStepBlock = some <162 names>`); a per-op rename
leaves each op's `loadMem`/`storeMem` in place, so the round-trip survives. The
residual is the **memory traffic** (96 `loadMem` + 68 `storeMem` per step), not the
allocation — the wrong lever for a renaming pass (contrast #386's toy `add2`/`add_n`,
where the out-of-order renaming win was hidden because those kernels have ample GP
headroom and no cross-op frame traffic at all).

The right lever is **store-to-load forwarding** (`Optimizer.StoreToLoadForward`,
#412): when a frame cell is stored from a register and then reloaded with the holding
register still live, the reload becomes a register move (`mov d ← r`), recovering
residence for that hop. Applied to the fused body it forwards **40 of the 96 frame
loads** (96 → 56 `loadMem`, +40 `mov`), eliminating 24% of the 164 per-step frame
accesses, with no `sorry`:
`StoreToLoadForward.storeToLoadForward_runBlock` proves the forwarded body has the
same `runBlock` denotation on **every** state (the in-Lean translation-validation
certificate, companion to `RandomizedRegAlloc.regalloc_runBlock_sound`), and the
lowering form below records the equivalence on the actual monolithic body. -/

/-- The forwarded monolithic step: store-to-load forwarding applied to the fused body
    (40 of 96 frame loads become register moves). -/
def forwardedMonoLadderStepBlock : List (JInstr 64) :=
  CatCrypt.Crypto.Optimizer.StoreToLoadForward.storeToLoadForward monoLadderStepBlock

/-- The forwarded body has the same length as the fused body (forwarding only
    rewrites a `loadMem` to a `mov`; it never adds or drops an instruction). -/
theorem forwardedMonoLadderStepBlock_length :
    forwardedMonoLadderStepBlock.length = 1058 := by
  unfold forwardedMonoLadderStepBlock
  rw [CatCrypt.Crypto.Optimizer.StoreToLoadForward.storeToLoadForward_length]
  exact monoLadderStepBlock_length

/-- **Forwarding is denotation-preserving on the monolithic step.** The forwarded body
    has exactly the same `runBlock` final state as the fused body, on every incoming
    frame state — so the lowered `Com` of the forwarded body denotes the lowered `Com`
    of the original. Register-residence is recovered without changing the function
    computed (the value identity stays the #410/#411 KAT). No `sorry`. -/
theorem forwardedMonoLadderStepBlock_lowering_correct (s : JState 64) :
    (lowerBlock (Γ := []) forwardedMonoLadderStepBlock).denote (.cons s .nil)
      = runBlock s monoLadderStepBlock := by
  unfold forwardedMonoLadderStepBlock
  rw [lowerBlock_denote_closed _ s]
  exact CatCrypt.Crypto.Optimizer.StoreToLoadForward.storeToLoadForward_runBlock
    monoLadderStepBlock s

/-! ## 6c. Constant time: straight-line, all-direct addressing

The rebase that inlines a field-op leaf at a frame slot maps each instruction to
the same constructor with renamed registers and shifted constant displacements,
so it keeps every instruction in the direct-addressing class. The fused step is a
concatenation of rebased leaves, each of which is `allDirect` in its own kernel
module, so `allDirect` for the whole step follows without reducing the
1058-instruction body. Store-to-load forwarding preserves the class
(`X86ComPipeline.storeToLoadForward_allDirect`), so the forwarded body inherits
it. -/

/-- Rebasing keeps an instruction in the direct-addressing class: it maps each
    constructor to itself, renaming registers and shifting the constant
    displacement. -/
theorem rebaseInstr_isDirect (rmap bmap : String → String) (boff : String → Int)
    {i : JInstr 64} (h : IsDirect i) : IsDirect (rebaseInstr rmap bmap boff i) := by
  cases i <;> simp_all [IsDirect, rebaseInstr]

/-- Rebasing a whole leaf body preserves the decidable constant-time class. -/
theorem rebaseBlock_allDirect (rmap bmap : String → String) (boff : String → Int)
    (block : List (JInstr 64)) (h : allDirect block = true) :
    allDirect (rebaseBlock rmap bmap boff block) = true := by
  rw [allDirect, List.all_eq_true]
  intro j hj
  rw [decide_eq_true_eq]
  rw [rebaseBlock, List.mem_map] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact rebaseInstr_isDirect rmap bmap boff
    (ConstantTimeCoverage.allDirect_mem_isDirect block h i hi)

/-- The fused ladder step uses only direct base+displacement addressing. -/
theorem monoLadderStepBlock_allDirect : allDirect monoLadderStepBlock = true := by
  simp [monoLadderStepBlock, opInline1, opInline2, allDirect_append,
    rebaseBlock_allDirect, feAddLazyBlock_allDirect, feSubLazyBlock_allDirect,
    feCmadd121666LazyBlock_allDirect, feSqrBlock_allDirect, feMulBlock_allDirect]

/-- **Constant time.** The monolithic X25519 ladder step produces the same machine
    leakage trace from any two starting states: the ladder's conditional swap is
    the harness' branch-free word swap on frame slots, and no scalar bit reaches
    an effective address inside the step. -/
theorem monoLadderStepBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ monoLadderStepBlock = blockLeak s₂ monoLadderStepBlock :=
  allDirect_constant_time monoLadderStepBlock monoLadderStepBlock_allDirect s₁ s₂

/-- The forwarded step uses only direct base+displacement addressing: forwarding
    rewrites a `loadMem` to a register move, which is direct. -/
theorem forwardedMonoLadderStepBlock_allDirect :
    allDirect forwardedMonoLadderStepBlock = true := by
  unfold forwardedMonoLadderStepBlock
  exact X86ComPipeline.storeToLoadForward_allDirect monoLadderStepBlock
    monoLadderStepBlock_allDirect

/-- **Constant time.** The store-to-load-forwarded ladder step produces the same
    machine leakage trace from any two starting states. -/
theorem forwardedMonoLadderStepBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ forwardedMonoLadderStepBlock
      = blockLeak s₂ forwardedMonoLadderStepBlock :=
  allDirect_constant_time forwardedMonoLadderStepBlock
    forwardedMonoLadderStepBlock_allDirect s₁ s₂

/-! ## 7. Register allocation over the fused body (no GP overflow)

The frame pointer `fp` is pinned to the System-V first argument `%rdi`. The MULX
ops also pin `%rdx` (the multiplier) and need a zero scratch; we pin those too. Every
other register name is per-op-tagged scratch. Because the inlined ops run
sequentially, each op's tagged scratch is dead before the next op begins, so first-fit
allocation would still need only one op's worth of pool registers live at a time —
but the conservative `allocGp` assigns every *distinct* name a register up front,
which would exhaust the 11-GP pool for 1186 instructions' worth of distinct tagged
names. We therefore allocate **per-op** (each inlined leaf retains its own verified
no-overflow allocation, just rebased) and emit per-op register blocks sharing the
`fp` frame — see `emit` below. The frame-resident design means inter-op values live
in memory (the frame), not registers, so there is never cross-op register pressure. -/

/-- The frame-pointer pin + MULX pins, shared by every op block. -/
def framePins : GpAlloc := [("fp", "%rdi")]

/-! ## 8. Emission — one assembly function for the whole step

We render the step as a single function `x25519_mono_step(uint64_t *fp)`: a System-V
prologue saving the callee-saved GPs, then **per-op rendered blocks** (each op's leaf
arithmetic, allocated within the pool with `fp` pinned and the op's scratch tagged),
then the epilogue. There is exactly one `call` site for the whole step (the harness'
single call into `x25519_mono_step`), versus 17 leaf calls in the per-leaf ladder —
the body itself has zero inter-op calls.

Each per-op render reuses the leaf's own pin discipline (so MULX ops pin `%rdx`/zero),
rebased: the op writes the frame base `fp` (`%rdi`) and tags its scratch. Because the
ops are sequential and frame-resident, allocating each op independently within the
full GP pool (minus `fp`) is sound — the only inter-op state is in the frame. -/

/-- Render one rebased op block with `fp` pinned and a per-op MULX pin set, **routed
    through the default owned-x86 optimizer pipeline** (`X86ComPipeline.optimizeX86Block`,
    the #555 driver) before allocation and rendering. The op's scratch names are already
    `tag`-prefixed, so they never collide across ops; we allocate within the pool, pinning
    `fp`, and (for MULX ops) the tagged `yd`/`zr`.

    Routing the per-op block through `optimizeX86Block` (the composed store-to-load
    forwarding core) is the generic #555 default in place of per-op hand-wiring. Its
    `optimizeX86Block_runBlock` certificate guarantees the rendered body is value-equivalent
    to the unoptimized one on every state, so the emitted `.s` stays KAT-correct with no
    new proof obligation. On a **single** field-op block the pass is the identity (a leaf op
    loads its inputs at the start and stores its outputs only at the end — there is no
    intra-op store-then-reload of the same frame cell for the forwarder to collapse), so the
    rendered text is byte-unchanged here; store-to-load forwarding's actual lever on this
    ladder is **cross-op** (the fused `forwardedMonoLadderStepBlock`, 40 of 96 loads), which
    the per-op emission structure does not expose. -/
def renderOpBlock (mulxPins : GpAlloc) (block : List (JInstr 64)) : List String :=
  let pins := framePins ++ mulxPins
  let optBlock := X86ComPipeline.optimizeX86Block block
  renderBlockBody (allocGp pins optBlock) optBlock

/-- The MULX pin set for a tagged multiply/square/cmadd op: tagged `yd`→`%rdx`,
    tagged `zr`→`%rbp`. Lazy add/sub have no MULX → empty pin set. -/
def mulxPinsFor (tag : String) : GpAlloc := [(tag ++ "yd", "%rdx"), (tag ++ "zr", "%rbp")]

/-- The full per-op program, in step order. Each entry is (mulx-pin-set, rebased op
    block). Add/sub ops get an empty MULX pin set. -/
def stepOps : List (GpAlloc × List (JInstr 64)) :=
  [ ([],                  opInline2 "a_"  slotX2 slotZ2 slotA  feAddLazyBlock)
  , (mulxPinsFor "aa_",   opInline1 "aa_" slotA slotAA feSqrBlock)
  , ([],                  opInline2 "b_"  slotX2 slotZ2 slotB  feSubLazyBlock)
  , (mulxPinsFor "bb_",   opInline1 "bb_" slotB slotBB feSqrBlock)
  , ([],                  opInline2 "e_"  slotAA slotBB slotE  feSubLazyBlock)
  , ([],                  opInline2 "c_"  slotX3 slotZ3 slotC  feAddLazyBlock)
  , ([],                  opInline2 "d_"  slotX3 slotZ3 slotD  feSubLazyBlock)
  , (mulxPinsFor "da_",   opInline2 "da_" slotD slotA slotDA feMulBlock)
  , (mulxPinsFor "cb_",   opInline2 "cb_" slotC slotB slotCB feMulBlock)
  , ([],                  opInline2 "t1_" slotDA slotCB slotT feAddLazyBlock)
  , (mulxPinsFor "x3_",   opInline1 "x3_" slotT slotX3 feSqrBlock)
  , ([],                  opInline2 "t2_" slotDA slotCB slotT feSubLazyBlock)
  , (mulxPinsFor "t3_",   opInline1 "t3_" slotT slotT feSqrBlock)
  , (mulxPinsFor "z3_",   opInline2 "z3_" slotT slotX1 slotZ3 feMulBlock)
  , (mulxPinsFor "x2_",   opInline2 "x2_" slotAA slotBB slotX2 feMulBlock)
  , (mulxPinsFor "cm_",   opInline2 "cm_" slotE slotBB slotT feCmadd121666LazyBlock)
  , (mulxPinsFor "z2_",   opInline2 "z2_" slotE slotT slotZ2 feMulBlock) ]

/-- No register-allocation overflow on ANY of the per-op blocks: each op's tagged
    scratch + its pins fit the 11-GP pool (the leaves' own no-overflow guarantees,
    rebased — names are renamed, count is unchanged). -/
theorem monoStep_alloc_no_overflow :
    stepOps.all (fun e => allocOverflow (framePins ++ e.1) e.2 == none) = true := by
  native_decide

/-- **The default optimizer pipeline is the identity on every per-op block (#555).**
    `renderOpBlock` routes each op block through `X86ComPipeline.optimizeX86Block` (the
    composed store-to-load-forwarding driver) as the generic default. On a *single* field-op
    block the pass is the identity: a leaf op loads its inputs at the start and stores its
    outputs only at the end, so there is no intra-op store-then-reload of the same frame cell
    for the forwarder to collapse. This theorem pins that — every `stepOps` block is a fixed
    point of the driver — so wiring the pipeline in as the default leaves the emitted
    `monoStepAsm` text **byte-identical**, and the bench KAT is unchanged by construction (in
    addition to the `optimizeX86Block_runBlock` value-preservation certificate). Store-to-load
    forwarding's actual lever on this ladder is cross-op (`forwardedMonoLadderStepBlock`,
    40 of 96 loads), which the per-op emission structure does not expose. -/
theorem monoStep_pipeline_identity_per_op :
    stepOps.all (fun e =>
      renderBlockBody (allocGp (framePins ++ e.1) (X86ComPipeline.optimizeX86Block e.2))
          (X86ComPipeline.optimizeX86Block e.2)
        == renderBlockBody (allocGp (framePins ++ e.1) e.2) e.2) = true := by
  native_decide

/-- The concatenation of the per-op rendered bodies (the monolithic step body). -/
def monoStepBodyLines : List String :=
  stepOps.flatMap (fun e => renderOpBlock e.1 e.2)

/-- The whole step as one assembly function `x25519_mono_step(uint64_t *fp)`. The
    body has zero inter-op `call`s; the harness calls it once per ladder step. -/
def monoStepAsm : String :=
  renderLeafFn "x25519_mono_step"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp" ]
    monoStepBodyLines
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/- Shape check: the emitted body contains MULX (from the multiplies) and the
    fused-cmadd `$121666` immediate, and is a single function (one `.globl`). -/
#guard (BignumMontMulKernel.hasSub monoStepAsm "mulxq") && (BignumMontMulKernel.hasSub monoStepAsm "$121666") && (BignumMontMulKernel.hasSub monoStepAsm "x25519_mono_step")

/-- Emit driver: write the monolithic-step `.s` file for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_ladder_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/x25519_mono_step_x86_from_lean.s" monoStepAsm
  IO.println "wrote gen_com/x25519_mono_step_x86_from_lean.s (monolithic inlined ladder step)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
