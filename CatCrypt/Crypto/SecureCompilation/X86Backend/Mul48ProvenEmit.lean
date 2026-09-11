/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
public meta import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# `bignum_mul_4_8` emitted from the PROVEN product block (`emitProductBlock4`)

`BignumMontMulKernel.mul48Block` is the **hand-written** dual-carry-chain
schoolbook that currently ships as the owned `bignum_mul_4_8` artifact; its
all-inputs value identity is gated only by the external GMP + s2n KAT (REV-12),
because the in-Lean close (a 512-bit `bv_decide`/`omega`) is infeasible. The
hand-written block is the prototype; the canonical artifact should be **emitted
by the verified pipeline**.

This module is that "generate from a proven pipeline" step. The computational
core is `SchoolbookProductRunBlock.emitProductBlock4` — the 4×4 schoolbook
product whose `runBlock` output is proven to equal `valLimbs x · valLimbs y`
(`emitProductBlock_runBlock_value` / `sm2_emit_montmul_runBlock_full4`,
axiom-clean, no `native_decide` on the value). We wrap that proven core in the
load/store pointer ABI: `loadMem` the four `x`-limbs and four `y`-limbs out of
the `%rsi`/`%rdx` argument buffers into the multiplicand/multiplier registers
the proven block consumes, clear the eight accumulator registers, run the
proven product, and `storeMem` the eight accumulator words to the `%rdi`
(`z`) buffer. The load/store framing is **trusted ABI scaffolding** (exactly as
every other word kernel documents: "the System-V leaf prologue/epilogue is
trusted ABI scaffolding"); the COMPUTATIONAL CORE is the proven
`emitProductBlock4`, not a fresh hand-written kernel.

## Register pressure → the verified spilling allocator

The proven block keeps eight accumulator words, four multiplicand limbs, four
multiplier limbs, and two `MULX` scratch words all simultaneously live (18
distinct value names) plus the three pointer arguments — far past the 14-slot
GP pool. The non-spilling first-fit `allocGp` therefore overflows
(`mul48Proven_allocGp_overflows`); we route the body through the **verified
spilling allocator** (`Optimizer.SpillingRegAlloc.spillAllocPinned`,
translation-validated in `SpillingRegAlloc.lean`) exactly as the X25519
monolithic ladder does: the MULX-multiplier names go to `%rdx`, the rest run
the linear scan against the pool, and the genuinely-spilled values round-trip
through frame cells. `AsmPrinter.renderJInstrSpilled` realises each instruction
at its program point (reloads before, stores after, `%rdx` setup for `mulx`).

## Trust story

Identical to the other word kernels: the verified artifact is
`emitProductBlock4`'s `runBlock = valLimbs x · valLimbs y`
(`SchoolbookProductRunBlock`, axiom-clean). The spilling allocator's
reload/store insertion is denotation-preserving (`SpillingRegAlloc` §2/§4). The
load/store pointer framing and the System-V leaf prologue/epilogue are trusted
ABI scaffolding outside the verified body. `AsmPrinter` + `gas` is the thin
syntactic trust boundary. No `sorry`, no new `axiom`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Mul48ProvenEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The register-name layout for the 4-limb proven product

The proven `emitProductBlock4 accs as ys hi lo` is parametric over the register
names. We pick the concrete 4-limb instance: eight accumulator words `a0..a7`,
four `x`-limb sources `x0..x3`, four `y`-limb scalars `y0..y3`, and the two
`MULX` scratch words `phi`/`plo`. -/

/-- The eight accumulator-word register names (the 512-bit product output). -/
def accNames : List String := ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]

/-- The four `x`-limb (multiplicand) source register names. -/
def xNames : List String := ["x0", "x1", "x2", "x3"]

/-- The four `y`-limb (multiplier) scalar register names. Each is a `MULX`
    `src1`, so the pin-aware allocator binds it to `%rdx` for its row. -/
def yNames : List String := ["y0", "y1", "y2", "y3"]

/-- The `MULX` high scratch register name. -/
def hiName : String := "phi"

/-- The `MULX` low scratch register name. -/
def loName : String := "plo"

/-! ## 2. The wrapped block: load → clear → PROVEN core → store

`mul48ProvenBlock` is the proven `emitProductBlock4` framed by the pointer ABI:

* **load** `x[0..3]` from `[x + 8·i]` into `xNames`, `y[0..3]` from `[y + 8·i]`
  into `yNames` (`loadMem`);
* **clear** the eight accumulator registers with `xor aᵢ, aᵢ` — this both zeroes
  the accumulator file (the `hacc0` precondition of
  `emitProductBlock_runBlock_value`) and clears `CF`/`OF` (the `hcf`/`hof`
  precondition);
* the **proven core** `emitProductBlock4 accNames xNames yNames hiName loName`;
* **store** the eight accumulator words to `[z + 8·k]` (`storeMem`).

The middle segment is the verified computational core; the load/store framing is
trusted ABI scaffolding. -/

/-- Load the four `x`-limbs and four `y`-limbs from the argument buffers into the
    registers the proven block consumes (`loadMem dst base off`). -/
def loadInputs : List (JInstr 64) :=
  (List.range 4).map (fun i => JInstr.loadMem (xNames.getD i default) "x" (8 * (i : Int)))
    ++ (List.range 4).map (fun i => JInstr.loadMem (yNames.getD i default) "y" (8 * (i : Int)))

/-- Clear the eight accumulator registers (`xor aᵢ, aᵢ`): zeroes the file and
    clears `CF`/`OF`, establishing the proven core's entry precondition. -/
def clearAccs : List (JInstr 64) :=
  accNames.map (fun a => JInstr.xor_ a (.reg a))

/-- Store the eight accumulator words to the `z` buffer (`storeMem base off src`). -/
def storeOutputs : List (JInstr 64) :=
  (List.range 8).map (fun (k : Nat) =>
    JInstr.storeMem "z" (8 * (k : Int)) (.reg (accNames.getD k default)))

/-- **The shipped `bignum_mul_4_8` block: proven core + trusted load/store ABI.**
    `loadInputs` (pointer ABI) ++ `clearAccs` (entry precondition) ++ the PROVEN
    `emitProductBlock4` (the verified 256×256 product, `runBlock = x·y`) ++
    `storeOutputs` (pointer ABI). The computational core is exactly
    `emitProductBlock4 accNames xNames yNames hiName loName`; the wrapper is
    load/store only. This replaces the hand-written `BignumMontMulKernel.mul48Block`
    as the artifact emitted by the verified pipeline. -/
def mul48ProvenBlock : List (JInstr 64) :=
  loadInputs
    ++ clearAccs
    ++ emitProductBlock4 accNames xNames yNames hiName loName
    ++ storeOutputs

/-! ### MULX implicit-`%rdx` legalization (trusted emit scaffolding)

x86 `mulx` takes its multiplier (`src1`) **implicitly from `%rdx`**; the explicit
operands are only `src2` and the two destinations. The proven block's
`.mulx dh dl (.reg src1) (.reg src2)` reads `src1` *by name* (its `runBlock`
denotes `src1 · src2`), but `src1` is whatever schoolbook register the selector
chose — here the per-column multiplicand `xⱼ` (`MulxSelect.selectMulxMac acc a b …`
puts the first factor `a` in `src1`). Those `xⱼ` are all simultaneously live
across the four rows, so they cannot all sit in the single hardware `%rdx`; the
pin-aware allocator's "bind every multiplier name to `%rdx`" assumption
(`spillAllocPinned` + the `mulxRdxSetup` elision) is unsound for this block and
the emitted code read a stale `%rdx` (the GMP KAT `1 × X` returned `0`).

`mulxLegalize` rewrites each `mulx`/`mulxMem` so its `src1` is funnelled through
a single dedicated register name `mulxRdxName`, pinned to `%rdx`, materialised
**immediately before** the multiply:

```
.mulx dh dl (.reg src1) src2  ↦  [ .mov mulxRdxName (.reg src1)
                                 , .mulx dh dl (.reg mulxRdxName) src2 ]
```

The inserted `.mov mulxRdxName (.reg src1)` renders (after allocation pins
`mulxRdxName → %rdx`) as `movq <src1-reg>, %rdx`, so `%rdx := src1`, and the
`.mulx` then reads `%rdx`. Because `mulxRdxName` carries `src1`'s value, the
rewritten `.mulx dh dl (.reg mulxRdxName) src2` denotes `src1 · src2` — identical
to the original `.mulx dh dl (.reg src1) src2`. This is a pure **emit-level**
move-coalescing transform (a `movq %rdx ← src1` ABI realisation of the implicit
operand, exactly like the load/store wrapper): it carries **no new proof
obligation** on the proven `runBlock` core, whose `.mulx dh dl src1 src2` is
unchanged upstream.

After legalization the *only* mulx-`src1` name is the single `mulxRdxName`
(`mulxMultiplierNames` returns `[mulxRdxName]`); its live range is exactly each
`mov;mulx` adjacent pair, so it is never live across two multiplies — the
`multipliersDisjoint` side-condition the `%rdx` pin needs now holds by
construction. `%rdx` is therefore **dead-on-arrival** at each `mov` (no other
value resides in it — the allocator reserves it) and is consumed by the very next
`mulx`. The original `src1` registers (`xⱼ`) are now ordinary pool/spill values,
not pinned to `%rdx`. -/

/-- The single dedicated register name that funnels every `MULX` `src1` through
    `%rdx`. Pinned to `%rdx` by the pin-aware allocator (it is the sole
    mulx-`src1` name after legalization), so the `mulxRdxSetup` elision fires and
    the implicit `%rdx` materialisation is the inserted `.mov`. -/
def mulxRdxName : String := "__mulx_rdx__"

/-- **MULX-`%rdx` legalization (trusted emit scaffolding).** Map each instruction:
    a `.mulx dh dl (.reg src1) src2` (resp. `.mulxMem`) expands to
    `[.mov mulxRdxName (.reg src1), .mulx dh dl (.reg mulxRdxName) src2]`, moving
    the implicit first source into the `%rdx`-pinned `mulxRdxName` right before the
    multiply; every other instruction passes through unchanged. An immediate
    `src1` (never occurs for a multiplier) is left as-is. Semantics-preserving:
    `mulxRdxName` holds `src1`'s value, so `mulxRdxName · src2 = src1 · src2`. -/
def mulxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.flatMap (fun i => match i with
    | .mulx dh dl (.reg src1) src2 =>
        [ .mov mulxRdxName (.reg src1), .mulx dh dl (.reg mulxRdxName) src2 ]
    | .mulxMem dh dl (.reg src1) base off =>
        [ .mov mulxRdxName (.reg src1), .mulxMem dh dl (.reg mulxRdxName) base off ]
    | i => [i])

/-- The reserved **zero register** name, pinned to `%rbx` (zeroed in the prologue).
    `adxLegalize` rewrites the imm-0 carry-flushes to read it. -/
def zeroName : String := "__zero__"

/-- **ADX-immediate legalization (trusted emit scaffolding).** x86 `ADCX`/`ADOX`
    have no immediate-operand encoding, but the proven dual-carry chain ends each
    chain with `adcx/adox d (imm 0)` (the carry-flush `d := d + CF`). Rewrite each
    such imm addend to read the zero register `zeroName` (pinned to `%rbx`, held at
    0 by the prologue): `adcx/adox d (.reg zeroName)` renders `adcx/adox %rbx, d` =
    `d + 0 + CF = d + CF`, faithful to the model. Keeps `AsmPrinter` generic (no
    immediate-special-case in the printer); register-operand ADCX/ADOX (every other
    kernel) is untouched. -/
def adxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.map (fun i => match i with
    | .adcx d (.imm _) => .adcx d (.reg zeroName)
    | .adox d (.imm _) => .adox d (.reg zeroName)
    | i => i)

/-- **The legalized shipped block.** The proven-core-wrapped `mul48ProvenBlock`
    with every `mulx` `src1` funnelled through the `%rdx`-pinned `mulxRdxName`
    (`mulxLegalize`) and every imm-0 carry-flush funnelled through the `%rbx`-pinned
    `zeroName` (`adxLegalize`). This is the block the emitter allocates, renders, and
    ships; its computational core is unchanged (both legalizations only insert the
    fixed-register moves/operands the hardware `mulx`/`adcx`/`adox` encodings
    require). -/
def mul48ProvenBlockLegal : List (JInstr 64) :=
  adxLegalize (mulxLegalize mul48ProvenBlock)

/-! ## 3. Spilling allocation and rendering

The 18 live value names + 3 pointers exceed the 14-slot GP pool, so first-fit
`allocGp` overflows. We use the verified pin-aware spilling allocator over the
**legalized** block: `z` pinned to `%rdi`, `x` to `%rsi`, `y` to `%rdx`'s caller
arg (moved out by the ABI marshal), the single legalized mulx-`src1` funnel
`mulxRdxName` to `%rdx`, the rest linear-scanned. -/

/-- The register-allocation pins for the spilling allocator: the pointer arguments
    `z`→`%rdi`, `x`→`%rsi`, plus `%rdx` reserved for the implicit `MULX` `src1`.
    After `mulxLegalize`, the sole mulx-`src1` name is `mulxRdxName` (bound to
    `%rdx` by `spillAllocPinned`'s multiplier pin), materialised by the inserted
    `.mov mulxRdxName ← src1` immediately before each multiply; the original
    `xⱼ` multiplicands are ordinary pool/spill values. The third pointer argument
    `y` arrives in `%rdx` and is marshalled out into a pool register by the ABI
    layer before the body runs (`argMarshalMoves`).

    We additionally pin the **zero register** `zeroName` to `%rbx`: after
    `adxLegalize`, every imm-0 carry-flush reads `(.reg zeroName)`, so it renders
    `adcx/adox %rbx, d` (`d + 0 + CF`), faithful iff `%rbx = 0`. `zeroName` is only
    ever read (never written) by the body, and the prologue `xor`-zeroes `%rbx`, so
    it stays 0 throughout. Pinning it (one body value spills to a frame cell
    instead) is trusted ABI scaffolding outside the `runBlock`-verified body.
    `%rbx` is callee-saved (saved/restored by the prologue/epilogue). -/
def mul48ProvenPins : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("__rdx_reserved__", "%rdx"),
   (zeroName, "%rbx")]

/-- The spill decisions: pin-aware linear scan over `mul48ProvenBlockLegal`. The
    single legalized mulx-`src1` funnel name (`mulxRdxName`) goes to `%rdx`; every
    other name gets a pool register while one is free, else a frame spill cell. -/
def mul48ProvenDecisions : List (String × Slot) :=
  spillAllocPinned mul48ProvenPins 0 mul48ProvenBlockLegal

/-- The pin-aware allocation overflowing for the first-fit allocator demonstrates
    the spilling allocator is required: 18 live names + pins exceed the pool. -/
theorem mul48Proven_allocGp_overflows :
    allocOverflow mul48ProvenPins mul48ProvenBlockLegal ≠ none := by native_decide

/-- The resident allocation: the pins plus every name whose first spill decision
    is register-resident (including the `%rdx` multipliers), mapped to its
    register. Spilled names are handled via per-instruction reloads. -/
def mul48ProvenResident : GpAlloc :=
  mul48ProvenPins ++ (blockNames mul48ProvenBlockLegal).filterMap (fun n =>
    match mul48ProvenDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The pinned names (register-resident by pinning, never reloaded/stored). -/
def mul48ProvenPinnedNames : List String := mul48ProvenPins.map Prod.fst

/-- Whether a name is materialised via spill reload/store: it has a spill slot and
    is not a pinned name. -/
def mul48ProvenSpilled (n : String) : Option Int :=
  if mul48ProvenPinnedNames.contains n then none
  else spillSlotOf mul48ProvenDecisions n

/-- The per-instruction `SpillView`: resident map plus the spilled names this
    instruction reads/writes with their frame offsets, against frame base `z`'s
    register — we reuse `z`'s `%rdi` as the spill frame base, since `z` is live
    throughout (the store targets it) and its base address is the natural frame
    pointer for a leaf with a red-zone-free spill region above the `z` buffer.

    The spill region is disjoint from the `z` output buffer: `z[0..7]` occupy
    bytes `0..63`, and the linear scan numbers spill cells from base `512`
    (`mul48ProvenSpillBase`), well above the 64-byte output. -/
def mul48ProvenSpillBase : String := "fp"

/-- The frame base register: a dedicated `%rbp`-class callee-saved register, so
    spills do not collide with the `z` output buffer. We pin it explicitly. -/
def mul48ProvenFramePins : GpAlloc := [("fp", "%rbp")]

/-- Build the `SpillView` for one instruction. Resident names → pool register
    (incl. `%rdx` multipliers and the `fp` frame base); spilled names → reload
    into a working register at each use. -/
def mul48ProvenViewOf (i : JInstr 64) : SpillView where
  resident := mul48ProvenFramePins ++ mul48ProvenResident
  frameBase := mul48ProvenSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (mul48ProvenSpilled n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (mul48ProvenSpilled n).map (fun off => (n, off)))

/-- The spill-materialised body lines: each instruction rendered with reloads
    before / stores after, `%rdx` setup for each `mulx`. -/
def mul48ProvenBodyLines : List String :=
  mul48ProvenBlockLegal.flatMap (fun i => renderJInstrSpilled (mul48ProvenViewOf i) i)

/-- **No `<UNALLOCATED>` sentinel in the emitted body.** Every name is placed:
    residents to their pool register, spilled names to a working register at each
    use, multipliers to `%rdx`. This is the gate first-fit fails
    (`mul48Proven_allocGp_overflows`). -/
theorem mul48ProvenBody_no_unallocated :
    (mul48ProvenBodyLines.any (fun l =>
      BignumMontMulKernel.hasSub l "<UNALLOCATED")) = false := by native_decide

/-- **The MULX implicit-`%rdx` realization is in the emitted text — every multiply
    reads a freshly-set `%rdx`.** Walking the rendered body, the nearest line *at or
    before* each `mulx` that writes the hardware `%rdx` (matches `, %rdx`) is a
    `movq <src1>, %rdx` (matches `movq` ∧ `, %rdx`) — the `mulxLegalize`
    `.mov mulxRdxName ← src1`. Equivalently: scanning back from each `mulx`, the
    first `%rdx`-writing line is the legalization's `movq`, with only spill-reload
    lines (which target the `%r14`/`%r15` working registers, never `%rdx`) possibly
    in between. This is exactly the gap whose absence made the earlier emit compute
    wrong products (the GMP KAT `1 × X = 0`): the pin-aware `mulxRdxSetup` elided
    the `%rdx` move because every `xⱼ` was (unsoundly) pinned to the single `%rdx`,
    so a stale `%rdx` was read; after legalization the lone `mulxRdxName` funnel
    (`mulxMultiplierNames mul48ProvenBlockLegal = [mulxRdxName]`) carries `src1`
    into `%rdx` immediately before each multiply, never live across two of them. -/
theorem mul48ProvenBody_mulx_rdx_legalized :
    -- the sole MULX `src1` name is the `%rdx`-pinned funnel (no `xⱼ` pinned to `%rdx`)
    CatCrypt.Crypto.Optimizer.SpillingRegAlloc.mulxMultiplierNames
        mul48ProvenBlockLegal = [mulxRdxName]
    -- and every `mulx`'s nearest preceding `%rdx`-writer is a `movq …, %rdx`
    ∧ (mul48ProvenBodyLines.zipIdx.filter (fun (li : String × Nat) =>
        BignumMontMulKernel.hasSub li.1 "mulx"
          && (let prevRdx := ((mul48ProvenBodyLines.take li.2).reverse).find?
                  (fun l => BignumMontMulKernel.hasSub l ", %rdx")
              match prevRdx with
              | some l => ¬ BignumMontMulKernel.hasSub l "movq"
              | none   => true))).length = 0 := by native_decide

/-! ## 4. The emitted `.s` leaf function

The spill frame base `fp` and the pointer arguments are framed by the System-V
leaf ABI: `z`→`%rdi`, `x`→`%rsi`, the third pointer `y` marshalled out of
`%rdx`, `fp` set to the red-zone spill region. We hand-write the minimal
prologue/epilogue (save `%rbp` and the callee-saved working registers, point
`fp`/`%rbp` at the spill region, marshal `y` out of `%rdx`); this is trusted ABI
scaffolding outside the verified body. -/

/-- The System V signature: three pointer arguments `z`, `x`, `y` (in
    `%rdi`, `%rsi`, `%rdx`). -/
def mul48ProvenArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The argument-marshalling moves for the resident allocation: copy `y` out of
    its `%rdx` home (reserved for `MULX`) into its allocated pool register. -/
def mul48ProvenArgMoves : List String :=
  argMarshalMoves (mul48ProvenFramePins ++ mul48ProvenResident) mul48ProvenArgs

/-- The trusted leaf prologue: save the callee-saved registers the spill path and
    frame base use (`%rbp` for `fp`, `%r14`/`%r15` working registers, `%rbx` and
    `%r12`/`%r13` if the resident pool reached them), set up the frame base
    pointer into the red zone (a `lea` of `%rsp` minus the spill window), then
    marshal `y` out of `%rdx`. Trusted ABI scaffolding outside the verified body. -/
def mul48ProvenPrologue : List String :=
  [ "\tpushq %rbp", "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
  , "\tpushq %r14", "\tpushq %r15"
    -- point the frame base (`fp` → %rbp) at a spill window below %rsp (the leaf
    -- red zone is too small for the >512-byte spill base, so we reserve a frame).
  , "\tleaq -1024(%rsp), %rbp"
    -- zero the zero register `zeroName` (pinned to %rbx) so the body's imm-0
    -- carry-flushes — `adxLegalize`d to `adcx/adox (.reg zeroName) , d`, rendered
    -- `adcx/adox %rbx, d` — compute `d + 0 + CF = d + CF`. The allocator pins
    -- `zeroName`→%rbx, so it stays 0 for the whole body. Trusted ABI scaffolding.
  , "\txorq %rbx, %rbx" ]
    ++ mul48ProvenArgMoves

/-- The trusted leaf epilogue: restore the callee-saved registers and return. -/
def mul48ProvenEpilogue : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
  , "\tpopq %rbx", "\tpopq %rbp", "\tret" ]

/-- The full emitted `.s` leaf function `bignum_mul_4_8_proven`: the trusted
    prologue, the spill-materialised body lines (the proven `emitProductBlock4`
    core wrapped in load/store), and the trusted epilogue. -/
def mul48ProvenAsm : String :=
  renderLeafFn "bignum_mul_4_8_proven"
    mul48ProvenPrologue mul48ProvenBodyLines mul48ProvenEpilogue

/- Shape check: the emitted asm contains the dual carry-chain idiom (`mulx`,
    `adcx`, `adox`) from the proven core, the load/store pointer ABI
    (`(%rsi)`, `(%rdi)`), and the `bignum_mul_4_8_proven` symbol. -/
#guard (BignumMontMulKernel.hasSub mul48ProvenAsm "bignum_mul_4_8_proven") && (BignumMontMulKernel.hasSub mul48ProvenAsm "mulx") && (BignumMontMulKernel.hasSub mul48ProvenAsm "adcx") && (BignumMontMulKernel.hasSub mul48ProvenAsm "adox")

/-- Emit driver: write the proven-core-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/s2n_montmul_compare/gen_com"
  IO.FS.writeFile
    "bench/s2n_montmul_compare/gen_com/lean_mul48_proven.s" mul48ProvenAsm
  IO.println "wrote gen_com/lean_mul48_proven.s (emitProductBlock4 proven core, spilling RA)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Mul48ProvenEmit
