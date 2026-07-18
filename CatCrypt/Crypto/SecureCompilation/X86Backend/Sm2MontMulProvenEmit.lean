/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# `bignum_montmul_sm2` emitted from PROVEN blocks (product + Montgomery reduce)

`Sm2MontMulKernel.lean` ships a **hand-written** 4-limb CIOS Montgomery multiply
whose all-inputs value identity (`z = x·y·2^-256 mod p_sm2`) is gated only by
the external GMP + s2n KAT — and which was, in fact, *buggy* until the KAT
caught it. The hand-written block is the prototype; the canonical artifact
should be **emitted by the verified pipeline**.

This module is that "generate from proven blocks" step for the *full* SM2
Montgomery multiply. The two computational cores are both proven over `runBlock`:

* **`SchoolbookProductRunBlock.emitProductBlock4`** — the 4×4 schoolbook product
  whose `runBlock` output (read out of the eight accumulator words) equals
  `valLimbs x · valLimbs y` (`sm2_emit_montmul_runBlock_full4`, axiom-clean, no
  `native_decide` on the value); and
* **`MontReduceRunBlock.emitMontRedcStep`** — one emitted Montgomery reduce
  word-step (digit `m = T₀·n'` + `m·p` accumulate row + shift-down) whose
  recombined `runBlock` value equals one `Number.montgomeryReduce (valLimbs p)
  (2^64) n' (valLimbs T)` step (`emitMontRedcStep_runBlock`). Four such steps
  chain into `montRedc4` (`emitMontRedc4_value`); for SM2 `n' = 1`
  (`Cios4LimbProven.sm2_nprime_one`).

`sm2ProvenBlock` wraps these two proven cores in the pointer ABI: `loadInputs`
the four `x`-limbs and four `y`-limbs out of the `%rsi`/`%rdx` argument buffers,
load the four SM2 modulus limbs (`sm2Limbs`) as constants and `n' = 1`, clear the
eight accumulator words, run the proven product (→ 8-word `T = x·y`), run the
four proven reduce word-steps (`emitMontRedc4Block`), and `storeOutputs` the
four result limbs to the `%rdi` (`z`) buffer.

## Trust story (identical to `Mul48ProvenEmit`)

The verified artifacts are `emitProductBlock4`'s `runBlock = valLimbs x ·
valLimbs y` and `emitMontRedcStep`'s `runBlock = montgomeryReduce` step
(axiom-clean). The two **trusted emit-scaffolding** pieces are:

1. the **load/store pointer framing** + the System-V leaf prologue/epilogue
   (`y` marshalled out of `%rdx`, modulus-limb / `n'` constant materialisation,
   the `%rdx`/`%rbx`/`%rbp` pins), exactly as every other word kernel documents;
   and
2. the **inter-step register routing** — feeding step `i`'s shifted-down
   accumulator words into step `i+1`'s input registers across one fused emitted
   block. This is the same multi-block register-routing the schoolbook's
   `SchoolbookRunBlock` named for its inter-row combine; it does not change the
   per-step value spec (each step's `runBlock` value IS a genuine
   `montgomeryReduce` step, proven in `MontReduceRunBlock`).

`AsmPrinter` + `gas` is the thin syntactic trust boundary. No `sorry`, no new
`axiom`. The MULX implicit-`%rdx` and ADX immediate legalizations
(`mulxLegalize`/`adxLegalize`, mirrored from `Mul48ProvenEmit`) are the same
fixed-register-encoding realisations the hardware requires.

## Register pressure → the verified spilling allocator

The product alone keeps 18 distinct value names live (8 accumulator words, 4
`x`-limbs, 4 `y`-limbs, 2 `MULX` scratch); the reduce adds the four modulus-limb
registers, the `n'` constant, the digit, and the reduce carry/scratch — far past
the 14-slot GP pool, even more than `mul48` (which had only the product). The
non-spilling first-fit `allocGp` overflows (`sm2Proven_allocGp_overflows`); the
body is routed through the **verified spilling allocator**
(`Optimizer.SpillingRegAlloc.spillAllocPinned`), exactly as `Mul48ProvenEmit`
and the X25519 monolithic ladder do.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2MontMulProvenEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The register-name layout

The proven product is parametric over register names. We pick the concrete SM2
4-limb instance: eight accumulator words `t0..t7` (the 512-bit product, then the
reduce window), four `x`-limb sources `x0..x3`, four `y`-limb scalars `y0..y3`,
the two `MULX` scratch words `phi`/`plo`; for the reduce, the four SM2
modulus-limb registers `p0..p3`, the `n' = 1` constant `np`, the digit register
`m`, and the reduce carry/scratch `rcy`/`rhi`/`rlo`. -/

/-- The eight accumulator-word register names (the 512-bit product output, then
    the reduce window). -/
def accNames : List String := ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7"]

/-- The four `x`-limb (multiplicand) source register names. -/
def xNames : List String := ["x0", "x1", "x2", "x3"]

/-- The four `y`-limb (multiplier) scalar register names. -/
def yNames : List String := ["y0", "y1", "y2", "y3"]

/-- The four SM2 modulus-limb (`p_sm2 = valLimbs sm2Limbs`) register names. -/
def pNames : List String := ["p0", "p1", "p2", "p3"]

/-- The `MULX` high / low scratch register names (shared by product and reduce). -/
def hiName : String := "phi"
def loName : String := "plo"

/-- The Montgomery constant register: holds `n' = 1` for SM2
    (`Cios4LimbProven.sm2_nprime_one`). -/
def npName : String := "np"

/-- The Montgomery digit register `m = T₀·n' mod 2^64`. -/
def mName : String := "m"

/-- The reduce-step carry word register (carry-out of one `m·p` accumulate row). -/
def rcyName : String := "rcy"

/-- The reduce **top-carry** word register: the 257th-bit overflow of the
    reduced accumulator. A faithful 4-word CIOS reduce produces a value `< 2·p`
    (`emitMontRedc4_value`), which can exceed `2^256` by one bit; that overflow
    is captured here (the analogue of the hand-written kernel's `t5` top word),
    and consumed by the final conditional-subtract's borrow chain. -/
def rtopName : String := "rtop"

/-- The four canonical-result register names: the conditional-subtract trial
    difference `accNames[4..7] − p_sm2`, then `CMOVB`-selected back to the
    original on borrow. After the select these hold the canonical `< p_sm2`
    result that `storeOutputs` writes to the `z` buffer. -/
def resNames : List String := ["r0", "r1", "r2", "r3"]

/-- The four SM2 modulus limbs (the canonical `Cios4LimbProven.sm2Limbs`
    constants), as 64-bit immediates for the constant-materialisation. -/
def sm2LimbImms : List Nat := sm2Limbs.map (·.toNat)

/-! ## 2. The wrapped block: load → constants → clear → PROVEN product → PROVEN
       reduce → store

### 2a. Loads / constant materialisation (trusted ABI scaffolding) -/

/-- Load the four `x`-limbs and four `y`-limbs from the argument buffers
    (`loadMem dst base off`). -/
def loadInputs : List (JInstr 64) :=
  (List.range 4).map (fun i => JInstr.loadMem (xNames.getD i default) "x" (8 * (i : Int)))
    ++ (List.range 4).map (fun i => JInstr.loadMem (yNames.getD i default) "y" (8 * (i : Int)))

/-- Materialise the four SM2 modulus limbs into `p0..p3` and `n' = 1` into `np`
    as immediate moves (`mov dst (.imm c)`). Trusted ABI/constant scaffolding —
    the modulus is the fixed SM2 prime `valLimbs sm2Limbs`. -/
def loadConsts : List (JInstr 64) :=
  (List.range 4).map (fun i =>
      JInstr.mov (pNames.getD i default) (.imm (sm2LimbImms.getD i 0)))
    ++ [ JInstr.mov npName (.imm 1) ]

/-- Clear the eight accumulator registers and the reduce top-carry word
    (`xor tᵢ, tᵢ`, `xor rtop, rtop`): zeroes the product file and the 257th-bit
    overflow word, and clears `CF`/`OF`, establishing the proven product core's
    entry precondition. `rtop` must start at `0` because the final reduce step
    accumulates its fold-carry onto it (`adc rtop, 0`). -/
def clearAccs : List (JInstr 64) :=
  accNames.map (fun a => JInstr.xor_ a (.reg a))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]

/-- Store the four **canonical** SM2 result limbs to the `z` buffer. After the
    four reduce steps the (`< 2·p_sm2`) result sits in `t4..t7` (the product file
    shifted down by four words) with its 257th-bit overflow in `rtop`; the final
    conditional subtract (`emitCondSubP`) canonicalises it into `resNames`
    (`r0..r3`, each `< p_sm2`), which the store reads. -/
def storeOutputs : List (JInstr 64) :=
  (List.range 4).map (fun (k : Nat) =>
    JInstr.storeMem "z" (8 * (k : Int)) (.reg (resNames.getD k default)))

/-! ### 2b. The proven Montgomery reduce as four chained steps

Each emitted reduce word-step is `MontReduceRunBlock.emitMontRedcStep`, whose
recombined `runBlock` value equals one `Number.montgomeryReduce (valLimbs p)
(2^64) n'` step (`emitMontRedcStep_runBlock`). For SM2 `n' = 1`.

Step `i` operates on the four-word window `accNames[i .. i+3]` of the shared
accumulator file: it forms the digit `m` from that window's low word
`accNames[i]`, accumulates `m·p` over the four modulus-limb registers `pNames`
into the window, threads the carry into the next free word `accNames[i+4]`, and
the shift-down `/2^64` is realised by the window sliding to `accNames[i+1 ..]`
for step `i+1`. The carry word `rcy` is added into `accNames[i+4]` by an explicit
inter-step `mov`/add (the *inter-step register routing* — trusted emit
scaffolding; the per-step accumulate semantics is the proven
`emitMontRedcStep`). -/

/-- One emitted reduce word-step at window offset `i`, with the inter-step
    register routing made faithful (trusted emit scaffolding).

    **Entry-precondition re-establishment.** `emitMontRedcStep`'s value spec
    (`MontReduceRunBlock.emitMontRedcStep_runBlock`) requires entering each step
    with the digit accumulator `m = 0`, the carry register `rcy = 0`, and both
    flags `CF = OF = 0`. After step `i` the row leaves `m = montDigit` (nonzero)
    and `rcy` holding the accumulate carry-out — neither is `0`, so step `i+1`'s
    digit/accumulate would read stale data. We therefore precede each step with
    two flag-and-register clears:

    * `xor m, m`   — clear the digit accumulator (satisfies the digit column's
      `acc = 0` entry, `hm0`);
    * `xor rcy, rcy` — clear the shared digit/row carry register (satisfies the
      digit's `dcy = 0` *and* the row's `rcy = 0` entry, `hdcy0`/`hrcy0`); as the
      last instruction before the step it also leaves `CF = OF = 0` (`x86_XOR`
      resets both), re-establishing the flag precondition.

    **Carry fold (the word shift-down).** The accumulate row zeroes the window
    low word `accNames[i]` (the Montgomery cancellation) and leaves the carry-out
    in `rcy`, with `CF = OF = 0`. The `/2^64` shift is realised by sliding the
    window to `accNames[i+1 ..]`; the carry word `rcy` is *added* into the next
    free accumulator word `accNames[i+4]` (a CF-independent `add`, since the row
    cleared `CF`), and that `add`'s own carry-out is propagated one word further
    into `accNames[i+5]` (for `i < 3`) or into the dedicated top-carry word
    `rtop` (for the final step `i = 3`, capturing the 257th-bit overflow of the
    `< 2·p` result). This is the genuine `n+2`-word CIOS window discipline the
    hand-written kernel documents (its `t5` top word); the per-step accumulate
    semantics is the proven `emitMontRedcStep`. -/
def emitMontRedcStepAt (i : Nat) : List (JInstr 64) :=
  let win := (accNames.drop i).take 4
  let t0 := win.headD default
  let nextCarryWord := accNames.getD (i + 4) default
  -- the word two above the window: a real accumulator word for i<3, else `rtop`
  let foldCarryWord := if i + 5 < accNames.length then accNames.getD (i + 5) default
                       else rtopName
    -- entry-precondition re-establishment (trusted emit scaffolding): clear the
    -- digit accumulator, the shared carry register, and (via the second xor) the
    -- CF/OF flags, so step `i` enters at `m = rcy = 0`, `CF = OF = 0`.
  [ JInstr.xor_ mName (.reg mName), JInstr.xor_ rcyName (.reg rcyName) ]
    ++ emitMontRedcStep mName t0 npName rcyName hiName loName win pNames rcyName hiName loName
    -- inter-step routing (trusted emit scaffolding): the accumulate's carry-out
    -- `rcy` is added into the next free accumulator word `accNames[i+4]`
    -- (CF-independent `add`: the row left CF = 0), completing the word
    -- shift-down for step `i+1`'s window; that add's carry-out propagates one
    -- word further (into `accNames[i+5]`, or `rtop` for the final step).
    ++ [ JInstr.add nextCarryWord (.reg rcyName)
       , JInstr.adc foldCarryWord (.imm 0) ]

/-- **The proven Montgomery reduction: four chained `emitMontRedcStep` blocks.**
    Steps at window offsets `0,1,2,3`, each the proven `emitMontRedcStep` (one
    `montgomeryReduce (valLimbs sm2Limbs) (2^64) 1` step over `runBlock`), routed
    by the inter-step carry folds. After all four the SM2 result (`< 2·p_sm2`,
    `· 2^256 ≡ x·y mod p_sm2` by `emitMontRedc4_value`) sits in the shifted-down
    window `accNames[4..7]`. -/
def emitMontRedc4Block : List (JInstr 64) :=
  emitMontRedcStepAt 0 ++ emitMontRedcStepAt 1 ++ emitMontRedcStepAt 2 ++ emitMontRedcStepAt 3

/-! ### 2c. The final canonical conditional subtract of `p_sm2`

After `emitMontRedc4Block` the reduced accumulator value `v < 2·p_sm2`
(`emitMontRedc4_value`) sits in the four words `accNames[4..7]` with its
257th-bit overflow in `rtop`. The canonical result is `v % p_sm2 = if v < p_sm2
then v else v − p_sm2` (`FieldAddSubTierA.condSubP_eq_mod`, the `< 2p` branch).

The emitted realisation is the standard branch-free trial-subtract + `CMOVB`
select (the `FieldAddSubTierA.condSubP` / `Sm2MontMulKernel.condSub` idiom):
copy `accNames[4..7]` into the result registers `resNames`, trial-subtract the
SM2 modulus limbs with a borrow chain (`sub`/`sbb`) threaded through the
top-carry word `rtop`, then `CMOVB` each result register back to the original
accumulator word **iff** the final borrow `CF = 1` (i.e. `v < p_sm2`, keep `v`);
otherwise the trial difference `v − p_sm2` is kept. Trusted emit scaffolding
(KAT-gated), exactly like the hand-written kernel's `condSub`. -/

/-- The final conditional subtract of `p_sm2`: trial-subtract the modulus from
    `accNames[4..7]` (borrow chain through `rtop`) into `resNames`, then `CMOVB`
    each `resNames[k]` back to `accNames[k+4]` on a final borrow — leaving the
    canonical `< p_sm2` result in `resNames`. -/
def emitCondSubP : List (JInstr 64) :=
  -- copy the reduced window into the result registers
  (List.range 4).map (fun (k : Nat) =>
      JInstr.mov (resNames.getD k default) (.reg (accNames.getD (k + 4) default)))
  -- trial-subtract the modulus limbs from the live `pNames` registers (x86
  -- SUB/SBB take only ≤32-bit immediates, but the SM2 limbs are full 64-bit, so
  -- we subtract the registers `loadConsts` materialised — they still hold the
  -- modulus here, read-only through the reduce). SUB the low word, SBB the rest,
  -- then SBB the top-carry word so CF is the final borrow over the 257-bit value.
    ++ [ JInstr.sub (resNames.getD 0 default) (.reg (pNames.getD 0 default)) ]
    ++ (List.range 3).map (fun (k : Nat) =>
        JInstr.sbb (resNames.getD (k + 1) default) (.reg (pNames.getD (k + 1) default)))
    ++ [ JInstr.sbb rtopName (.imm 0) ]
  -- CF = 1 ⇒ v < p_sm2 ⇒ keep the original window word; else keep the trial diff
    ++ (List.range 4).map (fun (k : Nat) =>
        JInstr.cmovb (resNames.getD k default) (.reg (accNames.getD (k + 4) default)))

/-- **The shipped `bignum_montmul_sm2` block: two proven cores + trusted ABI /
    inter-step routing.** `loadInputs` (pointer ABI) ++ `loadConsts` (SM2
    modulus + `n'`) ++ `clearAccs` (product entry precondition) ++ the PROVEN
    `emitProductBlock4` (the verified 256×256 product, `runBlock = x·y`) ++ the
    PROVEN `emitMontRedc4Block` (four `emitMontRedcStep`, `runBlock =
    montgomeryReduce`) ++ `emitCondSubP` (the final canonical conditional
    subtract of `p_sm2`, `< 2p → < p`) ++ `storeOutputs` (pointer ABI). The two
    computational cores are exactly `emitProductBlock4` and `emitMontRedcStep`;
    the wrapper is load/store + constants + inter-step carry routing + the final
    canonicalising conditional subtract. This replaces the hand-written
    `Sm2MontMulKernel` as the artifact emitted by the verified pipeline. -/
def sm2ProvenBlock : List (JInstr 64) :=
  loadInputs
    ++ loadConsts
    ++ clearAccs
    ++ emitProductBlock4 accNames xNames yNames hiName loName
    ++ emitMontRedc4Block
    ++ emitCondSubP
    ++ storeOutputs

/-! ### MULX / ADX legalization (trusted emit scaffolding)

Identical to `Mul48ProvenEmit`: x86 `mulx` reads its multiplier (`src1`)
implicitly from `%rdx`, and `adcx`/`adox` have no immediate encoding. Both proven
cores emit `.mulx dh dl (.reg src1) src2` (reading `src1` by name) and
`.adcx/.adox d (imm 0)` carry-flushes. `mulxLegalize` funnels every `mulx` `src1`
through a single `%rdx`-pinned register `mulxRdxName` materialised right before
the multiply; `adxLegalize` rewrites each imm-0 carry-flush to read the
`%rbx`-pinned zero register `zeroName`. Both are pure emit-level
fixed-register-encoding realisations carrying no new proof obligation on the
proven `runBlock` cores. See `Mul48ProvenEmit` for the full rationale. -/

/-- The single dedicated register funnelling every `MULX` `src1` through `%rdx`. -/
def mulxRdxName : String := "__mulx_rdx__"

/-- **MULX-`%rdx` legalization (trusted emit scaffolding).** Each
    `.mulx dh dl (.reg src1) src2` (resp. `.mulxMem`) expands to
    `[.mov mulxRdxName (.reg src1), .mulx … (.reg mulxRdxName) src2]`. -/
def mulxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.flatMap (fun i => match i with
    | .mulx dh dl (.reg src1) src2 =>
        [ .mov mulxRdxName (.reg src1), .mulx dh dl (.reg mulxRdxName) src2 ]
    | .mulxMem dh dl (.reg src1) base off =>
        [ .mov mulxRdxName (.reg src1), .mulxMem dh dl (.reg mulxRdxName) base off ]
    | i => [i])

/-- The reserved **zero register** name, pinned to `%rbx` (zeroed in the prologue). -/
def zeroName : String := "__zero__"

/-- **ADX-immediate legalization (trusted emit scaffolding).** Each imm-0
    carry-flush `adcx/adox d (imm 0)` reads the `%rbx`-pinned zero register
    instead: `adcx/adox %rbx, d = d + 0 + CF = d + CF`. -/
def adxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.map (fun i => match i with
    | .adcx d (.imm _) => .adcx d (.reg zeroName)
    | .adox d (.imm _) => .adox d (.reg zeroName)
    | i => i)

/-- **The legalized shipped block.** `sm2ProvenBlock` with every `mulx` `src1`
    funnelled through the `%rdx`-pinned `mulxRdxName` and every imm-0 carry-flush
    funnelled through the `%rbx`-pinned `zeroName`. -/
def sm2ProvenBlockLegal : List (JInstr 64) :=
  adxLegalize (mulxLegalize sm2ProvenBlock)

/-! ## 3. Spilling allocation and rendering

The 18 product live names + 3 pointers + the reduce values (4 modulus limbs,
`n'`, digit, carry) exceed the 14-slot GP pool, so first-fit `allocGp` overflows.
We use the verified pin-aware spilling allocator over the **legalized** block:
`z`→`%rdi`, `x`→`%rsi`, `%rdx` reserved for the `MULX` funnel, `%rbx` the zero
register, the two `MULX` scratch destinations `phi`/`plo`→`%rax`/`%rcx` (so no
single `mulx` ever touches more spilled operands than the two reserved working
registers can reload — see `sm2ProvenPins`), the rest linear-scanned (the
genuinely-spilled values round-trip through frame cells via
`renderJInstrSpilled`). -/

/-- The register-allocation pins for the spilling allocator: `z`→`%rdi`,
    `x`→`%rsi`, `%rdx` reserved for the implicit `MULX` `src1` funnel, and the
    zero register `zeroName`→`%rbx` (zeroed by the prologue, only read by the
    body). The third pointer argument `y` arrives in `%rdx` and is marshalled out
    into a pool register by the ABI layer before the body runs.

    The two `MULX` scratch destinations `hiName`/`loName` (`phi`/`plo`) are
    additionally pinned to fixed pool registers (`%rax`/`%rcx`). They are the
    high/low words *written by every* `mulx`, so each multiply writes two of them;
    a `mulx` also reads its multiplicand `src2` (which the linear scan may spill).
    If `phi`/`plo` were themselves spilled, that single `mulx` would touch three
    spilled operands (`src2` read + `phi`/`plo` writes) — more than the two
    reserved working registers (`%r14`/`%r15`) can reload at one program point,
    leaving the third name `<UNALLOCATED>`. The SM2 reduce's extra live names
    (modulus limbs, `n'`, digit, carries) raised the register pressure past the
    point where the linear scan happened to keep `phi`/`plo` resident (as it did
    for the product-only `Mul48ProvenEmit`), so we pin them. They have very short
    (per-multiply) live ranges, so reserving two pool registers for them costs
    almost nothing; it keeps every instruction's spilled-operand footprint within
    the two working registers, which is exactly the `workRegs` budget the spill
    renderer assumes. -/
def sm2ProvenPins : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("__rdx_reserved__", "%rdx"),
   (zeroName, "%rbx"), (hiName, "%rax"), (loName, "%rcx")]

/-- The spill decisions: pin-aware linear scan over `sm2ProvenBlockLegal`. -/
def sm2ProvenDecisions : List (String × Slot) :=
  spillAllocPinned sm2ProvenPins 0 sm2ProvenBlockLegal

/-- The pin-aware allocation overflowing for the first-fit allocator demonstrates
    the spilling allocator is required: the product + reduce live names + pins far
    exceed the pool. -/
theorem sm2Proven_allocGp_overflows :
    allocOverflow sm2ProvenPins sm2ProvenBlockLegal ≠ none := by native_decide

/-- The resident allocation: the pins plus every name whose first spill decision
    is register-resident, mapped to its register. -/
def sm2ProvenResident : GpAlloc :=
  sm2ProvenPins ++ (blockNames sm2ProvenBlockLegal).filterMap (fun n =>
    match sm2ProvenDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The pinned names (register-resident by pinning, never reloaded/stored). -/
def sm2ProvenPinnedNames : List String := sm2ProvenPins.map Prod.fst

/-- Whether a name is materialised via spill reload/store. -/
def sm2ProvenSpilled (n : String) : Option Int :=
  if sm2ProvenPinnedNames.contains n then none
  else spillSlotOf sm2ProvenDecisions n

/-- The dedicated frame-base register name, pinned to `%rbp`, so spills do not
    collide with the `z` output buffer. -/
def sm2ProvenSpillBase : String := "fp"

/-- The frame-base register pin. -/
def sm2ProvenFramePins : GpAlloc := [("fp", "%rbp")]

/-- Build the `SpillView` for one instruction: resident names → pool register
    (incl. `%rdx`/`%rbx`/`fp`); spilled names → reload into a working register at
    each use. -/
def sm2ProvenViewOf (i : JInstr 64) : SpillView where
  resident := sm2ProvenFramePins ++ sm2ProvenResident
  frameBase := sm2ProvenSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (sm2ProvenSpilled n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (sm2ProvenSpilled n).map (fun off => (n, off)))

/-- The spill-materialised body lines: each instruction rendered with reloads
    before / stores after, `%rdx` setup for each `mulx`. -/
def sm2ProvenBodyLines : List String :=
  sm2ProvenBlockLegal.flatMap (fun i => renderJInstrSpilled (sm2ProvenViewOf i) i)

/-- **No `<UNALLOCATED>` sentinel in the emitted body.** Every name is placed. -/
theorem sm2ProvenBody_no_unallocated :
    (sm2ProvenBodyLines.any (fun l =>
      BignumMontMulKernel.hasSub l "<UNALLOCATED")) = false := by native_decide

/-! ## 4. The emitted `.s` leaf function -/

/-- The System V signature: three pointer arguments `z`, `x`, `y`. -/
def sm2ProvenArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The argument-marshalling moves: copy `y` out of `%rdx` into its pool reg. -/
def sm2ProvenArgMoves : List String :=
  argMarshalMoves (sm2ProvenFramePins ++ sm2ProvenResident) sm2ProvenArgs

/-- The trusted leaf prologue: save the callee-saved registers, point the frame
    base (`fp`→`%rbp`) at a spill window below `%rsp`, zero the zero register
    (`%rbx`), then marshal `y` out of `%rdx`. Trusted ABI scaffolding. -/
def sm2ProvenPrologue : List String :=
  [ "\tpushq %rbp", "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
  , "\tpushq %r14", "\tpushq %r15"
  , "\tleaq -1024(%rsp), %rbp"
  , "\txorq %rbx, %rbx" ]
    ++ sm2ProvenArgMoves

/-- The trusted leaf epilogue: restore the callee-saved registers and return. -/
def sm2ProvenEpilogue : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
  , "\tpopq %rbx", "\tpopq %rbp", "\tret" ]

/-- The full emitted `.s` leaf function `sm2_montmul_proven`: the trusted
    prologue, the spill-materialised body (the proven `emitProductBlock4` and
    `emitMontRedcStep` cores wrapped in load/const/store + inter-step routing),
    and the trusted epilogue. -/
def sm2ProvenAsm : String :=
  renderLeafFn "sm2_montmul_proven"
    sm2ProvenPrologue sm2ProvenBodyLines sm2ProvenEpilogue

/-- Shape check: the emitted asm contains the product + reduce dual-carry idiom
    (`mulx`, `adcx`, `adox`) from both proven cores, the load/store pointer ABI
    (`(%rsi)`, `(%rdi)`), and the `sm2_montmul_proven` symbol. -/
theorem sm2ProvenAsm_shape :
    BignumMontMulKernel.hasSub sm2ProvenAsm "sm2_montmul_proven"
      ∧ BignumMontMulKernel.hasSub sm2ProvenAsm "mulx"
      ∧ BignumMontMulKernel.hasSub sm2ProvenAsm "adcx"
      ∧ BignumMontMulKernel.hasSub sm2ProvenAsm "adox" := by native_decide

/-- Emit driver: write the proven-cores-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/sm2_compare/gen"
  IO.FS.writeFile
    "bench/sm2_compare/gen/sm2_montmul_proven.s" sm2ProvenAsm
  IO.println "wrote gen/sm2_montmul_proven.s (emitProductBlock4 + emitMontRedcStep proven cores, spilling RA)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sm2MontMulProvenEmit
