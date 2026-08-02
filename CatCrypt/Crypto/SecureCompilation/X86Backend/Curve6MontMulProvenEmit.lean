/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# 6-limb curve Montgomery multiply emitted from PROVEN blocks (P384, BLS12-381)

This module generalizes the 4-limb `Curve4MontMulProvenEmit` template to **6
limbs at radix `R = 2^384`** for the two 6-limb curves **P384 / secp384r1** and
the **BLS12-381 base field**. The full Montgomery multiply is assembled from the
same two proven `runBlock` cores —
`SchoolbookProductRunBlock.emitProductBlock` (here via the 6-limb alias
`Curve6LimbTierA.emitProductBlock6`, the 384×384→768 product,
`runBlock = x·y`) and `MontReduceRunBlock.emitMontRedcStep` (one Montgomery
reduce word-step, general `n'`) — chained six times over a 12-word accumulator,
then canonicalised by a multi-round conditional subtract over six modulus limbs.

## Generalisation 4 → 6

* inputs: 6 `x`-limbs and 6 `y`-limbs (vs 4);
* accumulator file: 12 words (the 6×6 product is 768-bit, vs 8 words at 4 limbs);
* reduce: 6 word-steps (window offsets `0..5`), `nextCarryWord = accNames[i+6]`;
* conditional subtract: 6 modulus words, restore-copy from `accNames[6..11]`;
* radix: `R = 2^384`.

The proven cores are radix- and arity-parametric, so no new multiply or reduction
proof is needed (the Tier-A value specs at `R = 2^384` live in
`Curve6LimbTierA`); only the modulus immediates and the per-word `n'` are
curve-specific.

## The `n' ≠ 1` separate-carry fix (carried from the template)

Both 6-limb curves have `n' ≠ 1` (P384 `n' = 0x100000001`, BLS12-381
`n' = 0x89f3fffcfffcfffd`), so the Montgomery digit `m = T₀·n' mod 2^64` has a
nonzero high word. As in the 4-limb template, the digit column threads its
(discarded) carry through a **separate** `dcy` register, distinct from the
accumulate-row carry `rcy`, and each step re-establishes `m = dcy = rcy = 0`,
`CF = OF = 0` via three `xor` clears (the last resetting both flags).

## Trust story (identical to the 4-limb template)

The verified artifacts are `emitProductBlock`'s
`runBlock = valLimbs x · valLimbs y` and `emitMontRedcStep`'s
`runBlock = montgomeryReduce` step (both axiom-clean, general-`N`). The trusted
emit scaffolding is: (1) the load/store pointer ABI + leaf prologue/epilogue +
modulus/`n'` materialisation; (2) the inter-step carry routing (the word
shift-down folds); and (3) the final canonicalising conditional subtract. The
`AsmPrinter` + `gas` + the external GMP KAT (`x·y·R⁻¹ mod p`, `R = 2^384`) are
the syntactic/value trust boundary, exactly as at 4 limbs. No `sorry`, no new
`axiom`. The MULX/ADX legalizations and the verified spilling allocator are
reused unchanged.

The per-word `n'` is pinned to the curve prime by `<curve>NPrime_pin`
(`(p₀ · n') % 2^64 = 2^64 − 1`, one `mod`); the moduli are the
`native_decide`-pinned `p384Limbs` / `bls12381Limbs` from `Curve6LimbTierA`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6MontMulProvenEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.MontReduceRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The register-name layout (shared across both 6-limb curves)

Identical structure to the 4-limb template, scaled to 12 accumulator words, 6
`x`/`y`/modulus/result limbs, plus the dedicated digit-carry register `dcy`
(the `n' ≠ 1` fix). -/

/-- The twelve accumulator-word register names (the 768-bit product, then the
    reduce window). -/
def accNames : List String :=
  ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9", "t10", "t11"]

/-- The six `x`-limb (multiplicand) source register names. -/
def xNames : List String := ["x0", "x1", "x2", "x3", "x4", "x5"]

/-- The six `y`-limb (multiplier) scalar register names. -/
def yNames : List String := ["y0", "y1", "y2", "y3", "y4", "y5"]

/-- The six curve modulus-limb register names. -/
def pNames : List String := ["p0", "p1", "p2", "p3", "p4", "p5"]

/-- The `MULX` high / low scratch register names (shared by product and reduce). -/
def hiName : String := "phi"
def loName : String := "plo"

/-- The Montgomery constant register: holds the curve's per-word `n'`. -/
def npName : String := "np"

/-- The Montgomery digit register `m = T₀·n' mod 2^64`. -/
def mName : String := "m"

/-- The reduce-step **row**-carry word register (carry-out of one `m·p`
    accumulate row). -/
def rcyName : String := "rcy"

/-- The reduce-step **digit**-carry word register (carry-out of the digit column
    `m = T₀·n' mod 2^64`). For `n' ≠ 1` this high word is nonzero, so it must be a
    register *distinct* from the row carry `rcy` — the `n' ≠ 1` fix. -/
def dcyName : String := "dcy"

/-- The reduce top-carry word register: the 385th-bit overflow of the reduced
    accumulator, consumed by the final conditional-subtract's borrow chain. -/
def rtopName : String := "rtop"

/-- The six canonical-result register names (the conditional-subtract trial
    difference, `CMOVB`-selected). -/
def resNames : List String := ["r0", "r1", "r2", "r3", "r4", "r5"]

/-! ## 2. The parametric wrapped block

`montMul6ProvenBlock limbImms nprime` is the 6-limb analogue of the 4-limb
`montMulProvenBlock`: a 12-word accumulator, 6 reduce steps, a 6-word
multi-round conditional subtract, `R = 2^384`, with **separate** digit/row
carry scratch (`n' ≠ 1`-safe). -/

/-- Load the six `x`-limbs and six `y`-limbs from the argument buffers. -/
def loadInputs : List (JInstr 64) :=
  (List.range 6).map (fun i => JInstr.loadMem (xNames.getD i default) "x" (8 * (i : Int)))
    ++ (List.range 6).map (fun i => JInstr.loadMem (yNames.getD i default) "y" (8 * (i : Int)))

/-- Materialise the six modulus limbs into `p0..p5` and `n' = nprime` into `np`
    as immediate moves. Trusted ABI/constant scaffolding. -/
def loadConsts (limbImms : List Nat) (nprime : Nat) : List (JInstr 64) :=
  (List.range 6).map (fun i =>
      JInstr.mov (pNames.getD i default) (.imm (limbImms.getD i 0)))
    ++ [ JInstr.mov npName (.imm nprime) ]

/-- Clear the twelve accumulator registers and the reduce top-carry word. -/
def clearAccs : List (JInstr 64) :=
  accNames.map (fun a => JInstr.xor_ a (.reg a))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]

/-- Store the six canonical result limbs to the `z` buffer. -/
def storeOutputs : List (JInstr 64) :=
  (List.range 6).map (fun (k : Nat) =>
    JInstr.storeMem "z" (8 * (k : Int)) (.reg (resNames.getD k default)))

/-- One emitted reduce word-step at window offset `i` (6-limb window), with the
    inter-step register routing made faithful (trusted emit scaffolding) and the
    **`n' ≠ 1` separate-carry fix**.

    **Entry-precondition re-establishment.** Three clears precede each step so it
    enters at `m = dcy = rcy = 0`, `CF = OF = 0` (`emitMontRedcStep`'s
    `hm0`/`hdcy0`/`hrcy0`/`hcf`/`hof`): `xor m,m`; `xor dcy,dcy` (the digit
    column's nonzero high word, kept off the row carry); `xor rcy,rcy` (also
    resetting `CF = OF = 0` as the last instruction).

    **Carry fold (the word shift-down).** The accumulate row leaves its carry-out
    in `rcy` (`CF = OF = 0`); the 6-word window slides to `accNames[i+1..]`, and
    `rcy` is *added* into `accNames[i+6]` (a CF-independent `add`), its carry-out
    propagated through every higher accumulator word and finally into `rtop` — no
    carry is ever dropped, so `rtop` is the 385th bit of the running
    value. (At 6 limbs `nextCarryWord = accNames[i+6]` and the fold chain spans
    `accNames[i+7 .. 11]` then `rtop`.) -/
def emitMontRedcStepAt (i : Nat) : List (JInstr 64) :=
  let win := (accNames.drop i).take 6
  let t0 := win.headD default
  let nextCarryWord := accNames.getD (i + 6) default
  let foldChain : List (JInstr 64) :=
    ((List.range (accNames.length - (i + 7))).map (fun j =>
        JInstr.adc (accNames.getD (i + 7 + j) default) (.imm 0)))
      ++ [ JInstr.adc rtopName (.imm 0) ]
  [ JInstr.xor_ mName (.reg mName)
  , JInstr.xor_ dcyName (.reg dcyName)
  , JInstr.xor_ rcyName (.reg rcyName) ]
    ++ emitMontRedcStep mName t0 npName dcyName hiName loName win pNames rcyName hiName loName
    ++ [ JInstr.add nextCarryWord (.reg rcyName) ]
    ++ foldChain

/-- The six chained `emitMontRedcStep` blocks (window offsets `0..5`). -/
def emitMontRedc6Block : List (JInstr 64) :=
  emitMontRedcStepAt 0 ++ emitMontRedcStepAt 1 ++ emitMontRedcStepAt 2
    ++ emitMontRedcStepAt 3 ++ emitMontRedcStepAt 4 ++ emitMontRedcStepAt 5

/-- One branch-free conditional-subtract round on the 6-word value in `resNames`
    (7th word `rtop`): trial `res − p` (borrow chain through `rtop`), then `CMOVB`
    each `res[k]` back to the saved copy `acc[k+6]` on a final borrow (`res < p`).
    Leaves `res = (res ≥ p) ? res − p : res`. -/
def condSubRound : List (JInstr 64) :=
  [ JInstr.sub (resNames.getD 0 default) (.reg (pNames.getD 0 default)) ]
    ++ (List.range 5).map (fun (k : Nat) =>
        JInstr.sbb (resNames.getD (k + 1) default) (.reg (pNames.getD (k + 1) default)))
    ++ [ JInstr.sbb rtopName (.imm 0) ]
    ++ (List.range 6).map (fun (k : Nat) =>
        JInstr.cmovb (resNames.getD k default) (.reg (accNames.getD (k + 6) default)))

/-- Number of conditional-subtract rounds (generous, KAT-gated). The chained
    per-step reduce leaves a value correct mod `p` but a loose representative;
    each round removes one `p` once `≥ p` and is a no-op once `< p`. -/
def condSubRounds : Nat := 8

/-- One full canonicalisation round followed by the save/clear bookkeeping that
    sets up the next round's restore-copy (`acc[6..11] ← res`, `rtop ← 0`). -/
def condSubRoundFull : List (JInstr 64) :=
  condSubRound
    ++ (List.range 6).map (fun (k : Nat) =>
        JInstr.mov (accNames.getD (k + 6) default) (.reg (resNames.getD k default)))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]

def emitCondSubP : List (JInstr 64) :=
  -- res ← window
  (List.range 6).map (fun (k : Nat) =>
      JInstr.mov (resNames.getD k default) (.reg (accNames.getD (k + 6) default)))
  -- `condSubRounds` canonicalisation rounds
    ++ (List.range condSubRounds).flatMap (fun _ => condSubRoundFull)

/-- **The parametric shipped 6-limb block: two proven cores + trusted ABI /
    inter-step routing.** `loadInputs` ++ `loadConsts` ++ `clearAccs` ++ the
    PROVEN `emitProductBlock6` ++ the PROVEN `emitMontRedc6Block` (separate
    digit/row carry, `n' ≠ 1`-safe) ++ `emitCondSubP` ++ `storeOutputs`. The
    6-limb, `R = 2^384` analogue of `Curve4MontMulProvenEmit.montMulProvenBlock`. -/
def montMul6ProvenBlock (limbImms : List Nat) (nprime : Nat) : List (JInstr 64) :=
  loadInputs
    ++ loadConsts limbImms nprime
    ++ clearAccs
    ++ emitProductBlock6 accNames xNames yNames hiName loName
    ++ emitMontRedc6Block
    ++ emitCondSubP
    ++ storeOutputs

/-! ## 3. MULX / ADX legalization (trusted emit scaffolding, identical to 4-limb) -/

/-- The single dedicated register funnelling every `MULX` `src1` through `%rdx`. -/
def mulxRdxName : String := "__mulx_rdx__"

/-- **MULX-`%rdx` legalization (trusted emit scaffolding).** -/
def mulxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.flatMap (fun i => match i with
    | .mulx dh dl (.reg src1) src2 =>
        [ .mov mulxRdxName (.reg src1), .mulx dh dl (.reg mulxRdxName) src2 ]
    | .mulxMem dh dl (.reg src1) base off =>
        [ .mov mulxRdxName (.reg src1), .mulxMem dh dl (.reg mulxRdxName) base off ]
    | i => [i])

/-- The reserved zero register name, pinned to `%rbx`. -/
def zeroName : String := "__zero__"

/-- **ADX-immediate legalization (trusted emit scaffolding).** -/
def adxLegalize : List (JInstr 64) → List (JInstr 64) :=
  List.map (fun i => match i with
    | .adcx d (.imm _) => .adcx d (.reg zeroName)
    | .adox d (.imm _) => .adox d (.reg zeroName)
    | i => i)

/-- The legalized parametric 6-limb block. -/
def montMul6ProvenBlockLegal (limbImms : List Nat) (nprime : Nat) : List (JInstr 64) :=
  adxLegalize (mulxLegalize (montMul6ProvenBlock limbImms nprime))

/-! ## 4. Spilling allocation and rendering (parametric, identical pins to 4-limb)

At 6 limbs the register pressure is much higher (12 accumulator words + 6
modulus + 6 `x` + the carries/scratch ≫ 14 GP registers), so essentially every
non-pinned name is spilled — the verified spilling allocator handles this
unchanged. The `phi`/`plo` pin (the two `MULX` scratch destinations at
`%rax`/`%rcx`) is the key trick: a 2-destination `MULX` touching `> 2` spilled
operands would overflow the two work-registers, so its scratch destinations are
pinned. -/

/-- The register-allocation pins for the spilling allocator: `z`→`%rdi`,
    `x`→`%rsi`, `%rdx` reserved for the implicit `MULX` `src1` funnel, the zero
    register `zeroName`→`%rbx`, and the two `MULX` scratch destinations
    `hiName`/`loName`→`%rax`/`%rcx`. Identical pins to the 4-limb template. -/
def provenPins : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("__rdx_reserved__", "%rdx"),
   (zeroName, "%rbx"), (hiName, "%rax"), (loName, "%rcx")]

/-- The spill decisions: pin-aware linear scan over the legalized block. -/
def provenDecisions (limbImms : List Nat) (nprime : Nat) : List (String × Slot) :=
  spillAllocPinned provenPins 0 (montMul6ProvenBlockLegal limbImms nprime)

/-- The resident allocation: the pins plus every register-resident name. -/
def provenResident (limbImms : List Nat) (nprime : Nat) : GpAlloc :=
  provenPins ++ (blockNames (montMul6ProvenBlockLegal limbImms nprime)).filterMap (fun n =>
    match (provenDecisions limbImms nprime).lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The pinned names (register-resident by pinning). -/
def provenPinnedNames : List String := provenPins.map Prod.fst

/-- Whether a name is materialised via spill reload/store. -/
def provenSpilled (limbImms : List Nat) (nprime : Nat) (n : String) : Option Int :=
  if provenPinnedNames.contains n then none
  else spillSlotOf (provenDecisions limbImms nprime) n

/-- The dedicated frame-base register name, pinned to `%rbp`. -/
def provenSpillBase : String := "fp"

/-- The frame-base register pin. -/
def provenFramePins : GpAlloc := [("fp", "%rbp")]

/-- Build the `SpillView` for one instruction. -/
def provenViewOf (limbImms : List Nat) (nprime : Nat) (i : JInstr 64) : SpillView where
  resident := provenFramePins ++ provenResident limbImms nprime
  frameBase := provenSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (provenSpilled limbImms nprime n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (provenSpilled limbImms nprime n).map (fun off => (n, off)))

/-- The spill-materialised body lines. -/
def provenBodyLines (limbImms : List Nat) (nprime : Nat) : List String :=
  (montMul6ProvenBlockLegal limbImms nprime).flatMap (fun i =>
    renderJInstrSpilled (provenViewOf limbImms nprime i) i)

/-! ## 5. The emitted `.s` leaf function (parametric) -/

/-- The System V signature: three pointer arguments `z`, `x`, `y`. -/
def provenArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The argument-marshalling moves: copy `y` out of `%rdx` into its pool reg. -/
def provenArgMoves (limbImms : List Nat) (nprime : Nat) : List String :=
  argMarshalMoves (provenFramePins ++ provenResident limbImms nprime) provenArgs

/-- The trusted leaf prologue. A larger spill frame (`-2048`) than the 4-limb
    template, since the 12-word accumulator + 6 modulus + 6 `x`/`y` are mostly
    spilled. -/
def provenPrologue (limbImms : List Nat) (nprime : Nat) : List String :=
  [ "\tpushq %rbp", "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
  , "\tpushq %r14", "\tpushq %r15"
  , "\tleaq -2048(%rsp), %rbp"
  , "\txorq %rbx, %rbx" ]
    ++ provenArgMoves limbImms nprime

/-- The trusted leaf epilogue. -/
def provenEpilogue : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
  , "\tpopq %rbx", "\tpopq %rbp", "\tret" ]

/-- The full emitted `.s` leaf function for a 6-limb curve, parametric over the
    symbol, modulus immediates, and `n'`. -/
def provenAsm (sym : String) (limbImms : List Nat) (nprime : Nat) : String :=
  renderLeafFn sym
    (provenPrologue limbImms nprime) (provenBodyLines limbImms nprime) provenEpilogue

/-! ## 6. Per-curve instantiations

For each 6-limb curve {P384, BLS12-381}: the modulus immediates (from the
`<curve>Limbs` vendored in `Curve6LimbTierA`), the per-word `n'` with its light
pin (`(p₀ · n') % 2^64 = 2^64 − 1`, one `mod` — no heavy asm-scanning checks),
the proven block, the asm, and the emit driver. -/

/-! ### 6a. P384 / secp384r1 (`n' = 0x100000001`, low limb `0x00000000ffffffff`) -/

def p384LimbImms : List Nat := p384Limbs.map (·.toNat)
def p384NPrime : Nat := 0x100000001

/-- P384's per-word Montgomery constant pin: `(p₀ · n') % 2^64 = 2^64 − 1` on the
    low limb `p384Limbs[0] = 0x00000000ffffffff`. -/
theorem p384NPrime_pin :
    ((p384Limbs.headD 0).toNat * p384NPrime) % 2 ^ 64 = 2 ^ 64 - 1 := by
  native_decide

def p384ProvenBlock : List (JInstr 64) :=
  montMul6ProvenBlock p384LimbImms p384NPrime
def p384ProvenAsm : String :=
  provenAsm "p384_montmul_proven" p384LimbImms p384NPrime

def emitMainP384 : IO Unit := do
  IO.FS.createDirAll "bench/p384_compare/gen"
  IO.FS.writeFile
    "bench/p384_compare/gen/p384_montmul_proven.s" p384ProvenAsm
  IO.println "wrote bench/p384_compare/gen/p384_montmul_proven.s"

/-! ### 6b. BLS12-381 base field (`n' = 0x89f3fffcfffcfffd`, low limb
`0xb9feffffffffaaab`) -/

def bls12381LimbImms : List Nat := bls12381Limbs.map (·.toNat)
def bls12381NPrime : Nat := 0x89f3fffcfffcfffd

/-- BLS12-381's per-word Montgomery constant pin: `(p₀ · n') % 2^64 = 2^64 − 1`
    on the low limb `bls12381Limbs[0] = 0xb9feffffffffaaab`. -/
theorem bls12381NPrime_pin :
    ((bls12381Limbs.headD 0).toNat * bls12381NPrime) % 2 ^ 64 = 2 ^ 64 - 1 := by
  native_decide

def bls12381ProvenBlock : List (JInstr 64) :=
  montMul6ProvenBlock bls12381LimbImms bls12381NPrime
def bls12381ProvenAsm : String :=
  provenAsm "bls12381_montmul_proven" bls12381LimbImms bls12381NPrime

def emitMainBls12381 : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_compare/gen"
  IO.FS.writeFile
    "bench/bls12381_compare/gen/bls12381_montmul_proven.s" bls12381ProvenAsm
  IO.println "wrote bench/bls12381_compare/gen/bls12381_montmul_proven.s"

/-! ## Artifact generation at elaboration

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMainP384
#eval emitMainBls12381

end CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6MontMulProvenEmit
