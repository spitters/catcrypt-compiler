/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519ReduceRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA
import CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# Curve25519 plain field multiply emitted from the PROVEN product + a Solinas reduce

`Fe25519MulProvenEmit.lean` emits the full Curve25519 **plain** field multiply
`z = (x · y) mod (2^255 − 19)` assembled from the proven 256×256→512 product core
`SchoolbookProductRunBlock.emitProductBlock4` (whose `runBlock` value is
`valLimbs x · valLimbs y`, axiom-clean) followed by the Solinas `·19` reduction
for `p25519 = 2^255 − 19`. This is the Solinas analogue of
`Curve4MontMulProvenEmit` / `Sm2MontMulProvenEmit`: the **same** load / product /
MULX-`%rdx` legalize / spilling-allocator / leaf-ABI scaffolding, with the
Montgomery word-reduce replaced by the Solinas split-and-fold below. It is a
PLAIN field multiply (no `R⁻¹` Montgomery factor).

## The Solinas reduce (2^255 − 19), emitted after the product

The product `P = x·y < 2^510` lands in the eight accumulator words
`accNames[0..7]`. Since `2^255 ≡ 19 (mod p)`:

1. **Split at bit 255** (NON-word-aligned). `hi = P >> 255` and
   `lo = P mod 2^255`. There is no `SHRD` constructor in the dialect, so the
   255-bit-non-word-aligned shift is realised with `shr`/`shl`/`or_`: word `k` of
   `hi` is `(acc[k+3] >> 63) | (acc[k+4] << 1)`. `lo` is the four low words with
   the top bit of `acc[3]` masked off (`and acc3, 0x7fff…ff`).
2. **Fold** `t = lo + 19·hi` — the `foldMul19` arithmetic shape (`19·hi` via a
   `MULX`-by-19 per high limb threaded with `adcx`, ripple-added into `lo`). The
   high words of `hi` are < 2^255, so `19·hi < 20·2^255 ≈ 2^260`: `t` is ≈5 words.
3. **Refold** `t` at bit 255 again: `t_hi = t >> 255` is `< 20`, so
   `result = t_lo + 19·t_hi` is a single `imul`-by-19 + add-with-carry chain.
   `result < 2^255 + 380 < 2^256`.
4. **Canonicalise** by the `condSubRound` idiom (modulus `p25519` materialised in
   `pNames` registers, trial subtract + `cmovb` restore); `result < 2p`, so the
   rounds land it in `[0, p)`. Store the four words to `z`.

## Trust story

The verified artifact is `emitProductBlock4`'s `runBlock = valLimbs x · valLimbs y`
(axiom-clean, from `SchoolbookProductRunBlock`). The Solinas reduce's `·19` fold
**arithmetic** is the value-proven `Fe25519ReduceRunBlock.foldMul19` /
`foldMul19_reconstruct` (`= valLimbs high · 19 + valLimbs low`); the canonical
residue identity is the value-proven `Fe25519TierA.reduce25519_eq_mod`. The
EMITTED reduce here is the *trusted emit scaffolding* that realises that proven
arithmetic over the register words: the bit-255 (non-word-aligned) split mask
sequence (`shr`/`shl`/`or_`/`and`), the inter-limb carry routing of the fold, and
the final canonicalising conditional subtract. That non-word-aligned split is the
named `Fe25519ReduceRunBlock.splitBookkeepingGap`, gated by the external GMP KAT
(`bench/x25519_fieldmul_compare`, the REV-12 discipline). `AsmPrinter` + `gas`
+ the GMP KAT are the syntactic / value trust boundary. No `sorry`, no new
`axiom`. The MULX-`%rdx` legalization and the verified spilling allocator are
reused unchanged from the Montgomery template.

The modulus limbs are `Fe25519TierA.p25519Limbs`, pinned by `native_decide`
to the prime `2^255 − 19 = solinasParams25519.modulus`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulProvenEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519TierA
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. Register-name layout (shared with the Montgomery template) -/

/-- The eight accumulator-word register names (the 512-bit product `P = x·y`). -/
def accNames : List String := ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7"]

/-- The four `x`-limb (multiplicand) source register names. -/
def xNames : List String := ["x0", "x1", "x2", "x3"]

/-- The four `y`-limb (multiplier) scalar register names. -/
def yNames : List String := ["y0", "y1", "y2", "y3"]

/-- The four `p25519` modulus-limb register names (for the conditional subtract). -/
def pNames : List String := ["p0", "p1", "p2", "p3"]

/-- The `MULX` high / low scratch register names (shared by product and fold). -/
def hiName : String := "phi"
def loName : String := "plo"

/-- The Solinas constant register (holds `19`). -/
def cName : String := "c19"

/-- The five `hi`-half word registers `hi = P >> 255` (words 0..4; word 4 catches
    the top `acc[7] << 1` bit). -/
def hiNames : List String := ["h0", "h1", "h2", "h3", "h4"]

/-- The five `19·hi` row word registers (`19·hi < 2^260`, ≈5 words). -/
def folNames : List String := ["f0", "f1", "f2", "f3", "f4"]

/-- The reduce top-carry word register (the few-bit overflow of `t = lo + 19·hi`
    and of the refold; consumed by the conditional subtract's borrow chain). -/
def rtopName : String := "rtop"

/-- A general scratch register. -/
def scrName : String := "scr"

/-- The four canonical-result register names (the conditional-subtract trial
    difference, `cmovb`-selected back to the saved copy on borrow). -/
def resNames : List String := ["r0", "r1", "r2", "r3"]

/-- The four saved-result register names (the pre-subtract copy `cmovb` restores
    from when `result < p`). -/
def savNames : List String := ["s0", "s1", "s2", "s3"]

/-! ## 2. Load / store / constant scaffolding (trusted ABI). -/

/-- Load the four `x`-limbs and four `y`-limbs from the argument buffers. -/
def loadInputs : List (JInstr 64) :=
  (List.range 4).map (fun i => JInstr.loadMem (xNames.getD i default) "x" (8 * (i : Int)))
    ++ (List.range 4).map (fun i => JInstr.loadMem (yNames.getD i default) "y" (8 * (i : Int)))

/-- Materialise the four `p25519` modulus limbs into `p0..p3` and the Solinas
    constant `19` into `c19` as immediate moves. Trusted ABI/constant scaffolding. -/
def loadConsts : List (JInstr 64) :=
  (List.range 4).map (fun i =>
      JInstr.mov (pNames.getD i default) (.imm ((p25519Limbs.getD i 0).toNat)))
    ++ [ JInstr.mov cName (.imm 19) ]

/-- Clear the eight accumulator registers and the reduce top-carry word. -/
def clearAccs : List (JInstr 64) :=
  accNames.map (fun a => JInstr.xor_ a (.reg a))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]

/-- Store the four canonical result limbs to the `z` buffer. -/
def storeOutputs : List (JInstr 64) :=
  (List.range 4).map (fun (k : Nat) =>
    JInstr.storeMem "z" (8 * (k : Int)) (.reg (resNames.getD k default)))

/-! ## 3. The Solinas reduce, emitted as `JInstr` after the product.

The product `P = x·y` is in `accNames[0..7]`. The reduce realises the value-proven
`Fe25519ReduceRunBlock.solinasReduce_grounded_fold` over the register words. -/

/-- **Step 1 — split at bit 255 (non-word-aligned).** `hi = P >> 255`, materialised
    word by word with `shr`/`shl`/`or_` (no `SHRD` in the dialect): for `k = 0..3`,
    `hi[k] = (acc[k+3] >> 63) | (acc[k+4] << 1)`, and `hi[4] = acc[7] >> 63`. Then
    `lo` is left in `accNames[0..3]` with the top bit of `acc[3]` masked off
    (`and acc3, 0x7fff…ff`). Trusted emit scaffolding (the bit-255 split mask). -/
def emitSplit255 : List (JInstr 64) :=
  -- hi[k] for k = 0..3: (acc[k+3] >> 63) | (acc[k+4] << 1)
  ((List.range 4).flatMap (fun k =>
    [ JInstr.mov (hiNames.getD k default) (.reg (accNames.getD (k + 3) default))
    , JInstr.shr (hiNames.getD k default) (.imm 63)
    , JInstr.mov scrName (.reg (accNames.getD (k + 4) default))
    , JInstr.shl scrName (.imm 1)
    , JInstr.or_ (hiNames.getD k default) (.reg scrName) ]))
  -- hi[4] = acc[7] >> 63
    ++ [ JInstr.mov (hiNames.getD 4 default) (.reg (accNames.getD 7 default))
       , JInstr.shr (hiNames.getD 4 default) (.imm 63) ]
  -- mask lo = acc[0..3] with the top bit of acc[3] cleared (acc[0..2] already < 2^64)
    ++ [ JInstr.mov scrName (.imm 0x7fffffffffffffff)
       , JInstr.and_ (accNames.getD 3 default) (.reg scrName) ]

/-- **Step 2 — the `·19` fold `t = lo + 19·hi`** (the `foldMul19` arithmetic shape).
    `19·hi` is a `MULX`-by-19 per high limb (`(folHi, folLo) = 19 · hi[k]`) threaded
    by `adcx` into the `folNames` row, then ripple-added into the low words
    `accNames[0..3]` (an `add`/`adc` chain), the running carry collected in
    `rtopName`. `19·hi < 2^260`, so `t = (accNames[0..3], rtop)` is ≈5 words.
    Trusted emit scaffolding for the proven `valLimbs (foldMul19 hi lo)
    = valLimbs hi · 19 + valLimbs lo`. -/
def emitFold19 : List (JInstr 64) :=
  -- 19·hi as the row folNames[0..4] (+ carry into rtop), via MULX-by-c19 + adcx
  -- row[k] gets the low word of 19·hi[k]; the high word adcx's into row[k+1].
  -- Build the row by clearing then accumulating each MULX.
  (folNames.map (fun f => JInstr.xor_ f (.reg f)))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]
  -- per-limb MULX-by-19 + carry into the next row word (adcx chain on CF)
    ++ (List.range 5).flatMap (fun k =>
        [ JInstr.mulx hiName loName (.reg cName) (.reg (hiNames.getD k default))
        , JInstr.add (folNames.getD k default) (.reg loName) ]
          ++ (if k < 4
              then [ JInstr.adc (folNames.getD (k + 1) default) (.reg hiName) ]
              else [ JInstr.adc rtopName (.reg hiName) ]))
  -- ripple-add the 19·hi row folNames[0..3] into the low words accNames[0..3],
  -- carrying through folNames[4] and rtop (folNames[4] holds the 5th word of 19·hi)
    ++ [ JInstr.add (accNames.getD 0 default) (.reg (folNames.getD 0 default)) ]
    ++ (List.range 3).map (fun k =>
        JInstr.adc (accNames.getD (k + 1) default) (.reg (folNames.getD (k + 1) default)))
    ++ [ JInstr.adc (folNames.getD 4 default) (.imm 0)
       , JInstr.adc rtopName (.imm 0) ]

/-- **Step 3 — refold `t` at bit 255.** After the fold the value
    `t = (accNames[0..3], folNames[4], rtop)` is `< 2^260`, so `t_hi = t >> 255`
    fits in `< 20`. Form `t_hi = (acc[3] >> 63) | (folNames[4] << 1)` (one word
    suffices since the 5th+ words are tiny), `result = t_lo + 19·t_hi` where
    `t_lo = acc[0..3]` with `acc[3]`'s top bit masked; `19·t_hi < 380` so it is a
    single `imul`-by-19 into the low word + a short carry chain. Trusted emit
    scaffolding. -/
def emitRefold : List (JInstr 64) :=
  -- t_hi (one word, < 20·2^5): (acc[3] >> 63) | (folNames[4] << 1) | (rtop << ...).
  -- rtop is at most a couple of bits; fold it in via shl by 1 too (folNames[4] is
  -- the word at 2^256, so >>255 brings its bit 0 to position 1; rtop sits above).
  [ JInstr.mov scrName (.reg (accNames.getD 3 default))
  , JInstr.shr scrName (.imm 63)                       -- bit 255 of t_lo half
  , JInstr.mov hiName (.reg (folNames.getD 4 default))
  , JInstr.shl hiName (.imm 1)                         -- folNames[4] · 2 (its weight 2^256 → 2^1 after >>255)
  , JInstr.or_ scrName (.reg hiName)
  -- bring rtop (weight ≥ 2^320) down: shift left by 65 is out of one word, but
  -- rtop is provably 0 for reduced inputs (t < 2^260); add it defensively as a
  -- high contribution folded through the cond-sub instead. Keep t_hi = scr.
  -- mask t_lo: clear the top bit of acc[3]
  , JInstr.mov hiName (.imm 0x7fffffffffffffff)
  , JInstr.and_ (accNames.getD 3 default) (.reg hiName)
  -- 19 · t_hi  (single word, < 380)
  , JInstr.imul scrName (.imm 19)
  -- result = t_lo + 19·t_hi : add into acc[0], carry up
  , JInstr.add (accNames.getD 0 default) (.reg scrName) ]
    ++ (List.range 3).map (fun k =>
        JInstr.adc (accNames.getD (k + 1) default) (.imm 0))
  -- top carry of the refold (≤ 1) into rtop for the cond-sub borrow chain
    ++ [ JInstr.xor_ rtopName (.reg rtopName)
       , JInstr.adc rtopName (.imm 0) ]

/-- One branch-free conditional-subtract round on the 4-word value in `resNames`
    (5th word `rtop`): trial `res − p25519` (borrow chain through `rtop`), then
    `cmovb` each `res[k]` back to the saved copy `sav[k]` on a final borrow
    (`res < p`). Leaves `res = (res ≥ p) ? res − p : res`. The `condSubRound`
    idiom from the Montgomery template, with the saved copy in `savNames`. -/
def condSubRound : List (JInstr 64) :=
  [ JInstr.sub (resNames.getD 0 default) (.reg (pNames.getD 0 default)) ]
    ++ (List.range 3).map (fun (k : Nat) =>
        JInstr.sbb (resNames.getD (k + 1) default) (.reg (pNames.getD (k + 1) default)))
    ++ [ JInstr.sbb rtopName (.imm 0) ]
    ++ (List.range 4).map (fun (k : Nat) =>
        JInstr.cmovb (resNames.getD k default) (.reg (savNames.getD k default)))

/-- Number of conditional-subtract rounds. The refold leaves `result < 2^255 + 380
    < 2p`, so a single round canonicalises; we run a couple defensively (each is a
    no-op once `< p`). KAT-gated. -/
def condSubRounds : Nat := 2

/-- One canonicalisation round with the save/clear bookkeeping that sets up the
    next round's restore-copy (`sav ← res`, `rtop ← 0`). -/
def condSubRoundFull : List (JInstr 64) :=
  condSubRound
    ++ (List.range 4).map (fun (k : Nat) =>
        JInstr.mov (savNames.getD k default) (.reg (resNames.getD k default)))
    ++ [ JInstr.xor_ rtopName (.reg rtopName) ]

/-- The conditional-subtract canonicalisation: load `res`/`sav` from the reduced
    low words `accNames[0..3]`, then run `condSubRounds` rounds. -/
def emitCondSubP : List (JInstr 64) :=
  (List.range 4).flatMap (fun (k : Nat) =>
      [ JInstr.mov (resNames.getD k default) (.reg (accNames.getD k default))
      , JInstr.mov (savNames.getD k default) (.reg (accNames.getD k default)) ])
    ++ (List.range condSubRounds).flatMap (fun _ => condSubRoundFull)

/-! ## 4. The shipped block: proven product + Solinas reduce + cond-sub. -/

/-- **The shipped block.** `loadInputs ++ loadConsts ++ clearAccs ++` the PROVEN
    `emitProductBlock4` (`runBlock = valLimbs x · valLimbs y`) `++` the Solinas
    reduce (`emitSplit255 ++ emitFold19 ++ emitRefold`, trusted emit scaffolding
    realising the value-proven `foldMul19`/`reduce25519_eq_mod`) `++ emitCondSubP
    ++ storeOutputs`. -/
def fe25519ProvenBlock : List (JInstr 64) :=
  loadInputs
    ++ loadConsts
    ++ clearAccs
    ++ emitProductBlock4 accNames xNames yNames hiName loName
    ++ emitSplit255
    ++ emitFold19
    ++ emitRefold
    ++ emitCondSubP
    ++ storeOutputs

/-! ## 5. MULX / ADX legalization (trusted emit scaffolding, identical to template). -/

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

/-- The legalized block. -/
def fe25519ProvenBlockLegal : List (JInstr 64) :=
  adxLegalize (mulxLegalize fe25519ProvenBlock)

/-! ## 6. Spilling allocation and rendering (identical pins to the template). -/

/-- The register-allocation pins for the spilling allocator: `z`→`%rdi`,
    `x`→`%rsi`, `%rdx` reserved for the implicit `MULX` `src1` funnel, the zero
    register `zeroName`→`%rbx`, and the two `MULX` scratch destinations
    `hiName`/`loName`→`%rax`/`%rcx`. -/
def provenPins : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("__rdx_reserved__", "%rdx"),
   (zeroName, "%rbx"), (hiName, "%rax"), (loName, "%rcx")]

/-- The spill decisions: pin-aware linear scan over the legalized block. -/
def provenDecisions : List (String × Slot) :=
  spillAllocPinned provenPins 0 fe25519ProvenBlockLegal

/-- The resident allocation: the pins plus every register-resident name. -/
def provenResident : GpAlloc :=
  provenPins ++ (blockNames fe25519ProvenBlockLegal).filterMap (fun n =>
    match provenDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The pinned names (register-resident by pinning). -/
def provenPinnedNames : List String := provenPins.map Prod.fst

/-- Whether a name is materialised via spill reload/store. -/
def provenSpilled (n : String) : Option Int :=
  if provenPinnedNames.contains n then none
  else spillSlotOf provenDecisions n

/-- The dedicated frame-base register name, pinned to `%rbp`. -/
def provenSpillBase : String := "fp"

/-- The frame-base register pin. -/
def provenFramePins : GpAlloc := [("fp", "%rbp")]

/-- Build the `SpillView` for one instruction. -/
def provenViewOf (i : JInstr 64) : SpillView where
  resident := provenFramePins ++ provenResident
  frameBase := provenSpillBase
  spilledReads := (readNames i).filterMap (fun n =>
    (provenSpilled n).map (fun off => (n, off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (provenSpilled n).map (fun off => (n, off)))

/-- The spill-materialised body lines. -/
def provenBodyLines : List String :=
  fe25519ProvenBlockLegal.flatMap (fun i =>
    renderJInstrSpilled (provenViewOf i) i)

/-! ## 7. The emitted `.s` leaf function. -/

/-- The System V signature: three pointer arguments `z`, `x`, `y`. -/
def provenArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The argument-marshalling moves: copy `y` out of `%rdx` into its pool reg. -/
def provenArgMoves : List String :=
  argMarshalMoves (provenFramePins ++ provenResident) provenArgs

/-- The trusted leaf prologue. -/
def provenPrologue : List String :=
  [ "\tpushq %rbp", "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"
  , "\tpushq %r14", "\tpushq %r15"
  , "\tleaq -1024(%rsp), %rbp"
  , "\txorq %rbx, %rbx" ]
    ++ provenArgMoves

/-- The trusted leaf epilogue. -/
def provenEpilogue : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
  , "\tpopq %rbx", "\tpopq %rbp", "\tret" ]

/-- The full emitted `.s` leaf function for the plain Curve25519 field multiply,
    symbol `fe25519_mul_proven`, ABI `void f(uint64_t *z, const uint64_t *x,
    const uint64_t *y)`. -/
def fe25519ProvenAsm : String :=
  renderLeafFn "fe25519_mul_proven" provenPrologue provenBodyLines provenEpilogue

/-- Emit `fe25519_mul_proven.s` into the x25519 field-multiply bench directory. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_fieldmul_compare/gen"
  IO.FS.writeFile
    "bench/x25519_fieldmul_compare/gen/fe25519_mul_proven.s" fe25519ProvenAsm
  IO.println "wrote bench/x25519_fieldmul_compare/gen/fe25519_mul_proven.s"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulProvenEmit
