/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect

/-!
# X25519 Montgomery ladder as a verified `JForProg` loop

The Montgomery ladder is a fixed **255-iteration** loop: for each scalar bit
(top to bottom) it conditionally swaps the working points (`cswap`, NOT a
branch), runs one differential add-and-double step, and swaps back. Its defining
*constant-time* property is exactly that the iteration count is fixed and the
only scalar-bit-dependent operation is `cswap`.

This file models that loop as a `JForProg` (the verified bounded-loop layer,
`JForProgCT.lean`): a static iteration count `n = 255` and an accumulator-update
`Com jasminDialect [accTy] accTy`. The accumulator **bundles the whole ladder
state** — the four working coordinates `x2,z2,x3,z3` (4×`u64[4]`), the scalar
(`u64[4]`, consumed bit-by-bit), and the base `x1` (`u64[4]`) — into one
`stackArr 64 24`. One iteration is the leaf `x25519_ladder_iter` (cswap + the
differential step + a scalar shift); keeping it a leaf matches the opaque-leaf
model used throughout (the field ops and `cswap` are trusted jasmin, e.g.
formosa/fiat). `JForProg.toProg` emits the loop skeleton
`fn x25519_ladder(acc){ for i=0 to 255 { acc = x25519_ladder_iter(acc) } }`.

What this **verifies**: the *orchestration* — that the ladder is a fixed-trip,
`cswap`-based loop that leaks nothing through control flow or addressed memory
(`ctSafeJForProg = true`), the constant-time guarantee the Montgomery ladder
exists to provide. The field-op-level body (inlining the verified single step,
`X25519Program.ladderStepX2`, over the bundle's sub-fields) needs a dialect
sub-array-slice op to pass slices to the field leaves — the one remaining
framework piece for a field-granular emitted ladder.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.X25519Ladder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-- The bundled ladder-state accumulator: `x2,z2,x3,z3` (4×`u64[4]`) ‖ scalar
    (`u64[4]`) ‖ base `x1` (`u64[4]`) = 24 × 64-bit words. -/
abbrev LadderState : JasminTy := .stackArr 64 24

/-- One ladder iteration as an opaque leaf over the bundled state: reads the
    scalar's current top bit, `cswap`s the working points, runs the differential
    add-and-double step, swaps back, and shifts the scalar. All scalar-bit
    dependence is inside the (constant-time) `cswap`. -/
def ladderIterBody : Com jasminDialect [LadderState] LadderState :=
  .var (.mk (.extCall "x25519_ladder_iter" [LadderState] LadderState) rfl
          (.cons .here .nil))
    (.ret .here)

/-- The X25519 ladder: 255 fixed iterations of `ladderIterBody`. -/
def x25519Ladder : JForProg LadderState :=
  { n := 255, update := ladderIterBody }

/-! ## Constant-time verification -/

/-- The ladder loop is **constant-time**: 255 fixed iterations whose body has no
    addressed-memory access keyed by a secret — the only data-dependent work is
    the `cswap` inside the trusted leaf. Holds even when the accumulator (which
    carries the secret scalar) is labelled `.Secret`: the orchestration leaks
    nothing through control flow or memory addressing. -/
theorem x25519Ladder_ctSafe_secret :
    ctSafeJForProg x25519Ladder SecretLevel.Secret = true := by native_decide

theorem x25519Ladder_ctSafe_public :
    ctSafeJForProg x25519Ladder SecretLevel.Public = true := by native_decide

/-- Stronger: the ladder is **robustly** CT-safe — CT under *every* attacker
    labelling of the accumulator (the loop adds no timing channel regardless of
    how the state is classified). -/
theorem x25519Ladder_robustlyCTSafe : RobustlyCTSafeJForProg x25519Ladder := by
  intro accL
  cases accL <;> native_decide

/-! ## Emission

`x25519Ladder_prog : JasminProg` is the source-level emission target: a single
`for i = 0 to 255 { acc = x25519_ladder_iter(acc) }` over the bundle. The bench
(`bench/x25519_ladder/`) renders it to `.jazz` and compiles with jasminc.

Taking the artifact off jasminc would require the whole `x25519_scalarmult`
(decode/clamp + the ladder loop + invert/encode) as an owned-RA `Lprog`/`Lcmd`
so the `X86Backend.LprogBytes.encodeLprog` byte encoder can emit the `.o`
directly. Two distinct lowerings produce it:

* **loop lowering (PRESENT)** — `LprogControlFlow.cforToLcmd` lowers a front
  `JForProg` bounded loop to the owned-RA looped `Lcmd`: it register-allocates the
  straight-line body once via `JasminLprogExport.comToLfundefPhys`, drops the
  function-return `Lret`, appends the counter decrement, and wraps it in
  `loopLcmd` (`Llabel top ; body ; SUB n,1 ; CMP ; Lcond NZ → top`). The X25519
  ladder `JForProg` lowers through it: the loop skeleton (label + back-edge) emits
  and byte-encodes byte-identically to gas (`bench/lprog_bytes_looped`).
* **field-leaf lowering (the `JInstr`-leaf → call-target bridge, now PRESENT)** —
  the field ops are the owned `Fe25519{Mul,Ops}Kernel`s, straight-line
  `List (JInstr 64)` kernels. `X86Backend.Fe25519LfundefBridge` bridges them to
  call targets two ways: (1) the verified `renderSysVLeafFn` path emits each as a
  `.globl` leaf `.s` symbol (`fe25519_{mul,sqr,add,sub,mul121666}_x86_from_lean`),
  the faithful ADX/MULX schoolbook; (2) `jinstrBlockToLfundef` lifts each block to
  an owned-RA `Lfundef`. A field-op call becomes a real `LinstrR.Lcall` rendering
  to `call <leaf>` (the new `LprogAsmPrinter` `Lcall` arm), resolved intra-object
  (`R_X86_64_PLT32`) by gas/`ld` — the text-path analogue of
  `LprogBytes.encodeLcmdReloc`'s intra-object resolution; the byte encoder
  (`encodeLcmdReloc`) emits the same `E8 00000000` + reloc. The end-to-end bridge
  KAT is `bench/x25519_ladder/fieldcall_kat.c` (owned dispatcher thunks `call` the
  verified leaves; each dispatched op == s2n-bignum over 50k vectors, no jasminc).

  **The remaining residual is now narrow and precise**: the field leaves' ADX
  schoolbook (`mulx`/`mulxMem`/`adcx`/`adox`, in `mul`/`sqr`/`mul121666`) has NO
  faithful `LinstrR`/byte-encoder image — the `LinstrR` MULX model renders a
  2-operand `imul` and `encodeLopn` has no MULX/ADCX/ADOX opcode — so those leaves
  are NOT byte-encodable by `encodeLprogReloc` to a `.o` directly; they reach the
  `.o` only via the verified-`.s`-then-gas route (the established kernel trust
  boundary). `Fe25519LfundefBridge.{feAdd,feSub}_lift_byteEncodable` /
  `{feMul,feSqr,feMul121666}_lift_has_adx` pin exactly this split. Closing the byte
  route fully needs ADX/MULX opcode bytes in `LprogBytes.encodeLopn`.

So (a) the `JForProg`/`Cfor` → `Lcmd` loop lowering is present (`cforToLcmd`);
(b) the fe25519 leaves are now owned-RA `Lfundef`s / verified `.s` symbols and the
ladder's field calls are real `Lcall`s resolved intra-object (bridge + KAT landed).

**The whole function is now off gas as ONE emitted `.o` (milestone closed).**
`X86Backend.Fe25519LfundefBridge.x25519ScalarmultLcmd` folds the entire RFC 7748
`x25519_scalarmult(out,k,u)` — the little-endian decode, the clamp (`k[0]&=248`,
`k[31]&=127|64`, byte-ops correctly lifted to the limb masks), the 255-iteration
constant-time `cswap` ladder loop (`LprogControlFlow.loopLcmd` back-edge; the body is
the branchless mask `cswap` + a scalar-bit walk + a `call x25519_mono_step`), the
`z^(p-2)` inversion addition chain (intra-object `call`s to the byte-encoded
`fe25519_{mul,sqr}` leaves + `loopLcmd` squaring runs), and the LE encode — into one
owned-RA `Lcmd`. It byte-encodes through `LprogBytes.encodeLprogReloc` together with
`x25519_mono_step` and the called field leaves into ONE multi-symbol `.o`
(`x25519ScalarmultFullObject`). NO C scaffolding, NO gas instruction selection, NO
jasminc on the artifact path: the `.o` IS the whole function. The RFC 7748 §5.2
vec1/vec2 + iterated(1)/(1000) + 5000-vector s2n KAT
(`bench/x25519_ladder/scalarmult_owned_kat.c`, which only marshals bytes↔limbs and
calls the entry point) is byte-exact; the differential vs `renderLprogAtt → gas` is
byte-identical except in the intra-object `call` rel32 fields the verified encoder
resolves directly (gas leaves a `0`-placeholder + `R_X86_64_PLT32` relocation). -/

/-- The emitted jasmin loop skeleton:
    `fn x25519_ladder(acc : u64[24]) { for i=0 to 255 { … acc = x25519_ladder_iter(acc) } ; return acc }`. -/
def x25519Ladder_prog := JForProg.toProg "x25519_ladder" x25519Ladder

/-- The emitted program denotes to the 255-fold iteration of the step (the loop
    layer's characterisation), so the model's meaning is exactly "apply one
    ladder iteration 255 times". -/
theorem x25519Ladder_n : x25519Ladder.n = 255 := rfl

/-! ## Emitted-loop denotation preservation (the keystone, ladder instance) -/

open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect in
/-- `ladderIterBody` is a single-leaf body (one `extCall` then `.ret .here`). -/
theorem ladderIterBody_singleVar :
    x25519Ladder.update
      = SingleVarBody (accTy := LadderState)
          (.mk (.extCall "x25519_ladder_iter" [LadderState] LadderState) rfl
            (.cons .here .nil)) := rfl

open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (LeafSem LeafAgrees)

/-- **Keystone — the emitted X25519 ladder loop denotes the 255-fold step.**
    Running the emitted `for i = 0 to 255 { acc = x25519_ladder_iter(acc) }` by
    iterating the word-level body evaluator 255 times from `init`, threading the
    bundled ladder-state accumulator, equals `x25519Ladder.denote init` — the
    255-fold application of one ladder iteration. The single carried hypothesis
    is the opaque-leaf edge `LeafAgrees` for the trusted `x25519_ladder_iter`
    leaf (the field ops + `cswap`), exactly as the rest of the emit-correctness
    theory carries its leaf semantics. The `StepAgrees` per-iteration edge of
    `JForProgCT.loopRun_eq` is *discharged* here, not hypothesised. -/
theorem x25519Ladder_loop_denote_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : ⟦LadderState⟧) :
    loopRun x25519Ladder (bodyStepRun leafSem x25519Ladder) init
      = x25519Ladder.denote init :=
  loop_denote_eq hLeaf _ x25519Ladder ladderIterBody_singleVar init

end CatCrypt.Crypto.SecureCompilation.VIR.X25519Ladder
