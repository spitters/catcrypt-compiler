/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw

/-!
# The Plonky3 BabyBear NTT butterfly, lowered through the in-Lean x86 backend (#281)

`Plonky3NttButterflyEmit` emits the radix-2 decimation-in-time NTT butterfly
*body* as a `Com jasminDialect` of `regArith mul/shr/sub/and/add` bindings,
rendered to a `.jazz` for **jasminc** to compile. This module lowers the *same*
butterfly word arithmetic through the **in-Lean** x86 backend instead — a
straight-line `List (JInstr 64)` denoting via the faithful Jasmin-Rocq port
(`JasminModel.runBlock` / `evalInstr`), down to AT&T text by `AsmPrinter`, with
**no jasminc** in the chain.

This is the next increment of the own-the-backend task: the first FULL hot
kernel lowered end-to-end through the in-Lean backend. It exercises the new
word-granular memory operands (`loadMem`/`storeMem`) the reg-ptr ABI needs to
copy the `[a, b, w]` arguments in from `[inp + 8·k]` and store the two result
words out to `[out + 0]`, `[out + 8]`, plus the new `NEG` used by the branchless
conditional subtract.

## The reg-ptr ABI and the body

The exported leaf has the signature of `plonky3_ntt_butterfly_rc`: a `u64[2]`
output buffer `out` and a `const u64[9]` input buffer `inp` whose words are
`[a, b, w, MU, p, 0, 30, 32, 63]`. Here the field constants (`MU, p` and the
shift counts) are folded into **immediate** operands, so the kernel reads only
`a, b, w` from memory. The branchless conditional subtract
`csub(r) = let t = r − p; t + (p & (0 − (t >> 63)))` is realised with `MOV/SUB/
SHR/NEG/AND/ADD`; `bbSub a wb = let d = a − wb; d + (p & (0 − (d >> 63)))` is the
same shape with no leading `− p`.

## What is proved here

* `butterflyBlock_lowering_correct` (via `lowerBlock_denote_closed`): lowering the
  block to `Com (x86Dialect 64)` and denoting it on an init state equals
  `runBlock` on the source block — the in-Lean backend's straight-line lowering
  is denotation-preserving, including across the new memory ops.
* `butterfly_out0_spec` / `butterfly_out1_spec`: the two stored output words equal
  the **spec field butterfly** `(bbAdd a (bbMul w b), bbSub a (bbMul w b))` over
  canonical residues `a, b, w < p`. This reuses the proved Barrett law
  (`Plonky3BarrettLaw.barrettMul_correct`) and the conditional-subtract laws
  (`Poseidon2Emit.bbCsub_correct`, `bbAdd_correct`), so the in-Lean-lowered kernel
  computes the BabyBear field butterfly.

## Trust story

Identical to `JasminModel` / `X86Dialect` / `AsmPrinter`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the thin syntactic trust
boundary. No `sorry`; axioms are `[propext, Quot.sound]` (+ `Lean.ofReduceBool`
for the `native_decide` numeric pins), matching the rest of the backend.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
  (bbP bbCsub bbMul bbAdd bbMul_correct)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3BarrettLaw
  (bbMU barrettReduceMU barrettMul_correct)

/-! ## 1. Numeric constants as immediate operands -/

/-- The Barrett constant `MU = ⌊2^62 / p⌋ = 2290649223`. -/
def muN : Nat := 2290649223
/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921`. -/
def pN : Nat := 2013265921

/-! ## 2. The straight-line body as a `List (JInstr 64)`

Register names: `inp`/`out` (the two pointers, holding the buffer base
addresses), `a`/`b`/`w` (copied-in inputs), `x`/`q` (Barrett scratch), `wb` (the
field product), `m` (csub mask scratch), `o0`/`o1` (the two outputs). -/

/-- The butterfly body. Matches `Plonky3NttButterflyEmit`'s `regArith` sequence,
    with field constants as immediates and arg/result copies as memory `MOV`s. -/
def butterflyBlock : List (JInstr 64) :=
  [ -- copy args in: a=[inp], b=[inp+8], w=[inp+16]
    .loadMem "a" "inp" 0
  , .loadMem "b" "inp" 8
  , .loadMem "w" "inp" 16
    -- materialize MU in a register: it exceeds the signed imm32 range, so it
    -- cannot be an `IMUL` immediate operand (the by-construction emit would use
    -- a constant register slot; here we MOV it in once).
  , .mov "MU" (.imm muN)
    -- x = w * b  (the canonical product, < 2^62)
  , .mov "x" (.reg "w")
  , .imul "x" (.reg "b")
    -- q = ((x >> 30) * MU >> 32) * p     (Barrett estimate q·p)
  , .mov "q" (.reg "x")
  , .shr "q" (.imm 30)
  , .imul "q" (.reg "MU")
  , .shr "q" (.imm 32)
  , .imul "q" (.imm pN)
    -- x = t = x - q·p   (∈ [0, 2p))
  , .sub "x" (.reg "q")
    -- wb = csub(x):  s = x - p; m = 0 - (s>>63); wb = s + (m & p)
  , .mov "wb" (.reg "x")
  , .sub "wb" (.imm pN)
  , .mov "m" (.reg "wb")
  , .shr "m" (.imm 63)
  , .neg "m"
  , .and_ "m" (.imm pN)
  , .add "wb" (.reg "m")
    -- o1 = bbSub a wb:  d = a - wb; m = 0 - (d>>63); o1 = d + (m & p)
  , .mov "o1" (.reg "a")
  , .sub "o1" (.reg "wb")
  , .mov "m" (.reg "o1")
  , .shr "m" (.imm 63)
  , .neg "m"
  , .and_ "m" (.imm pN)
  , .add "o1" (.reg "m")
    -- o0 = bbAdd a wb:  s = (a + wb) - p; m = 0 - (s>>63); o0 = s + (m & p)
  , .mov "o0" (.reg "a")
  , .add "o0" (.reg "wb")
  , .sub "o0" (.imm pN)
  , .mov "m" (.reg "o0")
  , .shr "m" (.imm 63)
  , .neg "m"
  , .and_ "m" (.imm pN)
  , .add "o0" (.reg "m")
    -- store results: out[0] = o0 (= a + ω·b), out[1] = o1 (= a − ω·b)
  , .storeMem "out" 0 (.reg "o0")
  , .storeMem "out" 8 (.reg "o1") ]

/-- Instruction count of the lowered kernel body (excluding ABI prologue /
    epilogue): 3 loads + 1 MU-load + 8 Barrett + 6 csub + 6 subReduce + 7
    add-reduce + 2 stores = 36 instructions. -/
theorem butterflyBlock_length : butterflyBlock.length = 36 := by native_decide

/-! ## 3. The initial machine state (reg-ptr ABI)

`inp`/`out` hold the buffer base addresses (modeled as the register *names*
`"inp"`/`"out"`; only the keying matters). The input words live in memory at
`[inp + 8·k]`; we seed `a, b, w` at offsets `0, 8, 16`. -/

/-- Build the init state from the three canonical-residue inputs `a, b, w`: the
    `inp` buffer holds `a, b, w` at offsets `0, 8, 16`; flags clear; `out` and
    every other cell start at `0`. The `inp`/`out` pointer registers are
    irrelevant to the word arithmetic (they only key the memory map). -/
def initState (a b w : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "inp" then
        if off = 0 then a else if off = 8 then b else if off = 16 then w else 0
      else 0 }

/-! ## 4. Lowering correctness (denotation = `runBlock`, incl. memory ops) -/

/-- **Lowering correctness on the butterfly block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the in-Lean backend's straight-line lowering is
    denotation-preserving across `loadMem`/`imul`/`shr`/`sub`/`neg`/`and`/`add`/
    `storeMem`. -/
theorem butterflyBlock_lowering_correct (a b w : BitVec 64) :
    (lowerBlock (Γ := []) butterflyBlock).denote (.cons (initState a b w) .nil)
      = runBlock (initState a b w) butterflyBlock :=
  lowerBlock_denote_closed butterflyBlock (initState a b w)

/-! ## 5. The denoted output words equal the BabyBear field butterfly

The block's `runBlock` final state stores `o0` to `[out + 0]` and `o1` to
`[out + 8]`. We prove those words equal the spec field butterfly over canonical
residues `a, b, w < p`:
* `out[0] = bbAdd a (bbMul w b)`  (`= a + ω·b mod p`),
* `out[1] = bbSub a (bbMul w b)`  (`= a − ω·b mod p`).

`runBlock` on the concrete block reduces (by `simp` through `evalInstr`) to the
nested `BitVec` arithmetic; we then identify the Barrett block with
`barrettReduceMU` and the csub idioms with `bbCsub`, and close via the proved
laws. -/

/-- The denoted final state, abbreviated. -/
def finalState (a b w : BitVec 64) : JState 64 :=
  runBlock (initState a b w) butterflyBlock

/-! ## 5b. The kernel's own conditional-subtract / Barrett expressions

These mirror the emitted block **exactly**, including the `(… &&& p)` operand
order the two-address `AND` produces (`m &= p`), so `butterfly_words` closes by
`rfl`. We then bridge each to the field-op laws (`bbCsub`, `barrettReduceMU`) by
`and`-commutativity over an *abstract* word — never bit-blasting the multiply. -/

/-- The kernel's branchless conditional subtract `r ↦ (r − p) + ((0 − ((r−p)>>63)) & p)`
    (the `&&& p` order the emitted two-address `AND` produces). -/
def kCsub (r : BitVec 64) : BitVec 64 :=
  (r - 2013265921#64) + ((0#64 - (r - 2013265921#64) >>> (63 : Nat)) &&& 2013265921#64)

/-- The kernel's branchless field subtract `a wb ↦ (a − wb) + ((0 − ((a−wb)>>63)) & p)`. -/
def kSubReduce (a wb : BitVec 64) : BitVec 64 :=
  (a - wb) + ((0#64 - (a - wb) >>> (63 : Nat)) &&& 2013265921#64)

/-- The kernel's Barrett product `w·b ↦ csub(x − ((x>>30)·MU>>32)·p)`, `x = w·b`. -/
def kBarrett (w b : BitVec 64) : BitVec 64 :=
  let x := w * b
  let q := (((x >>> (30 : Nat)) * 2290649223#64) >>> (32 : Nat)) * 2013265921#64
  kCsub (x - q)

set_option maxRecDepth 4000 in
/-- **The emitted block's two stored words, as the kernel's own arithmetic.** The
    `runBlock` final state stores `out[0] = kCsub (a + kBarrett w b)` (the field
    add) and `out[1] = kSubReduce a (kBarrett w b)` (the field sub) — each a
    line-for-line `rfl` against the lowered `evalInstr` chain (the field
    multiplies stay opaque). This is the **word-level** denotation of the
    in-Lean-lowered kernel. -/
theorem butterfly_words (a b w : BitVec 64) :
    (finalState a b w).load "out" 0 = kCsub (a + kBarrett w b)
      ∧ (finalState a b w).load "out" 8 = kSubReduce a (kBarrett w b) := by
  -- Step the 35-instruction straight-line block: each `runBlock_cons` peels one
  -- `evalInstr`, reducing the chain to a structural `BitVec` term over `a b w`.
  simp only [finalState, butterflyBlock, runBlock_cons, runBlock_nil, evalInstr,
    initState, JState.load, JState.store, JState.setReg, JState.get, JState.writeB5W,
    x86_MOV, x86_IMULt, x86_SHR, x86_SUB, x86_NEG, x86_AND, x86_ADD,
    JOperand.eval, rflags_of_aluop, rflags_of_bwop, rflags_of_mul, rflags_OF,
    shiftCount, wshr, B5W.word, wreprN, BitVec.ofNat_eq_ofNat,
    BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
    Nat.min_def, Nat.reduceLeDiff,
    kCsub, kSubReduce, kBarrett, bbMU, bbP, muN, pN,
    show ((0 : Int) = 8) = False by decide,
    show ((0 : Int) = 0) = True by decide,
    show ((8 : Int) = 0) = False by decide,
    show ((16 : Int) = 0) = False by decide,
    show ((16 : Int) = 8) = False by decide,
    String.reduceEq,
    reduceIte, and_self, and_true, true_and, reduceCtorEq, ite_true, ite_false]

/-! ## 6. The output words ARE the BabyBear field butterfly

For canonical residues `a, b, w < p`, the stored words equal the spec butterfly
`(a + ω·b mod p, a − ω·b mod p)`. First the kernel's `kBarrett`/`kCsub` match the
proved field ops (`barrettReduceMU`, `bbCsub`) by `and`-commutativity over an
abstract word; then `barrettMul_correct` / `bbAdd_correct` give the field
multiply and add. -/

/-- The kernel `kCsub` equals the proved `bbCsub` (only the `AND` operand order
    differs). Abstract over the input — no multiply is bit-blasted. -/
theorem kCsub_eq_bbCsub (r : BitVec 64) : kCsub r = bbCsub r := by
  simp only [kCsub, bbCsub, bbP]
  bv_decide

/-- The kernel `kBarrett` equals the proved Barrett reduction `barrettReduceMU`. -/
theorem kBarrett_eq (w b : BitVec 64) : kBarrett w b = barrettReduceMU (w * b) := by
  simp only [kBarrett, barrettReduceMU, kCsub_eq_bbCsub, bbMU, bbP]
  rfl

/-- `wb = barrettReduceMU (w·b)` is canonical (`< p`) for canonical `w, b`. -/
theorem wb_lt_p (b w : BitVec 64) (hb : b < bbP) (hw : w < bbP) :
    barrettReduceMU (w * b) < bbP := by
  rw [barrettMul_correct w b hw hb]
  exact BitVec.umod_lt _ (by decide)

/-- **`out[0]` is the field sum `a + ω·b`.** For canonical `a, b, w < p`, the
    stored low word equals `bbAdd a (bbMul w b) = (a + (w·b mod p)) mod p`. -/
theorem butterfly_out0_spec (a b w : BitVec 64)
    (ha : a < bbP) (hb : b < bbP) (hw : w < bbP) :
    (finalState a b w).load "out" 0 = bbAdd a (bbMul w b) := by
  rw [(butterfly_words a b w).1, kBarrett_eq, kCsub_eq_bbCsub]
  -- bbCsub (a + wb) = bbAdd a wb, and bbMul w b = (w*b)%p = barrettReduceMU (w*b)
  rw [show bbMul w b = barrettReduceMU (w * b) by
        rw [bbMul_correct w b hw hb, barrettMul_correct w b hw hb]]
  rfl

/-- **`out[1]` is the field difference `a − ω·b`.** For canonical `a, b, w < p`,
    the stored high word equals `(a + p − (w·b mod p)) mod p` — the BabyBear
    field subtract `bbSub a (bbMul w b)`. -/
theorem butterfly_out1_spec (a b w : BitVec 64)
    (ha : a < bbP) (hb : b < bbP) (hw : w < bbP) :
    (finalState a b w).load "out" 8
      = (a + bbP - bbMul w b) % bbP := by
  have hwb : barrettReduceMU (w * b) < bbP := wb_lt_p b w hb hw
  rw [(butterfly_words a b w).2, kBarrett_eq]
  rw [show bbMul w b = barrettReduceMU (w * b) by
        rw [bbMul_correct w b hw hb, barrettMul_correct w b hw hb]]
  -- field subtract on canonical residues, via the sign-bit conditional add
  set wb := barrettReduceMU (w * b) with hwbdef
  have haa : a < (2013265921 : BitVec 64) := by simpa [bbP] using ha
  have hww : wb < (2013265921 : BitVec 64) := by simpa [bbP] using hwb
  simp only [kSubReduce, bbP]
  bv_decide

/-! ## 6b. Constant time -/

/-- Every memory reference in the butterfly body is a base+displacement
    `loadMem`/`storeMem` on `inp`/`out` with a literal offset; the Barrett
    reduce and both conditional subtracts are branch-free sign-mask arithmetic.
    The body is therefore in the direct-addressing class. -/
theorem butterflyBlock_allDirect : allDirect butterflyBlock = true := by decide

/-- **Constant time.** The BabyBear butterfly produces the same machine leakage
    trace from any two starting states, via
    `ConstantTimeCoverage.allDirect_constant_time`. -/
theorem butterflyBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ butterflyBlock = blockLeak s₂ butterflyBlock :=
  allDirect_constant_time butterflyBlock butterflyBlock_allDirect s₁ s₂

/-! ## 7. AT&T assembly emission (in-Lean backend, no jasminc)

`AsmPrinter.renderLeafFn` wraps the rendered body in a System-V leaf with the
reg-ptr ABI glue: `out` pinned to `%rdi`, `inp` to `%rsi` (the first two
argument registers). The body lines are the 36 `JInstr` rendered one-per-line;
the prologue/epilogue are trusted ABI scaffolding outside the verified body. -/

/-- Pin the two pointer arguments to the System-V argument registers. -/
def butterflyPinned : GpAlloc := [("out", "%rdi"), ("inp", "%rsi")]

/-- The register allocation for the kernel (pointers pinned, working regs
    first-fit over the remaining pool). -/
def butterflyAlloc : GpAlloc := allocGp butterflyPinned butterflyBlock

/-- The rendered AT&T body (one line per `JInstr`). -/
def butterflyAsmBody : List String := renderBlockBody butterflyAlloc butterflyBlock

/-- The full emitted `.s` leaf function. The body is `runBlock`-verified; the
    callee-saved-register save/restore prologue/epilogue and the `ret` are
    trusted System-V ABI glue, *outside* the verified body. The first-fit
    allocator uses `%rbx`, `%r12`, `%r13` (callee-saved), so they are pushed on
    entry and popped before `ret`; `out`/`inp` arrive in `%rdi`/`%rsi` per the
    ABI. -/
def butterflyAsm : String :=
  renderLeafFn "plonky3_ntt_butterfly_x86"
    ["\tpushq %rbx", "\tpushq %r12", "\tpushq %r13"]
    butterflyAsmBody
    ["\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret"]

-- #eval IO.println butterflyAsm

/-- The emitted asm has one body line per instruction. -/
theorem butterflyAsmBody_length : butterflyAsmBody.length = 36 := by native_decide

/-- Local substring test (`needle` occurs in `hay`), for the shape checks. -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- The Barrett constant and prime appear as immediates; the memory loads/stores
    print in AT&T `off(%base)` form; `negq` and `mulx`-free scalar body. -/
#guard (hasSub butterflyAsm "2290649223") && (hasSub butterflyAsm "2013265921") && (hasSub butterflyAsm "(%rsi)") && (hasSub butterflyAsm "(%rdi)") && (hasSub butterflyAsm "negq")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/ntt_butterfly_x86_from_lean.s" butterflyAsm
  IO.println "wrote gen_com/ntt_butterfly_x86_from_lean.s (in-Lean x86 backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel
