/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel

/-!
# Pasta (Pallas/Vesta) field add/sub, lowered through the in-Lean x86 backend

This module re-emits the Pasta-cycle base-field add and subtract through the
SAME owned x86 backend (`JasminModel.runBlock` / `X86Dialect.lowerBlock_denote`
/ `AsmPrinter`, no jasminc) used for the BLS12-381 / BN254 Montgomery
field-multiply kernels — but with **hardware ADD/ADC carry chains + CMOV** for
the conditional modular reduction, replacing the **branchless carry synthesis**
the #440 emit used (the per-limb `and`/`xor`/`shr $63` carry-bit computation,
~10 instructions per carry where a single `adc`/`sbb` suffices).

Both Pasta primes are 255-bit, four 64-bit limbs:

* Pallas base field `Fp` (= Vesta scalar field):
  `p = 0x4000000000000000_0000000000000000_224698fc094cf91b_992d30ed00000001`.
* Vesta base field `Fq` (= Pallas scalar field):
  `q = 0x4000000000000000_0000000000000000_224698fc0994a8dd_8c46eb2100000001`.

(Both `≈ 2^254`, so for canonical inputs `a, b ∈ [0, p)` we have `a + b < 2p`,
i.e. a single conditional subtract of `p` suffices for add, and a single
conditional add of `p` for sub.)

## The two kernels

`addBlock pLimbs` (inputs `a, b ∈ [0, p)`):

1. **Carry-add** `t := a + b` over five words: `add t0, b0`; `adc t1, b1`; … ;
   the overflow lands in a fifth word `t4` (`mov t4,0; adc t4,0`) — a genuine
   hardware ADD/ADC chain, not synthesised carries.
2. **Trial subtract** `s := t − p`: copy `t0..t3` to `s0..s3`, `sub s0, p0`;
   `sbb s1, p1`; … ; `sbb t4, 0`. The final borrow `CF = 1` iff `t < p`.
3. **Branch-free select** (`cmovb`): when `CF = 1` (`t < p`) keep the original
   `tj`; else keep the reduced `sj`. Store four words to `r`.

`subBlock pLimbs` (inputs `a, b ∈ [0, p)`):

1. **Borrow-subtract** `t := a − b`: `sub t0, b0`; `sbb t1, b1`; … . The final
   borrow `CF = 1` iff `a < b`, i.e. the true difference is negative.
2. **Masked conditional add of `p`**: form the mask `m = 0 − CF` (all-ones iff
   borrow) via `sbb m, m`, then `and pj, m` and an ADD/ADC chain `t += (m & p)`.
   When `a ≥ b` the mask is zero so nothing is added; when `a < b` it adds `p`
   back, landing `t ∈ [0, p)`. Store four words to `r`.

Both use only `loadMem` / `mov` / `add` / `adc` / `sub` / `sbb` / `cmovb` /
`and_` / `storeMem` — the hardware-flag ADD/ADC + CMOV instruction set, the
same arms the BN254 final conditional subtract uses, lowered through the owned
backend with the denotation-preserving lowering proved
(`lowerBlock_denote_closed`).

## What is proved / gated here

* `pastaAddBlock_lowering_correct` / `pastaSubBlock_lowering_correct`: lowering
  the block to `Com (x86Dialect 64)` and denoting on the init state equals
  `runBlock` on the source block — the owned backend's straight-line lowering is
  denotation-preserving across the `loadMem`/`mov`/`add`/`adc`/`sub`/`sbb`/
  `cmovb`/`and_`/`storeMem` mix.
* `*Alloc_no_overflow`: the first-fit allocator assigns every register name a
  distinct pool register (no silent `%rax`-alias, the #380 class).
* `*Asm_shape`: the emitted text contains hardware `addq`/`adcq`/`sbbq`/`cmovb`
  and **no** `shrq $63` carry-synthesis idiom — the witness that the #440
  branchless synthesis is gone.
* The all-inputs byte-identity that the emitted stream computes `(a±b) mod p`
  is the external KAT (`bench/halo2_compare/pasta_field_addsub_kat`, vs GMP
  `(a±b) mod p`): corners + max + random vectors. The value-level field tie is
  `ZK.Halo2PastaFieldEmit.{pastaAdd,pastaSub}_realizes_{add,sub}` (#440), proved
  over `Fp = ZMod p`; this module re-emits those operations with hardware
  carries.

## Trust story

Identical to the BN254/BLS kernels: the verified artifact is
`Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is the thin syntactic trust
boundary, and the SysV leaf prologue/epilogue is trusted ABI scaffolding.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. The Pasta moduli (canonical little-endian limbs) -/

/-- Pallas base-field prime little-endian 64-bit limbs
    (`0x4000000000000000_0000000000000000_224698fc094cf91b_992d30ed00000001`,
    `= 28948022309329048855892746252171976963363056481941560715954676764349967630337`,
    the AUCurves `pallas_modulus`). -/
def pallasLimbs : List Nat :=
  [ 0x992d30ed00000001, 0x224698fc094cf91b, 0x0000000000000000, 0x4000000000000000 ]

/-- Vesta base-field prime little-endian 64-bit limbs
    (`0x4000000000000000_0000000000000000_224698fc0994a8dd_8c46eb2100000001`,
    `= 28948022309329048855892746252171976963363056481941647379679742748393362948097`,
    the AUCurves `vesta_modulus`). -/
def vestaLimbs : List Nat :=
  [ 0x8c46eb2100000001, 0x224698fc0994a8dd, 0x0000000000000000, 0x4000000000000000 ]

/-! ## 2. The field-add body (`a + b mod p`)

`a` words are loaded from `[a + 8j]`, `b` from `[b + 8j]`. The carry-add lands
the (≤ 256-bit, since `a + b < 2p < 2^255`) sum in `t0..t3` with the top carry
in `t4`; a single trial subtract of `p` plus a `cmovb` select reduces it. -/

/-- The hardware-ADD/ADC + CMOV field add over modulus limbs `p`.
    Register names: `a`/`b`/`z` pointers; `t0..t4` the sum window; `s0..s3` the
    trial `t − p`; `hi` stages the `p[j]` immediates. -/
def addBlock (p : List Nat) : List (JInstr 64) :=
  -- t := a + b  (5-word, hardware carry chain)
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .add "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .adc "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .adc "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .adc "t3" (.reg "hi")
  , .mov "t4" (.imm 0), .adc "t4" (.imm 0)
  -- s := t − p  (trial; CF = final borrow = 1 iff t < p)
  , .mov "s0" (.reg "t0"), .mov "hi" (.imm (p[0]!)), .sub "s0" (.reg "hi")
  , .mov "s1" (.reg "t1"), .mov "hi" (.imm (p[1]!)), .sbb "s1" (.reg "hi")
  , .mov "s2" (.reg "t2"), .mov "hi" (.imm (p[2]!)), .sbb "s2" (.reg "hi")
  , .mov "s3" (.reg "t3"), .mov "hi" (.imm (p[3]!)), .sbb "s3" (.reg "hi")
  , .sbb "t4" (.imm 0)   -- top word; CF = 1 ⇒ t < p ⇒ keep originals
  -- select: CF=1 keep tj (original), else keep sj (reduced); store to z.
  , .cmovb "s0" (.reg "t0"), .storeMem "z" 0  (.reg "s0")
  , .cmovb "s1" (.reg "t1"), .storeMem "z" 8  (.reg "s1")
  , .cmovb "s2" (.reg "t2"), .storeMem "z" 16 (.reg "s2")
  , .cmovb "s3" (.reg "t3"), .storeMem "z" 24 (.reg "s3") ]

/-! ## 3. The field-sub body (`a − b mod p`)

The borrow-subtract `a − b` sets `CF = 1` iff `a < b` (the difference is
negative). The mask `m = 0 − CF` (`sbb m, m`) is all-ones in that case; the
masked modulus `m & p` is added back with a hardware ADD/ADC chain — a single
conditional add of `p` (sufficient since `a, b ∈ [0, p)`). -/

/-- The hardware-SUB/SBB + masked-ADD/ADC field sub over modulus limbs `p`.
    Register names: `a`/`b`/`z` pointers; `t0..t3` the difference; `m` the
    borrow mask; `q0..q3` the four masked modulus words; `hi` stages the `p[j]`
    immediates.

    The masked modulus words `qj = m & p[j]` are materialised into registers
    **before** the ADD/ADC chain — the `mov`/`and` that compute them clobber
    `CF`, so they must not interleave the carry chain (the same discipline as
    `P256FieldKernel.condAddP`). The chain itself is then an uninterrupted
    `add`/`adc`/`adc`/`adc`. -/
def subBlock (p : List Nat) : List (JInstr 64) :=
  -- t := a − b  (hardware borrow chain); CF = 1 iff a < b
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .sub "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .sbb "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .sbb "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .sbb "t3" (.reg "hi")
  -- m := 0 − CF  (all-ones iff borrow)
  , .mov "m" (.imm 0), .sbb "m" (.imm 0)
  -- precompute the four masked modulus words qj = m & p[j] (these clobber CF)
  , .mov "q0" (.imm (p[0]!)), .and_ "q0" (.reg "m")
  , .mov "q1" (.imm (p[1]!)), .and_ "q1" (.reg "m")
  , .mov "q2" (.imm (p[2]!)), .and_ "q2" (.reg "m")
  , .mov "q3" (.imm (p[3]!)), .and_ "q3" (.reg "m")
  -- uninterrupted ADD/ADC chain: t += (m & p)
  , .add "t0" (.reg "q0"), .adc "t1" (.reg "q1")
  , .adc "t2" (.reg "q2"), .adc "t3" (.reg "q3")
  -- store four words to z
  , .storeMem "z" 0  (.reg "t0"), .storeMem "z" 8  (.reg "t1")
  , .storeMem "z" 16 (.reg "t2"), .storeMem "z" 24 (.reg "t3") ]

/-! ## 4. The initial machine state (reg-ptr ABI)

`a`/`b`/`z` hold the buffer base addresses (register names); the operand words
live at `[a + 8j]`, `[b + 8j]`. -/

/-- Build the init state from the eight operand limbs. -/
def initState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "a" then
        if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
        else if off = 24 then a3 else 0
      else if base = "b" then
        if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
        else if off = 24 then b3 else 0
      else 0 }

/-! ## 5. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the Pallas add block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the owned backend's straight-line lowering is denotation-
    preserving across the `loadMem`/`mov`/`add`/`adc`/`sub`/`sbb`/`cmovb`/
    `storeMem` mix. -/
theorem pallasAddBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (addBlock pallasLimbs)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) (addBlock pallasLimbs) :=
  lowerBlock_denote_closed (addBlock pallasLimbs)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-- **Lowering correctness on the Pallas sub block.** -/
theorem pallasSubBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (subBlock pallasLimbs)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) (subBlock pallasLimbs) :=
  lowerBlock_denote_closed (subBlock pallasLimbs)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-- **Lowering correctness on the Vesta add block.** -/
theorem vestaAddBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (addBlock vestaLimbs)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) (addBlock vestaLimbs) :=
  lowerBlock_denote_closed (addBlock vestaLimbs)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-- **Lowering correctness on the Vesta sub block.** -/
theorem vestaSubBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (subBlock vestaLimbs)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) (subBlock vestaLimbs) :=
  lowerBlock_denote_closed (subBlock vestaLimbs)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-! ## 6. Register allocation (reg-ptr ABI, no scratch frame)

`z`→`%rdi`, `a`→`%rsi`, `b`→`%rdx` (the SysV argument registers). No `MULX`, so
`%rdx` is free for the `b` pointer; no stack scratch frame is needed (the trial
and mask live in pool registers). -/

/-- Pin the three buffer pointers to the SysV argument registers. -/
def pastaAddSubPinned : GpAlloc :=
  [("z", "%rdi"), ("a", "%rsi"), ("b", "%rdx")]

/-- The Pallas add allocation maps every name to a distinct pool register. -/
theorem pallasAddAlloc_no_overflow :
    allocOverflow pastaAddSubPinned (addBlock pallasLimbs) = none := by native_decide

/-- The Pallas sub allocation maps every name to a distinct pool register. -/
theorem pallasSubAlloc_no_overflow :
    allocOverflow pastaAddSubPinned (subBlock pallasLimbs) = none := by native_decide

/-- The Vesta add allocation maps every name to a distinct pool register. -/
theorem vestaAddAlloc_no_overflow :
    allocOverflow pastaAddSubPinned (addBlock vestaLimbs) = none := by native_decide

/-- The Vesta sub allocation maps every name to a distinct pool register. -/
theorem vestaSubAlloc_no_overflow :
    allocOverflow pastaAddSubPinned (subBlock vestaLimbs) = none := by native_decide

/-! ## 7. AT&T assembly emission (reg-ptr SysV ABI, no scratch frame) -/

/-- Render one add/sub leaf. The three pointer args are already in their SysV
    registers (`z`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`); the prologue only saves the
    callee-saved registers the allocation uses. The body is `runBlock`-verified;
    the prologue/epilogue are trusted ABI scaffolding. -/
def renderAddSub (name : String) (block : List (JInstr 64)) : String :=
  let alloc := allocGp pastaAddSubPinned block
  renderLeafFn name
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15" ]
    (renderBlockBody alloc block)
    [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- The emitted Pallas field add leaf `pasta_field_add(r, a, b)`. -/
def pallasAddAsm : String := renderAddSub "pasta_field_add" (addBlock pallasLimbs)

/-- The emitted Pallas field sub leaf `pasta_field_sub(r, a, b)`. -/
def pallasSubAsm : String := renderAddSub "pasta_field_sub" (subBlock pallasLimbs)

/-- The emitted Vesta field add leaf `vesta_field_add(r, a, b)`. -/
def vestaAddAsm : String := renderAddSub "vesta_field_add" (addBlock vestaLimbs)

/-- The emitted Vesta field sub leaf `vesta_field_sub(r, a, b)`. -/
def vestaSubAsm : String := renderAddSub "vesta_field_sub" (subBlock vestaLimbs)

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Shape check: the emitted Pallas add uses the hardware ADD/ADC carry chain +
    `cmovb` select, and contains **no** `shrq $63` carry-synthesis idiom (the
    #440 branchless form) — the witness that hardware carries replaced it. -/
theorem pallasAddAsm_shape :
    hasSub pallasAddAsm "addq"
      ∧ hasSub pallasAddAsm "adcq"
      ∧ hasSub pallasAddAsm "sbbq"
      ∧ hasSub pallasAddAsm "cmovb"
      ∧ hasSub pallasAddAsm "(%rdi)"
      ∧ (hasSub pallasAddAsm "shrq $63" = false) := by native_decide

/-- Shape check: the emitted Pallas sub uses the hardware SUB/SBB borrow chain +
    masked ADD/ADC add-back, and contains **no** `shrq $63` carry synthesis. -/
theorem pallasSubAsm_shape :
    hasSub pallasSubAsm "subq"
      ∧ hasSub pallasSubAsm "sbbq"
      ∧ hasSub pallasSubAsm "adcq"
      ∧ hasSub pallasSubAsm "(%rdi)"
      ∧ (hasSub pallasSubAsm "shrq $63" = false) := by native_decide

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness.
    Pallas leaves use the bench's `pasta_field_{add,sub}` symbol names (drop-in
    over the #440 branchless `.s`); Vesta leaves are emitted alongside. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/halo2_compare/gen_com"
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/pasta_field_add_owned_from_lean.s" pallasAddAsm
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/pasta_field_sub_owned_from_lean.s" pallasSubAsm
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/vesta_field_add_owned_from_lean.s" vestaAddAsm
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/vesta_field_sub_owned_from_lean.s" vestaSubAsm
  IO.println "wrote gen_com/{pasta,vesta}_field_{add,sub}_owned_from_lean.s (owned x86 backend, hardware ADD/ADC+CMOV)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel
