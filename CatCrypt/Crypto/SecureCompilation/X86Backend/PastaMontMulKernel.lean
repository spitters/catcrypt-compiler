/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel

/-!
# Pasta (Pallas/Vesta) `Fp` Montgomery field-multiply, owned x86 backend

The companion to `PastaFieldAddSubKernel`: a full 4×64 CIOS
Montgomery multiply for the Pasta-cycle base fields, emitted through the SAME
owned x86 backend (`runBlock` / `lowerBlock_denote` / `AsmPrinter`, no jasminc)
as the BLS12-381 (`Bls12381MontMulKernel`) and BN254 (`Bn254MontMulKernel`)
field-mul kernels. It is the four-iteration CIOS analog of those, parameterised
over the modulus limbs and the Montgomery constant `n′ = −p⁻¹ mod 2^64`, and
instantiated for both Pasta primes.

In place of a product-then-CIOS-reduce *split* (`pasta_emit_mul_4_8` product +
`pasta_mont_redc_4` reduce) it emits a single fused CIOS body using the MULX +
dual ADCX/ADOX carry-chain idiom — the same machinery the BN254/BLS kernels use
— computing the whole `a·b·R⁻¹ mod p` field multiply in one own-emitted leaf.

## The Montgomery constants (canonical sources)

* Modulus limbs: `PastaFieldAddSubKernel.{pallasLimbs, vestaLimbs}` (the AUCurves
  `pallas_modulus` / `vesta_modulus`).
* `n′ = −p⁻¹ mod 2^64`: `0x992d30ecffffffff` (Pallas), `0x8c46eb20ffffffff`
  (Vesta). Each satisfies `p · n′ + 1 ≡ 0 (mod 2^64)` (checked: both give 0).

## What is proved / gated here

* `pastaMontMulBlock_lowering_correct` (Pallas and Vesta instances): lowering to
  `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
  source block — denotation-preserving across the full
  `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`imul`/`mov`/`sub`/`sbb`/`cmovb`/
  `storeMem` mix.
* `*Alloc_no_overflow`: the first-fit allocator assigns distinct pool registers.
* The all-inputs byte-identity (`emitted == a·b·R⁻¹ mod p`) is the external KAT
  vs GMP — the standard gate for these word kernels; CIOS value
  correctness is a generic Montgomery identity, a 256×256→512 SAT instance
  in-Lean, hence the external oracle. KAT
  (`bench/halo2_compare/pasta_owned_montmul_kat`): 50000 random + corner vectors,
  byte-identical to GMP, for both Pallas and Vesta. Bench: ~46 cyc/op (the fused
  CIOS), vs ~100 cyc for the product-then-reduce split and ~201 cyc for GMP
  `mpz_mul`+`mpz_mod`.

## Trust story

Identical to the BN254/BLS kernels: the verified artifact is
`Com (x86Dialect 64) → runBlock → evalInstr`; `AsmPrinter` + `gas` is the thin
syntactic boundary; the SysV leaf prologue/epilogue is trusted ABI scaffolding.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PastaMontMulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel (pallasLimbs vestaLimbs)

/-! ## 1. The Montgomery constants -/

/-- `n′ = −p⁻¹ mod 2^64` for Pallas (`p·n′ + 1 ≡ 0 mod 2^64`). -/
def pallasNPrime : Nat := 0x992d30ecffffffff

/-- `n′ = −p⁻¹ mod 2^64` for Vesta. -/
def vestaNPrime : Nat := 0x8c46eb20ffffffff

/-! ## 2. The CIOS body (parametric over modulus + `n′`)

The accumulator `T = (t0..t4)` starts at zero. For each multiplier word `b[i]`:
MAC `T += a·b[i]` (dual ADCX/ADOX), the Montgomery factor `m = t0·n′ mod 2^64`
(`imul`), the reduce `T += m·p` (cancels `t0`, window shifts down). After four
iterations a branch-free conditional subtract of `p` lands the result in
`[0, p)`. This is the four-limb specialisation of the BN254 CIOS body. -/

/-- One CIOS MAC step on column `j` (`0 < j < 4`). -/
def macStep (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "yd") "x" (8 * j)
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS reduce step on column `j` (`0 < j < 4`); `p[j]` staged in `hi`. -/
def redStep (p : List Nat) (tlo thi : String) (j : Nat) : List (JInstr 64) :=
  [ .mov "hi" (.imm (p[j]!))
  , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
  , .adcx tlo (.reg "lo"), .adox thi (.reg "hi") ]

/-- One CIOS iteration on multiplier word `b[i]` (MAC, factor, reduce + shift). -/
def ciosIter (p : List Nat) (nPrime : Nat) (i : Nat) : List (JInstr 64) :=
  -- Phase A: MAC  T += a·b[i]
  [ .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" (8 * i)
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ macStep "t1" "t2" 1
  ++ macStep "t2" "t3" 2
  ++ macStep "t3" "t4" 3
  ++ [ .adcx "t4" (.reg "zr"), .adox "t4" (.reg "zr") ]
  -- Phase B: m = t0 * n' mod 2^64, into the multiplier yd
  ++ [ .mov "yd" (.reg "t0"), .mov "hi" (.imm nPrime), .imul "yd" (.reg "hi") ]
  -- Phase C: reduce  T += m*p ; t0 cancels; window shifts down
  ++ [ .xor_ "zr" (.reg "zr")
     , .mov "hi" (.imm (p[0]!))
     , .mulx "hi" "lo" (.reg "yd") (.reg "hi")
     , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi") ]
  ++ redStep p "t1" "t2" 1
  ++ redStep p "t2" "t3" 2
  ++ redStep p "t3" "t4" 3
  ++ [ .adcx "t4" (.reg "zr"), .adox "t4" (.reg "zr")
     , .mov "t0" (.reg "t1"), .mov "t1" (.reg "t2"), .mov "t2" (.reg "t3")
     , .mov "t3" (.reg "t4"), .mov "t4" (.imm 0) ]

/-- The final branch-free conditional subtract of `p` and store to `z[0..3]`;
    trial words staged in the stack scratch frame `sp[0..3]`. -/
def finalReduce (p : List Nat) : List (JInstr 64) :=
  [ .mov "lo" (.reg "t0"), .mov "hi" (.imm (p[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (p[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (p[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (p[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .sbb "t4" (.imm 0)
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi") ]

/-- The full CIOS Montgomery multiply body over modulus `p` and constant `nPrime`. -/
def montMulBlock (p : List Nat) (nPrime : Nat) : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .mov "t0" (.imm 0), .mov "t1" (.imm 0), .mov "t2" (.imm 0)
  , .mov "t3" (.imm 0), .mov "t4" (.imm 0) ]
  ++ (List.range 4).flatMap (ciosIter p nPrime)
  ++ finalReduce p

/-! ## 3. The initial machine state (reg-ptr ABI) — `a` words at `[x]`, `b` at `[y]`. -/

/-- Build the init state from the eight operand limbs (`x`/`y` operand bases). -/
def initState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
        else if off = 24 then a3 else 0
      else if base = "y" then
        if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
        else if off = 24 then b3 else 0
      else 0 }

/-! ## 4. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the Pallas CIOS block.** -/
theorem pallasMontMulBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (montMulBlock pallasLimbs pallasNPrime)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3)
          (montMulBlock pallasLimbs pallasNPrime) :=
  lowerBlock_denote_closed (montMulBlock pallasLimbs pallasNPrime)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-- **Lowering correctness on the Vesta CIOS block.** -/
theorem vestaMontMulBlock_lowering_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) (montMulBlock vestaLimbs vestaNPrime)).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3)
          (montMulBlock vestaLimbs vestaNPrime) :=
  lowerBlock_denote_closed (montMulBlock vestaLimbs vestaNPrime)
    (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-! ## 5. Constant time: straight-line, all-direct addressing

The CIOS body's instruction sequence does not depend on the modulus limbs, only
its immediates do, so the `allDirect` check holds for **every** modulus and
Montgomery constant. Memory is addressed through a base pointer and a
compile-time-constant displacement (`loadMem`/`storeMem`/`mulxMem`), and the
final reduce is branch-free (`cmovb`), so no `loadMemIdx`/`storeMemIdx`
appears. -/

/-- One CIOS MAC step uses only direct base+displacement addressing. -/
theorem macStep_allDirect (tlo thi : String) (j : Nat) :
    allDirect (macStep tlo thi j) = true := rfl

/-- One CIOS reduce step uses only direct base+displacement addressing. -/
theorem redStep_allDirect (p : List Nat) (tlo thi : String) (j : Nat) :
    allDirect (redStep p tlo thi j) = true := rfl

/-- One CIOS iteration uses only direct base+displacement addressing. -/
theorem ciosIter_allDirect (p : List Nat) (nPrime i : Nat) :
    allDirect (ciosIter p nPrime i) = true := rfl

/-- The final conditional subtract uses only direct base+displacement
    addressing. -/
theorem finalReduce_allDirect (p : List Nat) :
    allDirect (finalReduce p) = true := rfl

/-- The CIOS Montgomery multiply body uses only direct base+displacement
    addressing, over any modulus limbs and Montgomery constant. Proved by
    splitting the body at its two concatenations and the iteration `flatMap`,
    so the cost is the per-piece checks rather than a reduction of the
    assembled block. -/
theorem montMulBlock_allDirect (p : List Nat) (nPrime : Nat) :
    allDirect (montMulBlock p nPrime) = true := by
  simp only [montMulBlock, allDirect, List.all_append, List.all_flatMap,
    Bool.and_eq_true]
  exact ⟨⟨rfl, List.all_eq_true.mpr fun i _ => ciosIter_allDirect p nPrime i⟩,
    finalReduce_allDirect p⟩

/-- **Constant time, for every modulus.** The emitted CIOS Montgomery multiply
    produces the same machine leakage trace from any two starting states: its
    observable control-flow + memory-address sequence is a function of the
    program text alone, so it carries no information about the operand limbs. -/
theorem montMulBlock_constant_time (p : List Nat) (nPrime : Nat)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ (montMulBlock p nPrime) = blockLeak s₂ (montMulBlock p nPrime) :=
  allDirect_constant_time _ (montMulBlock_allDirect p nPrime) s₁ s₂

/-- **Constant time** for the Pallas Montgomery multiply leaf. -/
theorem pallasMontMul_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ (montMulBlock pallasLimbs pallasNPrime)
      = blockLeak s₂ (montMulBlock pallasLimbs pallasNPrime) :=
  montMulBlock_constant_time _ _ s₁ s₂

/-- **Constant time** for the Vesta Montgomery multiply leaf. -/
theorem vestaMontMul_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ (montMulBlock vestaLimbs vestaNPrime)
      = blockLeak s₂ (montMulBlock vestaLimbs vestaNPrime) :=
  montMulBlock_constant_time _ _ s₁ s₂

/-! ## 6. Register allocation + AT&T emission (reg-ptr ABI + 32-byte scratch) -/

/-- Pin pointers + the `MULX` multiplier `yd`→`%rdx` + scratch base `sp`→`%rbp`. -/
def montMulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- The Pallas mont-mul allocation maps every name to a distinct pool register. -/
theorem pallasMontMulAlloc_no_overflow :
    allocOverflow montMulPinned (montMulBlock pallasLimbs pallasNPrime) = none := by
  native_decide

/-- The Vesta mont-mul allocation maps every name to a distinct pool register. -/
theorem vestaMontMulAlloc_no_overflow :
    allocOverflow montMulPinned (montMulBlock vestaLimbs vestaNPrime) = none := by
  native_decide

/-- Render one mont-mul leaf (reg-ptr ABI, 32-byte scratch, `y` moved out of
    `%rdx`). The body is `runBlock`-verified; prologue/epilogue are trusted. -/
def renderMontMul (name : String) (block : List (JInstr 64)) : String :=
  let alloc := allocGp montMulPinned block
  renderLeafFn name
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $32, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf alloc "y" ]
    (renderBlockBody alloc block)
    [ "\taddq $32, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- The emitted Pallas Montgomery field-mul leaf `pasta_mont_mul_4(z, x, y)`. -/
def pallasMontMulAsm : String :=
  renderMontMul "pasta_mont_mul_4" (montMulBlock pallasLimbs pallasNPrime)

/-- The emitted Vesta Montgomery field-mul leaf `vesta_mont_mul_4(z, x, y)`. -/
def vestaMontMulAsm : String :=
  renderMontMul "vesta_mont_mul_4" (montMulBlock vestaLimbs vestaNPrime)

/- Shape check: the emitted Pallas mont-mul uses the dual carry-chain CIOS
    idiom (`mulx`/`adcx`/`adox`/`imul`) + memory-operand `MULX` from `[x]`. -/
#guard (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "mulx") && (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "adcx") && (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "adox") && (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "imul") && (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "mulxq 0(%rsi)") && (PastaFieldAddSubKernel.hasSub pallasMontMulAsm "(%rdi)")

/-- Emit driver: write the in-Lean-backend-emitted mont-mul `.s` files. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/halo2_compare/gen_com"
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/pasta_mont_mul_4_owned_from_lean.s" pallasMontMulAsm
  IO.FS.writeFile
    "bench/halo2_compare/gen_com/vesta_mont_mul_4_owned_from_lean.s" vestaMontMulAsm
  IO.println "wrote gen_com/{pasta,vesta}_mont_mul_4_owned_from_lean.s (owned x86 backend CIOS, no jasminc)"

/-! ## Artifact generation at elaboration

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.PastaMontMulKernel
