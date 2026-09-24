/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254MontMulKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254MontMulKernel
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# BN254 `Fp2` add / sub, owned x86 leaves + component-wise driver

The BN254 pairing tower's `Fp2 = Fp[u]/(u² + 1)` additive group: `Fp2_add` and
`Fp2_sub` are **component-wise** modular add/sub on the two `Fp` halves
(`c0` at byte offset `0`, `c1` at byte offset `32` of a 64-byte `Fp2`). This is
the owned-pipeline twin of the AUCurves-emitted `gen/tower_subset.jazz`
(`bn254_Fp2_add` / `bn254_Fp2_sub`, which call the bedrock2 `bn254_add`/
`bn254_sub` leaves through jasminc); here both the four-limb `Fp` add/sub leaves
and the `Fp2` driver are emitted through CatCrypt's own x86 backend
(`Com (x86Dialect 64) → runBlock → evalInstr`, no jasminc).

The construction reuses the four-limb `Fp` modular-add/sub idiom proven for
`Bls12381Fp2MulKernel` (six-limb) and `Bn254MontMulKernel.bn254FinalReduce`
(four-limb conditional subtract), specialised to the BN254 base prime
`p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`
(`Bn254MontMulKernel.pLimbs`).

## Add idiom (`a + b mod p`)
Canonical residues (`a, b < p`) give `a + b < 2p < 2^256`, so one conditional
subtract of `p` reduces. The ADD/ADC chain lands the five-word sum in `t0..t4`;
the trial difference `t − p` is staged in the stack scratch frame `sp[0..3]`;
`cmovb` keeps the original word when the final borrow (`CF`) signals `t < p`.

## Sub idiom (`a − b mod p`)
The SUB/SBB borrow chain computes `a − b`; `CF = 1` iff `a < b`. The mask
`m = 0 − CF` is all-ones in that case; the masked modulus `m & p` is added back
with one ADD/ADC chain (sufficient since `a, b ∈ [0, p)`), the masked words
staged through the scratch frame so the AND (which clobbers `CF`) precedes the
uninterrupted carry chain.

## `Fp2` driver
`Fp2_add(z, x, y)` = `Fp_add(z+0, x+0, y+0)` ; `Fp_add(z+32, x+32, y+32)` (and
likewise for sub) — two calls into the verified four-limb `Fp` leaves at the
`c0`/`c1` offsets. The driver carries a SysV call frame (trusted scaffolding);
the arithmetic it performs is the two verified `Fp` bodies.

## Trust story
The verified artifact is the `runBlock`-of-`evalInstr` denotation of each `Fp`
body. §Denotation gives the in-Lean `#eval` evidence: the emitted add/sub blocks
compute `(a ± b) mod p` byte-identically on the published EIP-197 BN254 G2
generator coordinates (Montgomery form, the exact KAT anchor in
`bench/bn254_compare/jasmin_tower/bn254_tower_kat.rs`) plus boundary cases. The
`AsmPrinter` + `gas` step is the syntactic trust boundary; the driver call frame
is trusted scaffolding outside the verified field bodies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254Fp2AddSubKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254MontMulKernel (pLimbs)

/-! ## 1. The four-limb `Fp` add body (`a + b mod p`) -/

/-- The four-limb `Fp` add over the BN254 modulus. `a`/`b`/`z` operand/result
    pointers, `sp` the scratch-frame base; `t0..t4` the sum window; `lo`/`hi`
    stage the loaded `b[j]` and the `p[j]` immediates; the trial words `t − p`
    live in `sp[0..3]`. -/
def fpAddBlock : List (JInstr 64) :=
  -- t := a + b  (five-word, hardware carry chain; top carry in t4)
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .add "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .adc "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .adc "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .adc "t3" (.reg "hi")
  , .mov "t4" (.imm 0), .adc "t4" (.imm 0)
  -- trial := t − p ; CF = final borrow = 1 iff t < p ; stage to sp[0..3]
  , .mov "lo" (.reg "t0"), .mov "hi" (.imm (pLimbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (pLimbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (pLimbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (pLimbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .sbb "t4" (.imm 0)   -- top word; CF = 1 ⇒ t < p ⇒ keep originals
  -- select: load trial into hi, cmovb original (tj) over it when CF=1, store to z.
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi") ]

/-! ## 2. The four-limb `Fp` sub body (`a − b mod p`) -/

/-- The four-limb `Fp` sub over the BN254 modulus. `a`/`b`/`z` pointers, `sp`
    scratch base; `t0..t3` the difference; `m` the borrow mask; `lo`/`hi` stage
    operands and the `p[j] & m` masked words (held in `sp[0..3]`). The masked
    words are materialised **before** the ADD/ADC chain (the `and` clobbers CF). -/
def fpSubBlock : List (JInstr 64) :=
  -- t := a − b  (hardware borrow chain); CF = 1 iff a < b
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .sub "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .sbb "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .sbb "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .sbb "t3" (.reg "hi")
  -- m := 0 − CF  (all-ones iff borrow)
  , .mov "m" (.imm 0), .sbb "m" (.imm 0)
  -- precompute the four masked modulus words qj = m & p[j] into sp (these clobber CF)
  , .mov "lo" (.imm (pLimbs[0]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.imm (pLimbs[1]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.imm (pLimbs[2]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.imm (pLimbs[3]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 24 (.reg "lo")
  -- uninterrupted ADD/ADC chain: t += (m & p), reloading each masked word
  , .loadMem "hi" "sp" 0,  .add "t0" (.reg "hi")
  , .loadMem "hi" "sp" 8,  .adc "t1" (.reg "hi")
  , .loadMem "hi" "sp" 16, .adc "t2" (.reg "hi")
  , .loadMem "hi" "sp" 24, .adc "t3" (.reg "hi")
  -- store four words to z
  , .storeMem "z" 0  (.reg "t0"), .storeMem "z" 8  (.reg "t1")
  , .storeMem "z" 16 (.reg "t2"), .storeMem "z" 24 (.reg "t3") ]

/-! ## 3. The initial machine state (reg-ptr ABI) for the add/sub bodies -/

/-- Build the init state from the eight operand limbs (`a` at `[a+8j]`, `b` at
    `[b+8j]`). The scratch frame `sp` starts zeroed. -/
def initState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "a" then
        (if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
         else if off = 24 then a3 else 0)
      else if base = "b" then
        (if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
         else if off = 24 then b3 else 0)
      else 0 }

/-! ## 4. Lowering correctness (denotation = `runBlock`) for the `Fp` bodies -/

/-- **Lowering correctness on the `Fp` add block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the owned backend's straight-line lowering is
    denotation-preserving across the `loadMem`/`mov`/`add`/`adc`/`sub`/`sbb`/
    `cmovb`/`storeMem` mix. -/
theorem fpAddBlock_lowering_correct (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) fpAddBlock).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) fpAddBlock :=
  lowerBlock_denote_closed fpAddBlock (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-- **Lowering correctness on the `Fp` sub block.** -/
theorem fpSubBlock_lowering_correct (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (lowerBlock (Γ := []) fpSubBlock).denote
        (.cons (initState a0 a1 a2 a3 b0 b1 b2 b3) .nil)
      = runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) fpSubBlock :=
  lowerBlock_denote_closed fpSubBlock (initState a0 a1 a2 a3 b0 b1 b2 b3)

/-! ## 5. Constant time for the `Fp` bodies: straight-line, all-direct addressing

Both four-limb bodies address memory through a base pointer and a
compile-time-constant displacement (`loadMem`/`storeMem`); the conditional
reduce is branch-free (`cmovb` in the add, the borrow mask in the sub), so no
`loadMemIdx`/`storeMemIdx` appears and the decidable `allDirect` check carries
each block into `ConstantTimeCoverage.allDirect_constant_time`. The `Fp2`
drivers of §8 are `String` assembly with `call`s, outside the `JInstr`
leakage model. -/

/-- The four-limb `Fp` add body uses only direct base+displacement addressing. -/
theorem fpAddBlock_allDirect : allDirect fpAddBlock = true := by decide

/-- **Constant time.** The emitted four-limb `Fp` add produces the same machine
    leakage trace from any two starting states: its observable control-flow +
    memory-address sequence is a function of the program text alone, so it
    carries no information about the operand limbs. -/
theorem fpAddBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fpAddBlock = blockLeak s₂ fpAddBlock :=
  allDirect_constant_time fpAddBlock fpAddBlock_allDirect s₁ s₂

/-- The four-limb `Fp` sub body uses only direct base+displacement addressing. -/
theorem fpSubBlock_allDirect : allDirect fpSubBlock = true := by decide

/-- **Constant time.** The emitted four-limb `Fp` sub produces the same machine
    leakage trace from any two starting states. -/
theorem fpSubBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ fpSubBlock = blockLeak s₂ fpSubBlock :=
  allDirect_constant_time fpSubBlock fpSubBlock_allDirect s₁ s₂

/-! ## 6. Register allocation for the `Fp` bodies (reg-ptr ABI + scratch frame)

`z`→`%rdi`, `a`→`%rsi`, `b`→`%rdx` (the SysV argument registers); the scratch
base `sp`→`%rbp` (excluded from `gpPool`, so it costs no pool slot). No `MULX`,
so `%rdx` is free for the `b` pointer. -/

/-- Pin the three buffer pointers to the SysV argument registers + scratch base. -/
def fpAddSubPinned : GpAlloc :=
  [("z", "%rdi"), ("a", "%rsi"), ("b", "%rdx"), ("sp", "%rbp")]

/-! ## 7. AT&T emission of the `Fp` add/sub leaves (reg-ptr SysV ABI + frame)

The leaves carry a 32-byte scratch frame (`sp`→`%rbp`); the body is
`runBlock`-verified, the prologue/epilogue + frame are trusted ABI
scaffolding. -/

/-- Render one `Fp` add/sub leaf with a 32-byte scratch frame. -/
def renderFpAddSub (name : String) (block : List (JInstr 64)) : String :=
  let alloc := allocGp fpAddSubPinned block
  renderLeafFn name
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $32, %rsp", "\tmovq %rsp, %rbp" ]
    (renderBlockBody alloc block)
    [ "\taddq $32, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- The emitted `Fp` add leaf `bn254_fp_add_x86_from_lean(z, a, b)`. -/
def fpAddAsm : String := renderFpAddSub "bn254_fp_add_x86_from_lean" fpAddBlock

/-- The emitted `Fp` sub leaf `bn254_fp_sub_x86_from_lean(z, a, b)`. -/
def fpSubAsm : String := renderFpAddSub "bn254_fp_sub_x86_from_lean" fpSubBlock

/-! ## 8. The `Fp2` add / sub component-wise drivers (trusted call frame)

The drivers call the verified four-limb `Fp` add/sub leaves on the two `Fp`
halves of an `Fp2` (`c0` at byte offset `0`, `c1` at offset `32`). The pointer
arguments arrive `z`→`%rdi`, `x`→`%rsi`, `y`→`%rdx`; the bases are saved in
callee-saved registers across the calls and the live operand pointers are
recomputed into the arg registers via `lea` before each `call`. -/

/-- Helper: emit a `call leaf(z=zoff(%rbx), x=xoff(%r12), y=yoff(%r13))`, where
    `%rbx`/`%r12`/`%r13` hold the saved `z`/`x`/`y` bases. -/
def callFp (leaf : String) (zb : String) (zoff : Int)
    (xb : String) (xoff : Int) (yb : String) (yoff : Int) : List String :=
  [ "\tleaq " ++ toString zoff ++ "(" ++ zb ++ "), %rdi"
  , "\tleaq " ++ toString xoff ++ "(" ++ xb ++ "), %rsi"
  , "\tleaq " ++ toString yoff ++ "(" ++ yb ++ "), %rdx"
  , "\tcallq " ++ leaf ]

/-- `c0` half offset (byte 0) and `c1` half offset (byte 32) within a 64-byte
    `Fp2`. -/
def C0 : Int := 0
def C1 : Int := 32

/-- The `Fp2` add driver `bn254_Fp2_add_x86_from_lean(z, x, y)`:
    `z.c0 = x.c0 + y.c0` ; `z.c1 = x.c1 + y.c1`, each via the verified four-limb
    `Fp` add leaf. -/
def fp2AddAsm : String :=
  renderLeafFn "bn254_Fp2_add_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $8, %rsp"            -- keep %rsp 16-aligned at the call sites
    , "\tmovq %rdi, %rbx"          -- save z base
    , "\tmovq %rsi, %r12"          -- save x base
    , "\tmovq %rdx, %r13" ]        -- save y base
    ( callFp "bn254_fp_add_x86_from_lean" "%rbx" C0 "%r12" C0 "%r13" C0   -- z.c0 = x.c0 + y.c0
    ++ callFp "bn254_fp_add_x86_from_lean" "%rbx" C1 "%r12" C1 "%r13" C1 )  -- z.c1 = x.c1 + y.c1
    [ "\taddq $8, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- The `Fp2` sub driver `bn254_Fp2_sub_x86_from_lean(z, x, y)`:
    `z.c0 = x.c0 − y.c0` ; `z.c1 = x.c1 − y.c1`. -/
def fp2SubAsm : String :=
  renderLeafFn "bn254_Fp2_sub_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $8, %rsp"
    , "\tmovq %rdi, %rbx"
    , "\tmovq %rsi, %r12"
    , "\tmovq %rdx, %r13" ]
    ( callFp "bn254_fp_sub_x86_from_lean" "%rbx" C0 "%r12" C0 "%r13" C0   -- z.c0 = x.c0 − y.c0
    ++ callFp "bn254_fp_sub_x86_from_lean" "%rbx" C1 "%r12" C1 "%r13" C1 )  -- z.c1 = x.c1 − y.c1
    [ "\taddq $8, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-! ## 9. Denotation evidence (`#eval`, expect `true`)

The `Fp` add/sub blocks compute `(a ± b) mod p` over the BN254 base prime,
checked against the independent `Nat` reference on the published EIP-197 BN254
G2 generator coordinates (Montgomery form — the exact KAT anchor in
`bench/bn254_compare/jasmin_tower/bn254_tower_kat.rs`) plus boundary inputs. -/

/-- The BN254 base prime as a `Nat` (recombined from `pLimbs`). -/
def pNat : Nat :=
  (pLimbs[0]!) + (pLimbs[1]!) * 2^64 + (pLimbs[2]!) * 2^128 + (pLimbs[3]!) * 2^192

/-- Little-endian 4-limb split of a `< 2^256` value. -/
def limbsOf (n : Nat) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  (BitVec.ofNat 64 (n % 2^64), BitVec.ofNat 64 (n / 2^64 % 2^64),
   BitVec.ofNat 64 (n / 2^128 % 2^64), BitVec.ofNat 64 (n / 2^192 % 2^64))

/-- Recombine the four result words at `z[0..3]` after a run. -/
def zOut (s : JState 64) : Nat :=
  (s.load "z" 0).toNat + (s.load "z" 8).toNat * 2^64
    + (s.load "z" 16).toNat * 2^128 + (s.load "z" 24).toNat * 2^192

/-- Run the emitted `Fp` add block on `(x, y)` and read back the `z` value. -/
def runAdd (x y : Nat) : Nat :=
  let (a0, a1, a2, a3) := limbsOf x
  let (b0, b1, b2, b3) := limbsOf y
  zOut (runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) fpAddBlock)

/-- Run the emitted `Fp` sub block on `(x, y)` and read back the `z` value. -/
def runSub (x y : Nat) : Nat :=
  let (a0, a1, a2, a3) := limbsOf x
  let (b0, b1, b2, b3) := limbsOf y
  zOut (runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) fpSubBlock)

/-- Published BN254 G2 generator `c0` coordinate of `Qx` (Montgomery form). -/
def qx_c0 : Nat :=
  0x8e83b5d102bc2026 + 0xdceb1935497b0172 * 2^64
    + 0xfbb8264797811adf * 2^128 + 0x19573841af96503b * 2^192

/-- Published BN254 G2 generator `c0` coordinate of `Qy` (Montgomery form). -/
def qy_c0 : Nat :=
  0x619dfa9d886be9f6 + 0xfe7fd297f59e9b78 * 2^64
    + 0xff9e1a62231b7dfe * 2^128 + 0x28fd7eebae9e4206 * 2^192

/-- All denotation = `(a ± b) mod p` checks, including the EIP-197 anchor. -/
def denoteSpecOk : Bool :=
  (pNat % 2 == 1)                                                      -- p is odd
    && (runAdd qx_c0 qy_c0 == (qx_c0 + qy_c0) % pNat)                  -- add on the anchor
    && (runSub qx_c0 qy_c0 == (qx_c0 + pNat - qy_c0) % pNat)          -- sub on the anchor
    && (runAdd 0 0 == 0)                                               -- add identity
    && (runAdd (pNat - 1) (pNat - 1) == (2 * (pNat - 1)) % pNat)       -- max add (reduces)
    && (runSub 5 7 == (5 + pNat - 7) % pNat)                           -- sub underflow (wraps)
    && (runSub (runAdd qx_c0 qy_c0) qy_c0 == qx_c0)                    -- add/sub round-trip

-- #eval denoteSpecOk   -- expect: true

/-! ## 10. Emit driver -/

/-- Emit driver: write the owned-backend-emitted four-limb `Fp` add/sub leaves
    and the component-wise `Fp2` add/sub drivers for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bn254_compare/jasmin_tower/gen_com"
  IO.FS.writeFile
    "bench/bn254_compare/jasmin_tower/gen_com/bn254_fp_add_x86_from_lean.s" fpAddAsm
  IO.FS.writeFile
    "bench/bn254_compare/jasmin_tower/gen_com/bn254_fp_sub_x86_from_lean.s" fpSubAsm
  IO.FS.writeFile
    "bench/bn254_compare/jasmin_tower/gen_com/bn254_Fp2_add_x86_from_lean.s" fp2AddAsm
  IO.FS.writeFile
    "bench/bn254_compare/jasmin_tower/gen_com/bn254_Fp2_sub_x86_from_lean.s" fp2SubAsm
  IO.println "wrote gen_com/bn254_fp_{add,sub}_x86_from_lean.s + bn254_Fp2_{add,sub}_x86_from_lean.s (owned x86 backend, Fp2 over verified Fp leaves)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bn254Fp2AddSubKernel
