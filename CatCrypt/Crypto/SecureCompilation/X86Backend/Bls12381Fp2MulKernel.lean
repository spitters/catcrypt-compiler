/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel

/-!
# BLS12-381 `Fp2` (quadratic extension) multiply + square, owned x86 leaf (#602/#219)

**Variant: RELIC-transcribed (tests-only correctness).** This owned x86 emit is
hand-transcribed from the RELIC pairing reference and gated **byte-identical to
RELIC**. RELIC is unverified C, so that byte-identity is a **test**, not a
correctness proof. The verified-correctness BLS variant — owned emit whose
denotation is tied to the **AUCurves** Rocq-proved pairing via the rocqlean
axiom bridge — is a **separate** artifact, kept distinct from this one so the
RELIC-transcribed and AUCurves-generated variants can be compared.

The BLS12-381 pairing tower bottoms out at `Fp2 = Fp[u]/(u² + 1)` (`u² = −1`):
an element is `a + b·u` with `a, b ∈ Fp` (each a Montgomery-form 6×u64 limb
bundle). This module emits the **first real owned tower leaf** — the `Fp2`
multiply and square — by *composing* the committed owned base-field kernels:

* `bls12381_mont_mul_x86_from_lean` (#490, the in-Lean x86 CIOS Montgomery
  multiply, MULX + dual ADCX/ADOX) — the verified `Fp` multiply;
* `bls12381_fp_add_x86_from_lean` / `bls12381_fp_sub_x86_from_lean` — the
  six-limb `Fp` add / sub emitted **here** through the same owned backend
  (hardware ADD/ADC + conditional reduce, the `PastaFieldAddSubKernel` idiom
  widened from four to six limbs, with the trial difference staged into a small
  stack scratch frame so the body stays inside the 14-GP pool).

This **replaces the structural stub** flagged by the RELIC bench
(`bench/relic_compare`, README §"Owned kernels"): the prior BN254/BLS `Fp2_mul`
emit was a skeleton (0–1 multiply instructions, undefined leaf labels) and the
jasminc reg-ptr tower hit jasminc's register-allocator wall (#241) on the
pairing wrappers. The owned `Fp2` driver below carries **three real
`Fp`-multiply calls** plus `Fp` add/sub, with the Karatsuba live values
(`t0=ac`, `t1=bd`, `t2=(a+b)(c+d)`) held in a caller-owned stack frame rather
than fought through a fixed register file — the owned frame-spilling discipline
clears the #241 wall the jasminc path hit.

## The `Fp2` multiply (Karatsuba, 3 `Fp`-muls)

For `x = a + b·u`, `y = c + d·u`:

    x·y = (ac − bd) + (ad + bc)·u.

The 3-multiply Karatsuba schedule (the exact call graph the AUCurves Fp2 tower
emits — see `Pairing/Fp2TowerImport.lean`'s `fp2MulExpected`):

    t0 = a·c                       (Fp mul)
    t1 = b·d                       (Fp mul)
    t2 = (a + b)·(c + d)           (Fp add, Fp add, Fp mul)
    re = t0 − t1                   (Fp sub)
    im = t2 − t0 − t1              (Fp sub, Fp sub)

So one `Fp2` mul = **3 `Fp` muls + 2 `Fp` adds + 3 `Fp` subs**.

## The `Fp2` square (2 `Fp`-muls)

For `x = a + b·u`, the complex-squaring identity `u² = −1` gives

    x² = (a² − b²) + 2ab·u = (a − b)·(a + b) + ((a·b) + (a·b))·u,

a **2-multiply** schedule:

    s  = a + b                     (Fp add)
    d  = a − b                     (Fp sub)
    re = s·d                       (Fp mul)  = (a+b)(a−b) = a²−b²
    t  = a·b                       (Fp mul)
    im = t + t                     (Fp add)  = 2ab

So one `Fp2` sqr = **2 `Fp` muls + 2 `Fp` adds + 1 `Fp` sub**.

## What is verified vs trusted (honest scope)

* The `Fp` add / sub **bodies** are `runBlock`-verified through the owned
  backend (`*Block_lowering_correct`, the denotation-preserving lowering), the
  same standard as `Bls12381MontMulKernel.blsMontMulBlock` and the Pasta
  add/sub leaves; their first-fit allocation is overflow-free
  (`*Alloc_no_overflow`). The `Fp` **mul** body is the committed #490 kernel.
* The `Fp2` mul / sqr **driver** is a sequence of `call`s into those verified
  leaves over a stack-frame layout (`re`/`im`/scratch felems). The driver's
  call-and-frame scaffolding is **trusted ABI glue** (it is no longer a leaf —
  it makes calls — so it carries a real `%rsp`-moving frame), exactly the
  status of the `renderLeafFn` prologue/epilogue elsewhere. The *arithmetic* it
  composes is the verified field kernels.
* Value-level correctness — that the emitted driver computes the `Fp2` product
  / square — is the **external KAT** (`bench/bls12381_fp2_compare`, vs RELIC
  `fp2_mul`/`fp2_sqr` and GMP over the same canonical prime), the standard gate
  for these word kernels (per REV-12). This is the `Fp2` **leaf**; the
  `Fp6`/`Fp12`/Miller/final-exp layers above it are the documented follow-on.

## Trust story

Identical to `Bls12381MontMulKernel`: the verified artifact is
`Com (x86Dialect 64) → runBlock → evalInstr` for each `Fp` body; `AsmPrinter` +
`gas` is the syntactic trust boundary; the driver's SysV call frame is trusted
scaffolding outside the verified field bodies.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381MontMulKernel (pLimbs)

/-! ## 1. The six-limb `Fp` add body (`a + b mod p`)

`a` words are loaded from `[a + 8j]`, `b` from `[b + 8j]` (`j = 0..5`). The
inputs are canonical residues (`< p`), so `a + b < 2p < 2^382 < 2^384`, and a
single conditional subtract of `p` reduces. The carry-add lands the seven-word
sum in `t0..t6`; the trial difference `t − p` is staged into the stack scratch
frame `sp[0..5]` (rather than a second six-register set) so the body stays
inside the 14-GP pool — the same scratch-frame recovery
`Bls12381MontMulKernel.blsFinalReduce` uses for the CIOS final subtract. -/

/-- The six-limb `Fp` add over the BLS12-381 modulus. Register names:
    `a`/`b`/`z` operand/result pointers, `sp` the scratch-frame base; `t0..t6`
    the sum window; `lo`/`hi` stage the loaded `b[j]` and the `p[j]` immediates;
    the trial words `t − p` live in `sp[0..5]`. -/
def fpAddBlock : List (JInstr 64) :=
  -- t := a + b  (seven-word, hardware carry chain; top carry in t6)
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .add "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .adc "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .adc "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .adc "t3" (.reg "hi")
  , .loadMem "t4" "a" 32, .loadMem "hi" "b" 32, .adc "t4" (.reg "hi")
  , .loadMem "t5" "a" 40, .loadMem "hi" "b" 40, .adc "t5" (.reg "hi")
  , .mov "t6" (.imm 0), .adc "t6" (.imm 0)
  -- trial := t − p ; CF = final borrow = 1 iff t < p ; stage to sp[0..5]
  , .mov "lo" (.reg "t0"), .mov "hi" (.imm (pLimbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.reg "t1"), .mov "hi" (.imm (pLimbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.reg "t2"), .mov "hi" (.imm (pLimbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.reg "t3"), .mov "hi" (.imm (pLimbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 24 (.reg "lo")
  , .mov "lo" (.reg "t4"), .mov "hi" (.imm (pLimbs[4]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 32 (.reg "lo")
  , .mov "lo" (.reg "t5"), .mov "hi" (.imm (pLimbs[5]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" 40 (.reg "lo")
  , .sbb "t6" (.imm 0)   -- top word; CF = 1 ⇒ t < p ⇒ keep originals
  -- select: load trial into hi, cmovb original (tj) over it when CF=1, store to z.
  , .loadMem "hi" "sp" 0,  .cmovb "hi" (.reg "t0"), .storeMem "z" 0  (.reg "hi")
  , .loadMem "hi" "sp" 8,  .cmovb "hi" (.reg "t1"), .storeMem "z" 8  (.reg "hi")
  , .loadMem "hi" "sp" 16, .cmovb "hi" (.reg "t2"), .storeMem "z" 16 (.reg "hi")
  , .loadMem "hi" "sp" 24, .cmovb "hi" (.reg "t3"), .storeMem "z" 24 (.reg "hi")
  , .loadMem "hi" "sp" 32, .cmovb "hi" (.reg "t4"), .storeMem "z" 32 (.reg "hi")
  , .loadMem "hi" "sp" 40, .cmovb "hi" (.reg "t5"), .storeMem "z" 40 (.reg "hi") ]

/-! ## 2. The six-limb `Fp` sub body (`a − b mod p`)

The borrow-subtract `a − b` sets `CF = 1` iff `a < b` (the difference is
negative). The mask `m = 0 − CF` (`sbb m, m`) is all-ones in that case; the
masked modulus `m & p` is added back with a hardware ADD/ADC chain — a single
conditional add of `p` (sufficient since `a, b ∈ [0, p)`). The six masked
modulus words are staged through the scratch frame so only one `q` register is
live at a time, keeping the body inside the pool. -/

/-- The six-limb `Fp` sub over the BLS12-381 modulus. Register names:
    `a`/`b`/`z` pointers, `sp` scratch base; `t0..t5` the difference; `m` the
    borrow mask; `lo`/`hi` stage operands and the `p[j] & m` masked words (held
    in `sp[0..5]`). The masked words are materialised **before** the ADD/ADC
    chain (the `and` clobbers CF), the same discipline as the Pasta sub. -/
def fpSubBlock : List (JInstr 64) :=
  -- t := a − b  (hardware borrow chain); CF = 1 iff a < b
  [ .loadMem "t0" "a" 0,  .loadMem "hi" "b" 0,  .sub "t0" (.reg "hi")
  , .loadMem "t1" "a" 8,  .loadMem "hi" "b" 8,  .sbb "t1" (.reg "hi")
  , .loadMem "t2" "a" 16, .loadMem "hi" "b" 16, .sbb "t2" (.reg "hi")
  , .loadMem "t3" "a" 24, .loadMem "hi" "b" 24, .sbb "t3" (.reg "hi")
  , .loadMem "t4" "a" 32, .loadMem "hi" "b" 32, .sbb "t4" (.reg "hi")
  , .loadMem "t5" "a" 40, .loadMem "hi" "b" 40, .sbb "t5" (.reg "hi")
  -- m := 0 − CF  (all-ones iff borrow)
  , .mov "m" (.imm 0), .sbb "m" (.imm 0)
  -- precompute the six masked modulus words qj = m & p[j] into sp (these clobber CF)
  , .mov "lo" (.imm (pLimbs[0]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 0  (.reg "lo")
  , .mov "lo" (.imm (pLimbs[1]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 8  (.reg "lo")
  , .mov "lo" (.imm (pLimbs[2]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 16 (.reg "lo")
  , .mov "lo" (.imm (pLimbs[3]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 24 (.reg "lo")
  , .mov "lo" (.imm (pLimbs[4]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 32 (.reg "lo")
  , .mov "lo" (.imm (pLimbs[5]!)), .and_ "lo" (.reg "m"), .storeMem "sp" 40 (.reg "lo")
  -- uninterrupted ADD/ADC chain: t += (m & p), reloading each masked word
  , .loadMem "hi" "sp" 0,  .add "t0" (.reg "hi")
  , .loadMem "hi" "sp" 8,  .adc "t1" (.reg "hi")
  , .loadMem "hi" "sp" 16, .adc "t2" (.reg "hi")
  , .loadMem "hi" "sp" 24, .adc "t3" (.reg "hi")
  , .loadMem "hi" "sp" 32, .adc "t4" (.reg "hi")
  , .loadMem "hi" "sp" 40, .adc "t5" (.reg "hi")
  -- store six words to z
  , .storeMem "z" 0  (.reg "t0"), .storeMem "z" 8  (.reg "t1")
  , .storeMem "z" 16 (.reg "t2"), .storeMem "z" 24 (.reg "t3")
  , .storeMem "z" 32 (.reg "t4"), .storeMem "z" 40 (.reg "t5") ]

/-! ## 3. The initial machine state (reg-ptr ABI) for the add/sub bodies -/

/-- Build the init state from the twelve operand limbs (`a` at `[a+8j]`, `b` at
    `[b+8j]`). The scratch frame `sp` starts zeroed. -/
def initState (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "a" then
        if off = 0 then a0 else if off = 8 then a1 else if off = 16 then a2
        else if off = 24 then a3 else if off = 32 then a4 else if off = 40 then a5
        else 0
      else if base = "b" then
        if off = 0 then b0 else if off = 8 then b1 else if off = 16 then b2
        else if off = 24 then b3 else if off = 32 then b4 else if off = 40 then b5
        else 0
      else 0 }

/-! ## 4. Lowering correctness (denotation = `runBlock`) for the `Fp` bodies -/

/-- **Lowering correctness on the `Fp` add block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on
    the source block — the owned backend's straight-line lowering is
    denotation-preserving across the `loadMem`/`mov`/`add`/`adc`/`sub`/`sbb`/
    `cmovb`/`storeMem` mix. -/
theorem fpAddBlock_lowering_correct
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : BitVec 64) :
    (lowerBlock (Γ := []) fpAddBlock).denote
        (.cons (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) .nil)
      = runBlock (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) fpAddBlock :=
  lowerBlock_denote_closed fpAddBlock
    (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)

/-- **Lowering correctness on the `Fp` sub block.** -/
theorem fpSubBlock_lowering_correct
    (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : BitVec 64) :
    (lowerBlock (Γ := []) fpSubBlock).denote
        (.cons (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) .nil)
      = runBlock (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) fpSubBlock :=
  lowerBlock_denote_closed fpSubBlock
    (initState a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)

/-! ## 5. Register allocation for the `Fp` bodies (reg-ptr ABI + scratch frame)

`z`→`%rdi`, `a`→`%rsi`, `b`→`%rdx` (the SysV argument registers); the scratch
base `sp`→`%rbp` (excluded from `gpPool`, so it costs no pool slot — the same
recovery `Bls12381MontMulKernel` and `P384FieldKernel` use). No `MULX`, so
`%rdx` is free for the `b` pointer. -/

/-- Pin the three buffer pointers to the SysV argument registers + scratch base. -/
def fpAddSubPinned : GpAlloc :=
  [("z", "%rdi"), ("a", "%rsi"), ("b", "%rdx"), ("sp", "%rbp")]

/-- The `Fp` add allocation maps every name to a distinct pool register (no
    silent `%rax`-alias, the #380 class). -/
theorem fpAddAlloc_no_overflow :
    allocOverflow fpAddSubPinned fpAddBlock = none := by native_decide

/-- The `Fp` sub allocation maps every name to a distinct pool register. -/
theorem fpSubAlloc_no_overflow :
    allocOverflow fpAddSubPinned fpSubBlock = none := by native_decide

/-! ## 6. AT&T emission of the `Fp` add/sub leaves (reg-ptr SysV ABI + frame)

The leaves carry a 48-byte scratch frame (`sp`→`%rbp`); the body is
`runBlock`-verified, the prologue/epilogue + frame are trusted ABI
scaffolding. -/

/-- Render one `Fp` add/sub leaf with a 48-byte scratch frame. -/
def renderFpAddSub (name : String) (block : List (JInstr 64)) : String :=
  let alloc := allocGp fpAddSubPinned block
  renderLeafFn name
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $48, %rsp", "\tmovq %rsp, %rbp" ]
    (renderBlockBody alloc block)
    [ "\taddq $48, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- The emitted `Fp` add leaf `bls12381_fp_add_x86_from_lean(z, a, b)`. -/
def fpAddAsm : String := renderFpAddSub "bls12381_fp_add_x86_from_lean" fpAddBlock

/-- The emitted `Fp` sub leaf `bls12381_fp_sub_x86_from_lean(z, a, b)`. -/
def fpSubAsm : String := renderFpAddSub "bls12381_fp_sub_x86_from_lean" fpSubBlock

/-! ## 7. The `Fp2` mul / sqr drivers (trusted call-frame scaffolding)

The drivers are **not** leaves — they call the verified `Fp` mul/add/sub
leaves — so they carry a real `%rsp`-moving frame. The frame holds the
Karatsuba scratch felems (`Fp` is 48 bytes = 6×u64; the frame is 48-byte
aligned). The pointer arguments arrive `z`→`%rdi`, `x`→`%rsi`, `y`→`%rdx`; the
real/imag halves of an `Fp2` are at byte offsets `0` and `48` of each base. The
calls follow the SysV ABI (args in `%rdi/%rsi/%rdx`), and the live operand
pointers are recomputed into the arg registers before each `call` via `lea`
from the saved bases (held in callee-saved registers across the calls).

This is the owned **frame-spilling** discipline: the Karatsuba live values
`t0=ac`, `t1=bd`, `t2=(a+b)(c+d)` are caller-owned stack felems, not values
fought through a fixed register file — which is exactly what blew jasminc's
register allocator (#241) on the pairing wrappers. -/

/-- Helper: emit a `call leaf(z=zoff(%rbx), x=xoff(%r12), y=yoff(%r13))`,
    where `%rbx`/`%r12`/`%r13` hold the saved `z`/`x`/`y` bases (and the
    frame `%rbp` holds the scratch felems at `vN` offsets). The destination
    and the two source pointers are formed with `leaq off(%base), %argreg`. -/
def callFp (leaf : String) (zb : String) (zoff : Int)
    (xb : String) (xoff : Int) (yb : String) (yoff : Int) : List String :=
  [ "\tleaq " ++ toString zoff ++ "(" ++ zb ++ "), %rdi"
  , "\tleaq " ++ toString xoff ++ "(" ++ xb ++ "), %rsi"
  , "\tleaq " ++ toString yoff ++ "(" ++ yb ++ "), %rdx"
  , "\tcallq " ++ leaf ]

/-- Frame layout: three scratch `Fp` felems v0,v1,v2 at `%rbp` offsets
    `0, 48, 96` (48 bytes each). Total frame = 144 bytes, kept 16-aligned by
    rounding to 160. The saved bases live in callee-saved `%rbx`(z),
    `%r12`(x), `%r13`(y). -/
def V0 : Int := 0
def V1 : Int := 48
def V2 : Int := 96

/-- The `Fp2` multiply driver `bls12381_fp2_mul_x86_from_lean(z, x, y)`.

    `x = a + b·u` is `[x+0]` (a) and `[x+48]` (b); likewise `y = c + d·u`.
    Karatsuba (`t0=v0=ac`, `t1=v1=bd`, `t2=v2=(a+b)(c+d)`):

        v0 = a·c                              (fp_mul)
        v1 = b·d                              (fp_mul)
        z.re = a + b   (staged into z.re)     (fp_add)
        z.im = c + d   (staged into z.im)     (fp_add)
        v2 = z.re · z.im = (a+b)(c+d)         (fp_mul)
        z.re = v0 − v1                        (fp_sub)   = ac − bd
        v2 = v2 − v0                          (fp_sub)
        z.im = v2 − v1                        (fp_sub)   = (a+b)(c+d) − ac − bd = ad+bc

    Staging `a+b` / `c+d` into the output halves before the third mul matches
    the AUCurves `fp2MulExpected` schedule and keeps the scratch frame to three
    felems. The output `z` must not alias `x`/`y` (the standard `fp2_mul`
    contract); RELIC's `fp2_mul` is likewise non-aliasing for distinct buffers. -/
def fp2MulAsm : String :=
  renderLeafFn "bls12381_fp2_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $152, %rsp", "\tmovq %rsp, %rbp"   -- 152 = 16-aligned at call (≡8 mod16 entry + 6 pushes + 152)
    , "\tmovq %rdi, %rbx"          -- save z base
    , "\tmovq %rsi, %r12"          -- save x base
    , "\tmovq %rdx, %r13" ]        -- save y base
    ( callFp "bls12381_mont_mul_x86_from_lean" "%rbp" V0 "%r12" 0  "%r13" 0      -- v0 = a*c
    ++ callFp "bls12381_mont_mul_x86_from_lean" "%rbp" V1 "%r12" 48 "%r13" 48    -- v1 = b*d
    ++ callFp "bls12381_fp_add_x86_from_lean"   "%rbx" 0  "%r12" 0  "%r12" 48    -- z.re = a+b
    ++ callFp "bls12381_fp_add_x86_from_lean"   "%rbx" 48 "%r13" 0  "%r13" 48    -- z.im = c+d
    ++ callFp "bls12381_mont_mul_x86_from_lean" "%rbp" V2 "%rbx" 0  "%rbx" 48    -- v2 = (a+b)(c+d)
    ++ callFp "bls12381_fp_sub_x86_from_lean"   "%rbx" 0  "%rbp" V0 "%rbp" V1    -- z.re = v0-v1
    ++ callFp "bls12381_fp_sub_x86_from_lean"   "%rbp" V2 "%rbp" V2 "%rbp" V0    -- v2 = v2-v0
    ++ callFp "bls12381_fp_sub_x86_from_lean"   "%rbx" 48 "%rbp" V2 "%rbp" V1 )  -- z.im = v2-v1
    [ "\taddq $152, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- The `Fp2` square driver `bls12381_fp2_sqr_x86_from_lean(z, x)`.

    `x = a + b·u`, `x² = (a²−b²) + 2ab·u`. The 2-multiply schedule (`u² = −1`):

        v0 = a + b   (staged into z.re)       (fp_add)
        v1 = a − b   (staged into v1)         (fp_sub)
        z.re = z.re · v1 = (a+b)(a−b)         (fp_mul)   = a²−b²
        v2 = a · b                            (fp_mul)
        z.im = v2 + v2                        (fp_add)   = 2ab

    Only `x` is read (`y` argument absent); the second SysV arg `%rsi` is the
    `x` base. -/
def fp2SqrAsm : String :=
  renderLeafFn "bls12381_fp2_sqr_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $152, %rsp", "\tmovq %rsp, %rbp"   -- 152 = 16-aligned at call
    , "\tmovq %rdi, %rbx"          -- save z base
    , "\tmovq %rsi, %r12" ]        -- save x base
    ( callFp "bls12381_fp_add_x86_from_lean"   "%rbx" 0  "%r12" 0  "%r12" 48    -- z.re = a+b
    ++ callFp "bls12381_fp_sub_x86_from_lean"   "%rbp" V1 "%r12" 0  "%r12" 48    -- v1 = a-b
    ++ callFp "bls12381_mont_mul_x86_from_lean" "%rbx" 0  "%rbx" 0  "%rbp" V1    -- z.re = (a+b)(a-b)
    ++ callFp "bls12381_mont_mul_x86_from_lean" "%rbp" V2 "%r12" 0  "%r12" 48    -- v2 = a*b
    ++ callFp "bls12381_fp_add_x86_from_lean"   "%rbx" 48 "%rbp" V2 "%rbp" V2 )  -- z.im = 2*ab
    [ "\taddq $152, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-! ## 8. Shape checks (real multiply instructions, real calls) -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Count non-overlapping-ish occurrences of `needle` in `hay` (one hit per
    start index). Used to witness "three real `Fp`-mul calls" in the driver. -/
def countSub (hay needle : String) : Nat :=
  (List.range (hay.length + 1)).foldl
    (fun acc i =>
      if needle == String.ofList (hay.toList.drop i |>.take needle.length)
      then acc + 1 else acc) 0

/- Shape: the emitted `Fp` add leaf uses the hardware ADD/ADC chain + `cmovb`
    select (no synthesised-carry `shrq $63`). -/
#guard (hasSub fpAddAsm "addq") && (hasSub fpAddAsm "adcq") && (hasSub fpAddAsm "cmovb") && (hasSub fpAddAsm "(%rdi)") && !(hasSub fpAddAsm "shrq $63")

/- Shape: the emitted `Fp` sub leaf uses the hardware SUB/SBB borrow chain +
    masked ADD/ADC add-back. -/
#guard (hasSub fpSubAsm "subq") && (hasSub fpSubAsm "sbbq") && (hasSub fpSubAsm "adcq") && !(hasSub fpSubAsm "shrq $63")

/-- **The owned `Fp2` mul carries three real `Fp`-multiply calls** (not the 0–1
    multiply-insn stub the RELIC bench flagged): the driver contains exactly
    three `callq bls12381_mont_mul_x86_from_lean` — the three Karatsuba
    `Fp`-muls — plus `Fp` add/sub calls, all to **defined** owned leaves. -/
theorem fp2MulAsm_three_real_muls :
    countSub fp2MulAsm "callq bls12381_mont_mul_x86_from_lean" = 3
      ∧ hasSub fp2MulAsm "callq bls12381_fp_add_x86_from_lean"
      ∧ hasSub fp2MulAsm "callq bls12381_fp_sub_x86_from_lean" := by native_decide

/-- **The owned `Fp2` sqr carries two real `Fp`-multiply calls** (the standard
    2-mul complex-squaring schedule). -/
theorem fp2SqrAsm_two_real_muls :
    countSub fp2SqrAsm "callq bls12381_mont_mul_x86_from_lean" = 2
      ∧ hasSub fp2SqrAsm "callq bls12381_fp_add_x86_from_lean"
      ∧ hasSub fp2SqrAsm "callq bls12381_fp_sub_x86_from_lean" := by native_decide

/-! ## 9. Emit driver -/

/-- Emit driver: write the in-Lean-backend-emitted `Fp` add/sub leaves and the
    `Fp2` mul/sqr drivers for the bench harness. The committed `Fp` mul leaf
    (`bls12381_mont_mul_x86_from_lean.s`, #490) is referenced read-only by the
    harness and is **not** re-emitted here. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_fp2_compare/gen_com"
  IO.FS.writeFile
    "bench/bls12381_fp2_compare/gen_com/bls12381_fp_add_x86_from_lean.s" fpAddAsm
  IO.FS.writeFile
    "bench/bls12381_fp2_compare/gen_com/bls12381_fp_sub_x86_from_lean.s" fpSubAsm
  IO.FS.writeFile
    "bench/bls12381_fp2_compare/gen_com/bls12381_fp2_mul_x86_from_lean.s" fp2MulAsm
  IO.FS.writeFile
    "bench/bls12381_fp2_compare/gen_com/bls12381_fp2_sqr_x86_from_lean.s" fp2SqrAsm
  IO.println "wrote gen_com/bls12381_fp_{add,sub}_x86_from_lean.s + bls12381_fp2_{mul,sqr}_x86_from_lean.s (owned x86 backend, Fp2 over verified Fp leaves)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bls12381Fp2MulKernel
