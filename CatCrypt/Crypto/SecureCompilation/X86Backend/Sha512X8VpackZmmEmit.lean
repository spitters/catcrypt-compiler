/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
public import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool

/-!
# SHA-512 8-way σ/Σ lane kernel migrated onto the unified `Com jasminDialect` (512-bit ZMM)

The committed SHA-512 8-way multi-buffer emit (`Sha512X8Emit`,
`bench/sha2_compare/sha512_x8_emit.lean`) packs **eight** independent SHA-512
streams across the eight `u64` lanes of a 512-bit ZMM register and runs the
80-round FIPS 180-4 §6.4 compression lane-parallel. Its body is a `ZOp` block over
the bespoke AVX-512 register machine (`Avx512Model.ZInstr` / `runZBlock`), lowered
by `Avx512Lowering.lowerZBlock` and printed by `Avx512AsmPrinter.renderZInstr`.

This module is the **SIMD-dialect-unification** twin of the kernel's
σ/Σ-mixing core — the σ0 (small sigma 0) lane function, the canonical
rotate-recombination building block that `Sha512X8Emit.protrZ` / `psigmaZ`
assemble — re-expressed as a straight-line `Com jasminDialect` program over
`reg 512` (ZMM) registers, **off** the bespoke `Avx512Model` machine, rendered
through `VpackZmmAsmPrint.renderVpackZmmCom` + `VsimdAsmPrint.frameAsmFunction`.

```
sigma0Com  (Com jasminDialect, vpackZMM .shr/.shl/.or/.xor)
        │  XAlloc (caller-supplied: param + SSA-result → %zmm)
        ▼  VpackZmmAsmPrint.renderVpackZmmCom
   List String  (owned AT&T %zmm body lines)
        │  VsimdAsmPrint.frameAsmFunction  (SysV ABI load/store glue)
        ▼
   String        (a complete owned `.s`, symbol `sha512_x8_sigma0`)
```

The import set is exactly `VpackZmmAsmPrint` (→ `JasminPrint`/`JasminDialect`, the
de-Bruijn→name walk + the `%zmm` operand renderer; `VsimdAsmPrint`'s `XAlloc` /
`frameAsmFunction` reused transitively). The bespoke `Avx512Model`
(`ZInstr`/`ZState`/`runZBlock`), `Avx512Lowering`, and `Avx512AsmPrinter` are
**not** in the lowering or printing path — this is the no-jasminc,
no-`Avx512Model` route.

## What σ0 is (FIPS 180-4 §4.1.3)

`σ0(x) = rotr(x, 1) ^ rotr(x, 8) ^ shr(x, 7)`, packed over all 8 lanes — exactly
`Sha512X8Emit.psigmaZ` instantiated at `smallSig0 = (1, 8, 7)` with
`r3IsShr = true`. The two rotates expand to `protrZ`:
`rotr(x, n) = (x >>> n) ||| (x <<< (64 - n))`.

## Op mapping (this is the migration's substance)

`Sha512X8Emit` uses xor/or plus **immediate** shifts for the σ/Σ rotates.
The unified `vpackZMM .shl` / `.shr` render to the **variable** per-lane shifts
`vpsllvq` / `vpsrlvq` (each lane's shift count read from the second register's
lane), not the immediate-count `vpsllq` / `vpsrlq`. The migration expresses each
immediate shift-by-`n` as a `vpackZMM .shl` / `.shr` whose **second operand is a
broadcast-constant register** holding `n` in every 64-bit lane:

| `Sha512X8Emit.ZOp`      | `Com jasminDialect` op                | denote               |
|------------------------------|---------------------------------------|----------------------|
| `.xor d a b`                 | `vpackZMM .xor` (vpxorq)               | `zmmPackQ .xor a b`  |
| `.or  d a b`                 | `vpackZMM .or`  (vporq)                | `zmmPackQ .or  a b`  |
| `.shr d x n` (immediate)     | `vpackZMM .shr x cₙ`  (vpsrlvq)        | `zmmPackQ .shr x cₙ` |
| `.shl d x (64-n)` (immediate)| `vpackZMM .shl x c₆₄₋ₙ` (vpsllvq)      | `zmmPackQ .shl x c₆₄₋ₙ` |

`zmmPackQ .shr x cₙ` shifts lane `k` of `x` right by `(cₙ.qword[k]).toNat`. When
`cₙ` is the broadcast constant `n` in every lane, this is **lane-uniform
shift-by-`n`** — functionally identical to the immediate `.shr x n`
(`variable-shift-by-a-constant = immediate-shift`). The shift counts are threaded
as **extra context registers** (broadcast `.rodata` constants), one per distinct
amount used by σ0: `n ∈ {1, 63, 8, 56, 7}`. In the emitted `.s` these are loaded
once by the prologue (`vpbroadcastq` of a `.quad n`), exactly the broadcast-shift
idiom already used for the SHA dword schedule.

`rotr(x, n) = (x >>> n) ||| (x <<< (64-n))` becomes two broadcast-shifts plus a
`vpackZMM .or`. Every op of σ0 has a `vpackZMM` equivalent under this idiom, so
the migration is complete (no out-of-fragment op — no immediate-count `vpsllq`
needed, no cross-lane permute).

The **value** correctness (each ZMM lane = scalar SHA-512 σ0) is established by
the external C KAT harness (`bench/sha2_compare/sha512_x8_kat.c`, eight
independent messages, each lane's digest compared against a reference SHA-512),
NOT by an in-kernel multi-vector `native_decide`. This module pins the
`Com` denotation against `zmmPackQ` (`sigma0Com_denote`).

The rendered text of the kernel (the nine body lines, the export label, the
packed mnemonics, the `%zmm` registers, the `.rodata` shift-count label and the
absence of jasmin intrinsics) is checked by the compiled program
`JasminLprogShapeKat` (`sha512Sigma0TextChecks`), not at elaboration:

```
lake exe jasmin-lprog-shape-kat
```

Invoke the emitter:
`lake build CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8VpackZmmEmit`
or `lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/Sha512X8VpackZmmEmit.lean`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8VpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.RodataPool (Pool quadsAt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)

/-! ## 1. Register types and the σ0 input context

A `reg 512` (one ZMM 8×u64 lane-vector) is the working type. σ0 has **one** data
input `x` plus the broadcast shift-count constants threaded as extra context
registers (each a ZMM holding the count `n` in every 64-bit lane). σ0 uses the
amounts `{1, 63, 8, 56, 7}` (rotr-1 = shr 1 ∥ shl 63; rotr-8 = shr 8 ∥ shl 56;
shr 7). De-Bruijn order of the input context (head = de-Bruijn 0):

```
[ x, c1, c63, c8, c56, c7 ]
   0   1    2   3    4    5
```
-/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- σ0's input context: the data word `x` plus the five broadcast shift-count
    constants `c1, c63, c8, c56, c7` (each `reg 512`). -/
abbrev sigma0Ctx : Ctxt jasminDialect := [r512, r512, r512, r512, r512, r512]

/-! ## 2. The dialect-native σ0 program `Com jasminDialect`

`σ0(x) = rotr(x,1) ^ rotr(x,8) ^ shr(x,7)`. Straight-line SSA, each binding one
`vpackZMM` op. De-Bruijn indices are tracked against the context, which grows by
one (at the front) per binding. Initial context `[x,c1,c63,c8,c56,c7]`.

```
t1  := vpackZMM shr x c1      -- x >>> 1
t63 := vpackZMM shl x c63     -- x <<< 63
r1  := vpackZMM or  t1 t63    -- rotr(x,1)
t8  := vpackZMM shr x c8      -- x >>> 8
t56 := vpackZMM shl x c56     -- x <<< 56
r8  := vpackZMM or  t8 t56    -- rotr(x,8)
s7  := vpackZMM shr x c7      -- x >>> 7
m   := vpackZMM xor r1 r8     -- rotr(x,1) ^ rotr(x,8)
out := vpackZMM xor m  s7     -- σ0(x)
ret out
```
-/

/-- The migrated SHA-512 σ0 lane kernel as a `Com jasminDialect` over `reg 512`
    registers — the dialect-native equivalent of `Sha512X8Emit.psigmaZ` at
    `smallSig0 = (1,8,7)`, `r3IsShr = true`. Every immediate shift is a
    `vpackZMM .shl/.shr` against a broadcast shift-count constant (de-Bruijn
    indices below are tracked against the growing context). -/
def sigma0Com : Com jasminDialect sigma0Ctx r512 :=
  -- t1 := x >>> 1   ; ctx [x,c1,c63,c8,c56,c7] → x=0, c1=1
  .var (.mk (.vpackZMM .shr) rfl
          (.cons .here (.cons (.there .here) .nil)))
  -- ctx [t1,x,c1,c63,c8,c56,c7]
  -- t63 := x <<< 63 ; x=1, c63=3
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there .here)
            (.cons (.there (.there (.there .here))) .nil)))
  -- ctx [t63,t1,x,c1,c63,c8,c56,c7]
  -- r1 := t1 ||| t63 ; t1=1, t63=0
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- ctx [r1,t63,t1,x,c1,c63,c8,c56,c7]
  -- t8 := x >>> 8 ; x=3, c8=6
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there .here)))
            (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- ctx [t8,r1,t63,t1,x,c1,c63,c8,c56,c7]
  -- t56 := x <<< 56 ; x=4, c56=8
  (.var (.mk (.vpackZMM .shl) rfl
          (.cons (.there (.there (.there (.there .here))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
              .nil)))
  -- ctx [t56,t8,r1,t63,t1,x,c1,c63,c8,c56,c7]
  -- r8 := t8 ||| t56 ; t8=1, t56=0
  (.var (.mk (.vpackZMM .or) rfl
          (.cons (.there .here) (.cons .here .nil)))
  -- ctx [r8,t56,t8,r1,t63,t1,x,c1,c63,c8,c56,c7]
  -- s7 := x >>> 7 ; x=6, c7=11
  (.var (.mk (.vpackZMM .shr) rfl
          (.cons (.there (.there (.there (.there (.there (.there .here))))))
            (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
              .nil)))
  -- ctx [s7,r8,t56,t8,r1,t63,t1,x,…]
  -- m := r1 ^^^ r8 ; r1=4, r8=1
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons (.there (.there (.there (.there .here)))) (.cons (.there .here) .nil)))
  -- ctx [m,s7,r8,t56,t8,r1,t63,t1,x,…]
  -- out := m ^^^ s7 ; m=0, s7=1
  (.var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)))))))))

/-! ## 3. Denotation characterization

`sigma0Com` computes `σ0(x)` as the verified-dialect packed lane ops, with
`zmmPackQ` the 8×u64 packed-lane semantics. The proof is `rfl`: `Com.denote` of
the straight-line program unfolds definitionally through the `vpackZMM` denote
arm to the nine `zmmPackQ` calls. With the shift-count registers `c1…c7` bound to
the broadcast constants `1,63,8,56,7`, this is the lane-uniform
`rotr(x,1) ^ rotr(x,8) ^ (x >>> 7)`. -/

-- `zmmPackQ` is held irreducible so the defeq check unfolds only `Com.denote` and
-- matches the nine `zmmPackQ` applications syntactically.
attribute [local irreducible] zmmPackQ in
/-- **σ0 denotation pin.** On input valuation `⟨x, c1, c63, c8, c56, c7⟩`,
    `sigma0Com` denotes to the verified-dialect packed
    `(rotr-by-c1 ⊕ rotr-by-c8) ⊕ shr-by-c7`, written out via `zmmPackQ`. Binding
    the shift-count registers to the broadcast constants `1,63,8,56,7` makes this
    exactly the scalar SHA-512 σ0 on every lane — the value the bespoke
    `psigmaZ smallSig0` block writes lane-by-lane. -/
theorem sigma0Com_denote (x c1 c63 c8 c56 c7 : BitVec 512) :
    sigma0Com.denote
        (.cons x (.cons c1 (.cons c63 (.cons c8 (.cons c56 (.cons c7 .nil))))))
      = zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or (zmmPackQ .shr x c1) (zmmPackQ .shl x c63))
            (zmmPackQ .or (zmmPackQ .shr x c8) (zmmPackQ .shl x c56)))
          (zmmPackQ .shr x c7) :=
  rfl

/-! ## 4. The owned `.s`, parametric over the caller-supplied `XAlloc`

`emitSigma0` renders the migrated `Com` body via `renderVpackZmmCom` and frames it
with the SysV-ABI glue under the owned export symbol `sha512_x8_sigma0`. The data
input `x` is loaded from `(%rdi)`; the five broadcast shift-count constants are
loaded once (from `.rodata`) into their pinned registers by the prologue; the
8-lane result stores to `(%rdi)`. -/

/-- The five shift counts of σ0, in the order of the context registers `%zmm1..5`. -/
def sigma0ShiftCounts : List Nat := [1, 63, 8, 56, 7]

/-- The pool entry of shift count `n`: `n` in each of the eight 64-bit lanes, 64-byte
    aligned for the aligned load `vmovdqa64`. -/
def shiftEntry (n : Nat) : Nat × List Nat := (6, List.replicate 8 n)

/-- The `.rodata` pool of the five shift-count constants. -/
def sigma0Pool : Pool := Pool.ofList ".Lsha512_x8_sigma0" (sigma0ShiftCounts.map shiftEntry)

/-- The label holding shift count `n` in every lane. -/
def shiftCountRef (n : Nat) : String := sigma0Pool.ref (shiftEntry n).1 (shiftEntry n).2

/-- The words at the label of each shift count are `n` in every lane. -/
theorem quadsAt_shiftCountRef (n : Nat) (h : n ∈ sigma0ShiftCounts) :
    quadsAt sigma0Pool.directives (shiftCountRef n) = some (List.replicate 8 n) :=
  Pool.quadsAt_ofList_ref _ _ 6 _ (List.mem_map_of_mem (f := shiftEntry) h)

/-- The `.rodata` section of the shift-count pool. -/
def rodataShiftCounts : String := sigma0Pool.text

/-- The ABI **load** prologue: pull the data word `x` from `(%rdi)` into `%zmm0`,
    and load the five shift-count constants into their pinned ZMM registers
    `%zmm1..%zmm5` (the broadcast-shift idiom). -/
def sigma0AbiLoads : List String :=
  "\tvmovdqu64\t(%rdi), %zmm0" :: sigma0ShiftCounts.zipIdx.map (fun (n, i) =>
    "\tvmovdqa64\t" ++ shiftCountRef n ++ "(%rip), %zmm" ++ toString (i + 1))

/-- The ABI **store** epilogue: write the σ0 result (`%zmm0`) back through the
    output pointer `%rdi`. -/
def sigma0AbiStore : List String := [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The owned `.s` body for `sha512_x8_sigma0` under the caller-supplied `%zmm`
    allocation `alloc`. Renders `sigma0Com`'s nine `vpackZMM` bindings to owned
    `%zmm` AT&T lines and frames them with the SysV-ABI load/store glue.
    No `Avx512Model`, no jasminc. -/
def emitSigma0Body (alloc : XAlloc) : String :=
  frameAsmFunction "sha512_x8_sigma0"
    sigma0AbiLoads (renderVpackZmmCom alloc sigma0Com).1 sigma0AbiStore

/-! ## 5. A concrete allocation + the emitted artifact

The data input `x` (param `p0`) → `%zmm0`; the five shift-count constants
(`p1..p5`) → `%zmm1..%zmm5` (matching the prologue broadcast-loads). The nine SSA
temporaries are packed into the remaining ZMM registers `%zmm6..%zmm15`, with the
σ0 result `v8` placed in `%zmm0` so the ABI store of `%zmm0` writes the output. -/

/-- A concrete `%zmm` allocation for σ0: data `x` → `%zmm0`, shift counts
    `c1..c7` → `%zmm1..%zmm5`, SSA temps → `%zmm6..%zmm15`, result `v8` → `%zmm0`. -/
def sigma0Alloc : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
    ("p4", "%zmm4"), ("p5", "%zmm5"),
    ("v0", "%zmm6"),   -- t1  = x >>> 1
    ("v1", "%zmm7"),   -- t63 = x <<< 63
    ("v2", "%zmm8"),   -- r1  = rotr(x,1)
    ("v3", "%zmm9"),   -- t8  = x >>> 8
    ("v4", "%zmm10"),  -- t56 = x <<< 56
    ("v5", "%zmm11"),  -- r8  = rotr(x,8)
    ("v6", "%zmm12"),  -- s7  = x >>> 7
    ("v7", "%zmm13"),  -- m   = rotr(x,1) ^ rotr(x,8)
    ("v8", "%zmm0") ]  -- out = σ0(x)

/-- The emitted owned `.s` for `sha512_x8_sigma0` (owned AVX-512 ZMM, via `Com`),
    including the `.rodata` broadcast shift-count table. -/
def sha512_x8_sigma0_vpackzmm_asm : String :=
  emitSigma0Body sigma0Alloc ++ "\n" ++ rodataShiftCounts

-- Print the emitted owned `.s` for visual inspection.
-- #eval IO.println sha512_x8_sigma0_vpackzmm_asm

/-! ## 6. Emit driver -/

/-- Write the owned-backend (`Com`-rendered AVX-512 ZMM) σ0 lane-kernel `.s` to
    `bench/sha2_compare/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/sha2_compare/gen_com"
  IO.FS.writeFile "bench/sha2_compare/gen_com/sha512_x8_sigma0.s"
    sha512_x8_sigma0_vpackzmm_asm
  IO.println
    "wrote bench/sha2_compare/gen_com/sha512_x8_sigma0.s (owned Com vpackZMM σ0, 8x u64)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8VpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha512X8VpackZmmEmit in
/-- `lake env lean --run` entry point: emit the owned `Com`-rendered σ0 kernel. -/
private def main : IO Unit := emit
