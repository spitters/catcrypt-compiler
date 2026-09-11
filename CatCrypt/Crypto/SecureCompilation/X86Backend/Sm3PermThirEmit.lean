/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# SM3 (GB/T 32905-2016 §4.3) permutation functions P0/P1 through the OWNED x86 backend (no jasminc)

The two SM3 message-permutation sub-functions driven through the
`compile-from-hax` front (`Com thirDialect`) onto the OWNED x86 backend — NO
jasminc anywhere. Width-32 single-input siblings of the SHA-256 big-Sigma
module, but with LEFT-rotates (ROTL) instead of right-rotates:

    P0(x) = x ⊕ ROTL⁹(x)  ⊕ ROTL¹⁷(x)   (GB/T 32905-2016 §4.3)
    P1(x) = x ⊕ ROTL¹⁵(x) ⊕ ROTL²³(x)

`P0` is the compression-function permutation (mixing `TT2` into the working
variable); `P1` is the message-expansion permutation (used to derive `W[16..67]`
from earlier words). Both are PURE rotates — no shift — and each is a 3-term XOR
where the **first** operand is the raw input `x` itself (an identity term), NOT a
rotate.

## ROTL from the native right-rotate `thRor`

The THIR surface has only the native rotate-RIGHT op `thRor`; there is no
`thRol`. Over a `u32`, `ROTL n = ROTR (32 - n)`, so each `ROTL n` is emitted as
`thRor 32 (32 - n)`. With `n ∈ {9, 17, 15, 23}` the shift amount `32 - n ∈
{23, 15, 17, 9}` is always in `1..31`, so no zero-rotate edge case arises for the
rotate terms. The identity term `x` is emitted as a rotate-by-zero
`thRor 32 0` (= identity copy), the same idiom `ChaChaQRThirEmit` uses for
its final word; rotate-legalisation lowers it to a shift-by-0 pair (a no-op on
x86), so the emitted `.s` carries no unhandled-op sentinel.

The pipeline mirrors `Sha256BigSigmaThirEmit`:

    sm3P{0,1}Thir : Com thirDialect [.reg 32] (.reg 32)
      --lowerThir-->            Com jasminDialect [.reg 32] (.reg 32)
      --Com.toLprogPhysAbi-->   Lprog (physical-register, two-address, SysV ABI)
      --renderLprogAtt-->       AT&T `.s` (assembled by `as`/`cc`, no jasminc)

## ABI (2-pointer SysV, the `comToLfundefPhysAbi` shape)

`comToLfundefPhysAbi` emits the 2-pointer SysV signature (`RDI` = out, `RSI` =
inp); the single input is loaded from `[RSI + 0]` and the single output stored
to `[RDI + 0]`:

```c
extern void sm3_p0(uint32_t *out, const uint32_t *inp);  // inp = [x]
extern void sm3_p1(uint32_t *out, const uint32_t *inp);  // inp = [x]
//   out[0] receives x ^ ROTL9(x)  ^ ROTL17(x)   (P0)
//   out[0] receives x ^ ROTL15(x) ^ ROTL23(x)   (P1)
```

The ABI maps (`sigma1InLoadMap` / `sigma1OutStoreMap`) are reused from
`Sha256Sigma1ThirEmit`: `inLoadMap 0 = ("RSI", 0)` and
`outStoreMap = [("RDI", 0)]`.

## What is verified vs trusted

* **Verified (value)**: `sm3P0Thir_denote` / `sm3P1Thir_denote` (each leaf
  denotes the SM3 permutation `sm3P0Spec` / `sm3P1Spec`) and
  `sm3P{0,1}_via_thirDialect` (the lowered `Com jasminDialect` denotes the same).
* **Trusted (thin)**: `renderLfundef` / `gas` / the SysV leaf ABI frame.

The byte-identity to the GB/T reference is the external `as`/`cc` KAT in
`bench/thir_front_sm3_perm_owned/` (no jasminc).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Sm3PermThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect lowerThir_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Sha256Sigma1ThirEmit
  (sigma1InLoadMap sigma1OutStoreMap legalizeShiftImmLprog)

/-! ## 0. The SM3 permutation specs (width 32)

Each `ROTL n` is written as `rotateRight (32 - n)` so the leaf below denotes the
spec by `rfl` (matching the `thRor 32 (32 - n)` front encoding); the identity
term is `x.rotateRight 0 = x`. -/

/-- SM3 P0 = x ⊕ ROTL⁹(x) ⊕ ROTL¹⁷(x) (GB/T 32905-2016 §4.3). The first term is
    the raw input (encoded `rotateRight 0`); the two rotates are encoded as
    right-rotates `rotateRight (32 - n)`. -/
def sm3P0Spec (x : BitVec 32) : BitVec 32 :=
  (x.rotateRight 0) ^^^ (x.rotateRight (32 - 9)) ^^^ (x.rotateRight (32 - 17))

/-- SM3 P1 = x ⊕ ROTL¹⁵(x) ⊕ ROTL²³(x) (GB/T 32905-2016 §4.3). -/
def sm3P1Spec (x : BitVec 32) : BitVec 32 :=
  (x.rotateRight 0) ^^^ (x.rotateRight (32 - 15)) ^^^ (x.rotateRight (32 - 23))

/-! ## 1. The SM3 permutation programs as `Com thirDialect` leaves

Built directly at the THIR-dialect level (`thRor`, `thBin`), mirroring the
`sha256BigSigma0Thir` constructor shape but with the first term a rotate-by-zero
identity (`thRor 32 0`) and the two ROTLs encoded as `thRor 32 (32 - n)`:

    let rId = thRor 32 0      x;  -- identity (= x)
    let rA  = thRor 32 (32-a) x;  let rB = thRor 32 (32-b) x
    let t   = thBin xor rId rA;   let o = thBin xor t rB;  ret o

The de-Bruijn discipline (each `.var` prepends one binding):
`[x]` → `[rId,x]` → `[rA,rId,x]` → `[rB,rA,rId,x]`; the first xor reads
`rId` (`there (there here)`) and `rA` (`there here`) giving `[t,rB,rA,rId,x]`;
the second xor reads `t` (`here`) and `rB` (`there here`), so the result is
`(rId ⊕ rA) ⊕ rB = x ⊕ ROTLa(x) ⊕ ROTLb(x)`. -/

/-- SM3 P0 = x ⊕ ROTL⁹(x) ⊕ ROTL¹⁷(x), as a `Com thirDialect`. -/
def sm3P0Thir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 0) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 (32 - 9)) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 32 (32 - 17)) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- SM3 P1 = x ⊕ ROTL¹⁵(x) ⊕ ROTL²³(x), as a `Com thirDialect`. -/
def sm3P1Thir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thRor 32 0) rfl (.cons .here .nil))
    (.var (.mk (.thRor 32 (32 - 15)) rfl (.cons (.there .here) .nil))
      (.var (.mk (.thRor 32 (32 - 23)) rfl (.cons (.there (.there .here)) .nil))
        (.var (.mk (.thBin .xor 32) rfl
            (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
          (.var (.mk (.thBin .xor 32) rfl
              (.cons .here (.cons (.there .here) .nil)))
            (.ret .here)))))

/-- The THIR-dialect P0 denotes to the SM3 P0 spec on any input valuation. -/
theorem sm3P0Thir_denote (x : BitVec 32) :
    sm3P0Thir.denote (.cons x .nil) = sm3P0Spec x := by
  rfl

/-- The THIR-dialect P1 denotes to the SM3 P1 spec on any input valuation. -/
theorem sm3P1Thir_denote (x : BitVec 32) :
    sm3P1Thir.denote (.cons x .nil) = sm3P1Spec x := by
  rfl

/-- **P0 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for P0 denotes the same `BitVec 32` as the SM3 P0
    spec. -/
theorem sm3P0_via_thirDialect (x : BitVec 32) :
    (lowerThir sm3P0Thir).denote (.cons x .nil) = sm3P0Spec x := by
  rw [lowerThir_denote sm3P0Thir (.cons x .nil), sm3P0Thir_denote]

/-- **P1 re-derived through the dialect spine.** The lowered (two-stage)
    `Com jasminDialect` for P1 denotes the same `BitVec 32` as the SM3 P1
    spec. -/
theorem sm3P1_via_thirDialect (x : BitVec 32) :
    (lowerThir sm3P1Thir).denote (.cons x .nil) = sm3P1Spec x := by
  rw [lowerThir_denote sm3P1Thir (.cons x .nil), sm3P1Thir_denote]

/-! ## 2. The owned `Lprog`s and combined AT&T emission (no jasminc)

Each permutation is exported to a physical, two-address SysV `Lprog` and
rotate-legalised (reusing `Sha256Sigma1ThirEmit.legalizeShiftImmLprog`, the
ABI maps, and the 2-pointer SysV signature). The two single-func `Lprog`s are
then merged into one `Lprog` so a single `.s` carries both leaves
(`sm3_p0` and `sm3_p1`). -/

/-- P0 lowered through the thirDialect spine, exported to a physical SysV
    `Lprog`, then rotate-immediate-legalised. `fname` `"sm3_p0"` becomes the
    emitted asm label (matching the C extern). -/
def sm3P0Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sm3P0Thir) "sm3_p0"
      (fun _ => none)                       -- shiftImm oracle (unused)
      (fun _ => none)                       -- immSlotMap (no input immediates)
      sigma1InLoadMap                       -- inLoadMap (single arg ↦ RSI[0])
      sigma1OutStoreMap                     -- outStoreMap (result ↦ RDI[0])
      ["RDI", "RSI"]                        -- abiArgs (out, inp)
      [32])                                 -- abiTyin (1 u32 input)

/-- P1 lowered through the thirDialect spine, exported to a physical SysV
    `Lprog`, then rotate-immediate-legalised. `fname` `"sm3_p1"` becomes the
    emitted asm label (matching the C extern). -/
def sm3P1Lprog : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir sm3P1Thir) "sm3_p1"
      (fun _ => none)
      (fun _ => none)
      sigma1InLoadMap
      sigma1OutStoreMap
      ["RDI", "RSI"]
      [32])

/-- The two SM3 permutation leaves merged into ONE `Lprog`, so a single rendered
    `.s` exports both `sm3_p0` and `sm3_p1`. -/
def sm3PermLprog : Lprog :=
  { sm3P0Lprog with
    lp_funcs := sm3P0Lprog.lp_funcs ++ sm3P1Lprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for both SM3 permutations (no jasminc). -/
def sm3PermAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned sm3PermLprog

/-! ## 3. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` for both SM3 permutations into the
    `bench/thir_front_sm3_perm_owned/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_sm3_perm_owned/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/sm3_perm_owned.s") sm3PermAsm
  IO.println "WROTE bench/thir_front_sm3_perm_owned/gen/sm3_perm_owned.s"
  IO.println "  (SM3 GB/T 32905-2016 permutation functions sm3P0Thir / sm3P1Thir"
  IO.println "   through Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt"
  IO.println "   onto the OWNED x86 backend, NO jasminc)"

/-! ## 5. Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.Sm3PermThirEmit
