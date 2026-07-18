/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminEmit
import CatCrypt.Crypto.Jasmin.JasminCT

set_option autoImplicit false

/-!
# 32-bit-limb `mpn_mul_1` kernel (Route (a) of the `USE_GMP=OFF` width fork)

Mirror of `MpnMul1Prototype.lean` at U32 for the scalar-multiplication kernel
`out[] = a[] * b + carry`.  Together with `MpnAddmul132Emit.lean` and
`MpnSubmul132Emit.lean`, this completes the carry-bearing scalar-multiply
trio at the 32-bit limb width that matches Lean's fallback
`mpn_digit = unsigned int`.

The shape mirrors the 64-bit `loopBodyMul` verbatim with width swap:

* limb load is `[:u32 ap + 0]` over a **4-byte** stride (`ap += 4` / `op += 4`,
  vs `8` at u64);
* the full product is `#MULX_32(b, t)` producing a u32 high limb and a u32 low
  limb (the 64-bit version uses `#MULX`; jasminc's 32-bit variant is the
  width-suffixed `#MULX_32` — verified accepted by `jasminc -arch x86-64`);
* the running carry is added via `#ADD_32`;
* the carry recombination `cy = hi + c` is a `u32` register add;
* address/count registers (`op`/`ap`/`n`) stay `u64`; the scalar `b` and all
  limb data (`t`/`hi`/`lo`/`c`/`cy`) are `u32`.

## Emission only — proof reuse is future work

This file provides the U32 `FunDecl` and emits its `.jazz` (verified to compile
with `jasminc -arch x86-64`).  The *correctness* re-proof at U32 — the analogue
of `MpnMul1JasminRefines` over `BitVec 32` limbs — is a separate, larger task
(`BignumExec` is stated at u64; `MpnGenericWidth` / `MpnWidthInstances` exist
to generalize).  Here we only exercise the *emitter's* U32 rendering path and
the jasminc carry-shape acceptance.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnMul132Emit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  The U32 Jasmin `mpn_mul_1` body -/

/-- `reg u32` limb register (the limb data width). -/
def vr32 (s : String) : Var := { vname := s, vtype := .sword .U32 }

/-- `reg u64` address/count register (pointers + `mp_size_t` count). -/
def vr64 (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s` (limb-width view). -/
def pv32 (s : String) : PExpr := .Pvar { gv := { var := vr32 s }, gs := false }

/-- A `Pvar` reading register `s` (address-width view). -/
def pv64 (s : String) : PExpr := .Pvar { gv := { var := vr64 s }, gs := false }

/-- U32 memory load `x := [:u32 base + 0]`.  `base` is a 64-bit pointer. -/
def load32At0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr32 x }) .AT_none (.sword .U32)
    (.Pload .U32 { var := vr64 base } (.Pconst 0))

/-- U32 memory store `[:u32 base + 0] := src`. -/
def store32At0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U32 { var := vr64 base } (.Pconst 0)) .AT_none (.sword .U32)
    (.Pvar { gv := { var := vr32 src }, gs := false })

/-- 64-bit pointer/count update `r += k` / `r -= k`. -/
def ptrImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr64 r }) .AT_none (.sword .U64)
    (.Papp2 op (pv64 r) (.Pconst k))

/-- u32 register add `dst = src1 + src2` (for the `cy = hi + c` recombination). -/
def regAdd32 (dst src1 src2 : String) : InstrR :=
  .Cassgn (.Lvar { var := vr32 dst }) .AT_none (.sword .U32)
    (.Papp2 (.Oadd .U32) (pv32 src1) (pv32 src2))

/-- The 6-LVal `#ADD_32` flag bundle `[_, cf_out, _, _, _, dst]`. -/
def addCopn32 (cfName rName aName bName : String) : InstrR :=
  .Copn ([.Lnone {} (.sword .U32), .Lvar { var := vr32 cfName }]
          ++ List.replicate 3 (.Lnone {} (.sword .U32))
          ++ [.Lvar { var := vr32 rName }])
        .AT_none (.Oasm ⟨"ADD_32"⟩)
        [pv32 aName, pv32 bName]

/-- `hi, lo = #MULX_32(b, t);` — the full 32×32→64 product, 2-LVal bundle
    `[hi, lo]` (`#MULX_32` touches no flags).  jasminc's 32-bit variant of
    `#MULX` is `#MULX_32`; verified by direct compilation. -/
def mulxCopn32 (hiName loName bName tName : String) : InstrR :=
  .Copn [.Lvar { var := vr32 hiName }, .Lvar { var := vr32 loName }]
        .AT_none (.Oasm ⟨"MULX_32"⟩)
        [pv32 bName, pv32 tName]

/-- One U32 loop iteration body for `mpn_mul_1`:
    ```
    t       = [:u32 ap + 0];
    hi, lo  = #MULX_32(b, t);
    _, c, _, _, _, lo = #ADD_32(lo, cy);
    [:u32 op + 0] = lo;
    cy = hi + c;
    ap += 4; op += 4;
    n  -= 1;
    ```
    `cy` is initialised to 0 before the loop; the scalar multiplier sits in
    register `b` and is never advanced.  4-byte stride for the U32 width. -/
def loopBodyMul32 : List InstrR :=
  [ load32At0 "t" "ap"
  , mulxCopn32 "hi" "lo" "b" "t"
  , addCopn32 "c" "lo" "lo" "cy"
  , store32At0 "op" "lo"
  , regAdd32 "cy" "hi" "c"
  , ptrImm "ap" (.Oadd .U64) 4
  , ptrImm "op" (.Oadd .U64) 4
  , ptrImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_mul_1` at U32:
    ```
    cy = 0;
    while (n != 0) { <loopBodyMul32> }
    ```
    `cy` holds the final carry (the GMP `mpn_mul_1` ABI returns it). -/
def bodyMul32 : List InstrR :=
  [ .Cassgn (.Lvar { var := vr32 "cy" }) .AT_none (.sword .U32) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodyMul32 ]

/-- `mpn_mul_1_32(op, ap, b, n)` as a Jasmin `FunDecl`, **U32 limbs**.
    Symbol `mpn_mul_1_32`.  `op`/`ap`/`n` are `u64`; `b` is `u32`. -/
def mpnMul132Fd : FunDecl where
  name := { name := "mpn_mul_1_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr32 "b" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := bodyMul32
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyMul32 = true := by decide

/-- Emit the real 32-bit `.jazz` source. -/
def emitted32 : Option String := emitFunDecl mpnMul132Fd

#eval match emitted32 with | some s => s | none => "EMIT FAILED"

end CatCrypt.Crypto.Jasmin.Examples.MpnMul132Emit
