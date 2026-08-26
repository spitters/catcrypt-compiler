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
# 32-bit-limb `mpn_addmul_1` kernel (Route (a) of the `USE_GMP=OFF` width fork)

Mirror of `Mpn.Addmul1Prototype.lean` at U32 for the multiply-accumulate
kernel `out[] += a[] * b + carry`.  Companion to `Mpn.Mul132Emit.lean` and
`Mpn.Submul132Emit.lean`.

The shape mirrors the 64-bit `loopBodyAddmul` verbatim with width swap:

* limb loads/stores are `[:u32 base + 0]` over a **4-byte** stride;
* the full product is `#MULX_32(b, t)` (jasminc's width-suffixed `#MULX`);
* the running carry add and the accumulator add are both `#ADD_32`;
* the final carry recombination `cy = hi + c1; cy += c2` uses u32 register
  adds (the strict `cy < 2^32` bound is the U32 analogue of the U64 bound
  `a·b + cy + out ≤ 2^128 − 1` at the smaller width);
* address/count registers (`op`/`ap`/`n`) stay `u64`; the scalar `b` and
  all limb data (`t`/`hi`/`lo`/`w`/`c1`/`c2`/`cy`) are `u32`.

`op` is read (into `w`) before it is stored, realising the multiply-accumulate
just as in the U64 kernel.

## Emission only — proof reuse is future work

Provides the U32 `FunDecl` and emits its `.jazz` (verified to compile with
`jasminc -arch x86-64`).  The U32 correctness re-proof — the analogue of
`MpnAddmul1JasminRefines` over `BitVec 32` limbs — is a separate task.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Addmul132Emit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  The U32 Jasmin `mpn_addmul_1` body -/

/-- `reg u32` limb register. -/
def vr32 (s : String) : Var := { vname := s, vtype := .sword .U32 }

/-- `reg u64` address/count register. -/
def vr64 (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s` (limb-width view). -/
def pv32 (s : String) : PExpr := .Pvar { gv := { var := vr32 s }, gs := false }

/-- A `Pvar` reading register `s` (address-width view). -/
def pv64 (s : String) : PExpr := .Pvar { gv := { var := vr64 s }, gs := false }

/-- U32 memory load `x := [:u32 base + 0]`. -/
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

/-- u32 register add `dst = src1 + src2`. -/
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

/-- `hi, lo = #MULX_32(b, t);` — the full 32×32→64 product. -/
def mulxCopn32 (hiName loName bName tName : String) : InstrR :=
  .Copn [.Lvar { var := vr32 hiName }, .Lvar { var := vr32 loName }]
        .AT_none (.Oasm ⟨"MULX_32"⟩)
        [pv32 bName, pv32 tName]

/-- One U32 loop iteration body for `mpn_addmul_1`:
    ```
    t       = [:u32 ap + 0];
    hi, lo  = #MULX_32(b, t);
    _, c1, _,_,_, lo = #ADD_32(lo, cy);
    w       = [:u32 op + 0];           -- read out[i]
    _, c2, _,_,_, lo = #ADD_32(lo, w);
    [:u32 op + 0] = lo;                -- store accumulated low word
    cy      = hi + c1;
    cy      = cy + c2;
    ap += 4; op += 4;
    n  -= 1;
    ```
    Unlike `loopBodyMul32`, `op` is *read* (into `w`) before it is *stored*,
    realising the multiply-accumulate. -/
def loopBodyAddmul32 : List InstrR :=
  [ load32At0 "t" "ap"
  , mulxCopn32 "hi" "lo" "b" "t"
  , addCopn32 "c1" "lo" "lo" "cy"
  , load32At0 "w" "op"
  , addCopn32 "c2" "lo" "lo" "w"
  , store32At0 "op" "lo"
  , regAdd32 "cy" "hi" "c1"
  , regAdd32 "cy" "cy" "c2"
  , ptrImm "ap" (.Oadd .U64) 4
  , ptrImm "op" (.Oadd .U64) 4
  , ptrImm "n"  (.Osub .U64) 1 ]

/-- Full body of `mpn_addmul_1` at U32:
    ```
    cy = 0;
    while (n != 0) { <loopBodyAddmul32> }
    ```
    `cy` holds the final carry (the GMP `mpn_addmul_1` ABI returns it). -/
def bodyAddmul32 : List InstrR :=
  [ .Cassgn (.Lvar { var := vr32 "cy" }) .AT_none (.sword .U32) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBodyAddmul32 ]

/-- `mpn_addmul_1_32(op, ap, b, n)` as a Jasmin `FunDecl`, **U32 limbs**.
    Symbol `mpn_addmul_1_32`.  `op`/`ap`/`n` are `u64`; `b` is `u32`. -/
def mpnAddmul132Fd : FunDecl where
  name := { name := "mpn_addmul_1_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr32 "b" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := bodyAddmul32
  results := []

/-- Constant-time-*shaped*: the loop guard `n != 0` depends only on the public
    length `n`, never a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd bodyAddmul32 = true := by decide

/-- Emit the real 32-bit `.jazz` source. -/
def emitted32 : Option String := emitFunDecl mpnAddmul132Fd

#eval match emitted32 with | some s => s | none => "EMIT FAILED"

end CatCrypt.Crypto.Jasmin.Mpn.Addmul132Emit
