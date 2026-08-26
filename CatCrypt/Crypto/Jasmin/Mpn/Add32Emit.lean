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
# 32-bit-limb `mpn_add_n` kernel (Route (a) of the `USE_GMP=OFF` width fork)

The verified-pipeline `mpn_*` kernels are emitted at **64-bit** limb width
(u64), matching real gmp.  The Lean runtime's *fallback* `mpn_digit` is
`unsigned int` = **32-bit** (`src/runtime/mpn.h`, see
`bench/integration/INTEGRATION.md` §4c).  Route (a) of the width fork keeps the
32-bit `mpn_digit` (zero `.olean` reformat cost) and re-emits the kernels at
**32-bit limb width**.

This file is the first such re-emission: the open-coded-carry `mpn_add_n`
(mirror of `Mpn.AddOpenCarryPrototype.mpnAddNFd`) at **U32** limbs.  The shape is
identical — two `#ADD_32` carry bundles plus an `Olor`, threading the carry as
an ordinary GPR value across the `while` back-edge — only the limb width
changes:

* limb loads/stores are `[:u32 base + 0]` over a **4-byte** stride
  (`ap += 4` / `bp += 4` / `op += 4`, vs `8` at u64);
* the arithmetic is `.Oadd .U32` / `.Olor .U32`;
* the threaded carry register is a `u32` GPR.

The **address/count** registers (`op`, `ap`, `bp`, `n`) stay `u64`: pointers
are 64-bit on x86-64 and the count is `mp_size_t`.  So the kernel is
*mixed-width* — the emitter declares `op`/`ap`/`bp`/`n` as `reg u64` and the
limb data registers (`t`/`s`/`r0`/`r`/`cf`/…) as `reg u32`.

## Emission only — proof reuse is future work

This file provides the U32 `FunDecl` and emits its `.jazz` (verified to compile
with `jasminc -arch x86-64`).  The *correctness* re-proof at U32 — the analogue
of `Mpn.AddOpenCarryPrototype.MpnAddOpenCarryRefines` over `BitVec 32` limbs —
is a separate, larger task (`BignumExec` is stated at u64; `MpnGenericWidth` /
`MpnWidthInstances` exist to generalize).  Here we only exercise the *emitter's*
U32 rendering path and the jasminc carry-shape acceptance.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Add32Emit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  The open-coded U32 Jasmin `mpn_add_n` body -/

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

/-- 64-bit pointer/count update `r += k` / `r -= k` (`.Oadd .U64` / `.Osub .U64`). -/
def ptrImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr64 r }) .AT_none (.sword .U64)
    (.Papp2 op (pv64 r) (.Pconst k))

/-- The 6-LVal `#ADD_32` flag bundle `[_, cf_out, _, _, _, dst]` capturing the
    carry-out into u32 register `cfName` and the sum into u32 register `rName`. -/
def addCopn32 (cfName rName aName bName : String) : InstrR :=
  .Copn ([.Lnone {} (.sword .U32), .Lvar { var := vr32 cfName }]
          ++ List.replicate 3 (.Lnone {} (.sword .U32))
          ++ [.Lvar { var := vr32 rName }])
        .AT_none (.Oasm ⟨"ADD_32"⟩)
        [pv32 aName, pv32 bName]

/-- One open-coded U32 loop iteration (mirror of
    `Mpn.AddOpenCarryPrototype.loopBody`, with 4-byte stride):
    ```
    t  = [:u32 ap + 0];
    s  = [:u32 bp + 0];
    _, cf1, _, _, _, r0 = #ADD_32(t, s);     // addCarry t s
    _, cf2, _, _, _, r  = #ADD_32(r0, cf);   // addCarry r0 cf (cf = GPR carry-in)
    cf = cf1 | cf2;                          // Olor: new u32 carry ∈ {0,1}
    [:u32 op + 0] = r;
    ap += 4; bp += 4; op += 4; n -= 1;
    ```
    `cf`/`cf1`/`cf2`/`t`/`s`/`r0`/`r` are `u32`; `ap`/`bp`/`op`/`n` are `u64`. -/
def loopBody32 : List InstrR :=
  [ load32At0 "t" "ap"
  , load32At0 "s" "bp"
  , addCopn32 "cf1" "r0" "t" "s"
  , addCopn32 "cf2" "r" "r0" "cf"
  , .Cassgn (.Lvar { var := vr32 "cf" }) .AT_none (.sword .U32)
      (.Papp2 (.Olor .U32) (pv32 "cf1") (pv32 "cf2"))
  , store32At0 "op" "r"
  , ptrImm "ap" (.Oadd .U64) 4
  , ptrImm "bp" (.Oadd .U64) 4
  , ptrImm "op" (.Oadd .U64) 4
  , ptrImm "n"  (.Osub .U64) 1 ]

/-- Full U32 body: `cf = 0; while (n != 0) { <loopBody32> }`.  The threaded
    carry `cf` is a `u32` register; the loop counter `n` is `u64`. -/
def body32 : List InstrR :=
  [ .Cassgn (.Lvar { var := vr32 "cf" }) .AT_none (.sword .U32) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBody32 ]

/-- `mpn_add_n(op, ap, bp, n)` as a `FunDecl`, open-coded carry, **U32 limbs**.
    Symbol `mpn_add_n_oc_32`. -/
def mpnAddN32Fd : FunDecl where
  name := { name := "mpn_add_n_oc_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr64 "bp" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := body32
  results := []

/-- The U32 loop is constant-time-shaped: the guard depends only on the public
    length `n`. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body32 = true := by decide

/-- Emit the real 32-bit `.jazz` source. -/
def emitted32 : Option String := emitFunDecl mpnAddN32Fd

#eval match emitted32 with | some s => s | none => "EMIT FAILED"

end CatCrypt.Crypto.Jasmin.Mpn.Add32Emit
