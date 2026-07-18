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
# 32-bit-limb `mpn_sub_n` kernel (Route (a) of the `USE_GMP=OFF` width fork)

Mirror of `MpnAdd32Emit.lean` at U32 for **subtraction**.  The verified-pipeline
`mpn_sub_n` is emitted at u64; this file re-emits it at the 32-bit limb width
that matches Lean's fallback `mpn_digit = unsigned int`, so the MIXED
`mpn.cpp` adapter (`bench/lean_mpn_adapter/`) can wire it under the
`lean::mpn_sub` ABI without an `.olean` reformat.

The open-coded-borrow shape is identical to add, with `#SUB_32` in place of
`#ADD_32`: two subtractions per iteration thread a `u32` borrow GPR across the
`while` back-edge (`bf1 | bf2`), which jasminc's register allocator accepts as-is.

* limb loads/stores are `[:u32 base + 0]` over a **4-byte** stride;
* arithmetic is `.Osub .U32` / `.Olor .U32`;
* the threaded borrow register is `u32`;
* address/count registers (`op`/`ap`/`bp`/`n`) stay `u64`.

Emission only — the BitVec 32 correctness re-proof is a separate follow-on
(`BignumExec`'s u32 ops are in place after `cacca611`, so it is now reachable).
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnSub32Emit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  The open-coded U32 Jasmin `mpn_sub_n` body -/

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

/-- The 6-LVal `#SUB_32` flag bundle `[_, bf_out, _, _, _, dst]` capturing the
    borrow-out into u32 register `bfName` and the difference into u32 register
    `rName`. -/
def subCopn32 (bfName rName aName bName : String) : InstrR :=
  .Copn ([.Lnone {} (.sword .U32), .Lvar { var := vr32 bfName }]
          ++ List.replicate 3 (.Lnone {} (.sword .U32))
          ++ [.Lvar { var := vr32 rName }])
        .AT_none (.Oasm ⟨"SUB_32"⟩)
        [pv32 aName, pv32 bName]

/-- One open-coded U32 loop iteration:
    ```
    t  = [:u32 ap + 0];
    s  = [:u32 bp + 0];
    _, bf1, _, _, _, r0 = #SUB_32(t, s);     // first borrow
    _, bf2, _, _, _, r  = #SUB_32(r0, cf);   // borrow-in via cf
    cf = bf1 | bf2;                          // new u32 borrow ∈ {0,1}
    [:u32 op + 0] = r;
    ap += 4; bp += 4; op += 4; n -= 1;
    ```
    `cf`/`bf1`/`bf2`/`t`/`s`/`r0`/`r` are `u32`; `ap`/`bp`/`op`/`n` are `u64`. -/
def loopBody32 : List InstrR :=
  [ load32At0 "t" "ap"
  , load32At0 "s" "bp"
  , subCopn32 "bf1" "r0" "t" "s"
  , subCopn32 "bf2" "r" "r0" "cf"
  , .Cassgn (.Lvar { var := vr32 "cf" }) .AT_none (.sword .U32)
      (.Papp2 (.Olor .U32) (pv32 "bf1") (pv32 "bf2"))
  , store32At0 "op" "r"
  , ptrImm "ap" (.Oadd .U64) 4
  , ptrImm "bp" (.Oadd .U64) 4
  , ptrImm "op" (.Oadd .U64) 4
  , ptrImm "n"  (.Osub .U64) 1 ]

/-- Full U32 body: `cf = 0; while (n != 0) { <loopBody32> }`.  The threaded
    borrow `cf` is a `u32` register; the loop counter `n` is `u64`. -/
def body32 : List InstrR :=
  [ .Cassgn (.Lvar { var := vr32 "cf" }) .AT_none (.sword .U32) (.Pconst 0)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) loopBody32 ]

/-- `mpn_sub_n(op, ap, bp, n)` as a `FunDecl`, open-coded borrow, **U32 limbs**.
    Symbol `mpn_sub_n_oc_32`. -/
def mpnSubN32Fd : FunDecl where
  name := { name := "mpn_sub_n_oc_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr64 "bp" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := body32
  results := []

/-- The U32 loop is constant-time-shaped: the guard depends only on the public
    length `n`. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd body32 = true := by decide

/-- Emit the real 32-bit `.jazz` source. -/
def emitted32 : Option String := emitFunDecl mpnSubN32Fd

#eval match emitted32 with | some s => s | none => "EMIT FAILED"

end CatCrypt.Crypto.Jasmin.Examples.MpnSub32Emit
