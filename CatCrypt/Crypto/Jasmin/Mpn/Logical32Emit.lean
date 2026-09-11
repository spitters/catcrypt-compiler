/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminAST
public meta import CatCrypt.Crypto.Jasmin.JasminEmit
public import CatCrypt.Crypto.Jasmin.JasminEmit
public meta import CatCrypt.Crypto.Jasmin.JasminCT
public import CatCrypt.Crypto.Jasmin.JasminCT


@[expose] public section
set_option autoImplicit false

/-!
# 32-bit-limb `mpn_{and,ior,xor}_n` kernels (Route (a) of the width fork)

Mirror of `Mpn.LogicalPrototype.lean` at U32, parallel to `MpnAdd32Emit` /
`MpnSub32Emit`.  These are the simplest of the bounded mpn ops — no carry,
no scalar multiplication: per-limb bitwise op, store, advance.

* limb loads/stores are `[:u32 base + 0]` over a **4-byte** stride;
* arithmetic is `.Oland .U32` / `.Olor .U32` / `.Olxor .U32` (the per-bit
  operations carry over verbatim from u64, since `BitVec.and`/`.or`/`.xor`
  are bit-parallel — same denotation at any width);
* address/count registers (`op`/`ap`/`bp`/`n`) stay `u64`.

Emitted symbols: `mpn_and_n_32`, `mpn_ior_n_32`, `mpn_xor_n_32`.
Each kernel is constant-time-shaped (loop guard on public `n` only).

Emission only — the BitVec 32 correctness re-proof is the follow-on; the
denotation `toNat (mpnAnd a b) = toNat a &&& toNat b` from the u64 prototype
generalizes word-for-word to u32 once the u32 InstrR↔interpreter bridge is
re-derived from `cacca611`'s u32 ops.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Logical32Emit

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Emit

/-! ## §1  U32 helpers (same shape as `MpnAdd32Emit`/`MpnSub32Emit`) -/

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

/-- 64-bit pointer/count update `r OP= k`. -/
def ptrImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr64 r }) .AT_none (.sword .U64)
    (.Papp2 op (pv64 r) (.Pconst k))

/-- `r := t OP s` at u32 (single `Papp2`, no carry). -/
def binOp32 (r t s : String) (op : SOp2) : InstrR :=
  .Cassgn (.Lvar { var := vr32 r }) .AT_none (.sword .U32)
    (.Papp2 op (pv32 t) (pv32 s))

/-! ## §2  The loop bodies + FunDecls

A bitwise-op iteration mirrors `Mpn.LogicalPrototype.logBody` at u32:
```
t = [:u32 ap + 0];
s = [:u32 bp + 0];
r = t OP s;          // u32, single Papp2
[:u32 op + 0] = r;
ap += 4; bp += 4; op += 4; n -= 1;
```
The full body is just the `while (n != 0)` — no carry prelude (there is no
carry). -/

/-- One open-coded U32 iteration parametric on the bitwise op. -/
def logBody32 (op : SOp2) : List InstrR :=
  [ load32At0 "t" "ap"
  , load32At0 "s" "bp"
  , binOp32 "r" "t" "s" op
  , store32At0 "op" "r"
  , ptrImm "ap" (.Oadd .U64) 4
  , ptrImm "bp" (.Oadd .U64) 4
  , ptrImm "op" (.Oadd .U64) 4
  , ptrImm "n"  (.Osub .U64) 1 ]

/-- Full body: just the loop (no carry prelude). -/
def logFullBody32 (op : SOp2) : List InstrR :=
  [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) (logBody32 op) ]

/-- `mpn_and_n` at U32 limbs. Symbol `mpn_and_n_32`. -/
def mpnAndN32Fd : FunDecl where
  name := { name := "mpn_and_n_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr64 "bp" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := logFullBody32 (.Oland .U32)
  results := []

/-- `mpn_ior_n` at U32 limbs. Symbol `mpn_ior_n_32`. -/
def mpnIorN32Fd : FunDecl where
  name := { name := "mpn_ior_n_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr64 "bp" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := logFullBody32 (.Olor .U32)
  results := []

/-- `mpn_xor_n` at U32 limbs. Symbol `mpn_xor_n_32`. -/
def mpnXorN32Fd : FunDecl where
  name := { name := "mpn_xor_n_32" }
  params := [⟨{ var := vr64 "op" }⟩, ⟨{ var := vr64 "ap" }⟩,
             ⟨{ var := vr64 "bp" }⟩, ⟨{ var := vr64 "n" }⟩]
  body := logFullBody32 (.Olxor .U32)
  results := []

/-! ## §3  CT shape + emission -/

/-- Each kernel is constant-time-shaped (loop guard on public `n` only). -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody32 (.Oland .U32)) = true := by decide
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody32 (.Olor  .U32)) = true := by decide
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody32 (.Olxor .U32)) = true := by decide

/-- Emit the three 32-bit `.jazz` sources. -/
def emittedAnd32 : Option String := emitFunDecl mpnAndN32Fd
def emittedIor32 : Option String := emitFunDecl mpnIorN32Fd
def emittedXor32 : Option String := emitFunDecl mpnXorN32Fd

#eval match emittedAnd32 with | some s => s | none => "EMIT FAILED"

end CatCrypt.Crypto.Jasmin.Mpn.Logical32Emit
