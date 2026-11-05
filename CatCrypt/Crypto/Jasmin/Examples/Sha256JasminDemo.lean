/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-!
# SHA-256 inner bit-functions in Lean Jasmin AST + safe-Rust emit

Hand-transcribed from libjade (https://github.com/formosa-crypto/libjade) at commit
`9426b320031ea121c9b07b1a7d7d616dd97c1a75`,
`oldsrc-should-delete/crypto_hash/sha256/amd64/ref/sha256.jinc` (lines 81–138).
Demonstrates path (iii) of the Jasmin → safe-Rust pipeline:

  1. Build a `JasminProg` containing the four SHA-256 round helpers
     (Ch, Maj, BSig0, BSig1) directly as `FunDecl` AST values.
  2. Run `JasminToRustEmit.ppJasminProg` to emit a Rust source string.
  3. Write to `/tmp/sha256_jasmin_demo.rs`.
  4. Compile + KAT-check downstream.

This is the *minimum-scope demo* — enough to show the Jasmin AST →
safe-Rust pipeline runs end-to-end.  The full SHA-256 (compression
function, message schedule, padding, byte-encoding) is ~400 LoC of
transcription on top; out of scope for the demo.

Spec reference: FIPS 180-4 §4.1.2:

```
Ch(x, y, z)   = (x AND y) XOR ((NOT x) AND z)
Maj(x, y, z)  = (x AND y) XOR (x AND z) XOR (y AND z)
BSig0(x)      = ROTR_2(x)  XOR ROTR_13(x) XOR ROTR_22(x)
BSig1(x)      = ROTR_6(x)  XOR ROTR_11(x) XOR ROTR_25(x)
```
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.Sha256JasminDemo

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-! ## §1.  AST construction helpers -/

/-- Build a u32-typed local variable. -/
def u32Var (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U32 } }

/-- Build a global-var (read-only) of u32 type — for use in Pvar. -/
def u32GVar (name : String) : GVar :=
  { gv := u32Var name, gs := false }

/-- Pvar shorthand. -/
def E (name : String) : PExpr := PExpr.Pvar (u32GVar name)

/-- Pconst shorthand. -/
def K (n : Nat) : PExpr := PExpr.Pconst n

/-- Lvar shorthand. -/
def Lv (name : String) : LVal := LVal.Lvar (u32Var name)

/-- u32 binary op shorthand. -/
def Op2 (op : SOp2) (a b : PExpr) : PExpr := PExpr.Papp2 op a b

/-- u32 unary op shorthand. -/
def Op1 (op : SOp1) (a : PExpr) : PExpr := PExpr.Papp1 op a

/-- Cassgn x := e, x is a fresh u32 local. -/
def Assn (name : String) (e : PExpr) : InstrR :=
  InstrR.Cassgn (Lv name) AssgnTag.AT_none (SType.sword WSize.U32) e

/-- ROR_32 via Copn asm op: dest = src.rotate_right(amt). -/
def Ror32 (dest : String) (src : PExpr) (amt : Nat) : InstrR :=
  InstrR.Copn [Lv dest] AssgnTag.AT_none
    (SOpn.Oasm { name := "#ROR_32" })
    [src, PExpr.Pconst amt]

/-! ## §2.  The four SHA-256 helpers -/

/-- `Ch(x, y, z) = (x AND y) XOR ((NOT x) AND z)`. -/
def chFd : FunDecl :=
  { name    := { name := "sha256_ch" }
  , params  := [{ var := u32Var "x" }, { var := u32Var "y" }, { var := u32Var "z" }]
  , body    :=
      [ Assn "t1"     (Op2 (SOp2.Oland WSize.U32) (E "x") (E "y"))     -- t1 = x & y
      , Assn "nx"     (Op1 (SOp1.Olnot WSize.U32) (E "x"))              -- nx = !x
      , Assn "t2"     (Op2 (SOp2.Oland WSize.U32) (E "nx") (E "z"))     -- t2 = nx & z
      , Assn "result" (Op2 (SOp2.Olxor WSize.U32) (E "t1") (E "t2"))    -- result = t1 ^ t2
      ]
  , results := [u32Var "result"]
  }

/-- `Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)`. -/
def majFd : FunDecl :=
  { name    := { name := "sha256_maj" }
  , params  := [{ var := u32Var "x" }, { var := u32Var "y" }, { var := u32Var "z" }]
  , body    :=
      [ Assn "xy"     (Op2 (SOp2.Oland WSize.U32) (E "x") (E "y"))      -- xy = x & y
      , Assn "xz"     (Op2 (SOp2.Oland WSize.U32) (E "x") (E "z"))      -- xz = x & z
      , Assn "yz"     (Op2 (SOp2.Oland WSize.U32) (E "y") (E "z"))      -- yz = y & z
      , Assn "t1"     (Op2 (SOp2.Olxor WSize.U32) (E "xy") (E "xz"))    -- t1 = xy ^ xz
      , Assn "result" (Op2 (SOp2.Olxor WSize.U32) (E "t1") (E "yz"))    -- result = t1 ^ yz
      ]
  , results := [u32Var "result"]
  }

/-- `BSig0(x) = ROTR_2(x) XOR ROTR_13(x) XOR ROTR_22(x)`. -/
def bsig0Fd : FunDecl :=
  { name    := { name := "sha256_bsig0" }
  , params  := [{ var := u32Var "x" }]
  , body    :=
      [ Ror32 "r2"     (E "x")  2
      , Ror32 "r13"    (E "x") 13
      , Ror32 "r22"    (E "x") 22
      , Assn  "t1"     (Op2 (SOp2.Olxor WSize.U32) (E "r2")  (E "r13"))
      , Assn  "result" (Op2 (SOp2.Olxor WSize.U32) (E "t1")  (E "r22"))
      ]
  , results := [u32Var "result"]
  }

/-- `BSig1(x) = ROTR_6(x) XOR ROTR_11(x) XOR ROTR_25(x)`. -/
def bsig1Fd : FunDecl :=
  { name    := { name := "sha256_bsig1" }
  , params  := [{ var := u32Var "x" }]
  , body    :=
      [ Ror32 "r6"     (E "x")  6
      , Ror32 "r11"    (E "x") 11
      , Ror32 "r25"    (E "x") 25
      , Assn  "t1"     (Op2 (SOp2.Olxor WSize.U32) (E "r6")  (E "r11"))
      , Assn  "result" (Op2 (SOp2.Olxor WSize.U32) (E "t1")  (E "r25"))
      ]
  , results := [u32Var "result"]
  }

/-- Combined Jasmin program. -/
def sha256DemoProg : JasminProg :=
  { funcs := [chFd, majFd, bsig0Fd, bsig1Fd] }

/-- Pre-computed Rust output (so it can be inspected without I/O). -/
def emit : String := ppJasminProg sha256DemoProg

end CatCrypt.Crypto.Jasmin.Examples.Sha256JasminDemo

/-- `lake env lean --run` entry point: write to a fixed file. -/
private def main : IO Unit := do
  let path := "/tmp/sha256_jasmin_demo.rs"
  IO.FS.writeFile path
    CatCrypt.Crypto.Jasmin.Examples.Sha256JasminDemo.emit
  IO.println s!"wrote {path}"
