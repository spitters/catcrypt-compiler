/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminAST
public import CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-!
# SHA-256: full inner functions + compression + schedule, in Lean Jasmin AST

Hand-transcribed from `BLS/libjade/oldsrc-should-delete/crypto_hash/
sha256/amd64/ref/sha256.jinc` — the FIPS 180-4 / RFC 6234 SHA-256
specification.

What gets emitted:

  * `sha256_ch`, `sha256_maj`              — round Boolean functions
  * `sha256_bsig0`, `sha256_bsig1`         — Σ₀, Σ₁ rotation triples (state)
  * `sha256_ssig0`, `sha256_ssig1`         — σ₀, σ₁ rotation triples (schedule)
  * `sha256_msg_schedule`                  — expand W[16..63] from W[0..15]
  * `sha256_compress`                      — 64-round compression: state' = compress(state, W)

Padding, multi-block iteration, FIPS H-init, and final state→bytes
encoding are kept as **hand-coded Rust glue** in
`signal-wasm/component/src/sha256.rs` — that's mechanical plumbing
around the Lean-emitted core.

Spec: FIPS 180-4 §6.2.

```
σ₀(x) = ROTR_7(x) ⊕ ROTR_18(x) ⊕ SHR_3(x)
σ₁(x) = ROTR_17(x) ⊕ ROTR_19(x) ⊕ SHR_10(x)
W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]   for t ∈ 16..64

T1 = h + Σ₁(e) + Ch(e,f,g) + K[t] + W[t]
T2 = Σ₀(a) + Maj(a,b,c)
h ← g, g ← f, f ← e, e ← d + T1, d ← c, c ← b, b ← a, a ← T1 + T2
```
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.Examples.Sha256JasminFull

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-! ## §1.  AST construction helpers (u32 bias) -/

def u32Var (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U32 } }

def u32GVar (name : String) : GVar := { gv := u32Var name, gs := false }

def E (name : String) : PExpr := PExpr.Pvar (u32GVar name)
def K (n : Nat) : PExpr := PExpr.Pconst n
def Lv (name : String) : LVal := LVal.Lvar (u32Var name)

def Op2 (op : SOp2) (a b : PExpr) : PExpr := PExpr.Papp2 op a b
def Op1 (op : SOp1) (a : PExpr) : PExpr := PExpr.Papp1 op a

def Assn (name : String) (e : PExpr) : InstrR :=
  InstrR.Cassgn (Lv name) AssgnTag.AT_none (SType.sword WSize.U32) e

def Ror32 (dest : String) (src : PExpr) (amt : Nat) : InstrR :=
  InstrR.Copn [Lv dest] AssgnTag.AT_none
    (SOpn.Oasm { name := "#ROR_32" })
    [src, PExpr.Pconst amt]

def Shr32 (dest : String) (src : PExpr) (amt : Nat) : InstrR :=
  InstrR.Copn [Lv dest] AssgnTag.AT_none
    (SOpn.Oasm { name := "#SHR_32" })
    [src, PExpr.Pconst amt]

/-- Call a single-result helper.  Equivalent to `let mut name = fn(args);`. -/
def Call (name : String) (fn : String) (args : List PExpr) : InstrR :=
  InstrR.Ccall InlineInfo.DoInline [Lv name] { name := fn }
    args

/-- u32-array-typed variable (length `n`).  The vtype encodes total
    bytes (`sarr (n*4)`), but we override the Rust type at emit time
    via `paramTypeOverrides`. -/
def u32ArrParam (name : String) (n : Nat) : FunParam :=
  { var := { var := { vname := name, vtype := SType.sarr (n * 4) } } }

/-- u32 scalar parameter. -/
def u32Param (name : String) : FunParam := { var := u32Var name }

/-- Pget for a u32 array indexed by a u32 expression. -/
def Get32 (arr : String) (idx : PExpr) : PExpr :=
  PExpr.Pget ArrAccess.AAscale WSize.U32
    { gv := { var := { vname := arr, vtype := SType.sarr (64 * 4) } }, gs := false }
    idx

/-- Laset for a u32 array slot — write `arr[idx] = expr`. -/
def Set32 (arr : String) (idx : PExpr) (e : PExpr) : InstrR :=
  InstrR.Cassgn
    (LVal.Laset ArrAccess.AAscale WSize.U32
      { var := { vname := arr, vtype := SType.sarr (64 * 4) } } idx)
    AssgnTag.AT_none (SType.sword WSize.U32) e

/-- u32 add (wrapping, mod 2^32). -/
def Add32 (a b : PExpr) : PExpr := Op2 (SOp2.Oadd WSize.U32) a b
def Xor32 (a b : PExpr) : PExpr := Op2 (SOp2.Olxor WSize.U32) a b
def And32 (a b : PExpr) : PExpr := Op2 (SOp2.Oland WSize.U32) a b
def Not32 (a : PExpr)   : PExpr := Op1 (SOp1.Olnot WSize.U32) a

/-! ## §2.  The six SHA-256 round helpers (Ch / Maj / Σ / σ) -/

/-- `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def chFd : FunDecl :=
  { name    := { name := "sha256_ch" }
  , params  := [u32Param "x", u32Param "y", u32Param "z"]
  , body    :=
      [ Assn "t1"     (And32 (E "x") (E "y"))
      , Assn "nx"     (Not32 (E "x"))
      , Assn "t2"     (And32 (E "nx") (E "z"))
      , Assn "result" (Xor32 (E "t1") (E "t2"))
      ]
  , results := [u32Var "result"]
  }

/-- `Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def majFd : FunDecl :=
  { name    := { name := "sha256_maj" }
  , params  := [u32Param "x", u32Param "y", u32Param "z"]
  , body    :=
      [ Assn "xy"     (And32 (E "x") (E "y"))
      , Assn "xz"     (And32 (E "x") (E "z"))
      , Assn "yz"     (And32 (E "y") (E "z"))
      , Assn "t1"     (Xor32 (E "xy") (E "xz"))
      , Assn "result" (Xor32 (E "t1") (E "yz"))
      ]
  , results := [u32Var "result"]
  }

/-- `Σ₀(x) = ROTR₂(x) ⊕ ROTR₁₃(x) ⊕ ROTR₂₂(x)`. -/
def bsig0Fd : FunDecl :=
  { name    := { name := "sha256_bsig0" }
  , params  := [u32Param "x"]
  , body    :=
      [ Ror32 "r2"  (E "x")  2
      , Ror32 "r13" (E "x") 13
      , Ror32 "r22" (E "x") 22
      , Assn  "t1"     (Xor32 (E "r2")  (E "r13"))
      , Assn  "result" (Xor32 (E "t1")  (E "r22"))
      ]
  , results := [u32Var "result"]
  }

/-- `Σ₁(x) = ROTR₆(x) ⊕ ROTR₁₁(x) ⊕ ROTR₂₅(x)`. -/
def bsig1Fd : FunDecl :=
  { name    := { name := "sha256_bsig1" }
  , params  := [u32Param "x"]
  , body    :=
      [ Ror32 "r6"  (E "x")  6
      , Ror32 "r11" (E "x") 11
      , Ror32 "r25" (E "x") 25
      , Assn  "t1"     (Xor32 (E "r6")  (E "r11"))
      , Assn  "result" (Xor32 (E "t1")  (E "r25"))
      ]
  , results := [u32Var "result"]
  }

/-- `σ₀(x) = ROTR₇(x) ⊕ ROTR₁₈(x) ⊕ SHR₃(x)`. -/
def ssig0Fd : FunDecl :=
  { name    := { name := "sha256_ssig0" }
  , params  := [u32Param "x"]
  , body    :=
      [ Ror32 "r7"  (E "x")  7
      , Ror32 "r18" (E "x") 18
      , Shr32 "s3"  (E "x")  3
      , Assn  "t1"     (Xor32 (E "r7")  (E "r18"))
      , Assn  "result" (Xor32 (E "t1")  (E "s3"))
      ]
  , results := [u32Var "result"]
  }

/-- `σ₁(x) = ROTR₁₇(x) ⊕ ROTR₁₉(x) ⊕ SHR₁₀(x)`. -/
def ssig1Fd : FunDecl :=
  { name    := { name := "sha256_ssig1" }
  , params  := [u32Param "x"]
  , body    :=
      [ Ror32 "r17" (E "x") 17
      , Ror32 "r19" (E "x") 19
      , Shr32 "s10" (E "x") 10
      , Assn  "t1"     (Xor32 (E "r17") (E "r19"))
      , Assn  "result" (Xor32 (E "t1")  (E "s10"))
      ]
  , results := [u32Var "result"]
  }

/-! ## §3.  Message schedule expansion W[16..63]

Implements the recurrence `W[t] = σ₁(W[t-2]) + W[t-7] + σ₀(W[t-15]) + W[t-16]`
for t ∈ {16, …, 63}.  Caller initialises `W[0..15]` from the input
block (with appropriate big-endian decoding) before calling this. -/

def msgScheduleBody : Cmd :=
  [ -- for tr in 16..64 do W[tr] := σ₁(W[tr-2]) + W[tr-7] + σ₀(W[tr-15]) + W[tr-16]
    InstrR.Cfor (u32Var "tr")
      { dir := LoopDir.UpTo, lo := 16, hi := 64 }
      [ Assn "wt2"   (Get32 "W" (Op2 (SOp2.Osub WSize.U32) (E "tr") (K 2)))
      , Call "s1"    "sha256_ssig1" [E "wt2"]
      , Assn "wt7"   (Get32 "W" (Op2 (SOp2.Osub WSize.U32) (E "tr") (K 7)))
      , Assn "wt15"  (Get32 "W" (Op2 (SOp2.Osub WSize.U32) (E "tr") (K 15)))
      , Call "s0"    "sha256_ssig0" [E "wt15"]
      , Assn "wt16"  (Get32 "W" (Op2 (SOp2.Osub WSize.U32) (E "tr") (K 16)))
      , Assn "sum1"  (Add32 (E "s1") (E "wt7"))
      , Assn "sum2"  (Add32 (E "s0") (E "wt16"))
      , Assn "sum"   (Add32 (E "sum1") (E "sum2"))
      , Set32 "W"    (E "tr") (E "sum")
      ]
  ]

def msgScheduleFd : FunDecl :=
  { name    := { name := "sha256_msg_schedule" }
  , params  := [u32ArrParam "W" 64]
  , body    := msgScheduleBody
  , results := []  -- W is mutated in-place via `&mut [u32; 64]`
  }

/-! ## §4.  Compression function

State (a..h) is read from input params, mutated through 64 rounds
against (K, W), and the per-block result `state[i] += a..h[i]`
returned as a tuple of 8 u32 values.  Caller (Rust glue) handles
state init, multi-block iteration, padding, and final encoding. -/

def compressBody : Cmd :=
  [ -- Initialise working registers.
    Assn "a" (E "a_in")
  , Assn "b" (E "b_in")
  , Assn "c" (E "c_in")
  , Assn "d" (E "d_in")
  , Assn "e" (E "e_in")
  , Assn "f" (E "f_in")
  , Assn "g" (E "g_in")
  , Assn "h" (E "h_in")
    -- Round loop: 64 iterations.
  , InstrR.Cfor (u32Var "tr")
      { dir := LoopDir.UpTo, lo := 0, hi := 64 }
      [ -- T1 = h + Σ₁(e) + Ch(e,f,g) + K[tr] + W[tr]
        Call "s1"   "sha256_bsig1" [E "e"]
      , Call "ch"   "sha256_ch"    [E "e", E "f", E "g"]
      , Assn "kt"   (Get32 "K" (E "tr"))
      , Assn "wt"   (Get32 "W" (E "tr"))
      , Assn "t1a"  (Add32 (E "h")    (E "s1"))
      , Assn "t1b"  (Add32 (E "t1a")  (E "ch"))
      , Assn "t1c"  (Add32 (E "t1b")  (E "kt"))
      , Assn "T1"   (Add32 (E "t1c")  (E "wt"))
        -- T2 = Σ₀(a) + Maj(a,b,c)
      , Call "s0"   "sha256_bsig0" [E "a"]
      , Call "mj"   "sha256_maj"   [E "a", E "b", E "c"]
      , Assn "T2"   (Add32 (E "s0")   (E "mj"))
        -- Shift-down: h = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2
      , Assn "h_new" (E "g")
      , Assn "g_new" (E "f")
      , Assn "f_new" (E "e")
      , Assn "e_new" (Add32 (E "d") (E "T1"))
      , Assn "d_new" (E "c")
      , Assn "c_new" (E "b")
      , Assn "b_new" (E "a")
      , Assn "a_new" (Add32 (E "T1") (E "T2"))
        -- Re-bind a..h for the next iteration.
      , Assn "a"     (E "a_new")
      , Assn "b"     (E "b_new")
      , Assn "c"     (E "c_new")
      , Assn "d"     (E "d_new")
      , Assn "e"     (E "e_new")
      , Assn "f"     (E "f_new")
      , Assn "g"     (E "g_new")
      , Assn "h"     (E "h_new")
      ]
    -- Final: result_i = state_in_i + a..h_i
  , Assn "out_a" (Add32 (E "a") (E "a_in"))
  , Assn "out_b" (Add32 (E "b") (E "b_in"))
  , Assn "out_c" (Add32 (E "c") (E "c_in"))
  , Assn "out_d" (Add32 (E "d") (E "d_in"))
  , Assn "out_e" (Add32 (E "e") (E "e_in"))
  , Assn "out_f" (Add32 (E "f") (E "f_in"))
  , Assn "out_g" (Add32 (E "g") (E "g_in"))
  , Assn "out_h" (Add32 (E "h") (E "h_in"))
  ]

def compressFd : FunDecl :=
  { name    := { name := "sha256_compress" }
  , params  := [ u32Param "a_in", u32Param "b_in", u32Param "c_in", u32Param "d_in"
               , u32Param "e_in", u32Param "f_in", u32Param "g_in", u32Param "h_in"
               , u32ArrParam "K" 64
               , u32ArrParam "W" 64 ]
  , body    := compressBody
  , results := [ u32Var "out_a", u32Var "out_b", u32Var "out_c", u32Var "out_d"
               , u32Var "out_e", u32Var "out_f", u32Var "out_g", u32Var "out_h" ]
  }

/-! ## §5.  Combined emit -/

/-- Type overrides: K and W are u32 arrays of length 64, accessed as
    `&[u32; 64]` (Rust idiomatic).  Without these the auto-derived
    type from `sarr 256` would be `[u8; 256]`, which is wrong for our
    Pget U32 access pattern. -/
def kwOverrides : List (String × String) :=
  [ ("W", "&mut [u32; 64]")
  , ("K", "&[u32; 64]") ]

/-- Single, unified emit.  The helpers (Ch, Maj, Σ, σ) emit with
    `#[inline]` so rustc folds them into the compression hot path. -/
def emit : String :=
  let inlineAttr := ["#[inline]"]
  let body := String.intercalate "\n\n" [
      ppFunDeclWith [] [] inlineAttr chFd,
      ppFunDeclWith [] [] inlineAttr majFd,
      ppFunDeclWith [] [] inlineAttr bsig0Fd,
      ppFunDeclWith [] [] inlineAttr bsig1Fd,
      ppFunDeclWith [] [] inlineAttr ssig0Fd,
      ppFunDeclWith [] [] inlineAttr ssig1Fd,
      ppFunDeclWith [("W", "&mut [u32; 64]")] [] [] msgScheduleFd,
      ppFunDeclWith kwOverrides [] [] compressFd
    ]
  body

end CatCrypt.Crypto.Jasmin.Examples.Sha256JasminFull

/-- `lake env lean --run` entry point: write the emitted Rust to a
    fixed file location for downstream consumption (signal-wasm
    component). -/
private def main : IO Unit := do
  let path := "/tmp/sha256_jasmin_full.rs"
  IO.FS.writeFile path
    CatCrypt.Crypto.Jasmin.Examples.Sha256JasminFull.emit
  IO.println s!"wrote {path}"
