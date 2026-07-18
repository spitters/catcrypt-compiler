/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-!
# HMAC-SHA-256 (RFC 2104) in Lean Jasmin AST

Companion to `Sha256JasminFull.lean`.  Where that module emits the
SHA-256 round helpers and compression / schedule functions, this one
emits the HMAC byte-level pad construction:

```
ipad = 0x36 × 64
opad = 0x5c × 64
inner_hash = SHA256( (key' XOR ipad) || msg )
outer_hash = SHA256( (key' XOR opad) || inner_hash )
```

where `key'` is `key` zero-padded to 64 bytes if shorter, or
`SHA256(key)` zero-padded if longer.

What is emitted as Lean Jasmin AST:

  * `hmac_sha256_xor_ipad` — fill `inner_key[0..64] = key_padded ⊕ 0x36`
  * `hmac_sha256_xor_opad` — fill `outer_key[0..64] = key_padded ⊕ 0x5c`

Padding (key < 64 bytes vs key > 64 bytes), buffer concatenation
`inner_key || msg`, and the two SHA-256 calls themselves stay as
hand-coded Rust glue — exactly the same pattern used by
`Sha256JasminFull` for FIPS H-init / multi-block iteration / final
encoding.  The structural part (the 64-byte XOR loops with the magic
0x36 / 0x5c constants) is what we want mechanically auditable.

References: RFC 2104 §2; FIPS 198-1 §4.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-! ## §1.  AST construction helpers (u8 / u64 bias) -/

def u8Var (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U8 } }

def u64Var (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U64 } }

def u8GVar (name : String) : GVar := { gv := u8Var name, gs := false }

def E8 (name : String) : PExpr := PExpr.Pvar (u8GVar name)
def K (n : Nat) : PExpr := PExpr.Pconst n

/-- u8-array-typed parameter (length `n` bytes). -/
def u8ArrParam (name : String) (n : Nat) : FunParam :=
  { var := { var := { vname := name, vtype := SType.sarr n } } }

/-- u64 scalar param (used as a loop bound surrogate; absent here but
    kept for parallel structure with HKDF). -/
def u64Param (name : String) : FunParam := { var := u64Var name }

/-- Pget for a u8 array indexed by a u8 expression.  We declare the
    array's vtype as `sarr 64` (matching the byte length) so the
    auto-derived Rust type would be `[u8; 64]` — overridden at emit
    time when we want `&[u8; 64]` / `&mut [u8; 64]`. -/
def Get8 (arr : String) (idx : PExpr) : PExpr :=
  PExpr.Pget ArrAccess.AAdirect WSize.U8
    { gv := { var := { vname := arr, vtype := SType.sarr 64 } }, gs := false }
    idx

/-- Laset for a u8 array slot. -/
def Set8 (arr : String) (idx : PExpr) (e : PExpr) : InstrR :=
  InstrR.Cassgn
    (LVal.Laset ArrAccess.AAdirect WSize.U8
      { var := { vname := arr, vtype := SType.sarr 64 } } idx)
    AssgnTag.AT_none (SType.sword WSize.U8) e

/-- u8 XOR shorthand. -/
def Xor8 (a b : PExpr) : PExpr := PExpr.Papp2 (SOp2.Olxor WSize.U8) a b

/-- Loop variable, u64-typed (so `for i in 0u64..64u64` parses). -/
def loopVarU64 (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U64 } }

/-! ## §2.  IPAD / OPAD XOR helpers

Each takes a 64-byte zero-padded key buffer + a destination 64-byte
buffer; XORs the magic constant byte-by-byte into the destination. -/

def xorPadBody (padByte : Nat) : Cmd :=
  [ InstrR.Cfor (loopVarU64 "i")
      { dir := LoopDir.UpTo, lo := 0, hi := 64 }
      [ InstrR.Cassgn (LVal.Lvar (u8Var "kb")) AssgnTag.AT_none
          (SType.sword WSize.U8) (Get8 "key_padded" (PExpr.Pvar (u8GVar "i")))
      , Set8 "out" (PExpr.Pvar (u8GVar "i")) (Xor8 (E8 "kb") (K padByte))
      ]
  ]

def xorIpadFd : FunDecl :=
  { name    := { name := "hmac_sha256_xor_ipad" }
  , params  := [u8ArrParam "key_padded" 64, u8ArrParam "out" 64]
  , body    := xorPadBody 0x36
  , results := []
  }

def xorOpadFd : FunDecl :=
  { name    := { name := "hmac_sha256_xor_opad" }
  , params  := [u8ArrParam "key_padded" 64, u8ArrParam "out" 64]
  , body    := xorPadBody 0x5c
  , results := []
  }

/-! ## §3.  Emit -/

/-- Type overrides: both arrays are accessed with read+write per call,
    so caller passes the key as a `&[u8; 64]` and the destination as
    `&mut [u8; 64]`. -/
def ipadOverrides : List (String × String) :=
  [ ("key_padded", "&[u8; 64]")
  , ("out",        "&mut [u8; 64]") ]

def opadOverrides : List (String × String) := ipadOverrides

/-- Hand-coded Rust glue (NOT Lean-emitted).  Wraps the two AST
    helpers + a `sha256` oracle into the full HMAC-SHA-256 surface
    expected by RFC 2104 / FIPS 198-1.  Mirrors how
    `Sha256JasminFull` punts padding/iteration to caller-side glue. -/
def hmacGlue : String :=
  "// ---- hand-glue for HMAC-SHA-256 (not Lean-emitted) ---- " ++
  "\n// Wraps `hmac_sha256_xor_ipad` / `hmac_sha256_xor_opad` (which" ++
  "\n// ARE Lean-emitted just above) and the `sha256` oracle into" ++
  "\n// the full HMAC-SHA-256 surface (RFC 2104).\n" ++
  "pub fn sha256(data: &[u8]) -> [u8; 32] {\n" ++
  "    use core::convert::TryInto;\n" ++
  "    // FIPS 180-4 H-init.\n" ++
  "    let h0: [u32; 8] = [\n" ++
  "        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,\n" ++
  "        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,\n" ++
  "    ];\n" ++
  "    // SHA-256 round constants K[0..64].\n" ++
  "    let k: [u32; 64] = [\n" ++
  "        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,\n" ++
  "        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,\n" ++
  "        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,\n" ++
  "        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,\n" ++
  "        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,\n" ++
  "        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,\n" ++
  "        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,\n" ++
  "        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,\n" ++
  "    ];\n" ++
  "    // FIPS 180-4 §5.1.1 padding: msg || 0x80 || zeros || u64 length-bits.\n" ++
  "    let bitlen = (data.len() as u64).wrapping_mul(8);\n" ++
  "    let mut padded: Vec<u8> = data.to_vec();\n" ++
  "    padded.push(0x80);\n" ++
  "    while padded.len() % 64 != 56 { padded.push(0); }\n" ++
  "    padded.extend_from_slice(&bitlen.to_be_bytes());\n" ++
  "    let mut state = h0;\n" ++
  "    for chunk in padded.chunks_exact(64) {\n" ++
  "        let mut w = [0u32; 64];\n" ++
  "        for i in 0..16 {\n" ++
  "            w[i] = u32::from_be_bytes(chunk[4*i..4*i+4].try_into().unwrap());\n" ++
  "        }\n" ++
  "        sha256_msg_schedule(&mut w);\n" ++
  "        let (a,b,c,d,e,f,g,h) = sha256_compress(\n" ++
  "            state[0], state[1], state[2], state[3],\n" ++
  "            state[4], state[5], state[6], state[7], &k, &mut w);\n" ++
  "        state = [a,b,c,d,e,f,g,h];\n" ++
  "    }\n" ++
  "    let mut out = [0u8; 32];\n" ++
  "    for i in 0..8 {\n" ++
  "        out[4*i..4*i+4].copy_from_slice(&state[i].to_be_bytes());\n" ++
  "    }\n" ++
  "    out\n" ++
  "}\n\n" ++
  "pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {\n" ++
  "    // Step 1: pad the key to 64 bytes.\n" ++
  "    let mut key_padded = [0u8; 64];\n" ++
  "    if key.len() > 64 {\n" ++
  "        let kh = sha256(key);\n" ++
  "        key_padded[..32].copy_from_slice(&kh);\n" ++
  "    } else {\n" ++
  "        key_padded[..key.len()].copy_from_slice(key);\n" ++
  "    }\n" ++
  "    // Step 2: build inner / outer XOR'd keys via Lean-emitted helpers.\n" ++
  "    let mut inner_key = [0u8; 64];\n" ++
  "    let mut outer_key = [0u8; 64];\n" ++
  "    hmac_sha256_xor_ipad(&key_padded, &mut inner_key);\n" ++
  "    hmac_sha256_xor_opad(&key_padded, &mut outer_key);\n" ++
  "    // Step 3: inner_hash = SHA256(inner_key || msg).\n" ++
  "    let mut inner_buf: Vec<u8> = inner_key.to_vec();\n" ++
  "    inner_buf.extend_from_slice(msg);\n" ++
  "    let inner_hash = sha256(&inner_buf);\n" ++
  "    // Step 4: outer_hash = SHA256(outer_key || inner_hash).\n" ++
  "    let mut outer_buf: Vec<u8> = outer_key.to_vec();\n" ++
  "    outer_buf.extend_from_slice(&inner_hash);\n" ++
  "    sha256(&outer_buf)\n" ++
  "}\n"

/-- Lean-emitted slice of HMAC: just the IPAD / OPAD XOR helpers.
    The full file (with prepended SHA-256 primitives + appended HMAC
    glue) is assembled by `runEmit` via I/O, to avoid a toplevel
    `def main` collision when `Sha256JasminFull` is imported. -/
def emitHmacAst : String :=
  String.intercalate "\n\n" [
    ppFunDeclWith ipadOverrides [] [] xorIpadFd,
    ppFunDeclWith opadOverrides [] [] xorOpadFd
  ]

/-- Hand-glue + Lean-AST emit, concatenated.  Excludes the SHA-256
    primitives — those are concatenated by `runEmit`. -/
def emitWithoutSha : String :=
  emitHmacAst ++ "\n\n" ++ hmacGlue

/-- Library entry point.  Reads the SHA-256 primitives from
    `/tmp/sha256_jasmin_full.rs` (produced by `Sha256JasminFull.main`)
    and prepends them to the HMAC AST + glue.  Run order:
    ```
    lake env lean --run …/Sha256JasminFull.lean
    lake env lean --run …/HmacSha256JasminEmit.lean
    ```
    -/
def runEmit : IO Unit := do
  let shaPath := "/tmp/sha256_jasmin_full.rs"
  let outPath := "/tmp/hmac_sha256_jasmin.rs"
  let shaSrc ←
    if ← System.FilePath.pathExists shaPath then
      IO.FS.readFile shaPath
    else
      pure "// (sha256_jasmin_full.rs not found — run Sha256JasminFull first)\n"
  IO.FS.writeFile outPath (shaSrc ++ "\n\n" ++ emitWithoutSha)
  IO.println s!"wrote {outPath}"

end CatCrypt.Crypto.Jasmin.Examples.HmacSha256Jasmin
