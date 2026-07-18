/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-!
# HKDF-SHA-256 (RFC 5869) in Lean Jasmin AST

Two phases:

  * `Extract(salt, ikm) = HMAC-SHA-256(salt, ikm) → 32-byte PRK`
  * `Expand(prk, info, length) = T(1) || T(2) || …` where
    `T(i) = HMAC-SHA-256(prk, T(i-1) || info || i)` and `T(0) = ε`.

Lean-AST-emitted helpers:

  * `hkdf_copy_prev` — copy the previous 32-byte block `T(i-1)` into
    the head of the HMAC-input buffer (the `T(i-1) || info || i`
    concatenation).  Byte-by-byte to stay in the AST.

(Single helper — the concatenation logic is the only piece with
non-trivial structure.  Counter-byte append and SHA-mac orchestration
are one-liners best left as glue.)

`Extract`, `Expand`, and the outer T-loop are hand-glue, mirroring the
HMAC pattern: thin Rust composition over the Lean-emitted core.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.JasminToRustEmit

/-! ## §1.  AST construction helpers (mirrors HMAC module). -/

def u8Var (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U8 } }

def u8GVar (name : String) : GVar := { gv := u8Var name, gs := false }

def u64LoopVar (name : String) : VarI :=
  { var := { vname := name, vtype := SType.sword WSize.U64 } }

def u8ArrParam (name : String) (n : Nat) : FunParam :=
  { var := { var := { vname := name, vtype := SType.sarr n } } }

def u8GVarOfArr (name : String) (n : Nat) : GVar :=
  { gv := { var := { vname := name, vtype := SType.sarr n } }, gs := false }

def Get8 (arr : String) (n : Nat) (idx : PExpr) : PExpr :=
  PExpr.Pget ArrAccess.AAdirect WSize.U8 (u8GVarOfArr arr n) idx

def Set8 (arr : String) (n : Nat) (idx : PExpr) (e : PExpr) : InstrR :=
  InstrR.Cassgn
    (LVal.Laset ArrAccess.AAdirect WSize.U8
      { var := { vname := arr, vtype := SType.sarr n } } idx)
    AssgnTag.AT_none (SType.sword WSize.U8) e

/-! ## §2.  `hkdf_copy_prev`

Copies the 32-byte previous-block buffer `prev` into the head of a
larger destination buffer `dest` (which the caller pre-sized to fit
`prev || info || counter`).  This is the structural kernel of the
`T(i-1) || info || i` concatenation that drives HKDF-Expand. -/

def copyPrevBody : Cmd :=
  [ InstrR.Cfor (u64LoopVar "i")
      { dir := LoopDir.UpTo, lo := 0, hi := 32 }
      [ Set8 "dest" 4096 (PExpr.Pvar (u8GVar "i"))
          (Get8 "prev" 32 (PExpr.Pvar (u8GVar "i")))
      ]
  ]

def copyPrevFd : FunDecl :=
  { name    := { name := "hkdf_copy_prev" }
  , params  := [u8ArrParam "prev" 32, u8ArrParam "dest" 4096]
  , body    := copyPrevBody
  , results := []
  }

/-! ## §3.  Hand-glue (HKDF orchestration). -/

def hkdfGlue : String :=
  "// ---- hand-glue for HKDF-SHA-256 (not Lean-emitted) ----\n" ++
  "// `hmac_sha256` and `sha256` are expected to be in scope from\n" ++
  "// `hmac_sha256_jasmin.rs`.  `hkdf_copy_prev` is the Lean-emitted\n" ++
  "// helper above.\n\n" ++
  "/// HKDF-Extract per RFC 5869 §2.2.  Returns a 32-byte PRK.\n" ++
  "pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {\n" ++
  "    // RFC 5869: if salt is empty, treat it as 32 zero bytes.\n" ++
  "    if salt.is_empty() {\n" ++
  "        let zero = [0u8; 32];\n" ++
  "        hmac_sha256(&zero, ikm)\n" ++
  "    } else {\n" ++
  "        hmac_sha256(salt, ikm)\n" ++
  "    }\n" ++
  "}\n\n" ++
  "/// HKDF-Expand per RFC 5869 §2.3.  Returns `length` bytes.\n" ++
  "/// Caller's responsibility: `length <= 255 * 32`.\n" ++
  "pub fn hkdf_expand(prk: &[u8; 32], info: &[u8], length: usize) -> Vec<u8> {\n" ++
  "    assert!(length <= 255 * 32, \"HKDF-Expand length too large\");\n" ++
  "    let n = (length + 31) / 32;  // number of 32-byte blocks\n" ++
  "    let mut out: Vec<u8> = Vec::with_capacity(length);\n" ++
  "    let mut prev = [0u8; 32];\n" ++
  "    let mut prev_len = 0usize;\n" ++
  "    for i in 1..=n {\n" ++
  "        // Build buf = T(i-1) || info || (i as u8).\n" ++
  "        // Use the Lean-emitted `hkdf_copy_prev` for the prefix on\n" ++
  "        // iterations 2..n (i=1 has prev_len=0).\n" ++
  "        let mut buf: Vec<u8> = Vec::new();\n" ++
  "        if prev_len == 32 {\n" ++
  "            let mut staging = [0u8; 4096];\n" ++
  "            hkdf_copy_prev(&prev, &mut staging);\n" ++
  "            buf.extend_from_slice(&staging[..32]);\n" ++
  "        }\n" ++
  "        buf.extend_from_slice(info);\n" ++
  "        buf.push(i as u8);\n" ++
  "        let t = hmac_sha256(prk, &buf);\n" ++
  "        prev = t;\n" ++
  "        prev_len = 32;\n" ++
  "        let take = (length - out.len()).min(32);\n" ++
  "        out.extend_from_slice(&t[..take]);\n" ++
  "    }\n" ++
  "    out\n" ++
  "}\n"

/-! ## §4.  Emit -/

def copyPrevOverrides : List (String × String) :=
  [ ("prev", "&[u8; 32]")
  , ("dest", "&mut [u8; 4096]") ]

def emitHkdfAst : String :=
  ppFunDeclWith copyPrevOverrides [] [] copyPrevFd

def emitWithoutHmac : String :=
  emitHkdfAst ++ "\n\n" ++ hkdfGlue

/-- Library entry point.  Reads the HMAC bundle (which itself contains
    the SHA-256 primitives) from `/tmp/hmac_sha256_jasmin.rs` and
    appends the HKDF AST + glue. -/
def runEmit : IO Unit := do
  let hmacPath := "/tmp/hmac_sha256_jasmin.rs"
  let outPath := "/tmp/hkdf_sha256_jasmin.rs"
  let hmacSrc ←
    if ← System.FilePath.pathExists hmacPath then
      IO.FS.readFile hmacPath
    else
      pure "// (hmac_sha256_jasmin.rs not found — run HmacSha256JasminEmit first)\n"
  IO.FS.writeFile outPath (hmacSrc ++ "\n\n" ++ emitWithoutHmac)
  IO.println s!"wrote {outPath}"

end CatCrypt.Crypto.Jasmin.Examples.HkdfSha256Jasmin
