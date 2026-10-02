/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors

# `Scalar25519` operations as Lean `LowCT` ASTs.

Source: `curve25519-jasmin-rs/src/scalar25519.rs`.

Six Curve25519-scalar-field operations authored as standalone `LowCT`
bodies, each emitted to Rust via `RustEmit.ppRustFunction`.  All
operate over fiat-crypto's `curve25519_scalar_64` Montgomery-domain
representation (`TFpL25519`); the byte-canonical `[u8; 32]` boundary is
hit only by `from_bytes_mod_order_emit` (32 bytes -> Mont) and
`to_bytes_emit` (Mont -> 32 bytes).

The wide-reduction `from_bytes_mod_order_wide` is NOT a single AST — it
is composed in the Rust shim from the 6 primitives below.  The split is
deliberate: `from_bytes_mod_order_wide`'s 64-byte input needs to be
sliced into two 32-byte halves, and the IR (TBytes / TArr) does not
expose byte-range slicing.  Per the task's "Hax-readiness" constraint
(no IR hacks), we stop at the primitives.

## Leaves used

Each per-method body is ONE `RCall` to a fiat-crypto wrapper provided
by the consumer Rust module:

  * `scalar25519_bytes_to_mont (out a)`     — from_bytes + to_montgomery
  * `scalar25519_mont_to_bytes (out a)`     — from_montgomery + to_bytes
  * `scalar25519_mul_mont (out a b)`        — fiat_25519_scalar_mul
  * `scalar25519_add_mont (out a b)`        — fiat_25519_scalar_add
  * `scalar25519_sub_mont (out a b)`        — fiat_25519_scalar_sub
  * `scalar25519_opp_mont (out a)`          — fiat_25519_scalar_opp

The shim defines them as 1-3-line wrappers over fiat-crypto's verified
`curve25519_scalar_64` primitives.

## Why all-AST-trivial?

Each AST is a single leaf call.  This is intentional: per the task
spec, we author the Scalar25519 method *bodies* as LowCT ASTs.  The
bodies are by design thin wrappers — the cryptographic work happens
inside fiat-crypto.  What the AST guarantees is the structural shape
of each method: exactly one fiat-crypto call, with the expected
in/out slot types.  Composition (e.g. wide-reduction) is then a Rust
shim concern, not an AST extension.
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCTExec
public import CatCrypt.Crypto.Jasmin.RustEmit


@[expose] public section
namespace CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops

open CatCrypt.Crypto.Jasmin.LowCT

/-- A `TFpL25519` (Mont-domain scalar) slot. -/
def scalar (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TFpL25519 }

/-- A `TBytes 32` slot. -/
def bytes32 (v : String) : Located :=
  { locVar := v, locSrc := TowerType.TBytes 32 }

/-! ## §1.  `from_bytes_mod_order` body

  Reads input `bytes_in : [u8; 32]`, writes `out : FpL25519`.
  Single leaf call: bytes -> non-Mont -> Mont. -/

def fromBytesModOrderBody : LowCT :=
  LowCT.RCall "scalar25519_bytes_to_mont" (scalar "out") [bytes32 "bytes_in"]

def fromBytesModOrderParams  : List Located := [ bytes32 "bytes_in" ]
def fromBytesModOrderResults : List Located := [ scalar "out" ]

def emitFromBytesModOrder (_ : Unit) : String :=
  ppRustFunction "scalar25519_from_bytes_mod_order_emit"
    fromBytesModOrderParams fromBytesModOrderResults fromBytesModOrderBody

/-! ## §2.  `to_bytes` body

  Reads `mont : FpL25519`, writes `out : [u8; 32]`.
  Single leaf call: Mont -> non-Mont -> bytes. -/

def toBytesBody : LowCT :=
  LowCT.RCall "scalar25519_mont_to_bytes" (bytes32 "out") [scalar "mont"]

def toBytesParams  : List Located := [ scalar "mont" ]
def toBytesResults : List Located := [ bytes32 "out" ]

def emitToBytes (_ : Unit) : String :=
  ppRustFunction "scalar25519_to_bytes_emit"
    toBytesParams toBytesResults toBytesBody

/-! ## §3.  `mul` body

  Reads `a, b : FpL25519` (both Mont), writes `out : FpL25519` (Mont).
  Single leaf call: Mont * Mont -> Mont (REDC inside fiat). -/

def mulBody : LowCT :=
  LowCT.RCall "scalar25519_mul_mont" (scalar "out") [scalar "a", scalar "b"]

def mulParams  : List Located := [ scalar "a", scalar "b" ]
def mulResults : List Located := [ scalar "out" ]

def emitMul (_ : Unit) : String :=
  ppRustFunction "scalar25519_mul_emit"
    mulParams mulResults mulBody

/-! ## §4.  `add` body -/

def addBody : LowCT :=
  LowCT.RCall "scalar25519_add_mont" (scalar "out") [scalar "a", scalar "b"]

def emitAdd (_ : Unit) : String :=
  ppRustFunction "scalar25519_add_emit"
    mulParams mulResults addBody

/-! ## §5.  `sub` body -/

def subBody : LowCT :=
  LowCT.RCall "scalar25519_sub_mont" (scalar "out") [scalar "a", scalar "b"]

def emitSub (_ : Unit) : String :=
  ppRustFunction "scalar25519_sub_emit"
    mulParams mulResults subBody

/-! ## §6.  `negate` body

  Reads `a : FpL25519`, writes `out : FpL25519`. -/

def negateBody : LowCT :=
  LowCT.RCall "scalar25519_opp_mont" (scalar "out") [scalar "a"]

def negateParams  : List Located := [ scalar "a" ]
def negateResults : List Located := [ scalar "out" ]

def emitNegate (_ : Unit) : String :=
  ppRustFunction "scalar25519_negate_emit"
    negateParams negateResults negateBody

/-! ## §7.  Driver -/

/-- Concatenate all 6 emitted function bodies into a single Rust source
    blob, separated by blank lines. -/
def emitAll (_ : Unit) : String :=
  emitFromBytesModOrder () ++ "\n\n" ++
  emitToBytes ()           ++ "\n\n" ++
  emitMul ()               ++ "\n\n" ++
  emitAdd ()               ++ "\n\n" ++
  emitSub ()               ++ "\n\n" ++
  emitNegate ()

def runEmit : IO Unit := do
  let outPath := "/tmp/scalar25519_emitted.rs"
  let s := emitAll ()
  IO.FS.writeFile outPath s
  IO.println s!"wrote {outPath}"
  IO.println s!"({s.length} bytes)"
  IO.println "---"
  IO.println s

end CatCrypt.Crypto.Jasmin.Examples.Scalar25519Ops
