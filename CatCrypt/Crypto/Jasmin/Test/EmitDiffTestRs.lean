/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.BignumExecDiffTest

@[expose] public section

set_option autoImplicit false

/-!
# Rust harness emitter for `BignumExec` differential test cases

`lake env lean --run ...` (or via a `lake exe` target) emits a complete
Rust harness file per test case for the C-side gate in
`scripts/diff_bignum_sem.sh`. The harness:

1. Allocates a 64KB byte buffer (test addresses are offsets in).
2. Pre-populates the bytes specified by `initMem`.
3. Calls the linked `extern "C"` routine using `initRegs` for pointer
   args (treated as offsets into the buffer).
4. Compares the resulting buffer at the `expectedMem` addresses.
5. Returns exit code 0 (PASS) or 1 (FAIL).

Build with:
```
rustc -C opt-level=2 -L<port-dir> -l<port_name> /tmp/<case>.rs -o /tmp/<case>
```
Run: `./tmp/<case>; echo $?`.

## Why Rust, not C / JSON

Single source-of-truth flow: Lean test case → Rust source → rustc →
binary. No runtime parsing, no separate harness boilerplate. Rust's
`extern "C"` calls jasminc's SysV-ABI assembly identically to C, but
the `unsafe` boundaries make memory ownership explicit so harness
bugs surface at compile time. Long-term fit: when AUCurves Phase 1.5
lands and emits verified Rust, the same harness shape calls it as
plain Rust without an FFI cross.

## Buffer layout

The Rust harness uses one 64KB stack buffer (`[u8; 65536]`) and
treats each `initMem.addr` and each `initRegs.value` as a u8 offset
into that buffer. Caveat: test addresses must fit in `[0, 65536)`.
The two existing test cases (`tcModCanonical` at base 0x1000/0x2000,
`tcModAboveP` at 0x3000/0x4000) fit comfortably.
-/

namespace CatCrypt.Crypto.Jasmin.Test.EmitDiffTestRs

open CatCrypt.Crypto.Jasmin.BignumExecDiffTest

/-! ## §1. Helpers -/

/-- Hex-format a `Nat` with leading `0x`. -/
def hexNat (n : Nat) : String :=
  "0x" ++ (Nat.toDigits 16 n |> String.ofList)

/-- Hex-format a `UInt8` zero-padded to 2 hex digits. -/
def hexU8 (v : UInt8) : String :=
  let n := v.toNat
  let s := Nat.toDigits 16 n |> String.ofList
  "0x" ++ (if n < 0x10 then "0" ++ s else s)

/-- Hex-format a `UInt64` with `0x` prefix. -/
def hexU64 (v : UInt64) : String := hexNat v.toNat

/-- Generate the `extern "C"` declaration for a port name. The two
    pointer-ABI shapes we ship today are:
      - one-arg:  `bignum_<x>(op, ap)` for unary routines.
      - two-arg:  `bignum_<x>(op, ap, bp)` for binary routines. -/
def externDecl (portName : String) : String :=
  match portName with
  | "bignum_mod_p25519_4"
  | "bignum_double_p25519"
  | "bignum_inv_p25519"
  | "bignum_sqr_4" =>
    "extern \"C\" {\n" ++
    "    fn " ++ portName ++ "(op: *mut u64, ap: *const u64);\n" ++
    "}\n"
  | "bignum_add_4"
  | "bignum_mul_4"
  | "bignum_mul_4_adcx"
  | "bignum_sub_p25519"
  | "bignum_montmul_p25519" =>
    "extern \"C\" {\n" ++
    "    fn " ++ portName ++ "(op: *mut u64, ap: *const u64, bp: *const u64);\n" ++
    "}\n"
  | _ =>
    "extern \"C\" {\n" ++
    "    fn " ++ portName ++ "();  // unknown ABI — TODO\n" ++
    "}\n"

/-- The unsafe call site for a port. Uses `ap`/`bp`/`op` local
    variables defined in the harness's `main` body. -/
def callSite (portName : String) : String :=
  match portName with
  | "bignum_mod_p25519_4"
  | "bignum_double_p25519"
  | "bignum_inv_p25519"
  | "bignum_sqr_4" =>
    "    unsafe { " ++ portName ++ "(op, ap); }\n"
  | _ =>
    "    unsafe { " ++ portName ++ "(op, ap, bp); }\n"

/-! ## §2. Main emitter -/

/-- Emit the `initMem` writes (one statement per byte). -/
def emitInitMem (entries : List (UInt64 × UInt8)) : String :=
  entries.foldl (init := "") fun acc ⟨addr, byte⟩ =>
    acc ++ "    mem[" ++ hexU64 addr ++ "] = " ++ hexU8 byte ++ ";\n"

/-- Emit register-as-pointer-into-mem aliases. -/
def emitRegAliases (regs : List (String × UInt64)) : String :=
  regs.foldl (init := "") fun acc ⟨name, off⟩ =>
    let mut_qual := if name = "op" then "_mut_ptr().add" else "_ptr().add"
    let cast := if name = "op" then "*mut u64" else "*const u64"
    acc ++ "    let " ++ name ++ " = unsafe { mem.as" ++ mut_qual ++
           "(" ++ hexU64 off ++ ") } as " ++ cast ++ ";\n"

/-- Emit the expected-byte slice as a `[u8; N]` literal + addr offset
    of the first byte (for `from_raw_parts`). The harness then reads
    `expectedMem.size` bytes starting at the same offset and memcmp's. -/
def emitExpectedCheck (entries : List (UInt64 × UInt8)) : String :=
  match entries with
  | [] => "    // expectedMem empty — nothing to check.\n"
  | first :: _ =>
    let firstAddr := first.1
    let bytesLit := entries.map (fun ⟨_, b⟩ => hexU8 b)
                    |> String.intercalate ", "
    let n := entries.length
    "    let expected: [u8; " ++ toString n ++ "] = [" ++ bytesLit ++ "];\n" ++
    "    let actual = unsafe {\n" ++
    "        std::slice::from_raw_parts(\n" ++
    "            mem.as_ptr().add(" ++ hexU64 firstAddr ++ "),\n" ++
    "            " ++ toString n ++ ",\n" ++
    "        )\n" ++
    "    };\n" ++
    "    if actual != &expected[..] {\n" ++
    "        eprintln!(\"FAIL: expected {:?}, got {:?}\", &expected[..], actual);\n" ++
    "        return 1;\n" ++
    "    }\n"

/-- Render a complete Rust harness for a `TestCase`. -/
def emitHarness (tc : TestCase) : String :=
  "// Auto-generated diff-test harness. Do not edit by hand.\n" ++
  "// Lean source: CatCrypt.Crypto.Jasmin.BignumExecDiffTest." ++ tc.portName ++ "\n" ++
  "\n" ++
  externDecl tc.portName ++
  "\n" ++
  "fn run() -> i32 {\n" ++
  "    let mut mem: [u8; 65536] = [0u8; 65536];\n\n" ++
  "    // initMem\n" ++
  emitInitMem tc.initMem ++
  "\n    // initRegs as pointer-into-mem aliases\n" ++
  emitRegAliases tc.initRegs ++
  "\n    // call the routine\n" ++
  callSite tc.portName ++
  "\n    // expectedMem comparison\n" ++
  emitExpectedCheck tc.expectedMem ++
  "    0\n" ++
  "}\n\n" ++
  "fn main() {\n" ++
  "    std::process::exit(run());\n" ++
  "}\n"

/-! ## §3. Lookup + main entry -/

def lookupCase : String → Option TestCase
  | "tcModCanonical"             => some tcModCanonical
  | "tcModAboveP"                => some tcModAboveP
  | "tcAdd4Small"                => some tcAdd4Small
  | "tcSubP25519Small"           => some tcSubP25519Small
  | "tcDoubleP25519Small"        => some tcDoubleP25519Small
  | "tcMul4Small"                => some tcMul4Small
  | "tcMul4AdcxSmall"            => some tcMul4AdcxSmall
  | "tcSqr4Small"                => some tcSqr4Small
  | "tcMontMulSmall"             => some tcMontMulSmall
  | "tcInvP25519"                => some tcInvP25519
  | _                            => none

def main' (args : List String) : IO Unit := do
  match args with
  | []         => IO.eprintln "missing case name"
  | name :: _  =>
    match lookupCase name with
    | some tc => IO.println (emitHarness tc)
    | none    => IO.eprintln ("unknown case: " ++ name)

/-! ## §4. Smoke (truncated; the full output is ~150 lines per case) -/

end CatCrypt.Crypto.Jasmin.Test.EmitDiffTestRs

/-- Top-level `main` so `lake env lean --run` finds it. -/
def main (args : List String) : IO Unit :=
  CatCrypt.Crypto.Jasmin.Test.EmitDiffTestRs.main' args
