/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.SHAKE128
public import CatCrypt.Crypto.Primitives.KeccakArray
public import CatCrypt.Crypto.Primitives.BLAKE2s
public import CatCryptCore.Crypto.KeyAgreement.Curve25519

/-!
# Known-answer runner for the Lean hash and key-agreement specifications

`lake exe spec-kat --only <row>` reads the vector file of one row at run time and compares the
Lean specification with the vectors. The rows are

* `shake128`: `SHAKE128.shake128` and `KeccakSponge.shake128` against NIST CAVP
  `SHAKE128ShortMsg.rsp`;
* `shake256`: `KeccakSponge.shake256` against NIST CAVP `SHAKE256ShortMsg.rsp`;
* `sha3_256`: `KeccakSponge.sha3_256` against NIST CAVP `SHA3_256ShortMsg.rsp`;
* `blake2s`: `BLAKE2s.blake2s` against RFC 7693, Appendix B;
* `x25519`: the x-only Montgomery ladder `xladderFold` with the parameters of
  `curve25519Params`, driven by the RFC 7748 scalar clamping, u-coordinate decoding and final
  inversion, against RFC 7748, Section 5.2 (two vectors, the 1-iteration and the
  1,000-iteration results).

The closure state of `Keccak.keccakF` makes the compiled permutation exponential in the number of
rounds, so this module imports `KeccakArray`: its `@[csimp]` equalities, proved in that module,
compile the four sponge functions above to their array forms.

The vector files are in `bench/spec_kat/vectors/`, resolved from the working directory and, for a
run from the workspace root, from `../catcrypt-compiler/`. The output has one line per vector,
`ok <index>` or `FAIL <index>`, and a summary line. The exit code is `0` when every vector
matches, `1` when a vector differs, and `2` for a usage, file or parse error.

## Main definitions

* `parseNist`: the vectors of a CAVP `.rsp` file.
* `runNist`, `runBlake2s`, `runX25519`: the rows.
* `x25519Bytes`: RFC 7748 X25519 on byte strings over `xladderFold`.
* `runRow`, `main`: the dispatch of `--only <row>` and `--list`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SpecKat

open CatCrypt.Crypto.ECC

/-- The value of one hexadecimal digit. -/
def hexNib (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Decode a list of hexadecimal digits into bytes. -/
def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let x ← hexNib a
    let y ← hexNib b
    let r ← hexBytes rest
    pure ((x * 16 + y).toUInt8 :: r)

/-- Decode a hexadecimal string into bytes. -/
def parseHex (s : String) : Option (List UInt8) := hexBytes s.toList

/-- The lower-case hexadecimal digit of a number below 16. -/
def hexDigit (n : Nat) : Char := Nat.digitChar n

/-- Render bytes as lower-case hexadecimal. -/
def toHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- One NIST CAVP vector: the message truncated to `Len / 8` bytes and the expected output. -/
structure NistVec where
  /-- The message bytes. -/
  msg : List UInt8
  /-- The expected digest or XOF output. -/
  out : List UInt8

/-- Parse a CAVP `.rsp` text (`Len`, `Msg`, then `Output` or `MD` per vector). -/
def parseNist (text : String) : Except String (Array NistVec) := do
  let mut acc : Array NistVec := #[]
  let mut len : Option Nat := none
  let mut msg : Option (List UInt8) := none
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" || line.startsWith "[" then continue
    match line.splitOn "=" with
    | [k, v] =>
      let k := k.trimAscii.toString
      let v := v.trimAscii.toString
      if k == "Len" then len := v.toNat?
      else if k == "Msg" then msg := parseHex v
      else if k == "Output" || k == "MD" then
        match len, msg, parseHex v with
        | some l, some m, some o => acc := acc.push ⟨m.take (l / 8), o⟩
        | _, _, _ => throw s!"malformed vector after {acc.size} vectors"
    | _ => throw s!"unparsable line: {line}"
  pure acc

/-- Read a vector file by its name in `bench/spec_kat/vectors/`, from the working directory or
from the sibling checkout `../catcrypt-compiler/`. -/
def readVectors (file : String) : IO (Option String) := do
  let rel := s!"bench/spec_kat/vectors/{file}"
  for base in ["", "../catcrypt-compiler/"] do
    let p : System.FilePath := base ++ rel
    if ← p.pathExists then
      return some (← IO.FS.readFile p)
  pure none

/-- Print the line for vector `i` and return `true` when `got = want`. -/
def report (row : String) (i : Nat) (label : String) (got want : List UInt8) : IO Bool := do
  if got == want then
    IO.println s!"ok {i} {label}"
    pure true
  else
    IO.println s!"FAIL {i} {label} got {toHex got} want {toHex want}"
    IO.eprintln s!"{row}: vector {i} ({label}) differs"
    pure false

/-- Print the summary line and return the exit code. -/
def summary (row : String) (total bad : Nat) : IO UInt32 := do
  IO.println s!"# {row}: {total - bad} of {total} vectors match"
  pure (if bad == 0 ∧ total > 0 then 0 else 1)

/-- Check a hash row: each implementation, given message and output length, against every vector of
a CAVP file. -/
def runNist (row file : String) (impls : List (String × (List UInt8 → Nat → List UInt8))) :
    IO UInt32 := do
  let some text ← readVectors file
    | IO.eprintln s!"{row}: vector file {file} not found"; pure 2
  match parseNist text with
  | .error e => IO.eprintln s!"{row}: {e}"; pure 2
  | .ok vs =>
    let mut total := 0
    let mut bad := 0
    for h : i in [0:vs.size] do
      for (label, f) in impls do
        total := total + 1
        let v := vs[i]
        if !(← report row i label (f v.msg v.out.length) v.out) then bad := bad + 1
    summary row total bad

/-- The key-value pairs `key = value` of a vector file, comments skipped. -/
def parsePairs (text : String) : List (String × String) :=
  (text.splitOn "\n").filterMap fun raw =>
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn "=" with
      | k :: rest => some (k.trimAscii.toString, ("=".intercalate rest).trimAscii.toString)
      | [] => none

/-- Check the BLAKE2s row against the RFC 7693 file. -/
def runBlake2s : IO UInt32 := do
  let row := "blake2s"
  let some text ← readVectors "rfc7693_blake2s.txt"
    | IO.eprintln s!"{row}: vector file not found"; pure 2
  match (parsePairs text).lookup "msg" >>= parseHex, (parsePairs text).lookup "hash" >>= parseHex
  with
  | some m, some h =>
    let ok ← report row 0 "blake2s" (CatCrypt.Crypto.Primitives.BLAKE2s.blake2s m) h
    summary row 1 (if ok then 0 else 1)
  | _, _ => IO.eprintln s!"{row}: malformed vector file"; pure 2

/-- The little-endian number of a byte list. -/
def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The `n` low-order bytes of `x`, least significant first. -/
def natLE (n x : Nat) : List UInt8 := (List.range n).map fun i => (x / 256 ^ i % 256).toUInt8

/-- `a ^ e` in `Fp25519` by square and multiply, over the bits of `e` from the least significant. -/
def powFp (a : Fp25519) (e : Nat) : Fp25519 := Id.run do
  let mut result : Fp25519 := 1
  let mut base := a
  let mut k := e
  while k > 0 do
    if k % 2 == 1 then result := result * base
    base := base * base
    k := k / 2
  pure result

/-- RFC 7748 `decodeScalar25519`: clear the three low bits, clear bit 255, set bit 254. -/
def clampScalar (k : List UInt8) : Nat :=
  (leNat k &&& (2 ^ 254 - 8)) ||| 2 ^ 254

/-- X25519 on 32-byte strings: the scalar is clamped and the u-coordinate has bit 255 cleared; the
x-only ladder `xladderFold` over `Fp25519` with `curve25519Params` runs on the 255 bits of the
scalar, and the projective result `(X, Z)` is returned as `X · Z^(p-2)` in 32 little-endian
bytes. -/
def x25519Bytes (k u : List UInt8) : List UInt8 :=
  let s := clampScalar k
  let uF : Fp25519 := ((leNat u % 2 ^ 255 : Nat) : Fp25519)
  let bits : List Bool := (List.range 255).map fun i => s.testBit i
  let R := (xladderFold (curve25519Params Fp25519).a24 (uF, 1) bits).1
  let x := R.1 * powFp R.2 (curve25519Prime - 2)
  natLE 32 (ZMod.val x)

/-- `n` iterations of the RFC 7748 chain `(k, u) := (X25519 k u, k)`, starting at `k = u = k0`. -/
def x25519Iter (k0 : List UInt8) : Nat → List UInt8
  | n => Id.run do
    let mut k := k0
    let mut u := k0
    for _ in [0:n] do
      let r := x25519Bytes k u
      u := k
      k := r
    pure k

/-- Check the X25519 row against the RFC 7748 file. -/
def runX25519 : IO UInt32 := do
  let row := "x25519"
  let some text ← readVectors "rfc7748_x25519.txt"
    | IO.eprintln s!"{row}: vector file not found"; pure 2
  let mut total := 0
  let mut bad := 0
  let mut bad2 := false
  let mut sc : Option (List UInt8) := none
  let mut uc : Option (List UInt8) := none
  for (k, v) in parsePairs text do
    if k == "scalar" then sc := parseHex v
    else if k == "u" then uc := parseHex v
    else if k == "out" then
      match sc, uc, parseHex v with
      | some s, some u, some o =>
        if !(← report row total "rfc7748-5.2" (x25519Bytes s u) o) then bad := bad + 1
        total := total + 1
      | _, _, _ => bad2 := true
    else if k == "iter" then
      match v.splitOn " " with
      | [n, k0, o] =>
        match n.toNat?, parseHex k0, parseHex o with
        | some n, some k0, some o =>
          if !(← report row total s!"iterations-{n}" (x25519Iter k0 n) o) then bad := bad + 1
          total := total + 1
        | _, _, _ => bad2 := true
      | _ => bad2 := true
  if bad2 then
    IO.eprintln s!"{row}: malformed vector file"
    pure 2
  else summary row total bad

/-- The row ids. -/
def rows : List String := ["shake128", "shake256", "sha3_256", "blake2s", "x25519"]

/-- Run one row. -/
def runRow : String → IO UInt32
  | "shake128" =>
    runNist "shake128" "SHAKE128ShortMsg.rsp"
      [("SHAKE128.shake128", CatCrypt.Crypto.Primitives.SHAKE128.shake128),
       ("KeccakSponge.shake128", CatCrypt.Crypto.Primitives.KeccakSponge.shake128)]
  | "shake256" =>
    runNist "shake256" "SHAKE256ShortMsg.rsp"
      [("KeccakSponge.shake256", CatCrypt.Crypto.Primitives.KeccakSponge.shake256)]
  | "sha3_256" =>
    runNist "sha3_256" "SHA3_256ShortMsg.rsp"
      [("KeccakSponge.sha3_256", fun m _ => CatCrypt.Crypto.Primitives.KeccakSponge.sha3_256 m)]
  | "blake2s" => runBlake2s
  | "x25519" => runX25519
  | r => do
    IO.eprintln s!"spec-kat: unknown row {r}"
    pure 2

end CatCrypt.Crypto.Primitives.SpecKat

/-- The entry point of `lake exe spec-kat --only <row>` (rows: `--list`). -/
def main (args : List String) : IO UInt32 :=
  match args with
  | ["--list"] => do
    for r in CatCrypt.Crypto.Primitives.SpecKat.rows do IO.println r
    pure 0
  | "--only" :: row :: _ => CatCrypt.Crypto.Primitives.SpecKat.runRow row
  | _ => do
    IO.eprintln "usage: spec-kat --only <shake128|shake256|sha3_256|blake2s|x25519> | --list"
    pure 2
