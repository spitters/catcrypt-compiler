/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminEmit
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

set_option autoImplicit false

/-!
# Per-port `.jazz` emitter for the diff-test gate

`lake env lean --run [...]/EmitPortJazz.lean -- <port_name>` prints
the Jasmin source for the named port on stdout. Consumed by
`scripts/diff_bignum_sem.sh` stage 2:

```
$ lake env lean --run [...]/EmitPortJazz.lean bignum_mod_p25519_4 \
    > /tmp/bignum_mod_p25519_4.jazz
$ jasminc /tmp/bignum_mod_p25519_4.jazz -o /tmp/bignum_mod_p25519_4.s
$ clang -c /tmp/bignum_mod_p25519_4.s -o /tmp/bignum_mod_p25519_4.o
```

This is the inverse of the `BignumExec`-Lean-side path: same
`FunDecl` body, traversed by `JasminEmit.emitFunDecl` to produce
the source string that jasminc compiles. The differential test
gate confirms the two paths agree on output bytes.
-/

namespace CatCrypt.Crypto.Jasmin.Test.EmitPortJazz

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-- Map a port name to its `FunDecl`. Add new ports here as they
    land in `S2NBignumSSA.lean`. -/
def lookupPort : String → Option FunDecl
  | "bignum_add_2"          => some BignumAdd2.fd
  | "bignum_add_4"          => some BignumAdd4.fd
  | "bignum_mul_4"          => some BignumMul4.fd
  | "bignum_mul_4_adcx"     => some BignumMul4Adcx.fd
  | "bignum_sub_p25519"     => some BignumSubP25519.fd
  | "bignum_double_p25519"  => some BignumDoubleP25519.fd
  | "bignum_sqr_4"          => some BignumSqr4.fd
  | "bignum_mod_p25519_4"   => some BignumModP25519_4.fd
  | "bignum_montmul_p25519" => some BignumMontMulP25519_4.fd
  | "bignum_inv_p25519"     => some BignumInvP25519.fd
  | _                       => none

/-! ### Ccall demo

A two-function `.jazz` exercising the new `Ccall` emit case: a
non-export helper `ccall_demo_helper` that adds two u64s, plus an
exported `ccall_demo_caller` that calls it once. Used by the
`scripts/test_ccall_emit.sh` driver to verify jasminc accepts the
emitted call syntax end-to-end (Lean → .jazz → jasminc → .s).

The two `FunDecl`s are emitted into a single `.jazz` source string
because jasminc requires the callee to be declared in the same
compilation unit as the caller. -/

namespace CcallDemo

private def v' (s : String) : Var := { vname := s, vtype := .sword .U64 }
private def lvR (s : String) : LVal := .Lvar { var := v' s }
private def pv (s : String) : PExpr := .Pvar { gv := { var := v' s }, gs := false }

/-- Helper: `r = a + b` (non-export, callable). Body uses the
    standard `r = a; r += b;` 2-operand pattern. -/
def helperFd : FunDecl where
  name := { name := "ccall_demo_helper" }
  params := [⟨{ var := v' "a" }⟩, ⟨{ var := v' "b" }⟩]
  body :=
    [ .Cassgn (lvR "r") .AT_none (.sword .U64) (pv "a")
    , .Cassgn (lvR "r") .AT_none (.sword .U64)
        (.Papp2 (.Oadd .U64) (pv "r") (pv "b")) ]
  results := [{ var := v' "r" }]

/-- Caller: `r = ccall_demo_helper(x, y);`. Demonstrates a Ccall
    with a single LVal output and two PVar arguments. -/
def callerFd : FunDecl where
  name := { name := "ccall_demo_caller" }
  params := [⟨{ var := v' "x" }⟩, ⟨{ var := v' "y" }⟩]
  body :=
    [ .Ccall .DoNotInline [lvR "r"]
        { name := "ccall_demo_helper" } [pv "x", pv "y"] ]
  results := [{ var := v' "r" }]

end CcallDemo

/-- Emit the Ccall demo as a single `.jazz` source string with both
    functions. Returns `none` if either emit fails. -/
def emitCcallDemo : Option String := do
  -- Helper must come first so jasminc sees its declaration before the call.
  let helper ← Emit.emitFunDecl CcallDemo.helperFd
  let caller ← Emit.emitFunDecl CcallDemo.callerFd
  -- The `helper` function should not be `export` so jasminc can inline it
  -- locally; for the demo we emit it with the default `export` modifier
  -- (jasminc accepts both forms — extern-linked or in-unit).
  some (helper ++ "\n" ++ caller)

/-! ### Combined emission for Ccall-using ports

When a port body contains `Ccall`s, jasminc needs the callee declared
in the same compilation unit as the caller. The driver below bundles
each Ccall-using port with its transitive callees. -/

/-- Emit `bignum_inv_p25519` together with its single callee
    `bignum_montmul_p25519`. Mirror of `emitCcallDemo` for the
    real port.

    The callee `bignum_montmul_p25519` is emitted as a non-export
    `fn` (rather than `export fn`) so that jasminc treats it as an
    internal function with a real call instruction, rather than
    inlining all 254 callsites into `bignum_inv_p25519` (which
    blows up the register allocator). -/
def emitInvP25519Combined : Option String := do
  let mm ← Emit.emitFunDecl BignumMontMulP25519_4.fd
  let inv ← Emit.emitFunDecl BignumInvP25519.fd
  -- Replace the leading `export fn bignum_montmul_p25519` with `fn`
  -- to suppress jasminc's inline-everything-export-callee behavior.
  let mmNonExport := mm.replace "export fn bignum_montmul_p25519"
                                 "fn bignum_montmul_p25519"
  some (mmNonExport ++ "\n" ++ inv)

def main' (args : List String) : IO Unit := do
  match args with
  | [] =>
    IO.eprintln "missing port name"
  | "ccall_demo" :: _ =>
    match emitCcallDemo with
    | none     => IO.eprintln "emit failed: ccall_demo"
    | some src => IO.println src
  | "bignum_inv_p25519" :: _ =>
    -- Special-case: emit both the callee (`bignum_montmul_p25519`)
    -- and the caller (`bignum_inv_p25519`) into a single `.jazz`.
    match emitInvP25519Combined with
    | none     => IO.eprintln "emit failed: bignum_inv_p25519 (combined)"
    | some src => IO.println src
  | name :: _ =>
    match lookupPort name with
    | none => IO.eprintln ("unknown port: " ++ name)
    | some fd =>
      match Emit.emitFunDecl fd with
      | none =>
        IO.eprintln ("emit failed: " ++ name)
      | some src => IO.println src

end CatCrypt.Crypto.Jasmin.Test.EmitPortJazz

/-- Top-level `main` so `lake env lean --run` finds it. -/
private def main (args : List String) : IO Unit :=
  CatCrypt.Crypto.Jasmin.Test.EmitPortJazz.main' args
