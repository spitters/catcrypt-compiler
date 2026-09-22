/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddEmit
public import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

@[expose] public section

set_option autoImplicit false

/-!
# The ed25519 point addition as a verified-encoder ELF object

`crates/catcrypt-ed25519` links the extended-coordinate addition
`ed25519_point_add`. This module byte-encodes it with
`LprogBytes.encodeLprogChecked` into a single-symbol ELF64 relocatable object,
so the crate links the encoder's bytes with no assembler hop.

The program encoded is the one `Ed25519PointAdd.pointAddAsm` prints: the
exported `pointAddLprog` through `FheMontMulEmit.fuseMulHiLprog`,
`LprogOptPipeline.optimizeLprogBasicBlocks` and `StackZeroize.zeroizeLprog`,
which are the three passes `LprogOptPipeline.renderOwnedZeroized` applies
before the AT&T printer. The text file
`crates/catcrypt-ed25519/asm/ed25519_point_add_x86_from_lean.s` is the printer's
rendering of that same program, and stays in the crate as the comparison
oracle for the object's `.text`.

The evaluation below is a permanent static check: it fails the build when a
body instruction falls outside the encoder's fragment, pinning the artifact
against an encoder or pipeline change that would leave the crate without an
object. It decides `LprogBytes.encodableLcmd` over the body and does not
materialize the byte list.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Ed25519BytesEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-- The point-addition program the crate ships: `pointAddLprog` after the MULX
    fusion pass, the basic-block optimizer and the frame-clearing pass. -/
def pointAddShippedLprog : Lprog :=
  StackZeroize.zeroizeLprog
    (LprogOptPipeline.optimizeLprogBasicBlocks
      (FheMontMulEmit.fuseMulHiLprog
        CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd.pointAddLprog))

/-- The gated object bytes of an `Lprog`: `none` when a body instruction is
    outside the encoder fragment. -/
def objBytes (p : Option Lprog) : Option (List (BitVec 8)) :=
  p.bind encodeLprogChecked

/-- The kernels, keyed by the object name `crates/catcrypt-ed25519/build.rs`
    archives; the object defines the symbol named by its `Lprog`. -/
def kernels : List (String × Option Lprog) :=
  [("ed25519_point_add_owned", some pointAddShippedLprog)]

-- Fails the build when the point-addition body leaves the encoder fragment.
#eval (do
  unless (objBytes (some pointAddShippedLprog)).isSome do
    throw (IO.userError "point addition: body outside the byte-encoder fragment") : IO Unit)

/-- Byte list to `ByteArray`, for `IO.FS.writeBinFile`. -/
def toByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

/-- Write the objects as `<dir>/<name>.o`. Fails rather than writing a
    truncated object when a kernel is outside the encoder fragment. -/
def emitTo (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, p) in kernels do
    match objBytes p with
    | some bs => IO.FS.writeBinFile (dir / s!"{name}.o") (toByteArray bs)
    | none => throw (IO.userError s!"{name}: body outside the byte-encoder fragment")

end CatCrypt.Crypto.SecureCompilation.X86Backend.Ed25519BytesEmit
