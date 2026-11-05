/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.RustAbiPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RustAbiPrinter

@[expose] public section

set_option autoImplicit false

/-!
# `crates/catcrypt-mpn` emit driver

Writes the generated portion of the `catcrypt-mpn` Rust crate from the five
front-compiled binary mpn kernels of `MpnLoopFrontEmit`
(`mpn_{add,sub,and,ior,xor}_n_loop_owned`):

* `crates/catcrypt-mpn/asm/<symbol>.s` — `renderLprogAtt` of each kernel's
  `Lprog` (the same values `MpnLoopFrontEmit.emitMain` renders to
  `bench/integration/gen_com/`; the crate carries its own copies, rendered
  from source rather than file-copied).
* `crates/catcrypt-mpn/src/mpn_ffi.rs` — the `RustAbiPrinter` safe-wrapper
  module: one `extern "C"` declaration and one safe slice wrapper per
  kernel, `unsafe` confined to the wrapper bodies.

Both artifacts come from the same in-memory `Lprog` values in one `#eval`,
so the Rust extern signatures cannot drift from the assembly.

## Derived vs asserted

Derived from each kernel's `Lprog` (`WrapperSpec.ofLprog`): the symbol name,
argument count, SysV argument registers, 64-bit widths, and the `RAX`
scalar-return slot. Asserted here: the parameter names `rp/ap/bp/n`, the
read/write modes (`rp` written, `ap`/`bp` read, `n` the shared limb count),
and the carry/borrow meaning of `RAX` for `add`/`sub`. A mismatch between
the asserted and derived signature makes `WrapperSpec.ofLprog` return
`none`, and `emitMain` then throws without writing the crate. The closing
`#eval emitMain` is commented out, so no build runs the emit; run it from the
dev root, the working directory against which `crateDir` is resolved.

The hand-written crate portions (`src/lib.rs` seam glue, `build.rs`,
`Cargo.toml`, `tests/`) live in `crates/catcrypt-mpn/` directly; see the
crate README for the generated/hand-written split.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCrateEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RustAbiPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- Bind a kernel's front-compiled `Lprog` to its asserted wrapper fields;
    `none` when the front compile fails or the asserted signature mismatches
    the derived one. -/
def entry (lp? : Option Lprog) (rustName opDoc : String)
    (names : List String) (kinds : List ParamKind) (ret : RetMeaning) :
    Option (Lprog × WrapperSpec) := do
  let lp ← lp?
  let ws ← WrapperSpec.ofLprog rustName opDoc names kinds ret lp
  pure (lp, ws)

/-- GMP `mpn` binary-kernel parameter names `(rp, ap, bp, n)`. -/
def binNames : List String := ["rp", "ap", "bp", "n"]

/-- Modes of the binary-kernel slots: `rp` written, `ap`/`bp` read, `n` the
    shared limb count. -/
def binKinds : List ParamKind :=
  [.limbs .write, .limbs .read, .limbs .read, .sharedLen]

def addEntry (_ : Unit) : Option (Lprog × WrapperSpec) :=
  entry (addLprogFront ()) "mpn_add_n"
    "Limbwise little-endian sum: rp = ap + bp mod 2^(64 n)."
    binNames binKinds .carry

def subEntry (_ : Unit) : Option (Lprog × WrapperSpec) :=
  entry (subLprogFront ()) "mpn_sub_n"
    "Limbwise little-endian difference: rp = ap - bp mod 2^(64 n)."
    binNames binKinds .borrow

def andEntry (_ : Unit) : Option (Lprog × WrapperSpec) :=
  entry (andLprog ()) "mpn_and_n" "Limbwise AND: rp[i] = ap[i] & bp[i]."
    binNames binKinds .unused

def iorEntry (_ : Unit) : Option (Lprog × WrapperSpec) :=
  entry (iorLprog ()) "mpn_ior_n" "Limbwise OR: rp[i] = ap[i] | bp[i]."
    binNames binKinds .unused

def xorEntry (_ : Unit) : Option (Lprog × WrapperSpec) :=
  entry (xorLprog ()) "mpn_xor_n" "Limbwise XOR: rp[i] = ap[i] ^ bp[i]."
    binNames binKinds .unused

/-- The five crate kernels, in extern-block order. -/
def entries (_ : Unit) : List (Option (Lprog × WrapperSpec)) :=
  [addEntry (), subEntry (), andEntry (), iorEntry (), xorEntry ()]

/-- Crate root, relative to the dev root, the working directory of every build. -/
def crateDir : String := "../catcrypt-compiler/crates/catcrypt-mpn"

/-- Write `asm/<symbol>.s` for each kernel and the generated
    `src/mpn_ffi.rs`. Throws when a front compile or a spec derivation
    returns `none`. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll (crateDir ++ "/asm")
  IO.FS.createDirAll (crateDir ++ "/src")
  let mut specs : Array WrapperSpec := #[]
  for e? in entries () do
    match e? with
    | none => throw (IO.userError
        "catcrypt-mpn: spec derivation failed (front compile returned none, or asserted names/kinds mismatch the Lprog signature)")
    | some (lp, ws) =>
      IO.FS.writeFile (crateDir ++ "/asm/" ++ ws.cName ++ ".s")
        (renderLprogAtt lp)
      specs := specs.push ws
  IO.FS.writeFile (crateDir ++ "/src/mpn_ffi.rs")
    (genModule "CatCrypt/Crypto/SecureCompilation/X86Backend/MpnCrateEmit.lean"
      specs.toList)

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCrateEmit
