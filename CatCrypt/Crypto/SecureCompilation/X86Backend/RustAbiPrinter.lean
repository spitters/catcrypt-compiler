/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

@[expose] public section

set_option autoImplicit false

/-!
# Safe-Rust wrapper printer over `Lprog` export signatures

A port of AUCurves' `src/Bedrock/ToSafeRustString.v` safe-wrapper generator,
retargeted from bedrock2/fiat leaves to the CatCrypt owned-emit pipeline. The
printer renders, for a set of exported kernels, one Rust module containing an
`extern "C"` block and one safe wrapper function per kernel, with `unsafe`
confined to the wrapper bodies.

## Derived vs asserted spec fields

AUCurves reads access modes off bedrock2 separation-logic specs (buffer
unchanged in the postcondition → `&T`, changed → `&mut T`, separating
conjunction → distinct references). Our access-mode source is the emit
signature itself: a [`WrapperSpec`] is populated from the `Lprog` value that
also renders the kernel's assembly (`ComL.toLprogPhysAbi` /
`toLprogPhysAbiScalarAcc` output), so the two artifacts cannot drift apart.

Per field:

* **Derived from the `Lprog`** — the exported symbol name (`lp_funcs` key),
  the argument count, the SysV argument registers (`lfd_arg`), the argument
  bit widths (`lfd_tyin`), and the scalar-return slot (`lfd_res`/`lfd_tyout`,
  `RAX`). [`WrapperSpec.ofLprog`] returns `none` on any mismatch between
  these and the asserted fields, so an emit driver that `#eval`s the printer
  fails elaboration when the emit-side signature changes.
* **Asserted per kernel** — the Rust-facing parameter names, each parameter's
  [`ParamKind`] (read-only limb slice, written limb slice, or the shared
  runtime limb count), whether the `RAX` value is a carry limb, a borrow
  limb, or meaningless, and the one-line semantics docstring. The `Lfundef`
  signature does not record which memref arguments the body writes, so the
  in/out split cannot be derived from it; the assertion is checked against
  the derived arity and widths but not against the body.

## Aliasing

No exported kernel carries a verified in-place (`rp == ap`) contract: the
kernels' correctness statements are over distinct arrays. The printer
therefore has no in-place mode — every written buffer is a distinct `&mut`
parameter, and Rust's borrow checker rejects aliasing at every call site.

## Shape of the generated wrapper

The runtime limb count `n` is a [`ParamKind.sharedLen`] slot: the safe
wrapper does not expose it, deriving it from the first limb-slice parameter's
length and `assert_eq!`-checking every other limb slice against it, then
passing it in the slot's register position. A written slice maps to
`&mut [u64]`, a read slice to `&[u64]`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RustAbiPrinter

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog Lfundef)

/-- Access mode of a limb-slice parameter: read (`&[u64]`) or written
    (`&mut [u64]`). There is no in-place mode; see the module docstring. -/
inductive ParamMode
  | read
  | write
  deriving Repr, DecidableEq

/-- What a SysV argument slot carries at the Rust boundary. -/
inductive ParamKind
  /-- Pointer to a `u64` limb array whose length is the shared runtime limb
      count `n`. -/
  | limbs (mode : ParamMode)
  /-- The runtime limb count `n` itself. The safe wrapper derives it from the
      limb-slice lengths instead of taking it as a parameter. -/
  | sharedLen
  deriving Repr, DecidableEq

/-- Meaning of the kernel's `RAX` return value. -/
inductive RetMeaning
  /-- Carry limb of the modular sum. -/
  | carry
  /-- Borrow limb of the modular difference. -/
  | borrow
  /-- The register value is meaningless; the safe wrapper discards it. -/
  | unused
  deriving Repr, DecidableEq

/-- One SysV argument slot: asserted name and kind, derived register and
    width. -/
structure SlotSpec where
  name : String
  reg : String
  width : Nat
  kind : ParamKind
  deriving Repr

/-- A safe-wrapper specification for one exported kernel. `cName`, the slot
    registers/widths, and `retReg` come from the `Lprog`; the rest is
    asserted (see the module docstring). -/
structure WrapperSpec where
  /-- Exported assembly symbol (extern block entry). -/
  cName : String
  /-- Safe Rust function name. -/
  rustName : String
  slots : List SlotSpec
  /-- Scalar-return register and width, when the export declares one. -/
  retReg : Option (String × Nat)
  ret : RetMeaning
  /-- One-line semantics for the wrapper docstring. -/
  opDoc : String
  deriving Repr

/-- Zip the asserted names/kinds against a derived `Lfundef` signature.
    `none` when the arity disagrees, a width is not 64, or a declared return
    meaning has no scalar-return slot to carry it. -/
def WrapperSpec.ofLfundef (rustName opDoc : String) (names : List String)
    (kinds : List ParamKind) (ret : RetMeaning)
    (sym : String) (f : Lfundef) : Option WrapperSpec := do
  guard (names.length == f.lfd_arg.length)
  guard (kinds.length == f.lfd_arg.length)
  guard (f.lfd_tyin.length == f.lfd_arg.length)
  guard (f.lfd_tyin.all (· == 64))
  let regsW := f.lfd_arg.zip f.lfd_tyin
  let slots := (names.zip kinds).zip regsW |>.map fun ((nm, k), (rg, w)) =>
    { name := nm, reg := rg, width := w, kind := k : SlotSpec }
  let retReg := match f.lfd_res.head?, f.lfd_tyout.head? with
    | some r, some w => some (r, w)
    | _, _ => none
  if ret != .unused then
    guard (retReg == some ("RAX", 64))
  pure { cName := sym, rustName, slots, retReg, ret, opDoc }

/-- [`WrapperSpec.ofLfundef`] applied to the sole function of an `Lprog`
    (`none` unless the program exports exactly one). -/
def WrapperSpec.ofLprog (rustName opDoc : String) (names : List String)
    (kinds : List ParamKind) (ret : RetMeaning) (p : Lprog) :
    Option WrapperSpec :=
  match p.lp_funcs with
  | [(sym, f)] => WrapperSpec.ofLfundef rustName opDoc names kinds ret sym f
  | _ => none

/-! ## Rust text generators -/

/-- Raw pointer type of a slot at the `extern "C"` boundary. -/
def rustPtrTy : ParamKind → String
  | .limbs .write => "*mut u64"
  | .limbs .read => "*const u64"
  | .sharedLen => "u64"

/-- `name: type` parameter of the extern declaration. -/
def externParam (s : SlotSpec) : String := s.name ++ ": " ++ rustPtrTy s.kind

/-- `name=REG` ABI summary of the slot list. -/
def abiSummary (slots : List SlotSpec) : String :=
  String.intercalate ", " (slots.map fun s => s.name ++ "=" ++ s.reg)

/-- Return-type suffix of the extern declaration (`""` when the export has no
    scalar-return slot). -/
def externRet (ws : WrapperSpec) : String :=
  match ws.retReg with
  | some _ => " -> u64"
  | none => ""

/-- Doc line describing the `RAX` value. -/
def retDocLine (ws : WrapperSpec) : String :=
  match ws.ret, ws.retReg with
  | .carry, _ => "; carry limb out in RAX"
  | .borrow, _ => "; borrow limb out in RAX"
  | .unused, some (r, _) => "; " ++ r ++ " value meaningless"
  | .unused, none => ""

/-- The extern-block declaration for one kernel. `pub(crate)` so that
    hand-written crate modules (e.g. a C-ABI export shim) call the same
    declaration instead of re-declaring the symbol. -/
def genExternDecl (ws : WrapperSpec) : String :=
  "    /// SysV x86-64: " ++ abiSummary ws.slots ++ retDocLine ws ++ ".\n" ++
  "    pub(crate) fn " ++ ws.cName ++ "(" ++
    String.intercalate ", " (ws.slots.map externParam) ++ ")" ++
    externRet ws ++ ";"

/-- Slice parameter of the safe wrapper (limb slots only). -/
def safeParam (s : SlotSpec) : Option String :=
  match s.kind with
  | .limbs .write => some (s.name ++ ": &mut [u64]")
  | .limbs .read => some (s.name ++ ": &[u64]")
  | .sharedLen => none

/-- Argument expression of a slot at the unsafe call site. -/
def callArg (s : SlotSpec) : String :=
  match s.kind with
  | .limbs .write => s.name ++ ".as_mut_ptr()"
  | .limbs .read => s.name ++ ".as_ptr()"
  | .sharedLen => "n as u64"

/-- The safe wrapper function for one kernel: slice parameters, the shared
    limb count derived from the first limb slice and checked against the
    rest, `unsafe` confined to the extern call. -/
def genSafeWrapper (ws : WrapperSpec) : String :=
  let limbSlots := ws.slots.filter fun s => s.kind != .sharedLen
  let params := ws.slots.filterMap safeParam
  let lenChecks := match limbSlots with
    | [] => []
    | s₀ :: rest =>
      ("    let n = " ++ s₀.name ++ ".len();") ::
        rest.map fun s => "    assert_eq!(" ++ s.name ++ ".len(), n);"
  let retTy := match ws.ret with
    | .carry | .borrow => " -> u64"
    | .unused => ""
  let call := ws.cName ++ "(" ++
    String.intercalate ", " (ws.slots.map callArg) ++ ")"
  let body := match ws.ret, ws.retReg with
    | .unused, some _ => "    let _ = unsafe { " ++ call ++ " };"
    | .unused, none => "    unsafe { " ++ call ++ " };"
    | _, _ => "    unsafe { " ++ call ++ " }"
  let retDoc := match ws.ret with
    | .carry => "/// Returns the carry limb (0 or 1).\n"
    | .borrow => "/// Returns the borrow limb (0 or 1).\n"
    | .unused => ""
  "/// " ++ ws.opDoc ++ "\n" ++
  "///\n" ++
  retDoc ++
  "/// Calls `" ++ ws.cName ++ "` (SysV: " ++ abiSummary ws.slots ++
    "). All slices must have equal length; checked.\n" ++
  "#[inline]\n" ++
  "pub fn " ++ ws.rustName ++ "(" ++ String.intercalate ", " params ++ ")" ++
    retTy ++ " {\n" ++
  String.intercalate "\n" lenChecks ++ "\n" ++
  "    // SAFETY: the slices are distinct (borrow-checked), each n limbs\n" ++
  "    // long; the kernel reads/writes exactly n limbs per pointer and\n" ++
  "    // retains none of them.\n" ++
  body ++ "\n" ++
  "}\n"

/-- A complete generated Rust module: header, extern block, safe wrappers.
    `genNote` names the emitting Lean module in the do-not-edit header. -/
def genModule (genNote : String) (specs : List WrapperSpec) : String :=
  "//! GENERATED by `" ++ genNote ++ "` — do not edit.\n" ++
  "//!\n" ++
  "//! Extern declarations and safe equal-length wrappers for the owned\n" ++
  "//! CatCrypt-emitted kernels in `asm/*.s`. Symbol names, argument\n" ++
  "//! registers, widths, and the scalar-return slot are read from the same\n" ++
  "//! `Lprog` values that render the assembly; parameter names, read/write\n" ++
  "//! modes, and the carry/borrow meaning of the return value are asserted\n" ++
  "//! in the emitting module.\n" ++
  "//!\n" ++
  "//! The wrappers take distinct slices (`&mut` written, `&` read): Rust's\n" ++
  "//! borrow checker enforces non-aliasing, matching the distinct-array\n" ++
  "//! state model of the kernels' verification. No in-place aliasing API is\n" ++
  "//! exposed.\n" ++
  "#![allow(unsafe_code)]\n" ++
  "\n" ++
  "extern \"C\" {\n" ++
  String.intercalate "\n" (specs.map genExternDecl) ++ "\n" ++
  "}\n" ++
  "\n" ++
  String.intercalate "\n" (specs.map genSafeWrapper)

end CatCrypt.Crypto.SecureCompilation.X86Backend.RustAbiPrinter
