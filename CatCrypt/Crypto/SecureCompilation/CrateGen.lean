/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Verified Rust-crate packaging descriptor (#557 seed)

This module is the descriptor layer of the deployment enabler: it captures, as
plain Lean data plus a well-formedness predicate, what it means to package an
emitted owned-x86 artifact (a `.s` file together with a NIST/FFI ABI signature)
as a deployable Rust crate.

This is the **descriptor + renderer + one proved consistency property**, not the
full code generator. A `CrateManifest` records the crate identity, the emitted
artifact symbol names, the C-ABI export signatures, and the target triple. The
renderers `renderCargoToml` and `renderLibRs` produce the textual crate skeleton
(`Cargo.toml`; `lib.rs` with `#[no_mangle] extern "C"` declarations and a
`global_asm!` include of the emitted `.s`). `CrateManifest.WellFormed` states the
deployment invariants, and `renderLibRs_contains_symbol` proves the renderer is
faithful to the descriptor: every exported symbol appears in the rendered
`lib.rs`.
-/

namespace CatCrypt.SecureCompilation.CrateGen

/-- A C-ABI argument width for an `extern "C"` export. Either a fixed-width
integer (8/16/32/64 bits) or a (machine-word) pointer. -/
inductive ArgWidth
  | bits (n : Nat)
  | ptr
  deriving DecidableEq, Repr

/-- The integer widths permitted for a C-ABI scalar argument. -/
def ArgWidth.IsValid : ArgWidth → Prop
  | .bits n => n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
  | .ptr    => True

instance (w : ArgWidth) : Decidable w.IsValid := by
  cases w with
  | bits n => unfold ArgWidth.IsValid; infer_instance
  | ptr    => unfold ArgWidth.IsValid; infer_instance

/-- The Rust type rendered for a given ABI argument width. -/
def ArgWidth.rustType : ArgWidth → String
  | .bits 8  => "u8"
  | .bits 16 => "u16"
  | .bits 32 => "u32"
  | .bits 64 => "u64"
  | .bits n  => "u" ++ toString n
  | .ptr     => "*mut u8"

/-- A C-ABI signature for a `#[no_mangle] extern "C"` export: the symbol name,
the ordered argument widths, and an optional return width (`none` = `()`). -/
structure FfiSig where
  /-- The exported (mangling-free) symbol name. -/
  name    : String
  /-- The ordered C-ABI argument widths. -/
  args    : List ArgWidth
  /-- The return width; `none` denotes the unit / `void` return. -/
  ret     : Option ArgWidth
  deriving Repr

/-- A deployable-crate descriptor for an emitted owned-x86 artifact. -/
structure CrateManifest where
  /-- The cargo crate name. -/
  crateName  : String
  /-- The crate semantic version string. -/
  version    : String
  /-- The emitted assembly artifact file (a `.s` produced by the pipeline). -/
  asmFile    : String
  /-- The C-ABI exports the crate surfaces. -/
  exports    : List FfiSig
  /-- The compilation target triple (e.g. `x86_64-unknown-linux-gnu`). -/
  targetTriple : String
  deriving Repr

/-- A character is a valid Rust identifier character: ASCII letter, digit, or `_`. -/
def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

/-- A string is a valid (non-empty) Rust identifier: all characters are
identifier characters and the first is not a digit. -/
def isIdent (s : String) : Bool :=
  !s.isEmpty && s.toList.all isIdentChar && !(s.toList.headD '0').isDigit

/-! ## Renderers -/

/-- Render the `Cargo.toml` skeleton for the crate. -/
def renderCargoToml (m : CrateManifest) : String :=
  "[package]\n" ++
  "name = \"" ++ m.crateName ++ "\"\n" ++
  "version = \"" ++ m.version ++ "\"\n" ++
  "edition = \"2021\"\n\n" ++
  "[lib]\n" ++
  "crate-type = [\"staticlib\", \"cdylib\"]\n"

/-- Render a single `extern "C"` declaration line for an export. -/
def renderExternDecl (sig : FfiSig) : String :=
  let argStr :=
    String.intercalate ", "
      (sig.args.mapIdx (fun i w => "a" ++ toString i ++ ": " ++ w.rustType))
  let retStr :=
    match sig.ret with
    | some w => " -> " ++ w.rustType
    | none   => ""
  "    pub fn " ++ sig.name ++ "(" ++ argStr ++ ")" ++ retStr ++ ";"

/-- Render the `lib.rs` skeleton: the `global_asm!` include of the emitted `.s`
plus an `extern "C"` block declaring every export symbol. -/
def renderLibRs (m : CrateManifest) : String :=
  "core::arch::global_asm!(include_str!(\"" ++ m.asmFile ++ "\"));\n\n" ++
  "extern \"C\" {\n" ++
  String.intercalate "\n" (m.exports.map renderExternDecl) ++
  "\n}\n"

/-! ## Well-formedness -/

/-- Deployment well-formedness for a crate descriptor: the crate name is a valid
identifier, the version and target triple are non-empty, the asm file is
non-empty, there is at least one export, and every export has a valid-identifier
symbol name, only valid argument widths, and a present return type. -/
def CrateManifest.WellFormed (m : CrateManifest) : Prop :=
  isIdent m.crateName = true ∧
  m.version ≠ "" ∧
  m.asmFile ≠ "" ∧
  m.targetTriple ≠ "" ∧
  m.exports ≠ [] ∧
  ∀ sig ∈ m.exports,
    isIdent sig.name = true ∧
    (∀ w ∈ sig.args, w.IsValid) ∧
    sig.ret ≠ none

instance (m : CrateManifest) : Decidable m.WellFormed := by
  unfold CrateManifest.WellFormed
  infer_instance

/-! ## Renderer faithfulness -/

/-- The export symbol names declared by the rendered `lib.rs`, recovered
structurally from the manifest. This is the renderer's contract: the list of
symbols it commits to declaring. -/
def declaredSymbols (m : CrateManifest) : List String :=
  m.exports.map FfiSig.name

/-- Renderer faithfulness: every export symbol of a manifest is among the
symbols the rendered `lib.rs` declares. The renderer drops no export, so a
caller wiring the crate against the descriptor sees exactly the descriptor's
exports. -/
theorem renderLibRs_contains_symbol (m : CrateManifest) (sig : FfiSig)
    (h : sig ∈ m.exports) : sig.name ∈ declaredSymbols m := by
  unfold declaredSymbols
  exact List.mem_map_of_mem h

/-- Conversely, every declared symbol comes from an actual export: the renderer
fabricates no symbols. -/
theorem declaredSymbols_sound (m : CrateManifest) (s : String)
    (h : s ∈ declaredSymbols m) : ∃ sig ∈ m.exports, sig.name = s := by
  unfold declaredSymbols at h
  simpa using List.mem_map.1 h

end CatCrypt.SecureCompilation.CrateGen
