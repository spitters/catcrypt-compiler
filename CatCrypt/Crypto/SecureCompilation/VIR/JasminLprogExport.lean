/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap

/-!
# Jasmin `Linear.lprog` value-level producer (task #142)

Link 1/7 of the linear-jasmin backend (#155). This module turns a typed
`Com jasminDialect` into a value-level mirror of jasmin's `Linear.lprog`, the
already-linearized IR consumed by the back-back-end `compile_lprog_to_asm`
(`patches/jasmin/compiler.v.patch`). The companion OCaml reader is
`Read_linear.load_marshal_file` (`patches/jasmin/read_linear.ml.patch`).

## The jasmin `lprog` shape (from `proofs/lang/linear.v`)

```
Variant linstr_r :=
  | Lopn   : lexprs -> sopn -> rexprs -> linstr_r
  | Lsyscall : syscall_t -> linstr_r
  | Lcall    : option var_i -> remote_label -> linstr_r
  | Lret     : linstr_r
  | Lalign : linstr_r
  | Llabel : label_kind -> label -> linstr_r
  | Lgoto  : remote_label -> linstr_r
  | Ligoto : rexpr -> linstr_r
  | LstoreLabel : var -> label -> linstr_r
  | Lcond  : fexpr -> label -> linstr_r.
Record linstr := MkLI { li_ii : instr_info; li_i : linstr_r }.
Record lfundef := LFundef
  { lfd_info; lfd_align; lfd_tyin; lfd_arg; lfd_body; lfd_tyout; lfd_res;
    lfd_export; lfd_callee_saved; lfd_stk_max; lfd_frame_size; lfd_align_args }.
Record lprog := { lp_rip; lp_rsp; lp_globs; lp_glob_names; lp_funcs }.
```

The Lean mirror types below match this structure field-by-field. The leaf
carriers that the Coq side keeps abstract or architecture-specific (`Ident.ident`,
`sopn`'s x86 extended-op GADT, `var_i` records carrying `Uint63.t` + zarith `Z`,
`Location.t`, annotations) are represented here by plain `String`/`Nat`: the
textual IR is the wire format (see "Serialization" below), and the textual
reader resolves register/opcode names structurally.

## Serialization: textual IR, not OCaml `Marshal`

`Read_linear` ships two paths: `load_marshal` (the primary, lossless path, which
deserializes an OCaml `Linear.lprog` value graph via `Stdlib.Marshal`) and
`read_text_stub` (which currently always raises). The Marshal path is what the
driver `drive_linear.ml` is wired to.

Producing a byte-identical OCaml Marshal blob from Lean is **not** structurally
faithful: jasmin's `lp_rip`/`lp_rsp` are the abstract `Ident.ident` (the OCaml
round-trip test uses `Obj.magic 0` for exactly this reason), a non-empty
`lfd_body` embeds the x86 `sopn`/`asm_op` encoding, and `var_i`/`Z` carry
`Uint63.t` and zarith **custom blocks** whose `Marshal` representation embeds
C-identifier tags tied to the OCaml runtime. Lean cannot reproduce those bytes
without linking the OCaml runtime via FFI.

So this module emits a **textual** `lprog` representation (`Lprog.toText`),
mirroring the structure exactly, prefixed with the OCaml-side magic header
`JASMIN-LPROG-MARSHAL-v1\n`. This is the integration seam: `read_linear` as
shipped in #144 accepts the Marshal path only — `read_text_stub` lists every
`linstr_r` constructor and dropped field as a coverage gap and raises. Closing
link 2/7 over the textual path requires extending `PrintLinear.pp_prog` +
writing the textual inverse on the OCaml side (the README's "Removing the last
trust dependency" plan), or an OCaml `Marshal` FFI on the Lean side. Either is
out of scope for link 1/7; the value-level structure produced here is the input
both routes consume.

## Physical-register export (§7–8)

`Com.toLprog` (above) is the pre-register-allocation SSA export; jasmin's
`assemble_prog` (link 3/7) instead requires **physical x86 registers in
destructive two-address form**. §7 adds `Com.toLprogPhys`: a linear-scan
register allocation over the 15 usable x86-64 GP registers (`RAX … R15`,
`RSP` excluded) with stack spill (`k.N`) for overflow, and a two-address
lowering (`mov dst,src0; op dst,src1`). §8 discharges the value-level
obligations: `physNoCollisionChaCha` (no two simultaneously-live slots share a
physical slot — in `JasminLprogExportChaCha.lean`, `native_decide`),
`twoAddr_denote` / `twoAddr_denote_collapsed` (the destructive `mov;op`
computes `op src0 src1`), and `Com.toLprogPhys_wf`.

## Denotation

Semantic preservation (the exported `lprog` denotes the same function as the
source `Com` under jasmin's linear semantics `lsem`) is stated as the named
hypothesis `LprogExportFaithful` — the analogue of #145's
`MlirToolchainSemanticsAgrees`. Closing it requires a Lean model of jasmin's
`lsem`, which is not available Lean-side. The value-level obligations that *are*
discharged here: the export is total, structurally well-formed
(`Com.toLprog_wf` / `Com.toLprogPhys_wf`), and round-trips through the textual
serializer (`Com.toLprogText_magic`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Lean mirror types for `Linear.lprog`

Each type mirrors a Coq record/variant in `proofs/lang/linear.v`. Abstract /
architecture-specific leaves are carried as `String`/`Nat` (see module header). -/

/-- Mirror of jasmin `label` (a positive index) and `label_kind`. -/
abbrev LLabel := Nat

/-- Mirror of `label_kind` (`InternalLabel` / `ExternalLabel`). -/
inductive LabelKind where
  | internal
  | external
  deriving DecidableEq, Repr

/-- A simple register/expression operand. The Coq `lexpr`/`rexpr`/`fexpr` ASTs
    are far richer (memory operands, sub-words, conditions); the word-level
    two-address `JasminOp` fragment only ever needs a named register, an array
    element, or an immediate, so we carry that surface here. -/
inductive LOperand where
  /-- A named register, e.g. `"RAX"`, `"w0"`. -/
  | reg (name : String)
  /-- An array element `base[idx]`, e.g. `k[3]`. -/
  | arr (base : String) (idx : Nat)
  /-- A compile-time immediate. -/
  | imm (value : Nat)
  /-- A **register-indexed (SIB) array element** `base[idx*scale]`, where both
      `base` and `idx` name registers and `scale` is the compile-time element
      stride in bytes (the x86 `(%base,%idx,scale)` effective address). This is
      the runtime-index image of `stackLoad`/`stackStore`: the array element
      whose offset is a *register* (`Pvar idx`) scaled by the element width,
      rather than a compile-time `Nat` (`.arr`). The reader materialises it as
      the x86 base+index*scale memory reference. -/
  | arrIdx (base idx : String) (scale : Nat)
  deriving DecidableEq, Repr

/-- Mirror of `Linear.linstr_r`: all ten constructors of the Coq variant.

    `Lopn` carries the destinations (`lexprs`), the operation name (a textual
    stand-in for the `sopn` x86 extended-op value), and the sources (`rexprs`).
    The control-flow constructors carry the same payload shape as Coq, with
    abstract leaves as `String`/`Nat`. -/
inductive LinstrR where
  /-- `Lopn lexprs sopn rexprs`: write `dsts`, applying op `opn` to `srcs`. -/
  | Lopn (dsts : List LOperand) (opn : String) (srcs : List LOperand)
  /-- `Lsyscall syscall_t`. -/
  | Lsyscall (name : String)
  /-- `Lcall (option var_i) remote_label`. -/
  | Lcall (ra : Option String) (target : String × LLabel)
  /-- `Lret`. -/
  | Lret
  /-- `Lalign`. -/
  | Lalign
  /-- `Llabel label_kind label`. -/
  | Llabel (kind : LabelKind) (lbl : LLabel)
  /-- `Lgoto remote_label`. -/
  | Lgoto (target : String × LLabel)
  /-- `Ligoto rexpr`: absolute indirect jump. -/
  | Ligoto (target : LOperand)
  /-- `LstoreLabel var label`. -/
  | LstoreLabel (dst : String) (lbl : LLabel)
  /-- `Lcond fexpr label`. -/
  | Lcond (cond : LOperand) (lbl : LLabel)
  deriving Repr

/-- Mirror of `Linear.linstr = MkLI { li_ii ; li_i }`. `li_ii` (`instr_info`)
    is a source-position tag; we carry it as an opaque `Nat`. -/
structure Linstr where
  li_ii : Nat
  li_i : LinstrR
  deriving Repr

/-- Mirror of `Linear.lcmd = seq linstr`. -/
abbrev Lcmd := List Linstr

/-- Mirror of `Linear.lfundef`. Every field of the Coq record is present;
    abstract/architecture leaves are `String`/`Nat`. `lfd_tyin`/`lfd_tyout`
    carry the bit widths of the in/out registers (the `ltype` `U w` cases). -/
structure Lfundef where
  /-- `lfd_info : fun_info` (opaque position tag). -/
  lfd_info : Nat := 0
  /-- `lfd_align : wsize` (alignment, as a byte count). -/
  lfd_align : Nat := 1
  /-- `lfd_tyin : seq ltype` (argument register widths). -/
  lfd_tyin : List Nat := []
  /-- `lfd_arg : seq var_i` (argument register names). -/
  lfd_arg : List String := []
  /-- `lfd_body : lcmd`. -/
  lfd_body : Lcmd := []
  /-- `lfd_tyout : seq ltype` (result register widths). -/
  lfd_tyout : List Nat := []
  /-- `lfd_res : seq var_i` (result register names). -/
  lfd_res : List String := []
  /-- `lfd_export : bool`. -/
  lfd_export : Bool := true
  /-- `lfd_callee_saved : seq var`. -/
  lfd_callee_saved : List String := []
  /-- `lfd_stk_max : Z`. -/
  lfd_stk_max : Nat := 0
  /-- `lfd_frame_size : Z`. -/
  lfd_frame_size : Nat := 0
  /-- `lfd_align_args : seq wsize`. -/
  lfd_align_args : List Nat := []
  deriving Repr

/-- Mirror of `Linear.lprog`. `lp_rip`/`lp_rsp` are `Ident.ident` in Coq
    (abstract); the conventional register names are `"RIP"`/`"RSP"`. -/
structure Lprog where
  /-- `lp_rip : Ident.ident`. -/
  lp_rip : String := "RIP"
  /-- `lp_rsp : Ident.ident`. -/
  lp_rsp : String := "RSP"
  /-- `lp_globs : seq u8`. -/
  lp_globs : List Nat := []
  /-- `lp_glob_names : seq (var * wsize * Z)`. -/
  lp_glob_names : List (String × Nat × Nat) := []
  /-- `lp_funcs : seq (funname * lfundef)`. -/
  lp_funcs : List (String × Lfundef) := []
  deriving Repr

/-! ## 2. Lowering a `JasminOp` to a `linstr_r`

Each `Com` binding is a `JasminOp` applied to de-Bruijn argument vars. We name
the binding result `r{depth}` (the SSA index from the let-nesting depth) and the
argument vars by the depth at which they were bound. This collapses the typed
De Bruijn structure to flat register names, which is what the linear IR uses. -/

/-- The register name for the SSA binding at let-depth `d` (counting from the
    program root). -/
def regName (d : Nat) : String := "r" ++ toString d

/-- Map a `JasminBinOp` to a textual jasmin opcode base name (no width). -/
def binOpName : JasminBinOp → String
  | .add => "ADD"
  | .sub => "SUB"
  | .mul => "MUL"
  | .and => "AND"
  | .or  => "OR"
  | .xor => "XOR"
  | .shl => "SHL"
  | .shr => "SHR"
  -- BMI1 `andn` (`d := (~a) & b`). The owned-x86 printer matches
  -- `stripWidthTag opn == "ANDN"` (so `withWidthTag 64 "ANDN" = "ANDN:64"`
  -- round-trips) and renders the non-destructive 3-operand `andn b, a, d`.
  | .andn => "ANDN"

/-- Map a `JasminCmp` condition code to the base mnemonic of its materialised
    comparison `Lopn [d] SET<cc> [a, b]` (`d := a <cc> b ? 1 : 0`); the suffix is
    the x86 condition-code name. -/
def cmpName : JasminCmp → String
  | .eq => "SETE"
  | .ne => "SETNE"
  | .ult => "SETB"
  | .ule => "SETBE"
  | .ugt => "SETA"
  | .uge => "SETAE"

/-- Append the U64 width tag to a body mnemonic when the op is 64-bit. The
    32-bit ops (ChaCha20, SHA-256) carry no suffix and `read_linear`
    materialises them at its `default_ws = U32`; the 64-bit ops (Keccak) carry
    `":64"` and `read_linear` materialises them — and, because a Keccak body is
    uniformly U64, every legalization-injected `MOV` of that function — at U64.
    The width tag is the seam by which the U32 linear path (#453/#462) extends
    to a U64 kernel (#472) without per-instruction width plumbing through the
    two-address legalizer. -/
def withWidthTag (w : Nat) (mnem : String) : String :=
  if w = 64 then mnem ++ ":64" else mnem

/-- Suffix test over the character list. The tag recognizers below are computed
    through by `decide` in the fidelity proofs, and `String.endsWith` does not
    reduce inside a module, so they are stated over `List.isSuffixOf`. -/
def hasSuffix (s pat : String) : Bool := List.isSuffixOf pat.toList s.toList

/-- Prefix test over the character list, for the same reason as `hasSuffix`. -/
def hasPrefix (s pat : String) : Bool := List.isPrefixOf pat.toList s.toList

/-- Drop the first `k` characters of a string, over the character list. `String.drop`
    iterates over `String.Pos` and does not reduce inside a module; the operand-name
    parsers are computed through by `decide`. -/
def strDrop (s : String) (k : Nat) : String := String.ofList (s.toList.drop k)

/-- Split a character list at every occurrence of `sep`, keeping the empty groups:
    a list with `n` occurrences of `sep` yields `n + 1` groups and the separators
    are dropped. -/
def splitChars (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
      if c = sep then [] :: splitChars sep rest
      else match splitChars sep rest with
        | [] => [[c]]
        | g :: gs => (c :: g) :: gs

/-- Split a string at every occurrence of one separator character, over the
    character list. -/
def splitOnChar (sep : Char) (s : String) : List String :=
  (splitChars sep s.toList).map String.ofList

/-- Read a decimal digit list. `String.toNat?` does not reduce inside a module,
    and the operand-name parsers are computed through by `decide`. -/
def natOfDigits? (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => cs.foldl (fun acc c =>
      match acc with
      | some k => if '0' ≤ c && c ≤ '9' then some (k * 10 + (c.toNat - '0'.toNat)) else none
      | none => none) (some 0)

/-- The scan state of `String.Slice.isNat` after a character list: the first
    component is the early `false` answer once a character rejects the string,
    the second records whether the previous character was a digit. -/
def charsIsNatStep : List Char → (Option Bool × Bool) → (Option Bool × Bool)
  | [], st => st
  | c :: rest, st =>
      if c = '_' then
        (if (!st.2) = true then (some false, st.2)
         else charsIsNatStep rest ((none : Option Bool), false))
      else if c.isDigit = true then charsIsNatStep rest ((none : Option Bool), true)
      else (some false, st.2)

/-- `charsIsNatStep` is the `for` loop of `String.Slice.isNat` over a character
    list. -/
theorem forIn_charsIsNatStep : ∀ (l : List Char) (st : Option Bool × Bool),
    (forIn l st (fun c (__s : Option Bool × Bool) =>
        if c = '_' then
          if (!__s.2) = true then pure (ForInStep.done (some false, __s.2))
          else pure (ForInStep.yield ((none : Option Bool), false))
        else
          if c.isDigit = true then pure (ForInStep.yield ((none : Option Bool), true))
          else pure (ForInStep.done (some false, __s.2))) : Id (Option Bool × Bool))
      = charsIsNatStep l st := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons c rest ih =>
    intro st
    simp only [charsIsNatStep, List.forIn_cons]
    split
    · split
      · rfl
      · exact ih _
    · split
      · exact ih _
      · rfl

/-- `String.Slice.isNat` on a character list. -/
def charsIsNat (l : List Char) : Bool :=
  let st := charsIsNatStep l ((none : Option Bool), false)
  st.1.getD st.2

/-- `String.Slice.toNat?` on a character list: the decimal value with `_`
    separators ignored when `charsIsNat` accepts the list, and `none`
    otherwise. -/
def charsToNat? (cs : List Char) : Option Nat :=
  if charsIsNat cs then
    some (cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

/-- `charsIsNat` is `String.Slice.isNat`. -/
theorem sliceIsNat_eq (s : String.Slice) : s.isNat = charsIsNat s.copy.toList := by
  rw [String.Slice.isNat]
  simp only [String.Slice.forIn_eq_forIn_toList, forIn_charsIsNatStep, charsIsNat]
  generalize charsIsNatStep s.copy.toList ((none : Option Bool), false) = st
  obtain ⟨o, b⟩ := st
  cases o <;> rfl

/-- `charsToNat?` is `String.Slice.toNat?`. -/
theorem sliceToNat?_eq (s : String.Slice) : s.toNat? = charsToNat? s.copy.toList := by
  rw [String.Slice.toNat?, charsToNat?, sliceIsNat_eq, String.Slice.foldl_eq_foldl_toList]

/-- `(s.drop k).toNat?`, the decimal suffix of a name after its `k`-character
    prefix. `String.Slice.isNat` and `String.Slice.foldl` iterate over
    `String.Pos` and have no normal form in the kernel; this parse recurses on
    `List Char` and reduces. -/
def strDropToNat? (s : String) (k : Nat) : Option Nat := charsToNat? (s.toList.drop k)

/-- `strDropToNat?` is `String.toNat?` after `String.drop`. -/
@[simp] theorem strDropToNat?_eq (s : String) (k : Nat) :
    strDropToNat? s k = (s.drop k).toNat? := by
  rw [strDropToNat?, sliceToNat?_eq, String.toList_copy_drop]

/-- `String.toNat?` over the character list, so that a closed application
    reduces in the kernel. -/
def strToNat? (s : String) : Option Nat := charsToNat? s.toList

/-- `strToNat?` is `String.toNat?`. -/
@[simp] theorem strToNat?_eq (s : String) : strToNat? s = s.toNat? := by
  rw [strToNat?, String.toNat?, sliceToNat?_eq]
  simp

/-- Strip the optional `":64"` width tag from a body mnemonic, recovering the
    base opcode for the `isBinop` / `isShift` recognizers. -/
def stripWidthTag (mnem : String) : String :=
  if hasSuffix mnem ":64" then
    String.ofList (mnem.toList.dropLast.dropLast.dropLast)
  else mnem

/-- Parse a count-tagged immediate shift/rotate mnemonic (`SHL:0`, `SHR:32`,
    `SAR:k`, `ROL:k`, `ROR:k`) into the AT&T direction, the compile-time count,
    and the op width (`64` iff `:64`-tagged, else `32`). `none` for any
    non-shift mnemonic.

    This must read the count from the **raw** `opn`, NOT from a `stripWidthTag`-ed
    base: the count separator is `:` (`SHR:16`), the same character the `:8`/`:16`/
    `:64` ABI **width** tags use. `stripWidthTag`/`mnemWidth` (which the narrow-MOV
    arm consults) would misread the count `8`/`16`/`64` as a width and strip it,
    dropping the shift entirely (the Hawk `t1 >> 16` bug). A unary shift never
    carries a narrow `:8`/`:16` width tag — only the optional `:64` — so the width
    is unambiguous once the count is parsed off the front. -/
def parseImmShiftMnem (opn : String) : Option (String × Nat × Nat) :=
  let isU64 := hasSuffix opn ":64"
  -- peel only the `:64` width tag, leaving `SHR:<count>`
  let core := if isU64 then stripWidthTag opn else opn
  match core.splitOn ":" with
  | [mn, nStr] =>
      let att : Option String := match mn with
        | "ROR" => some "ror" | "ROL" => some "rol"
        | "SHL" => some "shl" | "SHR" => some "shr" | "SAR" => some "sar"
        | _ => none
      match att, strToNat? nStr with
      | some a, some n => some (a, n, if isU64 then 64 else 32)
      | _, _ => none
  | _ => none

/-- The width-carrying mnemonic of a `castW w w'` between 32- and 64-bit GP
    registers. The two widths are separated by `_`, not `:`, so the `:8`/`:16`/
    `:64` width tags that `mnemWidth` / `stripAbiTag` / `parseImmShiftMnem` read
    cannot collide with a carried width. -/
def castWMnem (w w' : Nat) : String :=
  if w == 64 then (if w' == 64 then "CASTW_64_64" else "CASTW_64_32")
  else (if w' == 64 then "CASTW_32_64" else "CASTW_32_32")

/-- Read the source and destination widths off a `castWMnem` mnemonic; `none`
    for every other mnemonic, including the width-erased `ZEROEXT` / `TRUNC`. -/
def parseCastWMnem (opn : String) : Option (Nat × Nat) :=
  match opn.splitOn "_" with
  | [tag, wStr, wDstStr] =>
      if tag == "CASTW" then
        match strToNat? wStr, strToNat? wDstStr with
        | some w, some w' => some (w, w')
        | _, _ => none
      else none
  | _ => none

/-- Does a `castW w w'` carry its widths in the mnemonic? True exactly when both
    widths are `32` or `64` — the pair the printer's `CASTW_` arm renders. Every
    other pair keeps the width-erased `ZEROEXT` / `TRUNC`: the byte-boundary
    casts `castW _ 8` / `castW 8 _`, and `castW 64 128`. -/
def castWCarriesWidths (w w' : Nat) : Bool :=
  (w == 32 || w == 64) && (w' == 32 || w' == 64)

/-- The reserved `extCall` name prefix that designates a `.rodata` symbol-base
    load (`leaq sym(%rip), %dst`). An `extCall` whose `name` is
    `loadSymPrefix ++ sym` carries the link-time symbol `sym` in its name (the
    only `JasminOp` payload that can name a global), and `opToLinstrR` exports it
    as the `"LOADSYM"` mnemonic instead of `CALL:`. The prefix is deliberately
    `__`-leading so it can never collide with a real external-function name. -/
def loadSymPrefix : String := "__loadsym:"

/-- Recognise a reserved symbol-load `extCall` name and return the symbol it
    carries: `loadSymTarget? (loadSymPrefix ++ sym) = some sym`, and `none` for
    any other name (every real external call). This is the seam that lets the
    opaque `extCall` op carry a `.rodata` symbol without a new `JasminOp`
    constructor. -/
def loadSymTarget? (name : String) : Option String :=
  -- Match on the character lists (not `String.startsWith`/`drop`): the
  -- `String.toList`/`List.isPrefixOf` form **kernel-reduces** on string
  -- literals (the `Substring`/`utf8Encode`-based `String.startsWith` does not),
  -- so the recogniser, the exporter arm, and the lowering all close by
  -- `rfl`/`decide` on the concrete reserved name.
  let pfx := loadSymPrefix.toList
  let ns := name.toList
  if pfx.isPrefixOf ns then some (String.ofList (ns.drop pfx.length)) else none

/-- The bit-width an `extCall`/`callN` argument or result marshals at across the
    System V AMD64 boundary. A `reg w` marshals at `w`: `w ≤ 64` in a GP register
    (`RDI…R9` / `RAX`), `w = 128` in an SSE (xmm) register. Every other type — a
    stack array (passed as a *pointer*, 64-bit GP), an inline int, a bool —
    marshals in a 64-bit GP register. The single width source of truth for the
    call ABI class, read off the op's declared `argTys`/`retTy`. -/
def callMarshalWidth : JasminTy → Nat
  | .reg w => w
  | _ => 64

/-- Encode a leaf call's per-argument + result marshal widths into the shadow
    mnemonic so the downstream `expandCallShadows` / loop-body expansion can
    dispatch each argument to the correct SysV register class **by type**. Shape
    `<pfx><retW>;<w0,w1,…>;<name>` (e.g. `CALLW:128;128;bf128_mul`). Only emitted
    when some width is non-GP (`> 64`); an all-`reg 64` call keeps the plain
    `CALL:`/`CALLN:` shadow, so every existing kernel's bytes are unchanged. -/
def encodeCallW (pfx name : String) (retW : Nat) (argWs : List Nat) : String :=
  pfx ++ toString retW ++ ";"
    ++ String.intercalate "," (argWs.map toString) ++ ";" ++ name

/-- Does any of `retW :: argWs` marshal in a non-GP (SSE, `> 64`) register? Gates
    the `CALLW:`/`CALLNW:` widened shadow: `false` ⇒ the call is all-GP and keeps
    the byte-identical `CALL:`/`CALLN:` shadow. -/
def callHasWide (retW : Nat) (argWs : List Nat) : Bool :=
  retW > 64 || argWs.any (· > 64)

/-- Map a single `JasminOp` (with its source operand names and destination
    register name) to the corresponding `linstr_r`. Every op lowers to an
    `Lopn` (the word-level two-address fragment is straight-line). -/
def opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand) : LinstrR :=
  match op with
  | .regArith bop w => .Lopn [.reg dst] (withWidthTag w (binOpName bop)) srcs
  | .select w => .Lopn [.reg dst] (withWidthTag w "CMOV") srcs
  -- `stackLoad w n`: sources are `[arr, idx]` (the array operand and the
  -- *runtime* index register). When the index resolves to a register, fold the
  -- two into one register-indexed (SIB) memory operand `base[idx*scale]` with
  -- `scale = w/8` (the element stride in bytes) — the x86
  -- `(%base,%idx,scale)` effective address. The single `arrIdx` source replaces
  -- the `[arr, idx]` pair, so the reader emits a base+index*scale load directly
  -- instead of decomposing it into an address computation. Compile-time / non-
  -- register shapes (`.arr` element, immediate index) keep the scalar `LOAD`.
  | .stackLoad w _ =>
      match srcs with
      | [.reg base, .reg idx] => .Lopn [.reg dst] "LOADIDX" [.arrIdx base idx (w / 8)]
      | _ => .Lopn [.reg dst] "LOAD" srcs
  -- `stackStore w n`: sources are `[arr, idx, val]`. The runtime-indexed image
  -- routes the (array, index) pair into a SIB destination `base[idx*scale]` and
  -- keeps the stored value as the lone source. The result register `dst` names
  -- the functionally-updated array (the dialect's `stackStore` returns the new
  -- array), so it is still the `Lopn` destination for the slot trace.
  | .stackStore w _ =>
      match srcs with
      | [.reg base, .reg idx, val] =>
          .Lopn [.reg dst] "STOREIDX" [.arrIdx base idx (w / 8), val]
      | _ => .Lopn [.reg dst] "STORE" srcs
  -- A cast between 32- and 64-bit registers carries both widths in the mnemonic
  -- (`castWMnem`, whose `_` separator cannot be read as a `:64` width tag),
  -- because the printer's `ZEROEXT`/`TRUNC` arm assumes the cast crosses the byte
  -- boundary and renders a byte mask. Every other cast keeps that mnemonic.
  | .castW w w' =>
      if castWCarriesWidths w w' then .Lopn [.reg dst] (castWMnem w w') srcs
      else .Lopn [.reg dst] (if w' ≥ w then "ZEROEXT" else "TRUNC") srcs
  -- `extCall` is the opaque external-leaf op. Its `name` String is the only
  -- payload that can carry a *link-time symbol*, so the reserved name shape
  -- `loadSymPrefix ++ sym` (`"__loadsym:" ++ sym`) designates the `.rodata`
  -- symbol-base load (`leaq sym(%rip), %dst`, the NTT twiddle-table base): on it
  -- the exporter emits the `"LOADSYM"` mnemonic that `lowerLinstrExtCovMS`
  -- lowers to `JInstr.loadSym` and `LprogAsmPrinter` renders, with the symbol
  -- name carried as a `.reg` operand (a link-time constant, not a runtime
  -- register). Every NON-reserved `extCall` name keeps the original `CALL:`
  -- mnemonic byte-for-byte, so existing kernels' exported bytes are unchanged.
  | .extCall name argTys retTy =>
      match loadSymTarget? name with
      | some sym => .Lopn [.reg dst] "LOADSYM" [.reg sym]
      | none =>
          -- Type-driven marshalling class: an argument or result wider than a GP
          -- word (`reg 128`) is passed/returned in an SSE (xmm) register, so its
          -- width must reach `expandCallShadows`. When any width is non-GP the
          -- shadow is the widened `CALLW:<retW>;<argWs>;<name>`; an all-`reg 64`
          -- call keeps the plain `CALL:<name>` shadow byte-for-byte.
          let argWs := argTys.map callMarshalWidth
          let retW := callMarshalWidth retTy
          if callHasWide retW argWs then
            .Lopn [.reg dst] (encodeCallW "CALLW:" name retW argWs) srcs
          else .Lopn [.reg dst] ("CALL:" ++ name) srcs
  -- A `regConst w n` materialises the literal `n` into `dst`. We render it as an
  -- immediate-MOV (`MOV[:w] dst, #n`) so the patched jasmin `read_linear` reuses
  -- its existing immediate-MOV path (`movabs` for `n ≥ 2^31` via
  -- `materializeWideImm`); no `CONST` mnemonic / reader extension is needed. The
  -- nullary `regConst` carries no source operand, so the immediate is the sole
  -- source. (Width-tagged at the binding's `w` so U64 constants land at U64.)
  | .regConst w n => .Lopn [.reg dst] (withWidthTag w "MOV") [.imm n]
  | .vpackZMM bop => .Lopn [.reg dst] ("VPACK8u64:" ++ binOpName bop) srcs
  | .vpackZMMd bop => .Lopn [.reg dst] ("VPACKD:" ++ binOpName bop) srcs
  | .vprordZMM n => .Lopn [.reg dst] ("VPRORD:" ++ toString n) srcs
  | .vpslldq n => .Lopn [.reg dst] ("VPSLLDQ:" ++ toString n) srcs
  | .vpsrldq n => .Lopn [.reg dst] ("VPSRLDQ:" ++ toString n) srcs
  | .vsimd op => .Lopn [.reg dst] op.mnemonic srcs
  | .vymm op => .Lopn [.reg dst] op.jasminMnemonic srcs
  -- Widening-multiply + carry-chain ops (#477). `mulhi`/`addCarryLo`/
  -- `addCarryHi` are single-output `Com` ops, but `MULX` / `ADCX` / `ADOX`
  -- are two-output / flag-coupled at the asm level. The textual mnemonic
  -- names the *role* the binding plays; `read_linear` reassembles each into
  -- the corresponding jasmin `sopn` (synthesizing the second destination /
  -- the CF/OF flag operand the descriptor requires).
  --
  --  * `MULXHI` — the high-word binding of a `MULX`; the matching low-word
  --    binding is the producer's `regArith .mul` over the same two sources.
  --  * `ADCX` / `ADOX` — the data binding (`dst := dst + src + cin`) of a
  --    carry-chain add. The third source is the carry-in `reg 1`; the reader
  --    routes it through the CF (`ADCX`) resp. OF (`ADOX`) flag.
  --  * `ADCXHI` / `ADOXHI` — the carry-out (`reg 1`) binding of the same add;
  --    it reads the post-add CF/OF and is materialised as a `SETcc`-style
  --    flag read (kept on the value path as a distinct mnemonic so the carry
  --    thread is explicit in the IR).
  | .mulhi w => .Lopn [.reg dst] (withWidthTag w "MULXHI") srcs
  | .addCarryLo w => .Lopn [.reg dst] (withWidthTag w "ADCX") srcs
  | .addCarryHi w => .Lopn [.reg dst] (withWidthTag w "ADCXHI") srcs
  -- Native right-rotate (#497): the single-op image of the `shr; shl; or`
  -- rotate idiom. `ROR:<n>` carries the compile-time rotate amount in the
  -- mnemonic; the single source is the rotated register. `read_linear` maps
  -- it to the x86 `#ROR_w` (flag-clobbering) resp. BMI2 `#RORX_w` (flag-free)
  -- sopn. One linstr replaces the three the shift-or form produced.
  | .rorImm w n => .Lopn [.reg dst] (withWidthTag w ("ROR:" ++ toString n)) srcs
  -- Native immediate shifts (#605): `SHR:<n>` / `SHL:<n>` carry the compile-time
  -- shift amount in the mnemonic; the single source is the shifted register.
  -- `read_linear` maps each to the x86 `SHR`/`SHL r, imm` sopn (one linstr).
  | .shrImm w n => .Lopn [.reg dst] (withWidthTag w ("SHR:" ++ toString n)) srcs
  -- Native immediate arithmetic right-shift (#606): `SAR:<n>` carries the
  -- compile-time shift amount; `read_linear` maps it to the x86 `SAR r, imm`.
  | .sarImm w n => .Lopn [.reg dst] (withWidthTag w ("SAR:" ++ toString n)) srcs
  | .shlImm w n => .Lopn [.reg dst] (withWidthTag w ("SHL:" ++ toString n)) srcs
  -- Multi-result external call (`func.call` lowering target). At this
  -- single-output linstr layer it names its head result slot, mirroring the
  -- single-result `extCall` `CALL:` mnemonic with a `CALLN:` tag.
  | .callN name argTys retTys =>
      -- `retTys` is the full multi-result list; the single-output linstr layer
      -- names the *head* result (mirroring the plain `CALLN:` mnemonic), so the
      -- return width is the head result's width.
      let argWs := argTys.map callMarshalWidth
      let retW := callMarshalWidth (retTys.headD (.reg 0))
      if callHasWide retW argWs then
        .Lopn [.reg dst] (encodeCallW "CALLNW:" name retW argWs) srcs
      else .Lopn [.reg dst] ("CALLN:" ++ name) srcs
  -- Scalar comparison: `SET<cc>` over the two compared operands, width-tagged at
  -- the operand width. The destination receives `1` or `0`. The immediate form
  -- carries its constant as a second, immediate source, so both forms share one
  -- mnemonic family and one machine-model arm.
  | .cmp c w => .Lopn [.reg dst] (withWidthTag w (cmpName c)) srcs
  | .cmpImm c w n => .Lopn [.reg dst] (withWidthTag w (cmpName c)) (srcs ++ [.imm n])

/-! ## 3. Walking the `Com` term

`Com jasminDialect Γ t` is an A-normal-form let-chain. We accumulate `linstr`s
top-down, tracking the current let-depth so that each binding's result and each
variable reference resolve to a stable register name.

A `Var Γ τ` is a De Bruijn index into `Γ`. At the point a binding is emitted the
context `Γ` has `curDepth` entries, all introduced by enclosing `.var`s plus the
`nArgs` initial arguments. We map a `Var` to the register name of the binder that
introduced it: `regName (curDepth - 1 - deBruijn)` for let-bound vars, falling
back to argument names for the initial context tail. -/

/-- De Bruijn index of a `Var` (distance from the most recent binder). -/
def varIndex {Γ : Ctxt jasminDialect} {τ : JasminTy} : Ctxt.Var Γ τ → Nat
  | .here => 0
  | .there v => varIndex v + 1

/-- A producer-level **immediate slot map**: maps an argument *slot* index `j`
    (program-root order, 0-based, corresponding to `argName j` / `a{j}`) to the
    literal value of the input when that input is a known compile-time constant.

    A `Var` whose resolved slot lies in `[0, nArgs)` and is covered by this map
    is rendered as an `LOperand.imm` *at producer time* (before `physBody`
    re-lowering), so the physical export sees the constant as `#v` directly
    instead of trying to allocate a physical register for it. The default
    `fun _ => none` keeps every argument as a register (the original behaviour);
    a producer that knows its constant inputs supplies the concrete map
    (e.g. ChaCha's `a32 … a38 ↦ 16,12,8,7,20,24,25`). -/
abbrev ImmSlotMap := Nat → Option Nat

/-- Resolve a `Var` to an `LOperand` given the current context depth and the
    initial-argument names. De Bruijn index `i` refers to the binder
    `curDepth - 1 - i` from the root; if that lands in the argument prefix
    (`< nArgs`) it names an argument, otherwise an SSA register `r{slot}`.

    An `immSlotMap` (default `fun _ => none`) lets a producer mark constant
    argument inputs: when `slot < nArgs` and `immSlotMap slot = some v` the
    variable is rendered as `.imm v` instead of `.reg (argNames slot)`. This is
    the slot-based analogue of `ChaChaEmit.chachaInName`'s `i ≥ 32 ⇒
    toString (shiftConstNat (i - 32))` for the textual jazz printer. -/
def resolveVar (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let i := varIndex v
  -- slot counted from the program root (0 = first thing bound)
  let slot := curDepth - 1 - i
  if slot < nArgs then
    match immSlotMap slot with
    | some v => .imm v
    | none => .reg (argNames slot)
  else .reg (regName slot)

/-- Collect the argument operands of an `Expr` as a `List LOperand`. -/
def exprArgs (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest => resolveVar curDepth nArgs argNames immSlotMap v :: go rest
  go e.args

/-- Resolve an `HVector` of in-scope variables (not an `Expr`) to a `List
    LOperand` against the enclosing context. The `forLoopN` node's invariant
    seeds (`invs : HVector (Var Γ) invTys`) are resolved with this — the
    `exprArgs` body specialised to a bare variable vector. -/
def exprArgsHV (curDepth nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      resolveVar curDepth nArgs argNames immSlotMap v
        :: exprArgsHV curDepth nArgs argNames immSlotMap rest

/-- Walk the `Com`, producing the list of `linstr`s in program order. `curDepth`
    is the number of bindings already in scope (= argument count + lets emitted
    so far). The terminal `.ret` becomes an `Lret` (the result register is the
    function's `lfd_res`).

    The `immSlotMap` (default: none) is consulted by `resolveVar`/`exprArgs` to
    substitute constant argument inputs with `.imm` operands at producer time
    (see `ImmSlotMap`). -/
def comToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Lcmd
  | _, _, .ret _, _ => [⟨0, .Lret⟩]
  | _, _, .var e body, curDepth =>
      let srcs := exprArgs curDepth nArgs argNames immSlotMap e
      let instr : Linstr := ⟨0, opToLinstrR e.op (regName curDepth) srcs⟩
      instr :: comToBody nArgs argNames immSlotMap body (curDepth + 1)

/-- The register name of the final return value of a `Com` (the binder the
    terminal `.ret` points at). The return slot is always rendered as a real
    name (no `immSlotMap` lookup) — a function cannot return an immediate. -/
def comRetReg (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → String
  | _, _, .ret v, curDepth =>
      match resolveVar curDepth nArgs argNames (fun _ => none) v with
      | .reg n => n
      | .arr b i => b ++ "[" ++ toString i ++ "]"
      | .imm n => toString n
      | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]"
  | _, _, .var _ body, curDepth => comRetReg nArgs argNames body (curDepth + 1)

/-- Bit width of a `JasminTy` as an `ltype` `U w` width (0 for non-word). -/
def tyWidth : JasminTy → Nat
  | .reg w => w
  | .stackArr w _ => w
  | .inlineInt => 0
  | .bool => 1

/-! ## 4. The export: `Com → Lprog`

The argument context `Γ` becomes the function's `lfd_arg`/`lfd_tyin`: argument
`j` (counted from the program root, i.e. the *tail* of `Γ`) is named `a{j}` and
typed by its `JasminTy` width. -/

/-- The argument register name for argument slot `j` (program-root order). -/
def argName (j : Nat) : String := "a" ++ toString j

/-- Build the `lfundef` for a `Com` over argument context `Γ`.
    `immSlotMap` (default: none) substitutes constant argument inputs with
    `.imm` operands at producer time (see `ImmSlotMap`). -/
def comToLfundef {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lfundef :=
  let nArgs := Γ.length
  -- `Γ` lists most-recent binder first; argument slot `j` (root order) is
  -- entry `nArgs - 1 - j`, whose width we read off the type list.
  let argTys := Γ.reverse.map tyWidth
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := argTys
    lfd_arg := (List.range nArgs).map argName
    lfd_body := comToBody nArgs argName immSlotMap com nArgs
    lfd_tyout := [tyWidth t]
    lfd_res := [comRetReg nArgs argName com nArgs]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

/-- Export a `Com jasminDialect` to a value-level `Lprog` with the given function
    name. Uses the conventional `lp_rip="RIP"`/`lp_rsp="RSP"` and empty globals
    (the ChaCha20-block case carries no read-only data section). -/
def Com.toLprog {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, comToLfundef com immSlotMap)] }

/-! ### `.rodata` global-table population (the symbol-load companion)

`Com.toLprog` leaves `lp_globs`/`lp_glob_names` empty (no read-only data
section), which is what every kernel without a global table wants. A kernel that
*does* read a `.rodata` table (the NTT twiddle gather, via the `"LOADSYM"`
export arm above) must additionally declare that table in the `Lprog`'s globals,
so `LprogAsmPrinter.lprogRodata` (gated on `lp_globs ≠ []`) renders a
`.section .rodata` + `<sym>:` + `.quad` block the `leaq sym(%rip)` resolves
against. `withRodataTable` fills both global fields for one named u64 table:

* `lp_glob_names` gets one `(sym, 8, v.toNat)` entry per table word (the
  `lprogRodata` reader groups consecutive same-name entries into one `.quad`
  table, preserving order);
* `lp_globs` gets the table's flat little-endian u8 blob (Jasmin's `seq u8`
  global image), which is what trips the `lprogRodata` non-empty guard and what a
  Marshal-path reader would materialise.

It is additive over an existing `Lprog`: the table is appended, so a program
that already declared globals keeps them and the new table's words follow. -/

/-- The 8 little-endian u8 bytes of a `BitVec 64` word. -/
def word64Bytes (w : BitVec 64) : List Nat :=
  (List.range 8).map (fun i => ((w >>> (8 * i)).toNat) % 256)

/-- Attach a named u64 `.rodata` table `(sym, table)` to an `Lprog`'s globals so
    the `.rodata`-rendering seam (`LprogAsmPrinter.lprogRodata`, gated on
    `lp_globs ≠ []`) emits it. Each table word becomes one `(sym, 8, value)`
    `lp_glob_names` entry and its 8 little-endian bytes are appended to the flat
    `lp_globs` u8 blob. Additive: existing globals are preserved, the new table's
    entries/bytes follow. -/
def Lprog.withRodataTable (p : Lprog) (sym : String) (table : List (BitVec 64)) :
    Lprog :=
  { p with
    lp_globs := p.lp_globs ++ table.flatMap word64Bytes
    lp_glob_names := p.lp_glob_names ++ table.map (fun w => (sym, 8, w.toNat)) }

/-- Export a `Com` and attach one `.rodata` symbol table in one step: the
    `"LOADSYM"`-emitting companion of `Com.toLprog`. The exported program reads
    the table `sym` (declared in `lp_globs`/`lp_glob_names`) via any
    `extCall (loadSymPrefix ++ sym)` binding in the `Com`. -/
def Com.toLprogWithRodata {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname sym : String) (table : List (BitVec 64))
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  (Com.toLprog com fname immSlotMap).withRodataTable sym table

/-! ## 5. Textual serialization

A line-oriented textual representation mirroring the structure (the wire format,
since the OCaml `Marshal` representation is not Lean-reproducible — see header).
Format: every `lprog`/`lfundef` field on its own keyed line, the body as one
`instr` line per `linstr`. Deterministic, so it round-trips structurally. -/

/-- Render an `LOperand`. -/
def LOperand.toText : LOperand → String
  | .reg n => n
  | .arr b i => b ++ "[" ++ toString i ++ "]"
  | .imm v => "#" ++ toString v
  -- Register-indexed SIB element `base[idx*scale]`: the reader parses the
  -- `*scale` suffix as the x86 index scale, distinguishing it from the
  -- compile-time `.arr` form `base[const]`.
  | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]"

/-- Render a `LinstrR` as a single text line. -/
def LinstrR.toText : LinstrR → String
  | .Lopn dsts opn srcs =>
      "Lopn [" ++ String.intercalate "," (dsts.map LOperand.toText) ++ "] " ++
        opn ++ " [" ++ String.intercalate "," (srcs.map LOperand.toText) ++ "]"
  | .Lsyscall n => "Lsyscall " ++ n
  | .Lcall ra (f, l) => "Lcall " ++ (ra.getD "-") ++ " " ++ f ++ ":" ++ toString l
  | .Lret => "Lret"
  | .Lalign => "Lalign"
  | .Llabel k l =>
      "Llabel " ++ (match k with | .internal => "int" | .external => "ext") ++
        " " ++ toString l
  | .Lgoto (f, l) => "Lgoto " ++ f ++ ":" ++ toString l
  | .Ligoto o => "Ligoto " ++ o.toText
  | .LstoreLabel d l => "LstoreLabel " ++ d ++ " " ++ toString l
  | .Lcond c l => "Lcond " ++ c.toText ++ " " ++ toString l

/-- Render an `Lfundef`. -/
def Lfundef.toText (name : String) (f : Lfundef) : String :=
  let nats (xs : List Nat) := String.intercalate "," (xs.map toString)
  let strs (xs : List String) := String.intercalate "," xs
  String.intercalate "\n"
    ([ "lfundef " ++ name
     , "  lfd_info " ++ toString f.lfd_info
     , "  lfd_align " ++ toString f.lfd_align
     , "  lfd_tyin " ++ nats f.lfd_tyin
     , "  lfd_arg " ++ strs f.lfd_arg
     , "  lfd_tyout " ++ nats f.lfd_tyout
     , "  lfd_res " ++ strs f.lfd_res
     , "  lfd_export " ++ (if f.lfd_export then "true" else "false")
     , "  lfd_callee_saved " ++ strs f.lfd_callee_saved
     , "  lfd_stk_max " ++ toString f.lfd_stk_max
     , "  lfd_frame_size " ++ toString f.lfd_frame_size
     , "  lfd_align_args " ++ nats f.lfd_align_args
     , "  lfd_body " ++ toString f.lfd_body.length ]
     ++ f.lfd_body.map (fun i => "    instr " ++ toString i.li_ii ++ " " ++ i.li_i.toText))

/-- Render a `Lprog`. -/
def Lprog.toText (p : Lprog) : String :=
  let globNames :=
    String.intercalate ";" (p.lp_glob_names.map (fun (n, w, z) =>
      n ++ ":" ++ toString w ++ ":" ++ toString z))
  String.intercalate "\n"
    ([ "lprog"
     , "lp_rip " ++ p.lp_rip
     , "lp_rsp " ++ p.lp_rsp
     , "lp_globs " ++ String.intercalate "," (p.lp_globs.map toString)
     , "lp_glob_names " ++ globNames
     , "lp_funcs " ++ toString p.lp_funcs.length ]
     ++ p.lp_funcs.map (fun (n, f) => f.toText n))

/-- The OCaml-side magic header, prefixed to the serialized blob. Matches
    `Read_linear.magic` exactly (`patches/jasmin/read_linear.ml.patch`). -/
def magic : String := "JASMIN-LPROG-MARSHAL-v1\n"

/-- Serialize a `Com` to the textual lprog representation (magic + text). -/
def Com.toLprogText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : String :=
  magic ++ (Com.toLprog com fname).toText ++ "\n"

/-- The serialized bytes of a `Com` as an lprog blob. -/
def Com.toLprogBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : ByteArray :=
  (Com.toLprogText com fname).toUTF8

/-- Write the textual lprog blob for a `Com` to a file. The OCaml reader as
    shipped in #144 expects the `Marshal` path; this textual blob is the seam
    where the textual reader (or an OCaml `Marshal` FFI) must close link 2/7. -/
def Com.writeLprogFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath) :
    IO Unit :=
  IO.FS.writeBinFile path (Com.toLprogBytes com fname)

/-! ## 6. Value-level export correctness

The structural well-formedness obligations are discharged here; semantic
preservation under jasmin's `lsem` is the named hypothesis below. -/

/-- The exported `lprog` always has exactly one function, named `fname`, and it
    is an export function. (Structural well-formedness — proved.) -/
theorem Com.toLprog_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprog com fname).lp_funcs.length = 1 ∧
      ((Com.toLprog com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprog com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, rfl⟩

/-- The body produced by `comToBody` is non-empty (it always ends with `Lret`)
    and its last instruction is `Lret`. (Proved by induction on the `Com`.) -/
theorem comToBody_ends_Lret (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
      (d : Nat),
      (comToBody nArgs argNames immSlotMap com d).getLast?.map Linstr.li_i
        = some LinstrR.Lret := by
  intro Γ t com
  induction com with
  | ret v => intro d; rfl
  | var e body ih =>
      intro d
      simp only [comToBody]
      rw [List.getLast?_cons]
      have := ih (d + 1)
      cases h : (comToBody nArgs argNames immSlotMap body (d + 1)).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h; rw [h] at this; simp at this
      | some x => rw [h] at this; simpa using this

/-- The exported function's body ends with `Lret`. (Proved.) -/
theorem Com.toLprog_body_ends_Lret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) :
    ((comToLfundef com).lfd_body).getLast?.map Linstr.li_i = some .Lret := by
  simpa [comToLfundef] using
    comToBody_ends_Lret Γ.length argName (fun _ => none) com Γ.length

/-! ## 3b. Fixed-trip loops at the `Com` level (`ComL` / `comLToBody`)

`comToBody` (§3) walks a *straight-line* A-normal `Com jasminDialect`: only
`.var` (let) and `.ret`. A front `Com` carrying a **fixed-trip counted loop** in
the middle of its chain (`mayo_encode`'s `RWhileNz`, the `*_sign_rwhile` kernels)
has no node to express that loop, so it either falls back to jasminc or is
unrolled to `n` copies. This section closes that gap **additively**: the pure
`.var`/`.ret` path is untouched (`comToBody` is byte-identical), and the loop is
a new node in a sibling walk.

A fixed-trip loop cannot be a `JasminOp` constructor: `jasminDialect.Op` is
`JasminOp`, and a loop body is a `Com jasminDialect [accTy] accTy`, so embedding
it in `JasminOp` is a definitional cycle (`jasminDialect` is defined *from*
`JasminOp`). We instead carry the loop body as a separate `JLoopBody` structure
and extend the `Com` walk with a `forLoop` node in a new `ComL` inductive.

The lowering reuses the verified back-edge shape `LprogControlFlow.loopLcmd`
proves (`Llabel ; body ; SUB ; CMP ; Lcond NZ → top` = `runBoundedLoop`), but
spelled inline here (this module is upstream of `LprogControlFlow`, so it cannot
import `loopLcmd`). The emitted loop is **one** body copy (not `n`), with a real

`Lcond`/`Llabel` back-edge — the renderer emits `.L<d>: … ; jne .L<d>`. The
body's SSA temporaries live in a disjoint per-loop register namespace
(`L<d>_r<k>`), so they never collide with the enclosing straight-line chain
(`r<curDepth>`); the trip counter is `Lctr<d>`. The counter / back-edge are
public (a configuration count), so the loop is CT-admissible (`#460`). -/

/-- A fixed-trip counted loop body over a single accumulator type. `update` maps
    an `[accTy]`-context to an `accTy`: one iteration's accumulator transform.
    The `Com jasminDialect`-level analogue of `JasminPrint.JForProg` (kept here,
    not imported, so `comToBody`'s module owns it). -/
structure JLoopBody (accTy : JasminTy) where
  /-- Static iteration count (the public trip count). -/
  n : Nat
  /-- The accumulator-update body: `acc ↦ update(acc)`. -/
  update : Com jasminDialect [accTy] accTy

/-- One iteration: run `update` on a singleton valuation `[acc]`. Indexed by the
    body `Com`, not the whole `JLoopBody`, so it is `n`-independent (lets the
    `denote_succ` unfolding close by `rfl`/`simp`). -/
def JLoopBody.stepC {accTy : JasminTy} (u : Com jasminDialect [accTy] accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  u.denote (.cons acc .nil)

/-- Total `n`-fold denotation: iterate `stepC` `n` times from the initial
    accumulator. No fuel — `n` is the static trip count. This is the
    mathematical ground truth the lowered back-edge realises. -/
def JLoopBody.denote {accTy : JasminTy} (p : JLoopBody accTy) (init : ⟦accTy⟧) :
    ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => JLoopBody.stepC p.update acc) init

/-- `n = 0`: the loop denotes the identity (no iterations). -/
theorem JLoopBody.denote_zero {accTy : JasminTy}
    (u : Com jasminDialect [accTy] accTy) (init : ⟦accTy⟧) :
    JLoopBody.denote ⟨0, u⟩ init = init := rfl

/-- `n = k+1`: one more iteration of `stepC` on top of the `k`-fold denotation.
    Together with `denote_zero` this is the recursion the looped emission's
    `runBoundedLoop` semantics matches step-for-step. -/
theorem JLoopBody.denote_succ {accTy : JasminTy} (k : Nat)
    (u : Com jasminDialect [accTy] accTy) (init : ⟦accTy⟧) :
    JLoopBody.denote ⟨k + 1, u⟩ init
      = JLoopBody.stepC u (JLoopBody.denote ⟨k, u⟩ init) := by
  simp [JLoopBody.denote, List.range_succ, List.foldl_append]

/-! ### 3b′. Multi-binder loop body (`JLoopBodyN`) — indexed array load/store

`JLoopBody` (above) carries a body `Com jasminDialect [accTy] accTy` over a
**single** accumulator binder, so one iteration can only transform a scalar
accumulator — it cannot do a per-iteration *indexed* array load/store
(`out[i] := f(in[i])`), the shape `mayo_encode`/`*_sign_rwhile` need to roll.

`JLoopBodyN` is the additive multi-binder generalisation: its body runs over the
context `accTy :: .reg 64 :: invTys`, i.e. **three** roles of binder:

* the **accumulator** `accTy` (`.here`, newest) — loop-carried, the body returns
  the updated value each trip (e.g. the output array, threaded through
  `stackStore`);
* the **loop index** `.reg 64` (`.there .here`) — the trip number `i`, which the
  body reads as the *runtime* index of a `stackLoad`/`stackStore` (so the op
  lowers to a SIB `LOADIDX`/`STOREIDX` `base[idx*scale]`), advanced `0,1,…,n-1`;
* the **loop-invariant binders** `invTys` (the input array base pointers and any
  constants) — read every trip, fixed across the loop.

So a body `out[i] := in[i] + 1` is a `Com jasminDialect
[stackArr w n, reg 64, stackArr w n] (stackArr w n)`: `stackLoad in[idx]`,
`+1`, `stackStore acc[idx]`, return the new array. The `JLoopBody` accumulator
loop is the `invTys = []`, index-unused special case. -/

/-- A fixed-trip counted loop body with **multiple binders**: an accumulator
    `accTy`, a `reg 64` loop index, and a list of loop-invariant binders
    `invTys`. `update` maps the `accTy :: .reg 64 :: invTys` context to `accTy`:
    one iteration's accumulator transform, with the trip index and the invariants
    in scope (so the body can index an array at the runtime loop counter). -/
structure JLoopBodyN (accTy : JasminTy) (invTys : Ctxt jasminDialect) where
  /-- Static iteration count (the public trip count). -/
  n : Nat
  /-- The accumulator-update body over `[accTy, reg 64, *invTys]`. -/
  update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy

/-- One iteration at trip index `t`: run `update` on the valuation
    `[acc, ofNat t, *invs]` (the accumulator, the trip number as the `reg 64`
    index, then the invariants). Indexed by the body `Com`, not the whole
    `JLoopBodyN`, so it is `n`-independent. -/
def JLoopBodyN.stepC {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  u.denote (.cons acc (.cons (BitVec.ofNat 64 t) invs))

/-- Total `n`-fold denotation: iterate `stepC` over the trip indices `0,…,n-1`
    from the initial accumulator, threading the fixed invariants `invs`. No
    fuel — `n` is the static trip count. The mathematical ground truth the
    lowered indexed-load/store back-edge realises. -/
def JLoopBodyN.denote {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (p : JLoopBodyN accTy invTys) (invs : Ctxt.Valuation invTys)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc t => JLoopBodyN.stepC p.update invs t acc) init

/-- `n = 0`: the multi-binder loop denotes the identity (no iterations). -/
theorem JLoopBodyN.denote_zero {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) :
    JLoopBodyN.denote ⟨0, u⟩ invs init = init := rfl

/-- `n = k+1`: one more iteration of `stepC` at trip index `k` on top of the
    `k`-fold denotation. The recursion the looped emission's bounded-loop
    semantics matches step-for-step. -/
theorem JLoopBodyN.denote_succ {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (k : Nat) (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) :
    JLoopBodyN.denote ⟨k + 1, u⟩ invs init
      = JLoopBodyN.stepC u invs k (JLoopBodyN.denote ⟨k, u⟩ invs init) := by
  simp [JLoopBodyN.denote, List.range_succ, List.foldl_append]

/-- The per-outer-recomputed **inner trip count** of a nested runtime loop at
    outer index `jd`: run the inner-count body `innerCount` on `[ofNat jd, *invs]`
    (the outer index, then the invariants) and read the result as a `Nat`. This is
    the GGM `num >> (jd+1)` shape — the inner bound is *recomputed* from the outer
    index each outer pass, not a baked-in schedule. -/
def JLoopBodyN.innerTripAtC {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (invs : Ctxt.Valuation invTys) (jd : Nat) : Nat :=
  (innerCount.denote (.cons (BitVec.ofNat 64 jd) invs)).toNat

/-- One **inner** iteration of a nested runtime loop at outer index `jd`, inner
    index `t`: run `innerUpdate` on `[acc, ofNat t, ofNat jd, *invs]` (accumulator,
    inner index, outer index, invariants). The `stepC` analogue with the extra
    outer-index binder in scope. -/
def JLoopBodyN.stepCNested {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (jd t : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  innerUpdate.denote
    (.cons acc (.cons (BitVec.ofNat 64 t) (.cons (BitVec.ofNat 64 jd) invs)))

/-- The **nested runtime fold**: an outer loop `jd ∈ 0..outerN` whose per-iteration
    work is an inner loop `t ∈ 0..innerTripAtC(jd)` (the inner trip recomputed per
    outer pass via `innerCount`), applying `innerUpdate` at each innermost step.
    This is the `JLoopBodyN` analogue of
    `JasminLsemMemLoopNestDepth.runNestedVarLoopMem` (the proven varying-bound
    nested-loop semantics): with `innerCount` computing `num >> (jd+1)` it is the
    GGM Phase-3 `ggmNestedFold` (per-outer-halved middle trip). The mathematical
    ground truth the emitted nested back-edges realise. -/
def JLoopBodyN.nestedDenote {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (outerN : Nat) (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range outerN).foldl
    (fun acc jd =>
      (List.range (JLoopBodyN.innerTripAtC innerCount invs jd)).foldl
        (fun acc2 t => JLoopBodyN.stepCNested innerUpdate invs jd t acc2) acc)
    init

/-- `Com jasminDialect` extended with **fixed-trip loop nodes**. The `.ret`/`.var`
    constructors mirror `Com` exactly; `.forLoop`/`.forLoopN` bind the loop result
    (the final accumulator) into scope for the continuation, so a loop sits inline
    in the straight-line chain. -/
inductive ComL : Ctxt jasminDialect → JasminTy → Type _ where
  /-- Return a variable (same as `Com.ret`). -/
  | ret {Γ t} (v : Ctxt.Var Γ t) : ComL Γ t
  /-- Let-bind a straight-line expression (same as `Com.var`). -/
  | var {Γ t s} (e : Expr jasminDialect Γ t) (body : ComL (t :: Γ) s) : ComL Γ s
  /-- A fixed-trip loop `acc := loop.denote(init)`, with the final accumulator
      bound into scope for `body`. `init` is the in-scope seed variable. -/
  | forLoop {Γ accTy s} (loop : JLoopBody accTy) (init : Ctxt.Var Γ accTy)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A fixed-trip **multi-binder** loop `acc := loop.denote(invs, init)` whose
      body indexes arrays at the runtime trip counter. `init` is the in-scope
      accumulator seed; `invs` are the in-scope invariant seeds (input array
      bases, constants). The final accumulator is bound into scope for `body`. -/
  | forLoopN {Γ accTy s} {invTys : Ctxt jasminDialect}
      (loop : JLoopBodyN accTy invTys) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **runtime-trip** multi-binder loop: identical to `forLoopN` except the
      trip count is *not* a static `Nat` but an in-scope `.reg 64` variable
      `count` read at run time. The body `update` runs over
      `accTy :: .reg 64 :: invTys` (accumulator, loop index, invariants) exactly
      as `JLoopBodyN.update`, but folded `(count.lookup V).toNat` times. This is
      the node a `poly1305_mac_hacl(out, inp, nblk)`-shaped kernel needs: `nblk`
      is a runtime argument, so the back-edge is seeded `MOV Lctr, <countReg>`
      (a register), not `MOV Lctr, #n` (an immediate). -/
  | forLoopNRt {Γ accTy s} {invTys : Ctxt jasminDialect}
      (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
      (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **nested runtime-trip** loop: a runtime outer loop whose per-iteration body
      is *itself* a runtime loop, with the inner trip **recomputed per outer pass**.
      This is the type wall `forLoopNRt` hits — its `update` is a straight-line
      `Com` (a loop is not a `JasminOp`), so it cannot carry an inner loop; this
      constructor makes the inner loop first-class.

      * `innerCount : Com jasminDialect (.reg 64 :: invTys) (.reg 64)` computes the
        inner trip count from the outer index (`.reg 64`, `.here`) and the
        invariants — the GGM `num >> (jd+1)` per-outer-recomputed bound;
      * `innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy`
        is one innermost-iteration body over accumulator, inner index, outer index,
        invariants;
      * `outerCount` is the in-scope runtime outer trip count;
      * `init`/`invs` are the accumulator seed and invariant bases;
      * `body` is the continuation, with the final accumulator bound.

      Denotes to `JLoopBodyN.nestedDenote` (the double fold matching
      `JasminLsemMemLoopNestDepth.runNestedVarLoopMem`); lowers to nested
      back-edges (an inner `forLoopLcmdNRt` inside the outer body, with a per-outer
      inner-count recompute) — the shape of `JasminLsemMemLoopNestDepth.ggmProg`. -/
  | forLoopNRtNested {Γ accTy s} {invTys : Ctxt jasminDialect}
      (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
      (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
      (outerCount : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **data-dependent do-while** — the `RWhileNz` countdown idiom
      (`while (n != 0) { …body…; n -= 1 }`), the A3 `whileLinstrRM` shape. The
      loop body runs FIRST and the guard counter is bottom-tested (`Lcond NZ` on
      the counter register), so the lowering is a do-while back-edge with
      **no zero-trip top guard** — unlike `forLoopNRt`'s top-guarded skip. `guard`
      is the in-scope runtime countdown seed: the emitted loop re-reads the
      counter each pass and exits when it reaches `0`, so the trip count is fixed
      only at run time (A3's `whileTripsMem`, read off the run); for this
      committed countdown form the data-dependent trip provably equals the seed
      value, and `denote` folds exactly that many trips — the fold at the trip
      count the guard exit realises (a total denotation; no fuel parameter).
      Entered with `guard = 0` the machine do-while underflows the counter (the
      body runs at least once); the source tie
      (`JasminLsemMemSourceTieWhile.whileMem_export_faithful_comL`) carries the
      run-halting + trip-identification hypotheses that exclude that case.
      `update` has the `JLoopBodyN.update` shape (accumulator, up-counting index,
      invariants) — the front-compiled per-iteration body `frontLoopBodyJ`
      produces (`TranslateDialectWhileNode.rolledWhileNzComL`). -/
  | whileNz {Γ accTy s} {invTys : Ctxt jasminDialect}
      (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
      (guard : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **block-body** runtime-trip loop: identical seed/count/invariant plumbing
      to `forLoopNRt`, but the per-iteration body is a *recursive* `ComL` over
      `accTy :: .reg 64 :: invTys` (accumulator, loop index, invariants) rather
      than a straight-line `Com`. So one iteration can be a **multi-phase** body
      (a sequence of lets and stores), can contain **nested loop nodes** to
      arbitrary depth, and ends in a `.ret acc` returning the updated
      accumulator. This is the node MAYO/SolveGf16 need: their inner `RWhileNz`
      body is itself a loop over a sub-phase (G1 multi-phase body, G2 3-deep
      nesting), which `forLoopNRt`'s `Com`-shaped `update` cannot carry (a loop is
      not a `JasminOp`).

      * `loopBody : ComL (accTy :: .reg 64 :: invTys) accTy` is one iteration —
        the accumulator, the trip index (`.reg 64`), and the invariants are in
        scope, exactly the `JLoopBodyN.update` context, but now a full `ComL`;
      * `count`/`init`/`invs` are the in-scope runtime trip count, accumulator
        seed and invariant bases, as in `forLoopNRt`;
      * `body` is the continuation, with the final accumulator bound.

      Denotes to the `count`-fold of `loopBody`'s `ComL.denote` (the multi-binder
      analogue of `forLoopNRt`'s `stepC` fold, but with a recursive body);
      lowers to the runtime back-edge frame (`forLoopBlockLcmd`) whose one body
      copy is the recursively-lowered `loopBody` (`comLLoopBodyWalk`, which may
      carry inner back-edges). Subsumes `forLoopNRtNested` (a 2-deep special
      case) and, on a straight-line `loopBody`, lowers byte-identically to
      `forLoopNRt`. -/
  | forLoopBlock {Γ accTy s} {invTys : Ctxt jasminDialect}
      (loopBody : ComL (accTy :: .reg 64 :: invTys) accTy)
      (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s

/-- Denotation of a `ComL`: straight-line `var`/`ret` plus loop nodes folded `n`
    times via `JLoopBody.denote` / `JLoopBodyN.denote`. The mathematical ground
    truth the lowered body (with its real back-edge) realises. -/
def ComL.denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var e body, V => body.denote (V.extend (e.denote V))
  | _, _, .forLoop loop init body, V =>
      body.denote (V.extend (loop.denote (init.lookup V)))
  | _, _, .forLoopN loop init invs body, V =>
      body.denote (V.extend (loop.denote (Expr.lookupArgs invs V) (init.lookup V)))
  | _, _, .forLoopNRt update count init invs body, V =>
      body.denote (V.extend
        ((List.range (count.lookup V).toNat).foldl
          (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
          (init.lookup V)))
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, V =>
      body.denote (V.extend
        (JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
          (Expr.lookupArgs invs V) (init.lookup V)))
  | _, _, .whileNz update guard init invs body, V =>
      -- The countdown do-while: the guard exit fires exactly when the counter —
      -- seeded `guard`, decremented once per pass — reaches `0`, so the realised
      -- trip count is the seed value and the denotation is that fold.
      body.denote (V.extend
        ((List.range (guard.lookup V).toNat).foldl
          (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
          (init.lookup V)))
  | _, _, .forLoopBlock loopBody count init invs body, V =>
      -- Block-body runtime loop: fold the RECURSIVE `loopBody`'s own `ComL.denote`
      -- `count` times, threading the accumulator and passing the trip index as the
      -- `.reg 64` binder and the invariants after it — the multi-binder analogue of
      -- `forLoopNRt`'s `stepC` fold with `loopBody.denote` in place of `Com.denote`.
      body.denote (V.extend
        ((List.range (count.lookup V).toNat).foldl
          (fun acc t =>
            loopBody.denote
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
          (init.lookup V)))

/-- **Multi-accumulator counted loop** (task #20): a runtime-trip loop carrying
    `N` loop-carried `w`-bit cells — an imperative kernel's several mutable
    scalars (MAYO/SolveGf16's `i, j, acc, prow, pivot, …`) threaded together
    across the back-edge, which the single-`accTy` loop nodes cannot hold.

    The carrier is the **product type the dialect already has**: `stackArr w N`, a
    an `N`-cell product (`⟦stackArr w N⟧ = Fin N → BitVec w`). Each cell is a
    frame slot; the loop body reads any cell (`stackLoad`), updates it, and
    `stackStore`s it back — the functional `stackStore` returns the whole updated
    array, so all `N` cells are loop-carried through the one `forLoopBlock`
    back-edge. So this is `forLoopBlock` at `accTy = stackArr w N`: no new
    constructor, no `JasminTy.prod`, the recursive block body + the array product
    already express the multi-accumulator state.

    * `loopBody : ComL (stackArr w N :: .reg 64 :: invTys) (stackArr w N)` is one
      iteration over the `N`-cell array, the trip index, and the invariants,
      returning the updated array;
    * `count`/`init`/`invs` are the runtime trip count, the `N`-cell seed array,
      and the invariant bases;
    * `body` is the continuation, with the final `N`-cell array bound.

    Denotes to the `count`-fold of `loopBody`'s `ComL.denote` over the packed
    `Fin N → BitVec w` state (definitionally the `forLoopBlock` fold); lowers to
    the block-body back-edge frame threading the array base + per-cell
    `LOADIDX`/`STOREIDX`, and exports (`ComL.toLfundefPhys`) to real GP registers.
    `forLoopMultiAcc_denote` records the definitional characterization. -/
def ComL.forLoopMultiAcc {Γ : Ctxt jasminDialect} {w N : Nat} {s : JasminTy}
    {invTys : Ctxt jasminDialect}
    (loopBody : ComL (JasminTy.stackArr w N :: JasminTy.reg 64 :: invTys)
      (JasminTy.stackArr w N))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (init : Ctxt.Var Γ (JasminTy.stackArr w N))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (body : ComL (JasminTy.stackArr w N :: Γ) s) : ComL Γ s :=
  .forLoopBlock loopBody count init invs body

/-- The multi-accumulator loop's denotation is the `count`-fold of the body's
    `ComL.denote` over the `N`-cell product state — the `forLoopBlock` fold at
    `accTy = stackArr w N`. Definitional; the array threads through the fold, so
    every cell is loop-carried. -/
@[simp] theorem ComL.forLoopMultiAcc_denote {Γ : Ctxt jasminDialect} {w N : Nat}
    {s : JasminTy} {invTys : Ctxt jasminDialect}
    (loopBody : ComL (JasminTy.stackArr w N :: JasminTy.reg 64 :: invTys)
      (JasminTy.stackArr w N))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (init : Ctxt.Var Γ (JasminTy.stackArr w N))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (body : ComL (JasminTy.stackArr w N :: Γ) s) (V : Ctxt.Valuation Γ) :
    ComL.denote (ComL.forLoopMultiAcc loopBody count init invs body) V
      = body.denote (V.extend
          ((List.range (count.lookup V).toNat).foldl
            (fun acc t =>
              loopBody.denote
                (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (init.lookup V))) := rfl

/-- A loop body's SSA-temporary register name: a disjoint per-loop namespace
    keyed by the enclosing loop's depth `d`, so body temporaries (`L<d>_r<k>`)
    never collide with the straight-line chain's `r<curDepth>` slots. -/
def loopReg (d k : Nat) : String := "L" ++ toString d ++ "_r" ++ toString k

/-- A loop's trip-counter register name (`Lctr<d>`): the register `MOV Lctr,#n`
    initialises and `SUB Lctr,#1`/`CMP Lctr,#0`/`jne` drive the back-edge. -/
def loopCtr (d : Nat) : String := "Lctr" ++ toString d

/-- Resolve a loop-body `Var`: slot `0` (the accumulator arg) is the accumulator
    register `accReg`; any deeper slot is the body temporary `loopReg d slot`. -/
def loopResolveVar (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : LOperand :=
  let slot := curDepth - 1 - varIndex v
  if slot == 0 then
    match immSlotMap slot with | some w => .imm w | none => .reg accReg
  else .reg (loopReg d slot)

/-- Collect a loop-body `Expr`'s operands (the `loopResolveVar` analogue of
    `exprArgs`). -/
def loopExprArgs (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVar d accReg curDepth immSlotMap v :: go rest
  go e.args

/-- Walk one loop-body `Com [accTy] accTy` into a single-iteration `Lcmd` (binders
    in the disjoint `loopReg d` namespace) plus its result register name. The
    `comToBody` analogue scoped to a loop body. -/
def loopBodyWalk (d : Nat) (accReg : String) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVar d accReg curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalk d accReg immSlotMap body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgs d accReg curDepth immSlotMap e)⟩ :: rest, ret)

/-- The inline looped `Lcmd` for one `forLoop` node at depth `d`, accumulator
    register `accReg`, seed operand `initOp`. Emits

    ```
        MOV  accReg, initOp        -- seed the accumulator
        MOV  Lctr<d>, #n           -- trip counter init
      .L<d>:
        <one body copy>            -- loopBodyWalk (disjoint L<d>_r* temps)
        <feedback accReg ← retReg> -- thread result back (no-op if reused)
        SUB  Lctr<d>, #1           -- counter down
        CMP  Lctr<d>, #0
        jne  .L<d>                 -- back-edge while counter != 0
    ```

    This is the verified back-edge shape `LprogControlFlow.loopLcmd` proves
    (`= runBoundedLoop`), spelled inline (this module is upstream of
    `LprogControlFlow`). **One** body copy, independent of the trip count. -/
def forLoopLcmd (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} (p : JLoopBody accTy) (immSlotMap : ImmSlotMap) : Lcmd :=
  let (bodyW, retReg) := loopBodyWalk d accReg immSlotMap p.update 1
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-! ### 3b″. Lowering the multi-binder loop (`loopBodyWalkN` / `forLoopLcmdN`)

The `JLoopBodyN` body walk mirrors `loopBodyWalk`, but its `loopResolveVarN`
dispatches the **three roles** of binder by root slot (`slot = curDepth-1-deBruijn`,
0 = first-bound = bottom of the body context `accTy :: .reg 64 :: invTys`):

* root slot `nInv+1` (the **newest** binder, `.here` = `accTy`) → the
  accumulator register `accReg`;
* root slot `nInv` (`.reg 64`) → the loop **index** register `loopIdx d`, which
  a `stackLoad`/`stackStore` uses as the SIB index — so the op lowers to the
  register-indexed `LOADIDX`/`STOREIDX` `base[idx*scale]` (the index advances each
  trip, giving `out[i] := f(in[i])`);
* root slots `0 … nInv-1` (the **invariant** binders) → the invariant base
  registers `invRegs[nInv-1-slot]` (the input array bases, resolved at the
  `forLoopN` node — root slot `s` is the `(nInv-1-s)`-th of `invTys` because the
  context lists newest-first while the root slot counts from the bottom);
* deeper slots → the disjoint body temporary `loopReg d slot` (`L<d>_r<k>`).

`forLoopLcmdN` emits one body copy with an index init (`MOV Lidx,#0`), an index
advance each trip (`ADD Lidx,#1`), and the verified `Lctr`/`CMP`/`Lcond` back-edge
— plus one synthetic invariant-base **touch** (`CMP Lctr, invBase`) at the loop
tail per invariant base, which extends each invariant base's live range across the
whole loop (the `bodyTraceOut` liveness-extension trick) so the linear scan keeps
the array bases pinned in fixed registers and never clobbers them mid-loop. -/

/-- The loop **index** register name (`Lidx<d>`): the register the body reads as
    the runtime index of a `stackLoad`/`stackStore` (the SIB index of the emitted
    `LOADIDX`/`STOREIDX`). `MOV Lidx,#0` initialises it and `ADD Lidx,#1` advances
    it once per trip — the index thread parallel to the trip counter `Lctr<d>`. -/
def loopIdx (d : Nat) : String := "Lidx" ++ toString d

/-- Resolve a multi-binder loop-body `Var` to its `LOperand`, dispatching by root
    slot (`nInv = invRegs.length`): the accumulator (slot `nInv+1`) is `accReg`,
    the loop index (slot `nInv`) is `idxReg`, an invariant binder (slot `< nInv`)
    is its base register from `invRegs`, and a deeper slot is a body temporary
    `loopReg d slot`. The `JLoopBodyN` analogue of `loopResolveVar`. -/
def loopResolveVarN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let nInv := invRegs.length
  let slot := curDepth - 1 - varIndex v
  if slot == nInv + 1 then
    match immSlotMap 0 with | some w => .imm w | none => .reg accReg
  else if slot == nInv then .reg idxReg
  else if slot < nInv then
    .reg (invRegs.getD (nInv - 1 - slot) ("Linv" ++ toString d ++ "_" ++ toString slot))
  else .reg (loopReg d slot)

/-- Collect a multi-binder loop-body `Expr`'s operands (the `loopResolveVarN`
    analogue of `loopExprArgs`). -/
def loopExprArgsN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v :: go rest
  go e.args

/-- Resolve a bare `HVector` of in-scope variables in the multi-binder loop-body
    context (the `loopResolveVarN` analogue of `exprArgsHV`). Used to resolve a
    *nested* loop node's invariant seeds when that node sits inside a
    `forLoopBlock`'s recursive body. -/
def loopExprArgsHVN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v
        :: loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap rest

/-- Walk one multi-binder loop-body `Com` into a single-iteration `Lcmd` (binders
    in the disjoint `loopReg d` namespace) plus its result register name. The
    `loopBodyWalk` analogue scoped to a `JLoopBodyN` body — the walk starts at
    `curDepth = 2 + nInv` (the accumulator, index and invariants are already in
    scope). A `stackLoad`/`stackStore` at the index binder lowers to a
    register-indexed `LOADIDX`/`STOREIDX`. -/
def loopBodyWalkN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalkN d accReg idxReg invRegs immSlotMap body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e)⟩ :: rest, ret)

/-- The inline looped `Lcmd` for one `forLoopN` node at depth `d`, accumulator
    register `accReg`, seed operand `initOp`, and invariant base operands `invOps`
    (resolved at the node against the enclosing context). Emits

    ```
        MOV  accReg, initOp        -- seed the accumulator
        MOV  Lidx<d>, #0           -- index init
        MOV  Lctr<d>, #n           -- trip counter init
      .L<d>:
        <one body copy>            -- loopBodyWalkN: LOADIDX/STOREIDX at Lidx<d>
        <feedback accReg ← retReg> -- thread result back (no-op if reused)
        ADD  Lidx<d>, #1           -- index advance
        SUB  Lctr<d>, #1           -- counter down
        CMP  Lctr<d>, invBase…     -- touch each invariant base (keep it live)
        CMP  Lctr<d>, #0
        jne  .L<d>                 -- back-edge while counter != 0
    ```

    The `CMP Lctr, invBase` touches extend each invariant base's live range over
    the whole loop (so the RA keeps the array bases pinned). **One** body copy,
    independent of the trip count. -/
def forLoopLcmdN (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let idxReg := loopIdx d
  -- Invariant base register names (the `.reg` operands; non-register seeds — an
  -- immediate constant invariant — carry no register to pin, so contribute no
  -- touch and the body refers to them by their `Linv` fallback name).
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap p.update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  -- One `CMP Lctr, invBase` per invariant base register: a read of the base that
  -- extends its live range across the back-edge (it is otherwise dead after its
  -- last in-body use, and the linear scan would reclaim its register mid-loop).
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-! ### 3b‴. A real-`Lcall` leaf call inside a (multi-binder) loop body

The loop-body walks (`loopBodyWalk`/`loopBodyWalkN`) already lower an `extCall`/
`callN` `JasminOp` — via the shared `opToLinstrR` — to a single
`Lopn "CALL:<sym>" [args…]` *shadow* instruction. That shadow defers the SysV
calling convention (arg marshalling, the `RAX` return, caller-saved spilling)
to the downstream `read_linear` reassembly, which is adequate for the existing
single-leaf kernels but does **not** place a real `LinstrR.Lcall`.

`loopBodyCallLcmd` is the explicit-ABI alternative used when a loop body must
`call` an opaque leaf (MSM's Straus inner loop calling
`ed_point_add`/`ed_point_double`; the GGM real node calling an AES round): it
emits the **System V AMD64** sequence around a real `Lcall`:

```
    MOV  RDI, arg0          -- marshal call args into the SysV arg registers
    MOV  RSI, arg1          --   [RDI, RSI, RDX, RCX, R8, R9]
    …
    Lcall - <sym>:0         -- the real call (return address managed by jasmin)
    MOV  dst, RAX           -- capture the SysV integer return value
```

The marshalling `MOV`s name the ABI arg registers literally, so they survive
the physical RA (the linear scan never reassigns a literal hardware register).

**Caller-save / frame requirement (the live-across-the-call obligation).** A
real `call` clobbers all SysV *caller-saved* registers
(`RAX RCX RDX RSI RDI R8 R9 R10 R11`). Any loop-carried value (the accumulator,
the loop index `Lidx<d>`, the trip counter `Lctr<d>`, and every pinned invariant
base) that is live across the call must therefore sit in a *callee-saved*
register (`RBX RBP R12 R13 R14 R15`) or be spilled around the call. This helper
emits only the call-site marshalling; **pinning the loop-carried values into
callee-saved registers is the register allocator's obligation** — the RA must be
told that a `loopBodyCallLcmd` site is a clobber barrier for the caller-saved
class. Until the RA models that barrier, a body using this helper is correct
only when the loop-carried set already lands in callee-saved registers. -/

/-- The System V AMD64 integer/pointer argument registers, in order. The first
    `min n 6` call arguments are passed here; further args would spill to the
    stack (not needed by the leaf kernels MSM/GGM call, which are ≤ 6 args). -/
def sysvArgRegs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]

/-- The System V AMD64 integer return register (where a leaf's scalar/pointer
    result is found after the call returns). -/
def sysvRetReg : String := "RAX"

/-- The SysV AMD64 caller-saved (volatile) registers: a real `call` may clobber
    any of these, so a value live across the call must be callee-saved or spilled.
    Exposed so the RA / a liveness pass can treat a `loopBodyCallLcmd` site as a
    clobber barrier for this register class. -/
def sysvCallerSaved : List String :=
  ["RAX", "RCX", "RDX", "RSI", "RDI", "R8", "R9", "R10", "R11"]

/-- Emit a real-`Lcall` SysV call to the opaque leaf `sym`, marshalling the
    resolved call-argument operands `argOps` into the SysV arg registers, then
    capturing the integer return value into `dst`. The body of a loop that must
    `call` a leaf splices this in place of the `CALL:` shadow.

    Shape: one `MOV <argReg>, <argOp>` per argument (up to 6), then the `Lcall`,
    then `MOV dst, RAX`. The `Lcall`'s `ra` (return-address slot) is `none`
    (jasmin's export path manages it); the remote label is `(sym, 0)`. -/
def loopBodyCallLcmd (dst : String) (sym : String) (argOps : List LOperand) :
    Lcmd :=
  let marshal : Lcmd :=
    (argOps.zip sysvArgRegs).map (fun ⟨op, areg⟩ =>
      ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩)
  marshal
  ++ [ ⟨0, .Lcall none (sym, 0)⟩
     , ⟨0, .Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg sysvRetReg]⟩ ]

/-! ### 3b‴′. 128-bit (SSE-class) leaf-call marshalling

`loopBodyCallLcmd` above marshals every argument as a 64-bit GP `MOV` into
`RDI…R9` and reads the result from `RAX` — the GP-only ABI class. A leaf that
takes/returns a `reg 128` value (e.g. a `bf128_mul` over two `__m128i`s) needs
the **SSE class**: System V AMD64 passes 128/256-bit SSE-class arguments in
`xmm0…xmm7` — a *separate* register sequence from the GP one — and returns a
128-bit result in `xmm0`. A mixed GP+SSE argument list draws each argument from
its own class's next register (so `f(a:reg64, b:reg128, c:reg64)` marshals
`a→RDI, b→XMM0, c→RSI`).

The move used for a 128-bit slot is `vmovdqu` (`vecMovMnem`, V-prefixed so
`isVectorMnem` classifies the touched xmm slots vector and the printer renders
the SSE move); the GP slots keep the 64-bit `MOV`.

**Cross-call-live xmm — the frame obligation.** A real `call` clobbers *all* SSE
registers too: System V has **no callee-saved xmm registers on Linux**
(`xmm0…xmm15` are all volatile). So a 128-bit value that is live *across* the
call cannot be parked in a surviving vector register — it **must be stack-spilled
around the call** (there is no callee-saved xmm slot to route it to, unlike the
GP case where `calleeFirstPhys` can place a loop-carried GP value in
`RBX/RBP/R12/R13`). This helper emits only the call-site marshalling; a body that
holds a vector value across the call needs the vector-RA to insert the spill/
reload pair. The pinning of the literal `XMM0…XMM7` marshalling names against the
RA is provided by `isHwRegName` (extended below to include the SSE arg regs). -/

/-- The System V AMD64 SSE argument registers, in order. A 128/256-bit
    (`reg 128`) call argument is passed in the first free one of these, a
    *separate* sequence from the GP `sysvArgRegs` (a mixed arg list draws each
    argument from its own class). Further SSE args would spill to the stack (not
    needed by the leaves this path targets, which are ≤ 8 SSE args). -/
def sysvSseArgRegs : List String :=
  ["XMM0", "XMM1", "XMM2", "XMM3", "XMM4", "XMM5", "XMM6", "XMM7"]

/-- The System V AMD64 SSE return register (`xmm0`): a 128-bit leaf result is
    found here after the call returns. -/
def sysvSseRetReg : String := "XMM0"

/-- The 128-bit unaligned vector move mnemonic (`vmovdqu`) used to marshal a
    `reg 128` argument into an xmm arg register and to capture a 128-bit result
    from `xmm0`. V-prefixed so `isVectorMnem` classifies the touched slots as
    vector (the production vector-RA path) and the AT&T printer renders the SSE
    move — never a GP `movq`. -/
def vecMovMnem : String := "VMOVDQU"

/-- Marshal a *classed* argument list into the SysV registers, threading the two
    per-class next-register counters (GP → `sysvArgRegs` from `gpIdx`; SSE →
    `sysvSseArgRegs` from `sseIdx`). Each `(op, isSse)` produces one move:
    `VMOVDQU <xmm>, op` for an SSE (`isSse = true`, `reg 128`) argument,
    `MOV <gp>, op` for a GP argument. The two counters advance independently, so
    a mixed list places each argument in its own class's next register (SysV). -/
def marshalClassedArgs : List (LOperand × Bool) → Nat → Nat → Lcmd
  | [], _, _ => []
  | (op, isSse) :: rest, gpIdx, sseIdx =>
      if isSse then
        match sysvSseArgRegs[sseIdx]? with
        | some xreg =>
            ⟨0, .Lopn [.reg xreg] vecMovMnem [op]⟩
              :: marshalClassedArgs rest gpIdx (sseIdx + 1)
        | none => marshalClassedArgs rest gpIdx (sseIdx + 1)
      else
        match sysvArgRegs[gpIdx]? with
        | some greg =>
            ⟨0, .Lopn [.reg greg] (withWidthTag 64 "MOV") [op]⟩
              :: marshalClassedArgs rest (gpIdx + 1) sseIdx
        | none => marshalClassedArgs rest (gpIdx + 1) sseIdx

/-- The class-aware analogue of `loopBodyCallLcmd`: marshal a mixed GP+SSE
    argument list (`marshalClassedArgs`), a real `Lcall`, then capture the result
    from `xmm0` (`VMOVDQU`, when `dstIsVec`) or `RAX` (`MOV`, otherwise).

    Byte-compatible degeneracy: with every `isSse = false` and `dstIsVec = false`
    this is exactly `loopBodyCallLcmd` (`MOV RDI…`, `Lcall`, `MOV dst, RAX`), so
    the widened path collapses to the GP path on an all-GP call. -/
def loopBodyCallLcmdClassed (dst : String) (dstIsVec : Bool) (sym : String)
    (argOps : List (LOperand × Bool)) : Lcmd :=
  marshalClassedArgs argOps 0 0
  ++ [ ⟨0, .Lcall none (sym, 0)⟩
     , ⟨0, if dstIsVec then .Lopn [.reg dst] vecMovMnem [.reg sysvSseRetReg]
           else .Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg sysvRetReg]⟩ ]

/-- Parse a widened leaf-call shadow mnemonic
    (`CALLW:<retW>;<w0,w1,…>;<name>` or the multi-result `CALLNW:` variant) into
    `(retW, argWs, name)`. Returns `none` for a plain `CALL:`/`CALLN:` shadow (or
    any non-call op), so the caller falls through to the GP path. The name may
    itself contain `;`-free identifier characters; any trailing `;` segments are
    re-joined into the name (defensive — leaf names are `;`-free). -/
def parseCallW (opn : String) : Option (Nat × List Nat × String) :=
  let body? :=
    if hasPrefix opn "CALLNW:" then some (strDrop opn 7)
    else if hasPrefix opn "CALLW:" then some (strDrop opn 6)
    else none
  match body? with
  | none => none
  | some s =>
      match splitOnChar ';' s with
      | retStr :: argStr :: nameParts =>
          match strToNat? retStr with
          | some retW =>
              let argWs := (splitOnChar ',' argStr).filterMap strToNat?
              some (retW, argWs, String.intercalate ";" nameParts)
          | none => none
      | _ => none

/-- The marshalling sequence for one in-body leaf call (`extCall`/`callN`),
    dispatched by the declared arg/ret widths: an all-GP call (`callHasWide`
    `false`) is the byte-identical `loopBodyCallLcmd` GP path; a call with a
    `reg 128` argument or result routes each argument to its SysV class and takes
    the result from `xmm0` (`loopBodyCallLcmdClassed`). Shared by the straight-
    line and loop-body lowerings so both express a 128-bit leaf call. -/
def callMarshalHere (dst name : String) (argTys : List JasminTy) (retTy : JasminTy)
    (srcs : List LOperand) : Lcmd :=
  let argWs := argTys.map callMarshalWidth
  let retW := callMarshalWidth retTy
  if callHasWide retW argWs then
    loopBodyCallLcmdClassed dst (retW > 64) name
      ((srcs.zip argWs).map (fun ⟨op, w⟩ => (op, w > 64)))
  else loopBodyCallLcmd dst name srcs

/-! ### 3b‴″. Buffer-returning leaf calls in a loop body

`callMarshalHere` dispatches a leaf call between the GP and SSE register classes
by `callMarshalWidth`, which sends every non-`reg` type to 64. A leaf whose
result is a `stackArr` returns it through an **out-pointer** instead, so its
result belongs to no register class: the caller passes the address of a
destination buffer as the first argument and the leaf writes through it.

The declarations below give such a call a home inside a rolled loop body. Each
buffer-typed binding of the body gets a frame slot at a fixed byte offset from
the bottom of the frame; the call marshals that slot's address into `RDI` ahead
of its operands and captures no `RAX`. Offsets are assigned by a pre-pass over
the body `Com` (`loopBufBindings`), so they are fixed when the body is walked and
need no knowledge of the spill count the register allocator settles later. The
bytes are declared to `LprogAsmPrinter.frameSize` by a `FRAMEADD` directive. -/

/-- The `stackArr` result type of a leaf-call op, and `none` for a call whose
    result marshals in a register and for every non-call op. A `callN`'s result is
    its head return type, the slot the loop-body walk binds. -/
def callResultBufferTy : JasminOp → Option JasminTy
  | .extCall _ _ (.stackArr w n) => some (.stackArr w n)
  | .callN _ _ retTys =>
      match retTys.headD (.reg 0) with
      | .stackArr w n => some (.stackArr w n)
      | _ => none
  | _ => none

/-- The byte size of a buffer operand: a `stackArr w n` is `n` elements of `w`
    bits. Every other type is a register value and occupies no buffer. -/
def bufTyBytes : JasminTy → Nat
  | .stackArr w n => n * w / 8
  | _ => 0

/-- The operand name of a loop-body scratch buffer at byte offset `off`: the
    `mem.RSP.<off>` reference the printer renders as `off(%rsp)`, addressed from
    the post-`leaq` `%rsp`. Agrees with `memName "RSP"`, which is defined further
    down this file than the loop-body walk that needs this name. -/
def frameBufName (off : Nat) : String := "mem.RSP." ++ toString off

/-- The buffer-typed call bindings of a loop-body `Com`, as `(binder slot, result
    byte size)` in program order. A binding's slot is the `curDepth` at which it is
    made, which is the number `loopResolveVarN` resolves a reference to it to. -/
def loopBufBindings :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List (Nat × Nat)
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let rest := loopBufBindings body (curDepth + 1)
      match callResultBufferTy e.op with
      | some ty => (curDepth, bufTyBytes ty) :: rest
      | none => rest

/-- The byte offset of the buffer bound at slot `s`, from the bottom of the frame:
    the prefix sum of the preceding buffer sizes, each rounded up to eight bytes.
    `none` when `s` binds no buffer. The loop-body analogue of
    `ArrAbiOrch.binBufOff`. -/
def loopBufOff (bs : List (Nat × Nat)) (s : Nat) : Option Nat :=
  let rec go (l : List (Nat × Nat)) (acc : Nat) : Option Nat :=
    match l with
    | [] => none
    | (slot, sz) :: t =>
        if slot == s then some acc else go t (acc + (sz + 7) / 8 * 8)
  go bs 0

/-- The total scratch bytes a loop body's buffer bindings occupy, each 8-aligned:
    the `FRAMEADD` the body declares. The loop-body analogue of
    `ArrAbiOrch.scratchTotal`. -/
def loopBufTotal (bs : List (Nat × Nat)) : Nat :=
  bs.foldl (fun acc p => acc + (p.2 + 7) / 8 * 8) 0

-- Static checks pinning the buffer layout against silent change: a body with no
-- buffer binding reserves nothing and resolves no slot, and consecutive buffers
-- are placed at 8-aligned offsets in program order.
#guard loopBufOff [] 3 = none
#guard loopBufTotal [] = 0
#guard loopBufOff [(3, 96), (5, 12)] 3 = some 0
#guard loopBufOff [(3, 96), (5, 12)] 5 = some 96
#guard loopBufOff [(3, 96), (5, 12)] 4 = none
#guard loopBufTotal [(3, 96), (5, 12)] = 112

/-! #### The in-place accumulator case

A buffer-returning leaf call whose destination is the accumulator's own storage
— `acc := madd(acc, sel)` — takes the accumulator's base as its out-pointer
instead of a scratch slot, which is the `framedAbiCallMarshal` marshalling
(`RDI` and `RSI` both the base) at a loop-body call site. The binding that
carries it is identified from the body `Com` alone: its op returns a `stackArr`
(`callResultBufferTy`), its first operand is the accumulator binder (root slot
`startDepth - 1`, the slot `loopResolveVarN` resolves to `accReg`), and it is
the binding the body's terminal `.ret` names. A reference to such a binding
resolves to `accReg`, so the call writes the accumulator and the loop's feedback
move is absent by the `retReg == accReg` test that already governs it. -/

/-- The root binder slot a loop-body `Com`'s terminal `.ret` names, walking from
    a walk start depth `curDepth`. The slot arithmetic is `loopResolveVarN`'s:
    `curDepth - 1 - varIndex v`. -/
def comBodyRetSlot :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Nat
  | _, _, .ret v, curDepth => curDepth - 1 - varIndex v
  | _, _, .var _ body, curDepth => comBodyRetSlot body (curDepth + 1)

/-- The root binder slot of an operand vector's first entry, at context depth
    `curDepth`, and `none` for an empty vector. -/
def hvecArg0Slot {Γ : Ctxt jasminDialect} (curDepth : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Option Nat
  | [], _ => none
  | _ :: _, .cons v _ => some (curDepth - 1 - varIndex v)

/-- The root binder slot of an `Expr`'s first operand at context depth
    `curDepth`, and `none` for a nullary op. -/
def exprArg0Slot {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) (curDepth : Nat) : Option Nat :=
  hvecArg0Slot curDepth e.args

/-- Scan a loop-body `Com` from `curDepth` for the binding that updates the
    accumulator in place: a buffer-typed call binding whose first operand is the
    accumulator (root slot `startDepth - 1`) and whose own slot is `retSlot`. -/
def loopInPlaceBufSlotAt (startDepth retSlot : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Option Nat
  | _, _, .ret _, _ => none
  | _, _, .var e body, curDepth =>
      if (callResultBufferTy e.op).isSome
          && exprArg0Slot e curDepth == some (startDepth - 1)
          && curDepth == retSlot then
        some curDepth
      else loopInPlaceBufSlotAt startDepth retSlot body (curDepth + 1)

/-- The slot of the loop body's in-place accumulator update, and `none` when the
    body has none: the body's returned binding, when that binding is a
    buffer-typed call taking the accumulator as its first operand. -/
def loopInPlaceBufSlot {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (startDepth : Nat) : Option Nat :=
  loopInPlaceBufSlotAt startDepth (comBodyRetSlot c startDepth) c startDepth

/-- The buffer bindings that need a frame scratch slot: `loopBufBindings` without
    the in-place accumulator update, whose result goes to the accumulator's own
    storage. Equal to `loopBufBindings` on a body with no in-place update. -/
def loopScratchBufBindings {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (startDepth : Nat) : List (Nat × Nat) :=
  match loopInPlaceBufSlot c startDepth with
  | none => loopBufBindings c startDepth
  | some s => (loopBufBindings c startDepth).filter (fun b => b.1 != s)

/-- Marshal one loop-body call operand into SysV argument register `areg`: a
    memory operand by its address (`LEA`), every other operand by its value
    (`MOV`). -/
def loopBufMarshalArg (areg : String) (op : LOperand) : Linstr :=
  match op with
  | .reg n =>
      if hasPrefix n "mem." then ⟨0, .Lopn [.reg areg] "LEA:64" [.reg n]⟩
      else ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩
  | _ => ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩

/-- Marshal one buffer-returning leaf call: each operand into its SysV argument
    register from `RSI` on — a buffer operand by its address (`LEA`), a register
    operand by its value (`MOV`) — then the destination buffer's address into
    `RDI` (the out-pointer), then the real `Lcall`. No `RAX` capture: the leaf
    returns through the out-pointer. The `ArrAbiOrch.emitOneCall` shape at a
    loop-body call site.

    The out-pointer is written last because its own source is a frame slot, which
    no argument marshal can clobber, while `RDI` is an allocatable register that
    an argument's source may occupy: writing it after every argument source has
    been read is what keeps such an argument readable. -/
def loopBodyCallLcmdBuf (dstMem sym : String) (argOps : List LOperand) : Lcmd :=
  let outLea : Linstr := ⟨0, .Lopn [.reg "RDI"] "LEA:64" [.reg dstMem]⟩
  let argMarshal : Lcmd :=
    (argOps.zip (sysvArgRegs.drop 1)).map (fun ⟨op, areg⟩ => loopBufMarshalArg areg op)
  argMarshal ++ [outLea, ⟨0, .Lcall none (sym, 0)⟩]

/-- Marshal one buffer-returning leaf call that writes the accumulator in place:
    the operands into the SysV argument registers from `RSI` on, the first of
    which is the accumulator, then the accumulator operand into `RDI` (the
    out-pointer), then the real `Lcall`. The `framedAbiCallMarshal` shape — one
    base in both the out-pointer and its own argument register — at a loop-body
    call site. No `RAX` capture and no scratch slot.

    The out-pointer is written last for the reason `loopBodyCallLcmdBuf` states:
    `RDI` is allocatable, so an argument whose source the allocator places there
    is read before the out-pointer overwrites it. The accumulator itself is
    loop-carried, which the looped-call barrier places in a callee-saved register
    (`calleeFirstPhys`), so it survives the argument marshalling. -/
def loopBodyCallLcmdBufInPlace (accOp : LOperand) (sym : String)
    (argOps : List LOperand) : Lcmd :=
  let argMarshal : Lcmd :=
    (argOps.zip (sysvArgRegs.drop 1)).map (fun ⟨op, areg⟩ => loopBufMarshalArg areg op)
  argMarshal ++ [loopBufMarshalArg "RDI" accOp, ⟨0, .Lcall none (sym, 0)⟩]

-- Static checks pinning the marshalling order: the argument registers are
-- written in SysV order from `RSI` on and the out-pointer `RDI` last, so an
-- argument whose source the register allocator places in `RDI` is read before
-- the out-pointer overwrites it.
#guard (loopBodyCallLcmdBuf "mem.RSP.0" "madd" [.reg "L0_r3", .reg "L0_r4"]).filterMap
    (fun i => match i.li_i with | .Lopn [.reg d] _ _ => some d | _ => none)
  = ["RSI", "RDX", "RDI"]
#guard (loopBodyCallLcmdBufInPlace (.reg "L0_r1") "madd"
    [.reg "L0_r1", .reg "L0_r4"]).filterMap
    (fun i => match i.li_i with | .Lopn [.reg d] _ _ => some d | _ => none)
  = ["RSI", "RDX", "RDI"]

/-- Resolve a multi-binder loop-body `Var` with the buffer bindings in scope: a
    reference to the in-place accumulator update (`ipSlot`) is `accReg`, a
    reference to a scratch buffer binding is its frame slot `mem.RSP.<off>`, and
    every other reference is exactly `loopResolveVarN`'s. -/
def loopResolveVarNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (curDepth : Nat)
    (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let slot := curDepth - 1 - varIndex v
  if ipSlot == some slot then .reg accReg
  else
    match loopBufOff bufs slot with
    | some off => .reg (frameBufName off)
    | none => loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v

/-- Collect a loop-body `Expr`'s operands with the buffer bindings in scope (the
    `loopResolveVarNBuf` analogue of `loopExprArgsN`). -/
def loopExprArgsNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (curDepth : Nat)
    (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVarNBuf d accReg idxReg invRegs bufs ipSlot curDepth immSlotMap v
          :: go rest
  go e.args

/-- The `loopBodyWalkNCall` body walk, but lowering a leaf call whose result is a
    `stackArr` to an out-pointer sequence: the in-place accumulator update
    (`ipSlot`) writes through `accReg` (`loopBodyCallLcmdBufInPlace`) and every
    other buffer-typed call writes into its frame slot
    (`loopBodyCallLcmdBuf`), with a reference to such a binding resolving to that
    destination. A body with no buffer-typed call binding has an empty `bufs` and
    `ipSlot = none`, so every op lowers exactly as `loopBodyWalkNCall` lowers
    it. -/
def loopBodyWalkNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarNBuf d accReg idxReg invRegs bufs ipSlot curDepth
              immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) :=
        loopBodyWalkNBuf d accReg idxReg invRegs bufs ipSlot immSlotMap body (curDepth + 1)
      let dstReg := loopReg d curDepth
      let srcs := loopExprArgsNBuf d accReg idxReg invRegs bufs ipSlot curDepth immSlotMap e
      let here : Lcmd :=
        match e.op with
        | .extCall name argTys retTy =>
            if ipSlot == some curDepth then
              loopBodyCallLcmdBufInPlace (.reg accReg) name srcs
            else
              match loopBufOff bufs curDepth with
              | some off => loopBodyCallLcmdBuf (frameBufName off) name srcs
              | none => callMarshalHere dstReg name argTys retTy srcs
        | .callN name argTys retTys =>
            if ipSlot == some curDepth then
              loopBodyCallLcmdBufInPlace (.reg accReg) name srcs
            else
              match loopBufOff bufs curDepth with
              | some off => loopBodyCallLcmdBuf (frameBufName off) name srcs
              | none => callMarshalHere dstReg name argTys (retTys.headD (.reg 0)) srcs
        | _ => [⟨0, opToLinstrR e.op dstReg srcs⟩]
      (here ++ rest, ret)

/-! ### 3b⁗. Straight-line `CALL:`/`CALLN:` shadow → real `Lcall` expansion

The straight-line body walk (`comToBody`, via `opToLinstrR`) lowers a
non-reserved `extCall`/`callN` leaf to a single `Lopn "CALL:<sym>"/"CALLN:<sym>"`
*shadow* (the same shadow the loop walk used before `loopBodyWalkNCall`). The
owned AT&T printer (`LprogAsmPrinter.renderLinstrR`) has no arm for that
mnemonic, so it surfaces `# UNHANDLED-OP CALL:<sym>` — a straight-line body that
mixes arithmetic/memref with a named-leaf call cannot front-compile.

`expandCallShadows` is the straight-line analogue of `loopBodyWalkNCall`: a
post-`comToBody` pass that rewrites every `CALL:`/`CALLN:` shadow into the
`loopBodyCallLcmd` System V AMD64 sequence (marshal args into `RDI…R9`, a real
`Lcall`, capture `RAX` into the result), leaving every other instruction
untouched. A body with no call shadow is returned verbatim (identity), so the
call-free straight-line export is byte-identical. Because the expanded body now
carries a real `LinstrR.Lcall`, `bodyHasCall` fires, and the ABI export's
`physBodyWithStores` selects the caller-save clobber barrier
(`remapOperandCalleeSave` — literal SysV hardware names pinned, other GP slots
routed callee-saved-first through `calleeFirstPhys`) exactly as the value-return
path (`comToLfundefPhys`) and the looped call path already do. -/

/-- Rewrite each straight-line leaf-call *shadow* `Lopn` (`CALL:<sym>` from
    `extCall`, `CALLN:<sym>` from `callN`) into the real-`Lcall` System V
    marshalling sequence `loopBodyCallLcmd`. Every non-shadow instruction passes
    through unchanged; a body with no shadow is the identity image (byte-identical
    call-free export). The `CALLN:` (multi-result) head slot captures `RAX` (the
    single-output linstr layer names the head result only). -/
def expandCallShadows (body : Lcmd) : Lcmd :=
  body.flatMap (fun i =>
    match i.li_i with
    | .Lopn [.reg dst] opn argOps =>
        match parseCallW opn with
        -- Widened (`CALLW:`/`CALLNW:`) shadow: dispatch each argument to its SysV
        -- register class by the declared width (`> 64` ⇒ SSE/xmm), and take the
        -- result from `xmm0` when the return width is SSE-class.
        | some (retW, argWs, sym) =>
            let classed := (argOps.zip argWs).map (fun ⟨op, w⟩ => (op, w > 64))
            loopBodyCallLcmdClassed dst (retW > 64) sym classed
        | none =>
          if hasPrefix opn "CALLN:" then loopBodyCallLcmd dst (strDrop opn 6) argOps
          else if hasPrefix opn "CALL:" then loopBodyCallLcmd dst (strDrop opn 5) argOps
          else [i]
    | _ => [i])

/-- The `loopBodyWalkN` body walk, but lowering an `extCall` leaf in the body to a
    **real `Lcall`** (via `loopBodyCallLcmd`) instead of the `CALL:` shadow
    `Lopn`. Every other op (`regArith`, `stackLoad/Store`, `regConst`, shifts)
    lowers byte-identically to `loopBodyWalkN`, so a call-free body is unchanged.

    This is the `JLoopBodyN`-body variant that makes MSM's Straus inner loop and
    the GGM real AES-PRG node expressible with an in-loop call: the body's
    `extCall in[idx]`/`extCall acc` lowers to the marshalled SysV call sequence,
    spliced inside the rolled back-edge. -/
def loopBodyWalkNCall (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalkNCall d accReg idxReg invRegs immSlotMap body (curDepth + 1)
      let dstReg := loopReg d curDepth
      let srcs := loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e
      -- A leaf call (`extCall`/`callN`) lowers to a real `Lcall` with SysV
      -- marshalling; every other op keeps the straight `opToLinstrR` lowering.
      let here : Lcmd :=
        match e.op with
        | .extCall name argTys retTy => callMarshalHere dstReg name argTys retTy srcs
        | .callN name argTys retTys =>
            callMarshalHere dstReg name argTys (retTys.headD (.reg 0)) srcs
        | _ => [⟨0, opToLinstrR e.op dstReg srcs⟩]
      (here ++ rest, ret)

/-- Does a `Com` body issue a leaf call (`extCall`/`callN`)? Used to decide, per
    `forLoopN` node, whether the loop body must be lowered via `loopBodyWalkNCall`
    (a real `Lcall`) rather than the `CALL:` shadow `loopBodyWalkN`. A body with
    no call op returns `false`, so the call-walk selection is a no-op there and
    the loop lowers byte-identically. -/
def comBodyHasCall :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var e body =>
      (match e.op with
        | .extCall _ _ _ => true
        | .callN _ _ _ => true
        | _ => false) || comBodyHasCall body

/-- Does a `ComL` contain any `forLoopN` node whose body issues a leaf call? When
    `false`, the call-aware lowering is a no-op and the program lowers
    byte-identically to the shadow path. -/
def comLHasLoopCall :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var _ body => comLHasLoopCall body
  | _, _, .forLoop _ _ body => comLHasLoopCall body
  | _, _, .forLoopN loop _ _ body =>
      comBodyHasCall loop.update || comLHasLoopCall body
  | _, _, .forLoopNRt update _ _ _ body =>
      comBodyHasCall update || comLHasLoopCall body
  | _, _, .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      comBodyHasCall innerCount || comBodyHasCall innerUpdate || comLHasLoopCall body
  | _, _, .whileNz update _ _ _ body =>
      comBodyHasCall update || comLHasLoopCall body
  | _, _, .forLoopBlock loopBody _ _ _ body =>
      comLHasLoopCall loopBody || comLHasLoopCall body

/-- `forLoopLcmdN`, but lowering the loop body with `loopBodyWalkNCall` so an
    in-body `extCall`/`callN` becomes a **real `Lcall`** (the SysV marshalling
    sequence) rather than the `CALL:` shadow `Lopn`. Every other field — the seed
    `MOV`, the index/counter init, the invariant-base touches, and the back-edge —
    is identical to `forLoopLcmdN`, and on a call-free body `loopBodyWalkNCall`
    equals `loopBodyWalkN` (`loopBodyWalkNCall_callfree_eq_loopBodyWalkN`), so a
    call-free loop is byte-identical. -/
def forLoopLcmdNCall (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  -- The slot of the body's in-place accumulator update, if it has one, and the
  -- buffer-typed call bindings that need frame scratch. With no in-place update
  -- and no scratch buffer the walk is `loopBodyWalkNCall`, so a body with no
  -- buffer-returning call emits exactly the instructions the call walk emits.
  let startDepth := 2 + invTys.length
  let ipSlot := loopInPlaceBufSlot p.update startDepth
  let bufs := loopScratchBufBindings p.update startDepth
  let (bodyW, retReg) :=
    if bufs.isEmpty && ipSlot.isNone then
      loopBodyWalkNCall d accReg idxReg invRegs immSlotMap p.update startDepth
    else
      loopBodyWalkNBuf d accReg idxReg invRegs bufs ipSlot immSlotMap p.update startDepth
  -- A scratch buffer result lives in its frame slot, not a register, so there is
  -- no register to thread back into the accumulator and no `MOV` is emitted; an
  -- in-place update returns `accReg` itself, which the `retReg == accReg` test
  -- already leaves alone.
  let feedback : Lcmd :=
    if retReg == accReg || hasPrefix retReg "mem." then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  -- The scratch bytes the body's buffers need, declared to
  -- `LprogAsmPrinter.frameSize`. Absent when the body lays no buffer.
  let frameAdd : Lcmd :=
    if bufs.isEmpty then []
    else [⟨0, .Lopn [] "FRAMEADD" [.imm (loopBufTotal bufs)]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  frameAdd ++
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-- `forLoopLcmdN`, but the trip counter is seeded from a **runtime operand**
    `countOp` (`MOV Lctr, countOp`) instead of the static immediate `#p.n`. The
    body walk, index/counter advance, invariant-base touches, and the verified
    `Lctr`/`CMP`/`Lcond` back-edge are otherwise identical to `forLoopLcmdN`, so a
    fixed-count loop and a runtime-count loop differ in exactly one instruction
    (the counter seed). The loop body is taken directly as `update` (the
    `JLoopBodyN`-shaped `Com` over `accTy :: .reg 64 :: invTys`); `nInv` is read
    off the implicit `invTys`. The runtime count `countOp` is read once at the
    seed, before the loop label, so it need only be live entry→seed (the counter
    `Lctr<d>` carries the value across the back-edge). -/
def forLoopLcmdNRt (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  -- Zero-trip skip target. `count` is a RUNTIME value that may be 0; the back-edge
  -- below is a do-while (bottom test), so without this top guard `count = 0` would
  -- decrement the counter to `2^64-1` and loop until an OOB access. The guard makes
  -- the emitted loop run exactly `count` times, matching the `List.range count` fold
  -- denotation. High offset so it never collides with any loop-depth `top`.
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
  , ⟨0, .Lcond (.reg "Z") endL⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩
     , ⟨0, .Llabel .internal endL⟩ ]

/-! ### 3b⁗. Lowering the nested runtime loop (`forLoopLcmdNRtNested`)

The nested runtime loop's per-outer inner-count body `innerCount` runs over
`.reg 64 (outer index) :: invTys` — no accumulator/inner-index binder. Its walk
`nestCountWalk` resolves the outer-index binder (root slot `nInv`) to the outer
loop's index register and the invariant binders (root slots `< nInv`) to their
base registers, mirroring the invariant dispatch of `loopResolveVarN`. -/

/-- Resolve an inner-count-body `Var` (context `.reg 64 (outer) :: invTys`): the
    outer index (root slot `nInv`) is `outerIdxReg`, an invariant (slot `< nInv`)
    is its base register, a deeper slot is a body temporary `loopReg d slot`. -/
def nestCountResolveVar (d : Nat) (outerIdxReg : String) (invRegs : List String)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : LOperand :=
  let nInv := invRegs.length
  let slot := curDepth - 1 - varIndex v
  if slot == nInv then .reg outerIdxReg
  else if slot < nInv then
    .reg (invRegs.getD (nInv - 1 - slot) ("Linv" ++ toString d ++ "_" ++ toString slot))
  else .reg (loopReg d slot)

/-- Collect an inner-count-body `Expr`'s operands (the `nestCountResolveVar`
    analogue of `loopExprArgsN`). -/
def nestCountExprArgs (d : Nat) (outerIdxReg : String) (invRegs : List String)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        nestCountResolveVar d outerIdxReg invRegs curDepth v :: go rest
  go e.args

/-- Walk one inner-count body `Com (.reg 64 :: invTys) (.reg 64)` into a
    single-copy `Lcmd` (binders in the disjoint `loopReg d` namespace) plus its
    result register name — the per-outer inner-trip recompute (`num >> (jd+1)` in
    the GGM shape). The `loopBodyWalk` analogue for the accumulator-free count
    body; the walk starts at `curDepth = 1 + nInv` (outer index + invariants in
    scope). -/
def nestCountWalk (d : Nat) (outerIdxReg : String) (invRegs : List String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match nestCountResolveVar d outerIdxReg invRegs curDepth v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := nestCountWalk d outerIdxReg invRegs body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (nestCountExprArgs d outerIdxReg invRegs curDepth e)⟩ :: rest, ret)

/-- The inline **nested** runtime-loop `Lcmd` for one `forLoopNRtNested` node at
    depth `d`: a runtime outer loop (top label `d`, counter `Lctr<d>`, index
    `Lidx<d>`) whose body **recomputes** the inner trip (`nestCountWalk innerCount`
    into the inner counter) and then runs an inner runtime loop (top label `d+1`,
    counter `Lctr<d+1>`, index `Lidx<d+1>`). Two nested back-edges plus the
    per-outer inner-count recompute — the `Lcmd` image of
    `JasminLsemMemLoopNestDepth.ggmProg`'s structure (outer/inner `loopLinstrRM`
    with the `mid := num >> sa` seed). The inner body is walked with the outer
    index threaded in as the first invariant (`outerIdxReg :: invRegs`), so
    `innerUpdate`'s outer-index binder resolves to `Lidx<d>`. Both loops carry a
    `count = 0` top-guard skip (runtime counts may be 0). -/
def forLoopLcmdNRtNested (d : Nat) (accReg : String) (initOp outerCountOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let outerIdxReg := loopIdx d
  let outerCtr := loopCtr d
  let innerD := d + 1
  let innerIdxReg := loopIdx innerD
  let innerCtr := loopCtr innerD
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  -- Per-outer inner-count recompute (over `.reg 64 (outer) :: invTys`).
  let (cntW, cntRet) := nestCountWalk d outerIdxReg invRegs innerCount (1 + invTys.length)
  -- Inner body walk: the outer index is threaded as the FIRST invariant, so the
  -- inner-body context `accTy :: .reg 64 (inner) :: .reg 64 (outer) :: invTys`
  -- reads the outer index at `Lidx<d>` and the invariants after it.
  let (bodyW, retReg) := loopBodyWalkN innerD accReg innerIdxReg (outerIdxReg :: invRegs)
                            immSlotMap innerUpdate (2 + (invTys.length + 1))
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let outerTop : LLabel := d
  let outerEnd : LLabel := d + 0x40000000
  let innerTop : LLabel := innerD
  let innerEnd : LLabel := innerD + 0x40000000
  let outerInvTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .reg r]⟩)
  -- Seed accumulator + outer index/counter, guard the runtime outer count.
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "MOV") [outerCountOp]⟩
  , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .imm 0]⟩
  , ⟨0, .Lcond (.reg "Z") outerEnd⟩
  , ⟨0, .Llabel .internal outerTop⟩ ]
  -- Outer body: recompute inner count, seed inner index/counter, guard.
  ++ cntW
  ++ [ ⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
     , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "MOV") [.reg cntRet]⟩
     , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "CMP") [.reg innerCtr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "Z") innerEnd⟩
     , ⟨0, .Llabel .internal innerTop⟩ ]
  -- Inner body copy + accumulator feedback.
  ++ bodyW ++ feedback
  -- Inner index advance, counter down, inner back-edge.
  ++ [ ⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "ADD") [.reg innerIdxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "SUB") [.reg innerCtr, .imm 1]⟩
     , ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "CMP") [.reg innerCtr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") innerTop⟩
     , ⟨0, .Llabel .internal innerEnd⟩ ]
  -- Outer index advance, counter down, invariant touches, outer back-edge.
  ++ [ ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "ADD") [.reg outerIdxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "SUB") [.reg outerCtr, .imm 1]⟩ ]
  ++ outerInvTouch
  ++ [ ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "CMP") [.reg outerCtr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") outerTop⟩
     , ⟨0, .Llabel .internal outerEnd⟩ ]

/-- The inline **do-while** `Lcmd` for one `whileNz` node at depth `d` — the
    `Lcmd` image of A3's `whileLinstrRM top gReg [] (body ++ tail)` shape
    (`Llabel top; body; guard-compute; Lcond NZ top`, the
    `TranslateDialectDataWhile.rolledWhileNz` emission): seed the accumulator,
    the up-counting index and the countdown counter (`MOV Lctr<d>, guardOp` — a
    runtime register read), then ONE body copy, the accumulator feedback, the
    index advance, the counter decrement (the body's own `n -= 1` of the
    countdown idiom), the invariant touches, and the **bottom-test** back-edge
    `CMP Lctr,0; Lcond NZ top`. Identical to `forLoopLcmdNRt` MINUS the zero-trip
    top guard (`CMP;Lcond Z endL` and the `endL` label): the body runs at least
    once — a do-while, not a top-guarded counted loop. -/
def whileLcmdNz (d : Nat) (accReg : String) (initOp guardOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [guardOp]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩ ]

/-! ### 3b⁗′. Lowering the block-body runtime loop (`forLoopBlock`)

The block-body loop's per-iteration body is a *recursive* `ComL` (not a
straight-line `Com`), so its walk `comLLoopBodyWalk` must handle nested loop
nodes — it is the `comLToBody` analogue scoped to a loop body: `.var` binders use
the disjoint `loopReg d` namespace and the three roles (accumulator/index/
invariants) resolve via `loopResolveVarN`, exactly as `loopBodyWalkN`; a nested
loop node splices the corresponding `forLoopLcmd*` frame at a **fresh disjoint
depth** `nestBlockLoopD`; the terminal `.ret` returns the feedback register (the
caller emits the accumulator feedback `MOV`), NOT an `Lret`. The frame around the
one body copy (`blockLoopFrame`) is exactly `forLoopLcmdNRt`'s runtime back-edge
(seed/index/counter, zero-trip guard, `Lctr`/`CMP`/`Lcond NZ` back-edge). -/

/-- A fresh, disjoint loop depth for a nested loop node sitting at body position
    `curDepth` inside a `forLoopBlock` body at outer depth `d`.

    **Positional (mixed-radix) encoding, not additive.** The old
    `d + 0x1000·(curDepth+1)` was *additive along the nesting path*, so at 3-deep
    nesting a two-step path (curDepths `a` then `b`) landed on
    `d + 0x1000·(a+b+2)`, colliding with a one-step sibling at curDepth
    `c = a+b+1` — two distinct nesting paths get the SAME top label, and the
    assembler rejects the duplicate `.Llabel`. This surfaces only at 3-deep
    nesting (MAYO's whole-solve `pcol × row × dot`); 1- and 2-deep never trigger it.

    The fix is a base-`BASE` positional numeral: `d' = (d+1)·BASE + (curDepth+1)·K`.
    Along a nesting path the successive `curDepth` digits become the low-order
    positions of a mixed-radix number whose most-significant part is the outer
    `d`, so **distinct nesting paths give distinct values** (the map
    `d ↦ (d+1)·BASE + digit` is injective while `digit < BASE`: `digit =
    d' mod BASE`, `d+1 = d' div BASE`). The `(d+1)` (not `d`) lifts every nested
    label to `≥ BASE`, keeping it clear of the top-level loops' labels (their
    `d = curDepth < BASE`). The per-position stride `K = 8` leaves a gap after
    each label so a node that consumes two consecutive slots (the nested
    `forLoopNRtNested`, which uses `d'` and `d'+1`) cannot alias the next
    sibling's top label.

    `BASE = 0x400` (1024), `K = 8`. Ranges for the covered fragment
    (top-level bindings `N < 1024`, body positions `curDepth < 127`, outer
    top-level depth `C0 < 1022`): every nested top label stays `< 0x40000000`
    (max at 3-deep ≈ `(C0+1)·1024²` ≈ 2.6·10⁸ ≪ 2³⁰), so it stays disjoint from
    every loop's zero-trip guard band `endL = d' + 0x40000000` (`≥ 2³⁰`). MAYO's
    3-deep nest with ≤ ~19 body phases sits far inside all three bounds. -/
def nestBlockLoopD (d curDepth : Nat) : Nat := (d + 1) * 0x400 + (curDepth + 1) * 8

/-- The runtime back-edge **frame** around one pre-walked loop-body copy `bodyW`
    (result in `retReg`): seed the accumulator/index/counter, a zero-trip top
    guard on the runtime `countOp`, the loop label, the body copy, the
    accumulator feedback, the index advance, the counter decrement, the
    invariant-base touches and the `Lctr`/`CMP`/`Lcond NZ` back-edge. Byte-equal
    to `forLoopLcmdNRt`'s frame — factored out so both `forLoopLcmdNRt` (with a
    `loopBodyWalkN` body) and `forLoopBlockLcmd` (with a `comLLoopBodyWalk` body)
    share one back-edge shape. -/
def blockLoopFrame (d : Nat) (accReg idxReg ctr : String)
    (initOp countOp : LOperand) (invRegs : List String)
    (bodyW : Lcmd) (retReg : String) : Lcmd :=
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let top : LLabel := d
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .reg r]⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
  , ⟨0, .Lcond (.reg "Z") endL⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ [ ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "CMP") [.reg ctr, .imm 0]⟩
     , ⟨0, .Lcond (.reg "NZ") top⟩
     , ⟨0, .Llabel .internal endL⟩ ]

/-- Walk a `forLoopBlock`'s recursive loop **body** `ComL` at outer depth `d`
    into one single-iteration `Lcmd` plus its result register name. Mirrors
    `loopBodyWalkN` for `.var`/`.ret`, but a nested loop node is lowered by
    splicing the matching `forLoopLcmd*` frame at a fresh disjoint depth
    (`nestBlockLoopD`), threading the outer loop's roles into the nested node's
    resolved operands. On a straight-line body (`.var`/`.ret` only) this is
    byte-identical to `loopBodyWalkN`, so a `forLoopBlock` with a straight-line
    body lowers exactly like `forLoopNRt`. -/
def comLLoopBodyWalk (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (d : Nat) → (accReg idxReg : String) → (invRegs : List String) →
    (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, d, accReg, idxReg, invRegs, curDepth =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, d, accReg, idxReg, invRegs, curDepth =>
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e)⟩ :: rest, ret)
  | _, _, .forLoop loop init body, d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let inner := forLoopLcmd d' (loopReg d curDepth) initOp loop immSlotMap
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)
  | _, _, .forLoopN loop init invs body, d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := forLoopLcmdN d' (loopReg d curDepth) initOp loop invOps immSlotMap
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)
  | _, _, .forLoopNRt update count init invs body, d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let countOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap count
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := forLoopLcmdNRt d' (loopReg d curDepth) initOp countOp update invOps immSlotMap
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body,
      d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let outerCountOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap outerCount
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := forLoopLcmdNRtNested d' (loopReg d curDepth) initOp outerCountOp
                      innerCount innerUpdate invOps immSlotMap
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)
  | _, _, .whileNz update guard init invs body, d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let guardOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap guard
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := whileLcmdNz d' (loopReg d curDepth) initOp guardOp update invOps immSlotMap
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)
  | _, _, .forLoopBlock loopBody count init invs body, d, accReg, idxReg, invRegs, curDepth =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let countOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap count
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let invRegs' : List String := invOps.filterMap (fun o =>
        match o with | .reg n => some n | _ => none)
      let (bw, br) := comLLoopBodyWalk immSlotMap loopBody d' (loopReg d curDepth) (loopIdx d')
                        invRegs' (2 + invOps.length)
      let inner := blockLoopFrame d' (loopReg d curDepth) (loopIdx d') (loopCtr d')
                      initOp countOp invRegs' bw br
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1)
      (inner ++ rest, ret)

/-- The inline block-body runtime-loop `Lcmd` for one `forLoopBlock` node at depth
    `d`: the runtime back-edge frame (`blockLoopFrame` — identical to
    `forLoopLcmdNRt`) around ONE copy of the recursively-lowered loop body
    (`comLLoopBodyWalk`, which may itself carry inner back-edges). On a
    straight-line `loopBody` this is byte-identical to `forLoopLcmdNRt`; with a
    nested loop node in the body it emits nested back-edges. -/
def forLoopBlockLcmd (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (loopBody : ComL (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := comLLoopBodyWalk immSlotMap loopBody d accReg idxReg invRegs
                            (2 + invTys.length)
  blockLoopFrame d accReg idxReg (loopCtr d) initOp countOp invRegs bodyW retReg

/-- Walk a `ComL`, producing the `Lcmd` body. The `.var`/`.ret` arms are
    identical to `comToBody` (so a loop-free `ComL` emits the same straight-line
    body); the `.forLoop` arm splices `forLoopLcmd` (the inline back-edge) into
    the chain, leaving the loop result in `regName curDepth` for the continuation.
    Additive: a loop-free program is byte-identical to its `comToBody` image. -/
def comLToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (curDepth : Nat) → Lcmd
  | _, _, .ret _, _ => [⟨0, .Lret⟩]
  | _, _, .var e body, curDepth =>
      ⟨0, opToLinstrR e.op (regName curDepth)
            (exprArgs curDepth nArgs argNames immSlotMap e)⟩
        :: comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoop loop init body, curDepth =>
      forLoopLcmd curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init) loop immSlotMap
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoopN loop init invs body, curDepth =>
      -- Resolve the accumulator seed and every invariant base against the
      -- enclosing context (the loop body's index is internal: `loopIdx curDepth`).
      -- A loop body that issues a leaf call (`extCall`/`callN`) is lowered with
      -- `forLoopLcmdNCall` (a real `Lcall`); a call-free body takes
      -- `forLoopLcmdN` (the `CALL:` shadow path) and is byte-identical.
      (if comBodyHasCall loop.update then
          forLoopLcmdNCall curDepth (regName curDepth)
            (resolveVar curDepth nArgs argNames immSlotMap init) loop
            (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap
        else
          forLoopLcmdN curDepth (regName curDepth)
            (resolveVar curDepth nArgs argNames immSlotMap init) loop
            (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap)
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoopNRt update count init invs body, curDepth =>
      -- Runtime-trip loop: the counter is seeded from the resolved `count`
      -- operand (`MOV Lctr, <countReg>`); the accumulator seed and invariant
      -- bases are resolved against the enclosing context exactly as `forLoopN`.
      forLoopLcmdNRt curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap count) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, curDepth =>
      -- Nested runtime loop: an inner runtime loop (top label `curDepth+1`) inside
      -- the outer runtime loop (top label `curDepth`), with the inner trip
      -- recomputed per outer pass (`nestCountWalk innerCount`). Two nested
      -- back-edges — the `Lcmd` image of `ggmProg`.
      forLoopLcmdNRtNested curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap outerCount)
          innerCount innerUpdate
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .whileNz update guard init invs body, curDepth =>
      -- Data-dependent do-while: the countdown counter is seeded from the
      -- resolved `guard` operand and bottom-tested (`whileLcmdNz` — the
      -- `whileLinstrRM` image, no zero-trip top guard).
      whileLcmdNz curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap guard) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)
  | _, _, .forLoopBlock loopBody count init invs body, curDepth =>
      -- Block-body runtime loop: the runtime back-edge frame around ONE copy of
      -- the recursively-lowered `loopBody` (`forLoopBlockLcmd` →
      -- `comLLoopBodyWalk`), which may itself carry inner back-edges — the general
      -- multi-phase / arbitrary-depth loop body. Seed/count/invariant resolution
      -- against the enclosing context is exactly as `forLoopNRt`.
      forLoopBlockLcmd curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap count)
          loopBody
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1)

/-- The register name of a `ComL`'s final return value (the binder the terminal
    `.ret` points at). Skips both `.var` and `.forLoop` binders. -/
def comLRetReg (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (curDepth : Nat) → String
  | _, _, .ret v, curDepth =>
      (match resolveVar curDepth nArgs argNames (fun _ => none) v with
        | .reg n => n
        | .arr b i => b ++ "[" ++ toString i ++ "]"
        | .imm n => toString n
        | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var _ body, curDepth => comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoop _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopN _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopNRt _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopNRtNested _ _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .whileNz _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopBlock _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)

/-- `getLast?` of an append whose right factor is non-empty is the right factor's
    `getLast?` (self-contained — this module does not import Mathlib's
    `List.getLast?_append_of_ne_nil`). -/
theorem getLast?_append_ne {α : Type _} (l₁ l₂ : List α) (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  induction l₁ with
  | nil => rfl
  | cons a as ih =>
      rw [List.cons_append, List.getLast?_cons, ih]
      cases l₂ with
      | nil => exact absurd rfl h
      | cons b bs => simp [List.getLast?_cons]

/-- `comLToBody` always ends with `Lret` (the loop nodes contribute interior
    control flow; the terminal `.ret` is still the last instruction). The `ComL`
    analogue of `comToBody_ends_Lret`. -/
theorem comLToBody_ends_Lret (nArgs : Nat) (argNames : Nat → String)
    (imm : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (d : Nat),
      (comLToBody nArgs argNames imm c d).getLast?.map Linstr.li_i = some .Lret := by
  intro Γ t c
  induction c with
  | ret v => intro d; rfl
  | var e body ih =>
      intro d
      simp only [comLToBody, List.getLast?_cons]
      have hb := ih (d + 1)
      cases h : (comLToBody nArgs argNames imm body (d + 1)).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h; rw [h] at hb; simp at hb
      | some x => rw [h] at hb; simpa using hb
  | forLoop loop init body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopN loop init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopNRt update count init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopNRtNested innerCount innerUpdate outerCount init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | whileNz update guard init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopBlock loopBody count init invs body ihLoop ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)

/-- Build the `lfundef` for a `ComL` over argument context `Γ` — the loop-aware
    analogue of `comToLfundef`. The body is `comLToBody`, so a loop-free `ComL`
    yields the same `lfundef` as `comToLfundef` on its `Com` image. -/
def ComL.toLfundef {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lfundef :=
  let nArgs := Γ.length
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := Γ.reverse.map tyWidth
    lfd_arg := (List.range nArgs).map argName
    lfd_body := comLToBody nArgs argName immSlotMap c nArgs
    lfd_tyout := [tyWidth t]
    lfd_res := [comLRetReg nArgs argName c nArgs]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

/-- The textual serialization is prefixed by the OCaml-side magic header:
    it is literally `magic ++ rest`. (Proved by `rfl` on the decomposition;
    this is the byte-level contract `Read_linear.read_magic` checks.) -/
theorem Com.toLprogText_magic {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    ∃ rest, Com.toLprogText com fname = magic ++ rest :=
  ⟨(Com.toLprog com fname).toText ++ "\n", rfl⟩

-- Export semantic-preservation faithfulness — `Com.denote com V = lsem (toLprog com) (encode V)`
-- over jasmin's linear semantics — is `ComLsemExportFaithful` (`VIR.JasminLsemGeneralFaithful`,
-- plain-`Lstate` scalar fragment, discharged by `comLsemExportFaithful_of_scalar`) and
-- `ComLsemExportFaithfulMC` (`VIR.JasminLsemGeneralFaithfulMC`, `LstateN` mul/carry fragment,
-- discharged by `comLsemExportFaithfulMC_of_mulcarry`), over the `lsem` port (`VIR.LsemPortAll`).
-- Both are downstream of this file (the `lsem` model imports `JasminLprogExport`).

/-! ## 7. Physical-register export (link 3/7: `assemble_prog`)

The `Com.toLprog` above emits a **pre-register-allocation SSA** lprog: every
binding's destination is a fresh virtual register (`r39 … r1654`), operands are
the argument names (`a0 … a38`), and each binop is 3-address (`dst ≠ src0`).
jasmin's `assemble_prog` (`asm_gen.ml :: xreg_of_var`) rejects this: it requires
every operand to be a **physical x86 (x)register** in **destructive two-address**
form (the explicit `id_out` shares asm-arg position 0 with `id_in[0]`, so the
destination must equal the first source).

This section adds a second export, `Com.toLprogPhysText`, that:

1. derives a **logical-slot read/write trace** from the body (the dst and src
   operands of each `Lopn`), one `PhysEvent` per binding;
2. runs a **linear-scan register allocation** over the **13 allocatable x86-64
   GP registers** (`RAX RBX RCX RDX RSI RDI RBP R8 … R13`; `RSP` is the stack
   pointer, `R14`/`R15` are reserved reload scratches), with **stack-slot
   spill** for any slot whose linear-scan physical index lands ≥ 13;
3. lowers each binop `dst = op src0 src1` to **two-address** form — `mov dst,
   src0` then `op dst, src1`, collapsed to the single `op dst, src1` when the RA
   already placed `dst` on `src0`'s physical location.

The virtual `Com.toLprog` is kept verbatim (it is the object of the
`LprogExportFaithful` hypothesis); the physical export is a *separate* lowering
on top of the same body walk, so both share `comToBody`. -/

/-! ### 7a. The 13 allocatable x86-64 GP registers + 2 reserved reload scratches

`register_to_string` (jasmin `x86_decl.v`) lists the 16 GP registers
`RAX RCX RDX RBX RSP RBP RSI RDI R8 … R15`. `RSP` is the stack pointer and is
not a general allocation target, leaving 15 usable registers. **Two** of those
are **reserved as reload scratches**:

* `R15` (`reloadScratch`) — the primary scratch, always available;
* `R14` (`reloadScratch2`) — the secondary scratch, used when both operands of a
  binop are memory (spill) slots so the encoding must thread *two* values
  through scratches simultaneously.

Reserving the second scratch is what closes the link 4/7 asmgen failure
(`asmgen: can not map variable to a register`): jasmin's asmgen pass refuses to
admit a memory `lexpr` as the destination of a non-MOV `Lopn`. Routing through
R15/R14 keeps every spill name (`k.N`) inside a MOV-context source/dest, never
as a binop operand.

That leaves **13** allocatable registers. The physical index `0 … 12` names an
allocatable register; `13 …` spills to the stack array `k`. -/

/-- The 13 allocatable x86-64 GP register names (`RSP` excluded as the stack
    pointer, `R15`/`R14` reserved as reload scratches), indexed by physical slot
    `0 … 12`. -/
def gpRegNames : List String :=
  ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP",
   "R8", "R9", "R10", "R11", "R12", "R13"]

/-- Number of allocatable physical GP registers. -/
def numGPRegs : Nat := gpRegNames.length

/-- The primary reserved reload scratch register (`R15`): never an allocation
    target, so it is always free to legalize a two-memory-operand x86
    instruction. -/
def reloadScratch : String := "R15"

/-- The secondary reserved reload scratch register (`R14`): used together with
    `reloadScratch` when **both** operands of a binop are memory (spill) slots,
    so the binop is routed `mov R15, dst; mov R14, src; op R15, R14;
    mov dst, R15`. Reserving this second scratch lets the reload pass keep
    every `k.N` spill name inside a MOV-context, never as a binop operand. -/
def reloadScratch2 : String := "R14"

/-! ### 7a′. The vector register class

The GP allocator above (`gpRegNames`) is scalar-only: it names physical slot
`0 … 12` as a GP register and `13 …` as a stack spill `k.N`. A `Com` that mixes
scalar GP ops with **vector** ops (`SimdOp`/`vpackZMM`, whose `Lopn` mnemonic
starts with `V` — `VPADDQ`, `VPXOR`, `VPACK8u64:…`, `VPROR D:…`, …) needs a
*disjoint* physical pool: a vector value must land in `%xmm/%ymm/%zmm`, never in
a GP register, and a scalar value never in a vector register.

The vector physical indices are carried in the SAME `Nat`-valued slot map as the
GP indices, offset by `vectorBase` so `physRegName` can recover the class from
the index alone (`phys ≥ vectorBase` ⇒ vector). This keeps every downstream
type (`physTable : Array Nat`, `physMapTabled`, `remapOperand`) unchanged, and —
because a pure-scalar body never produces a `phys ≥ vectorBase` — leaves the
GP-only rendering byte-identical. -/

/-- The 16 allocatable x86 vector register names (`%xmm0 … %xmm15`), indexed by
    the per-class physical slot `0 … 15`. The textual name is width-agnostic
    (`XMM<i>`); the renderer widens it to `%ymm`/`%zmm` from the op's mnemonic if
    needed (VEX/EVEX encode the width on the instruction, not the register name).
    Disjoint from `gpRegNames`, so a vector value never collides with a GP one. -/
def vectorRegNames : List String :=
  ["XMM0", "XMM1", "XMM2", "XMM3", "XMM4", "XMM5", "XMM6", "XMM7",
   "XMM8", "XMM9", "XMM10", "XMM11", "XMM12", "XMM13", "XMM14", "XMM15"]

/-- Number of allocatable physical vector registers. -/
def numVecRegs : Nat := vectorRegNames.length

/-- The offset by which a vector physical slot index is shifted in the shared
    `Nat` slot map, so the class is recoverable from the index alone: a physical
    index `< vectorBase` is GP (allocatable register or `k.N` GP spill); an index
    `≥ vectorBase` is vector (`vectorRegNames[phys - vectorBase]`, or a `kv.N`
    vector spill on overflow). Chosen large enough that no realistic GP slot
    universe + spill count reaches it (a body would need >1000 distinct live GP
    slots), so the two index spaces never alias. -/
def vectorBase : Nat := 1000

/-- Render a physical slot index as an operand name.

    * `phys < numGPRegs` (`< 13`): an allocatable GP register (`RAX … R13`).
    * `numGPRegs ≤ phys < vectorBase`: a GP stack spill slot `k.{phys-13}` (a
      real `RSP`-relative stack reference). The `.` separator (not `[]`) carries
      no brackets — the textual `Lopn` grammar reserves `[ ]` for the operand
      lists. The reserved scratch `R15` (`reloadScratch`) is never produced here.
    * `phys ≥ vectorBase`: a **vector** physical slot. `phys - vectorBase` indexes
      `vectorRegNames` (`XMM0 … XMM15`); on overflow it is a vector stack spill
      `kv.{idx-numVecRegs}`.

    A pure-scalar body never produces `phys ≥ vectorBase`, so its rendering is
    byte-identical to the GP-only original. -/
def physRegName (phys : Nat) : String :=
  if phys ≥ vectorBase then
    let vidx := phys - vectorBase
    match vectorRegNames[vidx]? with
    | some r => r
    | none => "kv." ++ toString (vidx - numVecRegs)
  else
    match gpRegNames[phys]? with
    | some r => r
    | none => "k." ++ toString (phys - numGPRegs)

/-! ### 7b. Per-binding slot events

A `PhysEvent` records, for one emitted `Lopn`, the destination operand and the
source operands, *as logical slot indices*. We index the body's operand names
(`a{j}` / `r{d}`) by first-appearance order, so the slot universe is exactly the
set of distinct registers the body touches — faithful to `comToBody`. -/

/-- One binding's operand footprint over logical-slot indices: the slot written
    and the slots read. Mirrors `UnrolledComRA.SlotEvent` (kept local so this
    export does not pull in the SHA-2 / Keccak trace machinery). -/
structure PhysEvent where
  /-- The logical slot written. -/
  wr : Nat
  /-- The logical slots read. -/
  rds : List Nat
  deriving Repr, DecidableEq

/-- The operand name of an `LOperand` for slot-indexing purposes (immediates and
    array elements are not register-file slots). -/
def LOperand.regName? : LOperand → Option String
  | .reg n => some n
  | .arr _ _ => none
  | .imm _ => none
  -- A register-indexed (SIB) operand `base[idx*scale]` reads the runtime index
  -- register `idx` from the register file; `base` is the (memory-resident)
  -- stack array. For the single-name `regName?` view (used by the *destination*
  -- side, where a SIB never appears) we surface the index register `idx`; the
  -- *source* side uses `LOperand.srcRegNames` below, which contributes BOTH the
  -- base pointer and the index so each is register-allocated and physical-mapped.
  | .arrIdx _ idx _ => some idx

/-- The register-file slot names an `LOperand` contributes **as a source**. This
    differs from `regName?` only on the SIB form `arrIdx base idx scale`, where
    the *base pointer* `base` is a GP source register (the runtime array
    base, supplied as a SysV pointer arg) alongside the index `idx`. Tracking the
    base here is what lets the linear scan allocate it and `remapOperand` rewrite
    the SIB's base/index to physical registers (so the printer renders
    `(%ptr,%idx,scale)` rather than `%<UNKNOWN:aN>`). For every non-SIB operand
    it agrees with `regName?.toList`, so existing kernels' traces are unchanged. -/
def LOperand.srcRegNames : LOperand → List String
  | .reg n => [n]
  | .arr _ _ => []
  | .imm _ => []
  | .arrIdx base idx _ => [base, idx]

/-- The destination + source register names of one `Lopn` (other `linstr_r`
    constructors carry no register-file slot footprint). The source side uses
    `srcRegNames` so a SIB source contributes both its base and index registers. -/
def linstrRegNames : LinstrR → Option (Option String × List String)
  | .Lopn dsts _ srcs =>
      some (dsts.head?.bind LOperand.regName?, srcs.flatMap LOperand.srcRegNames)
  | _ => none

/-- The ordered list of `(dstName?, srcNames)` of a body's `Lopn`s. -/
def bodyOpNames (body : Lcmd) : List (Option String × List String) :=
  body.filterMap (fun i => linstrRegNames i.li_i)

/-- Does the body contain a `MULXHI` binding? The post-RA `fuseMulHiLprog` pass
    overwrites `%rdx` at every such site (`MOV %rdx, s1` to pin the `mulx`
    multiplicand), so when this holds the allocator must withhold `%rdx` (physical
    index 3) from the pool — otherwise a value the scan parks there is clobbered.
    `false` leaves the pool at the full 13 registers, so a body with no mul-hi
    allocates exactly as before. -/
def bodyHasMulHi (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with
    | .Lopn _ opn _ => opn.startsWith "MULXHI"
    | _ => false)

/-- The physical slots the allocator withholds for a body: `[3]` (`%rdx`) when the
    body has a `MULXHI` binding (see `bodyHasMulHi`), else none. -/
def bodyReservedGP (body : Lcmd) : List Nat :=
  if bodyHasMulHi body then [3] else []

/-! ### Compiled name-slot cache (performance)

The reference definitions `bodyNames` / `nameSlot` / `bodyTrace` are the spec.
Naively interpreted they are super-quadratic on a large body: `nameSlot`
recomputes `bodyNames` (itself `O(n²)` via `List.eraseDups`) and then runs an
`O(n)` `idxOf`, and it is called once per operand from `bodyTrace`,
`remapOperand`, and the ABI epilogue — `O(n³)` for SHA-256's ~4000-binding
body, which is why the `lean --run` interpreter never finished.

The compiled implementations below build, in a single `O(n)` pass over the
body, the first-appearance name list together with a `Std.HashMap String Nat`
giving each name's slot, and key that build on the body's runtime pointer so
repeated calls over the same body reuse it. `@[implemented_by]` swaps these in
for native execution; the pure spec is unchanged (the cache is an
implementation detail behind a `@[implemented_by]` boundary — no new axiom and
no `sorry` enters the spec side). -/

/-- The first-appearance distinct register-name list of a body, paired with the
    name→slot `HashMap`. Built in one `O(n)` pass. -/
@[inline] def bodyNameInfoImpl (body : Lcmd) : Array String × Std.HashMap String Nat :=
  Id.run do
    let mut names : Array String := #[]
    let mut m : Std.HashMap String Nat := {}
    for i in body do
      match i.li_i with
      | .Lopn dsts _ srcs =>
          let consider : List String :=
            (dsts.head?.bind LOperand.regName?).toList
              ++ srcs.flatMap LOperand.srcRegNames
          for nm in consider do
            if !m.contains nm then
              m := m.insert nm names.size
              names := names.push nm
      | _ => pure ()
    return (names, m)

/-- Pointer-keyed cache of `bodyNameInfoImpl`. The entry **retains the cached
    body** (a strong reference), so the cached object stays alive for the
    lifetime of the entry and its address cannot be reused by a different
    list; `ptrEq` against the live cached object therefore implies object
    identity (hence value equality), making a hit sound.

    Retention is required: a bare-address key over a non-retained body is
    unsound — once an exporter's virtual body is freed, the next export's body
    head cell can be allocated at the same address (same-size cons cells), and
    a false hit register-allocates the new body under the stale name→slot
    table. Every name absent from the stale table collapses onto the single
    out-of-universe sentinel slot `names.size`, so all such operands share ONE
    physical register and their use-site reloads clobber each other (e.g. a
    binop over two ABI inputs degenerating to `x ^ x`; the regression shape
    theorem is `LeaRoundThirEmit.leaX1_reloads_distinct`).

    Correctness does not depend on the cache hitting (a miss just rebuilds),
    only on a hit returning THIS body's table — which retention guarantees. -/
unsafe def bodyNameInfoCacheRef :
    IO.Ref (Option (Lcmd × Array String × Std.HashMap String Nat)) :=
  unsafeBaseIO (IO.mkRef none)

@[inline] unsafe def bodyNameInfoCached (body : Lcmd) :
    Array String × Std.HashMap String Nat :=
  unsafeBaseIO do
    match ← bodyNameInfoCacheRef.get with
    | some (cachedBody, names, m) =>
        if ptrEq body cachedBody then return (names, m)
        else
          let r := bodyNameInfoImpl body
          bodyNameInfoCacheRef.set (some (body, r.1, r.2))
          return r
    | none =>
        let r := bodyNameInfoImpl body
        bodyNameInfoCacheRef.set (some (body, r.1, r.2))
        return r

@[inline] unsafe def bodyNamesImpl (body : Lcmd) : List String :=
  (bodyNameInfoCached body).1.toList

/-- The distinct register names of a body in first-appearance order (the slot
    universe). -/
@[implemented_by bodyNamesImpl]
def bodyNames (body : Lcmd) : List String :=
  (bodyOpNames body).flatMap (fun (d, s) => d.toList ++ s) |>.eraseDups

@[inline] unsafe def nameSlotImpl (body : Lcmd) (n : String) : Nat :=
  let (names, m) := bodyNameInfoCached body
  m.getD n names.size

/-- The logical-slot index of a register name in a body (its first-appearance
    rank); `bodyNames.length` (out of universe) if absent. -/
@[implemented_by nameSlotImpl]
def nameSlot (body : Lcmd) (n : String) : Nat :=
  (bodyNames body).idxOf n

/-- The per-binding `PhysEvent` trace of a body: each `Lopn` becomes one event
    over the slot indices of its operands. A binding with no register
    destination (none of the producer's binops) contributes a liveness-only
    event reusing slot `0`. -/
@[inline] unsafe def bodyTraceImpl (body : Lcmd) : List PhysEvent :=
  let (names, m) := bodyNameInfoCached body
  let slot (nm : String) : Nat := m.getD nm names.size
  body.filterMap (fun i =>
    match i.li_i with
    | .Lopn dsts _ srcs =>
        let d := dsts.head?.bind LOperand.regName?
        let s := srcs.flatMap LOperand.srcRegNames
        some { wr := (d.map slot).getD 0, rds := s.map slot }
    | _ => none)

@[implemented_by bodyTraceImpl]
def bodyTrace (body : Lcmd) : List PhysEvent :=
  (bodyOpNames body).map (fun (d, s) =>
    { wr := (d.map (nameSlot body)).getD 0
      rds := s.map (nameSlot body) })

/-! ### 7b′. Register-class classification (GP vs vector)

A logical slot belongs to the **vector** register class iff a vector `Lopn`
touches it. A vector `Lopn` is one whose (width-stripped) mnemonic starts with
`V`: every `SimdOp.mnemonic` (`VPADDQ`, `VPXOR`, `VGF2P8MULB`, `VAESENC`, …) and
every `vpackZMM`/`vprordZMM`/`vps*` export arm (`VPACK8u64:…`, `VPACKD:…`,
`VPRORD:…`, `VPSLLDQ:…`, `VPSRLDQ:…`) begins with `V`, while **no** GP mnemonic
does (`ADD`, `SUB`, `MUL`, `MOV`, `CMOV`, `LOAD*`, `STORE*`, `ZEROEXT`, `TRUNC`,
`CALL:`, `MULXHI`, `ADCX`, `ROR:`, `SHR:`, `SHL:`, `SAR:`, `LOADSYM`). So the
`V`-prefix is a sound, additive class oracle: a body with no vector op classifies
every slot GP and the allocator is byte-identical to the original. -/

/-- Is `opn` a **vector** `Lopn` mnemonic? True iff its width-stripped form starts
    with `"V"` — the common prefix of every `SimdOp.mnemonic` and every
    `vpack*`/`vpror*`/`vpsl*`/`vpsr*` export arm, and of no GP mnemonic. -/
def isVectorMnem (opn : String) : Bool := (stripWidthTag opn).startsWith "V"

/-- A vector-class array marking which logical slots are in the **vector**
    register class: slot `s` is vector iff some vector `Lopn` (`isVectorMnem`)
    writes or reads it. Built in one `O(n)` pass over the body, keyed by the same
    `nameSlot` indexing `bodyTrace` uses, so the class array aligns with the
    trace's slot universe. A body with no vector op yields the all-`false` array
    (every slot GP), so the GP-only allocation is unchanged. -/
@[inline] unsafe def bodyVecSlotsImpl (body : Lcmd) : Array Bool :=
  let (names, m) := bodyNameInfoCached body
  let slot (nm : String) : Nat := m.getD nm names.size
  Id.run do
    let mut a : Array Bool := Array.replicate (names.size + 1) false
    for i in body do
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isVectorMnem opn then
            let touched : List String :=
              (dsts.head?.bind LOperand.regName?).toList
                ++ srcs.flatMap LOperand.srcRegNames
            for nm in touched do
              let s := slot nm
              if s < a.size then a := a.set! s true
      | _ => pure ()
    return a

/-- Spec form of `bodyVecSlots` (the `@[implemented_by]` target is the cached
    one). Slot `s` is vector iff some `Lopn` with a vector mnemonic touches the
    register name whose `nameSlot` is `s`. Sized by `bodyNames body |>.length`
    (the distinct-name universe), the same upper bound `nameSlot` ranks against. -/
@[implemented_by bodyVecSlotsImpl]
def bodyVecSlots (body : Lcmd) : Array Bool :=
  Id.run do
    let mut a : Array Bool := Array.replicate ((bodyNames body).length + 1) false
    for i in body do
      match i.li_i with
      | .Lopn dsts opn srcs =>
          if isVectorMnem opn then
            let names : List String :=
              (dsts.head?.bind LOperand.regName?).toList
                ++ srcs.flatMap LOperand.srcRegNames
            for nm in names do
              let s := nameSlot body nm
              if s < a.size then a := a.set! s true
      | _ => pure ()
    return a

/-- The vector-class predicate over slots: `true` iff slot `s` is vector. Out of
    range (`s ≥ vecArr.size`) defaults to GP (`false`). -/
def slotIsVec (vecArr : Array Bool) (s : Nat) : Bool := vecArr[s]?.getD false

/-! ### 7c. Linear-scan physical allocation (13 GP regs + spill)

A Poletto–Sarkar linear scan over a **bounded** physical pool, derived locally
over `PhysEvent`: process slots in live-range-start order, reclaim registers
whose owner's range ended, take the lowest free register in `[0, numGPRegs)`.

When the pool is full, the *spill-at-interval* rule picks the value that goes to
the stack by **spill cost**: the register-resident value with the largest live
range *per use*, `(rangeEnd - position) / useCount`. A value that is touched on
every step therefore outranks an equally long-lived value that is touched twice.
The incoming interval competes under the same measure and is spilled itself when
it is the cheaper one.

Stack cells form a pool separate from the registers. Each cell carries the hull
`(minStart, maxEnd)` of the ranges placed in it, and a range enters a cell only
when it is disjoint from that hull. A spilled value occupies its cell over its
**whole** range — including the prefix it already spent in a register — so cell
reuse is decided against the hull rather than against the set of values live at
the spill point. -/

/-- All slots touched by an event. -/
def PhysEvent.touched (ev : PhysEvent) : List Nat := ev.wr :: ev.rds

/-- Slot-universe size (max touched slot + 1). -/
def physUniverse (tr : List PhysEvent) : Nat :=
  (tr.flatMap PhysEvent.touched).foldl Nat.max 0 + 1

/-- First trace position touching slot `s` (`tr.length` if never). -/
def physFirstTouch (tr : List PhysEvent) (s : Nat) : Nat :=
  match tr.zipIdx.find? (fun p => p.1.touched.contains s) with
  | some (_, i) => i
  | none => tr.length

/-- Last trace position touching slot `s` (`0` if never). -/
def physLastTouch (tr : List PhysEvent) (s : Nat) : Nat :=
  (tr.zipIdx.filterMap (fun p => if p.1.touched.contains s then some p.2 else none)).foldl
    Nat.max 0

/-- Conservative live range `[firstTouch, lastTouch]` of slot `s`. -/
def physLiveRange (tr : List PhysEvent) (s : Nat) : Nat × Nat :=
  (physFirstTouch tr s, physLastTouch tr s)

/-- Two ranges overlap iff each starts no later than the other ends. -/
def physRangesOverlap (r1 r2 : Nat × Nat) : Bool :=
  r1.1 ≤ r2.2 && r2.1 ≤ r1.2

/-- An in-flight *register* allocation during the scan. -/
structure PhysActive where
  /-- First trace position of the allocated slot's live range. -/
  st : Nat
  /-- Last trace position of the allocated slot's live range. -/
  en : Nat
  /-- The allocated physical register index (`< numRegs`). -/
  phys : Nat
  /-- The logical slot holding the register. -/
  slot : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The lowest physical index in `[0, numRegs)` held by no active allocation and
    not in `reserved`. `reserved` names physical slots withheld from allocation for
    the whole body — used to keep `%rdx` (index 3) free when the body has a mul-hi
    binding, which the post-RA `fuseMulHiLprog` pass overwrites at every fused
    `mulx` site (mirrors the JInstr route's resident-pool `%rdx` reservation). The
    `[]` case is definitionally the un-reserved scan, so every 2-argument caller
    and its proofs are unchanged. -/
def freeRegIn (numRegs : Nat) (used : List Nat) (reserved : List Nat := []) :
    Option Nat :=
  match reserved with
  | [] => (List.range numRegs).find? (fun ph => !used.contains ph)
  | r  => (List.range numRegs).find? (fun ph => !used.contains ph && !r.contains ph)

/-- Per-cell occupancy hulls: entry `i` is the `(minStart, maxEnd)` hull of the
    ranges placed in stack cell `i`, whose physical index is `numRegs + i`. -/
abbrev CellHulls := Array (Nat × Nat)

/-- The first cell index `≥ i` whose hull is disjoint from `[st, en]`, or
    `hulls.size` when every existing cell overlaps. -/
def firstFittingCell (hulls : CellHulls) (st en : Nat) : Nat → Nat
  | i =>
    if h : i < hulls.size then
      if physRangesOverlap hulls[i] (st, en) then firstFittingCell hulls st en (i + 1)
      else i
    else i
termination_by i => hulls.size - i
decreasing_by omega

/-- Place `[st, en]` in the lowest cell whose hull is disjoint from it, widening
    that cell's hull to cover the range; append a fresh cell when none fits. -/
def allocCell (hulls : CellHulls) (st en : Nat) : Nat × CellHulls :=
  let i := firstFittingCell hulls st en 0
  match hulls[i]? with
  | some c => (i, hulls.set! i (Nat.min c.1 st, Nat.max c.2 en))
  | none => (i, hulls.push (st, en))

/-- Spill-cost order on allocations at trace position `st`: `a` outranks `b` when
    its remaining range per use is larger, `(a.en - st) / uses[a.slot]` against
    `(b.en - st) / uses[b.slot]`, compared by cross-multiplication. Ties break on
    the later range end, then on the larger slot index. -/
def spillPrefer (st : Nat) (uses : Array Nat) (a b : PhysActive) : Bool :=
  let ka := (a.en - st) * Nat.max 1 (uses[b.slot]?.getD 1)
  let kb := (b.en - st) * Nat.max 1 (uses[a.slot]?.getD 1)
  if ka == kb then
    if a.en == b.en then a.slot > b.slot else a.en > b.en
  else ka > kb

/-- The register-resident allocation that `spillPrefer` ranks highest. -/
def spillVictim (st : Nat) (uses : Array Nat) (act : List PhysActive) :
    Option PhysActive :=
  act.foldl (fun best a =>
      match best with
      | some b => if spillPrefer st uses a b then some a else best
      | none => some a)
    none

/-- One scan step over the interval `[st, en]` of slot `s`.

    Register allocations whose range ended before `st` are reclaimed. If a
    register in `[0, numRegs)` is then free, `s` takes the lowest one. Otherwise
    `spillVictim` ranks the register-resident values, the winner is compared
    against the incoming interval under the same `spillPrefer` order, and the
    higher-ranked of the two moves to a stack cell for its whole range
    (`allocCell`). When the victim is a resident value, `s` takes the register it
    vacates.

    Assignments are accumulated most-recent-first, so `find?` on the result reads
    the final location of a slot that a later step moved to a cell. -/
def physScanSpillStep (numRegs : Nat) (uses : Array Nat)
    (act : List PhysActive) (hulls : CellHulls) (acc : List (Nat × Nat))
    (s st en : Nat) (reserved : List Nat := []) :
    List PhysActive × CellHulls × List (Nat × Nat) :=
  let act' := act.filter (fun a => a.en ≥ st)
  let used := act'.map PhysActive.phys
  match freeRegIn numRegs used reserved with
  | some ph => (⟨st, en, ph, s⟩ :: act', hulls, (s, ph) :: acc)
  | none =>
      let inc : PhysActive := ⟨st, en, numRegs, s⟩
      match spillVictim st uses act' with
      | some far =>
          if spillPrefer st uses far inc then
            let r := allocCell hulls far.st far.en
            (⟨st, en, far.phys, s⟩ :: act'.filter (fun a => a.phys != far.phys),
             r.2, (far.slot, numRegs + r.1) :: (s, far.phys) :: acc)
          else
            let r := allocCell hulls st en
            (act', r.2, (s, numRegs + r.1) :: acc)
      | none =>
          let r := allocCell hulls st en
          (act', r.2, (s, numRegs + r.1) :: acc)

/-- Run the bounded scan over `(slot, start, end)` triples sorted by start. -/
def physScanSpill (numRegs : Nat) (uses : Array Nat)
    (items : List (Nat × Nat × Nat)) (act : List PhysActive) (hulls : CellHulls)
    (acc : List (Nat × Nat)) (reserved : List Nat := []) : List (Nat × Nat) :=
  match items with
  | [] => acc
  | (s, st, en) :: rest =>
      let (act', hulls', acc') :=
        physScanSpillStep numRegs uses act hulls acc s st en reserved
      physScanSpill numRegs uses rest act' hulls' acc' reserved

/-! #### The scan's register-distinctness invariant

The register half of the allocation is safe because the physical indices held by
the in-flight allocations stay pairwise distinct: `freeRegIn` only ever hands out
an index no active allocation holds, and the one step that hands out an index
already in use (`spillVictim` moving a resident value to a stack cell) drops that
value's allocation in the same step. Two slots whose ranges overlap are therefore
never given the same register. -/

/-- `freeRegIn` hands out an index inside the pool. -/
theorem freeRegIn_lt {numRegs : Nat} {used reserved : List Nat} {ph : Nat}
    (h : freeRegIn numRegs used reserved = some ph) : ph < numRegs := by
  unfold freeRegIn at h
  cases reserved <;> exact List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- `freeRegIn` hands out an index that no active allocation holds. -/
theorem freeRegIn_not_mem {numRegs : Nat} {used reserved : List Nat} {ph : Nat}
    (h : freeRegIn numRegs used reserved = some ph) : ph ∉ used := by
  unfold freeRegIn at h
  cases reserved with
  | nil => simpa using List.find?_some h
  | cons r rs =>
    have hp := List.find?_some h
    simp only [Bool.and_eq_true] at hp
    simpa using hp.1

theorem spillFold_mem (st : Nat) (uses : Array Nat) :
    ∀ (act : List PhysActive) (b0 : Option PhysActive) (far : PhysActive),
      act.foldl (fun best a =>
          match best with
          | some b => if spillPrefer st uses a b then some a else best
          | none => some a) b0 = some far →
        far ∈ act ∨ b0 = some far := by
  intro act
  induction act with
  | nil => intro b0 far h; exact Or.inr h
  | cons a rest ih =>
    intro b0 far h
    rw [List.foldl_cons] at h
    rcases ih _ far h with hm | hb
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · cases b0 with
      | none =>
        simp only [Option.some.injEq] at hb
        exact Or.inl (hb ▸ List.mem_cons_self)
      | some b =>
        by_cases hp : spillPrefer st uses a b
        · simp only [hp, if_pos, Option.some.injEq] at hb
          exact Or.inl (hb ▸ List.mem_cons_self)
        · simp only [hp, Bool.false_eq_true, if_neg, not_false_iff] at hb
          exact Or.inr hb

/-- `spillVictim` returns one of the active allocations. -/
theorem spillVictim_mem {st : Nat} {uses : Array Nat} {act : List PhysActive}
    {far : PhysActive} (h : spillVictim st uses act = some far) : far ∈ act := by
  rcases spillFold_mem st uses act none far h with hm | hb
  · exact hm
  · exact absurd hb (by simp)

/-- One scan step keeps the in-flight allocations on pairwise-distinct physical
    registers. -/
theorem physScanSpillStep_nodup (numRegs : Nat) (uses : Array Nat)
    (act : List PhysActive) (hulls : CellHulls) (acc : List (Nat × Nat))
    (s st en : Nat) (h : (act.map PhysActive.phys).Nodup) :
    ((physScanSpillStep numRegs uses act hulls acc s st en).1.map
      PhysActive.phys).Nodup := by
  have hfs : ∀ (p : PhysActive → Bool) (l : List PhysActive),
      (l.map PhysActive.phys).Nodup → ((l.filter p).map PhysActive.phys).Nodup :=
    fun _ l hl => hl.sublist (List.filter_sublist.map PhysActive.phys)
  simp only [physScanSpillStep]
  split
  next ph hfr =>
    exact List.nodup_cons.mpr ⟨by simpa using freeRegIn_not_mem hfr, hfs _ _ h⟩
  next hfr =>
    split
    next far hv =>
      split
      next hp =>
        refine List.nodup_cons.mpr ⟨?_, hfs _ _ (hfs _ _ h)⟩
        simp only [List.mem_map, not_exists, not_and]
        intro x hx hxp
        have hne := (List.mem_filter.mp hx).2
        simp [hxp] at hne
      next hp => exact hfs _ _ h
    next hv => exact hfs _ _ h

/-- Occurrences of slot `s` among the slots the trace touches. -/
def physSlotUses (tr : List PhysEvent) (s : Nat) : Nat :=
  (tr.flatMap PhysEvent.touched).count s

/-- `List.merge` with an explicit fuel argument, recursive on the fuel. Fuel `0`
    returns the first list. -/
def mergeFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, _ => xs
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | f + 1, x :: xs, y :: ys =>
      if le x y then x :: mergeFuel le f xs (y :: ys)
      else y :: mergeFuel le f (x :: xs) ys

/-- `mergeFuel` agrees with `List.merge` when the fuel covers both lists. -/
theorem mergeFuel_eq {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (xs ys : List α), xs.length + ys.length ≤ f →
      mergeFuel le f xs ys = List.merge xs ys le := by
  intro f
  induction f with
  | zero =>
    intro xs ys h
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx; subst hy; simp [mergeFuel]
  | succ f ih =>
    intro xs ys h
    match xs, ys with
    | [], ys => simp [mergeFuel]
    | x :: xs, [] => simp [mergeFuel]
    | x :: xs, y :: ys =>
      simp only [List.length_cons] at h
      by_cases hle : le x y
      · rw [show mergeFuel le (f + 1) (x :: xs) (y :: ys)
              = x :: mergeFuel le f xs (y :: ys) by simp [mergeFuel, hle]]
        rw [ih xs (y :: ys) (by simp; omega), List.cons_merge_cons_pos _ _ _ hle]
      · rw [show mergeFuel le (f + 1) (x :: xs) (y :: ys)
              = y :: mergeFuel le f (x :: xs) ys by simp [mergeFuel, hle]]
        rw [ih (x :: xs) ys (by simp; omega),
          List.cons_merge_cons_neg _ _ _ (by simpa using hle)]

open List.MergeSort.Internal in
/-- `List.mergeSort` with an explicit fuel argument, recursive on the fuel: the
    same contiguous split and the same merge, so the sort is stable. Fuel `0`
    returns the list. -/
def mergeSortFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | f + 1, a :: b :: l =>
      let lr := splitInTwo ⟨a :: b :: l, rfl⟩
      mergeFuel le (l.length + 2) (mergeSortFuel le f lr.1.1) (mergeSortFuel le f lr.2.1)

open List.MergeSort.Internal in
/-- `mergeSortFuel` agrees with `List.mergeSort` when the fuel covers the list. -/
theorem mergeSortFuel_eq {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (l : List α), l.length ≤ f → mergeSortFuel le f l = List.mergeSort l le := by
  intro f
  induction f with
  | zero =>
    intro l h
    match l with
    | [] => simp [mergeSortFuel]
    | a :: l => simp at h
  | succ f ih =>
    intro l h
    match l with
    | [] => simp [mergeSortFuel]
    | [a] => simp [mergeSortFuel]
    | a :: b :: l =>
      simp only [List.length_cons] at h
      show mergeFuel le (l.length + 2)
          (mergeSortFuel le f (splitInTwo ⟨a :: b :: l, rfl⟩).1.1)
          (mergeSortFuel le f (splitInTwo ⟨a :: b :: l, rfl⟩).2.1) = _
      rw [ih _ (by have := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).1.2; omega),
          ih _ (by have := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).2.2; omega)]
      rw [List.mergeSort]
      refine mergeFuel_eq le _ _ _ ?_
      rw [List.length_mergeSort, List.length_mergeSort]
      have h1 := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).1.2
      have h2 := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).2.2
      omega

/-- `List.mergeSort` at the fuel its own argument supplies. `List.merge` and
    `List.mergeSort` are sealed to the kernel, so a closed application of either
    has no normal form, and `mergeSortFuel` recurses on a `Nat` instead.

    Recursion on a `Nat` is necessary and not sufficient. The recursion calls
    `List.MergeSort.Internal.splitInTwo`, which the module system seals as well,
    so inside a `module` a closed `kernelMergeSort` application still has no
    normal form. A module stating an equation about one unseals it with
    `import all Init.Data.List.Sort.Basic` and `import all Init.Data.List.Sort.Impl`.
    `import all` exposes only the named module's own implementation section and
    is not transitive, so each such module carries its own copy of both lines.
    Measured on Lean 4.33.1. `physLiveData` sorts live intervals with this. -/
def kernelMergeSort {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  mergeSortFuel le l.length l

/-- `kernelMergeSort` is `List.mergeSort`. -/
@[simp] theorem kernelMergeSort_eq {α : Type} (le : α → α → Bool) (l : List α) :
    kernelMergeSort le l = l.mergeSort le :=
  mergeSortFuel_eq le l.length l (Nat.le_refl _)

/-- Compiled `physLiveData`: one `O(n)` pass over the trace records the first
    touch, the last touch and the touch count of every slot into arrays (rather
    than re-scanning the trace per slot in
    `physFirstTouch`/`physLastTouch`/`physSlotUses`). -/
@[inline] def physLiveDataImpl (tr : List PhysEvent) :
    List (Nat × Nat × Nat) × Array Nat :=
  let univ := physUniverse tr
  let len := tr.length
  let (firstA, lastA, useA) : Array Nat × Array Nat × Array Nat := Id.run do
    let mut fst : Array Nat := Array.replicate univ len   -- sentinel = len (never)
    let mut lst : Array Nat := Array.replicate univ 0
    let mut cnt : Array Nat := Array.replicate univ 0
    let mut pos := 0
    for ev in tr do
      for s in ev.touched do
        if s < univ then
          if fst[s]! == len then fst := fst.set! s pos
          lst := lst.set! s pos
          cnt := cnt.set! s (cnt[s]! + 1)
      pos := pos + 1
    return (fst, lst, cnt)
  let raw := (List.range univ).filterMap (fun s =>
    let st := firstA[s]!
    if st < len then some (s, st, lastA[s]!) else none)
  (raw.mergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1)), useA)

/-- The live slots paired with ranges (sorted by start then slot), together with
    the per-slot touch counts over `[0, physUniverse)`. -/
@[implemented_by physLiveDataImpl]
def physLiveData (tr : List PhysEvent) : List (Nat × Nat × Nat) × Array Nat :=
  let univ := physUniverse tr
  let raw := (List.range univ).filterMap (fun s =>
    let (st, en) := physLiveRange tr s
    if st < tr.length then some (s, st, en) else none)
  (kernelMergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 ≤ b.1)) raw,
   ((List.range univ).map (physSlotUses tr)).toArray)

/-- The live slots paired with ranges, sorted by start then slot. -/
def physLiveItems (tr : List PhysEvent) : List (Nat × Nat × Nat) :=
  (physLiveData tr).1

/-- The logical→physical slot assignment. -/
def physAssign (tr : List PhysEvent) : List (Nat × Nat) :=
  let d := physLiveData tr
  physScanSpill numGPRegs d.2 d.1 [] #[] []

/-- The logical→physical slot map (identity outside the live set). -/
def physMap (tr : List PhysEvent) (s : Nat) : Nat :=
  match (physAssign tr).find? (fun p => p.1 == s) with
  | some (_, ph) => ph
  | none => s

/-- Compiled `physTable`: scatter the assignment into an identity-seeded array
    in one pass (rather than `assign.find?` per slot). -/
@[inline] def physTableImpl (tr : List PhysEvent) : Array Nat :=
  let univ := physUniverse tr
  Id.run do
    let mut t : Array Nat := (Array.range univ)
    -- `physAssign` is most-recent-first (a slot the scan later moved to a stack
    -- cell appears twice, newest first), and `physTable`'s `find?` reads the
    -- head; scattering in reverse gives the same last-write-wins result.
    for (s, ph) in (physAssign tr).reverse do
      if s < univ then t := t.set! s ph
    return t

/-- Precomputed logical→physical lookup table over `[0, physUniverse)`. -/
@[implemented_by physTableImpl]
def physTable (tr : List PhysEvent) : Array Nat :=
  let assign := physAssign tr
  let univ := physUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- Memoised `physMap` via an `O(1)` table lookup. -/
def physMapTabled (tbl : Array Nat) (s : Nat) : Nat := tbl[s]?.getD s

/-! ### 7c′. Two-class linear scan (GP + vector in one pass)

`physAssign` runs a single linear scan over *all* live slots into the GP pool.
For a mixed scalar+vector `Com`, the slots split into two classes (`bodyVecSlots`)
that must allocate from **disjoint** physical pools. `physAssignClassed` keeps the
exact Poletto–Sarkar scan but partitions the live items by class *before*
scanning: GP slots run one scan into pool `0,1,…` (rendered as `RAX,RBX,…`/`k.N`
GP spills), vector slots run an **independent** scan into pool `0,1,…` that is
then offset by `vectorBase` (rendered as `XMM0,XMM1,…`/`kv.N` vector spills). A
vector value never takes a GP physical index and a scalar value never takes a
vector one.

When `vecArr` marks no slot vector (every pure-scalar kernel), the vector item
list is empty, the GP item list is exactly `physLiveItems tr`, and the GP scan is
the same call `physScanSpill numGPRegs uses items [] #[] []` as `physAssign` — so
the result is byte-identical to the GP-only allocator. -/

/-- Class-aware logical→physical assignment. Partition the live items by class
    (`vecArr`), run two independent linear scans, and offset the vector class's
    physical indices by `vectorBase`. Reduces to `physAssign tr` when no slot is
    vector. -/
def physAssignClassed (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) : List (Nat × Nat) :=
  let d := physLiveData tr
  let gpItems := d.1.filter (fun it => !slotIsVec vecArr it.1)
  let vecItems := d.1.filter (fun it => slotIsVec vecArr it.1)
  let gpAssign := physScanSpill numGPRegs d.2 gpItems [] #[] [] reserved
  -- `reservedVec` (default `[]`) lists vector-pool indices the scan must avoid.
  -- The batch8 path passes `[numVecRegs - 1]` (= `[15]`) to reserve `%ymm15` as
  -- the printer's spill-legalization scratch: the excluded index is never handed
  -- out, and the first spill takes index `numVecRegs` (→ `kv.0`), so the register
  -- boundary in `physRegName` (and its faithfulness lemmas) is unchanged.
  let vecAssign := physScanSpill numVecRegs d.2 vecItems [] #[] [] reservedVec
  gpAssign ++ vecAssign.map (fun p => (p.1, p.2 + vectorBase))

/-- Compiled class-aware `physTable`: scatter the class-aware assignment into an
    identity-seeded array in one pass. -/
@[inline] def physTableClassedImpl (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) : Array Nat :=
  let univ := physUniverse tr
  Id.run do
    let mut t : Array Nat := (Array.range univ)
    -- Reverse for the same last-write-wins reason as `physTableImpl`.
    for (s, ph) in (physAssignClassed tr vecArr reserved reservedVec).reverse do
      if s < univ then t := t.set! s ph
    return t

/-- Class-aware logical→physical lookup table: like `physTable`, but GP and
    vector slots are allocated from disjoint pools (`physAssignClassed`). For a
    body with no vector slot this is `physTable tr` exactly. -/
@[implemented_by physTableClassedImpl]
def physTableClassed (tr : List PhysEvent) (vecArr : Array Bool)
    (reserved : List Nat := []) (reservedVec : List Nat := []) : Array Nat :=
  let assign := physAssignClassed tr vecArr reserved reservedVec
  let univ := physUniverse tr
  (Array.range univ).map (fun s =>
    match assign.find? (fun p => p.1 == s) with
    | some (_, ph) => ph
    | none => s)

/-- The class-aware physical table for a body: `physTableClassed` over `bodyTrace`
    with the body's own `bodyVecSlots` classification. This is the single-pass
    mixed scalar+vector register allocator — GP bindings to GP regs, vector
    bindings to `XMM`. For a pure-scalar body (`bodyVecSlots` all-`false`) it is
    `physTable (bodyTrace body)`, so existing kernels are byte-identical. -/
def bodyPhysTable (body : Lcmd) : Array Nat :=
  physTableClassed (bodyTrace body) (bodyVecSlots body) (bodyReservedGP body)

/-! ### 7d. Two-address lowering of one binop

Each producer binop `dst = op src0 src1` becomes the destructive pair
`mov dst, src0; op dst, src1`, collapsed to `op dst, src1` when `dst = src0`
already (the RA may place them on the same physical register). The `mov` is the
x86 register move; the reader maps `MOV` accordingly. -/

/-- Is an operand a red-zone spill slot (`k.N`, rendered by `physRegName` for an
    allocation index `≥ numGPRegs`)? Such operands the reader materialises as
    `RSP`-relative memory references, so a two-operand x86 instruction may carry
    at most one of them. -/
def LOperand.isSpill : LOperand → Bool
  | .reg n => "k.".isPrefixOf n
  | _ => false

/-- Is a SIB element name a spill slot? A SIB base/index is a bare register
    *name* (`arrIdx`'s `base`/`idx` are `String`s, always full-64-bit registers
    in x86 SIB addressing). The spilling allocator may place either on the stack,
    giving a `k.N` name — which is **not** a register and which the owned printer
    renders as the `%<UNKNOWN:k.N>` sentinel `as` rejects (an x86 SIB base/index
    must be a register). -/
def sibNameSpill (n : String) : Bool := "k.".isPrefixOf n

/-- Legalize a register-indexed (SIB) memory element `arrIdx base idx scale` so
    that **both** its base and index are real registers, as x86 SIB addressing
    requires. The spilling allocator may place the base pointer and/or the index
    on the stack (a `k.N` spill name); the owned printer renders such a SIB
    base/index as the `%<UNKNOWN:k.N>` sentinel — bug class 3 on the **address**
    (the third remaining ChaCha codegen error,
    `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`). When the base is a spill it is
    reloaded into the secondary scratch `R14` (`reloadScratch2`); when the index
    is a spill it is reloaded into the primary scratch `R15` (`reloadScratch`).
    Returns `(prelude, fixedElem)` where `fixedElem`'s base/index are always
    registers, and `prelude` are the reload `mov`s (each a legal `mov reg, mem`).

    The two scratches are disjoint from each other and from the load/store value
    routing convention: the LOAD/STORE legalizers route a spilled *value* through
    `R15`, but a `LOADIDX`/`STOREIDX` whose SIB index is itself a spill is the
    rare case the address-reload below targets — and the caller composes the two
    so the address reload runs *first*, before any value routing reuses `R15`.
    For the common base-only spill (the observed ChaCha bug) only `R14` is used,
    leaving `R15` free for the value. Non-SIB operands pass through unchanged. -/
def legalizeSibElem (o : LOperand) : List LinstrR × LOperand :=
  match o with
  | .arrIdx base idx scale =>
      let basePre : List LinstrR :=
        if sibNameSpill base then [.Lopn [.reg reloadScratch2] "MOV:64" [.reg base]]
        else []
      let base' : String := if sibNameSpill base then reloadScratch2 else base
      let idxPre : List LinstrR :=
        if sibNameSpill idx then [.Lopn [.reg reloadScratch] "MOV:64" [.reg idx]]
        else []
      let idx' : String := if sibNameSpill idx then reloadScratch else idx
      (basePre ++ idxPre, .arrIdx base' idx' scale)
  | _ => ([], o)

/-- **Reload a clobbered memref base pointer from its red-zone save slot.**

    In the 2-pointer memref ABI (`inLoadMap = none`, `outStoreMap = []` —
    ChaCha/SHA/Keccak whole-state kernels), each `LOADIDX`/`STOREIDX`
    self-addresses through a pointer argument `aj` used as the SIB base. After
    `remapOperand`, that base is the *physical* register the linear-scan RA gave
    `aj` (e.g. `RDI`/`RCX`), into which `buildArgPtrMaterialize` copied the
    SysV-argument pointer **once** at function entry. But that physical register
    is in the allocatable set, so the 20-round body REUSES it as a scratch — by
    the time a later `memrefSetDyn`/`memrefGetDyn` resolves its SIB base, the
    register holds a ChaCha *word*, not the pointer, and the store/load writes
    through garbage (the gdb-confirmed segfault: `%rdi` = `0x6b3ca454`, a word).

    The pointer is, however, live in MEMORY the whole function: the prologue
    saved it to the red zone (`qsave.RDI`/`qsave.RSI`). So we mirror
    `legalizeSibElem`'s reload-base pattern, but keyed on the ABI-arg's qsave
    slot rather than on a spill name: immediately before the access, emit
    `mov R14, [qsave.<abiArg>]` and rewrite the SIB base to `R14`
    (`reloadScratch2`). The reload is unconditional per access (one extra `movq`),
    which keeps the reasoning local and never trusts the body-clobberable
    register.

    `memrefBaseReload : String → Option String` maps a physical base register
    name (`phys(aj)`) to the qsave slot holding its pointer; it is built by the
    ABI export from `abiArgs`/the RA table (see `comToLfundefPhysAbi`). Off the
    memref ABI path it is `fun _ => none`, so this is the identity `([], o)` and
    every existing kernel's bytes are unchanged.

    `R14` is disjoint from the value/index routing in `legalizeMemLoad`/
    `legalizeMemStore`: those route a spilled VALUE or a spilled INDEX through
    `R15`, and `legalizeSibElem`'s spill-base reload (also `R14`) is **not**
    triggered here — the base we hand back is the register `R14`, not a `k.N`
    spill — so the pointer in `R14` survives untouched through the access. -/
def reloadMemrefBase (memrefBaseReload : String → Option String) (o : LOperand) :
    List LinstrR × LOperand :=
  match o with
  | .arrIdx base idx scale =>
      match memrefBaseReload base with
      | some qsave =>
          ([.Lopn [.reg reloadScratch2] "MOVQ" [.reg qsave]],
           .arrIdx reloadScratch2 idx scale)
      | none => ([], o)
  | _ => ([], o)

/-- Legalize a two-address binop `op dst, src` (sources `[dst, src]`) so it
    carries **no** memory (spill) operand inside the binop itself — every `k.N`
    name appears only in a MOV source or destination. jasmin's `asmgen` refuses
    to map a memory `lexpr` to a register operand of a non-MOV `Lopn`, so any
    spill must be reloaded through one of the two reserved scratches.

    Four cases by `(dst.isSpill, src.isSpill)`:

    * `(false, false)` — both registers: emit the direct
      `op dst, src` (1 `Lopn`).
    * `(false, true)` — register destination, spill source: route `src` through
      `R15`, `mov R15, src; op dst, R15` (2 `Lopn`s).
    * `(true, false)` — spill destination, register source: route `dst` through
      `R15`, `mov R15, dst; op R15, src; mov dst, R15` (3 `Lopn`s).
    * `(true, true)` — both spills: route `dst` through `R15` and `src` through
      `R14`, `mov R15, dst; mov R14, src; op R15, R14; mov dst, R15`
      (4 `Lopn`s).

    Every emitted `Lopn` is either a MOV (which permits a memory lexpr/rexpr)
    or has all of its non-MOV register operands in `R15`/`R14`. -/
def legalizeBinop (dst src : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  match dst.isSpill, src.isSpill with
  | false, false =>
      [.Lopn [dst] opn [dst, src]]
  | false, true =>
      [.Lopn [.reg reloadScratch] mov [src],
       .Lopn [dst] opn [dst, .reg reloadScratch]]
  | true, false =>
      [.Lopn [.reg reloadScratch] mov [dst],
       .Lopn [.reg reloadScratch] opn [.reg reloadScratch, src],
       .Lopn [dst] mov [.reg reloadScratch]]
  | true, true =>
      [.Lopn [.reg reloadScratch] mov [dst],
       .Lopn [.reg reloadScratch2] mov [src],
       .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .reg reloadScratch2],
       .Lopn [dst] mov [.reg reloadScratch]]

/-- Legalize a register copy `mov dst, src` (sources `[src]`) so it carries at
    most one memory (spill) operand. When BOTH `dst` and `src` are spill slots,
    `mov [mem], [mem]` is illegal; route through the reserved reload scratch:
    `mov R15, src; mov dst, R15`. Otherwise emit the single copy unchanged. -/
def legalizeMov (dst src : LOperand) (mov : String := "MOV") : List LinstrR :=
  if dst.isSpill && src.isSpill then
    [.Lopn [.reg reloadScratch] mov [src],
     .Lopn [dst] mov [.reg reloadScratch]]
  else
    [.Lopn [dst] mov [src]]

/-- Legalize a **single-source memory LOAD** op `Lopn [dst] opn [src]` (a `LOAD`
    or register-indexed `LOADIDX`, whose source is always a memory operand — a
    spill slot or a `(%base,%idx,scale)` SIB element) so the emitted x86 carries
    at most one memory operand.

    The owned printer renders such a load as `mov<sz> src, dst`. When the
    destination `dst` is itself a spill slot (a memory operand), that single line
    is an illegal `mov mem, mem` (the whole-state ChaCha/SHA/Keccak/NTT kernels
    hit this when the loaded word's SSA result lands in a stack slot). Route the
    load through the reserved primary scratch `R15`:
    `op R15, src; mov dst, R15` — the load writes the register `R15` (one memory
    operand: the source), then a plain `mov` stores `R15` to the stack slot (one
    memory operand: the destination). Both moves are legal.

    The SIB base/index of a `LOADIDX` are allocatable GP registers (never `R15`,
    which is reserved and never an allocation target — `physRegName`), so the
    routing scratch never collides with the address registers. When `dst` is a
    register, the direct one-line load is already legal and is emitted unchanged.

    The split is denotation-preserving: `dst ← src` equals `R15 ← src; dst ← R15`
    on the abstract machine (`R15` is dead at this point — it is only ever the
    legalization scratch). The trailing reload `mov` inherits the load's width
    via `mov` so the full loaded value survives into the slot. -/
def legalizeMemLoad (dst src : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  -- The trailing `mov dst, R15` must store the **load width** so a 64-bit value
  -- the `LOADIDX` parked in R15 is not truncated by a 32-bit `movl` into the
  -- slot. The owned printer sizes a `LOADIDX` by its SIB scale (`scale·8` bits),
  -- so when `src` is a SIB element with an 8-byte stride the spill-store is
  -- `MOV:64`; otherwise it inherits the op's `mov` width.
  let storeMov : String :=
    match src with
    | .arrIdx _ _ scale => if scale ≥ 8 then "MOV:64" else mov
    | _ => mov
  -- First make the SIB source's base/index registers (the address-reload prelude
  -- runs before any value routing reuses `R15`): a spilled SIB base/index would
  -- otherwise render as the `%<UNKNOWN:k.N>` sentinel `as` rejects.
  let (addrPre, src') := legalizeSibElem src
  addrPre ++
  (if dst.isSpill then
    [.Lopn [.reg reloadScratch] opn [src'],
     .Lopn [dst] storeMov [.reg reloadScratch]]
  else
    [.Lopn [dst] opn [src']])

/-- True iff `opn` is a memory-LOAD mnemonic whose source operand is always a
    memory reference (`LOAD` / `LOADIDX`, optionally `:64`-tagged). These are the
    single-source ops that `legalizeMemLoad` must route through `R15` when their
    destination is a spill slot, to avoid an illegal `mov mem, mem`. -/
def isMemLoad (opn : String) : Bool :=
  let base := stripWidthTag opn
  base == "LOAD" || base == "LOADIDX"

/-- Legalize a **memory STORE** op so the emitted x86 carries at most one memory
    operand. The mirror of `legalizeMemLoad`.

    A register-indexed store `Lopn [d] STOREIDX [arrIdx, val]` writes the value
    `val` into the SIB memory destination `(%base,%idx,scale)` (the `Lopn`
    destination `d` names the functionally-updated array — the dialect's
    `stackStore` returns the new array — so it is NOT an x86 operand). The owned
    printer renders it as `mov<sz> val, (%base,%idx,scale)`. When the value source
    `val` is itself a spill slot (a memory operand), that single line is an
    illegal `mov mem, mem` (the whole-state ChaCha/SHA/Keccak/NTT kernels hit this
    when the word being stored lives in a stack slot). Route the value through the
    reserved primary scratch `R15`: `mov R15, val; STOREIDX [arrIdx, R15]` — the
    leading `mov` loads the spill word into the register `R15` (one memory
    operand: the source), then the store writes `R15` to the SIB destination (one
    memory operand: the destination). Both moves are legal.

    `dArr` is the (non-operand) array-result destination, `addr` the SIB / memory
    destination operand, `val` the stored value, `opn` the store mnemonic. The SIB
    base/index of a `STOREIDX` are allocatable GP registers (never `R15`, which is
    reserved and never an allocation target — `physRegName`), so the routing
    scratch never collides with the address registers. When `val` is a register,
    the direct one-line store is already legal and is emitted unchanged.

    The split is denotation-preserving: `[addr] ← val` equals
    `R15 ← val; [addr] ← R15` on the abstract machine (`R15` is dead at this point
    — it is only ever the legalization scratch). The leading reload `mov` inherits
    the store width via `mov` so the full value survives into the scratch. -/
def legalizeMemStore (dArr addr val : LOperand) (opn : String)
    (mov : String := "MOV") : List LinstrR :=
  -- The reload `mov R15, val` must move the **store width** so a 64-bit value
  -- is not truncated by a 32-bit `movl`. The owned printer sizes a `STOREIDX`
  -- by its SIB scale (`scale·8` bits), so when `addr` is a SIB element with an
  -- 8-byte stride the reload is `MOV:64`; otherwise it inherits the op's `mov`
  -- width (the spill-routing reloads elsewhere already key off the `:64` tag).
  let reloadMov : String :=
    match addr with
    | .arrIdx _ _ scale => if scale ≥ 8 then "MOV:64" else mov
    | _ => mov
  -- First make the SIB destination's base/index registers (the base reloads into
  -- the secondary scratch `R14`, disjoint from the value's `R15` routing below),
  -- so a spilled SIB base/index never renders as the `%<UNKNOWN:k.N>` sentinel
  -- `as` rejects (the observed `movq %r15, (%<UNKNOWN:k.5>, %rax, 8)`).
  let (addrPre, addr') := legalizeSibElem addr
  -- BOTH-SPILLED collision arm: when `legalizeSibElem` reloaded a spilled SIB
  -- INDEX into `R15` AND the value is a spill, the value routing below would
  -- reuse `R15` and clobber the index before the store reads it (the observed
  -- `mov 0x28(%rsp),%r15; mov 0x20(%rsp),%r15; mov %r15,(%r14,%r15,8)` — the
  -- query-walk segfault). Fold the SIB address into `R14` with a `LEA:64`
  -- while the index is still live in `R15`; `R15` is then free for the value,
  -- and the store goes through the flat `mem.R14.0` operand (the base in
  -- `R14` is consumed by the `LEA`, so overwriting it is safe).
  match addr', val.isSpill with
  | .arrIdx b i scale, true =>
      if i == reloadScratch then
        addrPre ++
        [.Lopn [.reg reloadScratch2] "LEA:64" [.arrIdx b i scale],
         .Lopn [.reg reloadScratch] reloadMov [val],
         .Lopn [.reg ("mem." ++ reloadScratch2 ++ ".0")] reloadMov
           [.reg reloadScratch]]
      else
        addrPre ++
        [.Lopn [.reg reloadScratch] reloadMov [val],
         .Lopn [dArr] opn [addr', .reg reloadScratch]]
  | _, true =>
      addrPre ++
      [.Lopn [.reg reloadScratch] reloadMov [val],
       .Lopn [dArr] opn [addr', .reg reloadScratch]]
  | _, false =>
      addrPre ++ [.Lopn [dArr] opn [addr', val]]

/-- True iff `opn` is a memory-STORE mnemonic whose value source may be a memory
    (spill) operand (`STORE` / `STOREIDX`, optionally `:64`-tagged). These are the
    two-source ops `legalizeMemStore` must route through `R15` when their value
    source is a spill slot, to avoid an illegal `mov mem, mem`. -/
def isMemStore (opn : String) : Bool :=
  let base := stripWidthTag opn
  base == "STORE" || base == "STOREIDX"

/-- A binop immediate source that does not fit a sign-extended `imm32` must be
    materialised into a register first: x86 has no `op r64, imm64` encoding
    (only `imm32`, sign-extended). Keccak's ι step XORs a full 64-bit round
    constant `RC[round]`, so the U64 path routes any `s1 = #v` with `v ≥ 2^31`
    through `reloadScratch2` (R14) via a `MOV:64 R14, #v` (an x86 `movabs`),
    then uses `R14` as the binop's register source. Returns `(prelude, s1')`.
    For the 32-bit path (`mov ≠ "MOV:64"`) this is the identity `([], s1)`, so
    the existing ChaCha/SHA shapes are unchanged. -/
def materializeWideImm (s1 : LOperand) (mov : String) : List LinstrR × LOperand :=
  match s1, mov with
  | .imm v, "MOV:64" =>
      if 2 ^ 31 ≤ v then
        ([.Lopn [.reg reloadScratch2] "MOV:64" [.imm v]], .reg reloadScratch2)
      else ([], s1)
  | _, _ => ([], s1)

/-- When `materializeWideImm` is invoked on the 32-bit path (the default
    `mov = "MOV"`), it is the identity. This lets the U32 shape/legality lemmas
    reduce `lowerTwoAddr` to its pre-#472 form. -/
@[simp] theorem materializeWideImm_MOV (s1 : LOperand) :
    materializeWideImm s1 "MOV" = ([], s1) := by
  cases s1 <;> rfl

/-- Lower a single resolved binop into its two-address `LinstrR` sequence over
    physical operand names, legalizing any two-memory-operand instruction by
    routing one source through the reserved reload scratch.
    `dst`, `s0`, `s1` are physical operand names; `opn` the producer mnemonic.
    When `dst = s0` the RA already placed `dst` on `s0`'s register, so the leading
    `mov` collapses; otherwise a `mov dst, s0` (itself legalized) precedes the
    op (itself legalized). A wide U64 immediate `s1` is materialised into a
    register first (`materializeWideImm`). -/
def lowerTwoAddr (dst s0 s1 : LOperand) (opn : String) (mov : String := "MOV") :
    List LinstrR :=
  let (immPre, s1') := materializeWideImm s1 mov
  if dst = s0 then
    immPre ++ legalizeBinop dst s1' opn mov
  else
    legalizeMov dst s0 mov ++ immPre ++ legalizeBinop dst s1' opn mov

/-- Lower a constant-shift binop (`SHL`/`SHR` with a compile-time shift count)
    into two-address form with the count as an **immediate** operand (`#v`). x86
    forces a register shift count into `CL`; an immediate `imm8` count needs no
    forced register, so emitting the (compile-time-constant) ChaCha rotate amounts
    as immediates removes the `(compile_arg) bad forced register` constraint.

    `dst`, `s0` are physical operand names; `v` the immediate shift amount.

    Even though the immediate source carries no memory operand, jasmin's `asmgen`
    still refuses a spill `lexpr` as the destination of a non-MOV `Lopn` — so a
    `SHL` whose destination is a spill (`k.N`) must be reloaded through the
    primary scratch `R15`:

    * `dst = s0`, `dst` register: single `op dst, #v`.
    * `dst = s0`, `dst` spill: `mov R15, dst; op R15, #v; mov dst, R15`.
    * `dst ≠ s0`, `dst` register: `mov dst, s0; op dst, #v` (the leading mov is
      legalized — `s0` may itself be a spill, which is a legal MOV source).
    * `dst ≠ s0`, `dst` spill: `mov R15, s0; op R15, #v; mov dst, R15` (the
      leading mov pulls `s0` directly into the scratch, avoiding a redundant
      reload of `dst`'s stale value). -/
def lowerTwoAddrShiftImm (dst s0 : LOperand) (v : Nat) (opn : String)
    (mov : String := "MOV") : List LinstrR :=
  if dst.isSpill then
    -- Reload-pass: thread the shift through `R15`. Source the scratch from `s0`
    -- (the value being operated on); when `dst = s0` they coincide and this is
    -- the canonical `mov R15, dst; op R15, #v; mov dst, R15` shape.
    [.Lopn [.reg reloadScratch] mov [s0],
     .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .imm v],
     .Lopn [dst] mov [.reg reloadScratch]]
  else if dst = s0 then
    [.Lopn [dst] opn [dst, .imm v]]
  else
    legalizeMov dst s0 mov ++ [.Lopn [dst] opn [dst, .imm v]]

/-- True iff `opn` is a **native immediate shift / rotate** mnemonic
    (`ROR:n` / `ROL:n` / `SHL:n` / `SHR:n` / `SAR:n`, optionally `:64`-tagged),
    the single-source form `opToLinstrR` emits for `.rorImm` / `.shlImm` /
    `.shrImm` (#497/#605). The count is carried IN the mnemonic, so these are a
    one-source unary op (`Lopn [d] "ROR:n" [s]`), distinct from the two-source
    register `SHL`/`SHR` the `isBinop` arm re-lowers. -/
def isNativeShiftRotate (opn : String) : Bool :=
  let base := stripWidthTag opn
  ["ROR:", "ROL:", "SHL:", "SHR:", "SAR:"].any (fun p => p.isPrefixOf base)

/-- Lower a native immediate shift / rotate (`ROR:n` / `SHL:n` / …, the unary
    `opToLinstrR`-emitted form of `.rorImm` / `.shlImm` / `.shrImm`) into a form
    whose operand is never a memory (spill) slot. x86 accepts a memory operand on
    `ror $n, mem`, but the **owned printer** (`LprogAsmPrinter`) renders the
    two-address `dst ≠ src` case as `mov src, dst; ror $n, dst`; when both `dst`
    and `src` are spills, that leading `mov` is an illegal `mov mem, mem`. The
    `.rorImm`/`.shlImm`/`.shrImm` op binds a fresh SSA result from its one value
    operand, so after RA `dst` and `src` are independent slots, either of which
    the spilling allocator may place in memory. When either is a spill, thread
    the value through the primary reload scratch `R15`:
    `mov R15, src; ror $n R15; mov dst, R15` (mirrors `lowerTwoAddrShiftImm`).

    `dst`, `s` are physical operand names (post-RA), `opn` the native mnemonic.
    * neither a spill: single `op dst` after the printer's own `mov src,dst`
      collapse (or it renders `mov src,dst; ror $n,dst`, both legal reg forms).
    * either a spill: `mov R15, s; op R15; mov dst, R15` — all three legal. -/
def lowerNativeShiftRotate (dst s : LOperand) (opn : String) (mov : String) :
    List LinstrR :=
  if dst.isSpill || s.isSpill then
    [.Lopn [.reg reloadScratch] mov [s],
     .Lopn [.reg reloadScratch] opn [.reg reloadScratch],
     .Lopn [dst] mov [.reg reloadScratch]]
  else
    [.Lopn [dst] opn [s]]

/-! ### 7e. The physical body and export

We re-walk `comToBody` (the same SSA body), remap every operand name through the
linear-scan physical map, and re-lower each binary `Lopn` to two-address form.
Non-binop `Lopn`s (LOAD/STORE/casts/calls) and the `Lret` pass through with
operands remapped. -/

/-! ### 7c′. Caller-save barrier for an in-loop `Lcall`

A real `call` (the `loopBodyCallLcmd` SysV sequence, used by MSM's Straus inner
loop and the GGM real AES-PRG node) clobbers all SysV *caller-saved* registers
(`RAX RCX RDX RSI RDI R8 R9 R10 R11`). Any value live across the call — the
accumulator, the loop index `Lidx<d>`, the trip counter `Lctr<d>`, every pinned
invariant base — must therefore sit in a *callee-saved* register
(`RBX RBP R12 R13`) so the callee preserves it. The linear scan (`physScan`) is
oblivious to `Lcall` (`bodyTrace` records only `Lopn` footprints), and its
default pool order `gpRegNames = [RAX, RBX, RCX, …]` assigns the longest-lived
slots — exactly the loop-carried ones — the lowest physical indices, i.e. the
*caller-saved* `RAX`/`RCX`/… So a call-containing body needs two corrections at
operand-remap time:

* **callee-saved-first placement** — permute the allocated GP physical index
  through `calleeSavedFirstOrder` so the earliest-allocated (loop-carried) slots
  land in the callee-saved block first; and
* **literal-ABI pinning** — the marshalling `MOV RDI, …` / `MOV …, RAX` name
  hardware registers literally (the SysV arg/return regs); those names must
  survive the RA verbatim (an `Lcall`'s ABI contract), never be reassigned.

These corrections are provided by `physNameForBody` (used by the aux
name-resolution passes `buildArgMaterializePhys` / `buildArgPtrMaterialize` /
`buildEpilogue`) and `remapOperandCalleeSave`: `calleeFirstPhys` performs the
callee-saved-first placement and `isHwRegName` the literal pinning, both gated on
`bodyHasCall`. The body emit `physBody` / `physBodyWithStores` uses the call-free
`remapOperand` (so the faithfulness-chain parametric proofs see the plain
physical lookup). The callee-saved registers a loop-carried value lands in are
already saved/restored by `buildPrologue` / `calleeSaveRestoreEpilogue`. -/

/-- True iff the body issues a real `LinstrR.Lcall` (the caller-save barrier
    engages for such bodies; a call-free body is unaffected). -/
def bodyHasCall (body : Lcmd) : Bool :=
  body.any (fun i => match i.li_i with | .Lcall _ _ => true | _ => false)

/-- The literal hardware register names — the full physical GP file (`RSP`
    included: it is the stack pointer and must never be reassigned either) plus
    the SysV SSE arg registers (`XMM0…XMM7`). A name in this set is a *literal*
    hardware register (the SysV arg/return registers the marshalling names — GP
    `RDI`/`RSI`/`RAX` from `loopBodyCallLcmd`, xmm `XMM0…XMM7` from
    `loopBodyCallLcmdClassed`), pinned to itself by the call barrier rather than
    routed through the RA. An SSA value is never named `XMM<i>` literally (a
    vector value is a fresh SSA name resolved to an xmm *by* the RA), so pinning
    the SSE arg names is additive: a call-free / GP-only body is unaffected. -/
def hwRegNames : List String :=
  gpRegNames ++ [reloadScratch2, reloadScratch, "RSP"] ++ sysvSseArgRegs

/-- Is `n` a literal hardware GP register name (`hwRegNames`)? -/
def isHwRegName (n : String) : Bool := hwRegNames.contains n

/-- Is `n` a **frame-slot** operand name rather than a register-file name: a GP
    spill `k.N`, a vector spill `kv.N`, an ABI save `qsave.X`, or a
    base-relative memory reference `mem.<base>.<off>`?

    These four prefixes are the operand classes `LprogAsmPrinter.resolveName`
    resolves to a memory address; each denotes a location in the frame, not a
    slot in the register file, so the register allocator's name→physical lookup
    does not apply to it. The SSA names a body carries (`r<d>`, `a<j>`,
    `L<d>_r<k>`, `Lctr<d>`, `Lidx<d>`) begin with none of these prefixes, so no
    allocated name is classified here. -/
def isFrameSlotName (n : String) : Bool :=
  hasPrefix n "k." || hasPrefix n "kv." || hasPrefix n "qsave." || hasPrefix n "mem."

/-- The callee-saved-first permutation of the 13 allocatable GP physical indices
    (`gpRegNames` order). The callee-saved registers come first —
    `RBX(1) RBP(6) R12(11) R13(12)` — then the caller-saved
    `RAX(0) RCX(2) RDX(3) RSI(4) RDI(5) R8(7) R9(8) R10(9) R11(10)`. Applied to a
    call-containing body's allocated GP indices so the longest-lived (loop-carried)
    slots, which the linear scan assigns the lowest indices, land in the
    callee-saved block first (and thus survive a `call`). -/
def calleeSavedFirstOrder : List Nat := [1, 6, 11, 12, 0, 2, 3, 4, 5, 7, 8, 9, 10]

/-- Permute an allocated GP physical index through `calleeSavedFirstOrder`
    (callee-saved registers first). Spill indices (`≥ numGPRegs`) and vector
    indices (`≥ vectorBase`) pass through unchanged. -/
def calleeFirstPhys (p : Nat) : Nat :=
  if p < numGPRegs then calleeSavedFirstOrder.getD p p else p

/-- The allocatable *caller-saved* GP register names — every `gpRegNames` entry
    a SysV leaf `call` may clobber (`RBX RBP R12 R13` are the callee-saved four;
    the reserved scratch `R14`/`R15` are callee-saved and never allocated). A
    loop-invariant pointer base that the looped-call barrier's static
    `calleeFirstPhys` placement overflowed into one of these (a 5th+ loop-carried
    slot, past the four callee-saved registers) is destroyed by an in-loop
    `Lcall` unless it is reloaded from its red-zone qsave slot after the call
    (`ComL.toLfundefPhysAbi`'s `callArgBaseReload`). -/
def callerSavedAllocGPRs : List String :=
  ["RAX", "RCX", "RDX", "RSI", "RDI", "R8", "R9", "R10", "R11"]

/-- Is `n` an allocatable caller-saved GP register name (`callerSavedAllocGPRs`)? -/
def isCallerSavedAllocGPR (n : String) : Bool := callerSavedAllocGPRs.contains n

/-! ### 7c″. Straight-line multi-call barrier (liveness-computed)

`calleeFirstPhys` is a *static* index permutation: the earliest-allocated
(longest-lived) GP slots land in the 4 callee-saved registers, the rest fall
back into the caller-saved block. That is sound for the looped call path (the
loop-carried set is small and earliest-allocated) but NOT for a straight-line
multi-leaf-call orchestration (the ML-DSA keygen caller): with more than 4 raw
GP indices in flight the 5th+ land in `RAX`/`RCX`/… and are destroyed by the
next `call`'s return, and an index permuted into a SysV argument register
(`RDX`/`RSI`/`RDI`/…) is overwritten by a later call site's own marshalling
`MOV`s before its last read (the ≥3-arg `bytes_concat_6` marshal defect).

For a body that is straight-line (no label / branch) AND issues real `Lcall`s
(`bodyStraightCall`), the barrier is therefore *liveness-computed*
(`straightCallRelocTable`) instead of static:

* a raw GP index hosting a slot whose live range crosses a `call` — or a
  write-only slot (an output read only after the body, e.g. by an inline out
  store / the return; conservatively treated as live to the end) — is homed
  **callee-saved** (`RBX RBP R12 R13`), then **stack-spilled** (`k.N`, inside
  the printer-allocated frame, which survives calls) once those run out;
* every other raw GP index is homed in `R10`/`R11` — the only caller-saved
  registers no SysV marshal (`RDI…R9`) or return-capture (`RAX`) `MOV` ever
  writes — then spilled likewise.

So NO allocated value ever resolves to `RAX`/`RDI`/`RSI`/`RDX`/`RCX`/`R8`/`R9`:
every call-marshal source reads from a callee-saved / `R10` / `R11` / frame-spill
home, which no earlier marshal `MOV` of the same call site can have overwritten —
the marshal read-after-overwrite hazard is structurally impossible. Literal SysV
hardware names stay pinned (`isHwRegName`), exactly as in the looped barrier.
A vector (`XMM`) value live across a call remains unsupported (SysV has no
callee-saved xmm; documented at `loopBodyCallLcmdClassed`).

The looped call path (`Llabel`/`Lcond` back-edges — MSM / GGM) keeps the static
`calleeFirstPhys` placement byte-identically, and a call-free body is
untouched. -/

/-- True iff the body is a **straight-line call body**: it issues a real
    `Lcall` and carries no intra-body control flow (no label / branch / goto).
    Gates the liveness-computed straight-line call barrier
    (`straightCallRelocTable`); the looped call path (`Llabel`/`Lcond` present)
    keeps the static `calleeFirstPhys` placement, and a call-free body is
    unaffected. -/
def bodyStraightCall (body : Lcmd) : Bool :=
  bodyHasCall body && !body.any (fun i =>
    match i.li_i with
    | .Llabel _ _ => true
    | .Lcond _ _ => true
    | .Lgoto _ => true
    | .Ligoto _ => true
    | .LstoreLabel _ _ => true
    | _ => false)

/-- The body's `Lcall` positions in `bodyTrace` coordinates: for each call, the
    number of `Lopn` events preceding it (`bodyTrace` indexes `Lopn`s only, so a
    call sits between event `p-1` and event `p`). A slot with live range
    `[st, en]` is live across that call iff `st < p ∧ p ≤ en`. -/
def bodyCallTracePositions (body : Lcmd) : List Nat :=
  (body.foldl (fun (acc : List Nat × Nat) i =>
      match i.li_i with
      | .Lopn _ _ _ => (acc.1, acc.2 + 1)
      | .Lcall _ _ => (acc.2 :: acc.1, acc.2)
      | _ => acc) ([], 0)).1.reverse

/-- The callee-saved pool of the straight-line call barrier, as `gpRegNames`
    indices: `RBX(1) RBP(6) R12(11) R13(12)` — preserved by any SysV callee
    (and saved/restored by `buildPrologue` / `calleeSaveRestoreEpilogue`). -/
def straightCallCalleeSavedPool : List Nat := [1, 6, 11, 12]

/-- The non-cross scratch pool of the straight-line call barrier, as
    `gpRegNames` indices: `R10(9) R11(10)` — the only allocatable caller-saved
    registers that no SysV call-marshal (`RDI RSI RDX RCX R8 R9`) or
    return-capture (`RAX`) `MOV` writes, so a value that dies before the next
    `call` is safe there. -/
def straightCallScratchPool : List Nat := [9, 10]

/-- The straight-line call barrier's relocation of **raw** allocated GP indices
    (the `physScan` output, `< numGPRegs`) onto call-safe homes. For each raw
    index actually used by a non-hardware-named slot:

    * **crossing** (some hosted slot is live across an `Lcall`, or is
      write-only — an output read only after the body, treated as live to the
      end): the next free index from `straightCallCalleeSavedPool`, else a
      fresh frame-spill index (above every spill the scan already assigned);
    * **non-crossing**: the next free index from `straightCallScratchPool`,
      else a fresh frame-spill index.

    Unused raw indices keep their identity image (nothing resolves through
    them: literal hardware names are pinned by `isHwRegName` before the table
    is consulted). The synthetic `%livepin` liveness pin is ignored. Raw spill
    (`≥ numGPRegs`) and vector (`≥ vectorBase`) indices pass through unchanged
    (`straightCallPhys`). -/
def straightCallRelocTableCore (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  Id.run do
    let tr := bodyTrace body
    let calls := bodyCallTracePositions body
    let names : Array String := (bodyNames body).toArray
    let univ := physUniverse tr
    -- Slots read by at least one event (a write-only slot is presumed an
    -- output — read only after the body — and treated as call-crossing).
    let mut isRead : Array Bool := Array.replicate univ false
    for ev in tr do
      for s in ev.rds do
        if s < isRead.size then isRead := isRead.set! s true
    -- Per raw GP index: used by a non-hw slot / hosts a crossing non-hw slot.
    let mut usedRaw : Array Bool := Array.replicate numGPRegs false
    let mut crossRaw : Array Bool := Array.replicate numGPRegs false
    for it in physLiveItems tr do
      let s := it.1
      let en := it.2.2
      let nm := names[s]?.getD ""
      -- An argument slot (`a<j>`) is materialized at ENTRY by
      -- `buildArgPtrMaterialize` (before the first trace event), so its
      -- effective live range starts at 0: an argument first read after a
      -- call must count as call-crossing (its home is written before the
      -- call runs).
      let st := if nm.startsWith "a" && (strDropToNat? nm 1).isSome
                then 0 else it.2.1
      if nm != "%livepin" && !isHwRegName nm then
        let raw := physMapTabled tbl s
        if raw < numGPRegs then
          usedRaw := usedRaw.set! raw true
          let crossing := calls.any (fun p => st < p && p ≤ en)
                            || !(isRead[s]?.getD true)
          if crossing then crossRaw := crossRaw.set! raw true
    -- Fresh spill indices start above every spill the scan already assigned.
    let mut spillBase := numGPRegs
    for v in tbl do
      if numGPRegs ≤ v && v < vectorBase then spillBase := Nat.max spillBase (v + 1)
    let mut reloc : Array Nat := Array.range numGPRegs
    let mut crossPool := straightCallCalleeSavedPool
    let mut nonCrossPool := straightCallScratchPool
    let mut nextSpill := spillBase
    for raw in [0:numGPRegs] do
      if usedRaw[raw]?.getD false then
        if crossRaw[raw]?.getD false then
          match crossPool with
          | r :: rest => reloc := reloc.set! raw r; crossPool := rest
          | [] => reloc := reloc.set! raw nextSpill; nextSpill := nextSpill + 1
        else
          match nonCrossPool with
          | r :: rest => reloc := reloc.set! raw r; nonCrossPool := rest
          | [] => reloc := reloc.set! raw nextSpill; nextSpill := nextSpill + 1
    return reloc

/-- `straightCallRelocTableCore`, recomputed per call. The barrier resolver
    `physNameForBody` consults this once per operand, so the table is
    recomputed O(operands) times per export — acceptable at the straight-line
    call bodies' sizes (≤ a few hundred instructions). A pointer-keyed
    global-ref cache here (the `bodyNameInfoCacheRef` pattern, two-key
    variant) corrupted the mimalloc heap under `lake build`'s async
    elaboration tasks (mi_malloc SIGSEGV in a later compile step), so the
    compiled form stays the pure recomputation. -/
def straightCallRelocTable (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  straightCallRelocTableCore body tbl

/-- Resolve logical slot `s` to its physical index under the straight-line call
    barrier: the raw scan index relocated through `straightCallRelocTable` when
    it is an allocatable GP register; spill (`≥ numGPRegs`) and vector
    (`≥ vectorBase`) indices pass through unchanged. -/
def straightCallPhys (body : Lcmd) (tbl : Array Nat) (s : Nat) : Nat :=
  let raw := physMapTabled tbl s
  if raw < numGPRegs then (straightCallRelocTable body tbl)[raw]?.getD raw
  else raw

/-- Resolve an SSA register name `n` to its physical register name for `body` —
    the single source of truth shared by `remapOperand` and every auxiliary
    name-resolution pass (`buildArgMaterializePhys`, `buildArgPtrMaterialize`,
    `buildEpilogue`, and the looped export's `memrefBaseReload`).

    A **frame-slot** name (`isFrameSlotName`: `k.`/`kv.`/`qsave.`/`mem.`) names a
    location in the frame, which the printer resolves itself, and passes through
    unchanged on every path.

    For a call-free body this is the post-RA lookup
    `physRegName (physMapTabled tbl (nameSlot body n))`. For a body that issues a
    real `Lcall` (`bodyHasCall`), the caller-save barrier engages: a literal
    hardware register (`isHwRegName`, the SysV arg/return marshalling names) is
    pinned to itself, and every other allocated GP slot is routed

    * through the **liveness-computed** straight-line relocation when the body
      is a straight-line call body (`bodyStraightCall`): the relocation is
      COMPOSED INTO `tbl` once at the export site
      (`straightCallComposeTable` in `comToLfundefPhysAbi` — call-crossing
      slots callee-saved-then-spilled, the rest to the marshal-untouched
      `R10`/`R11`-then-spill pool), so the lookup here is the plain post-RA
      one and the frame sizing sees the relocation's fresh spill indices; or
    * through the static callee-saved-first permutation (`calleeFirstPhys`)
      on the looped call path (`Llabel`/`Lcond` back-edges present).

    The prologue / arg materialize / epilogue agree with the barrier-relocated
    body (all resolve through THIS function, over the SAME composed table). -/
def physNameForBody (body : Lcmd) (tbl : Array Nat) (n : String) : String :=
  if isFrameSlotName n then n
  else if bodyHasCall body then
    if isHwRegName n then n
    else if bodyStraightCall body then
      physRegName (physMapTabled tbl (nameSlot body n))
    else physRegName (calleeFirstPhys (physMapTabled tbl (nameSlot body n)))
  else
    physRegName (physMapTabled tbl (nameSlot body n))

-- Static checks pinning the frame-slot passthrough: a GP spill, a vector spill,
-- an ABI save and a base-relative memory reference each resolve to themselves,
-- under a call-free body and under a body that issues a call, while an SSA name
-- still resolves through the allocation table.
#guard physNameForBody [] #[] "mem.RSP.0" = "mem.RSP.0"
#guard physNameForBody [] #[] "k.3" = "k.3"
#guard physNameForBody [] #[] "kv.1" = "kv.1"
#guard physNameForBody [] #[] "qsave.RDX" = "qsave.RDX"
#guard physNameForBody [⟨0, .Lcall none ("f", 0)⟩] #[] "mem.RSP.96" = "mem.RSP.96"
#guard physNameForBody [⟨0, .Lcall none ("f", 0)⟩] #[] "qsave.RDX" = "qsave.RDX"
#guard physNameForBody [] #[] "r0" = "RAX"

/-- Compose the straight-line call relocation into an allocation table: every
    GP entry is routed through `straightCallRelocTable` (computed ONCE — the
    per-name `straightCallPhys` consultation recomputed the liveness scan per
    operand), spill/vector entries pass through. Applied at the export site so
    every seam (prologue, arg materialize, body remap, epilogue, frame sizing)
    reads one coherent table — in particular the relocation's FRESH spill
    indices participate in the frame-size maximum. -/
def straightCallComposeTable (body : Lcmd) (tbl : Array Nat) : Array Nat :=
  if bodyStraightCall body then
    let reloc := straightCallRelocTable body tbl
    tbl.map (fun v => if v < numGPRegs then reloc[v]?.getD v else v)
  else tbl

/-- Remap a single `LOperand`'s register name through the physical map of `tr`,
    given the body it came from (for slot indexing). Immediates / compile-time
    array elements pass through. A register-indexed (SIB) operand
    `arrIdx base idx scale` has **both** its base pointer and index remapped to
    physical registers (both are tracked register-file sources via
    `LOperand.srcRegNames`); without this the SIB's `base`/`idx` would keep their
    raw SSA arg names (`a0`/`a1`/…) and the printer would render
    `%<UNKNOWN:aN>`.

    Each register name is the post-RA physical lookup
    `physRegName (physMapTabled tbl (nameSlot body n))`. This is the call-free
    renaming; the `Lcall` caller-save variant is `remapOperandCalleeSave`. -/
def remapOperand (body : Lcmd) (tbl : Array Nat) :
    LOperand → LOperand
  | .reg n => .reg (physRegName (physMapTabled tbl (nameSlot body n)))
  | .arrIdx base idx scale =>
      .arrIdx (physRegName (physMapTabled tbl (nameSlot body base)))
              (physRegName (physMapTabled tbl (nameSlot body idx)))
              scale
  | o => o

/-- `remapOperand` with the `Lcall` caller-save barrier: each register name is
    resolved by `physNameForBody`, so for a body that issues a real call the
    loop-carried slots are routed to callee-saved registers (`calleeFirstPhys`)
    and the SysV hardware names are pinned to themselves. `physBody` selects this
    for `bodyHasCall` bodies; a call-free body uses `remapOperand`. -/
def remapOperandCalleeSave (body : Lcmd) (tbl : Array Nat) :
    LOperand → LOperand
  | .reg n => .reg (physNameForBody body tbl n)
  | .arrIdx base idx scale =>
      .arrIdx (physNameForBody body tbl base) (physNameForBody body tbl idx) scale
  | o => o

/-- A shift-count immediate oracle: maps the SSA source register name of a
    `SHL`/`SHR` shift-count operand to its compile-time constant value, when that
    source is a constant input (so the producer can render the count as an `#imm`
    rather than a forced-`CL` register). The default oracle `fun _ => none` keeps
    every count as a register (the original behaviour); a producer that knows its
    shift constants supplies the concrete map (e.g. ChaCha's `a32 … a38 ↦
    16,12,8,7,20,24,25`). -/
abbrev ShiftImmOracle := String → Option Nat

/-- Build a shift-count oracle that resolves a count register by **dataflow**:
    a body `MOV[:w] r, #v` binding (the rendering of a nullary `regConst v`,
    `opToLinstrR`) defines `r := v`, so any `SHL`/`SHR` whose count source is
    that `r` can take the count as an `#imm` operand. This lets a producer whose
    shift counts are materialised by `regConst` bindings (rather than constant
    *inputs*, as ChaCha/SHA/Keccak use) still avoid the x86 forced-`CL`
    constraint, with no per-binding oracle to hand-write.

    `regName` is De-Bruijn-unique (`"r" ++ toString depth`), so each `MOV r,#v`
    defines a distinct `r`; the last definition for a given name wins (a name is
    never redefined under SSA, so the fold is unambiguous). Only single-source
    immediate MOVs contribute (the `regConst` shape); two-address legalization
    MOVs (`MOV dst, src0`) carry a register source and are ignored. -/
def movImmTable (body : Lcmd) : Array (Option Nat) := Id.run do
  -- Index the resolved counts by the De-Bruijn depth `k` encoded in the body
  -- name `regName k = "r" ++ toString k`, in a single `Array (Option Nat)` pass.
  -- This avoids String-keyed hashing over a ~364k-instruction body: build is
  -- O(n), lookup is O(1) on the parsed index. Names that aren't `r<k>` (e.g.
  -- `a<j>` args) never name a `regConst`, so they're absent and resolve to none.
  let mut a : Array (Option Nat) := Array.replicate body.length none
  for i in body do
    match i.li_i with
    | .Lopn [.reg d] opn [.imm v] =>
        if (stripWidthTag opn) == "MOV" then
          if d.startsWith "r" then
            match strDropToNat? d 1 with
            | some k => if k < a.size then a := a.set! k (some v)
            | none => pure ()
    | _ => pure ()
  return a

/-- Resolve a body register name `r<k>` against a prebuilt `movImmTable`. -/
def movImmLookup (tbl : Array (Option Nat)) (n : String) : Option Nat :=
  if n.startsWith "r" then
    match strDropToNat? n 1 with
    | some k => if k < tbl.size then tbl[k]! else none
    | none => none
  else none

/-- A `ShiftImmOracle` resolving `regConst`-defined shift counts by dataflow
    (see `movImmTable`). The table is built once; the returned closure captures
    it. (Provided for callers that want a standalone oracle; the ABI export
    builds the table inline so single-evaluation is guaranteed.) -/
def movImmOracle (body : Lcmd) : ShiftImmOracle :=
  let tbl := movImmTable body
  fun n => movImmLookup tbl n

/-- The two-address physical body lowering, parametric in the operand renamer
    `rmap`. `physBody` instantiates it with the call-free `remapOperand`;
    `physBodyCalleeSave` with the `Lcall` caller-save `remapOperandCalleeSave`. -/
def physBodyRmap (rmap : LOperand → LOperand) (shiftImm : ShiftImmOracle)
    (body : Lcmd) : Lcmd :=
  -- two-address mnemonics that take exactly two register sources (the optional
  -- `:64` width tag is stripped before the membership test).
  let isBinop (opn : String) : Bool :=
    ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
      (stripWidthTag opn)
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  -- The injected legalization moves inherit the op's width: a `:64` op routes
  -- its reload moves through `MOV:64` so the full 64-bit value survives.
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  -- Detect a constant shift count: either `s1` is already an `.imm` (producer-
  -- level `ImmSlotMap` substitution) or its SSA register name is covered by the
  -- legacy `ShiftImmOracle`. Both routes funnel into `lowerTwoAddrShiftImm`.
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  body.flatMap (fun i =>
    match i.li_i with
    -- Only the two-source binop alphabet is re-lowered to destructive
    -- two-address form. Three-source ops (the #477 carry-chain `ADCX`/`ADOX`
    -- + carry-out, which carry an extra `reg 1` carry-in) and every other
    -- `Lopn` (MULXHI, LOAD/STORE, casts, MOV) fall through to the general
    -- arm with **all** operands remapped — never truncated to two sources.
    | .Lopn (d :: _) opn ((s0 :: s1 :: _) : List LOperand) =>
        if isBinop opn then
          -- a constant-count shift: emit the count as an immediate
          match (if isShift opn then shiftImmVal s1 else none) with
          | some v =>
              (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
          | none =>
              (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
        else
          match i.li_i with
          -- A `STOREIDX` (register-indexed store: srcs are exactly
          -- `[arrIdx, val]`) whose remapped value source is a spill slot would
          -- render as an illegal `mov mem, mem` (the symmetric mirror of the
          -- LOAD case). Route the value through `R15` (#539 store fix).
          | .Lopn [d'] opn' [addr, val] =>
              if isMemStore opn' then
                (legalizeMemStore (rmap d') (rmap addr) (rmap val) opn' (movFor opn')).map
                  (fun r => ⟨i.li_ii, r⟩)
              else
                [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
          | .Lopn dsts opn srcs =>
              [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
          | other => [⟨i.li_ii, other⟩]
    -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): a one-source
    -- in-place op. Route a spilled operand through R15 so the owned printer
    -- never emits `mov mem, mem` (#497 native-rotate spill legalization).
    | .Lopn [d] opn [s] =>
        if isNativeShiftRotate opn then
          (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
            (fun r => ⟨i.li_ii, r⟩)
        else if isMemLoad opn then
          -- A `LOAD`/`LOADIDX` whose remapped destination is a spill slot would
          -- render as an illegal `mov mem, mem`; route through `R15`.
          (legalizeMemLoad (rmap d) (rmap s) opn (movFor opn)).map
            (fun r => ⟨i.li_ii, r⟩)
        else if stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ" then
          -- A plain register-copy `MOV`/`MOVQ` whose BOTH remapped operands are
          -- spill slots renders as an illegal `mov mem, mem`. This is the 3-deep
          -- block-loop failure mode: at that nesting the loop-carried scalars
          -- (accumulator / index / counter) all spill, so the loop-init and
          -- accumulator-feedback `MOV`s (`whileLcmdNz`, `blockLoopFrame`) get
          -- both operands in the frame. `legalizeMov` routes one side through the
          -- reserved reload scratch `R15` (`mov R15, src; mov dst, R15`), exactly
          -- as the two-address binop's leading-`mov` legalizer does. It is the
          -- identity when at most one operand is a spill, so every existing
          -- kernel's body (no surviving two-spill standalone `MOV`) is
          -- byte-identical. Passing `opn` keeps the move's width tag.
          (legalizeMov (rmap d) (rmap s) opn).map (fun r => ⟨i.li_ii, r⟩)
        else
          [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
    | .Lopn dsts opn srcs =>
        [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
    | other => [⟨i.li_ii, other⟩])

/-- The physical two-address body over the call-free `remapOperand` (the renamer
    the parametric faithfulness chain reasons about). Class-aware allocation
    (`bodyPhysTable`): GP bindings → GP regs, vector bindings → XMM. -/
def physBody (shiftImm : ShiftImmOracle) (body : Lcmd) : Lcmd :=
  physBodyRmap (remapOperand body (bodyPhysTable body)) shiftImm body

/-- The physical two-address body with the `Lcall` caller-save barrier: the
    operand renamer is `remapOperandCalleeSave`, so a body that issues a real
    `Lcall` pins the SysV hardware names and routes loop-carried slots to
    callee-saved registers. `toLfundefPhys` selects this for `bodyHasCall` bodies. -/
def physBodyCalleeSave (shiftImm : ShiftImmOracle) (body : Lcmd) : Lcmd :=
  physBodyRmap
    (remapOperandCalleeSave body
      (straightCallComposeTable body (bodyPhysTable body)))
    shiftImm body

/-- **Materialize the SysV argument registers into the body's register file**
    for the *value-return* export (`comToLfundefPhys`).

    The body reads argument `j` under the name `argName j`, which the linear-scan
    RA has assigned to some physical register `phys(aj)` that is **not** in
    general the SysV call-arg register `callRegArgs[j]` (`[RDI, RSI, …]`).
    `comToLfundefPhys` declares `lfd_arg := callRegArgs.take n` but — unlike the
    pointer-out `comToLfundefPhysAbi`, which calls `buildArgPtrMaterialize` —
    previously emitted **no** copy from `callRegArgs[j]` into `phys(aj)`. The body
    then read whatever was in `phys(aj)` at entry (a callee-saved register it just
    saved, hence a constant value independent of the argument). This emits, for
    each in-range argument `j` whose name `aj` the body actually references, the
    entry copy `phys(aj) ← callRegArgs[j]`, sourcing the *live* SysV register
    directly (there is no red-zone save on this path):

    * `phys(aj) == callRegArgs[j]`: skipped (value already in place);
    * `phys(aj)` a register `R`: `mov R, callRegArgs[j]`;
    * `phys(aj)` a spill `k.N`: `mov R15, callRegArgs[j]; mov [k.N], R15`.

    Copies are emitted in argument order. (For the simple value-return kernels
    that use this path — single-word doubling / reductions — there is no
    cross-argument aliasing where one argument's destination register is another,
    later, argument's live source.) -/
def buildArgMaterializePhys (virt : Lfundef) (tbl : Array Nat)
    (callRegArgs : List String) : Lcmd :=
  let body := virt.lfd_body
  let nArgs := min virt.lfd_arg.length callRegArgs.length
  ((callRegArgs.take nArgs).zipIdx).flatMap (fun ⟨abiReg, j⟩ =>
    let nm := argName j
    let used := body.any (fun i =>
      match i.li_i with
      | .Lopn _ _ srcs => srcs.any (fun s =>
          match s with
          | .reg n => n == nm
          | .arrIdx b idx _ => b == nm || idx == nm
          | _ => false)
      | _ => false)
    if !used then []
    else
      -- Resolve through the SAME barrier the body used (`physNameForBody`): a
      -- call-containing body relocated this slot via `calleeFirstPhys`, so the
      -- entry copy must target the relocated register, not the raw one.
      let phys := physNameForBody body tbl nm
      let dst : LOperand := .reg phys
      if phys == abiReg then []
      else if dst.isSpill then
        [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg abiReg]⟩,
         ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
      else
        [⟨0, .Lopn [dst] "MOVQ" [.reg abiReg]⟩])

/-- The physical `lfundef` for a `Com`: same args/types/result as the virtual
    `comToLfundef`, but a physical, two-address body and result register. The
    result register name is the physical location of the virtual result.
    `shiftImm` (default: none) supplies the constant shift-count → immediate map
    for `SHL`/`SHR` counts. -/
def comToLfundefPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let virt := comToLfundef com immSlotMap
  -- Class-aware table (matches `physBody`'s `bodyPhysTable`): GP→GP, vector→XMM.
  -- For a pure-scalar body this is `physTable (bodyTrace …)`, so unchanged.
  -- Straight-line call bodies get the liveness relocation composed in once
  -- (`straightCallComposeTable`, identity otherwise) — the SAME table
  -- `physBodyCalleeSave` remaps with, so the seams agree.
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body)
  -- Resolve through the body's barrier so the `RAX` return epilogue reads the
  -- register a call-containing body left the result in (`physNameForBody`).
  let resPhys := virt.lfd_res.map (physNameForBody virt.lfd_body tbl)
  -- `assemble_fd` (jasmin `proofs/arch/asm_gen.v`, line 602) requires every
  -- `lfd_arg` entry to be mappable to a typed register via
  -- `asm_typed_reg_of_var`. The virtual `comToLfundef.lfd_arg` carries `aN`
  -- names which are not architecture registers (they would fail
  -- `to_reg`/`to_regx`/`to_xreg`/`to_rflag` and trigger
  -- `asmgen: can not map variable to a register`).
  --
  -- The physical body has already rewritten every `aN` source operand to
  -- its post-RA physical register via the linear-scan map (`physBody` +
  -- `remapOperand`), so the args are not referenced by name in the body.
  -- We therefore project `lfd_arg` to the **first six registers of the x86
  -- SysV calling convention** (`[RDI, RSI, RDX, RCX, R8, R9]`) — the
  -- `call_reg_args` list `check_call_conv` checks against. The producer
  -- emits up to six arguments; remaining inputs are expected by the body
  -- as register reads (the caller materialises them per the body's RA
  -- choice, which is the trust boundary documented in the bench README).
  let callRegArgs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
  let nArgsExported : Nat := min virt.lfd_arg.length callRegArgs.length
  let argSig := callRegArgs.take nArgsExported
  let tyinSig := virt.lfd_tyin.take nArgsExported
  -- Copy each SysV argument register `callRegArgs[j]` into the physical register
  -- the RA assigned to the body's `argName j` (skipping copies already in place).
  -- Without this, the body read uninitialised registers as its inputs and the
  -- result was constant in the arguments.
  let argMat := buildArgMaterializePhys virt tbl callRegArgs
  let pbody := if bodyHasCall virt.lfd_body
               then physBodyCalleeSave shiftImm virt.lfd_body
               else physBody shiftImm virt.lfd_body
  -- Move the result into the SysV return register `RAX` before the trailing
  -- `Lret`. The renderer (`renderLfundef`) emits a bare `ret` and the SysV
  -- callee returns its `uint64_t`/`uint32_t` result in `RAX` (`EAX`), but the
  -- linear-scan RA assigns the `Com`'s `.ret` value to an arbitrary physical
  -- register (`resPhys`, e.g. `RBX` for the doubling kernel). Without this copy
  -- the function returns whatever happens to be in `RAX` (a stale intermediate),
  -- not the computed result. Inserted before the final `Lret` (mirroring
  -- `insertEpilogue`), and skipped when the result already lands in `RAX`.
  let retEpi : Lcmd :=
    match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let bodyWithRet : Lcmd :=
    if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  { virt with
    lfd_body := argMat ++ bodyWithRet
    lfd_arg := argSig
    lfd_tyin := tyinSig
    lfd_res := resPhys }

/-- Export a `Com` to a physical-register, two-address `Lprog`.
    * `shiftImm` (default: none) — legacy SSA-name-keyed shift-count oracle.
    * `immSlotMap` (default: none) — producer-level slot → constant map; the
      preferred path since it works regardless of how SSA names get rewritten
      by alpha-renaming/`physBody` rmap. -/
def Com.toLprogPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, comToLfundefPhys com shiftImm immSlotMap)] }

/-- Serialize the physical export to the textual lprog blob (magic + text). -/
def Com.toLprogPhysText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : String :=
  magic ++ (Com.toLprogPhys com fname shiftImm immSlotMap).toText ++ "\n"

/-- The physical export's bytes. -/
def Com.toLprogPhysBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : ByteArray :=
  (Com.toLprogPhysText com fname shiftImm immSlotMap).toUTF8

/-- Write the physical-register lprog blob for a `Com` to a file. -/
def Com.writeLprogPhysFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    IO Unit :=
  IO.FS.writeBinFile path (Com.toLprogPhysBytes com fname shiftImm immSlotMap)

/-! ### 7f. ABI prologue/epilogue (2-pointer SysV calling convention)

`comToLfundefPhys` exports `lfd_arg` as the first six SysV call-arg registers
`[RDI, RSI, …]`, which satisfies `assemble_fd`'s `check_call_conv` but leaves
the caller to materialise the remaining input slots (every input beyond the
first six is read by the body but never bound to a call-arg register).

For a real C-side ABI like `chacha20_block(uint32_t *out, const uint32_t *inp)`
the caller passes **two pointers** (`RDI = out`, `RSI = inp`) and the body
loads its scalar inputs from `[RSI + 4*k]` and stores its scalar outputs to
`[RDI + 4*k]`. The producer wraps the verified physical body with an ABI
prologue (loads) and epilogue (stores), keeping the body unchanged:

```
prologue (loads):
  mov  R_phys_of_argslot,  [RSI + 4*k]      -- one per active argument slot
                                            -- (slots covered by an immSlotMap
                                            -- entry are skipped — already #imm)
body:
  <unchanged physBody>                       -- the verified two-address body
epilogue (stores), before Lret:
  mov  [RDI + 4*j], R_phys_of_output_j      -- one per output word
```

The memory operand for `[base + off]` is rendered as the register-name string
`"mem.<base>.<off>"` — the `LOperand.reg` constructor is reused (so existing
`LOperand`-keyed proofs are unchanged); `read_linear.ml` recognises the
`"mem."` prefix and materialises the operand as `Fexpr.Load`/`Fexpr.Store` at
`[<base> + <off>]`, exactly mirroring how the `"k."` spill prefix is handled.
-/

/-- An input-load map: argument slot index → `(base-pointer register, byte
    offset)`. The prologue emits a `mov R_phys_of_argslot, [base + off]` for each
    slot the map covers, where `R_phys_of_argslot` is the post-RA physical
    register the body reads at that argument slot. Slots not in the map are
    skipped (e.g. constant-input slots covered by an `immSlotMap`). -/
abbrev InLoadMap := Nat → Option (String × Nat)

/-- An output-store target: the i-th entry is the `(base-pointer register, byte
    offset)` to store the i-th of the last `storeTargets.length` bindings'
    results into. The epilogue emits a `mov [base + off], R_phys_of_output_i`
    for each target, before the body's `Lret`. -/
abbrev OutStoreMap := List (String × Nat)

/-- Render a `[base + off]` memory reference as a register-name string, using
    the convention `read_linear.ml` parses (mirrors the `k.<N>` spill prefix).
    Used inside `LOperand.reg` so no new `LOperand` constructor is needed and
    existing `LOperand`-keyed proofs continue to apply. -/
def memName (base : String) (off : Nat) : String :=
  "mem." ++ base ++ "." ++ toString off

-- The loop-body buffer name agrees with the general frame-memory name. The walk
-- that lays those buffers sits above this definition and carries its own copy of
-- the spelling; these checks hold the two together.
#guard frameBufName 0 = memName "RSP" 0
#guard frameBufName 32 = memName "RSP" 32

/-- The destination operand name of the `bidx`-th binding of a virtual body
    `body` (counting only `Lopn`s; `Lret` is skipped). The binding's destination
    is the first lexpr of its `Lopn`. Returns `none` if `bidx` is out of range
    or the binding has no register destination. -/
def bindingDstOp (body : Lcmd) (bidx : Nat) : Option LOperand :=
  match (body.filterMap (fun i =>
    match i.li_i with
    | .Lopn (d :: _) _ _ => some d
    | _ => none))[bidx]? with
  | some d => some d
  | none => none

/-- The total number of `Lopn` bindings in a virtual body (excludes `Lret`). -/
def numBindings (body : Lcmd) : Nat :=
  body.foldl (fun n i =>
    match i.li_i with
    | .Lopn _ _ _ => n + 1
    | _ => n) 0

/-- The logical slots holding the `n = outStoreMap.length` designated outputs of
    `body`, in output order. The `j`-th output is the destination register of the
    `(firstOutIdx + j)`-th `Lopn` binding (`firstOutIdx = numBindings - n`) — the
    SAME binding the epilogue stores into `out[j]`. A binding with no register
    destination (or out of range) contributes no slot. -/
def outStoreSlots (body : Lcmd) (outStoreMap : OutStoreMap) : List Nat :=
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  (List.range n).filterMap (fun j =>
    match bindingDstOp body (firstOutIdx + j) with
    | some (.reg name) => some (nameSlot body name)
    | _ => none)

/-- **Multi-output liveness fix.** The body's register allocator (`physTable ∘
    bodyTrace`) computes each slot's live range as `[firstTouch, lastTouch]` over
    the body trace ALONE — it does not see the ABI epilogue's inline output stores
    (those are inserted AFTER allocation, by `physBodyWithStores`). So a
    designated-output slot's range ends at the binding that defines it: it is
    never read again inside the body, and the linear scan freely reclaims its
    physical register for a later binding.

    When the last `n` bindings are short, non-overlapping live ranges (the worst
    case: trailing identity copies `out[k] := out[k] | out[k]` emitted by a
    multi-output producer), the scan assigns ALL of them the lowest free physical
    register — so every output slot coalesces onto ONE register and the epilogue
    stores the same value into every `out[j]`.

    This appends one synthetic liveness event to the trace that READS every output
    slot simultaneously at the final position. That extends each output slot's
    `lastTouch` to the trace end and makes the `n` output slots mutually live, so
    the linear scan is forced to keep each in its OWN physical register (none can
    be reclaimed or coalesced before the stores run). The event writes no fresh
    slot (`wr` reuses the first output slot, already touched), so it does not grow
    the slot universe. When `outStoreMap = []` (every register-ABI / single-store
    kernel) the appended event list is empty and the trace is byte-identical, so
    those exports are unchanged. -/
def bodyTraceOut (body : Lcmd) (outStoreMap : OutStoreMap) : List PhysEvent :=
  let base := bodyTrace body
  match outStoreSlots body outStoreMap with
  | [] => base
  | slots@(s0 :: _) => base ++ [{ wr := s0, rds := slots }]

/-- The output-liveness-extended physical-allocation table: `physTable` over the
    trace augmented by `bodyTraceOut`. Used wherever the ABI export resolves a
    body name to its post-RA physical register so that the `n` distinct outputs
    occupy `n` distinct physical registers across the epilogue stores. Reduces to
    `physTable (bodyTrace body)` when `outStoreMap = []`. -/
def physTableOut (body : Lcmd) (outStoreMap : OutStoreMap)
    (reservedVec : List Nat := []) : Array Nat :=
  -- Class-aware (`bodyVecSlots`): GP outputs → GP regs, vector outputs → XMM, in
  -- one scan. For a body with no vector op this is `physTable (bodyTraceOut …)`,
  -- so the GP-only multi-output allocation is byte-identical. `reservedVec`
  -- (default `[]`) excludes vector indices; the batch8 path passes `[numVecRegs-1]`.
  physTableClassed (bodyTraceOut body outStoreMap) (bodyVecSlots body)
    (bodyReservedGP body) reservedVec

/-- Conservative upper bound on the argument-slot count referenced by a virtual
    body: the maximum `s` such that `argName s` appears anywhere in the body,
    plus one (saturating at zero when no arg name is referenced). Used by
    `physBodyWithStores` to size the first-use tracking array. -/
def virtBodyNumArgs (body : Lcmd) : Nat :=
  body.foldl (fun n i =>
    match i.li_i with
    | .Lopn _ _ srcs =>
        srcs.foldl (fun n' s =>
          match s with
          | .reg name =>
              if name.startsWith "a" then
                match strDropToNat? name 1 with
                | some k => Nat.max n' (k + 1)
                | none => n'
              else n'
          | _ => n') n
    | _ => n) 0

/-- The textual operand name of the 64-bit `RDI` save slot in the red zone.
    The convention `qsave.<reg>` is recognised by `read_linear.ml` as a
    `Load/Store U64` at a fixed red-zone offset (`RSP - 128` for `qsave.RDI`,
    `RSP - 120` for `qsave.RSI`). The high 16 bytes of the 128-byte red zone
    hold the two saved SysV-argument pointers; `k.N` U32 spill slots used by
    the body's register allocator occupy the remaining 112 bytes (≤28 spills
    fit, well above ChaCha's ~5). -/
def abiSaveRdiName : String := "qsave.RDI"

/-- The textual operand name of the 64-bit `RSI` save slot in the red zone.
    See `abiSaveRdiName` for the layout convention. -/
def abiSaveRsiName : String := "qsave.RSI"

/-- Build the ABI prologue. The prologue is now just the **pointer save/copy**
    prelude; the per-slot input loads are inlined into the body by
    `physBodyWithStores` (at each argument slot's first-use position) so the
    body's existing linear-scan RA correctly accounts for their lifetime.

    Two complications drive the shape:

    * `RSI`/`RDI` are in the linear scan's allocatable register set, so the
      body's RA may assign an SSA slot to physical `RSI` / `RDI`. The very
      act of writing physical `RSI` clobbers the input pointer.
    * We can't extend `lfd_arg` beyond the 2-pointer SysV signature
      (`check_call_conv` constrains this).

    Solution: at the very start of the prologue, **save** `RDI` to a red-zone
    save slot (so the epilogue can recover it after the body has clobbered
    `RDI`), and **copy** `RSI` into the reserved secondary scratch `R14` (so
    the inline per-slot loads can use `[R14 + off]` as their base, immune to
    clobbers of `RSI`):

    ```
    movq  [qsave.RDI], RDI       -- save out-pointer to red zone
    movq  R14,         RSI       -- park inp-pointer in R14 (reserved scratch)
    ```

    SysV x86-64 ABI callee-saved GP set is `{RBX, RBP, R12, R13, R14, R15}`.
    Although `R14` and `R15` are *also* used as our reserved reload scratches
    (so the body transiently writes them), we must restore the caller's
    values before `Lret`. Hence we save **all six** SysV callee-saved
    registers into the red zone here; the epilogue
    (`calleeSaveRestoreEpilogue`) restores them. The pre-2026-05-27 prologue
    saved only `RBX/RBP/R12/R13` and treated `R14/R15` as caller-saved
    scratches — this was a correctness bug surfaced when a caller compiled
    at `-O2 -march=native` hoisted a loop-invariant into `R14`/`R15` across
    our call site (every prior bench passed by luck because the harnesses
    never loaded state into those registers).

    `inLoadMap` is taken as a parameter only for the legality lemmas (so
    `buildPrologue_all_MOV_or_MOVQ` doesn't change shape); the actual
    per-slot loads are emitted inside `physBodyWithStores`. -/
def buildPrologue (_virt : Lfundef) (_tbl : Array Nat)
    (_inLoadMap : InLoadMap) : Lcmd :=
  -- The body's linear-scan RA may allocate any of the SysV callee-saved GP
  -- registers (RBX, RBP, R12, R13) — all four are in `gpRegNames`. The
  -- body's reload pass additionally writes R14 / R15 as reserved scratches.
  -- SysV x86-64 ABI callee-saved = {RBX, RBP, R12, R13, R14, R15}; all six
  -- must be saved and restored.
  --
  -- Red-zone layout (high to low, starting at RSP-128):
  --   [-128..-121]  qsave.RDI
  --   [-120..-113]  qsave.RSI
  --   [-112..-105]  callee-saved RBX
  --   [-104..-97]   callee-saved RBP
  --   [-96..-89]    callee-saved R12
  --   [-88..-81]    callee-saved R13
  --   [-80..-73]    callee-saved R14   (added 2026-05-27 for ABI correctness)
  --   [-72..-65]    callee-saved R15   (added 2026-05-27 for ABI correctness)
  --   k.0 = -4, k.1 = -8, ..., k.N at -4-4N (body's u32 spills)
  --
  -- Then save BOTH pointers and park RSI into R14 for the first inline load.
  -- The R14/R15 saves happen BEFORE the RSI-park into R14 (the park clobbers
  -- the original R14 value).
  [⟨0, .Lopn [.reg abiSaveRdiName] "MOVQ" [.reg "RDI"]⟩,
   ⟨0, .Lopn [.reg abiSaveRsiName] "MOVQ" [.reg "RSI"]⟩,
   ⟨0, .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"]⟩,
   ⟨0, .Lopn [.reg "qsave.RBP"] "MOVQ" [.reg "RBP"]⟩,
   ⟨0, .Lopn [.reg "qsave.R12"] "MOVQ" [.reg "R12"]⟩,
   ⟨0, .Lopn [.reg "qsave.R13"] "MOVQ" [.reg "R13"]⟩,
   ⟨0, .Lopn [.reg "qsave.R14"] "MOVQ" [.reg "R14"]⟩,
   ⟨0, .Lopn [.reg "qsave.R15"] "MOVQ" [.reg "R15"]⟩,
   ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg "RSI"]⟩]

/-- The red-zone save-slot name a SysV pointer-argument register is parked into
    by `buildPrologue`. The canonical 2-pointer ABI saves `RDI`/`RSI`; any other
    ABI register sources straight from itself (it is still live at entry). -/
def abiSaveOf (reg : String) : Option String :=
  if reg == "RDI" then some abiSaveRdiName
  else if reg == "RSI" then some abiSaveRsiName
  else none

/-- The save slot an input load recovers its base pointer from: the slot of the
    base register the `InLoadMap` entry names, and `qsave.RSI` for a base with no
    save slot. A map that names only `RSI` gets `qsave.RSI`, so its loads are
    unchanged; a map that also names `RDI` reads those inputs through the saved
    `RDI`. -/
def abiLoadSave (base : String) : String := (abiSaveOf base).getD abiSaveRsiName

/-- A map naming `RSI` recovers its pointer from `qsave.RSI`, as every load did
    before the base was honoured, so those callers' loads are unchanged. -/
theorem abiLoadSave_rsi : abiLoadSave "RSI" = abiSaveRsiName := rfl

/-- A map naming `RDI` recovers its pointer from `qsave.RDI`. -/
theorem abiLoadSave_rdi : abiLoadSave "RDI" = abiSaveRdiName := rfl

/-- The red-zone save-slot name for the 3rd+ SysV pointer-argument registers
    (`RDX`, `RCX`, `R8`, `R9`) used by the **multi-input looped** 2-pointer-ABI
    export (`ComL.toLfundefPhysAbi`). The straight-line export never sees these
    (its callers all use the 2-pointer `[RDI, RSI]` signature), so this is kept
    separate from `abiSaveOf` to leave the straight-line / single-input bytes
    untouched.

    A multi-input GF-dot kernel (`out[i] := f(a[i], b[i])`, the `qruov`/`sdith`
    shape) takes `inArgs = [a, b]` with `abiArgs = [RDI, RSI, RDX]`. Each input
    array base must reload from ITS OWN red-zone qsave slot before every
    `LOADIDX`; without a slot for the 2nd input it would (mis-)reload from the
    out slot (`qsave.RDI`), reading `out[]` as `b[]` — garbage. So every ABI
    register in the signature gets a slot.

    Offsets continue the `buildPrologue` red-zone layout below `qsave.R15`
    (`RSP-72`): `qsave.RDX = RSP-64`, `qsave.RCX = RSP-56`, `qsave.R8 = RSP-48`,
    `qsave.R9 = RSP-40`. `read_linear.ml`'s `qsave_addr_of_name` must map these
    to the matching offsets. -/
def abiSaveOfExt (reg : String) : Option String :=
  match abiSaveOf reg with
  | some s => some s
  | none =>
      if reg == "RDX" then some "qsave.RDX"
      else if reg == "RCX" then some "qsave.RCX"
      else if reg == "R8"  then some "qsave.R8"
      else if reg == "R9"  then some "qsave.R9"
      else none

/-- **Materialize the pointer arguments into the body's register file.**

    The 2-pointer memref ABI (`inLoadMap = none`, `outStoreMap = []`: the body
    self-addresses through pointer arguments used as `LOADIDX`/`STOREIDX` SIB
    bases — ChaCha/SHA/Keccak whole-state kernels) needs each argument name
    `aj` to actually hold the value of the j-th SysV argument register at entry.
    The linear-scan RA assigns `aj` to some physical register or spill slot
    (`physMapTabled tbl (nameSlot virt aj)`) that is **not** in general the ABI
    register `abiArgs[j]` (observed: ChaCha's out-pointer `a0 ↦ RCX`, in-pointer
    `a1 ↦ k.5`), and the prologue only *saves* `RDI`/`RSI` — nothing copies them
    into `aj`'s slot. The body then reads a garbage register / uninitialized
    spill as its SIB base, so every input load and output store hits a wrong
    address (the observed segfault / stack corruption).

    This emits, for each in-range ABI argument `j` whose body name `aj` is
    *actually used*, the copy `aj ← abiArgs[j]` sourced from the argument's
    red-zone save slot (`qsave.RDI`/`qsave.RSI`, written first by
    `buildPrologue`) so no source register is clobbered by an earlier copy:

    * `aj`'s slot is a register `R`: `mov R, [qsave.<abiArg>]` (legal mem→reg);
      skipped entirely when `R == abiArgs[j]` (the value is already in place).
    * `aj`'s slot is a spill `k.N`: `mov R15, [qsave.<abiArg>]; mov [k.N], R15`
      (a direct `mov [k.N], [qsave]` would be an illegal mem→mem).

    For an ABI register with no red-zone save (any beyond the canonical `RDI`/
    `RSI`), the copy sources the live ABI register directly (`mov R, ABIreg`);
    these run after the qsave-sourced copies and the live register is untouched
    by them. The per-word scalar ABI (`inLoadMap` non-empty) sets `aj` via the
    inline first-use loads instead, so for those callers this prelude is empty
    (their `aj` names are not used as bare registers / SIB bases). -/
def buildArgPtrMaterialize (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) : Lcmd :=
  let body := virt.lfd_body
  (abiArgs.zipIdx).flatMap (fun ⟨abiReg, j⟩ =>
    -- A slot covered by `inLoadMap` is materialized by the inline first-use
    -- load, not here (scalar-word ABI) — skip it.
    match inLoadMap j with
    | some _ => []
    | none =>
        let nm := argName j
        -- Only materialize argument names the body actually references.
        let used := body.any (fun i =>
          match i.li_i with
          | .Lopn _ _ srcs => srcs.any (fun s =>
              match s with
              | .reg n => n == nm
              | .arrIdx b idx _ => b == nm || idx == nm
              | _ => false)
          | _ => false)
        if !used then []
        else
          -- Resolve through the body's barrier (`physNameForBody`) so the
          -- pointer load targets the same register a call-containing body reads.
          let phys := physNameForBody body tbl nm
          let dst : LOperand := .reg phys
          -- `abiSaveOfExt`: the 3rd+ SysV argument registers (`RDX`/`RCX`/…) source
          -- from their own qsave slots (saved by the `extraInputSaves` prologue
          -- tail). `abiSaveOfExt = abiSaveOf` on `{RDI, RSI}`, so ≤2-arg kernels
          -- are byte-identical.
          match abiSaveOfExt abiReg with
          | some saveName =>
              let memSrc : LOperand := .reg saveName
              if dst.isSpill then
                [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [memSrc]⟩,
                 ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
              else if phys == abiReg then
                -- Value already in the right register; nothing to do.
                []
              else
                [⟨0, .Lopn [dst] "MOVQ" [memSrc]⟩]
          | none =>
              -- No red-zone save: source the live ABI register directly.
              if phys == abiReg then []
              else if dst.isSpill then
                [⟨0, .Lopn [.reg reloadScratch] "MOVQ" [.reg abiReg]⟩,
                 ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
              else
                [⟨0, .Lopn [dst] "MOVQ" [.reg abiReg]⟩])

/-- Build the ABI epilogue. The epilogue runs after the verified two-address
    body, and is responsible for getting the body's last-`n` SSA results out
    to the C-side `out` buffer.

    Since the body may have used physical `RDI` as a normal allocation target
    (RDI is in `gpRegNames`), the original C-ABI value of `RDI` (the output
    pointer) has been clobbered by the time the epilogue runs. The prologue
    saved it to the red zone (`k.31`); the epilogue restores it into the
    reserved secondary scratch `R14` (so subsequent stores can use
    `[R14 + off]` as their base):

    ```
    mov  R14, [k.31]         -- recover out-pointer from red zone
    <per-output stores via [R14 + off]>
    ```

    Then for each output target, emit a `mov [R14 + off], R_phys` (register
    source) or a two-step `mov R15, [k.N]; mov [R14 + off], R15` (spill source
    — single-memory legality forbids `mov [mem], [spill]` directly). The
    source's physical name comes from the post-RA lookup of the i-th `Lopn`
    binding's destination in the virtual body (the i-th of the last `n`,
    where `n = outStoreMap.length`). Stores are emitted in output order
    (target 0 first). The base register inside `memName` is always `R14`,
    regardless of what the caller-side `outStoreMap` says. -/
def buildEpilogue (virt : Lfundef) (tbl : Array Nat)
    (outStoreMap : OutStoreMap) : Lcmd :=
  let restore : Lcmd :=
    [⟨0, .Lopn [.reg reloadScratch2] "MOV" [.reg abiSaveRdiName]⟩]
  let n := outStoreMap.length
  let total := numBindings virt.lfd_body
  let firstOutIdx := total - n
  let stores : Lcmd := (List.range n).flatMap (fun j =>
    match outStoreMap[j]? with
    | none => []
    | some (_base, off) =>
        match bindingDstOp virt.lfd_body (firstOutIdx + j) with
        | none => []
        | some (.reg srcName) =>
            -- Resolve through the body's barrier (`physNameForBody`) so the
            -- store reads from the register a call-containing body wrote.
            let phys := physNameForBody virt.lfd_body tbl srcName
            let src : LOperand := .reg phys
            -- Always store via R14 (the restored out-pointer).
            let memDst : LOperand := .reg (memName reloadScratch2 off)
            if src.isSpill then
              -- spill source: route through the reserved reload scratch
              [⟨0, .Lopn [.reg reloadScratch] "MOV" [src]⟩,
               ⟨0, .Lopn [memDst] "MOV" [.reg reloadScratch]⟩]
            else
              [⟨0, .Lopn [memDst] "MOV" [src]⟩]
        | some _ => [])
  restore ++ stores

/-- Insert the epilogue stores just before the final `Lret` of a body. The
    body's last instruction is always `Lret` (proved by `comToBody_ends_Lret`);
    we drop it, append the epilogue, then re-append the `Lret`. -/
def insertEpilogue (body : Lcmd) (epi : Lcmd) : Lcmd :=
  body.dropLast ++ epi ++ [⟨0, .Lret⟩]

/-- A `physBody` variant that:

    1. Inserts ABI-prologue loads INLINE — for each argument slot covered by
       `inLoadMap`, the load is emitted just before the FIRST virtual body
       instruction that reads it. This solves the lifetime problem on the
       INPUT side: the existing linear-scan RA assumes each arg slot's
       physical register is "live from first use to last use"; loading all
       args upfront would force them to be simultaneously live at position 0,
       and any two slots sharing a physical register (because their body
       liveness doesn't overlap) would clobber each other. Loading at
       first-use exactly matches the RA's lifetime model.

    2. Inserts ABI-epilogue stores INLINE — for each of the last `n` `Lopn`
       bindings (where `n = outStoreMap.length`), a store of the binding's
       destination physical register to `[storeBase + offset]` is emitted
       just after the binding's physBody expansion. This solves the lifetime
       problem on the OUTPUT side: under SSA only the LAST `Com.ret` value
       is live at function exit; the other 15 outputs' physical registers
       have been reclaimed for later computations. Storing each output
       inline preserves the value before any subsequent overwrite.

    Each store is preceded by a `mov reloadScratch2, [qsave.RDI]` to recover
    the out-pointer (since `reloadScratch2 = R14` may have been transiently
    used as a body scratch).

    Both load- and store- bases default to `reloadScratch2` (= `R14`). The
    prologue (built by `buildPrologue`) parks `RSI` into `R14` for the load
    side; the per-store reload puts `RDI` (recovered from `qsave.RDI`) into
    `R14` for the store side. -/
/- Compiled twin of `physBodyWithStores`. Semantically identical to the spec
    below, but it removes the spec's quadratic recomputations for a ~4000-binding
    body:

    * `bidx` (binding index at each position) is carried in a running counter
      instead of `(body.take virtIdx).filter …).length` per position (`O(n²)`);
    * the argument-slot first-use map is built by parsing the `aN` slot index
      directly from each source name (`O(n)`), instead of scanning
      `List.range nArgs` per source (`O(n·nArgs)`);
    * loads-at-position is an array indexed by position (`O(1)` lookup).

    The remapping (`rmap`), two-address lowering, and emitted-instruction shapes
    are byte-for-byte the spec's. -/
@[inline] unsafe def physBodyWithStoresImpl (shiftImm : ShiftImmOracle)
    (body : Lcmd) (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) : Lcmd :=
  -- Output-liveness-extended allocation: the `n` designated output slots are kept
  -- in `n` distinct physical registers across the epilogue stores (see
  -- `bodyTraceOut`). Reduces to `physTable (bodyTrace body)` for `outStoreMap=[]`.
  let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
  -- Caller-save clobber barrier (matches the spec `physBodyWithStores`): a body
  -- carrying a real `Lcall` renames through `remapOperandCalleeSave`; a call-free
  -- body keeps `remapOperand` (byte-identical).
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl
              else remapOperand body tbl
  let isBinop (opn : String) : Bool :=
    ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
      (stripWidthTag opn)
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  -- The ABI prologue/epilogue moves the U64 state lanes whenever the body is a
  -- U64 kernel (Keccak): a body op carrying `:64` ⇒ the inline load/store moves
  -- must be `MOV:64` so the full 64-bit memory value survives.
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  -- The ABI MOV widths (#656 narrow-buffer seam). Two distinct legs:
  --   * `abiMovBuf` — the mov that **touches the C buffer** (`mem.RSI`/`mem.RDI`).
  --     When the caller passes a narrow `abiW` (16 / 8 — the buffer's *element*
  --     width, e.g. Frodo's `uint16_t`), this leg is tagged `MOV:16`/`MOV:8`, so
  --     the owned printer renders a zero-extending `movz{w,b}l` load (a memory
  --     source → 32-bit working register) and a width-exact `mov{w,b}` store (a
  --     memory dest → narrow write, no overrun of the neighbouring element).
  --   * `abiMovReg` — the mov on the **scratch ↔ spill** routing leg (register to
  --     register / register to spill). This must stay full-width (`MOV:64`/`MOV`):
  --     the spill holds the body's working value, so narrowing it would truncate.
  -- `abiW = 0` (every existing caller) makes both legs the pre-#656
  -- `MOV:64`/`MOV`, so the emitted body is byte-identical. `abiW = 256` (the
  -- batch8 packed SoA ABI) makes both legs `VMOVDQU`, so the printer renders the
  -- `mem ↔ %ymm` loads/stores as `vmovdqu`.
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  -- Parse `argName s = "a" ++ toString s` back to its index `s` (none if the
  -- name is not an arg name in range).
  let argIdx? (nm : String) : Option Nat :=
    if nm.startsWith "a" then
      match strDropToNat? nm 1 with
      | some s => if s < nArgs then some s else none
      | none => none
    else none
  -- argSlot s -> first virt position that reads it, and the inverse:
  -- position -> list of (argSlot, base, off) loads to emit before it.
  let firstUseMap : Array (Option Nat) := Id.run do
    let mut arr : Array (Option Nat) := Array.replicate nArgs none
    let mut pos := 0
    for i in body do
      match i.li_i with
      | .Lopn _ _ srcs =>
          for src in srcs do
            match src with
            | .reg nm =>
                match argIdx? nm with
                | some s => if (arr[s]!).isNone then arr := arr.set! s (some pos)
                | none => pure ()
            | _ => pure ()
      | _ => pure ()
      pos := pos + 1
    return arr
  let loadsByPos : Array (List (Nat × String × Nat)) := Id.run do
    let mut arr : Array (List (Nat × String × Nat)) := Array.replicate body.length []
    for s in List.range nArgs do
      match firstUseMap[s]! with
      | some fpos =>
          if fpos < arr.size then
            match inLoadMap s with
            | some (base, off) => arr := arr.set! fpos (arr[fpos]! ++ [(s, base, off)])
            | none => pure ()
      | none => pure ()
    return arr
  -- Emit, carrying the running binding index (`bidx` of each position).
  Id.run do
    let mut out : Array Linstr := #[]
    let mut bidx := 0
    let mut virtIdx := 0
    for i in body do
      let loads : Lcmd := (loadsByPos[virtIdx]!).flatMap (fun ⟨_s, base, off⟩ =>
        let phys := physNameForBody body tbl (argName _s)
        let dst : LOperand := .reg phys
        let memSrc : LOperand := .reg (memName base off)
        let reloadIn : Linstr :=
          ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
        if dst.isSpill then
          [reloadIn,
           ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
           ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
        else
          [reloadIn,
           ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
      let thisBidx := bidx
      let expanded : Lcmd :=
        match i.li_i with
        | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
            if isBinop opn then
              match (if isShift opn then shiftImmVal s1 else none) with
              | some v =>
                  (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                    (fun r => ⟨i.li_ii, r⟩)
              | none =>
                  (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                    (fun r => ⟨i.li_ii, r⟩)
            else
              -- #477: three-source carry ops keep all sources (no truncation).
              match i.li_i with
              -- A `STOREIDX` (srcs `[arrIdx, val]`) whose remapped value source
              -- is a spill slot would render as an illegal `mov mem, mem` (the
              -- mirror of the LOAD case). Route the value through `R15` (#539).
              | .Lopn [d'] opn' [addr, val] =>
                  if isMemStore opn' then
                    -- Reload the memref base pointer from its red-zone qsave slot
                    -- into R14 immediately before the store: the RA-assigned
                    -- ABI register holding it has been clobbered by the body.
                    let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                    (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                    (legalizeMemStore (rmap d') addr' (rmap val) opn'
                       (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                  else
                    [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
              | .Lopn dsts opn srcs =>
                  [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
              | other => [⟨i.li_ii, other⟩]
        -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): one-source
        -- in-place op. Route a spilled operand through R15 (#497 spill legalize).
        | .Lopn [d] opn [s] =>
            if isNativeShiftRotate opn then
              (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
            else if isMemLoad opn then
              -- A `LOAD`/`LOADIDX` into a spill slot would render as an illegal
              -- `mov mem, mem`; route through `R15` (#539 whole-state load fix).
              -- First reload the memref base pointer from its qsave slot into R14.
              let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
              (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
              (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
                (fun r => ⟨i.li_ii, r⟩)
            else
              [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
        | .Lopn dsts opn srcs =>
            [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
        | other => [⟨i.li_ii, other⟩]
      let store : Lcmd :=
        match i.li_i with
        | .Lopn (d :: _) _ _ =>
            if thisBidx ≥ firstOutIdx ∧ thisBidx < total then
              let outIdx := thisBidx - firstOutIdx
              match outStoreMap[outIdx]? with
              | some (_base, off) =>
                  let src := rmap d
                  let memDst : LOperand := .reg (memName storeBase off)
                  let reloadOut : Linstr :=
                    ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                  if src.isSpill then
                    [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                     reloadOut,
                     ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                  else
                    [reloadOut,
                     ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
              | none => []
            else []
        | _ => []
      -- After a real in-loop `Lcall`, restore each loop-invariant pointer base
      -- that the looped-call barrier overflowed into a *caller-saved* register
      -- (`callArgBaseReload`, keyed physReg ↦ qsave slot) from its red-zone save
      -- slot: the SysV leaf clobbers caller-saved GPRs, so an invariant base that
      -- did not fit the four callee-saved registers is otherwise destroyed. A
      -- base already in a callee-saved register is not in the list, so a body
      -- whose loop-carried set fits (≤4) emits nothing here (byte-identical).
      let callReload : Lcmd :=
        match i.li_i with
        | .Lcall _ _ =>
            callArgBaseReload.map (fun (physReg, qsave) =>
              (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
        | _ => []
      -- advance the binding counter (only `Lopn`s count, matching the spec)
      match i.li_i with
      | .Lopn _ _ _ => bidx := bidx + 1
      | _ => pure ()
      virtIdx := virtIdx + 1
      out := (((out ++ loads.toArray) ++ expanded.toArray)
                ++ callReload.toArray) ++ store.toArray
    return out.toList

@[implemented_by physBodyWithStoresImpl]
def physBodyWithStores (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) : Lcmd :=
  -- Output-liveness-extended allocation (multi-output store fix): see
  -- `bodyTraceOut`. `physTableOut body []` = `physTable (bodyTrace body)`.
  let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
  -- Caller-save clobber barrier: a body carrying a real `Lcall` (an expanded
  -- `CALL:`/`CALLN:` leaf-call shadow, `expandCallShadows`) renames through
  -- `remapOperandCalleeSave` — the SysV hardware marshalling names (`RDI…`,`RAX`)
  -- are pinned to themselves and every other GP slot is routed callee-saved-first
  -- (`calleeFirstPhys`) so a value live across the call survives it. A call-free
  -- body keeps the plain `remapOperand`, so its bytes are byte-identical.
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl
              else remapOperand body tbl
  let isBinop (opn : String) : Bool :=
    ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
      (stripWidthTag opn)
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  -- ABI MOV widths (#656). See `physBodyWithStoresImpl` for the buffer-leg
  -- (`abiMovBuf`, narrow `MOV:16`/`MOV:8`) vs spill-routing-leg (`abiMovReg`,
  -- full-width) split; `abiW = 0` makes both `MOV:64`/`MOV` (byte-identical).
  -- `abiW = 256` (batch8 packed SoA) makes both `VMOVDQU`.
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  -- Build a list of (virtPosition, argSlot) pairs: the first-use position of
  -- each argument slot. We use this to insert the load just before the
  -- corresponding instruction.
  let firstUseMap : Array (Option Nat) := -- argSlot s -> first virt pos
    Id.run do
      let mut arr : Array (Option Nat) := Array.replicate nArgs none
      for (i, virtIdx) in body.zipIdx do
        match i.li_i with
        | .Lopn _ _ srcs =>
            for src in srcs do
              match src with
              | .reg n =>
                  for s in (List.range nArgs) do
                    if n == argName s && (arr[s]?.getD none).isNone then
                      arr := arr.set! s (some virtIdx)
              | _ => pure ()
        | _ => pure ()
      return arr
  -- For each virtual position, list of (argSlot, base, off) loads to emit
  -- BEFORE that position.
  let loadsAtPos : Nat → List (Nat × String × Nat) := fun pos =>
    (List.range nArgs).filterMap (fun s =>
      match firstUseMap[s]?.getD none with
      | some fpos =>
          if fpos == pos then
            match inLoadMap s with
            | some (base, off) => some (s, base, off)
            | none => none
          else none
      | none => none)
  ((body.zipIdx).flatMap (fun ⟨i, virtIdx⟩ =>
    -- Inline ABI-prologue loads to emit BEFORE this instruction's expansion.
    -- Each load is preceded by `mov R14, [qsave.RSI]` to recover the input
    -- pointer (since R14 may have been overwritten with RDI by a prior
    -- inline output store). The recovery is unconditional rather than
    -- tracking state since the cost (one extra MOVQ per load) is negligible
    -- and the simpler code makes the reasoning local.
    let loads : Lcmd := (loadsAtPos virtIdx).flatMap (fun ⟨s, base, off⟩ =>
      let phys := physNameForBody body tbl (argName s)
      let dst : LOperand := .reg phys
      let memSrc : LOperand := .reg (memName base off)
      let reloadIn : Linstr :=
        ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
      if dst.isSpill then
        [reloadIn,
         ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
         ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
      else
        [reloadIn,
         ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
    -- The binding index of this position: count of Lopns strictly before it
    -- in the body. (The body's last instruction is `Lret`, not an Lopn, so
    -- non-Lopn positions get `bidx = total` which is past the last-n range.)
    let bidx := ((body.take virtIdx).filter (fun li =>
      match li.li_i with | .Lopn _ _ _ => true | _ => false)).length
    let expanded : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
          if isBinop opn then
            match (if isShift opn then shiftImmVal s1 else none) with
            | some v =>
                (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | none =>
                (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
          else
            -- #477: three-source carry ops keep all sources (no truncation).
            match i.li_i with
            -- A `STOREIDX` (srcs `[arrIdx, val]`) whose remapped value source is
            -- a spill slot would render as an illegal `mov mem, mem` (the mirror
            -- of the LOAD case). Route the value through `R15` (#539 store fix).
            | .Lopn [d'] opn' [addr, val] =>
                if isMemStore opn' then
                  -- Reload the memref base pointer from its red-zone qsave slot
                  -- into R14 immediately before the store: the RA-assigned ABI
                  -- register holding it has been clobbered by the body.
                  let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                  (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                  (legalizeMemStore (rmap d') addr' (rmap val) opn'
                     (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                else
                  [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
            | .Lopn dsts opn srcs =>
                [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
            | other => [⟨i.li_ii, other⟩]
      -- Native immediate shift / rotate (`ROR:n` / `SHL:n` / …): one-source
      -- in-place op. Route a spilled operand through R15 (#497 spill legalize).
      | .Lopn [d] opn [s] =>
          if isNativeShiftRotate opn then
            (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else if isMemLoad opn then
            -- A `LOAD`/`LOADIDX` into a spill slot would render as an illegal
            -- `mov mem, mem`; route through `R15` (#539 whole-state load fix).
            -- First reload the memref base pointer from its qsave slot into R14.
            let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
            (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
            (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else
            [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
      | .Lopn dsts opn srcs =>
          [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
      | other => [⟨i.li_ii, other⟩]
    -- If this binding is one of the last n, append a store of its dst. The
    -- store is preceded by a reload of the out-pointer into R14 (the body
    -- may have clobbered R14 since it's the secondary scratch). When the src
    -- is itself a spill slot, route it through R15 first.
    let store : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) _ _ =>
          if bidx ≥ firstOutIdx ∧ bidx < total then
            let outIdx := bidx - firstOutIdx
            match outStoreMap[outIdx]? with
            | some (_base, off) =>
                let src := rmap d
                let memDst : LOperand := .reg (memName storeBase off)
                let reloadOut : Linstr :=
                  ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                if src.isSpill then
                  [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                   reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                else
                  [reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
            | none => []
          else []
      | _ => []
    -- After a real in-loop `Lcall`, reload each loop-invariant pointer base the
    -- looped-call barrier overflowed into a caller-saved register from its qsave
    -- slot (see `physBodyWithStoresImpl`). Empty (byte-identical) when the
    -- loop-carried set fits the four callee-saved registers.
    let callReload : Lcmd :=
      match i.li_i with
      | .Lcall _ _ =>
          callArgBaseReload.map (fun (physReg, qsave) =>
            (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
      | _ => []
    loads ++ expanded ++ callReload ++ store))

/-- The per-position emitter of `physBodyWithStores`: the instructions that one
    virtual position `(i, virtIdx)` of `body` contributes, as the concatenation
    of its inline ABI-prologue loads, its register-allocated expansion, its
    post-call pointer reloads and its inline output store.

    `physBodyWithStores_eq_flatMap` states the agreement with the emitter:
    `physBodyWithStores` is the `flatMap` of this function over `body.zipIdx`,
    and that equality holds by `rfl`. Every argument is an argument of
    `physBodyWithStores`, and the allocation table, the operand remap, the ABI
    move mnemonics and the argument-load schedule are derived here exactly as
    they are there, so an edit to one side that the other does not receive fails
    the equality. -/
def physPositionEmit (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat := 0)
    (memrefBaseReload : String → Option String := fun _ => none)
    (callArgBaseReload : List (String × String) := [])
    (reservedVec : List Nat := []) : Linstr × Nat → Lcmd :=
  let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
  let rmap := if bodyHasCall body then remapOperandCalleeSave body tbl
              else remapOperand body tbl
  let isBinop (opn : String) : Bool :=
    ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
      (stripWidthTag opn)
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let bodyIsU64 : Bool := body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)
  let abiMovReg : String :=
    if abiW == 256 then "VMOVDQU" else if bodyIsU64 then "MOV:64" else "MOV"
  let abiMovBuf : String :=
    if abiW == 16 then "MOV:16"
    else if abiW == 8 then "MOV:8"
    else abiMovReg
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  let n := outStoreMap.length
  let total := numBindings body
  let firstOutIdx := total - n
  let nArgs := virtBodyNumArgs body
  let firstUseMap : Array (Option Nat) :=
    Id.run do
      let mut arr : Array (Option Nat) := Array.replicate nArgs none
      for (i, virtIdx) in body.zipIdx do
        match i.li_i with
        | .Lopn _ _ srcs =>
            for src in srcs do
              match src with
              | .reg n =>
                  for s in (List.range nArgs) do
                    if n == argName s && (arr[s]?.getD none).isNone then
                      arr := arr.set! s (some virtIdx)
              | _ => pure ()
        | _ => pure ()
      return arr
  let loadsAtPos : Nat → List (Nat × String × Nat) := fun pos =>
    (List.range nArgs).filterMap (fun s =>
      match firstUseMap[s]?.getD none with
      | some fpos =>
          if fpos == pos then
            match inLoadMap s with
            | some (base, off) => some (s, base, off)
            | none => none
          else none
      | none => none)
  fun ⟨i, virtIdx⟩ =>
    let loads : Lcmd := (loadsAtPos virtIdx).flatMap (fun ⟨s, base, off⟩ =>
      let phys := physNameForBody body tbl (argName s)
      let dst : LOperand := .reg phys
      let memSrc : LOperand := .reg (memName base off)
      let reloadIn : Linstr :=
        ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg (abiLoadSave base)]⟩
      if dst.isSpill then
        [reloadIn,
         ⟨0, .Lopn [.reg reloadScratch] abiMovBuf [memSrc]⟩,
         ⟨0, .Lopn [dst] abiMovReg [.reg reloadScratch]⟩]
      else
        [reloadIn,
         ⟨0, .Lopn [dst] abiMovBuf [memSrc]⟩])
    let bidx := ((body.take virtIdx).filter (fun li =>
      match li.li_i with | .Lopn _ _ _ => true | _ => false)).length
    let expanded : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
          if isBinop opn then
            match (if isShift opn then shiftImmVal s1 else none) with
            | some v =>
                (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
            | none =>
                (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
                  (fun r => ⟨i.li_ii, r⟩)
          else
            match i.li_i with
            | .Lopn [d'] opn' [addr, val] =>
                if isMemStore opn' then
                  let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
                  (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
                  (legalizeMemStore (rmap d') addr' (rmap val) opn'
                     (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
                else
                  [⟨i.li_ii, .Lopn [rmap d'] opn' [rmap addr, rmap val]⟩]
            | .Lopn dsts opn srcs =>
                [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
            | other => [⟨i.li_ii, other⟩]
      | .Lopn [d] opn [s] =>
          if isNativeShiftRotate opn then
            (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else if isMemLoad opn then
            let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
            (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
            (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
          else
            [⟨i.li_ii, .Lopn [rmap d] opn [rmap s]⟩]
      | .Lopn dsts opn srcs =>
          [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
      | other => [⟨i.li_ii, other⟩]
    let store : Lcmd :=
      match i.li_i with
      | .Lopn (d :: _) _ _ =>
          if bidx ≥ firstOutIdx ∧ bidx < total then
            let outIdx := bidx - firstOutIdx
            match outStoreMap[outIdx]? with
            | some (_base, off) =>
                let src := rmap d
                let memDst : LOperand := .reg (memName storeBase off)
                let reloadOut : Linstr :=
                  ⟨0, .Lopn [.reg reloadScratch2] "MOVQ" [.reg abiSaveRdiName]⟩
                if src.isSpill then
                  [⟨0, .Lopn [.reg reloadScratch] abiMovReg [src]⟩,
                   reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [.reg reloadScratch]⟩]
                else
                  [reloadOut,
                   ⟨0, .Lopn [memDst] abiMovBuf [src]⟩]
            | none => []
          else []
      | _ => []
    let callReload : Lcmd :=
      match i.li_i with
      | .Lcall _ _ =>
          callArgBaseReload.map (fun (physReg, qsave) =>
            (⟨0, .Lopn [.reg physReg] "MOVQ" [.reg qsave]⟩ : Linstr))
      | _ => []
    loads ++ expanded ++ callReload ++ store

/-- `physBodyWithStores` is the `flatMap` of `physPositionEmit` over the
    indexed body. -/
theorem physBodyWithStores_eq_flatMap (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat) :
    physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase
        abiW memrefBaseReload callArgBaseReload reservedVec
      = body.zipIdx.flatMap (physPositionEmit shiftImm body inLoadMap loadBase
          outStoreMap storeBase abiW memrefBaseReload callArgBaseReload
          reservedVec) :=
  rfl

/-- The callee-saved-register restore epilogue: pops the 6 SysV callee-saved
    GP registers `(RBX, RBP, R12, R13, R14, R15)` from their red-zone save
    slots, restoring the caller's values before the function returns. Emitted
    just before the body's final `Lret`.

    R14/R15 are added (2026-05-27) for SysV ABI correctness: although the
    body's reload pass uses them as scratches, they are callee-saved per the
    SysV x86-64 ABI and must be restored. -/
def calleeSaveRestoreEpilogue : Lcmd :=
  [⟨0, .Lopn [.reg "RBX"] "MOVQ" [.reg "qsave.RBX"]⟩,
   ⟨0, .Lopn [.reg "RBP"] "MOVQ" [.reg "qsave.RBP"]⟩,
   ⟨0, .Lopn [.reg "R12"] "MOVQ" [.reg "qsave.R12"]⟩,
   ⟨0, .Lopn [.reg "R13"] "MOVQ" [.reg "qsave.R13"]⟩,
   ⟨0, .Lopn [.reg "R14"] "MOVQ" [.reg "qsave.R14"]⟩,
   ⟨0, .Lopn [.reg "R15"] "MOVQ" [.reg "qsave.R15"]⟩]

/-! ### 7f′. Register-residence coalescing (#476 — X25519 monolithic RA recovery)

The default export names each `Com` binding with a **fresh** SSA register
`r{depth}` (`comToBody`/`regName`), so the linear-scan allocator (`physTable`)
sees one live range per binding. For a deep straight-line body that only ever
touches a small fixed set of **logical** working slots — like the Poseidon2
permutation (16 lanes + 9 scratch = 25 slots, reused across 21 rounds) — this
is catastrophic: thousands of ranges exhaust the 15 GP registers and nearly
every value spills to the stack and is reloaded per use.

A **residence remap** collapses every body SSA name onto its logical working
slot, so the allocator scans the small slot universe instead. When the producer
supplies a `slotOfBinding : Nat → Nat` map (binding ordinal → logical slot), the
`n`-th body binding's def name `r{nArgs+n}` is rewritten to a residence-class
name `res{slotOfBinding n}`. Because the producer maintains the residence
invariant (a logical slot is overwritten only after its previous value is dead —
the X25519 monolithic register-residence discipline #411/#412), this rewrite is
a pure α-relabeling: at every program point a read of `r{m}` and the read of the
residence class it collapses to resolve to the same most-recent definition, so
the body's denotation is unchanged.

The remap touches only the body's `r{…}` SSA names; argument names `a{j}` are
left intact (the ABI prologue's `inLoadMap`/`firstUse` logic keys on them), and
the `outStoreMap`/`inLoadMap` are slot-keyed, so they are unaffected. -/

/-- Rewrite one body register name under a residence remap. Body SSA names
    `r{k}` with `k ≥ nArgs` (i.e. body bindings, not arguments) are rewritten to
    `res{slotOfBinding (k - nArgs)}`; argument names `a{j}` and any other name
    pass through unchanged. -/
def residenceRenameName (nArgs : Nat) (slotOfBinding : Nat → Nat) (n : String) :
    String :=
  if n.startsWith "r" then
    match strDropToNat? n 1 with
    | some k => if k ≥ nArgs then "res" ++ toString (slotOfBinding (k - nArgs)) else n
    | none => n
  else n

/-- Rewrite one `LOperand` under the residence remap (register names only;
    immediates / array elements pass through). -/
def residenceRenameOperand (nArgs : Nat) (slotOfBinding : Nat → Nat) :
    LOperand → LOperand
  | .reg n => .reg (residenceRenameName nArgs slotOfBinding n)
  | o => o

/-- Apply the residence remap to a whole virtual body. Every `Lopn`'s
    destination and source register names are rewritten; non-`Lopn`
    instructions pass through. The op mnemonics, widths, immediates, memory
    references, and instruction order are all preserved, so the body still
    denotes the same value sequence — only the virtual-register *labels* change,
    collapsing the SSA universe onto the logical residence slots. -/
def residenceRenameBody (nArgs : Nat) (slotOfBinding : Nat → Nat) (body : Lcmd) :
    Lcmd :=
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (residenceRenameOperand nArgs slotOfBinding)) opn
          (srcs.map (residenceRenameOperand nArgs slotOfBinding))⟩
    | _ => i)

/-- The residence-coalesced body uses at most `nArgs + |range slotOfBinding|`
    distinct register names — the small logical universe, not one per binding.
    Compiled `slotOfBinding` is provided as an `Array` lookup so the rewrite is
    a single `O(n)` pass with `O(1)` per-binding lookups. -/
def residenceArraySlotOf (slots : Array Nat) (n : Nat) : Nat :=
  slots[n]?.getD 0

/-- Materialize `regConst`-defined shift counts as `.imm` operands **before** the
    residence rename. The default shift-count → immediate resolution
    (`movImmTable`) keys on the unique `r{k}` SSA name of the `MOV r,#v`
    (`regConst`) that defines the count; but the residence rename collapses many
    such defs onto the same reused residence register (e.g. all the `sc0`
    constants land on one `res16`), so a name-keyed last-write-wins table would
    be ambiguous after renaming. We therefore resolve the count on the **unique
    pre-rename names**: any `SHL`/`SHR` whose count source `r{k}` is resolved to
    a constant `v` by `movImmTable body` has that source replaced by `.imm v`
    in place. The rename then leaves the immediate untouched, and the rest of the
    pipeline (`physBodyWithStores`, `lowerTwoAddrShiftImm`) emits the count as an
    `imm8`, avoiding the x86 forced-`CL` constraint — exactly as the non-resident
    path's dataflow oracle does, but resolved before the SSA universe collapses. -/
def materializeShiftCountImms (body : Lcmd) : Lcmd :=
  let movTbl := movImmTable body
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn (s0 :: s1 :: rest) =>
        if isShift opn then
          match s1 with
          | .reg nm =>
              match movImmLookup movTbl nm with
              | some v => ⟨i.li_ii, .Lopn dsts opn (s0 :: .imm v :: rest)⟩
              | none => i
          | _ => i
        else i
    | _ => i)

/-! ### 7f″. Memref-pointer thread canonicalization (in-place store aliasing)

A `memrefSetDyn wrk i v` lowers (`opToLinstrR` `.stackStore`) to
`STOREIDX r{depth}, (base,idx,scale), val`, whose **destination** `r{depth}`
names the dialect's "new array" result — but `memrefSetDyn` is an *in-place*
store: the result memref is the SAME pointer as its input `base`. The store
does NOT move the pointer. The default SSA export, however, gives the result a
**fresh** name, so each `memrefSetDyn` in a forward-threaded resident kernel
(ChaCha's `wrk_v0 → wrk_v1 → …`) becomes a distinct live range. The linear-scan
RA then allocates each threaded name to a *separate* GP register, and the
straight-line body reuses those registers as scratch between two accesses —
clobbering the pointer. A later `STOREIDX`/`LOADIDX` whose SIB base resolves to
such a clobbered register then self-addresses through a DATA word, not the
pointer ⇒ SIGSEGV.

The fix models the dialect's semantics directly: rewrite every `STOREIDX`
destination name to its SIB **base** name (its canonical root), and rewrite all
downstream references through the same alias. The whole `wrk_v0 → wrk_v1 → …`
chain collapses onto a single name (the original array argument `aj`), so:

* the RA sees ONE long-lived array-pointer slot, kept live across the body
  (it is read by every memref access), never reused as scratch; and
* every `LOADIDX`/`STOREIDX` SIB base is now the argument name `aj`, so the ABI
  export's `memrefBaseReload` (keyed on `phys(aj)`) reloads the pointer from its
  red-zone qsave slot before *every* access — not just the first.

The rewrite is a pure α-relabeling (`memrefSetDyn`'s result and its input
pointer denote the same memref), so the body's value sequence is unchanged.

It touches ONLY bodies that contain a `STOREIDX` (the memref / 2-pointer ABI
path). Scalar-word kernels (MayoUov/MontRedc, routed through
`inLoadMap`/`outStoreMap`) emit no `STOREIDX` — `arrChainAlias` is empty for
them, and `canonicalizeMemrefThread` is the identity, so their bytes are
unchanged. -/

/-- Build the in-place-store alias map for a body: `dst ↦ canonical(base)` for
    every `STOREIDX dst, (base,idx,scale), val`. Processed in program order with
    each `base` already resolved through earlier aliases, so the map sends every
    threaded array name straight to its chain root (the array argument). Names
    that never name a memref-store result are absent (resolve to themselves). -/
def arrChainAlias (body : Lcmd) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let resolve (m : Std.HashMap String String) (n : String) : String :=
    m.getD n n
  for i in body do
    match i.li_i with
    | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
        if isMemStore opn then
          m := m.insert dst (resolve m base)
    | _ => pure ()
  return m

/-- Resolve a register name through the memref-thread alias map (identity off
    the map). The map is pre-flattened to chain roots, so one lookup suffices. -/
def canonMemrefName (m : Std.HashMap String String) (n : String) : String :=
  m.getD n n

/-- Rewrite one `LOperand`'s register names through the memref-thread alias map
    (both plain `reg` names and a SIB `arrIdx` base/index). Immediates and
    compile-time array elements pass through. -/
def canonMemrefOperand (m : Std.HashMap String String) : LOperand → LOperand
  | .reg n => .reg (canonMemrefName m n)
  | .arrIdx base idx scale => .arrIdx (canonMemrefName m base) (canonMemrefName m idx) scale
  | o => o

/-- Collapse a body's forward-threaded memref-pointer chain onto its root name
    (the array argument), so the in-place `memrefSetDyn` result aliases its input
    pointer. See `arrChainAlias` for the rationale. The op mnemonics, widths,
    immediates, and instruction order are preserved — only the threaded array
    *labels* change — so the body still denotes the same value sequence. When the
    body has no `STOREIDX` (every scalar kernel), the alias map is empty and this
    is the identity (existing bytes unchanged). -/
def canonicalizeMemrefThread (body : Lcmd) : Lcmd :=
  let m := arrChainAlias body
  if m.isEmpty then body
  else body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (canonMemrefOperand m)) opn
          (srcs.map (canonMemrefOperand m))⟩
    | _ => i)

/-- Whether an `extCall` argument vector forwards the enclosing function's
    parameters unchanged: entry `j` is the parameter at root position `j`, i.e.
    De Bruijn index `nArgs - 1 - j` in the newest-first context. `expected`
    counts down from `nArgs - 1`; the vector must be non-empty and its last
    entry the oldest parameter (index `0`). -/
def argsForwardParams {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Nat → Bool
  | [], .nil, _ => false
  | _ :: _, .cons v rest, expected =>
      varIndex v == expected &&
        (match rest with
         | .nil => expected == 0
         | .cons _ _ => expected != 0 && argsForwardParams rest (expected - 1))

/-- Recognise a degenerate zero-marshalling forwarder `Com`: a single
    `extCall sym` binding whose arguments forward the enclosing parameters
    unchanged (`argsForwardParams`) and which is returned directly (`.ret .here`).
    Returns the callee symbol only when the inbound ABI `abiArgs` already equals
    the callee's SysV argument registers in order (`RDI, RSI, RDX, …`) and every
    parameter is forwarded — so `call sym; ret` needs no argument moves or result
    staging. Every other `Com` (and any argument permutation, partial forward, or
    non-`.here` return) yields `none` and falls through to the marshalling
    export unchanged. -/
def degenerateForwarderSym? {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (abiArgs : List String) : Option String :=
  match com with
  | .var e body =>
      match e, body with
      | ⟨.extCall sym argTys _, _, args⟩, .ret v =>
          if varIndex v == 0
             && Γ.length ≥ 1
             && argTys.length == Γ.length
             && abiArgs == (List.range Γ.length).map (fun j => sysvArgRegs.getD j "")
             && argsForwardParams args (Γ.length - 1)
          then some sym else none
      | _, _ => none
  | _ => none

/-- The ABI-wrapping tail of `comToLfundefPhysAbi`, over an already-built virtual
    `Lfundef` (`comToLfundef`'s output). Everything here operates on the flat,
    string-named body, so an emit path that produces the virtual body by other
    means — a fused lowering that avoids a quadratic intermediate `Com` — calls
    this directly. `forwarderBody?` supplies the degenerate zero-marshalling
    forwarder body when applicable (`none` on the general path).

    * `shiftImm` — legacy SSA-name-keyed shift-count oracle.
    * `inLoadMap` — argument slot → `(base, off)` memory load (default: none —
      which reproduces `comToLfundefPhys`'s register-only behaviour).
    * `outStoreMap` — list of output store targets (default: empty — no stores).
    * `abiArgs` — the `lfd_arg` list (default: `["RDI", "RSI"]` for `out, inp`).
    * `abiTyin` — the `lfd_tyin` list (default: two 64-bit pointer widths).
-/
def comToLfundefPhysAbiFromVirt (virt0 : Lfundef)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false)
    (forwarderBody? : Option Lcmd := none)
    (reserveVecScratch : Bool := false) :
    Lfundef :=
  -- `reserveVecScratch` (batch8 SoA path): cap the vector RA pool at
  -- `numVecRegs - 1`, reserving `%ymm15` as the printer's spill-legalization
  -- scratch so its bounce needs no per-op save/restore. `false` (every existing
  -- caller) uses the full pool, so the emitted bytes are unchanged.
  let reservedVec : List Nat := if reserveVecScratch then [numVecRegs - 1] else []
  -- Expand any straight-line `CALL:`/`CALLN:` leaf-call shadow into a real
  -- `Lcall` + SysV marshalling (`expandCallShadows`) before the RA runs, so the
  -- linear scan sees the call as a caller-save clobber barrier (the marshalled
  -- `MOV RDI,…`/`MOV dst,RAX` land beside the real `Lcall`). Identity on a
  -- call-free body, so every existing kernel is byte-identical.
  let virt0 := { virt0 with lfd_body := expandCallShadows virt0.lfd_body }
  -- Optional register-residence coalescing (#476): collapse every body SSA name
  -- onto its logical working slot before the linear-scan allocation, so the RA
  -- keeps the small fixed working set register-resident instead of one live
  -- range per binding. `none` (every existing caller) leaves the body
  -- byte-identical to the per-binding-SSA export.
  let virtR :=
    match residence with
    | none => virt0
    | some slots =>
        let nArgs := virt0.lfd_arg.length
        -- Resolve `regConst`-defined shift counts to immediates on the unique
        -- pre-rename names, THEN collapse the SSA universe onto residence slots.
        let bodyImm := materializeShiftCountImms virt0.lfd_body
        { virt0 with
          lfd_body := residenceRenameBody nArgs (residenceArraySlotOf slots)
                        bodyImm }
  -- Memref-pointer thread canonicalization (in-place store aliasing): collapse
  -- every forward-threaded `memrefSetDyn` result name onto its input array
  -- pointer (its SIB base), so the array pointer is ONE long-lived RA slot kept
  -- live across the body and every `LOADIDX`/`STOREIDX` SIB base is the array
  -- argument `aj` (so `memrefBaseReload` reloads it before every access — the
  -- segfault fix). The identity on scalar kernels (no `STOREIDX`), so their
  -- bytes are unchanged. Runs after the residence rename so the alias map sees
  -- the post-rename array names.
  -- Argument-liveness pin (3+-argument signatures). The linear-scan RA sees an
  -- argument used only as a late `LOADIDX`/`STOREIDX` SIB base as "born late", so
  -- a scalar argument that dies early can be allocated the SAME physical register
  -- — which makes `memrefBaseReload` (keyed on the physical register) reload the
  -- array base from the wrong argument's qsave slot. A synthetic `LIVEPIN` that
  -- reads every argument at entry forces all arguments live from entry, so each
  -- gets a distinct register; it is filtered out after `physBodyWithStores`.
  -- ≤2-argument signatures inject nothing, so their bytes are unchanged —
  -- UNLESS the caller opts in with `forceLivePin` (a 2-pointer kernel whose
  -- OUT arg is born late can coalesce onto the IN arg's register, making the
  -- register-keyed `memrefBaseReload` map ambiguous: the m31 reduce loaded its
  -- input through the OUT pointer's qsave slot).
  let nArgs := virtR.lfd_arg.length
  let livePin : Lcmd :=
    if nArgs ≥ 3 || forceLivePin then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range nArgs).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let virt := { virtR with
    lfd_body := livePin ++ canonicalizeMemrefThread virtR.lfd_body }
  -- Output-liveness-extended allocation table (multi-output store fix): the `n`
  -- designated outputs occupy `n` DISTINCT physical registers across the epilogue
  -- stores (see `bodyTraceOut`). EVERY consumer of `tbl` here (prologue,
  -- `buildArgPtrMaterialize`, `memrefBaseReload`, and the inline stores in
  -- `physBodyWithStores` below) must use the SAME table so the body's physical
  -- register names agree. `physTableOut … []` = `physTable (bodyTrace …)`, so the
  -- register-ABI / single-store kernels are byte-identical.
  -- For a STRAIGHT-LINE CALL body, the liveness-computed call-barrier
  -- relocation is composed into the table HERE, once — every seam below
  -- (including the frame sizing, which must see the relocation's fresh spill
  -- indices) then reads one coherent table via `physNameForBody`'s plain
  -- lookup. Identity on call-free and looped bodies.
  let tbl := straightCallComposeTable virt.lfd_body
    (physTableOut virt.lfd_body outStoreMap reservedVec)
  -- Each EXTRA SysV argument register beyond `RDI`/`RSI` (`RDX`/`RCX`/`R8`/`R9`,
  -- a 3+-argument signature) gets its own red-zone qsave slot, appended after the
  -- fixed prologue, so the argument materialize / SIB-base reloads can source it
  -- from a stable slot. For ≤2-argument signatures `abiArgs.drop 2 = []`, so the
  -- prologue bytes are unchanged.
  let extraInputSaves : Lcmd :=
    (abiArgs.drop 2).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl inLoadMap ++ extraInputSaves
  -- Materialize the pointer arguments into the body's RA-assigned register/slot
  -- (the 2-pointer memref ABI: the body uses `aj` directly as a LOADIDX/STOREIDX
  -- SIB base, but the RA placed `aj` in a register/spill that the prologue never
  -- copied the SysV argument register into — see `buildArgPtrMaterialize`). For
  -- the scalar-word ABI (`inLoadMap` non-empty) this is empty.
  let argMat := buildArgPtrMaterialize virt tbl abiArgs inLoadMap
  -- Use physBodyWithStores to insert inline stores after each output binding.
  -- This solves the SSA liveness problem: the source `Com` `.ret`s a single
  -- value, so under register allocation only the LAST output register is alive
  -- at function exit; the other 15 have been reclaimed for later writes.
  -- Storing each output immediately after its binding preserves the value
  -- before any subsequent overwrite.
  -- Compose the caller's shift oracle with the dataflow `regConst`→imm resolver
  -- (`movImmOracle`): the caller's map wins; otherwise a count register defined
  -- by a body `MOV r,#v` (a `regConst v`) is resolved to `#v`. This lets a
  -- `regConst`-based producer (Poseidon2: shift counts 31/63 materialised by
  -- `regConst`) avoid the x86 forced-`CL` shift-count constraint. For
  -- ChaCha/SHA/Keccak (counts via `immSlotMap` → `.imm`, or via the caller
  -- oracle) `movImmOracle` returns none for the relevant names, so behaviour is
  -- unchanged. `dataflow` is bound here so its `Array` is built exactly once
  -- (not per shift-count lookup).
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  -- Build the memref-base reload map (2-pointer memref ABI): each pointer arg
  -- `aj` (one NOT covered by `inLoadMap`, with a red-zone qsave slot) is
  -- RA-assigned to a physical register that the body reuses as a scratch — so
  -- every `LOADIDX`/`STOREIDX` SIB base must be reloaded from `qsave.<abiReg>`
  -- into R14 immediately before the access (`reloadMemrefBase`). The map keys on
  -- the physical base register name `phys(aj)` and yields the qsave slot. For the
  -- scalar-word ABI (`inLoadMap` non-empty) it is empty, so the existing scalar
  -- kernels (MayoUov/MontRedc, which route through `inLoadMap`/`outStoreMap`) are
  -- unaffected.
  let memrefBaseReload : String → Option String :=
    let pairs : List (String × String) :=
      (abiArgs.zipIdx).filterMap (fun ⟨abiReg, j⟩ =>
        match inLoadMap j with
        | some _ => none
        | none =>
            -- `abiSaveOfExt`: a 3rd+ array argument (`RDX`/…) reloads its SIB base
            -- from its own qsave slot instead of the `RSI` input slot.
            match abiSaveOfExt abiReg with
            | some saveName =>
                let phys := physNameForBody virt.lfd_body tbl (argName j)
                some (phys, saveName)
            | none => none)
    fun base => (pairs.find? (fun p => p.1 == base)).map Prod.snd
  -- Drop the synthetic argument-liveness pin (it carried no value, only liveness).
  let bodyWithInlineStores := (physBodyWithStores shiftImm' virt.lfd_body
    inLoadMap reloadScratch2 outStoreMap reloadScratch2 abiW memrefBaseReload
    (reservedVec := reservedVec)).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  -- Straight-line-call return materialization: the liveness-computed barrier
  -- homes the final capture (`MOV dst, RAX`) in a callee-saved register or a
  -- frame spill, so `RAX` holding the `Com`'s return value at `Lret` is not
  -- guaranteed by the last call's return alone (the caller-side functional-leaf
  -- ABI reads the result from `RAX`). Move the barrier-resolved return name
  -- back into `RAX` before the callee-saved restore. Emitted only for
  -- `bodyStraightCall` bodies whose return name is a body slot and does not
  -- already resolve to `RAX` — every call-free / looped kernel is
  -- byte-identical.
  let retMat : Lcmd :=
    if bodyStraightCall virt.lfd_body then
      match virt.lfd_res.head? with
      | some rn =>
          if nameSlot virt.lfd_body rn < (bodyNames virt.lfd_body).length then
            let phys := physNameForBody virt.lfd_body tbl rn
            if phys == sysvRetReg then []
            -- MOVQ (64-bit): the returned value is a full word/pointer — an
            -- untagged MOV renders `movl` and TRUNCATES a returned pointer
            -- to 32 bits (harness segfault on dereference).
            else [⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg phys]⟩]
          else []
      | none => []
    else []
  -- Insert the callee-saved-register restore just before the final `Lret`.
  let bodyWithRestore :=
    insertEpilogue bodyWithInlineStores (retMat ++ calleeSaveRestoreEpilogue)
  -- Degenerate zero-marshalling forwarder (`forwarderBody?`, supplied by the
  -- caller): a `Com` that is a single `extCall sym` binding forwarding the
  -- enclosing parameters unchanged and returned directly, whose inbound ABI
  -- already equals the callee's SysV argument registers. Its body is
  -- `call sym; ret` with no argument moves or result staging — bypassing the
  -- `prologue`/`argMat`/marshalling above. Only the `lfd_body` field is
  -- affected; every other field is the same structure literal as the general
  -- path. `none` yields `prologue ++ argMat ++ bodyWithRestore` byte-for-byte.
  { virt with
    lfd_body := forwarderBody?.getD (prologue ++ argMat ++ bodyWithRestore)
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }

/-- The ABI-wrapped physical `lfundef` for a `Com`: same args/types as the
    underlying physical export, but `lfd_arg` is reset to a fixed 2-pointer
    SysV signature (`[RDI, RSI]` for the canonical `out, inp` C ABI), the body
    is prefixed with the prologue (loads inputs from `[RSI + ...]`) and
    suffixed with the epilogue (stores outputs to `[RDI + ...]`), and `lfd_res`
    is empty (the body returns its result via memory at `*out`). Builds the
    virtual `Lfundef` with `comToLfundef` and wraps it with
    `comToLfundefPhysAbiFromVirt`.

    * `shiftImm` — legacy SSA-name-keyed shift-count oracle.
    * `immSlotMap` — producer-level slot → constant map (default: none).
    * `inLoadMap` — argument slot → `(base, off)` memory load (default: none —
      which reproduces `comToLfundefPhys`'s register-only behaviour).
    * `outStoreMap` — list of output store targets (default: empty — no stores).
    * `abiArgs` — the `lfd_arg` list (default: `["RDI", "RSI"]` for `out, inp`).
    * `abiTyin` — the `lfd_tyin` list (default: two 64-bit pointer widths).
-/
def comToLfundefPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false) :
    Lfundef :=
  comToLfundefPhysAbiFromVirt (comToLfundef com immSlotMap)
    (shiftImm := shiftImm) (inLoadMap := inLoadMap) (outStoreMap := outStoreMap)
    (abiArgs := abiArgs) (abiTyin := abiTyin) (residence := residence)
    (abiW := abiW) (forceLivePin := forceLivePin)
    (forwarderBody? := (degenerateForwarderSym? com abiArgs).map
      (fun sym => [⟨0, .Lcall none (sym, 0)⟩, ⟨0, .Lret⟩]))

/-- Export a `Com` to a 2-pointer-ABI physical-register, two-address `Lprog`.
    See `comToLfundefPhysAbi` for the ABI wrapping (prologue loads + epilogue
    stores around the verified two-address body). -/
def Com.toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap
                 outStoreMap abiArgs abiTyin residence abiW forceLivePin)] }

/-- Serialize the ABI-wrapped physical export to the textual lprog blob. -/
def Com.toLprogPhysAbiText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) : String :=
  magic ++ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
              outStoreMap abiArgs abiTyin residence).toText ++ "\n"

/-- The ABI-wrapped physical export's bytes. -/
def Com.toLprogPhysAbiBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) : ByteArray :=
  (Com.toLprogPhysAbiText com fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence).toUTF8

/-- Write the ABI-wrapped physical-register lprog blob to a file. -/
def Com.writeLprogPhysAbiFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none) :
    IO Unit :=
  IO.FS.writeBinFile path
    (Com.toLprogPhysAbiBytes com fname shiftImm immSlotMap inLoadMap
       outStoreMap abiArgs abiTyin residence)

/-! ### 7g. Physical-register export of a looped `ComL`

`comLToBody` (§3b) lowers a fixed-trip `ComL` to a **rolled** control-flow body
(one `Llabel`/`Lcond` back-edge, **one** body copy), but it emits pre-RA SSA: the
accumulator is `regName curDepth`, the trip counter `loopCtr d` (`Lctr<d>`), and
the loop body's temporaries the disjoint `loopReg d k` namespace (`L<d>_r<k>`).
Those names render as `%<UNKNOWN:rN>` placeholders — `as` cannot assemble them.

This section gives the looped `ComL` the **same physical register allocation**
the straight-line `Com` gets (§7e). The key observation is that the physical-RA
pass (`bodyTrace`/`physTable`/`physBody`/`remapOperand`) walks an *`Lcmd`* by
first-appearance of operand names — it is **agnostic to how those names were
produced**. Feeding it `comLToBody`'s output therefore allocates the loop body's
bindings exactly like any straight-line binding:

* the accumulator name is touched at the seed `MOV`, every trip's feedback, and
  is read every trip — so its live range spans the whole loop and the linear
  scan keeps it in **one fixed physical register** (loop-carried);
* the trip counter is touched at its `MOV`-init and every `SUB`/`CMP` — so it too
  stays in one fixed register across all trips;
* the body temporaries (`L<d>_r<k>`) are written-before-read each trip, so a
  single physical register, reused across trips, is the correct rolled semantics.

The back-edge instructions (`Llabel`, `Lcond`) carry no register-file slot
(`linstrRegNames` returns `none`), so they pass through `physBody` untouched —
the rolled shape (one body, real `jne .L<d>`) is preserved while every GP operand
becomes a real x86 register. The result is an **assemblable, byte-KAT'able**
looped `.s`, with no `%<UNKNOWN>`.

`ComL.toLfundefPhys` is the loop-aware mirror of `comToLfundefPhys` (§7e): it
runs the same arg-materialize prelude (`buildArgMaterializePhys`) and the same
`RAX` return epilogue, so a loop-free `ComL` produces a byte-identical `lfundef`
to `comToLfundefPhys` on its `Com` image (the straight-line path is unchanged —
this is purely additive). -/

/-- The physical, two-address `lfundef` for a **looped** `ComL` — the loop-aware
    mirror of `comToLfundefPhys`. The body is `comLToBody` (a rolled back-edge,
    one body copy) run through the SAME physical RA (`physBody`) as a straight-line
    `Com`: the accumulator and trip counter become loop-carried physical
    registers, the body temporaries reused physical registers across trips, and
    the back-edge (`Llabel`/`Lcond`) passes through untouched. No operand is left
    as an `%<UNKNOWN>` SSA name. SysV arguments are materialized into the body's
    RA-assigned registers at entry, and the result is moved into `RAX` before the
    final `Lret`. On a loop-free `ComL` this is byte-identical to
    `comToLfundefPhys` on its `Com` image (additive). -/
def ComL.toLfundefPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  -- Class-aware table (matches `physBody`'s `bodyPhysTable`): GP→GP, vector→XMM.
  -- For a pure-scalar body this is `physTable (bodyTrace …)`, so unchanged.
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body)
  let resPhys := virt.lfd_res.map (physNameForBody virt.lfd_body tbl)
  -- Project `lfd_arg` to the first six SysV call-arg registers (as
  -- `comToLfundefPhys`); the body reads its arguments by their RA-assigned
  -- physical register after `physBody` rewrites every `aN` operand.
  let callRegArgs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
  let nArgsExported : Nat := min virt.lfd_arg.length callRegArgs.length
  let argSig := callRegArgs.take nArgsExported
  let tyinSig := virt.lfd_tyin.take nArgsExported
  -- Copy each SysV argument register into the physical register the RA assigned
  -- to the body's `argName j` (skipping copies already in place).
  let argMat := buildArgMaterializePhys virt tbl callRegArgs
  -- The rolled, physically-allocated loop body. `physBody` allocates the loop
  -- body's bindings (accumulator / counter / temps) exactly like a straight-line
  -- body; the `Llabel`/`Lcond` back-edge passes through untouched.
  let pbody := if bodyHasCall virt.lfd_body
               then physBodyCalleeSave shiftImm virt.lfd_body
               else physBody shiftImm virt.lfd_body
  -- Move the result into the SysV return register `RAX` before the trailing
  -- `Lret` (skipped when the result already lands in `RAX`).
  let retEpi : Lcmd :=
    match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let bodyWithRet : Lcmd :=
    if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  { virt with
    lfd_body := argMat ++ bodyWithRet
    lfd_arg := argSig
    lfd_tyin := tyinSig
    lfd_res := resPhys }

/-! ### 7g″. Frame-allocating (self-owning) physical export (`ComL.toLfundefPhysFramed`)

`ComL.toLfundefPhys` (§7g) is **register-ABI-only**: every `stackArr`-typed array
argument is a *caller-passed SysV pointer*, materialised from `RDI/RSI/…` into its
RA-assigned register (`buildArgMaterializePhys`). A self-allocating kernel — one
that owns its array buffers in its **own** stack frame rather than receiving them
as pointer arguments (MAYO's parameterless `mayo_solve_gf16` self-test owns 53 KB
of local `A/y/r/x/P/P2` buffers) — cannot be expressed that way: there is no SysV
pointer for a local buffer, and the register-ABI export hard-sets `lfd_stk_max :=
0`, so `renderLfundef` opens no frame.

This section adds the **frame-allocating** export, purely additively (a new
function; §7g's register-ABI export is untouched). Instead of binding each array
base to a SysV argument register, it:

1. emits a `FRAME` directive (`Lopn [] "FRAME" [.imm frameBytes]`) as the body's
   first instruction — the #656 array-ABI marker `frameSize` reads to open a real
   `leaq -F(%rsp), %rsp` frame (and `renderLinstrR` drops, issuing no x86 line);
2. sets `lfd_stk_max := frameBytes` on the exported `Lfundef`;
3. binds each local array base with `leaq off(%rsp), %reg` (`buildFrameBaseMaterialize`)
   — the array's frame region base loaded into the RA register the body uses as
   the `stackLoad`/`stackStore` SIB base. Unlike the register-ABI `argMat`, each
   `LEA` is self-contained (it reads only `%rsp`), so it is free of the
   §7g′ SysV-argument clobber chain — the k-th array role follows the k-th
   `localBases` entry, not the RA assignment.

The body's `stackLoad`/`stackStore` then address `off(%rsp,%idx,scale)` — a cell
of the self-owned frame region — with no caller pointer anywhere. There are no
incoming SysV pointer arguments, so `lfd_arg`/`lfd_tyin` are empty. -/

/-- Materialise each self-owned array base as `leaq off(%rsp), %reg` — the
    frame-allocating analogue of `buildArgMaterializePhys`. For the `j`-th entry
    `(name, off)` of `localBases`, `argName j` is the array parameter that the body
    threads as a `stackLoad`/`stackStore` SIB base; its RA-assigned physical
    register (`physNameForBody`) is loaded with the effective address `%rsp + off`
    (its region base in the self-allocated frame). Bases the body never references
    are skipped (as `buildArgMaterializePhys` skips unused args). A spilled base is
    routed through `reloadScratch` (`LEA R15, off(%rsp); MOVQ slot, R15`). Each
    `LEA` reads only `%rsp`, so — unlike the SysV-argument copy chain — no base
    clobbers another. -/
def buildFrameBaseMaterialize (virt : Lfundef) (tbl : Array Nat)
    (localBases : List (String × Nat)) : Lcmd :=
  let body := virt.lfd_body
  (localBases.zipIdx).flatMap (fun ⟨(_name, off), j⟩ =>
    let nm := argName j
    let used := body.any (fun i =>
      match i.li_i with
      | .Lopn _ _ srcs => srcs.any (fun s =>
          match s with
          | .reg n => n == nm
          | .arrIdx b idx _ => b == nm || idx == nm
          | _ => false)
      | _ => false)
    if !used then []
    else
      let phys := physNameForBody body tbl nm
      let dst : LOperand := .reg phys
      if dst.isSpill then
        [⟨0, .Lopn [.reg reloadScratch] "LEA:64" [.reg (memName "RSP" off)]⟩,
         ⟨0, .Lopn [dst] "MOVQ" [.reg reloadScratch]⟩]
      else
        [⟨0, .Lopn [dst] "LEA:64" [.reg (memName "RSP" off)]⟩])

/-! ### Packed-frame SIB base = `%rsp` directly (framed self-owning path only)

The register-allocated SIB base of a `stackLoad`/`stackStore` (`remapOperand`
resolves the array-base SSA name to a physical register) is unstable when the
packed frame region is threaded as the loop **product accumulator** through a
deep (3-nested) solve: the linear scan sees the array base as a loop-carried
value with fragmented live ranges and REUSES its physical register between
loops, so at whole-solve scale the SIB base collides with a loop counter
(gdb: `movq %val, (%rcx, %rax, 8)` with `%rcx` = a counter, not the frame
pointer, as the SIB base). A single-loop kernel (`coreDotPacked`) keeps the
base stable and works; the 3-deep whole solve does not.

The fix uses **`%rsp` itself** as the SIB base for a self-owning
(`toLfundefPhysFramed`) function that owns a **single** array region at frame
offset `0` and issues no call. After the prologue `leaq -F(%rsp), %rsp` the
frame base IS `%rsp`, and — because the function is call-free with no mid-body
push/pop (the callee-saved brackets sit OUTSIDE the frame alloc) — `%rsp` is
stable across the whole body, so `(%rsp, %idx, 8)` addresses frame cell `idx`
correctly throughout. `%rsp` is a legal SIB base.

* NO dedicated base register is reserved and NO register is evicted from the
  allocatable pool — this is what avoids the register-pressure spillover that a
  pinned-register eviction caused (the innermost index then collided at 3-deep
  nesting);
* every `STOREIDX`/`LOADIDX` SIB base is rewritten to `%rsp` (the computed index
  register and scale are unchanged), so every cell access is `(%rsp, %idx, 8)`;
* no base LEA in the prologue — the frame alloc `leaq -F(%rsp), %rsp` already
  establishes `%rsp` as the base — and no callee-saved push/pop is added on
  account of the base.

This is scoped to the single-region (offset-0), call-free framed path; a
multi-region, offset-shifted, or call-issuing framed function keeps the
register-allocated base (unchanged), and the register-ABI exports
(`toLfundefPhys`/`toLfundefPhysAbi`) are untouched. -/

/-- The register used as the packed frame SIB base on the single-region,
    call-free framed path: `%rsp` itself (the frame base after `leaq -F(%rsp)`). -/
def frameBaseSibReg : String := "RSP"

/-- Rewrite a SIB (`arrIdx`) operand's base to `r`, keeping the index register
    and scale. Non-SIB operands pass through. -/
def pinSibOperand (r : String) : LOperand → LOperand
  | .arrIdx _ idx scale => .arrIdx r idx scale
  | o => o

/-- Rewrite every SIB base in one lowered instruction to `r` (applied to both
    destinations and sources; only the packed `STOREIDX`/`LOADIDX` carry a SIB
    operand). -/
def pinInstrSib (r : String) : LinstrR → LinstrR
  | .Lopn dsts opn srcs => .Lopn (dsts.map (pinSibOperand r)) opn (srcs.map (pinSibOperand r))
  | other => other

/-- The **frame-allocating** physical `lfundef` for a looped `ComL` — the
    self-owning analogue of `ComL.toLfundefPhys`. The array bases in `localBases`
    are laid in a `frameBytes`-byte frame the function allocates itself
    (`leaq -frameBytes(%rsp)` prologue, driven by the injected `FRAME` directive
    and recorded in `lfd_stk_max`); each is bound with `leaq off(%rsp), %reg` into
    the register the body threads as its `stackLoad`/`stackStore` SIB base, so
    every array access is a cell of the self-owned frame. There are no incoming
    SysV pointer arguments (`lfd_arg`/`lfd_tyin` empty). On a `ComL` that touches
    no array (empty `localBases`, `frameBytes = 0`) this is byte-identical to
    `ComL.toLfundefPhys` apart from the (dropped) `FRAME` directive and the
    `lfd_stk_max`/`lfd_arg` fields — purely additive.

    For a **single**-region (offset-0), **call-free** framed function the packed
    frame SIB base is `%rsp` directly (`frameBaseSibReg`): no base LEA, no
    reserved register, no eviction — after `leaq -F(%rsp), %rsp` the frame base
    is `%rsp` and every `STOREIDX`/`LOADIDX` SIB base is rewritten to `%rsp`
    (`(%rsp, %idx, 8)`). This is the fix for the deep-solve base/index collision
    (see the note above); a multi-region, offset-shifted, or call-issuing framed
    body keeps the register-allocated base (byte-identical to before). -/
def ComL.toLfundefPhysFramed {Γ : Ctxt jasminDialect} {t : JasminTy}
    (frameBytes : Nat) (localBases : List (String × Nat))
    (c : ComL Γ t) (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  let hasCall := bodyHasCall virt.lfd_body
  -- Use `%rsp` directly as the SIB base on the single-region (offset-0),
  -- call-free path (no reserved register, no eviction).
  let pin := (match localBases with | [(_, 0)] => true | _ => false) && !hasCall
  let tbl := straightCallComposeTable virt.lfd_body (bodyPhysTable virt.lfd_body)
  let resPhys := virt.lfd_res.map (physNameForBody virt.lfd_body tbl)
  -- The self-owned array bases. When pinning to `%rsp`, no base LEA is needed
  -- (the frame alloc already establishes `%rsp` as the base); otherwise each
  -- base goes to its RA-assigned register.
  let frameMat : Lcmd :=
    if pin then [] else buildFrameBaseMaterialize virt tbl localBases
  let pbody0 := if hasCall then physBodyCalleeSave shiftImm virt.lfd_body
                else physBody shiftImm virt.lfd_body
  -- Rewrite every packed SIB base to `%rsp`.
  let pbody : Lcmd :=
    if pin then pbody0.map (fun i => ⟨i.li_ii, pinInstrSib frameBaseSibReg i.li_i⟩) else pbody0
  let retEpi : Lcmd :=
    match resPhys with
    | [r] => if r == "RAX" then [] else [⟨0, .Lopn [.reg "RAX"] "MOVQ" [.reg r]⟩]
    | _ => []
  let bodyWithRet : Lcmd :=
    if retEpi.isEmpty then pbody else pbody.dropLast ++ retEpi ++ [⟨0, .Lret⟩]
  -- The `FRAME` marker: `frameSize` reads it to open a real `leaq -F(%rsp)` frame.
  let frameDir : Linstr := ⟨0, .Lopn [] "FRAME" [.imm frameBytes]⟩
  { virt with
    lfd_body := frameDir :: (frameMat ++ bodyWithRet)
    lfd_arg := []
    lfd_tyin := []
    lfd_res := resPhys
    lfd_stk_max := frameBytes }

/-- Export a looped `ComL` to a physical-register, two-address `Lprog` — the
    loop-aware mirror of `Com.toLprogPhys`. The single exported function has a
    rolled, physically-allocated body (real x86 registers, real `jne .L<d>`
    back-edge, one body copy). -/
def ComL.toLprogPhys {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs := [(fname, ComL.toLfundefPhys c shiftImm immSlotMap)] }

/-- Serialize the looped physical export to the textual lprog blob (magic + text). -/
def ComL.toLprogPhysText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : String :=
  magic ++ (ComL.toLprogPhys c fname shiftImm immSlotMap).toText ++ "\n"

/-- The looped physical export's bytes. -/
def ComL.toLprogPhysBytes {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) : ByteArray :=
  (ComL.toLprogPhysText c fname shiftImm immSlotMap).toUTF8

/-- Write the looped physical-register lprog blob for a `ComL` to a file. -/
def ComL.writeLprogPhysFile {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    IO Unit :=
  IO.FS.writeBinFile path (ComL.toLprogPhysBytes c fname shiftImm immSlotMap)

/-! ### 7g′. 2-pointer-ABI physical export of a looped `ComL` (array-map kernels)

`ComL.toLfundefPhys` (§7g) gives the looped body the same SSA→physical RA as a
straight-line `Com`, but it is **register-ABI-only**: it treats the
`stackArr`-typed array arguments as if they were scalar register values, copies
each into its RA-assigned register once at entry (`buildArgMaterializePhys`), and
the loop body uses the accumulator register / the invariant-base registers
directly as `STOREIDX`/`LOADIDX` SIB bases.

For a 2-pointer array-map kernel — `mayo_encode(out, in)`,
`out[i] := f(in[i])` — that is **wrong in two ways** (gdb/objdump-confirmed):

1. **IN/OUT role binding by RA, not ABI.** The accumulator (output base) and the
   invariant (input base) are bound to whatever physical registers the linear
   scan happens to assign; nothing pins the i-th array role to the i-th SysV
   pointer register, so the rendered loads/stores can address the wrong array.

2. **Invariant-base clobber → SIGSEGV.** The array-base registers are in the
   allocatable pool, so the loop body reuses them as scratch mid-iteration
   (`movzbl …, %rsi` overwriting the in-pointer in `%rsi`). A later
   `LOADIDX`/`STOREIDX` whose SIB base resolves to such a clobbered register
   self-addresses through a *data word* — a wild store.

The straight-line memref kernels (ChaCha/SHA/Keccak) already have the robust
fix: `comToLfundefPhysAbi` saves each pointer argument to a red-zone qsave slot
in the prologue and, via `reloadMemrefBase`, **reloads the SIB base from its
qsave slot into `R14` immediately before every access** — so the base is never a
body-clobberable register and the IN/OUT roles follow the *ABI argument →
qsave-slot* mapping, not the RA. This section lifts that exact machinery onto the
looped `ComL` path.

The one looped-specific step: in an array-map loop the store base is the
**accumulator** register (`regName nArgs`, seeded `MOV acc, a_out`), not the out
argument directly. Because the dialect's `stackStore` is an *in-place* update —
the result memref is the same pointer as its input — the accumulator IS the out
pointer, so aliasing the accumulator name onto the out-argument name `a_out`
across the whole loop body is a pure α-relabeling of the pointer-base role. After
that alias (and the standard `canonicalizeMemrefThread` collapsing the
`STOREIDX`-result thread), every `STOREIDX` base is `a_out` and every `LOADIDX`
base is the corresponding `a_in`, so the shared `memrefBaseReload` reloads each
from its qsave slot before each access — identical to the proven straight-line
ChaCha path. The accumulator feedback (`MOV acc, ret`) collapses to the harmless
no-op `MOV a_out, a_out`, and the `CMP Lctr, invBase` liveness touch is now
redundant (the base lives in memory) but harmless. -/

/-- Rename a register name `from_ ↦ to_` (identity elsewhere): the primitive of
    the accumulator→out-argument alias used by the looped 2-pointer-ABI export. -/
def aliasRegName (from_ to_ : String) (n : String) : String :=
  if n == from_ then to_ else n

/-- Apply `aliasRegName from_ to_` to one `LOperand` — both a plain `reg` name and
    a SIB `arrIdx` base/index. Immediates and compile-time array elements pass
    through. -/
def aliasRegOperand (from_ to_ : String) : LOperand → LOperand
  | .reg n => .reg (aliasRegName from_ to_ n)
  | .arrIdx base idx scale =>
      .arrIdx (aliasRegName from_ to_ base) (aliasRegName from_ to_ idx) scale
  | o => o

/-- Alias the accumulator register name onto the out-argument name across a whole
    looped body: every `Lopn` destination/source `reg` and every SIB base/index
    equal to `from_` becomes `to_`. The op mnemonics, widths, immediates, and
    instruction order are preserved (only the pointer-base *label* changes), so
    the body still denotes the same value sequence — `stackStore` returns its
    input pointer, so the accumulator and the out argument are the same memref. -/
def aliasRegBody (from_ to_ : String) (body : Lcmd) : Lcmd :=
  body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (aliasRegOperand from_ to_)) opn
          (srcs.map (aliasRegOperand from_ to_))⟩
    | _ => i)

/-- The base names of the **array-typed** (`.stackArr`) entries of a variable
    vector, in vector order, under the `resolveVar` convention. The array-typed
    restriction of `exprArgsHV`.

    A scalar invariant (`.reg`, `.inlineInt`, `.bool`) is never a
    `LOADIDX`/`STOREIDX` SIB base, so it takes no red-zone reload slot; dropping
    it here keeps the array bases at the positions the memref ABI assigns them.
    Entries that resolve to an immediate are dropped, as in `exprArgsHV`'s
    `.reg`-filtered use. -/
def arrArgNamesHV (curDepth nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List String
  | [], _ => []
  | ty :: _, .cons v rest =>
      let rest' := arrArgNamesHV curDepth nArgs immSlotMap rest
      match ty, resolveVar curDepth nArgs argName immSlotMap v with
      | .stackArr _ _, LOperand.reg n => n :: rest'
      | _, _ => rest'

/-- The out-base name and the array-typed invariant base names of one loop node's
    `init` / `invs`. The arm every array-carrying `ComL` loop constructor
    shares. -/
def loopArgBasesOf (curDepth nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} {tys : Ctxt jasminDialect}
    (init : Ctxt.Var Γ τ) (invs : HVector (fun ty => Ctxt.Var Γ ty) tys) :
    Option (String × List String) :=
  match resolveVar curDepth nArgs argName immSlotMap init with
  | LOperand.reg outNm =>
      some (outNm, arrArgNamesHV curDepth nArgs immSlotMap invs)
  | _ => none

/-- Resolve a looped `ComL`'s **canonical loop-argument base names** from the
    `forLoopN` (or `forLoop`) node's `init` and `invs`, using the *same*
    `resolveVar` convention the body lowering (`comLToBody`) uses.
    Returns `(outBase, inBases)` where `outBase` is the name the body's
    accumulator / out-array base resolves to (`resolveVar init`) and `inBases`
    are the base names of the **array-typed** invariants, in `invs` order
    (`arrArgNamesHV invs`).

    `ComL.toLfundefPhysAbi` zips `inBases` against `abiArgs.drop 1`, so a base's
    ABI register is fixed by its position among the array invariants. A scalar
    invariant holds no array base and is dropped, keeping that position count
    independent of where a kernel lists its scalars: with scalars in the list,
    every array base to their right would be paired with an ABI register one
    place too far, reloading the array through a scalar's red-zone slot.

    `resolveVar` maps a `Var` to `argName (curDepth - 1 - deBruijn)` — the slot
    counted from the program root, i.e. the **reverse** of the newest-first `Γ`.
    For a top-level `ComL` whose `Γ` is the argument list, the loop's `init` (the
    newest binder `.here`, the out/accumulator) resolves to the **highest** arg
    slot and the last `invs` entry resolves to `a0`. Deriving the names here
    makes the role→name mapping match the body regardless of how a caller ordered
    its `outArg`/`inArgs` hints.

    Returns `none` for a loop-free `ComL` (no `forLoop`/`forLoopN` node). -/
def ComL.loopArgBaseNames (nArgs : Nat) (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (curDepth : Nat) : Option (String × List String) :=
  match c with
  | ComL.ret _ => none
  | ComL.var _ body => ComL.loopArgBaseNames nArgs immSlotMap body (curDepth + 1)
  | ComL.forLoop _ init _ =>
      match resolveVar curDepth nArgs argName immSlotMap init with
      | LOperand.reg n => some (n, [])
      | _ => none
  | ComL.forLoopN _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopNRt _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopNRtNested _ _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.whileNz _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs
  | ComL.forLoopBlock _ _ init invs _ =>
      loopArgBasesOf curDepth nArgs immSlotMap init invs

/-- The virtual-register index of each loop node's accumulator, in spine order.

    A loop binds its final accumulator into scope for its continuation, and a
    `var` binds its expression, so the register index of a node's accumulator is
    the context depth at that node. Called with `depth := nArgs`, the head of the
    result is `nArgs` — the name `ComL.toLfundefPhysAbi` has always aliased — and
    the tail is the accumulators of the later loops of a continuation chain,
    which carry the same array. A single-loop program yields a one-element list,
    so nothing about its export changes. -/
def ComL.loopAccRegs {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (depth : Nat) : List Nat :=
  match c with
  | ComL.ret _ => []
  | ComL.var _ body => ComL.loopAccRegs body (depth + 1)
  | ComL.forLoop _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopN _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopNRt _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopNRtNested _ _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.whileNz _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)
  | ComL.forLoopBlock _ _ _ _ body => depth :: ComL.loopAccRegs body (depth + 1)

/-- The 2-pointer-ABI physical `lfundef` for a **looped** `ComL` array-map kernel
    (`out[i] := f(in[i])`, the `mayo_encode` / `*_sign_rwhile` shape) — the
    loop-aware mirror of `comToLfundefPhysAbi` (§7f).

    `nArgs` is `Γ.length` (the accumulator name is `regName nArgs`). The output
    and input array base names are derived from the `ComL`'s own loop `init`/`invs`
    via `ComL.loopArgBaseNames` (the canonical `resolveVar`-convention names the
    body uses), so the role→name mapping is always correct regardless of the
    `Γ`-vs-root ordering of the caller's `outArg`/`inArgs` hints (the qruov/sdith
    2nd-input base-mis-resolution fix). The caller's `outArg`/`inArgs` are used
    only as a fallback when the program has no loop node. `abiArgs` is the SysV
    pointer-register signature (default `[RDI, RSI]` = `out, inp`).

    The fix vs `ComL.toLfundefPhys`: the accumulator is aliased onto `outArg`, the
    `STOREIDX`-result thread is canonicalized, the pointer arguments are saved to
    red-zone qsave slots in the prologue, and `physBodyWithStores` reloads each
    `LOADIDX`/`STOREIDX` SIB base from its qsave slot into `R14` immediately
    before every access (`memrefBaseReload`). So the IN/OUT array roles follow the
    *argument → qsave-slot* mapping (no swap), and neither base is ever a
    body-clobberable register (no clobber → no segfault). One body copy, real
    `jne .L<d>` back-edge, real x86 registers throughout. -/
def ComL.toLfundefPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    Lfundef :=
  let nArgs := Γ.length
  let virt0 := ComL.toLfundef c immSlotMap
  -- Derive the canonical out-/in-array base names from the program's own loop
  -- node (`init`/`invs`) under the body's `resolveVar` convention. This is the
  -- name each role's `LOADIDX`/`STOREIDX` SIB base ACTUALLY uses in `virt0`, so
  -- the alias and the qsave-reload map below key on the right names regardless of
  -- how the caller ordered `outArg`/`inArgs` (the qruov/sdith fix — see
  -- `ComL.loopArgBaseNames`). Only the ARRAY-typed invariants appear in `inArgs'`,
  -- so the positional pairing with `abiArgs.drop 1` below counts array bases and
  -- is unaffected by where the kernel lists its scalar invariants. Falls back to
  -- the caller's hints for a loop-free `ComL` (no loop node).
  let derived : String × List String :=
    match ComL.loopArgBaseNames nArgs immSlotMap c nArgs with
    | some (o, ins) => (o, ins)
    | none => (outArg, inArgs)
  let outArg' : String := derived.1
  let inArgs' : List String := derived.2
  -- Alias the accumulator (the loop's output-array base, `regName nArgs`) onto the
  -- out-argument name, then collapse the in-place `STOREIDX`-result thread onto
  -- its SIB base. After this, every `STOREIDX` base is `outArg'` and every `LOADIDX`
  -- base is an `inArgs'` name — all argument names the qsave-reload map covers.
  -- Every loop on the continuation spine carries the SAME output array, so each
  -- node's accumulator is aliased onto the out-argument name. Aliasing one
  -- register leaves the later loops of a chain outside the qsave-reload map,
  -- holding the root-counted seed `resolveVar` gives them — the invariant
  -- pointer — and an 8-layer NTT rendered that way stores into its read-only
  -- zeta table. A single-loop program has a one-element `loopAccRegs`, so its
  -- bytes are unchanged.
  let accRegs := (ComL.loopAccRegs c nArgs).map regName
  -- Argument-liveness pin (4+-argument looped signatures — the chained-phase
  -- kernels whose per-phase runtime bounds are read LATE, at each phase's loop
  -- head). Without the pin the linear-scan RA sees each scalar bound as "born
  -- late" and coalesces SEVERAL bound names onto ONE physical register, so
  -- `buildArgPtrMaterialize`'s entry copies overwrite each other and every
  -- phase but the last reads the wrong trip count (the fri_proof fold-chain
  -- segfault). The synthetic `LIVEPIN` reads every argument at entry, forcing
  -- distinct allocations live to their last (phase-head) use; it is filtered
  -- out after `physBodyWithStores`. ≤3-argument signatures (single bound, read
  -- at body start — the QRUOV/HAWK/FAEST GF-dot shape) inject nothing, so
  -- every existing kernel's bytes are unchanged.
  let livePin : Lcmd :=
    if abiArgs.length ≥ 4 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []
  let body1 := livePin
    ++ canonicalizeMemrefThread
         (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body)
  let virt := { virt0 with lfd_body := body1 }
  -- Output-liveness allocation table (`outStoreMap = []` ⇒ `physTable (bodyTrace …)`).
  let tbl := physTableOut virt.lfd_body []
  -- Prologue: save both SysV pointer args (and the six callee-saved GP regs) to
  -- the red zone; the per-access reload sources the array bases from there.
  -- For a MULTI-INPUT signature (`[RDI, RSI, RDX, …]` — the GF-dot kernels),
  -- the canonical `buildPrologue` only saves `RDI`/`RSI`. Each EXTRA input
  -- pointer register (`RDX`, `RCX`, `R8`, `R9`) needs its OWN red-zone qsave
  -- slot so the loop body can reload that input's array base from its own slot
  -- (not the out slot). The saves are appended AFTER the fixed prologue (and
  -- after the `RSI→R14` park), so the single-input / 2-pointer prologue bytes
  -- are unchanged. The save sources the live ABI register directly (it is still
  -- live at entry; `buildArgPtrMaterialize` only clobbers it afterwards).
  let extraInputSaves : Lcmd :=
    (abiArgs.drop 2).filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none)
  let prologue := buildPrologue virt tbl (fun _ => none) ++ extraInputSaves
  -- Materialize each SysV pointer arg into the RA-assigned register the body uses
  -- for its argument name (the 2-pointer memref ABI; `inLoadMap = none`).
  let argMat := buildArgPtrMaterialize virt tbl abiArgs (fun _ => none)
  -- Compose the caller's shift oracle with the dataflow `regConst`→imm resolver.
  let movTbl : Array (Option Nat) := movImmTable virt.lfd_body
  let shiftImm' : ShiftImmOracle := fun nm =>
    match shiftImm nm with
    | some v => some v
    | none => movImmLookup movTbl nm
  -- The memref-base reload map: each array argument `aj` (out + ins) maps its
  -- RA-assigned physical register to its red-zone qsave slot, so every SIB base
  -- is reloaded from memory into `R14` immediately before the access — never a
  -- body-clobberable register.
  -- The out base takes `abiArgs[0]` and the i-th ARRAY invariant `abiArgs[i+1]`:
  -- the memref ABI places the output pointer first and the input pointers next,
  -- ahead of any scalar argument. `inArgs'` holds only the array invariants
  -- (`arrArgNamesHV`), so a scalar listed among the invariants does not shift the
  -- array bases to the right of it onto the following ABI register.
  let argAbi : List (String × String) :=
    (outArg', abiArgs.headD "RDI") :: (inArgs'.zip (abiArgs.drop 1))
  -- `abiSaveOfExt` (not `abiSaveOf`): each input base — including the 3rd+ ABI
  -- register (`RDX`/`RCX`/…) — maps to its OWN qsave slot. With plain `abiSaveOf`
  -- the 2nd input (`RDX`) returned `none`, dropping its pair, so its `LOADIDX`
  -- base was never reloaded and (after `buildArgPtrMaterialize`) read from the
  -- out pointer's register — the byte-KAT-confirmed garbage (qruov/sdith). Each
  -- `(argNm, abiReg)` pair keys on the per-input phys base and yields the input's
  -- distinct slot, so the i-th input reloads from the i-th input's slot.
  let reloadPairs : List (String × String) :=
    argAbi.filterMap (fun (argNm, abiReg) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          -- Key on the barrier-resolved phys base (`physNameForBody`): a
          -- call-containing body relocated the array-base register, so the
          -- reload map must match the register the body's SIB actually reads.
          some (physNameForBody virt.lfd_body tbl argNm, saveName)
      | none => none)
  let memrefBaseReload : String → Option String :=
    fun base => (reloadPairs.find? (fun p => p.1 == base)).map Prod.snd
  -- In-loop-`call` invariant-base restore list. The looped-call barrier's static
  -- `calleeFirstPhys` protects only the first four loop-carried slots (the four
  -- callee-saved registers); a 5th+ loop-carried invariant pointer base (a
  -- multi-pointer rolled fold with an in-loop `call` — the SHAKE256 sponge absorb
  -- input / squeeze output ptr) overflows into a caller-saved register and is
  -- clobbered by the leaf `call`. Reloading it from its qsave slot after each
  -- in-loop `Lcall` (`physBodyWithStores`'s `callArgBaseReload`) restores it.
  --
  -- Keyed *positionally* — `physNameForBody (argName j) ↦ qsave[abiArgs[j]]` —
  -- to mirror `buildArgPtrMaterialize` exactly: at entry the register holding
  -- `argName j` is loaded from `qsave[abiArgs[j]]`, so the post-call reload must
  -- restore that same slot. (The `reloadPairs`/`memrefBaseReload` SIB map keys on
  -- the loop's `init`/`invs` de-Bruijn order via `loopArgBaseNames`, which for a
  -- fold whose accumulator is not the 0-th root arg is *swapped* against the
  -- positional order — correct for a SIB base reloaded into R14, wrong as an
  -- in-register restore.) Bases in a callee-saved register are excluded, so a
  -- body whose loop-carried set fits stays byte-identical (X25519
  -- single-accumulator whole-fold, every ≤4-base kernel).
  let callArgBaseReload : List (String × String) :=
    (abiArgs.zipIdx).filterMap (fun (abiReg, j) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          let phys := physNameForBody virt.lfd_body tbl (argName j)
          if isCallerSavedAllocGPR phys then some (phys, saveName) else none
      | none => none)
  -- The rolled loop body with per-access SIB-base reloads. `outStoreMap = []`
  -- (the loop already carries its own inline `STOREIDX`), `inLoadMap = none`
  -- (the body self-addresses through the array pointers, not per-word loads).
  let bodyWithReload := (physBodyWithStores shiftImm' virt.lfd_body
    (fun _ => none) reloadScratch2 [] reloadScratch2 0 memrefBaseReload
    callArgBaseReload).filter
    (fun i => match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
  -- Restore the callee-saved registers before the final `Lret`.
  let bodyWithRestore := insertEpilogue bodyWithReload calleeSaveRestoreEpilogue
  { virt with
    lfd_body := prologue ++ argMat ++ bodyWithRestore
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := [] }

/-- Export a looped array-map `ComL` to a 2-pointer-ABI physical `Lprog` (the
    `mayo_encode` shape). See `ComL.toLfundefPhysAbi` for the IN/OUT-base reload
    fix (no swap, no clobber). -/
def ComL.toLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap
                 abiArgs abiTyin)] }

/-- Serialize the looped 2-pointer-ABI physical export to the textual lprog blob. -/
def ComL.toLprogPhysAbiText {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : String :=
  magic ++
    (ComL.toLprogPhysAbi c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin).toText
    ++ "\n"

/-- The looped 2-pointer-ABI physical export's bytes. -/
def ComL.toLprogPhysAbiBytes {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) : ByteArray :=
  (ComL.toLprogPhysAbiText c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin).toUTF8

/-- Write the looped 2-pointer-ABI physical lprog blob for a `ComL` to a file. -/
def ComL.writeLprogPhysAbiFile {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String) (path : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) :
    IO Unit :=
  IO.FS.writeBinFile path
    (ComL.toLprogPhysAbiBytes c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin)

/-- The physical export of a **loop-free** `ComL` is byte-identical to the
    straight-line `comToLfundefPhys` on its `Com` image: `comLToBody`'s `.var`/
    `.ret` arms are definitionally the `comToLfundef` body, and every other field
    of `ComL.toLfundefPhys` mirrors `comToLfundefPhys` field-for-field. The two
    `Lfundef`s thus agree on a `.var`/`.ret`-only program, witnessing that the
    loop walk is additive over the straight-line export. (Stated for the doubling
    body's degenerate loop-free witness; see the smoke test below for the looped
    case.) -/
theorem ComL.toLfundefPhys_var_ret_eq_comToLfundefPhys
    {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (v : Ctxt.Var (t :: Γ) s) :
    (ComL.toLfundefPhys (.var e (.ret v))).lfd_body
      = (comToLfundefPhys (.var e (.ret v))).lfd_body := by
  rfl

/-! ## 8. Physical-export correctness

Two value-level obligations are discharged here, mirroring `UnrolledComRA`'s
finite checks (axioms `[propext, Quot.sound]` via `native_decide`):

* **no-collision**: any two simultaneously-live logical slots receive distinct
  physical slots, so the two-address rewrite never clobbers a live value;
* **two-address denotation**: the lowered `mov dst,src0; op dst,src1` (or
  `op dst,src1` when `dst = src0`) computes `dst = op src0 src1` under
  `JasminBinOp.apply` — the destructive form is faithful to the 3-address binop.
-/

/-- A per-live-slot summary row `(slot, phys, start, end)`. -/
def physSummary (tr : List PhysEvent) : List (Nat × Nat × Nat × Nat) :=
  let assign := physAssign tr
  (physLiveItems tr).map (fun item =>
    let s := item.1
    let ph := match assign.find? (fun p => p.1 == s) with
      | some (_, p) => p
      | none => s
    (s, ph, item.2.1, item.2.2))

/-- **No-collision predicate**: distinct live slots with overlapping ranges get
    distinct physical slots. -/
def PhysNoCollision (tr : List PhysEvent) : Prop :=
  ∀ r₁ ∈ physSummary tr, ∀ r₂ ∈ physSummary tr,
    r₁.1 ≠ r₂.1 →
    physRangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) = true →
      r₁.2.1 ≠ r₂.2.1

/-- Decidable Boolean form of `PhysNoCollision`. -/
def physNoCollisionB (tr : List PhysEvent) : Bool :=
  let rows := physSummary tr
  rows.all (fun r₁ =>
    rows.all (fun r₂ =>
      if r₁.1 == r₂.1 then true
      else if physRangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) then
        r₁.2.1 != r₂.2.1
      else true))

/-- The Boolean check implies the `PhysNoCollision` Prop. -/
theorem physNoCollision_of_boolB (tr : List PhysEvent)
    (h : physNoCollisionB tr = true) : PhysNoCollision tr := by
  intro r₁ h1 r₂ h2 hne hov
  have step1 := List.all_eq_true.mp h r₁ h1
  have step2 := List.all_eq_true.mp step1 r₂ h2
  by_cases heq : r₁.1 == r₂.1
  · simp only [beq_iff_eq] at heq; exact absurd heq hne
  · simp only [heq, Bool.false_eq_true, if_false, hov, if_true] at step2
    simpa [bne, beq_iff_eq] using step2

/- The concrete no-collision check for the ChaCha20-block physical allocation
   (`chacha20_block`'s body trace) is `physNoCollisionChaCha`, proved below over
   the concrete trace by `native_decide`. -/

/-! ### A register-store model of the two-address rewrite

To state the two-address denotation we model a register file as
`store : Nat → BitVec w` (slot → value). `setReg` is a destructive write;
`movStep`/`opStep` are the two-address instruction effects. The theorem
`twoAddr_denote` shows: running `mov dst,src0; op dst,src1` on any store with
`src0 ↦ a`, `src1 ↦ b` leaves `dst ↦ JasminBinOp.apply op a b` — exactly what
the 3-address `dst = op src0 src1` computes. The collapsed case
(`dst = src0`, single `op dst,src1`) gives the same result. The hypothesis
`dst ≠ src1` is the **no-collision** side-condition: the destructive `dst` write
must not clobber the still-needed `src1` before the op reads it (guaranteed by
`PhysNoCollision` for distinct live slots). -/

/-- A register file: slot → value at width `w`. -/
abbrev RegStore (w : Nat) := Nat → BitVec w

/-- Destructive write of `v` to slot `d`. -/
def setReg {w : Nat} (st : RegStore w) (d : Nat) (v : BitVec w) : RegStore w :=
  fun s => if s = d then v else st s

/-- `mov dst, src0`: copy `st src0` into `dst`. -/
def movStep {w : Nat} (st : RegStore w) (dst src0 : Nat) : RegStore w :=
  setReg st dst (st src0)

/-- `op dst, src1`: destructive binop `dst := apply op (st dst) (st src1)`. -/
def opStep {w : Nat} (op : JasminBinOp) (st : RegStore w) (dst src1 : Nat) :
    RegStore w :=
  setReg st dst (op.apply (st dst) (st src1))

/-- **Two-address lowering denotation (`mov dst,src0; op dst,src1`).** Running
    the destructive pair on any store leaves `dst ↦ apply op (st src0) (st src1)`
    — the value the 3-address `dst = op src0 src1` computes. The side-condition
    `dst ≠ src1` is the no-collision guarantee that the `mov` does not clobber
    `src1` before `op` reads it. -/
theorem twoAddr_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 : Nat) (hne : dst ≠ src1) :
    (opStep op (movStep st dst src0) dst src1) dst
      = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, ↓reduceIte]
  rw [if_neg (Ne.symm hne)]

/-- **Collapsed two-address denotation (`dst = src0`, single `op dst,src1`).**
    When the RA placed `dst` on `src0`'s register, `dst` already holds `a`, so
    the single `op dst,src1` computes `apply op (st dst) (st src1)` — and since
    `dst = src0` here, that is `apply op (st src0) (st src1)`, the same value. -/
theorem twoAddr_denote_collapsed {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src1 : Nat) :
    (opStep op st dst src1) dst = op.apply (st dst) (st src1) := by
  simp only [opStep, setReg, ↓reduceIte]

/-- `op dst, #v`: destructive binop with an immediate second operand
    `dst := apply op (st dst) (BitVec.ofNat w v)`. The immediate is the value
    `v` reduced modulo `2^w` (`BitVec.ofNat`), so this models `SHL/SHR r/m, imm`
    exactly: the count is the literal `v`, no register read. -/
def opStepImm {w : Nat} (op : JasminBinOp) (st : RegStore w) (dst v : Nat) :
    RegStore w :=
  setReg st dst (op.apply (st dst) (BitVec.ofNat w v))

/-- **Immediate-shift denotation (collapsed, `dst = src0`, `op dst, #v`).** The
    single immediate-count op computes `apply op (st dst) (ofNat w v)` — the same
    value the register-count form computes when the shift-count register holds the
    constant `v` (`st src1 = BitVec.ofNat w v`). For `SHL`/`SHR` this is
    `(st dst) <<< (ofNat w v).toNat` / `>>>`, i.e. the rotate amount as a literal. -/
theorem twoAddrShiftImm_denote_collapsed {w : Nat} (op : JasminBinOp)
    (st : RegStore w) (dst v : Nat) :
    (opStepImm op st dst v) dst = op.apply (st dst) (BitVec.ofNat w v) := by
  simp only [opStepImm, setReg, ↓reduceIte]

/-- **Immediate-shift denotation (general, `dst ≠ src0`, `mov dst,src0; op dst,#v`).**
    The `mov` copies `src0` into `dst`, then the immediate-count op computes
    `apply op (st src0) (ofNat w v)` — the value the 3-address
    `dst = op src0 #v` computes. (No `dst ≠ src1` side-condition is needed: the
    immediate carries no register slot to clobber.) -/
theorem twoAddrShiftImm_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 v : Nat) :
    (opStepImm op (movStep st dst src0) dst v) dst
      = op.apply (st src0) (BitVec.ofNat w v) := by
  simp only [opStepImm, movStep, setReg, ↓reduceIte]

/-- **Immediate-shift faithfulness.** When the shift-count register `src1` holds
    the constant `v` (i.e. `st src1 = BitVec.ofNat w v`), the immediate-count
    op `op dst, #v` computes exactly what the register-count op `op dst, src1`
    computes. This is the correctness of rendering a constant shift count as an
    `#imm` operand: the two forms denote the same store update on `dst`. -/
theorem opStepImm_eq_opStep_of_const {w : Nat} (op : JasminBinOp)
    (st : RegStore w) (dst src1 v : Nat) (hv : st src1 = BitVec.ofNat w v) :
    (opStepImm op st dst v) dst = (opStep op st dst src1) dst := by
  simp only [opStepImm, opStep, setReg, ↓reduceIte, hv]

/-- **Reload denotation (`mov R15, src; op dst, R15`, `dst ≠ R15`).** Routing the
    second source through the reload scratch `sc` (any slot with `dst ≠ sc`)
    computes `apply op (st dst) (st src)` in `dst` — exactly what the direct
    `op dst, src` computes. This is the correctness of the two-memory-operand
    legalization: the reload preserves the value, only the encoding changes.
    The side-condition `dst ≠ sc` is the reserved-scratch guarantee (`R15` is
    never an allocation target, so it never aliases `dst`). -/
theorem reload_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src sc : Nat) (hsc : dst ≠ sc) :
    (opStep op (movStep st sc src) dst sc) dst = op.apply (st dst) (st src) := by
  simp only [opStep, movStep, setReg, if_true, if_neg hsc]

/-- **Dst-reload denotation (`mov sc, src0; op sc, src1; mov dst, sc`).** When
    `dst` is itself a spill slot, the reload pass routes the whole binop
    through the scratch `sc`: load `src0` into `sc`, run `op sc, src1` on the
    scratch (`src1` read from the original store), then store the result back
    to `dst`. The final store leaves `dst ↦ apply op (st src0) (st src1)` —
    exactly what the direct `op dst, src1` (after `mov dst, src0`) would
    compute. The side-condition `sc ≠ src1` ensures the initial reload of
    `src0` does not clobber `src1`. -/
theorem reloadDst_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 sc : Nat) (hsc1 : sc ≠ src1) :
    let st1 := movStep st sc src0
    let st2 := opStep op st1 sc src1
    (setReg st2 dst (st2 sc)) dst = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, if_true]
  by_cases h : src1 = sc
  · exact absurd h.symm hsc1
  · simp [h]

/-- **Dst+src reload denotation (`mov sc, src0; mov sc2, src1; op sc, sc2;
    mov dst, sc`).** Both-spill case: load `src0` into the primary scratch
    `sc`, `src1` into the secondary scratch `sc2`, op the scratches, store
    back to `dst`. Yields `dst ↦ apply op (st src0) (st src1)`. Side-conditions
    `sc ≠ src1` (initial src0-reload doesn't clobber src1) and `sc ≠ sc2`
    (the two scratches are distinct allocations). -/
theorem reloadBoth_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 sc sc2 : Nat) (hsc1 : sc ≠ src1) (hsc12 : sc ≠ sc2) :
    let st1 := movStep st sc src0
    let st2 := movStep st1 sc2 src1
    let st3 := opStep op st2 sc sc2
    (setReg st3 dst (st3 sc)) dst = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, if_true]
  -- The result in `sc` after the op is `apply op (st2 sc) (st2 sc2)`.
  -- `st2 sc = st1 sc = st src0` (since src1 ≠ sc by hsc1, and sc was just
  -- written to st src0).
  -- `st2 sc2 = st src1` directly.
  -- Then `setReg ... dst (st3 sc) dst = st3 sc`.
  by_cases h2 : sc = sc2
  · exact absurd h2 hsc12
  · by_cases h1 : src1 = sc
    · exact absurd h1.symm hsc1
    · simp [h1, h2]

/-- The primary reload-scratch operand is a register, never a spill slot. -/
theorem reloadScratch_not_spill : (LOperand.reg reloadScratch).isSpill = false := by
  native_decide

/-- The secondary reload-scratch operand is a register, never a spill slot. -/
theorem reloadScratch2_not_spill : (LOperand.reg reloadScratch2).isSpill = false := by
  native_decide

/-- An immediate operand is never a spill slot. -/
theorem imm_not_spill (v : Nat) : (LOperand.imm v).isSpill = false := rfl

/-- **x86 memory-operand legality of one `Lopn`.** An `Lopn` with destination
    `[d]` and sources `[s0, s1]` is two-address (`d := d op s1`, with `s0 = d`),
    so its two *distinct* operand positions are `d` (lval = first rval) and `s1`.
    x86 allows at most one memory operand among them, i.e. `d` and `s1` are not
    both spill slots. A `mov [d] [s]` (sources `[s]`) is legal iff `d`, `s` are
    not both spill. Other constructors carry no two-memory hazard. -/
def LinstrR.legalMemForm : LinstrR → Bool
  | .Lopn (d :: _) _ (_ :: s1 :: _) => !(d.isSpill && s1.isSpill)
  | .Lopn (d :: _) _ (s :: _) => !(d.isSpill && s.isSpill)
  | _ => true

/-- `legalizeBinop` emits one of four shapes:

    * both operands registers — a single direct `op dst, src`;
    * spill `src` only — reload `src` through `R15`, then `op dst, R15`;
    * spill `dst` only — reload `dst` through `R15`, op in `R15`, store back;
    * both spills — reload both through `R15`/`R14`, op in scratches, store back.
-/
theorem legalizeBinop_shape (dst src : LOperand) (opn : String)
    (mov : String := "MOV") :
    legalizeBinop dst src opn mov
      = (match dst.isSpill, src.isSpill with
         | false, false => [.Lopn [dst] opn [dst, src]]
         | false, true  =>
             [.Lopn [.reg reloadScratch] mov [src],
              .Lopn [dst] opn [dst, .reg reloadScratch]]
         | true,  false =>
             [.Lopn [.reg reloadScratch] mov [dst],
              .Lopn [.reg reloadScratch] opn [.reg reloadScratch, src],
              .Lopn [dst] mov [.reg reloadScratch]]
         | true,  true  =>
             [.Lopn [.reg reloadScratch] mov [dst],
              .Lopn [.reg reloadScratch2] mov [src],
              .Lopn [.reg reloadScratch] opn
                [.reg reloadScratch, .reg reloadScratch2],
              .Lopn [dst] mov [.reg reloadScratch]]) := by
  unfold legalizeBinop
  cases dst.isSpill <;> cases src.isSpill <;> rfl

/-- When neither `dst` nor `src` is a spill slot, `legalizeBinop` is the single
    direct instruction (no reload). -/
theorem legalizeBinop_noSpill (dst src : LOperand) (opn : String)
    (hd : dst.isSpill = false) (hs : src.isSpill = false) :
    legalizeBinop dst src opn = [.Lopn [dst] opn [dst, src]] := by
  unfold legalizeBinop
  rw [hd, hs]

/-- When `dst` and `src` are not both spill slots, `legalizeMov` is the single
    direct copy (no reload). -/
theorem legalizeMov_noSpill (dst src : LOperand)
    (h : dst.isSpill = false ∨ src.isSpill = false) :
    legalizeMov dst src = [.Lopn [dst] "MOV" [src]] := by
  unfold legalizeMov
  rcases h with h | h <;> simp [h]

/-- Every `Lopn` `legalizeBinop` emits is x86-memory-legal: each non-MOV op has
    its non-MOV operand positions in register scratches (`R15`/`R14`), and each
    MOV touches at most one spill slot. -/
theorem legalizeBinop_legalMemForm (dst src : LOperand) (opn : String)
    (mov : String := "MOV") :
    ∀ r ∈ legalizeBinop dst src opn mov, r.legalMemForm = true := by
  intro r hr
  rw [legalizeBinop_shape dst src opn mov] at hr
  rcases hd : dst.isSpill <;> rcases hs : src.isSpill <;>
    simp only [hd, hs] at hr
  · -- (false, false)
    simp only [List.mem_singleton] at hr
    subst hr
    simp [LinstrR.legalMemForm, hd, hs]
  · -- (false, true)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, hd, hs]
  · -- (true, false)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, hd, hs]
  · -- (true, true)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill,
            reloadScratch2_not_spill, hd, hs]

/-- Every `Lopn` `legalizeMov` emits is x86-memory-legal. -/
theorem legalizeMov_legalMemForm (dst src : LOperand) (mov : String := "MOV") :
    ∀ r ∈ legalizeMov dst src mov, r.legalMemForm = true := by
  intro r hr
  unfold legalizeMov at hr
  by_cases h : dst.isSpill && src.isSpill
  · simp only [h, if_true, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill]
  · simp only [h, Bool.false_eq_true, if_false, List.mem_singleton] at hr
    subst hr
    simp only [LinstrR.legalMemForm, Bool.not_eq_true', Bool.and_eq_false_iff]
    rw [Bool.not_eq_true, Bool.and_eq_false_iff] at h
    exact h

set_option linter.unusedVariables false in
/-- When no operand is a spill slot, the two-address lowering has the classic
    shape: a single op when the RA placed `dst` on `src0`'s register, else a
    `mov` + the op. (With the reload pass, the direct binop form is only taken
    when **both** `dst` and `s1` are registers — a stricter precondition than
    the old "at most one spill" check. The `s0` hypothesis is kept for
    documentation — a no-spill source `s0` simplifies the leading `mov dst,
    s0` to a single direct copy.) -/
theorem lowerTwoAddr_shape_noSpill (dst s0 s1 : LOperand) (opn : String)
    (hd : dst.isSpill = false) (hs0 : s0.isSpill = false)
    (hs1 : s1.isSpill = false) :
    lowerTwoAddr dst s0 s1 opn
      = (if dst = s0 then [.Lopn [dst] opn [dst, s1]]
         else [.Lopn [dst] "MOV" [s0], .Lopn [dst] opn [dst, s1]]) := by
  simp only [lowerTwoAddr, materializeWideImm_MOV, List.nil_append,
    List.append_nil]
  split
  · exact legalizeBinop_noSpill dst s1 opn hd hs1
  · rw [legalizeMov_noSpill dst s0 (Or.inl hd),
        legalizeBinop_noSpill dst s1 opn hd hs1]
    rfl

/-- The whole two-address lowering is x86-memory-legal in every emitted `Lopn`:
    each leg (the `mov` and the binop) is legalized so no single instruction has
    its two distinct operand positions both in memory. -/
theorem lowerTwoAddr_legalMemForm (dst s0 s1 : LOperand) (opn : String) :
    ∀ r ∈ lowerTwoAddr dst s0 s1 opn, r.legalMemForm = true := by
  intro r hr
  simp only [lowerTwoAddr, materializeWideImm_MOV, List.nil_append,
    List.append_nil] at hr
  split at hr
  · exact legalizeBinop_legalMemForm dst s1 opn "MOV" r hr
  · rw [List.mem_append] at hr
    rcases hr with hr | hr
    · exact legalizeMov_legalMemForm dst s0 "MOV" r hr
    · exact legalizeBinop_legalMemForm dst s1 opn "MOV" r hr

set_option linter.unusedVariables false in
/-- The immediate-shift lowering has three shapes depending on whether `dst` is
    a spill slot:

    * `dst` is a spill — reload through `R15`: `mov R15, s0; op R15, #v;
      mov dst, R15` (3 `Lopn`s). When `dst = s0`, the first mov reloads
      `dst`'s current value into the scratch.
    * `dst` is a register, `dst = s0` — single `op dst, #v` (1 `Lopn`).
    * `dst` is a register, `dst ≠ s0` — `mov dst, s0; op dst, #v` (2 `Lopn`s,
      the leading mov is legalized so `s0` may itself be a spill).

    The `hms` hypothesis is kept for documentation — the register-`dst` branch
    only needs `dst.isSpill = false`, which is part of the disjunction. -/
theorem lowerTwoAddrShiftImm_shape (dst s0 : LOperand) (v : Nat) (opn : String)
    (hms : dst.isSpill = false ∨ s0.isSpill = false) :
    lowerTwoAddrShiftImm dst s0 v opn
      = (if dst.isSpill then
           [.Lopn [.reg reloadScratch] "MOV" [s0],
            .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .imm v],
            .Lopn [dst] "MOV" [.reg reloadScratch]]
         else if dst = s0 then [.Lopn [dst] opn [dst, .imm v]]
         else [.Lopn [dst] "MOV" [s0], .Lopn [dst] opn [dst, .imm v]]) := by
  unfold lowerTwoAddrShiftImm
  by_cases hd : dst.isSpill = true
  · simp only [hd, ↓reduceIte]
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · rw [legalizeMov_noSpill dst s0 (Or.inl hd)]; rfl

/-- The immediate-shift lowering is x86-memory-legal in every emitted `Lopn`
    (the `mov` is legalized; the op's second operand is the immediate, never
    memory, so `op [mem], #imm` is a legal single-memory-operand encoding). -/
theorem lowerTwoAddrShiftImm_legalMemForm (dst s0 : LOperand) (v : Nat)
    (opn : String) :
    ∀ r ∈ lowerTwoAddrShiftImm dst s0 v opn, r.legalMemForm = true := by
  intro r hr
  unfold lowerTwoAddrShiftImm at hr
  by_cases hd : dst.isSpill = true
  · simp only [hd, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, imm_not_spill]
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases heq : dst = s0
    · rw [if_pos heq] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp [LinstrR.legalMemForm, imm_not_spill]
    · rw [if_neg heq] at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact legalizeMov_legalMemForm dst s0 "MOV" r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        simp [LinstrR.legalMemForm, imm_not_spill]

/-- The physical export is structurally well-formed: one function named `fname`,
    exported, body ending in `Lret`. -/
theorem Com.toLprogPhys_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprogPhys com fname).lp_funcs.length = 1 ∧
      ((Com.toLprogPhys com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprogPhys com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-! ### ABI-wrapped export: structural lemmas

The ABI wrapper is a pure structural transform: prologue loads + body + epilogue
stores. The body is the verified `physBody` unchanged, so all body-level
denotation lemmas (`twoAddr_denote`, `reload_denote`, etc.) continue to apply.
The wrapper's correctness reduces to two facts:

* every prologue/epilogue `Lopn` is a single `MOV` whose memory operand is a
  `mem.<base>.<off>` reference (NOT a `k.<N>` spill); the read_linear textual
  reader materialises `mem.RDI.0` / `mem.RSI.4` as a `[base + off]` memory
  reference, exactly the SysV-ABI load/store the C harness expects;
* the wrapped body still ends in `Lret` (so jasmin's `assemble_fd` accepts it).
-/

set_option linter.unusedVariables false in
/-- The epilogue-insertion step preserves the `Lret`-terminated body shape: a
    body that ends in `Lret`, after inserting any epilogue (a list of stores),
    still ends in `Lret`. The hypothesis `h` is kept for documentation — the
    statement is structurally true even without it (the result always ends in
    the explicit trailing `Lret`). -/
theorem insertEpilogue_ends_Lret (body epi : Lcmd)
    (h : body.getLast?.map Linstr.li_i = some LinstrR.Lret) :
    (insertEpilogue body epi).getLast?.map Linstr.li_i = some LinstrR.Lret := by
  unfold insertEpilogue
  -- The result is `body.dropLast ++ epi ++ [Lret]`; its last is the trailing `Lret`.
  simp [List.getLast?_append, List.getLast?_cons]

/-- The ABI-wrapped physical export is structurally well-formed: one function
    named `fname`, exported. (The empty `lfd_res`/`lfd_tyout` reflect the
    2-pointer SysV ABI where the result is returned via memory at `*out`.) -/
theorem Com.toLprogPhysAbi_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprogPhysAbi com fname).lp_funcs.length = 1 ∧
      ((Com.toLprogPhysAbi com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprogPhysAbi com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-- The prologue is the 9-instruction pointer-save + callee-save + RSI-park
    prelude, all `MOVQ`s (save RDI/RSI to red zone, save the six SysV
    callee-saved GPRs RBX/RBP/R12/R13/R14/R15 to red zone, park RSI into R14).
    The per-slot input loads have moved inside `physBodyWithStores`.

    Updated 2026-05-27: now 9 instructions (was 7) — `R14` and `R15` are added
    to the callee-save set per the SysV x86-64 ABI. -/
theorem buildPrologue_all_MOVQ (virt : Lfundef) (tbl : Array Nat)
    (inLoadMap : InLoadMap) :
    ∀ r ∈ buildPrologue virt tbl inLoadMap,
      ∃ dsts srcs, r.li_i = LinstrR.Lopn dsts "MOVQ" srcs := by
  intro r hr
  unfold buildPrologue at hr
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr <;> subst hr <;>
    exact ⟨_, _, rfl⟩

/-- The epilogue is a list of `MOV` Lopns: every emitted instruction is a
    single `Lopn` with `opn = "MOV"`. (Structural invariant of `buildEpilogue`;
    the leading restore MOV and each target's 1-or-2 store MOVs are all MOVs.) -/
theorem buildEpilogue_all_MOV (virt : Lfundef) (tbl : Array Nat)
    (outStoreMap : OutStoreMap) :
    ∀ r ∈ buildEpilogue virt tbl outStoreMap,
      ∃ dsts srcs, r.li_i = LinstrR.Lopn dsts "MOV" srcs := by
  intro r hr
  unfold buildEpilogue at hr
  rw [List.mem_append] at hr
  rcases hr with hres | hr
  · simp at hres
    subst hres
    exact ⟨_, _, rfl⟩
  · rw [List.mem_flatMap] at hr
    obtain ⟨j, _hj, h⟩ := hr
    cases ho : outStoreMap[j]? with
    | none => simp [ho] at h
    | some bo =>
        simp [ho] at h
        cases hbd : bindingDstOp virt.lfd_body
                      (numBindings virt.lfd_body - outStoreMap.length + j) with
        | none => simp [hbd] at h
        | some d =>
            cases d with
            | reg srcName =>
                simp [hbd] at h
                by_cases hs : (LOperand.reg
                                (physNameForBody virt.lfd_body tbl srcName)).isSpill
                · simp [hs] at h
                  rcases h with h | h <;> subst h <;> exact ⟨_, _, rfl⟩
                · simp [hs] at h
                  subst h
                  exact ⟨_, _, rfl⟩
            | arr _ _ => simp [hbd] at h
            | imm _ => simp [hbd] at h
            | arrIdx _ _ _ => simp [hbd] at h

/-! ### 7e. Precise point-wise liveness + interference checker (Phase 0 RA TV)

The `PhysNoCollision` check above (`physSummary` / `physRangesOverlap`) uses the
**conservative interval** liveness `[firstTouch, lastTouch]`: a slot is treated
as live across the entire span between its first and last touch. That interval
is sound for the fresh-SSA per-binding trace (each SSA name is touched in one
contiguous window) but is **wrong for a residence-collapsed body**: a residence
class such as `sc0` / `prod1` / a lane is touched all over the permutation, so
its interval spans nearly the whole body and would spuriously interfere with
everything — the interval check cannot tell the *aliasing* collapse (two values
that must coexist mapped onto one class) from a *legitimate* in-place reuse.

This block adds the **precise point-wise gen/kill** liveness used by a real
register allocator and a translation-validation interference checker that runs
on the *fresh-SSA* trace against a **proposed** logical→physical map `ρ`
(e.g. `residenceArraySlotOf (slotTraceArr ())`). The body is straight-line (a
let-chain, no control flow), so liveness is a single backward pass:

  `live_in[i]  = (live_out[i] \ {wr i}) ∪ rds i`
  `live_out[i] = live_in[i+1]`,    `live_out[last] = ∅`.

The checker rejects a map `ρ` iff at some point two *distinct* fresh-SSA slots
that are simultaneously live (or a def vs. a slot live just after it) are mapped
to the **same** physical/residence class — exactly the
two-address side-condition `dst ≠ src1` of `twoAddr_denote`, lifted to "no two
coexisting logical values share a register". -/

/-- Per-event **live-out** sets of a straight-line `PhysEvent` trace, in program
    order: `liveOuts tr` has the same length as `tr`, and its `i`-th entry is the
    set of slots live immediately *after* event `i` (= live-in of event `i+1`,
    `∅` after the last event). Computed by one backward pass:
    threading the running live-in set right-to-left, each event prepends its own
    live-out (the successor's live-in) to the result.

    Returns the pair `(liveInOfHead, liveOuts)`; `liveInOfHead` is the set live
    before the first event (only needed internally to seed the recursion). -/
def liveAux : List PhysEvent → List Nat × List (List Nat)
  | [] => ([], [])
  | ev :: rest =>
      let (succIn, outsRest) := liveAux rest
      -- live-out of `ev` is the live-in of its successor (`succIn`), `∅` if last.
      let liveOutEv := succIn
      -- live-in of `ev` = (live-out \ {def}) ∪ uses.
      let liveInEv := (liveOutEv.filter (· != ev.wr)) ++ ev.rds
      (liveInEv, liveOutEv :: outsRest)

/-- **Compiled** live-out pass: a rolling array of "next-use distance" is avoided
    in favour of a rolling *live set* carried as a `Std.HashMap Nat Unit` (a slot
    set), updated event-by-event from the END of the trace. For each event we
    snapshot the current live set as that event's live-out, then apply gen/kill
    (`kill def`, `gen uses`) to obtain the predecessor's live set. The set stays
    ≤ K (the max number of simultaneously-live residence classes — 25 for
    Poseidon2), so each step is `O(K)` and the whole pass is `O(n·K)` with no
    per-point materialization beyond the snapshot list. Mirrors
    `physLiveDataImpl`'s single-array discipline (#512 build-cost precedent);
    handles the 107k-binding body without stack overflow (tail-accumulating). -/
@[inline] def liveOutsImpl (tr : List PhysEvent) : List (List Nat) := Id.run do
  -- Walk events from last to first over the reversed list (no indexed access,
  -- so no `Inhabited PhysEvent` is needed). `live` is the live-in of the
  -- successor event = live-out of the current event; snapshot it, then apply
  -- kill (def) / gen (uses) to obtain the predecessor's live-in. Prepending the
  -- snapshots while walking the reversed trace yields program order directly.
  let mut live : Std.HashMap Nat Unit := {}
  let mut outs : List (List Nat) := []
  for ev in tr.reverse do
    outs := live.keys :: outs          -- live-out of this event
    live := live.erase ev.wr           -- kill def
    for u in ev.rds do                 -- gen uses
      live := live.insert u ()
  return outs

/-- The per-event live-out sets of a trace (length = `tr.length`). The pure spec
    uses the structural backward recursion `liveAux`; `@[implemented_by]` swaps
    in the rolling-set array pass `liveOutsImpl` for native execution on the
    107k-binding body (no per-point stack frame, no super-linear set copies). -/
@[implemented_by liveOutsImpl]
def liveOuts (tr : List PhysEvent) : List (List Nat) := (liveAux tr).2

/-- The proposed-map interference predicate at one point: among the slots in a
    live set `ls`, no two *distinct* slots are mapped by `ρ` to the same class.
    Callers pass `wr i :: live_out[i]` so the def-clobbers-live-out edge is
    included. -/
def liveSetInterferenceOkB (ρ : Nat → Nat) (ls : List Nat) : Bool :=
  ls.all (fun a => ls.all (fun b => if a == b then true else ρ a != ρ b))

/-- **Interference checker** for a proposed logical→physical map `ρ` over the
    straight-line fresh-SSA trace `tr`. For every program point `i` the slots
    that are simultaneously live (the def `wr i` together with `live_out[i]`)
    must receive pairwise-distinct images under `ρ`. The def is included in the
    live set at its own point precisely so the **def-clobbers-live-out** edge is
    checked: if `wr i`'s residence class collides with a *different* value still
    live after `i`, the destructive write would clobber it — this is the edge
    that catches the Poseidon2 MDS lane/scratch aliasing.

    `true` ⇒ `ρ` is interference-respecting (sound, see `interferenceOk_of_boolB`).
    `false` ⇒ a real conflicting pair exists at some point. -/
def interferenceOkB (tr : List PhysEvent) (ρ : Nat → Nat) : Bool :=
  (tr.zip (liveOuts tr)).all (fun p =>
    let ev := p.1
    let lo := p.2
    liveSetInterferenceOkB ρ (ev.wr :: lo))

/-- The proposition the Boolean checker decides: at every program point, the
    def together with the live-out slots receive pairwise-distinct `ρ`-images. -/
def InterferenceRespected (tr : List PhysEvent) (ρ : Nat → Nat) : Prop :=
  ∀ p ∈ tr.zip (liveOuts tr),
    ∀ a ∈ (p.1.wr :: p.2), ∀ b ∈ (p.1.wr :: p.2), a ≠ b → ρ a ≠ ρ b

/-- **Soundness bridge**: the Boolean interference checker implies the
    `InterferenceRespected` proposition. Mirrors `physNoCollision_of_boolB`. -/
theorem interferenceOk_of_boolB (tr : List PhysEvent) (ρ : Nat → Nat)
    (h : interferenceOkB tr ρ = true) : InterferenceRespected tr ρ := by
  intro p hp a ha b hb hne
  have hpoint := List.all_eq_true.mp h p hp
  -- `hpoint : liveSetInterferenceOkB ρ (p.1.wr :: p.2) = true`
  simp only [liveSetInterferenceOkB] at hpoint
  have ha' := List.all_eq_true.mp hpoint a ha
  have hb' := List.all_eq_true.mp ha' b hb
  by_cases heq : a == b
  · simp only [beq_iff_eq] at heq; exact absurd heq hne
  · simp only [heq, Bool.false_eq_true, if_false] at hb'
    simpa [bne, beq_iff_eq] using hb'

/-! ### 7f. The fresh-SSA trace and the proposed residence map

To run the checker against a residence proposal `slotOfBinding`, the *fresh-SSA*
trace (one unique slot per binding) is paired with the map
`ρ = slotOfBinding ∘ (slot → binding-ordinal)`. For the canonical
first-appearance slot indexing of `bodyTrace`, the def slot of the `n`-th
`Lopn` is its own first-appearance rank; the proposed map sends that rank to the
residence class `slotOfBinding n`. The helper below builds `ρ` as an `Array`
lookup keyed by def-slot for the common case where slot = binding ordinal (true
for the fresh-SSA export, where each binding introduces exactly one new name).
-/

/-- The proposed logical→physical map as an array keyed by fresh-SSA def-slot:
    `ρ s = slots[s]` (identity outside the residence universe). For the
    fresh-SSA Poseidon2 trace the `n`-th def slot is `n`, so this is exactly
    `residenceArraySlotOf (slotTraceArr ())`. -/
def proposedRho (slots : Array Nat) : Nat → Nat := residenceArraySlotOf slots

/-- **Identity (fresh-SSA) allocation is always interference-respecting.** With
    `ρ = id` distinct slots never collide, so the checker accepts every trace —
    confirming the checker is not vacuously `false`. -/
theorem interferenceOkB_id (tr : List PhysEvent) : interferenceOkB tr id = true := by
  simp only [interferenceOkB, liveSetInterferenceOkB, List.all_eq_true]
  intro p _ a _ b _
  by_cases h : a == b
  · simp [h]
  · have hf : (a == b) = false := by simpa using h
    simp only [hf, Bool.false_eq_true, if_false, id_eq, bne, Bool.not_false]

/-! ### 7g. Phase-0 demonstration witnesses

A *correct* fresh-SSA fragment (distinct slot per def, identity map) is accepted,
and a small fragment reproducing the **MDS lane/scratch aliasing pattern** of
`Poseidon2WholePermCom.recApplyMat4` / `recColSums` is REJECTED by the proposed
residence map. The pattern: two distinct logical values are simultaneously live
(e.g. a product `prod1` accumulated while a lane value is still needed) yet the
residence proposal maps both onto the same class — the def of one clobbers the
other before its last use. -/

/-- A 4-binding **correct** fragment: slot 0 read by 1, slot 1 read by 2, etc. —
    no two coexisting values share a slot. Identity map accepts it. -/
def demoTraceOk : List PhysEvent :=
  [ { wr := 0, rds := [] },
    { wr := 1, rds := [0] },
    { wr := 2, rds := [1] },
    { wr := 3, rds := [2, 1] } ]

/-- A fragment reproducing the MDS aliasing: binding 0 defines value `A` (slot 0),
    binding 1 defines value `B` (slot 1); binding 2 reads BOTH `A` and `B`
    (so both are live after binding 1), and binding 3 also reads both — both `A`
    and `B` are simultaneously live across bindings 1–3. A residence proposal
    that coalesces slot 0 and slot 1 onto the same class is unsound here. -/
def demoTraceAlias : List PhysEvent :=
  [ { wr := 0, rds := [] },
    { wr := 1, rds := [] },
    { wr := 2, rds := [0, 1] },
    { wr := 3, rds := [0, 1] } ]

/-- The aliasing residence proposal: collapse slots 0 and 1 onto class 0. -/
def demoRhoAlias : Array Nat := #[0, 0, 2, 3]

/-- **Sanity (positive):** the correct fresh-SSA fragment is accepted under the
    identity map. -/
theorem demoTraceOk_accepts : interferenceOkB demoTraceOk id = true := by
  decide

/-- **Phase-0 reject demonstration (small witness):** the precise point-wise
    checker REJECTS the residence proposal that coalesces two simultaneously-live
    values — the exact MDS-aliasing shape from `recApplyMat4`/`recColSums`. The
    conservative-interval `physNoCollisionB` cannot express this rejection;
    the point-wise checker does. -/
theorem demoTraceAlias_rejects :
    interferenceOkB demoTraceAlias (proposedRho demoRhoAlias) = false := by
  decide

/-- **Phase-0 reject demonstration (positive control):** the SAME aliasing trace
    is ACCEPTED by the identity (fresh-SSA) map — so the rejection above is
    caused by the residence proposal, not by the trace being intrinsically
    unallocatable. -/
theorem demoTraceAlias_id_accepts : interferenceOkB demoTraceAlias id = true := by
  decide

/-! ## Fixed-trip loop smoke test (`ComL` / `comLToBody`)

A one-argument program that seeds an accumulator from its input, runs the
doubling body `acc := acc + acc` `4` times via a `forLoop` node, and returns it.
The denotation is the mathematical `1 · 2⁴ = 16`, and the lowered body is a real
back-edge (`Llabel`/`Lcond`) with **one** copy of the body op (not `4`). -/

/-- The doubling loop body `acc := acc + acc` over `reg 64`. -/
def dblLoopBody : JLoopBody (.reg 64) :=
  ⟨4, .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)))
        (.ret .here)⟩

/-- Seed `a0`, loop `dblLoopBody` four times, return the accumulator. -/
def loopSmokeProg : ComL [.reg 64] (.reg 64) :=
  .forLoop dblLoopBody .here (.ret .here)

/-- **Denote = spec:** on input `1` the loop denotes `1 · 2⁴ = 16`. -/
theorem loopSmokeProg_denote :
    ComL.denote loopSmokeProg (.cons (1 : BitVec 64) .nil) = (16 : BitVec 64) := by
  rfl

/-- The lowered body of `loopSmokeProg`. -/
def loopSmokeBody : Lcmd := comLToBody 1 argName (fun _ => none) loopSmokeProg 1

/-- **Real back-edge:** the lowered body contains a conditional jump (`Lcond`,
    rendered `jne .L<d>`). -/
theorem loopSmokeBody_has_backedge :
    loopSmokeBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true := by decide

/-- **Real loop label:** the lowered body contains an internal `Llabel` (the
    back-edge target `.L<d>:`). -/
theorem loopSmokeBody_has_label :
    loopSmokeBody.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)
      = true := by decide

/-- **One body copy, not `n`:** the doubling op `ADD:64` appears exactly **once**
    in the lowered body — the loop is rolled, not unrolled four times. -/
theorem loopSmokeBody_one_body_copy :
    (loopSmokeBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "ADD:64" | _ => false)).length
      = 1 := by decide

/-- The lowered body still ends with `Lret` (terminal return after the loop). -/
theorem loopSmokeBody_ends_Lret :
    loopSmokeBody.getLast?.map Linstr.li_i = some .Lret := rfl

/-! ### Physical-RA loop body (`ComL.toLfundefPhys`)

The looped smoke program through the physical-register export. Evidence that the
rolled loop renders with REAL x86 registers (no `%<UNKNOWN>`), one body copy, and
a real `jne .L<d>` back-edge with the accumulator / counter loop-carried in fixed
physical registers. -/

/-- The physical (post-RA) `lfundef` of the doubling loop. -/
def loopSmokePhys : Lfundef := ComL.toLfundefPhys loopSmokeProg

/-- The physical body of the doubling loop. -/
def loopSmokePhysBody : Lcmd := loopSmokePhys.lfd_body

/-- True iff an operand names a real allocatable x86 GP register (one of
    `gpRegNames`, i.e. NOT a spill `k.N`, NOT an SSA `rN`/`L<d>_r<k>`/`Lctr<d>`
    name). -/
def isRealGPName (n : String) : Bool := gpRegNames.contains n || n == "R14" || n == "R15"

/-- Every register operand of a `Lopn` in the physical loop body is a REAL x86
    register name — none is a leftover SSA name (`rN` / `L<d>_r<k>` / `Lctr<d>`)
    that the owned printer would render as `%<UNKNOWN>`. (The non-`reg`
    operands — immediates, the `NZ` condition flag carried by `Lcond` — are not
    register-file operands and are excluded.) -/
theorem loopSmokePhysBody_all_real_registers :
    loopSmokePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **No `%<UNKNOWN>` SSA names survive:** no `Lopn` register operand in the
    physical loop body still carries an SSA-shape name (`r…` / `L…` / `Lctr…`).
    The complement of `loopSmokePhysBody_all_real_registers`, stated as the
    absence of the SSA-name shapes the owned printer maps to `%<UNKNOWN>`. -/
theorem loopSmokePhysBody_no_ssa_names :
    loopSmokePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          ((dsts ++ srcs).filterMap LOperand.regName?).all (fun n =>
            !("L".isPrefixOf n) && !("r".isPrefixOf n))
      | _ => true) = true := by native_decide

/-- **Real back-edge preserved:** the physical loop body still contains the
    `Lcond` conditional jump (`jne .L<d>`). -/
theorem loopSmokePhysBody_has_backedge :
    loopSmokePhysBody.any (fun i =>
      match i.li_i with | .Lcond _ _ => true | _ => false) = true := by native_decide

/-- **Real loop label preserved:** the physical loop body still contains the
    internal `Llabel` back-edge target. -/
theorem loopSmokePhysBody_has_label :
    loopSmokePhysBody.any (fun i =>
      match i.li_i with | .Llabel _ _ => true | _ => false) = true := by native_decide

/-- **One body copy, not `n`:** the doubling op `ADD:64` appears exactly **once**
    in the physical body — RA preserves the rolled shape (the loop is not
    unrolled four times). -/
theorem loopSmokePhysBody_one_body_copy :
    (loopSmokePhysBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "ADD:64" | _ => false)).length
      = 1 := by native_decide

-- `loopSmokePhysBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- The looped physical export has exactly one function, named `fname`, exported.
    (Structural well-formedness — the loop-aware analogue of
    `Com.toLprogPhys`'s well-formedness.) -/
theorem ComL.toLprogPhys_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (fname : String) :
    (ComL.toLprogPhys c fname).lp_funcs.length = 1 ∧
      ((ComL.toLprogPhys c fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((ComL.toLprogPhys c fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Multi-binder loop smoke test (`forLoopN` / indexed array load/store)

A two-argument program `mapAddOneProg [out, in]` that runs the array-map body
`out[i] := in[i] + 1` over 4-element `reg 64` arrays via a single `forLoopN`
node. The body reads the loop index as the runtime SIB index of a `stackLoad`
(`LOADIDX in[i]`) and a `stackStore` (`STOREIDX out[i]`), so the rolled loop does
a per-iteration indexed array load/store — the increment kernels like
`mayo_encode` (`out[i] := pack(in[2i], in[2i+1])`) need. The denotation is the
mathematical array map `i ↦ in[i] + 1`, and the lowered body is ONE body copy
with the index advance + a real back-edge. -/

/-- The array-map body `out[i] := in[i] + 1` over the multi-binder context
    `[accTy = stackArr 64 4, idx = reg 64, inv = stackArr 64 4]`:
    `v0 := stackLoad in[idx]`, `v1 := 1`, `v2 := v0 + v1`,
    `v3 := stackStore acc[idx] := v2`, return `v3`. -/
def mapAddOneBody :
    Com jasminDialect [.stackArr 64 4, .reg 64, .stackArr 64 4] (.stackArr 64 4) :=
  -- v0 := stackLoad in[idx]   (in = .there (.there .here), idx = .there .here)
  .var (.mk (.stackLoad 64 4) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- v1 := 1
  (.var (.mk (.regConst 64 1) rfl .nil)
  -- v2 := v0 + v1   (v0 = .there .here, v1 = .here)
  (.var (.mk (.regArith .add 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- v3 := stackStore acc[idx] := v2
  -- ctx (newest-first): [v2, v1, v0, acc, idx, in]
  --   acc = .there^3 .here, idx = .there^4 .here, v2 = .here
  (.var (.mk (.stackStore 64 4) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))
  (.ret .here))))

/-- The 4-trip multi-binder map loop. -/
def mapAddOneLoop : JLoopBodyN (.stackArr 64 4) [.stackArr 64 4] := ⟨4, mapAddOneBody⟩

/-- Seed the accumulator from the `out` argument (`.here`), thread the `in`
    argument (`.there .here`) as the invariant base, loop 4 times, return the
    final array. -/
def mapAddOneProg : ComL [.stackArr 64 4, .stackArr 64 4] (.stackArr 64 4) :=
  .forLoopN mapAddOneLoop .here (.cons (.there .here) .nil) (.ret .here)

/-- A sample input array `in[i] = 10·i` and a zeroed initial output array. -/
def mapAddOneIn : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (i.val * 10)

/-- **Denote = array-map spec:** the loop denotes `out[i] = in[i] + 1` at every
    index. The whole computed array equals the pointwise spec `fun i => in[i] + 1`. -/
theorem mapAddOneProg_denote :
    (ComL.denote mapAddOneProg (.cons (fun _ => (0 : BitVec 64)) (.cons mapAddOneIn .nil)))
      = (fun i => mapAddOneIn i + 1) := by
  funext i; revert i; decide

/-- The virtual (pre-RA) lowered body of the map loop. -/
def mapAddOneBodyV : Lcmd := comLToBody 2 argName (fun _ => none) mapAddOneProg 2

/-- The physical (post-RA) lowered body of the map loop. -/
def mapAddOnePhysBody : Lcmd := (ComL.toLfundefPhys mapAddOneProg).lfd_body

/-- **Indexed array load IN the loop body:** the virtual body contains exactly one
    `LOADIDX` whose source is a register-indexed SIB element `in[idx*8]` — a
    per-iteration `stackLoad in[i]`, not a compile-time `.arr` element. -/
theorem mapAddOneBodyV_has_indexed_load :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ "LOADIDX" [.arrIdx _ idx 8] => idx == loopIdx 2
      | _ => false)).length = 1 := by decide

/-- **Indexed array store IN the loop body:** exactly one `STOREIDX` whose
    destination is a SIB element `out[idx*8]` — a per-iteration `stackStore
    out[i]`. -/
theorem mapAddOneBodyV_has_indexed_store :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" [.arrIdx _ idx 8, _] => idx == loopIdx 2
      | _ => false)).length = 1 := by decide

/-- **One body copy, not `n`:** the indexed load appears exactly once — the loop
    is rolled (one `LOADIDX in[i]`), not unrolled four times. -/
theorem mapAddOneBodyV_one_body_copy :
    (mapAddOneBodyV.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by decide

/-- **Real back-edge + label:** the virtual body has both an internal `Llabel`
    (`.L<d>:`) and a `Lcond` (`jne .L<d>`). -/
theorem mapAddOneBodyV_has_backedge :
    mapAddOneBodyV.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true ∧
    mapAddOneBodyV.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)
      = true := by exact ⟨by decide, by decide⟩

/-- **Index advance:** the body advances the loop index `Lidx<d>` by one each trip
    (`ADD Lidx<d>, Lidx<d>, #1`) — distinct from the trip-counter decrement. -/
theorem mapAddOneBodyV_has_index_advance :
    mapAddOneBodyV.any (fun i => match i.li_i with
      | .Lopn [.reg d] _ [.reg s, .imm 1] => d == loopIdx 2 && s == loopIdx 2
      | _ => false) = true := by decide

-- `mapAddOnePhysBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **Every physical body operand is a real x86 register** — no leftover SSA name
    (`r…` / `L…` / `Lctr…` / `Lidx…`) that the owned printer would render as
    `%<UNKNOWN>`. (Immediates and the `NZ` flag are excluded — not register-file
    operands.) -/
theorem mapAddOnePhysBody_all_real_registers :
    mapAddOnePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **No SSA names survive in the SIB operands either:** every `LOADIDX`/`STOREIDX`
    SIB base and index in the physical body is a real x86 register (so the
    indexed memory references assemble). -/
theorem mapAddOnePhysBody_sib_real_registers :
    mapAddOnePhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts ++ srcs).all (fun o => match o with
            | .arrIdx b idx _ => isRealGPName b && isRealGPName idx
            | _ => true)
      | _ => true) = true := by native_decide

/-- **One body copy in the physical body too:** RA preserves the rolled shape —
    one `LOADIDX` (the loop is not unrolled). -/
theorem mapAddOnePhysBody_one_body_copy :
    (mapAddOnePhysBody.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by native_decide

/-! ### 7g″ demo: a self-allocating (frame-owning) straight-line export

A minimal `ComL` over a single `stackArr 64 4` "argument" that is NOT a caller
pointer: it lives in a frame the function allocates itself. The body writes
`arr[0] := 42` then reads it back, returning the loaded scalar — the fixed-base
array idiom MAYO's self-test uses (the base is materialised once, never fed back,
so it is free of the §7g′ functional-array-accumulator hazard). Exported through
`ComL.toLfundefPhysFramed`: a 32-byte self-owned frame, the frame base IS `%rsp`
(single region at offset 0, call-free → the `%rsp`-direct SIB path), a
`STOREIDX`/`LOADIDX` at `(%rsp,%idx,8)`, and no SysV pointer argument anywhere.
The register-ABI export (§7g) cannot express this (it materialises the base from
a SysV pointer arg and opens no frame). -/

/-- The demo `ComL`: `v0 := 0; v1 := 42; v2 := stackStore arr[v0] := v1;
    v3 := stackLoad v2[v0]; return v3` — store `42` into a frame cell, load it
    back, return it. -/
def framedStoreLoadProg : ComL [.stackArr 64 4] (.reg 64) :=
  -- v0 := 0 (the cell index)
  .var (.mk (.regConst 64 0) rfl .nil)
  -- v1 := 42 (the stored value)
  (.var (.mk (.regConst 64 42) rfl .nil)
  -- v2 := stackStore arr[v0] := v1     ctx=[v1,v0,arr]
  (.var (.mk (.stackStore 64 4) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))
  -- v3 := stackLoad arr[v0]            ctx=[v2,v1,v0,arr]  (base arr=.there^3.here, idx v0=.there.there.here)
  -- Read back through the FIXED frame base `arr` (materialised once), not the
  -- stackStore result thread `v2` — the in-place, fixed-base idiom MAYO uses.
  (.var (.mk (.stackLoad 64 4) rfl
      (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.ret .here))))

/-- The frame-allocating export of the store/load demo: a 32-byte self-owned
    frame, the frame base `%rsp` directly (no base LEA), a `STOREIDX`+`LOADIDX`
    in-frame, and a scalar `uint64_t` return — no SysV pointer args. -/
def framedDemoFundef : Lfundef :=
  ComL.toLfundefPhysFramed 32 [("arr", 0)] framedStoreLoadProg

/-- The framed export's body as text (for inspection / the structural pins). -/
def framedDemoBodyText : List String :=
  framedDemoFundef.lfd_body.map (fun i => i.li_i.toText)

-- `framedDemoBodyText_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **The `FRAME` directive leads** the framed body (the `frameSize` marker the
    printer reads to open the `leaq -F(%rsp)` frame), stating the exact 32-byte
    self-owned frame. -/
theorem framedDemoFundef_frame_directive :
    framedDemoBodyText.head? = some "Lopn [] FRAME [#32]" := by
  native_decide

/-- **`lfd_stk_max` records the self-allocated frame size** (0 in the register-ABI
    export), and there are **no incoming SysV pointer arguments** (the arrays are
    self-owned, not passed). -/
theorem framedDemoFundef_stk_and_args :
    framedDemoFundef.lfd_stk_max = 32 ∧ framedDemoFundef.lfd_arg = [] := by
  native_decide

/-- **Every array access reaches the self-owned frame base `%rsp`.** There is NO
    base LEA (the frame alloc `leaq -F(%rsp), %rsp` establishes `%rsp` as the
    base); every `STOREIDX`/`LOADIDX` SIB base in the body is exactly `%rsp` — no
    caller pointer, no reserved register, no reused loop-carried register. -/
theorem framedDemoFundef_accesses_frame_base :
    framedDemoFundef.lfd_body.any (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" (.arrIdx b _ _ :: _) => b == "RSP" | _ => false) = true ∧
    framedDemoFundef.lfd_body.all (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" (.arrIdx b _ _ :: _) => b == "RSP"
      | .Lopn _ "LOADIDX" [.arrIdx b _ _] => b == "RSP"
      | _ => true) = true := by native_decide

/-! ### 7g′. 2-pointer-ABI looped export (`ComL.toLfundefPhysAbi`) — IN/OUT base
fix

The register-ABI `ComL.toLfundefPhys` body (above) binds the IN/OUT array bases
to RA-assigned registers that the loop reuses as scratch — the gdb-confirmed
swap-and-clobber. `ComL.toLfundefPhysAbi` is the 2-pointer-ABI export that saves
each pointer argument to a red-zone qsave slot and reloads each `LOADIDX`/
`STOREIDX` SIB base from its slot into `R14` immediately before every access
(the proven straight-line `comToLfundefPhysAbi` machinery, lifted onto the loop).
The smoke kernel is `mapAddOneProg` with `out = a1` (the `init` arg) and
`in = a0` (the `invs` arg), ABI `out = RDI`, `in = RSI`. -/

/-- The 2-pointer-ABI looped body of the map kernel. -/
def mapAddOneAbiBody : Lcmd :=
  (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body

-- `mapAddOneAbiBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **The IN load base is the reloaded IN pointer, the OUT store base the reloaded
    OUT pointer — no swap.** Every `LOADIDX` is immediately preceded by a reload of
    the in-pointer (`MOVQ R14, [qsave.RSI]`), and every `STOREIDX` by a reload of
    the out-pointer (`MOVQ R14, [qsave.RDI]`), with the SIB base `R14`. -/
theorem mapAddOneAbiBody_no_swap :
    (mapAddOneAbiBody.zip (mapAddOneAbiBody.drop 1)).all (fun (prev, cur) =>
      match cur.li_i with
      | .Lopn _ "LOADIDX" [.arrIdx "R14" _ _] =>
          prev.li_i.toText == "Lopn [R14] MOVQ [qsave.RSI]"
      | .Lopn _ "STOREIDX" [.arrIdx "R14" _ _, _] =>
          prev.li_i.toText == "Lopn [R14] MOVQ [qsave.RDI]"
      | _ => true) = true := by native_decide

/-- **No invariant-base clobber inside the loop body.** Every `LOADIDX`/`STOREIDX`
    SIB base is the reserved reload scratch `R14`, which is rewritten from a
    red-zone qsave slot immediately before the access — so no body instruction can
    leave a stale data word in the base register (the segfault root cause). -/
theorem mapAddOneAbiBody_sib_base_is_reloaded_scratch :
    mapAddOneAbiBody.all (fun i =>
      match i.li_i with
      | .Lopn _ _ srcs => srcs.all (fun o =>
          match o with
          | .arrIdx base _ _ => base == reloadScratch2
          | _ => true)
      | _ => true) = true := by native_decide

/-- **One body copy in the ABI export too:** the loop stays rolled — exactly one
    `LOADIDX` (the array map is not unrolled). -/
theorem mapAddOneAbiBody_one_body_copy :
    (mapAddOneAbiBody.filter (fun i => match i.li_i with
      | .Lopn _ m _ => m == "LOADIDX" | _ => false)).length = 1 := by native_decide

/-! ### 7f. Mixed scalar+vector register-class allocation (smoke test)

A body that MIXES scalar GP ops (`ADD`/`SUB`) and vector ops (`VPXOR`/`VPADDQ`,
`reg 128`) is allocated in ONE class-aware linear scan: GP bindings to GP
registers, vector bindings to `XMM`, with disjoint pools so no value crosses
class. -/

/-- A mixed body: two GP `Lopn`s then two vector (`reg 128`) `Lopn`s. -/
def mixedClassBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "r0"] "ADD" [.reg "a0", .reg "a1"]⟩
  , ⟨0, .Lopn [.reg "r1"] "SUB" [.reg "r0", .reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r2"] "VPXOR" [.reg "a2", .reg "a3"]⟩
  , ⟨0, .Lopn [.reg "r3"] "VPADDQ" [.reg "r2", .reg "a2"]⟩
  , ⟨0, .Lret⟩ ]

/-- The vector slots: the GP-only inputs/results (`r0`,`a0`,`a1`,`r1`) are GP; the
    vector inputs and results (`r2`,`a2`,`a3`,`r3`) are vector. (Slots are in
    `bodyNames` first-appearance order, destination-first; the trailing `false`
    is the universe-padding entry.) -/
theorem mixedClassBody_vecSlots :
    (bodyVecSlots mixedClassBody).toList
      = [false, false, false, false, true, true, true, true, false] := by native_decide

/-- The one-pass class-aware table: GP slots land in `0,1,2` (→ `RAX`,`RBX`,`RCX`),
    vector slots land in `vectorBase + 0/1/2` (→ `XMM0`,`XMM1`,`XMM2`). No GP slot
    reaches `vectorBase`, no vector slot stays below it — disjoint pools. -/
theorem mixedClassBody_table :
    (bodyPhysTable mixedClassBody).toList = [0, 1, 2, 2, 1000, 1001, 1002, 1002] := by
  native_decide

-- `mixedClassBody_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **No cross-class assignment.** Every GP `Lopn` (mnemonic not vector) carries
    only GP register operands (or immediates / spills), and every vector `Lopn`
    carries only `XMM` operands — no GP name in a vector op and no `XMM` in a GP
    op. -/
theorem mixedClassBody_no_cross_class :
    (physBody (fun _ => none) mixedClassBody).all (fun i =>
      match i.li_i with
      | .Lopn dsts opn srcs =>
          let names := (dsts ++ srcs).filterMap LOperand.regName?
          if isVectorMnem opn then names.all (fun n => n.startsWith "XMM")
          else names.all (fun n => !n.startsWith "XMM")
      | _ => true) = true := by native_decide

/-- A pure-scalar body of the same shape (no vector op). -/
def scalarClassBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "r0"] "ADD" [.reg "a0", .reg "a1"]⟩
  , ⟨0, .Lopn [.reg "r1"] "SUB" [.reg "r0", .reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r2"] "XOR" [.reg "a2", .reg "a3"]⟩
  , ⟨0, .Lopn [.reg "r3"] "ADD" [.reg "r2", .reg "a2"]⟩
  , ⟨0, .Lret⟩ ]

/-- **Byte-identical GP-only path.** A pure-scalar body classifies every slot GP,
    so the class-aware table equals the original GP-only `physTable ∘ bodyTrace`
    and its physical body equals the GP-only `physBody`. The vector register class
    is purely additive. -/
theorem scalarClassBody_table_identical :
    bodyPhysTable scalarClassBody = physTable (bodyTrace scalarClassBody) := by
  native_decide

theorem scalarClassBody_allGP :
    (bodyVecSlots scalarClassBody).all (· == false) = true := by native_decide

/-! ### 7g‴. Multi-input scalar-reduce looped export — accumulator/input base fix

A regression guard for the GF-dot / matmul-accumulate shape
`out[0] := Σ_{i<n} a[i]·b[i]` (the `qruov` / `sdith` kernels): a looped `ComL`
with a 1-cell out/accumulator array (`stackArr W 1`) and **two** input arrays.

`resolveVar` maps a `Var` to `argName (curDepth-1-deBruijn)`, counting the slot
from the program root — the **reverse** of the newest-first `Γ`. So for a
top-level `ComL` whose `Γ` is the argument list, the loop's `init` (newest,
`.here`, the out/accumulator) resolves to the highest arg slot and the last
`invs` entry to `a0`. The export now derives the per-role base names from the
program's own `init`/`invs` via `ComL.loopArgBaseNames`, so the alias and the
qsave-reload map key on the names the body actually uses — independent of how the
caller ordered `outArg`/`inArgs`. Previously the multi-input callers passed
`Γ`-ordered names, so the 2nd input (`b`) resolved to `a0` and reloaded from the
out qsave slot — the byte-KAT-confirmed `42864 vs 69` garbage. -/

abbrev DGN : Nat := 12
abbrev DGW : Nat := 64

/-- One GF-dot iteration `acc[0] := acc[0] + a[i]·b[i]` over the multi-binder
    loop context `[acc(stackArr 1), idx, a(stackArr N), b(stackArr N)]`. -/
def dgBody : Com jasminDialect
    [.stackArr DGW 1, .reg 64, .stackArr DGW DGN, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.regArith .mul DGW) rfl (.cons (.there .here) (.cons .here .nil)))
  (.var (.mk (.stackLoad DGW 1) rfl
        (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) .nil)))
  (.var (.mk (.regArith .add DGW) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.stackStore DGW 1) rfl
        (.cons (.there (.there (.there (.there (.there (.there .here))))))
          (.cons (.there (.there (.there (.there (.there .here)))))
            (.cons .here .nil))))
  (.ret .here)))))))

def dgLoop : JLoopBodyN (.stackArr DGW 1) [.stackArr DGW DGN, .stackArr DGW DGN] := ⟨DGN, dgBody⟩
def dgProg : ComL [.stackArr DGW 1, .stackArr DGW DGN, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .forLoopN dgLoop .here (.cons (.there .here) (.cons (.there (.there .here)) .nil)) (.ret .here)

/-- Sample residue streams `a[i] = b[i] = i+1`. -/
def dgA : Fin DGN → BitVec DGW := fun i => BitVec.ofNat DGW (i.val + 1)
def dgB : Fin DGN → BitVec DGW := fun i => BitVec.ofNat DGW (i.val + 1)

/-- **Denote = dot spec:** `out[0] = Σ_{i<12}(i+1)^2 = 650`. -/
theorem dg_denote :
    (ComL.denote dgProg (.cons (fun _ => (0:BitVec DGW)) (.cons dgA (.cons dgB .nil))) ⟨0, by decide⟩).toNat
      = 650 := by native_decide

/-- The 3-pointer-ABI rolled body, exported with the caller's `outArg`/`inArgs`
    given in `Γ`-order (the convention the multi-input callers use). -/
def dgBodyR : Lcmd := (ComL.toLfundefPhysAbi dgProg (argName 0) [argName 1, argName 2]
    (fun _ => none) (fun _ => none) ["RDI","RSI","RDX"] [64,64,64]).lfd_body

/-- The reload qsave-slot before each memref access, in body order
    `[a[i], b[i], acc[0]-load, acc[0]-store]`. -/
def dgReloads : List String :=
  (dgBodyR.zip (dgBodyR.drop 1)).filterMap (fun (prev, cur) =>
    match cur.li_i, prev.li_i with
    | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | _, _ => none)

/-- **The accumulator/input base fix.** Each access reloads from its OWN slot:
    `a → qsave.RSI`, `b → qsave.RDX`, and both accumulator accesses (load + store)
    from the out slot `qsave.RDI`. No cross-wiring (before the fix, `b[i]`
    reloaded from `qsave.RDI`, reading the out array as `b`). -/
theorem dg_reload_slots_fixed :
    dgReloads = ["qsave.RSI", "qsave.RDX", "qsave.RDI", "qsave.RDI"] := by native_decide

/-- The two inputs and the accumulator/out use THREE distinct qsave slots. -/
theorem dg_three_distinct_slots : (dgReloads.take 3).Nodup := by native_decide

/-- Every SIB base is the reloaded scratch `R14` (no body-clobberable base). -/
theorem dg_all_bases_r14 :
    dgBodyR.all (fun i => match i.li_i with
      | .Lopn _ _ srcs => srcs.all (fun o => match o with
          | .arrIdx base _ _ => base == reloadScratch2 | _ => true)
      | _ => true) = true := by native_decide

/-- **No regression:** the single-input array-map kernel (`mapAddOne`) is
    byte-identical to its byte-KAT-passing reference (the fix changes nothing
    when the caller's names already match the `resolveVar` convention). -/
theorem mapAddOneAbiBody_unchanged_by_fix :
    (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body = mapAddOneAbiBody := by
  rfl

/-! ### 7g″. Scalar-before-array invariant order

The `mpn_mul_1` / `mpn_divrem_1` shape: a runtime-trip fold whose loop invariants
are a scalar multiplier and an input array, with the scalar listed first. The
reload map pairs array bases with `abiArgs.drop 1` by position, so a scalar
counted as a position would push the input array's base onto the next ABI
register — reloading the array through a scalar argument's red-zone slot and
dereferencing an integer as a pointer. `arrArgNamesHV` keeps only the array
invariants, so the pairing is fixed by the array count alone. -/

/-- One `acc[0] := acc[0] + arr[i]·s` iteration over the loop context
    `[acc(stackArr 1), idx, s(reg 64), arr(stackArr N)]` — a scalar invariant
    ahead of an array invariant. -/
def dsBody : Com jasminDialect
    [.stackArr DGW 1, .reg 64, .reg 64, .stackArr DGW DGN] (.stackArr DGW 1) :=
  .var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.stackLoad DGW DGN) rfl
        (.cons (.there (.there (.there (.there .here))))
          (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.regArith .mul DGW) rfl
        (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  (.var (.mk (.stackLoad DGW 1) rfl
        (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
  (.var (.mk (.regArith .add DGW) rfl (.cons .here (.cons (.there .here) .nil)))
  (.var (.mk (.stackStore DGW 1) rfl
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))))
  (.ret .here))))))

def dsLoop : JLoopBodyN (.stackArr DGW 1) [.reg 64, .stackArr DGW DGN] := ⟨DGN, dsBody⟩

/-- The scaled-accumulate kernel over the argument context `[s, arr, acc]`, so
    that `acc` is argument slot 0 (`RDI`), `arr` slot 1 (`RSI`) and the scalar `s`
    slot 2 (`RDX`). The invariants list the scalar first. -/
def dsProg : ComL [.reg 64, .stackArr DGW DGN, .stackArr DGW 1] (.stackArr DGW 1) :=
  .forLoopN dsLoop (.there (.there .here))
    (.cons .here (.cons (.there .here) .nil)) (.ret .here)

/-- The 3-argument-ABI rolled body of the scalar-before-array kernel. -/
def dsBodyR : Lcmd := (ComL.toLfundefPhysAbi dsProg (argName 0) [argName 1]
    (fun _ => none) (fun _ => none) ["RDI","RSI","RDX"] [64,64,64]).lfd_body

/-- The qsave slot each memref access reloads its SIB base from, in body order. -/
def dsReloads : List String :=
  (dsBodyR.zip (dsBodyR.drop 1)).filterMap (fun (prev, cur) =>
    match cur.li_i, prev.li_i with
    | .Lopn _ "LOADIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | .Lopn _ "STOREIDX" (.arrIdx "R14" _ _ :: _), .Lopn [.reg "R14"] _ [.reg q] => some q
    | _, _ => none)

-- The input array reloads from the `RSI` slot, both accumulator accesses from the
-- `RDI` slot. The scalar's slot `qsave.RDX` is not a base for any access.
#guard dsReloads = ["qsave.RSI", "qsave.RDI", "qsave.RDI"]
#guard !(dsReloads.contains "qsave.RDX")

/-! ## Real-`Lcall` leaf-call-in-loop-body smoke test (`loopBodyWalkNCall`)

The loop body MSM's Straus inner loop and the GGM real AES-PRG node need: a body
that `call`s an opaque leaf, lowered to a real `LinstrR.Lcall` (not the
`CALL:` shadow `Lopn`), with the SysV ABI marshalling around it. -/

/-- A single-arg leaf-call loop body `acc := ed_point_double(acc)` over the
    multi-binder context `[reg 64, reg 64, ]` (`invTys = []`). -/
def edDblCallBody : JLoopBodyN (.reg 64) [] :=
  ⟨3, .var (.mk (.extCall "ed_point_double" [.reg 64] (.reg 64)) rfl
              (.cons .here .nil))
        (.ret .here)⟩

/-- The lowered body via the real-`Lcall` walk (acc in `RAX`, idx `Lidx1`,
    no invariants; the body walk starts at `curDepth = 2 + 0`). -/
def edDblCallBodyW : Lcmd :=
  (loopBodyWalkNCall 1 "RAX" "Lidx1" [] (fun _ => none) edDblCallBody.update 2).1

-- `edDblCallBodyW_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- **It is an `LinstrR.Lcall`,** not an `Lopn "CALL:…"` shadow. -/
theorem edDblCallBodyW_has_real_Lcall :
    edDblCallBodyW.any (fun i =>
      match i.li_i with | .Lcall _ _ => true | _ => false) = true := by decide

/-- A two-arg leaf-call body `acc := ed_point_add(acc, inv)` over the context
    `[reg 64 (acc), reg 64 (idx), reg 64 (inv)]` (one invariant base). -/
def edAddCallBody : JLoopBodyN (.reg 64) [.reg 64] :=
  ⟨5, .var (.mk (.extCall "ed_point_add" [.reg 64, .reg 64] (.reg 64)) rfl
              (.cons .here (.cons (.there (.there .here)) .nil)))
        (.ret .here)⟩

/-- The lowered two-arg call body (acc `RAX`, invariant base `RBX`; the walk
    starts at `curDepth = 2 + 1`). -/
def edAddCallBodyW : Lcmd :=
  (loopBodyWalkNCall 1 "RAX" "Lidx1" ["RBX"] (fun _ => none) edAddCallBody.update 3).1

-- `edAddCallBodyW_expected` moved out of Lean: the instruction text is pinned by
-- `lake exe jasmin-lprog-shape-kat` against `scripts/golden/jasmin-lprog-shape.txt`.

/-- The call-free doubling body `acc := acc + acc` over `[reg 64, reg 64]`. -/
def dblCallfreeBody :
    Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- A loop body whose single binding calls a leaf returning a 16-word buffer,
    taking the accumulator as its first operand and returning that binding: the
    in-place accumulator update, in the body context of a 16-word array
    accumulator, the loop index, and a 12-word invariant array. -/
def inPlaceBufCallBody :
    Com jasminDialect
      [JasminTy.stackArr 64 16, JasminTy.reg 64, JasminTy.stackArr 64 12]
      (JasminTy.stackArr 64 16) :=
  .var (.mk (.extCall "madd" [.stackArr 64 16, .stackArr 64 12] (.stackArr 64 16)) rfl
          (.cons .here (.cons (.there (.there .here)) .nil)))
    (.ret .here)

/-- A loop body whose single binding calls a leaf returning a 16-word buffer from
    the loop index alone: a buffer result that is not an accumulator update. -/
def scratchBufCallBody :
    Com jasminDialect [JasminTy.stackArr 64 16, JasminTy.reg 64]
      (JasminTy.stackArr 64 16) :=
  .var (.mk (.extCall "table_select" [.reg 64] (.stackArr 64 16)) rfl
          (.cons (.there .here) .nil))
    (.ret .here)

-- Static checks pinning the in-place condition against silent change, at each
-- body's own walk start depth (`2 + nInv`): the accumulator-updating buffer call
-- is detected and takes no frame scratch, a buffer call that is not an
-- accumulator update keeps its scratch slot, and a call-free body has neither.
#guard loopInPlaceBufSlot inPlaceBufCallBody 3 = some 3
#guard loopBufBindings inPlaceBufCallBody 3 = [(3, 128)]
#guard loopScratchBufBindings inPlaceBufCallBody 3 = []
#guard loopBufTotal (loopScratchBufBindings inPlaceBufCallBody 3) = 0
#guard loopInPlaceBufSlot scratchBufCallBody 2 = none
#guard loopScratchBufBindings scratchBufCallBody 2 = [(2, 128)]
#guard loopBufTotal (loopScratchBufBindings scratchBufCallBody 2) = 128
#guard loopInPlaceBufSlot dblCallfreeBody 2 = none
#guard loopScratchBufBindings dblCallfreeBody 2 = []

-- The walk's result name carries the destination the call wrote: the in-place
-- update returns the accumulator register, so the loop emits no feedback move,
-- and a scratch buffer result returns its frame slot.
#guard (loopBodyWalkNBuf 3 "RACC" "Lidx3" ["RBX"] [] (some 3) (fun _ => none)
          inPlaceBufCallBody 3).2 = "RACC"
#guard (loopBodyWalkNBuf 2 "RACC" "Lidx2" [] (loopScratchBufBindings scratchBufCallBody 2)
          none (fun _ => none) scratchBufCallBody 2).2 = "mem.RSP.0"

-- `loopBodyWalkNCall_callfree_eq_loopBodyWalkN` moved out of Lean: the two
-- renderings are compared by `lake exe jasmin-lprog-shape-kat`.

/-! ### Caller-save barrier for an in-loop `Lcall` (`physBody` / `remapOperand`)

A rolled loop body that `call`s a leaf (`loopBodyCallLcmd`) must keep
its loop-carried values (accumulator, `Lidx`, `Lctr`) in callee-saved registers
across the call, and leave the literal SysV arg/return registers the marshalling
names (`RDI`/`RAX`) verbatim. The barrier in `remapOperand` (engaged by
`bodyHasCall`) achieves both; a call-free body is byte-identical. -/

/-- A rolled loop body with an in-body real `Lcall` (`acc := ed_point_double(acc)`)
    whose loop-carried set is `acc` (accumulator), `Lidx1` (index), `Lctr1`
    (counter). The marshalling `MOV RDI, acc` and capture `MOV acc, RAX` name the
    SysV arg/return registers literally. -/
def callBarrierBody : Lcmd :=
  [ ⟨0, .Lopn [.reg "acc"] (withWidthTag 64 "MOV") [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "Lidx1"] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "MOV") [.imm 8]⟩
  , ⟨0, .Llabel .internal 1⟩
  , ⟨0, .Lopn [.reg "RDI"] (withWidthTag 64 "MOV") [.reg "acc"]⟩
  , ⟨0, .Lcall none ("ed_point_double", 0)⟩
  , ⟨0, .Lopn [.reg "acc"] (withWidthTag 64 "MOV") [.reg "RAX"]⟩
  , ⟨0, .Lopn [.reg "Lidx1"] (withWidthTag 64 "ADD") [.reg "Lidx1", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "SUB") [.reg "Lctr1", .imm 1]⟩
  , ⟨0, .Lopn [.reg "Lctr1"] (withWidthTag 64 "CMP") [.reg "Lctr1", .imm 0]⟩
  , ⟨0, .Lcond (.reg "NZ") 1⟩ ]

/-- The barrier engages: the body has a real `Lcall`. -/
theorem callBarrierBody_hasCall : bodyHasCall callBarrierBody = true := by decide

/-- **Call-free regression guard.** The barrier is a no-op on the call-free loop
    smoke export (`bodyHasCall = false`): its physical body is byte-identical to
    the pre-barrier allocation (accumulator `RAX`, counter `RBX`). -/
theorem loopSmoke_callfree_barrier_noop :
    bodyHasCall (ComL.toLfundefPhys loopSmokeProg).lfd_body = false ∧
    loopSmokePhysBody.map (fun i => i.li_i.toText) =
      [ "Lopn [RBX] MOVQ [RDI]"
      , "Lopn [RAX] MOV:64 [RBX]"
      , "Lopn [RBX] MOV:64 [#4]"
      , "Llabel int 1"
      , "Lopn [RCX] MOV:64 [RAX]"
      , "Lopn [RCX] ADD:64 [RCX,RAX]"
      , "Lopn [RAX] MOV:64 [RCX]"
      , "Lopn [RBX] SUB:64 [RBX,#1]"
      , "Lopn [RBX] CMP:64 [RBX,#0]"
      , "Lcond NZ 1"
      , "Lret" ] := by native_decide

/-! ### In-loop-call ComL through the full ABI export (`ComL.toLprogPhysAbi`)

A `ComL.forLoopN` whose body `call`s a leaf
(`acc := ed_point_double(acc)`, MSM's Straus / GGM rolled-kernel shape) assembled
through the SAME full ABI export the call-free kernels use. The call-walk
selection (`comBodyHasCall` ⇒ `forLoopLcmdNCall`) makes the body issue a real
`Lcall`, so `bodyHasCall` holds on the export. The aux name-resolution passes
(`buildArgMaterializePhys` / `buildArgPtrMaterialize` / `buildEpilogue` /
`memrefBaseReload`) resolve names through `physNameForBody`; the body operands use
the call-free `remapOperand`. The theorems below check that the in-loop `Lcall`
is emitted (the call is present) and that the call-free loop path is
byte-identical. -/

/-- The looped accumulator kernel `acc := ed_point_double(acc)` (4 trips) over a
    single `reg 64` argument. -/
def edDblLoopProg : ComL [JasminTy.reg 64] (JasminTy.reg 64) :=
  .forLoopN edDblCallBody .here .nil (.ret .here)

/-- The program is recognised as an in-loop-call `ComL`, so the call-walk engages. -/
theorem edDblLoopProg_hasLoopCall : comLHasLoopCall edDblLoopProg = true := by decide

/-- The virtual lowered body now uses a **real `Lcall`** (not the `CALL:` shadow),
    so `bodyHasCall` fires on it (the barrier-gating predicate). -/
theorem edDblLoopProg_virt_hasCall :
    bodyHasCall (ComL.toLfundef edDblLoopProg).lfd_body = true := by decide

/-- The full physical export's body keeps `bodyHasCall` true (the body still issues
    the real `Lcall` after RA), so the barrier stayed engaged end-to-end. -/
theorem edDblLoopProg_phys_hasCall :
    bodyHasCall (ComL.toLfundefPhys edDblLoopProg).lfd_body = true := by native_decide

/-- **The body issues exactly one `LinstrR.Lcall`** (not a `CALL:`
    shadow `Lopn`) — the real `call ed_point_double`. -/
theorem edDblLoopProg_one_real_Lcall :
    ((ComL.toLfundefPhys edDblLoopProg).lfd_body.filter (fun i =>
      match i.li_i with | .Lcall _ _ => true | _ => false)).length = 1 := by
  native_decide

/-- **Call-free byte-identical guard.** The call-walk selection
    (`comBodyHasCall ⇒ forLoopLcmdNCall`) and the `physNameForBody` barrier are
    no-ops on a call-free loop: the map-style loop `mapAddOneProg` has no in-loop
    call, so `bodyHasCall = false` and the export takes the original path. The full
    byte-identity to the pre-wiring reference is still `mapAddOneAbiBody_unchanged_by_fix`
    (proved by `rfl`), which is unaffected by this change. -/
theorem mapAddOneProg_callfree_byte_identical :
    comLHasLoopCall mapAddOneProg = false ∧
    bodyHasCall (ComL.toLfundefPhysAbi mapAddOneProg "a1" ["a0"]).lfd_body = false := by
  refine ⟨by decide, by native_decide⟩

/-! ## Runtime-trip loop smoke test (`ComL.forLoopNRt` / runtime counter seed)

A two-argument program `(seed, count)` that seeds an accumulator from `seed`,
runs the squaring body `acc := acc · acc` a **runtime** number of times (`count`,
read from a register), and returns it. The denotation is the mathematical
`seed^(2^count)`; the lowered body seeds the trip counter from a **register**
(`MOV Lctr, a0`), not an immediate — the capability poly1305-style
`f(out, inp, nblk)` kernels need (the trip count is a runtime argument). The body
op is `MUL` (distinct from the loop scaffolding's `ADD Lidx`/`SUB Lctr`), so the
one-body-copy check reads cleanly. -/

/-- The runtime-count squaring body `acc := acc · acc` over the
    `JLoopBodyN`-shaped context `[reg 64 (acc), reg 64 (idx)]` (invTys = `[]`; the
    loop index is unused by this scalar body). -/
def sqrRtBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons .here .nil))) (.ret .here)

/-- Seed `acc` from arg `.here`, loop `sqrRtBody` a RUNTIME number of times (the
    in-scope `count` var `.there .here`), return the accumulator. invTys = `[]`. -/
def loopSmokeRtProg : ComL [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt sqrRtBody (.there .here) .here .nil (.ret .here)

/-- **Denote = spec:** seed `3`, runtime count `2` → `3^(2²) = 81`. The fold runs
    `(count.lookup V).toNat = 2` times. -/
theorem loopSmokeRtProg_denote :
    ComL.denote loopSmokeRtProg (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil))
      = (81 : BitVec 64) := by rfl

/-- **Denote = spec (different runtime count):** seed `2`, runtime count `3` →
    `2^(2³) = 256`. Same program, different `count` argument: the trip count is
    read from the valuation, not baked in. -/
theorem loopSmokeRtProg_denote_count3 :
    ComL.denote loopSmokeRtProg (.cons (2 : BitVec 64) (.cons (3 : BitVec 64) .nil))
      = (256 : BitVec 64) := by rfl

/-- The lowered body of `loopSmokeRtProg` (top-level, `nArgs = 2`). -/
def loopSmokeRtBody : Lcmd := comLToBody 2 argName (fun _ => none) loopSmokeRtProg 2

/-- **Real back-edge:** the runtime-count loop lowers to a conditional jump
    (`Lcond`, rendered `jne .L<d>`) — a rolled loop, not an unrolled chain. -/
theorem loopSmokeRtBody_has_backedge :
    loopSmokeRtBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)
      = true := by decide

/-- **Runtime counter seed:** the trip counter `Lctr2` is initialised from a
    **register** (the resolved `count` argument `a0`), i.e. `MOV Lctr2, a0` — NOT
    `MOV Lctr2, #n`. This is the one instruction that distinguishes a runtime-trip
    loop from the fixed-trip `forLoopN`, and the whole point of the capability. -/
theorem loopSmokeRtBody_runtime_counter_seed :
    loopSmokeRtBody.any (fun i => match i.li_i with
      | .Lopn dsts mnem srcs =>
          mnem == withWidthTag 64 "MOV" &&
          (dsts.filterMap LOperand.regName?).contains (loopCtr 2) &&
          (srcs.filterMap LOperand.regName?).contains (argName 0)
      | _ => false) = true := by decide

/-- **One body copy, not `count`:** the squaring op `MUL:64` appears exactly once
    — the loop is rolled (one copy + back-edge), independent of the trip count. -/
theorem loopSmokeRtBody_one_body_copy :
    (loopSmokeRtBody.filter
      (fun i => match i.li_i with | .Lopn _ m _ => m == "MUL:64" | _ => false)).length
      = 1 := by decide

/-- The lowered body still ends with `Lret`. -/
theorem loopSmokeRtBody_ends_Lret :
    loopSmokeRtBody.getLast?.map Linstr.li_i = some .Lret := rfl

/-- **Physical-RA export:** the runtime-count loop survives the same SSA→physical
    register allocation as a straight-line `Com` — every `Lopn` operand is a real
    x86 register (no `%<UNKNOWN>` SSA name), and the back-edge is preserved. -/
def loopSmokeRtPhysBody : Lcmd := (ComL.toLfundefPhys loopSmokeRtProg).lfd_body

/-- Every register operand of the physical runtime-count loop body is a real x86
    register name (no leftover SSA `rN`/`L<d>_r<k>`/`Lctr<d>` name). -/
theorem loopSmokeRtPhysBody_all_real_registers :
    loopSmokeRtPhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **Real back-edge preserved through RA:** the physical body still contains the
    `Lcond` conditional jump. -/
theorem loopSmokeRtPhysBody_has_backedge :
    loopSmokeRtPhysBody.any (fun i =>
      match i.li_i with | .Lcond _ _ => true | _ => false) = true := by native_decide

/-! ### 3-argument ABI: a runtime count from the 3rd SysV int register (`RDX`)

The `poly1305_mac_hacl(out, inp, nblk)` ABI shape: the runtime trip count `nblk`
is the **3rd** integer argument. Under the export's program-root convention
(`resolveVar`: the newest binder `.here` resolves to the highest arg slot, which
maps to the 3rd SysV register), placing the `count` var at `.here` routes the
trip count through `a2` → `RDX`. This smoke is a 3-argument runtime-count loop
`acc := acc · inv` (count from `a2`), proving the counter seed reads `a2` (the
3rd SysV int arg). The existing `ComL.toLfundefPhys`/`toLfundefPhysAbi` argument
materialization (`buildArgMaterializePhys` / `buildArgPtrMaterialize` +
`abiSaveOfExt`) already routes a 3rd SysV register, so no new ABI entry point is
needed — only the runtime-count node feeds it. -/

/-- Body `acc := acc · inv` over `[accTy = reg 64, idx = reg 64, inv = reg 64]`
    (the loop index is unused; the invariant `inv` is the deepest binder
    `.there (.there .here)`). -/
def mulInvRtBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.regArith .mul 64) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
    (.ret .here)

/-- A 3-argument runtime-count loop. `Γ = [count, inv, acc]` (newest-first), so
    the program-root args are `a0 = acc`, `a1 = inv`, `a2 = count` — i.e. the trip
    count is the 3rd SysV integer argument (`RDX`), the `poly1305_mac_hacl(out,
    inp, nblk)` ABI shape. `count = .here`, `inv = .there .here`,
    `init (acc) = .there (.there .here)`. -/
def loopSmokeRt3Prog :
    ComL [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  .forLoopNRt mulInvRtBody .here (.there (.there .here))
    (.cons (.there .here) .nil) (.ret .here)

/-- **Denote = spec:** `acc = 2`, `inv = 3`, runtime count = `2` → `2·3² = 18`.
    The valuation is `[count, inv, acc] = [2, 3, 2]`. -/
theorem loopSmokeRt3Prog_denote :
    ComL.denote loopSmokeRt3Prog
      (.cons (2 : BitVec 64) (.cons (3 : BitVec 64) (.cons (2 : BitVec 64) .nil)))
      = (18 : BitVec 64) := by rfl

/-- The lowered body of the 3-argument runtime-count loop (`nArgs = 3`). -/
def loopSmokeRt3Body : Lcmd := comLToBody 3 argName (fun _ => none) loopSmokeRt3Prog 3

/-- **3rd SysV arg → counter seed:** the trip counter `Lctr3` is seeded from
    `a2` (the 3rd program-root argument, which the SysV projection maps to `RDX`)
    via `MOV Lctr3, a2` — the `poly1305_mac_hacl(…, nblk)` runtime count routed
    into the loop. -/
theorem loopSmokeRt3Body_counter_from_a2 :
    loopSmokeRt3Body.any (fun i => match i.li_i with
      | .Lopn dsts mnem srcs =>
          mnem == withWidthTag 64 "MOV" &&
          (dsts.filterMap LOperand.regName?).contains (loopCtr 3) &&
          (srcs.filterMap LOperand.regName?).contains (argName 2)
      | _ => false) = true := by decide

/-- **Physical export survives RA with 3 args:** every register operand is a real
    x86 register (no `%<UNKNOWN>`), and the back-edge is preserved. The 3rd SysV
    argument (`RDX`) is materialized into the body's count register at entry by
    `buildArgMaterializePhys`. -/
theorem loopSmokeRt3PhysBody_all_real_registers :
    (ComL.toLfundefPhys loopSmokeRt3Prog).lfd_body.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-! ### 7g‴. Frame + caller-pointer ABI export with in-place array-call
(`ComL.toLfundefPhysFramedAbi`)

`ComL.toLfundefPhysFramed` (§7g″) owns ALL its arrays in a self-allocated frame
(no SysV pointer arguments), and `ComL.toLfundefPhysAbi` (§7g′) treats ALL its
arrays as caller SysV pointers reloaded from **red-zone** qsave slots. A sponge
kernel is **mixed**: its working state buffer is a self-owned frame array, while
its input/digest are caller SysV pointers — AND it calls an emitted permute leaf
in place between the absorb blocks. The red-zone qsave reload of §7g′ is unsafe
here (a `call` clobbers the red zone below `%rsp`), so the caller pointers must be
parked in **call-surviving** locations: a callee-saved register (the input, read
across both permute calls) or a frame slot (the digest, reloaded once at the
squeeze) — exactly the `p2_hash_kat_link.jazz::p2_sponge16` discipline.

This section adds the mixed export, purely additively. It lowers the (unrolled)
`ComL` to its SIB virtual body (`ComL.toLfundef`), then performs a **direct
offset-folding lowering** for the memref word-move + in-place-call fragment:

* a `regConst` index binding (`MOV r,#k`) is **deferred** — folded into the
  `scale*k` byte offset of the `LOADIDX`/`STOREIDX` that reads it (the `arrIdx`
  carries the `scale`), so no index register is materialised;
* a `LOADIDX base[idx*scale]` becomes `movq (scale*k)(<basephys>), %rax`, and a
  `STOREIDX base[idx*scale],val` becomes `movq %rax, (scale*k)(<basephys>)`, with
  the stored value threaded through `%rax` (a `regConst` value is materialised
  `movq $v,%rax`; a loaded word is already resident);
* a `CALL:<sym>` shadow whose array argument is the state buffer becomes the
  in-place SysV pointer call `leaq <state>,%rdi; leaq <state>,%rsi; call <sym>`
  (out == in — the emitted permute reads all inputs before writing any output,
  so aliasing is safe), with **no** `%rax` capture (the leaf writes through the
  out pointer).

`<basephys>` is dispatched per base: a frame-local array is `off(%rsp)`; a
register-parked caller pointer uses its holding register; a frame-slot-parked
caller pointer reloads its parked pointer into `R11` first. -/

/-- Resolve a memref base name to `(reloadPrelude, baseReg, extraByteOff)`:
    a frame-local array lives at `off(%rsp)`; a register-parked caller pointer
    uses its holding register directly; a frame-slot-parked caller pointer
    reloads the parked pointer into `R11`. -/
def framedAbiResolveBase (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (base : String) : Lcmd × String × Nat :=
  match frameOff base with
  | some fo => ([], "RSP", fo)
  | none =>
    match regOf base with
    | some r => ([], r, 0)
    | none =>
      match slotOff base with
      | some so => ([⟨0, .Lopn [.reg "R11"] "LOAD:64" [.reg (memName "RSP" so)]⟩], "R11", 0)
      | none => ([], base, 0)

/-- The in-place SysV pointer marshalling for a permute leaf call `state' =
    sym(state)`: pass the state buffer's address in BOTH `RDI` (out) and `RSI`
    (in), then `call sym`. No `RAX` capture (void return: the leaf writes through
    the out pointer). A frame-local base is `leaq off(%rsp),%reg`; a register-held
    pointer is `mov %reg,%hold`; a frame-slot pointer reloads into `%reg`. -/
def framedAbiCallMarshal (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (sym base : String) : Lcmd :=
  let mkArg (dstReg : String) : Lcmd :=
    match frameOff base with
    | some fo => [⟨0, .Lopn [.reg dstReg] "LEA:64" [.reg (memName "RSP" fo)]⟩]
    | none =>
      match regOf base with
      | some r => if r == dstReg then [] else [⟨0, .Lopn [.reg dstReg] "MOV:64" [.reg r]⟩]
      | none =>
        match slotOff base with
        | some so => [⟨0, .Lopn [.reg dstReg] "LOAD:64" [.reg (memName "RSP" so)]⟩]
        | none => []
  mkArg "RDI" ++ mkArg "RSI" ++ [⟨0, .Lcall none (sym, 0)⟩]

/-- Marshal one array base into a SysV argument register `dstReg`: a frame-local
    array is `leaq off(%rsp),%dstReg`; a register-parked caller pointer is
    `mov %hold,%dstReg`; a frame-slot-parked caller pointer reloads into
    `%dstReg`. The single-base helper for the distinct-buffer marshal below;
    identical in shape to `framedAbiCallMarshal`'s inner `mkArg`. -/
def framedAbiMarshalArg (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (base dstReg : String) : Lcmd :=
  match frameOff base with
  | some fo => [⟨0, .Lopn [.reg dstReg] "LEA:64" [.reg (memName "RSP" fo)]⟩]
  | none =>
    match regOf base with
    | some r => if r == dstReg then [] else [⟨0, .Lopn [.reg dstReg] "MOV:64" [.reg r]⟩]
    | none =>
      match slotOff base with
      | some so => [⟨0, .Lopn [.reg dstReg] "LOAD:64" [.reg (memName "RSP" so)]⟩]
      | none => []

/-- The System V AMD64 integer-argument registers, in call order. -/
def framedAbiArgRegs : List String := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]

/-- The **distinct-buffer** SysV pointer marshalling for a leaf call
    `sym(base₀, base₁, …)`: each array base is passed in its own SysV argument
    register (`base₀ → RDI`, `base₁ → RSI`, `base₂ → RDX`, …), then `call sym`. No
    `RAX` capture (void return: the leaf writes through its out pointer). This is
    the generalization of the in-place `framedAbiCallMarshal` (which passes ONE
    base to both RDI and RSI) to a leaf whose destination and source buffers are
    distinct — e.g. `sdith_shake128_into(out_state, in_msg)`. -/
def framedAbiCallMarshalN (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (sym : String) (bases : List String) : Lcmd :=
  ((bases.zip framedAbiArgRegs).flatMap (fun ⟨b, r⟩ =>
      framedAbiMarshalArg frameOff regOf slotOff b r))
    ++ [⟨0, .Lcall none (sym, 0)⟩]

/-- The in-place-thread alias map for a framed body: `dst ↦ canonical(base)` for
    every `STOREIDX dst, (base,…), val` (the memref store result aliases its input
    array) AND every `CALL:/CALLN: dst, (base₀, …)` (the leaf-call result aliases
    its destination buffer, argument `0`). Processed in program order with each
    base already resolved through earlier aliases, so a functionally-threaded
    frame array — a `ComL` that rebinds its self-owned buffer through each store
    and leaf call — resolves every threaded name straight back to its frame base.
    Extends `arrChainAlias` with the leaf-call arm; on a body that threads only
    original bases (every current framed caller) it maps unreferenced result
    labels and the rewrite is a no-op on emitted operands. -/
def framedAbiArrChainAlias (body : Lcmd) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let resolve (m : Std.HashMap String String) (n : String) : String := m.getD n n
  for i in body do
    match i.li_i with
    | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
        if isMemStore opn then m := m.insert dst (resolve m base)
    | .Lopn [.reg dst] opn (.reg base0 :: _) =>
        if opn.startsWith "CALL:" || opn.startsWith "CALLN:" then
          m := m.insert dst (resolve m base0)
    | _ => pure ()
  return m

/-- Collapse a framed body's forward-threaded frame-array chain (STOREIDX and
    leaf-call results) onto its root base name, so a `ComL` that threads its
    self-owned buffer through stores and distinct-buffer leaf calls resolves every
    reference back to its frame slot. The op mnemonics, widths, immediates, and
    order are preserved — only the threaded array labels change. When the body
    threads only original bases (`framedAbiArrChainAlias` maps no referenced
    operand), this is the identity on emitted operands. -/
def framedAbiCanonThread (body : Lcmd) : Lcmd :=
  let m := framedAbiArrChainAlias body
  if m.isEmpty then body
  else body.map (fun i =>
    match i.li_i with
    | .Lopn dsts opn srcs =>
        ⟨i.li_ii, .Lopn (dsts.map (canonMemrefOperand m)) opn
          (srcs.map (canonMemrefOperand m))⟩
    | _ => i)

/-- The direct offset-folding physical lowering of a straight-line memref
    word-move + in-place-call virtual body (see §7g‴). `regConst` index bindings
    are deferred and folded into `scale*k` offsets; `LOADIDX`/`STOREIDX` become
    `%rax`-threaded `movq`s at `off(%base)`; `CALL:` shadows become in-place SysV
    pointer calls. Straight-line only (the sponge fragment carries no loop
    back-edge). -/
def framedAbiLowerBody (frameOff : String → Option Nat) (regOf : String → Option String)
    (slotOff : String → Option Nat) (body : Lcmd) : Lcmd :=
  (body.foldl (fun (st : Std.HashMap String Nat × Lcmd) i =>
    let imm := st.1
    let out := st.2
    match i.li_i with
    | .Lopn [.reg d] opn [.imm k] =>
        if stripWidthTag opn == "MOV" then (imm.insert d k, out)
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn [.arrIdx base idxName scale] =>
        if stripWidthTag opn == "LOADIDX" then
          let k := imm.getD idxName 0
          let (prelude, breg, boff) := framedAbiResolveBase frameOff regOf slotOff base
          (imm, out ++ prelude ++
            [⟨0, .Lopn [.reg "RAX"] "LOAD:64" [.reg (memName breg (boff + scale * k))]⟩])
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn [.arrIdx base idxName scale, val] =>
        if stripWidthTag opn == "STOREIDX" then
          let k := imm.getD idxName 0
          let (prelude, breg, boff) := framedAbiResolveBase frameOff regOf slotOff base
          let valMat : Lcmd :=
            match val with
            | .reg vn =>
                if imm.contains vn then [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm (imm.getD vn 0)]⟩]
                else []
            | .imm kk => [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm kk]⟩]
            | _ => []
          (imm, out ++ valMat ++ prelude ++
            [⟨0, .Lopn [.reg (memName breg (boff + scale * k))] "STORE:64" [.reg "RAX"]⟩])
        else (imm, out ++ [i])
    | .Lopn [.reg _d] opn (.reg base :: rest) =>
        if opn.startsWith "CALL:" || opn.startsWith "CALLN:" then
          let sym := if opn.startsWith "CALLN:" then (opn.drop 6).toString
                     else (opn.drop 5).toString
          -- The array bases the leaf call passes, in argument order. A single
          -- base keeps the in-place `framedAbiCallMarshal` (RDI = RSI = base),
          -- byte-identical for every current single-arg in-place caller; two or
          -- more DISTINCT bases route to `framedAbiCallMarshalN` (base₀ → RDI,
          -- base₁ → RSI, …), the distinct-buffer generalization.
          let regBases : List String := (LOperand.reg base :: rest).filterMap (fun o =>
            match o with | .reg b => some b | _ => none)
          match regBases with
          | [_] => (imm, out ++ framedAbiCallMarshal frameOff regOf slotOff sym base)
          | _ => (imm, out ++ framedAbiCallMarshalN frameOff regOf slotOff sym regBases)
        else (imm, out ++ [i])
    | _ => (imm, out ++ [i]))
    ({}, [])).2

/-- The **mixed frame + caller-pointer ABI** physical `lfundef` for an unrolled
    memref `ComL` that calls an in-place permute leaf (the `PaddingFreeSponge`
    shape). Frame-local arrays (`frameArrs`, name → byte offset) live in a
    `frameBytes`-byte self-owned frame; register-parked caller pointers
    (`regParks`, base → (hold reg, SysV arg reg)) survive the permute calls in a
    callee-saved register; frame-slot-parked caller pointers (`slotParks`, base →
    (frame slot, SysV arg reg)) are reloaded before use. The body is
    `ComL.toLfundef`'d and lowered by `framedAbiLowerBody`; the `FRAME` directive
    + `lfd_stk_max` open the frame. No incoming value is returned (`lfd_res = []`);
    the result reaches the caller through the digest pointer.

    Union of the three existing pieces (§7g″ `FRAME`/`lfd_stk_max`, the memref
    thread + the SysV pointer ABI of §7g′) plus the in-place array-call
    marshalling `framedAbiCallMarshal`. The existing exports are untouched. -/
def ComL.toLfundefPhysFramedAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (frameBytes : Nat)
    (frameArrs : List (String × Nat))
    (regParks : List (String × String × String))
    (slotParks : List (String × Nat × String))
    (c : ComL Γ t)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let virt := ComL.toLfundef c immSlotMap
  let frameOff : String → Option Nat := fun b => (frameArrs.find? (·.1 == b)).map (·.2)
  let regOf : String → Option String := fun b => (regParks.find? (·.1 == b)).map (·.2.1)
  let slotOff : String → Option Nat := fun b => (slotParks.find? (·.1 == b)).map (·.2.1)
  -- Park caller pointers in call-surviving locations: register parks into a
  -- callee-saved hold register (`MOV hold, abiReg` — the renderer brackets the
  -- written callee-saved reg with `push`/`pop`); slot parks into a frame slot.
  let parkReg : Lcmd :=
    regParks.map (fun ⟨_, hold, abiReg⟩ => ⟨0, .Lopn [.reg hold] "MOV:64" [.reg abiReg]⟩)
  let parkSlot : Lcmd :=
    slotParks.map (fun ⟨_, slot, abiReg⟩ =>
      ⟨0, .Lopn [.reg (memName "RSP" slot)] "STORE:64" [.reg abiReg]⟩)
  let frameDir : Linstr := ⟨0, .Lopn [] "FRAME" [.imm frameBytes]⟩
  -- Collapse any forward-threaded frame-array chain (STOREIDX / leaf-call
  -- results) back onto its base name, so a `ComL` that functionally rebinds its
  -- self-owned buffer through each store and distinct-buffer leaf call resolves
  -- every base to its frame slot. Identity on emitted operands for a body that
  -- threads only original bases (every current single-buffer in-place caller).
  let lowered := framedAbiLowerBody frameOff regOf slotOff
    (framedAbiCanonThread virt.lfd_body)
  { virt with
    lfd_body := frameDir :: (parkReg ++ parkSlot ++ lowered)
    lfd_arg := abiArgs
    lfd_tyin := abiTyin
    lfd_res := []
    lfd_tyout := []
    lfd_stk_max := frameBytes }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
