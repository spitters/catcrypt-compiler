/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Types
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhys
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Liveness
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Examples

/-!
# Jasmin `Linear.lprog` value-level producer

Link 1/7 of the linear-jasmin backend. This module turns a typed
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
shipped accepts the Marshal path only — `read_text_stub` lists every
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
hypothesis `LprogExportFaithful` — the analogue of the MLIR route's
`MlirToolchainSemanticsAgrees`. Closing it requires a Lean model of jasmin's
`lsem`, which is not available Lean-side. The value-level obligations that *are*
discharged here: the export is total, structurally well-formed
(`Com.toLprog_wf` / `Com.toLprogPhys_wf`), and round-trips through the textual
serializer (`Com.toLprogText_magic`).
-/

/-!
## Parts

This module re-exports its parts; a consumer needing less imports a part.

* `JasminLprogExport.Types`: the mirror types of `Linear.lprog`.
* `JasminLprogExport.Export`: op lowering, the `Com` walk, `Com.toLprog`, the
  textual serialization.
* `JasminLprogExport.ExportLoops`: `ComL` loops and their lowering.
* `JasminLprogExport.ExportPhys`: register classes, slot trace, linear scan,
  two-address lowering, caller-save barriers.
* `JasminLprogExport.ExportPhysAbi`: the SysV ABI wrapping and the physical
  exports of `Com` and `ComL`.
* `JasminLprogExport.Proofs`: the correctness theorems of the parts above.
* `JasminLprogExport.Liveness`: point-wise liveness and the interference checker.
* `JasminLprogExport.Examples`: worked instances of each export path.
-/
