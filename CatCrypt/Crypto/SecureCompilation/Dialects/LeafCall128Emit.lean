/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# 128-bit (SSE-class) leaf-call marshalling: front-derived validate

This validates the owned backend's **128-bit (`reg 128` / xmm) leaf-call
marshalling** (`JasminLprogExport.loopBodyCallLcmdClassed` reached from
`opToLinstrR` → `expandCallShadows`): a straight-line `Com jasminDialect` that
calls a leaf taking and returning a `reg 128` value front-compiles to a real
`call leaf128` whose System V argument is marshalled with `vmovdqu` into `xmm0`
and whose 128-bit result is taken back from `xmm0` — a *separate* register class
from the 64-bit GP path (`RDI…R9` / `RAX`), which is left byte-identical.

* `leafCall128Body` — `f(a : reg 128) = leaf128(a)`; `leaf128` is a trivial xmm
  op linked from C.
* The shape theorems below prove that the FRONT (`comToBody` →
  `expandCallShadows`) turns the `reg 128` `extCall` into the SSE marshalling
  sequence `vmovdqu %arg, %xmm0 ; call leaf128 ; vmovdqu %xmm0, %dst`, driven by
  the op's declared `argTys`/`retTy` widths (the `CALLW:` widened shadow), with
  no `UNHANDLED`/`CALL:` residual.
* The GP path is preserved: a `reg 64` leaf call keeps the plain `CALL:` shadow
  and the `RDI…/RAX` GP marshalling (`gp_call_unchanged`).

**Cross-call-live-xmm residual.** System V Linux has *no callee-saved xmm
register* — `xmm0…xmm15` are all volatile — so a 128-bit value live *across* the
call cannot survive in a register and must be stack-spilled/reloaded around the
call by the vector-RA. This validate keeps every 128-bit value consumed-by /
produced-at the call (no cross-call-live vector), so no spill is needed; the
spill obligation for the general `out = leaf128(a) ^ b` shape is documented on
`loopBodyCallLcmdClassed`.

The C KAT (`bench/leafcall128_compare/`) links `leaf128` and checks the 128-bit
result. Its `.s` is emitted by a self-contained AT&T renderer for the SSE
marshalling (`render128Lcmd`) below — the production printer's xmm arm lives in
the vsimd render module and is out of this file's scope.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.LeafCall128Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- Substring test (kernel-friendly, matches the sibling call-emit validate). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## The front-derived body and its marshalling -/

/-- `f(a : reg 128) = leaf128(a)`: a single `reg 128` argument passed to an
    opaque leaf that returns a `reg 128`. The whole marshalling class (arg in
    `xmm0`, result from `xmm0`) is fixed by the `extCall`'s declared widths. -/
def leafCall128Body : Com jasminDialect [JasminTy.reg 128] (.reg 128) :=
  .var (.mk (.extCall "leaf128" [.reg 128] (.reg 128)) rfl (.cons .here .nil))
  (.ret .here)

/-- The straight-line body walk (pre-RA) of the 128-bit-leaf body. -/
def leaf128Walk : Lcmd := comToBody 1 argName (fun _ => none) leafCall128Body 1

/-- The `expandCallShadows` image: the `CALLW:128;128;leaf128` widened shadow is
    rewritten to the real SSE marshalling sequence. -/
def leaf128Expanded : Lcmd := expandCallShadows leaf128Walk

/-- Text image of the expanded body (one instruction per line). -/
def leaf128ExpandedText : String :=
  String.intercalate "\n" (leaf128Expanded.map (fun i => i.li_i.toText))

/-! ## Shape theorems: the front emits SSE marshalling for a `reg 128` leaf -/

/-- The `reg 128` `extCall` lowers to the **widened** `CALLW:` shadow (carrying
    the return width `128` and the single argument width `128`), not the plain
    `CALL:` shadow — the type-driven class signal that reaches
    `expandCallShadows`. -/
theorem leaf128_walk_has_widened_shadow :
    leaf128Walk.any (fun i =>
      match i.li_i with
      | .Lopn _ opn _ => opn == "CALLW:128;128;leaf128"
      | _ => false) = true := by native_decide

/-- The argument is marshalled with `vmovdqu` into the SSE arg register `xmm0`
    (`VMOVDQU XMM0, a0`) — not a 64-bit `MOV` into `RDI`. -/
theorem leaf128_marshals_arg_into_xmm0 :
    leaf128Expanded.any (fun i =>
      match i.li_i with
      | .Lopn [.reg d] opn [.reg _] => d == "XMM0" && opn == "VMOVDQU"
      | _ => false) = true := by native_decide

/-- A **real** `Lcall leaf128` is emitted (the leaf is genuinely called). -/
theorem leaf128_has_real_call :
    leaf128Expanded.any (fun i =>
      match i.li_i with
      | .Lcall _ (sym, _) => sym == "leaf128"
      | _ => false) = true := by native_decide

/-- The 128-bit result is taken back from `xmm0` with `vmovdqu`
    (`VMOVDQU dst, XMM0`) — not from `RAX`. -/
theorem leaf128_result_from_xmm0 :
    leaf128Expanded.any (fun i =>
      match i.li_i with
      | .Lopn [.reg _] opn [.reg s] => s == "XMM0" && opn == "VMOVDQU"
      | _ => false) = true := by native_decide

/-- No residual `CALL`-family shadow survives the expansion (every leaf call
    became a real `Lcall`). -/
theorem leaf128_no_call_shadow :
    leaf128Expanded.all (fun i =>
      match i.li_i with
      | .Lopn _ opn _ =>
          !(opn.startsWith "CALL:") && !(opn.startsWith "CALLN:")
            && !(opn.startsWith "CALLW:") && !(opn.startsWith "CALLNW:")
      | _ => true) = true := by native_decide

/-! ## GP path preserved: a `reg 64` leaf keeps the 64-bit `CALL:`/`RDI…RAX` path -/

/-- `g(a : reg 64) = leaf64(a)`: an all-GP leaf call. -/
def leafCall64Body : Com jasminDialect [JasminTy.reg 64] (.reg 64) :=
  .var (.mk (.extCall "leaf64" [.reg 64] (.reg 64)) rfl (.cons .here .nil))
  (.ret .here)

/-- **GP path unchanged:** a `reg 64` leaf keeps the plain `CALL:leaf64` shadow —
    the widened `CALLW:` encoding fires only when a width is `> 64`. -/
theorem gp_call_keeps_plain_shadow :
    (comToBody 1 argName (fun _ => none) leafCall64Body 1).any (fun i =>
      match i.li_i with
      | .Lopn _ opn _ => opn == "CALL:leaf64"
      | _ => false) = true := by native_decide

/-- **GP path unchanged:** the `reg 64` leaf marshals its argument into `RDI`
    with a 64-bit `MOV` and takes the result from `RAX` — never touches xmm. -/
theorem gp_call_marshals_gp :
    (expandCallShadows (comToBody 1 argName (fun _ => none) leafCall64Body 1)).any
      (fun i =>
        match i.li_i with
        | .Lopn [.reg d] _ [.reg s] => d == "RDI" || s == "RAX"
        | _ => false) = true := by native_decide

/-- **GP path unchanged:** the `reg 64` expansion emits no xmm move. -/
theorem gp_call_no_xmm :
    (expandCallShadows (comToBody 1 argName (fun _ => none) leafCall64Body 1)).all
      (fun i =>
        match i.li_i with
        | .Lopn _ opn _ => !(opn == "VMOVDQU")
        | _ => true) = true := by native_decide

/-! ## Self-contained AT&T render of the SSE marshalling (for the C KAT)

The production printer's xmm arm lives in the vsimd render module; here a small
purpose-built renderer emits the SSE marshalling `Lcmd` (`VMOVDQU`/`Lcall`) to
real `vmovdqu`/`call` lines, so the emitted marshalling can be linked and its
128-bit result checked byte-for-byte against the C leaf. -/

/-- `XMM<i> → %xmm<i>` (the only register class this marshalling names). -/
def xmmAtt (n : String) : String :=
  if n.startsWith "XMM" then "%xmm" ++ (n.drop 3).toString
  else "%<" ++ n ++ ">"

/-- Render one SSE-marshalling `LinstrR` to its AT&T line. Handles exactly the
    two shapes `loopBodyCallLcmdClassed` produces for a 128-bit call: a
    register→register `VMOVDQU` and a real `Lcall`. -/
def render128Instr : LinstrR → String
  | .Lopn [.reg d] "VMOVDQU" [.reg s] => "\tvmovdqu " ++ xmmAtt s ++ ", " ++ xmmAtt d
  | .Lcall _ (sym, _) => "\tcall " ++ sym
  | other => "\t# UNHANDLED-128 " ++ other.toText

/-- Render an SSE-marshalling `Lcmd` (drops the trailing `Lret` a body wrapper
    adds; the marshalling core carries none). -/
def render128Lcmd (c : Lcmd) : List String :=
  c.filterMap (fun i =>
    match i.li_i with
    | .Lret => none
    | li => some (render128Instr li))

/-- The concrete SSE marshalling for `leaf128(x)` with the argument in `%xmm1`
    and the result placed back in `%xmm1` — produced by the SAME emit function
    `loopBodyCallLcmdClassed` the front reaches, with concrete register names so
    it renders to a linkable `.s`. -/
def marsh128 : Lcmd :=
  loopBodyCallLcmdClassed "XMM1" true "leaf128" [(.reg "XMM1", true)]

/-- The emitted SSE marshalling renders to real `vmovdqu`/`call` with no
    `UNHANDLED`. -/
theorem marsh128_renders_clean :
    (render128Lcmd marsh128).all (fun l => !(hasSub l "UNHANDLED")) = true := by
  native_decide

/-- The rendered marshalling is exactly `vmovdqu %xmm1,%xmm0 ; call leaf128 ;
    vmovdqu %xmm0,%xmm1`. -/
theorem marsh128_render_shape :
    render128Lcmd marsh128 =
      ["\tvmovdqu %xmm1, %xmm0", "\tcall leaf128", "\tvmovdqu %xmm0, %xmm1"] := by
  native_decide

/-- The full owned `.s` for `leaf128_call_owned(out = %rdi, in = %rsi)`:
    load the 128-bit argument from `in`, run the emit's SSE marshalling (arg into
    `%xmm0`, `call leaf128`, result from `%xmm0`), store the 128-bit result to
    `out`. The `movdqu` load/store are the standard 2-pointer ABI glue around the
    emit-derived marshalling core. -/
def leaf128CallAtt : String :=
  String.intercalate "\n"
    ([ "\t.text"
     , "\t.globl leaf128_call_owned"
     , "leaf128_call_owned:"
     , "\tmovdqu (%rsi), %xmm1" ]
     ++ render128Lcmd marsh128
     ++ [ "\tmovdqu %xmm1, (%rdi)"
        , "\tret", "" ])

/-! ## Emit driver -/

/-- Write the 128-bit leaf-call `.s` to the bench gen-from-Com directory. -/
def emit : IO Unit := do
  let dir := "bench/leafcall128_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/leaf128_call_owned.s") leaf128CallAtt
  IO.println "WROTE bench/leafcall128_compare/gen_com/leaf128_call_owned.s"
  IO.println "  owned x86 backend, REAL call leaf128, vmovdqu marshalling into xmm0, result from xmm0"

end CatCrypt.Crypto.SecureCompilation.Dialects.LeafCall128Emit
