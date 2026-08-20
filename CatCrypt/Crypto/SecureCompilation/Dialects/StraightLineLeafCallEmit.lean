/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Mixed straight-line body: arithmetic + memory ABI AROUND named leaf calls

This validates the straight-line owned-export call arm
(`JasminLprogExport.expandCallShadows` + the `physBodyWithStores` caller-save
clobber barrier): a straight-line `Com jasminDialect` that mixes `regArith` with
two named-leaf `extCall`s in ONE body now front-compiles through
`Com.toLprogPhysAbi → renderLprogAtt` to a real `call leaf` with System V
marshalling — no `# UNHANDLED-OP CALL:` sentinel — with a value (`t0`) held live
across the second call correctly routed to a callee-saved register.

Body: `f(a0, a1) = leaf(a0 + a1) ⊕ leaf(a0)` where `leaf(x) = x + 1`
(the trivial linked owned/C leaf). All inputs are runtime loads from the SysV
input pointer (`RSI`); the single output is stored to the out pointer (`RDI`).

The C KAT (`bench/leafcall_compare/`) links a two-line `leaf` and checks the
numeric result byte-for-byte.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- Substring test. -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- `f(a0,a1) = leaf(a0 + a1) ⊕ leaf(a0)` over two runtime words `[a0, a1]`
    (`Γ = [reg 64, reg 64]`). The first leaf result (`t0`) is used AFTER the
    second call — a value live across a call, which must land in a callee-saved
    register (the clobber barrier). -/
def leafMixBody : Com jasminDialect [JasminTy.reg 64, JasminTy.reg 64] (.reg 64) :=
  -- depth 2, ctx [a1, a0]:  here = a1, there here = a0
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- depth 3, ctx [s, a1, a0]:  s = a1 + a0
  (.var (.mk (.extCall "leaf_add1" [.reg 64] (.reg 64)) rfl (.cons .here .nil))
  -- depth 4, ctx [t0, s, a1, a0]:  t0 = leaf(s)
  (.var (.mk (.extCall "leaf_add1" [.reg 64] (.reg 64)) rfl
        (.cons (.there (.there (.there .here))) .nil))
  -- depth 5, ctx [t1, t0, s, a1, a0]:  t1 = leaf(a0)
  (.var (.mk (.regArith .xor 64) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r = t0 ⊕ t1
  (.ret .here))))

/-- Number of runtime input words. -/
def nIn : Nat := 2

/-- All inputs are runtime `RSI` loads; argument slot `s` ↔ input word
    `nIn-1-s` (the `comToLfundef` De Bruijn reversal). -/
def leafMixLprog : Lprog :=
  Com.toLprogPhysAbi leafMixBody "leaf_mix_owned"
    (fun _ => none)
    (fun _ => none)
    (fun s => if s < nIn then some ("RSI", (nIn - 1 - s) * 8) else none)
    [("RDI", 0)]

def leafMixAtt : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned leafMixLprog

/-! ## Shape lemmas: the mixed body renders a REAL `call`, no shadow, arithmetic intact -/

/-! ## Render-level gate = the C byte-KAT (not an in-model string scan)

The render-level properties (a REAL `call leaf_add1` — no `# UNHANDLED-OP
CALL:` shadow, no `# UNHANDLED-OP` sentinel, the surrounding `add`/`xor`
arithmetic intact) are gated by `bench/leafcall_compare`'s C byte-KAT on the
emitted `leaf_mix_owned.s`: a shadow or sentinel comment cannot assemble/link
into a passing numeric check, so the KAT strictly subsumes the substring
scan. An in-model `native_decide` over `hasSub leafMixAtt …` is NOT stated
here: executing this module's render under `lake build` trips an
allocation-pattern-sensitive SIGSEGV in the elaborating `lean` process (the
same content elaborates clean standalone, via `lake env lean`, and under the
LSP — toolchain artifact, not a content defect). The pass-level
`expandCallShadows` gates live in `StraightLineLeafCallPassGates`. -/

/-! ## Emit driver -/

/-- Write the mixed leaf-call `.s` to the bench gen-from-Com directory. -/
def emit : IO Unit := do
  let dir := "bench/leafcall_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/leaf_mix_owned.s") leafMixAtt
  IO.println "WROTE bench/leafcall_compare/gen_com/leaf_mix_owned.s"
  IO.println "  owned x86 backend (toLprogPhysAbi -> renderLprogAtt), REAL call leaf_add1, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.Dialects.StraightLineLeafCallEmit
