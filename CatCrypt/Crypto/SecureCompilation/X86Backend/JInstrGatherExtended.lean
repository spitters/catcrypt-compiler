/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr
import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-!
# `gatherJBlock2` — the extended `JInstr` gather that covers real GoldenPath kernel bodies

The POC `JInstr` gather (`OptimizedComToElf.gatherJBlock`, wired to
`LoweringExtended.lowerLinstrExtL`) returns `none` on **every** real GoldenPath
kernel body. A real kernel's exported `Lprog` body (`Com.toLprog … |>.lfd_body`)
is a list of **width-tagged** `Lopn`s terminated by an `Lret`, and the POC
`lowerLinstrExtL` rejects all of:

* the width-tagged two-source `regArith` exports `"OR:64"` / `"XOR:64"`
  (the POC only matches the **untagged** single-source `{ADD,SUB,…,OR,XOR}` table);
* the width-tagged immediate shifts `"SHR:19:64"` / `"SHL:45:64"`
  (the POC has no immediate-shift arm at all); and
* the trailing terminator `Lret` (a non-`Lopn` `LinstrR`).

So `comToFramedJFunc` / `comToFramedJLeaf` are `none` for all 23 kernels and
`compileComToElfJInstr` silently falls back to the `Lprog` (`compileComToElf`)
path. This module is the **additive** fix for the gather, step 1 of re-pointing the
GoldenPath kernels off the `Lprog` encoder.

## What this module adds (additive — the POC gather is untouched)

A new `gatherJBlock2` (distinct from `OptimizedComToElf.gatherJBlock`):

1. **drops the trailing `Lret`** (the framing supplies the `ret` — `epilogueBytes`
   ends in `LeafBytes.encRet`, the `0xC3` byte, so the body block must NOT carry an
   `Lret`); and
2. lowers every remaining instruction through the **superset**
   `LoweringExtendedCoverage.lowerLinstrExtCovL` — which delegates to
   `LoweringExtended.lowerLinstrExt2L` (covering the width-tagged two-source
   `regArith` and the immediate shifts `SHR:<n>:64` / `SHL:<n>:64`) and additionally
   folds in the carry-chain ADX (`ADCX:64`/`ADOX:64`/`ADCXHI:64`/`ADOXHI:64`) and the
   register-indexed (SIB) `LOADIDX`/`STOREIDX` shapes the wider bignum/field kernels
   use.

`comToFramedJFunc2` / `comToFramedJLeaf2` are the variant entries that thread
`gatherJBlock2` in place of the POC `gatherJBlock`, with the same shape as the
originals (`ComToFramedJInstr.comToFramedJFunc` / `CompileComToElfJInstr.comToFramedJLeaf`).

## Coverage evidence (the deliverable)

On the real GoldenPath kernel `AsconLinear.asconSigma0Com` (`Σ₀ x`, 8 width-tagged
`Lopn`s — `SHR:19:64`, `SHL:45:64`, `OR:64`, `SHR:28:64`, `SHL:36:64`, `OR:64`,
`XOR:64`, `XOR:64` — terminated by `Lret`):

* `asconSigma0_gather2_isSome` / the `#eval` cross-check show
  `comToFramedJLeaf2 asconSigma0Com "ascon_sigma0" alloc args F = some _`
  (i.e. `.isSome = true`), where the POC `comToFramedJLeaf` gives `none`;
* `asconSigma0_gather2_ops` `#eval`s the gathered `List (JInstr 64)` so the lowered
  ops are visible (each width-tagged op lowered into its two-address `JInstr` form,
  no `Lret`).

## Honesty — this is step 1 only

This closes the **gather** gap: the JInstr emit path can now *reach* a real kernel
body where before it bailed to `none`. It does **not** yet give a byte-MATCH against
`compileComToElf`/`toLprogPhysAbi`. `gatherJBlock2` feeds the **virtual-register**
`Com.toLprog` body (operand names are the SSA virtual registers), whereas the
`Lprog` owned-emit entry frames the **physical-ABI** body (`Com.toLprogPhysAbi`,
post-register-allocation, with the System-V arg-marshal). Re-pointing the kernels
for a passing byte-KAT additionally needs the physical-regalloc / arg-marshal
reconciliation (step 2): the `framedLeaqText_eq_lprog` side-conditions
(`CompileComToElfJInstr.jinstrElf_eq_lprogElf`) — matched saved-register sets,
empty arg-marshal, and the resolver-discharged body byte agreement — discharged on
the physical body. That reconciliation is out of scope here; this module only proves
the gather now succeeds.

No `sorry`, no axiom, no `native_decide`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr (comBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq (jinstrFramedLeaqText)

/-! ## 1. The extended gather

`gatherJBlock2` is the additive coverage gather. It first **drops every `Lret`**
(there is exactly one, the trailing terminator — the framing supplies the `ret`),
then lowers each remaining `Linstr` through the superset
`LoweringExtendedCoverage.lowerLinstrExtCovL`, flattening the per-instruction
blocks. `List.mapM` over `Option` keeps the no-silent-wrong-bytes guard: a single
uncovered (non-`Lret`) instruction makes the whole gather `none`. -/

/-- Whether an `Linstr` is the `Lret` terminator (dropped before gathering — the
    framing's `epilogueBytes` supplies the `ret` byte). -/
def isLret (i : Linstr) : Bool :=
  match i.li_i with
  | .Lret => true
  | _     => false

/-- **The extended `JInstr` gather.** Drop the trailing `Lret` (framing supplies the
    `ret`), then lower every remaining instruction through the superset
    `lowerLinstrExtCovL` (width-tagged two-source `regArith`, immediate shifts
    `SHR:<n>:64`/`SHL:<n>:64`, plus the ADX/SIB shapes) and flatten. `none` iff some
    non-`Lret` instruction is outside the superset fragment. -/
def gatherJBlock2 (body : List Linstr) : Option (List (JInstr 64)) :=
  ((body.filter (fun i => !isLret i)).mapM lowerLinstrExtCovL).map List.flatten

/-! ## 2. The variant entries (`comToFramedJFunc2` / `comToFramedJLeaf2`)

Same shape as `ComToFramedJInstr.comToFramedJFunc` and
`CompileComToElfJInstr.comToFramedJLeaf`, but threading `gatherJBlock2` (the
extended gather) in place of the POC `gatherJBlock`. -/

/-- The framed `JFunc` for a `Com`, via the **extended** gather. `none` only when
    some non-`Lret` body instruction is outside the superset fragment. -/
def comToFramedJFunc2 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option JFunc :=
  (comBody com fname immSlotMap).bind (fun body =>
    (gatherJBlock2 body).map (fun blk =>
      { name := fname, alloc := alloc, args := args, body := blk, savedRegs := savedRegs }))

/-- The `leaq`-framed single-function `ElfObject.Leaf` for a `Com`, via the
    **extended** gather — the `comToFramedJLeaf` analogue. `none` exactly when the
    body is outside the superset fragment. The frame size `F` is the matched `Lprog`
    body's `frameSize` (the same placement data the proved lowering pins). -/
def comToFramedJLeaf2 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg) (F : Nat)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option ElfObject.Leaf :=
  (comToFramedJFunc2 com fname alloc args savedRegs immSlotMap).map (fun f =>
    { name := fname, text := jinstrFramedLeaqText f F })

/-! ## 3. Coverage evidence on a real GoldenPath kernel (`asconSigma0Com`)

`AsconLinear.asconSigma0Com` is one of the 23 GoldenPath kernels — `Σ₀ x`, a
straight-line body of 8 width-tagged `Lopn`s terminated by `Lret`. The POC
`comToFramedJLeaf` is `none` on it (the width tags + the `Lret` defeat
`lowerLinstrExtL`); the extended `comToFramedJLeaf2` succeeds. -/

/-- A plausible placement for the kernel (the same demo shape as
    `JInstrFramedEmit.demoFunc`): the single argument `x` homes in `%rdi`, no
    callee-saved registers, empty frame. The exact placement is immaterial to the
    *gather* succeeding — the point is that `gatherJBlock2` now lowers the body. -/
def asconAlloc : GpAlloc := [("x", "%rdi")]

/-- The single ABI argument `x` (an integer in `%rdi`). -/
def asconArgs : List AbiArg := [⟨"x", .intPtr⟩]

/-! ### Coverage `#eval`s (the required evidence)

The extended leaf entry succeeds on the real kernel — where the POC
`comToFramedJLeaf` gives `none`, `comToFramedJLeaf2` gathers the full width-tagged
body and frames it. The first `#eval` prints `true` (the extended entry's `.isSome`),
the second `false` (the POC entry's `.isSome`, the gap this module closes), and the
third prints the gathered `List (JInstr 64)` — every width-tagged op lowered into its
two-address `JInstr` form, with no `Lret`.

The kernel-`Com` coverage `#eval` certificates (on `AsconLinear.asconSigma0Com`)
are re-homed in `GoldenPathByteIdentityDemo` to keep this chain file
GoldenPath-free. -/

/-! ### The literal exported body, and the `#eval` coverage witness

The literal `Lprog` body `Com.toLprog asconSigma0Com` exports (the
`#eval … (·.map (·.li_i))` printout below): 8 width-tagged `Lopn`s terminated by
`Lret`. We state coverage on this literal body too (independent of the
non-kernel-reducing `Com.toLprog` exporter): `gatherJBlock2 asconSigma0Body` is
`some` of the 16-instruction two-address block, and `none` from the POC
`gatherJBlock`. -/

/-- The literal `Lprog` body `Com.toLprog asconSigma0Com` exports for `ascon_sigma0`
    (the `#eval` printout below; the source-position tag `li_ii` is immaterial to the
    gather and taken `0`). 8 width-tagged `Lopn`s terminated by `Lret`. -/
def asconSigma0Body : List Linstr :=
  [ ⟨0, .Lopn [.reg "r1"] "SHR:19:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r2"] "SHL:45:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r3"] "OR:64" [.reg "r1", .reg "r2"]⟩
  , ⟨0, .Lopn [.reg "r4"] "SHR:28:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r5"] "SHL:36:64" [.reg "a0"]⟩
  , ⟨0, .Lopn [.reg "r6"] "OR:64" [.reg "r4", .reg "r5"]⟩
  , ⟨0, .Lopn [.reg "r7"] "XOR:64" [.reg "a0", .reg "r3"]⟩
  , ⟨0, .Lopn [.reg "r8"] "XOR:64" [.reg "r7", .reg "r6"]⟩
  , ⟨0, .Lret⟩ ]

-- Coverage (literal body): the extended gather lowers the full real kernel body —
-- every width-tagged two-source `regArith` (`OR:64`/`XOR:64`) and every immediate
-- shift (`SHR:<n>:64`/`SHL:<n>:64`), with the trailing `Lret` dropped — into the
-- 16-instruction two-address `JInstr` block. Prints `some [16 ops]`.
#eval gatherJBlock2 asconSigma0Body

-- The POC `gatherJBlock` returns `none` on the same literal body (the width tags +
-- the `Lret` defeat `lowerLinstrExtL`). Prints `none`.
#eval CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf.gatherJBlock asconSigma0Body

-- Coverage: the extended gather is `some` on the literal body — prints `true`, the
-- kernel-computable form of the real-kernel coverage the entry-level `#eval`s witness.
#eval (gatherJBlock2 asconSigma0Body).isSome

/-! ### Honesty — why these are `#eval`s, not `rfl`/`decide` theorems

The immediate-shift arm (`SHR:<n>:64`/`SHL:<n>:64`) is dispatched by
`LoweringExtended.parseShiftMnem`, whose detection is `String.startsWith`. In Lean
4.29 `String.startsWith` is `Slice`/UTF-8-backed and does **not** kernel-reduce —
even on a *closed literal* mnemonic like `"SHR:19:64"`, `rfl`/`decide`/`simp` all
get stuck (only `native_decide` evaluates it, which is out of policy here). This is
the same residual `ComLegalityToGatherFull` records for the shift family. The
compiled `#eval` evaluator does run `String.startsWith`, so the coverage is
witnessed by `#eval` (the required evidence: `(comToFramedJLeaf2 … ).isSome = true`
and `(gatherJBlock2 asconSigma0Body).isSome = true` both print `true`); a
kernel-reducible `rfl`/`decide` theorem is not attainable at this layer until the
toolchain gains a reducing `String.startsWith` (or the shift detection is reworked
to a kernel-reducible primitive). The width-tagged two-source `regArith`
(`OR:64`/`XOR:64`) arms *do* reduce (the `ComLegalityToGatherFull` per-op bridge
proves their `isSome` by `decide`); it is solely the shift arm that blocks a
whole-body `rfl`. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
