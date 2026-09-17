import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
The imported s2n-bignum block `s2nMontmulP384Block` printed back to AT&T assembly by
the owned scalar printer `AsmPrinter.renderBlockBody`, inside the leaf wrapper
`AsmPrinter.renderLeafFn` that `P384FieldKernel.p384MulAsm` also uses. The register
allocation is the identity on the block's register names, which are physical
registers, so the printer emits the registers of the source. The prologue and
epilogue repeat s2n-bignum's frame: `endbr64`, `pushq` of the six callee-saved
registers, the `popq` sequence in reverse, and `retq`.

MEASUREMENT ARTIFACT. The body is printed from the imported `JInstr` block by the
owned printer; the frame lines are literal text. The block is an import, not the output
of a verified front. `Ascent.Demos.S2nMontmulP384Proof.s2nMontmulP384_correct` proves
the block against the Montgomery specification over `JasminModel`; no theorem relates
the literal frame lines or this printed file to that block, so the file is a
known-answer and timing target against `bignum_montmul_p384`.

The `#eval main` at the end writes
`bench/s2n_import/gen/bignum_montmul_p384_reemitted.s` when `lake lean` elaborates
this file from the repository root (`make -C bench/s2n_import reemit`). It fails,
writing nothing, if the identity allocation leaves a name unmapped or maps a name
that is not a 64-bit general register.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

/-- The emitted symbol. -/
def reemitSymbol : String := "bignum_montmul_p384_reemitted"

/-- The 64-bit general registers other than `%rsp`. -/
def gp64 : List String :=
  [ "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15" ]

/-- The identity allocation on the block's register names. -/
def identityAlloc : GpAlloc :=
  (blockNames s2nMontmulP384Block).map fun r => (r, r)

/-- s2n-bignum's frame for `bignum_montmul_p384`, entry half. -/
def framePrologue : List String :=
  [ "\tendbr64", "\tpushq %rbx", "\tpushq %rbp", "\tpushq %r12", "\tpushq %r13",
    "\tpushq %r14", "\tpushq %r15" ]

/-- s2n-bignum's frame for `bignum_montmul_p384`, exit half. -/
def frameEpilogue : List String :=
  [ "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbp",
    "\tpopq %rbx", "\tretq" ]

/-- The re-emitted assembly text. -/
def reemittedAsm : String :=
  renderLeafFn reemitSymbol framePrologue
    (renderBlockBody identityAlloc s2nMontmulP384Block) frameEpilogue

def main : IO Unit := do
  let names := blockNames s2nMontmulP384Block
  let bad := names.filter fun r => !gp64.contains r
  unless bad.isEmpty do
    throw <| IO.userError s!"block names that are not 64-bit general registers: {bad}"
  let unmapped := names.filter fun r => (identityAlloc.lookup r).isNone
  unless unmapped.isEmpty do
    throw <| IO.userError s!"names the allocation leaves unmapped: {unmapped}"
  let path := "bench/s2n_import/gen/bignum_montmul_p384_reemitted.s"
  IO.FS.createDirAll "bench/s2n_import/gen"
  IO.FS.writeFile path reemittedAsm
  IO.println s!"wrote {path} ({s2nMontmulP384Block.length} body instructions)"

#eval main
