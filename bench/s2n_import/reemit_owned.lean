import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519MulShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SqrShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519AddShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Fe25519SubShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CombSelectShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519CompressShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PackSignShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519Join16Shipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519InvertShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
The blocks imported by `import_owned.sh` (the modules named in `owned_kernels.txt`)
printed back to AT&T assembly by the owned scalar printer
`AsmPrinter.renderBlockBody`, under the identity register allocation on each block's
register names. A block with calls prints each run followed by `call SYM`. Only the
body is printed: the importer checked and omitted the frame, and `compare_owned.sh`
omits the same frame lines from the source before comparing.

The `#eval main` at the end writes `bench/s2n_import/gen/owned/MODULE.s`, one
instruction per line, for each module, when `lake lean` elaborates this file from the
repository root (`make -C bench/s2n_import reemit-owned`). It fails, writing nothing
for that module, if a block names something other than a 64-bit general register or
`%rsp`.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported

/-- The 64-bit general registers, `%rsp` included: the importer keeps `%rsp` as a
    memory base and as a `lea` base. -/
def gp64rsp : List String :=
  [ "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%rsp",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15" ]

/-- The identity allocation on a block's register names. -/
def identityAlloc (block : List (JInstr 64)) : GpAlloc :=
  (blockNames block).map fun r => (r, r)

/-- The body lines of a block without calls. -/
def plainLines (block : List (JInstr 64)) : List String :=
  renderBlockBody (identityAlloc block) block

/-- The body lines of a block with calls: each run, then its `call`. -/
def callLines (block : List CallSeg) : List String :=
  let alloc := identityAlloc (CallSeg.instrs block)
  block.flatMap fun c =>
    renderBlockBody alloc c.body ++
      (match c.callee with
       | some s => ["\tcall " ++ s]
       | none => [])

/-- One imported function: its module name, its instructions and its printed body. -/
structure Reemitted where
  name : String
  instrs : List (JInstr 64)
  lines : List String

def plain (name : String) (b : List (JInstr 64)) : Reemitted :=
  ⟨name, b, plainLines b⟩

def withCalls (name : String) (b : List CallSeg) : Reemitted :=
  ⟨name, CallSeg.instrs b, callLines b⟩

def all : List Reemitted :=
  [ plain "Fe25519MulShipped" Fe25519MulShipped.fe25519MulShippedBlock,
    plain "Fe25519SqrShipped" Fe25519SqrShipped.fe25519SqrShippedBlock,
    plain "Fe25519AddShipped" Fe25519AddShipped.fe25519AddShippedBlock,
    plain "Fe25519SubShipped" Fe25519SubShipped.fe25519SubShippedBlock,
    plain "Ed25519CombSelectShipped" Ed25519CombSelectShipped.ed25519CombSelectShippedBlock,
    withCalls "Ed25519CompressShipped" Ed25519CompressShipped.ed25519CompressShippedBlock,
    plain "Ed25519PackSignShipped" Ed25519PackSignShipped.ed25519PackSignShippedBlock,
    withCalls "Ed25519MaddShipped" Ed25519MaddShipped.ed25519MaddShippedBlock,
    plain "Ed25519Join16Shipped" Ed25519Join16Shipped.ed25519Join16ShippedBlock,
    withCalls "Ed25519InvertShipped" Ed25519InvertShipped.ed25519InvertShippedBlock,
    plain "Ed25519ScReduceShipped" Ed25519ScReduceShipped.ed25519ScReduceShippedBlock,
    plain "Ed25519ScMuladdShipped" Ed25519ScMuladdShipped.ed25519ScMuladdShippedBlock,
    plain "Ed25519PointAddShipped" Ed25519PointAddShipped.ed25519PointAddShippedBlock ]

def main : IO Unit := do
  IO.FS.createDirAll "bench/s2n_import/gen/owned"
  for r in all do
    let bad := (blockNames r.instrs).filter fun n => !gp64rsp.contains n
    unless bad.isEmpty do
      throw <| IO.userError s!"{r.name}: block names that are not 64-bit registers: {bad}"
    let path := s!"bench/s2n_import/gen/owned/{r.name}.s"
    IO.FS.writeFile path (String.intercalate "\n" r.lines ++ "\n")
    IO.println s!"wrote {path} ({r.instrs.length} instructions)"

#eval main
