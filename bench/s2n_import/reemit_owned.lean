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
printed back to AT&T assembly, each between its prologue and its epilogue. The body is
printed by the owned scalar printer `AsmPrinter.renderBlockBody`, under the identity
register allocation on each block's register names; a block with calls prints each run
followed by `call SYM`. The prologue and the epilogue are printed by `frameLines`, which
reads each `lea %rsp` / `storeMem "%rsp" 0` pair as `pushq`, each `loadMem r "%rsp" 0` /
`lea %rsp` pair as `popq`, and a lone `lea`, `sub` or `add` on `%rsp` as the frame
allocation or release. `compare_owned.sh` removes only a leading `endbr64` and the
trailing `ret` from the source before comparing, since no imported list holds them.

The `#eval main` at the end writes `bench/s2n_import/gen/owned/MODULE.s`, one
instruction per line, for each module, when `lake lean` elaborates this file from the
repository root (`make -C bench/s2n_import reemit-owned`). It fails, writing nothing
for that module, if a block names something other than a 64-bit general register or
`%rsp`, or if a frame list holds an element outside the forms above.
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

/-- The lines of a frame list: `pushq`, `popq`, and the `%rsp` allocation and release;
    `none` for any other element. -/
def frameLines : List (JInstr 64) → Option (List String)
  | [] => some []
  | .lea "%rsp" "%rsp" "%rsp" 0 (-8) :: .storeMem "%rsp" 0 (.reg r) :: rest =>
      (frameLines rest).map (("\tpushq " ++ r) :: ·)
  | .loadMem r "%rsp" 0 :: .lea "%rsp" "%rsp" "%rsp" 0 8 :: rest =>
      (frameLines rest).map (("\tpopq " ++ r) :: ·)
  | .lea "%rsp" "%rsp" "%rsp" 0 d :: rest =>
      (frameLines rest).map ((s!"\tleaq {d}(%rsp), %rsp") :: ·)
  | .sub "%rsp" (.imm n) :: rest =>
      (frameLines rest).map ((s!"\tsubq ${n}, %rsp") :: ·)
  | .add "%rsp" (.imm n) :: rest =>
      (frameLines rest).map ((s!"\taddq ${n}, %rsp") :: ·)
  | _ => none

/-- One imported function: its module name, its body instructions, its printed body, and
    its prologue and epilogue. -/
structure Reemitted where
  name : String
  instrs : List (JInstr 64)
  lines : List String
  prologue : List (JInstr 64)
  epilogue : List (JInstr 64)

def plain (name : String) (b pro epi : List (JInstr 64)) : Reemitted :=
  ⟨name, b, plainLines b, pro, epi⟩

def withCalls (name : String) (b : List CallSeg) (pro epi : List (JInstr 64)) : Reemitted :=
  ⟨name, CallSeg.instrs b, callLines b, pro, epi⟩

open Fe25519MulShipped Fe25519SqrShipped Fe25519AddShipped Fe25519SubShipped
  Ed25519CombSelectShipped Ed25519CompressShipped Ed25519PackSignShipped Ed25519MaddShipped
  Ed25519Join16Shipped Ed25519InvertShipped Ed25519ScReduceShipped Ed25519ScMuladdShipped
  Ed25519PointAddShipped in
def all : List Reemitted :=
  [ plain "Fe25519MulShipped" fe25519MulShippedBlock fe25519MulShippedPrologue
      fe25519MulShippedEpilogue,
    plain "Fe25519SqrShipped" fe25519SqrShippedBlock fe25519SqrShippedPrologue
      fe25519SqrShippedEpilogue,
    plain "Fe25519AddShipped" fe25519AddShippedBlock fe25519AddShippedPrologue
      fe25519AddShippedEpilogue,
    plain "Fe25519SubShipped" fe25519SubShippedBlock fe25519SubShippedPrologue
      fe25519SubShippedEpilogue,
    plain "Ed25519CombSelectShipped" ed25519CombSelectShippedBlock
      ed25519CombSelectShippedPrologue ed25519CombSelectShippedEpilogue,
    withCalls "Ed25519CompressShipped" ed25519CompressShippedBlock
      ed25519CompressShippedPrologue ed25519CompressShippedEpilogue,
    plain "Ed25519PackSignShipped" ed25519PackSignShippedBlock ed25519PackSignShippedPrologue
      ed25519PackSignShippedEpilogue,
    withCalls "Ed25519MaddShipped" ed25519MaddShippedBlock ed25519MaddShippedPrologue
      ed25519MaddShippedEpilogue,
    plain "Ed25519Join16Shipped" ed25519Join16ShippedBlock ed25519Join16ShippedPrologue
      ed25519Join16ShippedEpilogue,
    withCalls "Ed25519InvertShipped" ed25519InvertShippedBlock ed25519InvertShippedPrologue
      ed25519InvertShippedEpilogue,
    plain "Ed25519ScReduceShipped" ed25519ScReduceShippedBlock ed25519ScReduceShippedPrologue
      ed25519ScReduceShippedEpilogue,
    plain "Ed25519ScMuladdShipped" ed25519ScMuladdShippedBlock ed25519ScMuladdShippedPrologue
      ed25519ScMuladdShippedEpilogue,
    plain "Ed25519PointAddShipped" ed25519PointAddShippedBlock ed25519PointAddShippedPrologue
      ed25519PointAddShippedEpilogue ]

def main : IO Unit := do
  IO.FS.createDirAll "bench/s2n_import/gen/owned"
  for r in all do
    let bad := (blockNames r.instrs).filter fun n => !gp64rsp.contains n
    unless bad.isEmpty do
      throw <| IO.userError s!"{r.name}: block names that are not 64-bit registers: {bad}"
    let some pro := frameLines r.prologue
      | throw <| IO.userError s!"{r.name}: a prologue element outside the frame forms"
    let some epi := frameLines r.epilogue
      | throw <| IO.userError s!"{r.name}: an epilogue element outside the frame forms"
    let path := s!"bench/s2n_import/gen/owned/{r.name}.s"
    IO.FS.writeFile path (String.intercalate "\n" (pro ++ r.lines ++ epi) ++ "\n")
    IO.println s!"wrote {path} ({r.instrs.length} instructions)"

#eval main
