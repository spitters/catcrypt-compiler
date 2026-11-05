/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpJasminValue

/-!
# Emitting the front-generated secp256k1 point ops, gated on the proof

The two point-op kernels are written only after the proved denotation results
`Secp256k1PointOpJasminValue.jacDblFrontCom_denote_cells_total` and
`jacAddFrontCom_denote_cells_total`, which give
`(com.denote V) m = pointCells (jacDblSpec X Y Z) m` for every input satisfying
`PrologueEntry`, with the source run discharged rather than assumed. A single
whole-op `Com.denote` of the composed ~6000-node point op peaks above 11 GB on a
14 GB host, so no runtime denotation is part of this producer.

The
`#check`s below make the dependency on the two theorems a build-time fact: if
either is renamed or weakened away, this module stops compiling rather than
silently reverting to an unjustified emit.

## Cost of the lowering

The emitter runs the `cryptoDialectToJasminCom` lowering inside
`jacDblLowered`/`jacAddLowered`. The lowering is a single linear pass, but
`VIR/Core.Ctxt.Var` is a unary inductive, so a variable at de Bruijn depth d is a
chain of d cells that the lowering rebuilds. The point-op front binds the reduction
constants and about 24 half-limbs at the top and every brick references them across
the schedule, so the lowered program has `Θ(nodes × schedule-length × depth)` cells,
about 50M. The staged probe `Secp256k1PointOpStageProbe` times the pipeline stage by
stage. A front that composes each brick relative to the frame (each brick loads its
operands from and stores its result to the frame, as `Ed25519PointKernel` does) keeps
the reference range at the size of a field operation.

## Main results

* `emitProven` — writes the front-generated `secp256k1_jac_dbl` /
  `secp256k1_jac_add` owned `.s`, with correctness carried by the theorems
  rather than by a runtime check; its run includes the lowering whose cost is
  described above.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontEmit

open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront (jacDblAsm jacAddAsm)

-- The two results that carry the point-op denotation. A rename or a
-- weakening breaks this module.
#check @Secp256k1PointOpJasminValue.jacDblFrontCom_denote_cells_total
#check @Secp256k1PointOpJasminValue.jacAddFrontCom_denote_cells_total

/-- **Write the front-generated point-op kernels.** No runtime `denote = spec`
    check: `jacDblFrontCom_denote_cells_total` and
    `jacAddFrontCom_denote_cells_total` prove that equation for all inputs in
    the entry scope, so the only failure this can report is the front itself
    declining to compile the body. -/
def emitProven (path : System.FilePath) : IO Unit := do
  match jacDblAsm (), jacAddAsm () with
  | some da, some aa => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path (da ++ "\n" ++ aa)
      IO.println s!"SECP256K1-POINTOP emit OK : {path} ({(da ++ aa).toUTF8.size} bytes)"
  | _, _ => throw (IO.userError "front-compile of the secp256k1 point-op kernels failed")

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontEmit
