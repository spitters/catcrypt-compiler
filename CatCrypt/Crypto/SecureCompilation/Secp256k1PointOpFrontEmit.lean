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

## The render is a second, separate wall

Removing the denotation gate is necessary but not sufficient, and the remaining
obstacle is a different one. Measured 2026-08-09: `lake exe secp256k1pointop`
built natively against this producer ran **25 minutes without completing**, at
about 1.35 GB — the PSI guard declined to kill it, correctly, as being under its
1500 MB selector floor. So this is throughput, not memory, and it is not the
>11 GB whole-op denotation.

The cost is in the `cryptoDialectToJasminCom` LOWERING inside
`jacDblLowered`/`jacAddLowered`, not in `toLprogPhysAbi`/`renderLprogAtt`.
A staged probe (`Secp256k1PointOpStageProbe`) times the pipeline as explicit
calls: `translateDialectControl` 16-18 s, the `ret` cap ~90 ms, and the run does
not survive the lowering. The lowering is a single linear pass, but
`VIR/Core.Ctxt.Var` is a unary Peano inductive, so a variable at de Bruijn depth
d is a d-cell chain the lowering rebuilds; the point-op front binds the reduction
constants and ~24 half-limbs at the top and every brick references them across
the schedule, giving `Θ(nodes × schedule-length × depth)` ≈ 50M output cells.
The fix is a front re-tile to frame-relative composition (each brick loads its
operands from and stores its result to the frame, keeping reference range
O(field-op size)), the proven `Ed25519PointKernel` shape. `bench/…/gen_com/` is
still empty.

## Main results

* `emitProven` — writes the front-generated `secp256k1_jac_dbl` /
  `secp256k1_jac_add` owned `.s`, with correctness carried by the theorems
  rather than by a runtime check. Producing the artifact additionally needs the
  render cost above brought down.
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
