/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
public import CatCrypt.Crypto.Jasmin.KeccakJincImport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519LfundefBridge
public meta import CatCrypt.Crypto.Jasmin.KeccakJincImport

/-!
# Control-flow graphs of shipped kernel bodies

Instruction, block and edge counts of `cfgOf` on the bodies of shipped kernels: the five
`mpn_*_loop_owned` kernels (a guarded counted loop: an entry `Lcond` past the loop, the
loop label, the back-edge `Lcond`, the exit label and `Lret`; three blocks, four edges),
the rolled Keccak-f1600 body (a counted loop with no entry guard; three blocks, three
edges), and the straight-line X25519 ladder step (one block ending in `Lret`).

## Main definitions

* `shapeOf p`: the instruction, block and edge counts of the graph of the first function
  body of `p`.
* `keccakRolledLprog`: the rolled Keccak-f1600 program as the owned emitter prints it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.Jasmin

/-- The instruction, block and edge counts of the graph of the first function body of
    `p`. -/
def shapeOf (p : Lprog) : Option (Nat × Nat × Nat) :=
  p.lp_funcs.head?.bind fun f =>
    let b := f.2.lfd_body.map Linstr.li_i
    (cfgOf b).map fun G => (b.length, G.blocks.size, G.numEdges)

/-- `shapeOf` of the owned body (`LprogOptPipeline.ownedLprog`) of a program a builder
    may decline to produce. -/
def ownedShape (p : Option Lprog) : Option (Nat × Nat × Nat) :=
  p.bind fun p => shapeOf (LprogOptPipeline.ownedLprog p)

/-- The rolled Keccak-f1600 program as `JincElab.emitJFunRolledAsm` passes it to the
    printer. -/
def keccakRolledLprog : Option Lprog :=
  match KeccakJincImport.keccakF1600Rolled with
  | .ok r => (JincElab.rolledLprog r.fn r.tables KeccakJincImport.keccakF1600Sym).map fun p =>
      JincElab.ymmIndexFoldLprog (JincElab.rorxLprog (LprogOptPipeline.ownedLprog p))
  | .error _ => none

#kat ownedShape (MpnLoopFrontEmit.addLprogFront ()) == some (73, 3, 4)
#kat ownedShape (MpnLoopFrontEmit.subLprogFront ()) == some (85, 3, 4)
#kat ownedShape (MpnLoopFrontEmit.andLprog ()) == some (43, 3, 4)
#kat ownedShape (MpnLoopFrontEmit.iorLprog ()) == some (47, 3, 4)
#kat ownedShape (MpnLoopFrontEmit.xorLprog ()) == some (43, 3, 4)
#kat shapeOf Fe25519LfundefBridge.monoStepLprog == some (1059, 1, 0)
set_option kat.ms 2000 in
#kat keccakRolledLprog.bind shapeOf == some (498, 3, 3)

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels
