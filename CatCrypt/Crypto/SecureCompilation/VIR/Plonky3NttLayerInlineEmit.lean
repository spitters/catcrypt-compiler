/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 two-NTT-layer fusion, FRONT-COMPILED (`plonky3_ntt_layer8x2_fused_rc`)

`FULL_PROVER_VS_P3.md` §"per-leaf-call ABI tax" names the precise overhead in
the emitted whole-prover: every emitted field-leaf round-trips its data through
a caller `(out, in)` buffer. When leaf **A** feeds leaf **B**, the bytes are
stored out of A's registers by A's copy-out, then loaded back by B's copy-in —
`2·nOut_A + 2·nCopy_B` pure-marshalling moves.

This module closes that tax for a representative consecutive leaf pair: two
chained radix-2 NTT layers (the squaring butterfly-chain stage the LDE /
FRI-fold phases run). The fusion happens at the SOURCE level and the fused
program is compiled by the verified front — NO hand-built `Com`:

```
  fusedBody = seqAll (layerStmts ++ layerStmts ++ outCopies)   (LowCT)
    --(translateDialectControl)-->   Com catCryptDialect srcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-->  fusedTwoLayerCom : Com jasminDialect inCtxt r64
```

`layerStmts` is the SINGLE layer's statement list (imported from
`Plonky3NttLayerEmit`, the same list its deployed `layerCom` is compiled
from), so the fused source is *definitionally* the single-layer source
sequenced twice (`fusedStmts_eq_two_layers`). The second copy of the
statements reads its eight values from the names `v0..v7` the first copy just
rebound — the SSA rebinding wires layer 1's outputs straight into layer 2, no
copy-out / copy-in between (the emitted `Com` is one straight-line pure-arith
chain, `fused_is_purearith_only`, with exactly the two bodies' bindings and
the single trailing copy epilogue, `fused_bindings_eq`).

## What is proved

* `fusedStmts_eq_two_layers` — the fused source IS the single-layer statements
  twice (definitional).
* `fused_denote_spec` — the front-compiled fused program denotes the
  independent `Nat % p` layer reference **applied twice** (same twiddles both
  layers — the squaring stage) on every sample, all eight output words. This
  is the in-model fusion-correctness statement matching the external KAT.
* `fused_bindings_eq` — `bindings(fused) + 8 = 2 · bindings(single layer)`:
  the fused `Com` carries exactly the two bodies' arithmetic (one shared
  8-copy output epilogue instead of two), no extra marshalling binding. A
  separate-call chain would additionally emit `2·nOut + 2·nCopy = 32`
  inter-layer marshalling moves (`ntt_marshal_saving`).

## ABI

Identical shape to a single layer: 18 input words
`[v0..v7, t0..t3, MU, p, 0, 30, 32, 63]` (values + twiddles runtime, constants
immediates), 8 output words as the last eight bindings. Export
`plonky3_ntt_layer8x2_fused_rc`, rendered owned
(`Com.toLprogPhysAbi -> renderLprogAtt`, no jasminc) to
`gen_com/ntt_layer_fused_owned.s`. The KAT
(`bench/plonky3_compare/ntt_layer_fused_kat.c`,
`make plonky3-ntt-layer-fused-kat`) checks the fused leaf byte-identical to
the C reference applied twice AND to running the emitted single layer twice.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerInlineEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
  (r64 bbPNat vN twN qN constNat seqAll layerStmts outCopies srcCtx srcVM
   frontComOf inCtxt valOf samples allPureArith copyFlags comBindings)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

set_option autoImplicit false

/-! ## 1. The fused two-layer source -/

/-- The fused statement list: the single layer's statements, twice. The second
    copy reads the `v0..v7` names the first copy rebound — layer 1's outputs
    feed layer 2 by SSA rebinding, no intermediate buffer. Twiddles `tw0..tw3`
    are shared (the squaring stage the KAT models). -/
def fusedStmts : List LowCT := layerStmts ++ layerStmts

/-- **Fusion = source-level composition.** The fused source is definitionally
    the single-layer statement list (the one `Plonky3NttLayerEmit.layerCom` is
    front-compiled from) sequenced twice. -/
theorem fusedStmts_eq_two_layers :
    fusedStmts = Plonky3NttLayerEmit.layerStmts ++ Plonky3NttLayerEmit.layerStmts := rfl

/-- The full fused body: two layer bodies, then the eight output copies
    `q{i} := v{i}` (the last-eight-bindings output convention). -/
def fusedBody : LowCT := seqAll (fusedStmts ++ outCopies)

/-! ## 2. The front-emitted fused program -/

/-- The fused front program capped at slot `name` (same 18-word context and
    `VarMap` as the single layer). -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  frontComOf fusedBody name

/-- The front-emitted fused program, lowered to the jasmin dialect (capped at
    the final output copy `q7`, whose binding is the `Com`'s last). -/
def fusedLoweredOpt :=
  (frontComAt (qN 7)).bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem fusedLowered_isSome : fusedLoweredOpt.isSome := by native_decide

/-- The fused two-layer `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built.
    One straight-line pure-arith chain: layer 1's bindings followed by layer
    2's bindings, no marshalling between. -/
def fusedTwoLayerCom : Com jasminDialect inCtxt r64 :=
  fusedLoweredOpt.get fusedLowered_isSome

/-! ## 3. `denote = spec ∘ spec` vs the independent reference

The KAT reference is the single-layer C transcription applied twice with the
same twiddles (`ntt_layer_fused_kat.c`). `refLayerNat` mirrors
`Plonky3NttLayerEmit.refNttLayerList` at the `Nat` level so it can be
iterated. -/

/-- The single-layer reference on canonical residues (`Nat`, direct `%`):
    12 words `[v0..v7, tw0..tw3]` in, the 8 transformed values out. -/
def refLayerNat (s : List Nat) : List Nat :=
  let v : Nat → Nat := fun i => s.getD i 0
  let tw : Nat → Nat := fun j => s.getD (8 + j) 0
  let wb : Nat → Nat := fun j => (tw j * v (j + 4)) % bbPNat
  (List.range 4).map (fun j => (v j + wb j) % bbPNat)
    ++ (List.range 4).map (fun j => (v j + bbPNat - wb j) % bbPNat)

/-- The two-layer (squaring-stage) reference: the layer applied twice with the
    same four twiddles. -/
def refFusedList (s : List Nat) : List (BitVec 64) :=
  (refLayerNat (refLayerNat s ++ s.drop 8)).map (BitVec.ofNat 64)

/-- All eight output-capped fused front programs exist. -/
theorem frontComAt_q_isSome :
    (List.range 8).all (fun j => (frontComAt (qN j)).isSome) = true := by
  native_decide

/-- Denote the fused front program capped at slot `name` on a sample. -/
def frontDenoteAt (name : String) (s : List Nat) : Option (BitVec 64) :=
  (frontComAt name).map (fun c => c.denote (valOf s))

/-- **denote = layer ∘ layer.** The fused front program capped at output copy
    `q[j]` denotes word `j` of the independent single-layer reference applied
    TWICE on every sample (the `Plonky3NttLayerEmit.samples` set) — the
    in-model statement of fusion correctness the external KAT witnesses on
    bytes. -/
theorem fused_denote_spec :
    samples.all (fun s =>
      (List.range 8).all (fun j =>
        frontDenoteAt (qN j) s
          == some ((refFusedList s).getD j 0))) = true := by
  native_decide

/-! ## 4. Structural gates on the lowered `Com` -/

/-- Every binding is a pure scalar-arith op — one straight-line chain, no
    `extCall`, no `stackLoad`/`stackStore`, and in particular NO inter-layer
    store/load marshalling. -/
theorem fused_is_purearith_only : allPureArith fusedTwoLayerCom = true := by
  native_decide

/-- The **last eight bindings** are identity copies — the `q[0..7]` output
    copies the owned render's last-`nOut` epilogue stores to `out[0..7]`. -/
theorem fused_last_eight_bindings_are_copies :
    ((copyFlags fusedTwoLayerCom).drop ((copyFlags fusedTwoLayerCom).length - 8))
      = List.replicate 8 true := by native_decide

/-! ## 5. Binding count: the marshalling tax that disappears -/

/-- The fused `Com` carries exactly the two layer bodies' arithmetic bindings
    plus ONE shared 8-copy output epilogue (a single layer = one body + the
    same epilogue): `bindings(fused) + 8 = 2 · bindings(layer)`. No extra
    binding for the (eliminated) inter-layer marshalling. -/
theorem fused_bindings_eq :
    comBindings fusedTwoLayerCom + 8
      = 2 * comBindings Plonky3NttLayerEmit.layerCom := by native_decide

/-- The inter-layer marshalling moves a separate-call chain would emit between
    the two `export fn` calls (`2·nOut` copy-out + `2·nCopy` copy-in), which
    the fusion removes. -/
def interLayerMarshalMoves (nOut nCopy : Nat) : Nat := 2 * nOut + 2 * nCopy

/-- For the NTT layer ABI (`nOut = 8`, `nCopy = 8`) the fusion removes 32
    marshalling moves between the two layers. -/
theorem ntt_marshal_saving : interLayerMarshalMoves 8 8 = 32 := by native_decide

/-! ## 6. Owned `.s` emit (verified x86 backend, NO jasminc)

The fused `Com` is rendered straight to AT&T `.s` through the owned
linear-jasmin path `Com.toLprogPhysAbi -> renderLprogAtt` — the same path the
single-leaf `ntt_layer_from_rustcmd_owned.s` uses. The 18-word input ABI:
values `0..7` and twiddles `8..11` are runtime words `[RSI+8·idx]`; constants
`12..17` are immediates. The 8 outputs store to `[RDI+8·j]`. -/

/-- The standard `out[0..nOut-1]` store map: output word `j` → `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- `(immSlotMap, inLoadMap)` for an `nIn`-word context: constants →
    immediates, runtime words → `[RSI+8·idx]`; argument slot `s` ↦ input word
    `nIn-1-s`. -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-- Constants are input words `12..17` (`MU,p,0,30,32,63`) — same as the single
    layer's `nttLayerConstAt`. -/
def fusedConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 12 ∧ idx ≤ 17 then some (constNat (idx - 12)) else none

/-- The owned fused-leaf `Lprog`: the fused `Com` lowered to physical-ABI
    linear jasmin, export `plonky3_ntt_layer8x2_fused_rc`, 8-word output. -/
def fusedLprog : Lprog :=
  let (imm, inl) := abiMaps 18 fusedConstAt
  Com.toLprogPhysAbi fusedTwoLayerCom
    "plonky3_ntt_layer8x2_fused_rc" (fun _ => none) imm inl (stdOutStore 8)

def fusedAsm : String := renderLprogAtt fusedLprog

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- The owned `.s` carries the fused export label and no unhandled-op
    sentinel. -/
#guard (hasSub fusedAsm "plonky3_ntt_layer8x2_fused_rc")

#guard !(hasSub fusedAsm "UNHANDLED")

/-! ## 7. Emit driver -/

def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  IO.FS.writeFile
    "bench/plonky3_compare/gen_com/ntt_layer_fused_owned.s" fusedAsm
  IO.println "wrote gen_com/ntt_layer_fused_owned.s"
  IO.println "  TWO NTT layers FUSED at the LowCT source (layerStmts ++ layerStmts), front-compiled: no inter-layer copy-out/copy-in"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerInlineEmit

/-- Top-level entry point for `lake env lean --run` (writes the fused owned
    `.s` to `bench/plonky3_compare/gen_com/`). No clashing aggregator `main`:
    this module is not pulled into `SecureCompilationAll`. -/
def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerInlineEmit.emitMain
