/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportPoseidon2
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2ResidenceAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Compiled Poseidon2-BabyBear linear-jasmin owned-RA producer (task #504)

The producer for the Poseidon2 owned-RA bench, compiled as a `lean_exe`
(`lake exe poseidon2linear`) so it runs as native code. The `lean --run`
interpreter cannot materialize `Poseidon2WholePermCom.poseidon2PermComOut` (a
deep straight-line term, on the order of SHA-256 / Keccak): it blows the
interpreter recursion stack and runs the super-quadratic spec definitions of
`nameSlot` / `physTable` / `physBodyWithStores`. Compiled, the C call stack
handles the deep term and the `@[implemented_by]` fast paths in
`JasminLprogExport` fire (single-pass `Array` / `Std.HashMap` builds replace the
spec's O(n³) `nameSlot` and per-position `bidx` recomputation).

Poseidon2-BabyBear is U64 throughout, so the body's `regArith _ 64` ops, the ABI
state-lane loads, and the output stores are all 64-bit; the emitted blob carries
the `:64` width tag on its body mnemonics and the patched `read_linear`
materialises them at U64.
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi Com.writeLprogPhysAbiFile
   poseidon2ImmSlots poseidon2InLoadMap poseidon2OutStoreMap
   comToLfundef residenceOfBody)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
  (poseidon2PermComOut)

def main : IO UInt32 := do
  let outPath : System.FilePath :=
    "bench/poseidon2_linear_compare/poseidon2_bb.lprogbin"
  IO.println s!"poseidon2_linear: link 1/7 (Com -> ABI-wrapped Linear.lprog) [compiled]"
  -- Register-RESIDENCE coalescing (#476): collapse the ≈107k per-binding SSA
  -- names onto their physical residence slots so the linear-scan allocator keeps
  -- the working state register-resident across the 21 rounds instead of spilling
  -- it every round (the X25519 monolithic-RA move #411/#412, at Poseidon2's 17×
  -- gcc-O3 headroom).
  --
  -- `residenceOfBody` assigns each binding a physical-slot index by first-fit
  -- over its live range `[def, last-use]` (`Poseidon2ResidenceAlloc.allocFold`),
  -- so two bindings share a slot only when their ranges do not overlap — the 16
  -- MDS lanes live in the external-MDS step receive 16 distinct slots. The trace
  -- is `bodyTraceOut`, whose appended output-read event keeps every designated
  -- output lane live to the epilogue store. `allocFold_pairwise_disj` proves
  -- ranges sharing a slot are non-overlapping. The prior `slotTraceArr` collapse
  -- (one class per logical slot) under-counted liveness and clobbered live lanes.
  let poseidon2Body :=
    (comToLfundef (poseidon2PermComOut ()) poseidon2ImmSlots).lfd_body
  -- Held at `none`. `residenceOfBody` is proven interference-free
  -- (`allocFold_pairwise_disj`) and KAT-correct, and its liveness is now precise
  -- (computed over the emit-time `materializeShiftCountImms` body). But Poseidon2
  -- is shift-free, so the precise body equals the raw body here: measured A/B is
  -- byte-identical to the over-approximated version (28343 stack refs, ~39032
  -- cyc/op) vs `none` at 33848 / 2287. Poseidon2's regression is not from liveness
  -- over-approximation but from the residence pre-colouring itself losing to the
  -- unconstrained linear-scan on this kernel. The allocator ships proven-but-unwired.
  let residence : Option (Array Nat) :=
    none
  let lp : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
    Com.toLprogPhysAbi (poseidon2PermComOut ()) "poseidon2_bb_permute"
              (fun _ => none) poseidon2ImmSlots
              poseidon2InLoadMap poseidon2OutStoreMap
              (residence := residence)
  IO.println s!"  functions     : {lp.lp_funcs.length}"
  match lp.lp_funcs.head? with
  | some (name, f) =>
      IO.println s!"  function name : {name}"
      IO.println s!"  args          : {f.lfd_arg.length} (2-pointer SysV ABI expected)"
      IO.println s!"  body linstrs  : {f.lfd_body.length} (prologue + two-addr + epilogue)"
      let mut maxSpill : Int := -1
      for li in f.lfd_body do
        match li.li_i with
        | .Lopn dsts _ srcs =>
            for o in (dsts ++ srcs) do
              match o with
              | .reg nm =>
                  if "k.".isPrefixOf nm then
                    match (nm.drop 2).toNat? with
                    | some k => if (k : Int) > maxSpill then maxSpill := k
                    | none => pure ()
              | _ => pure ()
        | _ => pure ()
      IO.println s!"  max spill k.N : {maxSpill}  (reserved frame holds {maxSpill + 1} U64 spill cells + 8 qsave)"
  | none => pure ()
  Com.writeLprogPhysAbiFile (poseidon2PermComOut ()) "poseidon2_bb_permute" outPath
    (fun _ => none) poseidon2ImmSlots poseidon2InLoadMap poseidon2OutStoreMap
    (residence := residence)
  let sz := (← outPath.metadata).byteSize
  IO.println s!"link 1/7 OK : {outPath} written ({sz} bytes)"
  -- OWNED path (task #537): render the SAME `Lprog` to AT&T `.s` directly.
  let ownedPath : System.FilePath :=
    "bench/poseidon2_compare/gen/poseidon2_bb_permute_x86_from_lean.s"
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
  let t0 ← IO.monoNanosNow
  IO.FS.writeFile ownedPath asm
  let t1 ← IO.monoNanosNow
  IO.println s!"OWNED emit OK : {ownedPath} written ({asm.toUTF8.size} bytes, owned render {(t1 - t0) / 1000} us)"
  return 0
