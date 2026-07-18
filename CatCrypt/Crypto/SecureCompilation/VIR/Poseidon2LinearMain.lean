/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportPoseidon2
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

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

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi Com.writeLprogPhysAbiFile
   poseidon2ImmSlots poseidon2InLoadMap poseidon2OutStoreMap)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
  (poseidon2PermComOut slotTraceArr)

private def main : IO UInt32 := do
  let outPath : System.FilePath :=
    "bench/poseidon2_linear_compare/poseidon2_bb.lprogbin"
  IO.println s!"poseidon2_linear: link 1/7 (Com -> ABI-wrapped Linear.lprog) [compiled]"
  -- Register-RESIDENCE coalescing (#476): collapse the ≈107k per-binding SSA
  -- names onto the 25 logical working slots (16 lanes + 9 scratch) so the
  -- linear-scan allocator keeps the working state register-resident across the
  -- 21 rounds instead of spilling it every round (the X25519 monolithic-RA move
  -- #411/#412, applied at Poseidon2's 17× gcc-O3 headroom).
  -- DISABLED: the residence-rename slot-trace under-counts liveness on the
  -- 16-lane MDS step (16 values live simultaneously), so collapsing to 25 slots
  -- clobbers live lanes and the Plonky3 KAT MISMATCHes. Sound register-residence
  -- here needs a real interference analysis, not this sequential-reuse slot-trace.
  let residence : Option (Array Nat) := none
  let _ := slotTraceArr  -- machinery retained for a future interference-aware version
  let residence := residence
  let lp : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
    Com.toLprogPhysAbi poseidon2PermComOut "poseidon2_bb_permute"
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
  Com.writeLprogPhysAbiFile poseidon2PermComOut "poseidon2_bb_permute" outPath
    (fun _ => none) poseidon2ImmSlots poseidon2InLoadMap poseidon2OutStoreMap
    (residence := residence)
  let sz := (← outPath.metadata).byteSize
  IO.println s!"link 1/7 OK : {outPath} written ({sz} bytes)"
  -- OWNED path (task #537): render the SAME `Lprog` to AT&T `.s` directly.
  let ownedPath : System.FilePath :=
    "bench/poseidon2_compare/gen/poseidon2_bb_permute_x86_from_lean.s"
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt lp
  let t0 ← IO.monoNanosNow
  IO.FS.writeFile ownedPath asm
  let t1 ← IO.monoNanosNow
  IO.println s!"OWNED emit OK : {ownedPath} written ({asm.toUTF8.size} bytes, owned render {(t1 - t0) / 1000} us)"
  return 0
