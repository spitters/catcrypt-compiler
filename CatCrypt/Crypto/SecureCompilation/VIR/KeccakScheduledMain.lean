/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportKeccak
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# ILP-scheduled Keccak-p[1600,24] owned producer

The same owned `keccak_f1600` linear-jasmin emit as `KeccakLinearMain`, but with
the virtual (pre-RA) body run through the **verified instruction-scheduling pass**
`LprogScheduler.scheduleBodyTail` before register allocation. The pass reorders
the straight-line `Lopn`s of the 24-round θ/ρ/π/χ/ι body by adjacent
footprint-disjoint swaps (latency-priority bubble), overlapping the otherwise
serial dependency chains, then RA / two-address lowering / ABI wrapping run
exactly as in the unscheduled owned path — over the *scheduled* body.

The output-staging tail (the last 25 bindings, whose results the ABI epilogue
stores to `out`) is kept fixed (`scheduleBodyTail nOut := 25`), so the epilogue
still stores the right bindings.

Soundness: the scheduled body is a permutation of the unscheduled one
(`scheduleBody_perm`) and every swap is between footprint-disjoint instructions
(`bubble_only_indep_swaps`), so it computes the same Keccak permutation. KAT'd
byte-identical against XKCP / the FAEST official vector in `bench/keccak_compare/`.

`keccakF1600Com` is a ~6900-binding term; the `lean --run` interpreter overflows
on it, so this is a compiled `lake exe keccakscheduled` (the `@[implemented_by]`
fast paths in `JasminLprogExport` fire under native code).
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (Com.toLprogPhysAbiScheduled)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
  (elimReloadsLprog countRemovedLprog)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (keccakImmSlots keccakInLoadMap keccakOutStoreMap)
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit (keccakF1600Com)

def main : IO UInt32 := do
  IO.println s!"keccak_scheduled: link (Com -> SCHEDULED virtual body -> RA -> owned .s) [compiled]"
  -- Keep the last 26 list elements fixed: the 25 output-staging `Lopn` bindings
  -- (the ABI epilogue's store targets, selected as the last `numBindings - 25`)
  -- PLUS the trailing `Lret` that `comToBody` appends. Everything before — the
  -- 24 θ/ρ/π/χ/ι rounds — is ILP-scheduled.
  let lp0 : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
    Com.toLprogPhysAbiScheduled keccakF1600Com "keccak_f1600" 26
              (fun _ => none) keccakImmSlots keccakInLoadMap keccakOutStoreMap
  -- Verified redundant-reload elimination (a verified CSE of repeated
  -- `movq <off>(%rsp),%rN` spill reloads
  -- with no intervening write). `elimReloadsLprog` drops every reload whose
  -- register provably already holds the slot; the output is a sublist of the
  -- input (`elimReloads_sublist`) and every drop is a held reload
  -- (`stepReload_drop_is_held_reload`), so the emitted `.s` is value-identical.
  let removed := countRemovedLprog lp0
  let lp := elimReloadsLprog lp0
  IO.println s!"  functions     : {lp.lp_funcs.length}"
  IO.println s!"  redundant reloads removed (verified CSE) : {removed}"
  match lp.lp_funcs.head? with
  | some (name, f) =>
      IO.println s!"  function name : {name}"
      IO.println s!"  body linstrs  : {f.lfd_body.length} (prologue + scheduled two-addr + epilogue, CSE'd)"
  | none => pure ()
  let ownedPath : System.FilePath :=
    "bench/keccak_compare/gen/keccak_f1600_scheduled.s"
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
  let unoptMovq := ((CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt lp).splitOn "movq").length - 1
  IO.println s!"  optimizer movq  : unopt {unoptMovq} -> opt {(asm.splitOn "movq").length - 1}"
  let t0 ← IO.monoNanosNow
  IO.FS.writeFile ownedPath asm
  let t1 ← IO.monoNanosNow
  IO.println s!"OWNED scheduled emit OK : {ownedPath} written ({asm.toUTF8.size} bytes, render {(t1 - t0) / 1000} us)"
  return 0
