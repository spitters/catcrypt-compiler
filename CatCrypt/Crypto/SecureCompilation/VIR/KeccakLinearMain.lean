/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportKeccak
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakRotateSelect
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
public import CatCrypt.Crypto.Optimizer.LoadCSE
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Compiled Keccak-p[1600,24] linear-jasmin owned-RA producer

The same producer as `bench/keccak_compare/keccak_linear.lean`, compiled as a
`lean_exe` (`lake exe keccaklinear`) so it runs as native code. The `lean --run`
interpreter cannot materialize `KeccakEmit.keccakF1600Com` (a ~6900-binding
straight-line term — deeper than SHA-256's ~4000): it blows the interpreter
recursion stack and runs the super-quadratic spec definitions of `nameSlot` /
`physTable` / `physBodyWithStores`. Compiled, the C call stack handles the deep
term and the `@[implemented_by]` fast paths in `JasminLprogExport` fire
(single-pass `Array` / `Std.HashMap` builds replace the spec's O(n³) `nameSlot`
and per-position `bidx` recomputation).

Keccak is U64 throughout, so the body's `regArith _ 64` ops, the ABI state-lane
loads, and the output stores are all 64-bit; the emitted blob carries the
`:64` width tag on its body mnemonics (see `JasminLprogExport.binOpName`) and
the patched `read_linear` materialises them at U64.
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi Com.writeLprogPhysAbiFile
   keccakImmSlots keccakInLoadMap keccakOutStoreMap)
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit (keccakF1600Com)

def main : IO UInt32 := do
  let outPath : System.FilePath := "bench/keccak_compare/gen/keccak_f1600.lprogbin"
  IO.println s!"keccak_linear: link 1/7 (Com -> ABI-wrapped Linear.lprog) [compiled]"
  let lp : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
    Com.toLprogPhysAbi keccakF1600Com "keccak_f1600"
              (fun _ => none) keccakImmSlots
              keccakInLoadMap keccakOutStoreMap
  IO.println s!"  functions     : {lp.lp_funcs.length}"
  match lp.lp_funcs.head? with
  | some (name, f) =>
      IO.println s!"  function name : {name}"
      IO.println s!"  args          : {f.lfd_arg.length} (2-pointer SysV ABI expected)"
      IO.println s!"  body linstrs  : {f.lfd_body.length} (prologue + two-addr + epilogue)"
      -- Report the maximum k.N spill index so the reserved-frame model
      -- can be checked: read_linear sizes the frame from the highest spill index.
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
  Com.writeLprogPhysAbiFile keccakF1600Com "keccak_f1600" outPath
    (fun _ => none) keccakImmSlots keccakInLoadMap keccakOutStoreMap
  let sz := (← outPath.metadata).byteSize
  IO.println s!"link 1/7 OK : {outPath} written ({sz} bytes)"
  -- OWNED path: render the SAME `Lprog` to AT&T `.s` directly.
  -- Verified redundant-reload elimination before rendering (the
  -- verified-native CSE of repeated `movq <off>(%rsp),%rN` spill reloads). The
  -- eliminated body is a sublist of the input (`elimReloads_sublist`) and every
  -- drop is a held reload (`stepReload_drop_is_held_reload`), value-identical.
  let removed := CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.countRemovedLprog lp
  let lp := CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.elimReloadsLprog lp
  IO.println s!"  redundant reloads removed (verified CSE) : {removed}"
  -- Verified CROSS-REGISTER load-CSE after the same-register reload
  -- drop. `loadCSELprog` redirects a second load of a slot already held in a
  -- different register onto that register (memory load -> register move), the
  -- generic compiler pass that yields the χ B-lane register reuse. The
  -- output is the same length (`loadCSE_length`); every changed instruction is a
  -- held-load register move (`loadCSEAux_pointwise`), value-identical.
  let cseRewrites := CatCrypt.Crypto.Optimizer.LoadCSE.countRewritesLprog lp
  -- `lpCSE` is the load-CSE'd program used for the AT&T `.s` render (gas/KAT). The
  -- byte-encode path below keeps the pre-load-CSE `lp`: the looped byte encoder
  -- does not encode a register-to-register `movq %r,%r` (the move the
  -- rewrite produces), so the bytes-direct `.o` uses the elimReloads-only body.
  let lpCSE := CatCrypt.Crypto.Optimizer.LoadCSE.loadCSELprog lp
  IO.println s!"  cross-register loads -> reg moves (verified load-CSE) : {cseRewrites}"
  IO.FS.createDirAll "bench/keccak_compare/gen"
  let ownedPath : System.FilePath := "bench/keccak_compare/gen/keccak_f1600_x86_from_lean.s"
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lpCSE
  let t0 ← IO.monoNanosNow
  IO.FS.writeFile ownedPath asm
  let t1 ← IO.monoNanosNow
  IO.println s!"OWNED emit OK : {ownedPath} written ({asm.toUTF8.size} bytes, owned render {(t1 - t0) / 1000} us)"
  -- BYTES-DIRECT path: byte-encode the SAME `Lprog` straight to an ELF
  -- `.o` via `LprogBytes.encodeLprog` (the looped byte encoder, which covers the
  -- `%rsp`-relative spill/qsave slots Keccak's heavy U64 register pressure uses),
  -- NO assembler; plus the function body `.text` + a matching body-only `.s` for a
  -- differential KAT byte-identical to the gas-assembled `renderLprogAtt` `.text`.
  let toBA : List (BitVec 8) → ByteArray := fun bs =>
    ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩
  let oBytes := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes.encodeLprog lp
  IO.FS.writeBinFile "bench/keccak_compare/gen/keccak_f1600_owned_enc.o" (toBA oBytes)
  match lp.lp_funcs.head? with
  | some (nm, f) =>
      let body := f.lfd_body
      let textBytes := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes.encodeLcmd body
      IO.FS.writeBinFile "bench/keccak_compare/gen/keccak_f1600_owned_enc_text.bin" (toBA textBytes)
      let frame := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.frameSize body
      let spillW := if CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.bodyIsU64 body
                    then 64 else 32
      let bodyLines := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLcmd
                         frame spillW body ""
      let bodyS := "\t.text\n\t.globl " ++ nm ++ "_body\n" ++ nm ++ "_body:\n"
                     ++ String.intercalate "\n" bodyLines ++ "\n"
                     ++ "\t.section .note.GNU-stack,\"\",@progbits\n"
      IO.FS.writeFile "bench/keccak_compare/gen/keccak_f1600_owned_body.s" bodyS
      IO.println s!"BYTES emit OK : keccak_f1600_owned_enc.o ({oBytes.length} bytes ELF), body .text = {textBytes.length} bytes (incl. spill slots, frame={frame}, spillW={spillW})"
  | none => pure ()
  return 0
