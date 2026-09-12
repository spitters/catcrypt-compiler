/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Stage-wise timing of the point-op producer pipeline

Runs the pipeline as explicit function calls — descend, cap, lower, ABI,
render — with a timestamp printed and flushed after each stage, so a killed run
still attributes its time to a stage. Writes the jacDbl `.s` if it reaches the
end. `main` prints before the first stage, which also separates module-load
cost from `main`'s own work in the native executable.
-/

@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront

def stamp (out : IO.FS.Stream) (label : String) (t0 : Nat) : IO Nat := do
  let t ← IO.monoMsNow
  out.putStrLn s!"{label}: {t - t0} ms"
  out.flush
  return t

def main : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "stage probe start (native)"; out.flush
  let t0 ← IO.monoMsNow
  match translateDialectControl inVM2 jacDblBody with
  | none => out.putStrLn "descend: NONE"
  | some o => do
    let t1 ← stamp out "descend (translateDialectControl)" t0
    match o.vm.lookup "out" with
    | some ⟨.memref 12, vv⟩ => do
      match o.cont (Com.ret (toVIRVar vv)) with
      | none => out.putStrLn "cap: NONE"
      | some com => do
        let t2 ← stamp out "cap (cont ∘ ret)" t1
        match cryptoDialectToJasminCom com with
        | none => out.putStrLn "lower: NONE"
        | some jcom => do
          let t3 ← stamp out "lower (cryptoDialectToJasminCom)" t2
          let lp := Com.toLprogPhysAbi jcom "secp256k1_jac_dbl"
            (fun _ => none) (fun _ => none) (fun _ => none) []
            (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64])
            (residence := none) (abiW := 0) (forceLivePin := true)
          let t4 ← stamp out "abi (toLprogPhysAbi)" t3
          let s := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
          let t5 ← stamp out "render (renderLprogAtt)" t4
          out.putStrLn s!"rendered {s.length} chars"; out.flush
          IO.FS.createDirAll "bench/secp256k1_pointop_front_compare/gen_com"
          IO.FS.writeFile
            "bench/secp256k1_pointop_front_compare/gen_com/secp256k1_jac_dbl_probe.s" s
          let _ ← stamp out "total" t0
    | _ => out.putStrLn "lookup: out is not memref 12"
