/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.KeccakJincImport
public import CatCrypt.Crypto.Jasmin.JincToLowCT
public meta import CatCrypt.Crypto.Jasmin.KeccakJincImport
public meta import CatCrypt.Crypto.Jasmin.JincToLowCT

/-!
# Emit the imported Keccak-f[1600]

Writes the owned AT&T text of `keccak_f1600` imported from the formosa-keccak
Jasmin source (`KeccakJincImport`) to
`bench/keccak_compare/gen_com/keccak_f1600_jinc_ref.s`, relative to the workspace
root the executable runs from. The artifact is the output; its values are checked
where it is consumed, by `bench/keccak_compare` (`make keccak-kat-jinc`) and
`bench/symcrust_compare`.

The round loop is kept rolled (`KeccakJincImport.keccakF1600RolledAsm`);
`--unrolled` writes the fully unrolled rendering (`keccakF1600Asm`) instead.
`--sponge` writes the sponges `sha3_256_jinc`, `shake128_jinc` and
`shake256_jinc` with the permutation they call (`keccakSpongeAsm`) to
`bench/keccak_compare/gen_com/sha3_jinc_ref.s`. `--x4` writes the four-way
permutation `keccak_f1600_x4` (`keccakF1600X4RolledAsm`) to
`bench/keccak_compare/gen_com/keccak_f1600_x4_jinc.s`; it exits non-zero when the
round loop was not kept rolled or the text holds a printer sentinel.

`keccakF1600_constant_time` states constant time of the rolled rendering over
`JincToLowCT.RolledCT.rolledLeak`, from the pointer registers and the address of
the round-constant table.

```
lake exe keccak-jinc-emit [--unrolled | --sponge | --x4]
```
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.KeccakJincEmit

/-- The directory the rendering is written to. -/
def outDir : String := "bench/keccak_compare/gen_com"

/-- The file name of the rendering. -/
def outFile : String := "keccak_f1600_jinc_ref.s"

/-- The file name of the sponge rendering. -/
def spongeOutFile : String := "sha3_jinc_ref.s"

/-- The file name of the four-way rendering. -/
def x4OutFile : String := "keccak_f1600_x4_jinc.s"

/-- An instruction line: tab-indented and neither a directive nor a comment. -/
def isInstrLine (l : String) : Bool :=
  l.startsWith "\t" && !l.startsWith "\t." && !l.startsWith "\t#"

/-- Whether a rendering holds a printer sentinel: an unhandled instruction or an
    unresolved operand. -/
def hasSentinel (asm : String) : Bool :=
  ["UNHANDLED", "<UNKNOWN", "<BAD", "<ARR:", "<NOTZMM"].any fun s => (asm.splitOn s).length > 1

/-- The program the owned printer receives for the rolled `keccak_f1600`
    (`JincElab.emitJFunRolledAsm`): `rolledLprog` with the round-constant table,
    then `ownedLprog`, `rorxLprog` and `ymmIndexFoldLprog`. -/
def keccakF1600Lprog : Option CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lprog :=
  match KeccakJincImport.keccakF1600Rolled with
  | .ok r => (JincElab.rolledLprog r.fn r.tables KeccakJincImport.keccakF1600Sym).map fun p =>
      JincElab.ymmIndexFoldLprog (JincElab.rorxLprog
        (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.ownedLprog p))
  | .error _ => none

/-- The public-register analysis accepts the compiled rolled `keccak_f1600` from
    the pointer arguments `RDI` (output) and `RSI` (input state) and the symbol
    `KECCAK1600_RC`, the address of the round-constant table. -/
theorem keccakF1600Lprog_check :
    keccakF1600Lprog.map (JincToLowCT.RolledCT.rolledLprogCheck ["RDI", "RSI", "KECCAK1600_RC"])
      = some true := by
  native_decide

/-- **Constant time of the rolled Keccak-f[1600].** The compiled `keccak_f1600`
    exists, its render is the text `main` writes (`keccakF1600RolledAsm`), and
    every function body in it is a rolled counted loop whose address-leak trace
    (`RolledCT.rolledLeak`: the instructions executed, the effective address of
    every register-indexed load and store, and each back-edge direction) is the
    same from any two states that agree on `RDI`, `RSI` and `KECCAK1600_RC`. The
    first two are the output and input pointers. `KECCAK1600_RC` holds the
    link-time address of the `.rodata` table of the 24 round constants, which are
    fixed by FIPS 202 and therefore public data. The state contents and every
    other register may differ. -/
theorem keccakF1600_constant_time :
    ∃ p, keccakF1600Lprog = some p ∧
      KeccakJincImport.keccakF1600RolledAsm
        = CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLprogAtt
            p none true ∧
      ∀ f ∈ p.lp_funcs, ∃ r : JincToLowCT.RolledCT.RolledShape,
        r.toBody = f.2.lfd_body.map (·.li_i) ∧
        ∀ (w fuel : Nat) (s₁ s₂ : CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem.Lstate w),
          JincToLowCT.RolledCT.Agree ["RDI", "RSI", "KECCAK1600_RC"] s₁ s₂ →
            JincToLowCT.RolledCT.rolledLeak r fuel s₁
              = JincToLowCT.RolledCT.rolledLeak r fuel s₂ := by
  have h := keccakF1600Lprog_check
  cases hp : keccakF1600Lprog with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
      rw [hp, Option.map_some, Option.some.injEq] at h
      refine ⟨p, rfl, ?_, JincToLowCT.RolledCT.rolledLprog_pub_determined _ p h⟩
      unfold keccakF1600Lprog at hp
      unfold KeccakJincImport.keccakF1600RolledAsm JincElab.emitJFunRolledAsm
      split at hp
      · rename_i r hr
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
        rw [hr]
        dsimp only
        rw [hq]
      · exact absurd hp (by simp)

end CatCrypt.Crypto.Jasmin.KeccakJincEmit

open CatCrypt.Crypto.Jasmin in
/-- Writes the four-way rendering `KeccakJincImport.keccakF1600X4RolledAsm`,
    exiting non-zero when the import or the elaboration fails, when the imported
    body has no rolled loop, or when the text holds a printer sentinel. -/
def emitX4 : IO UInt32 := do
  match KeccakJincImport.keccakF1600X4Rolled with
  | .error e =>
      IO.eprintln s!"keccak-jinc-emit: import failed: {e}"
      return 1
  | .ok r =>
      let rolled := r.fn.body.any fun (s : JincToCom.Stmt) => match s with
        | .forTo _ _ _ _ => true
        | _ => false
      unless rolled do
        IO.eprintln "keccak-jinc-emit: the round loop of keccak_f1600_x4 was not kept rolled"
        return 1
      let asm := JincElab.emitJFunRolledAsm r.fn r.tables KeccakJincImport.keccakF1600X4Sym
      if asm.startsWith ";" || KeccakJincEmit.hasSentinel asm then
        IO.eprintln s!"keccak-jinc-emit: rendering failed: {(asm.splitOn "\n").take 3}"
        return 1
      IO.FS.createDirAll KeccakJincEmit.outDir
      let path : System.FilePath :=
        System.FilePath.mk KeccakJincEmit.outDir / KeccakJincEmit.x4OutFile
      IO.FS.writeFile path asm
      let n := ((asm.splitOn "\n").filter KeccakJincEmit.isInstrLine).length
      IO.println s!"keccak-jinc-emit: wrote {path} ({r.fn.body.length} statements, {n} instruction lines)"
      return 0

open CatCrypt.Crypto.Jasmin in
/-- Writes the sponge rendering `KeccakJincImport.keccakSpongeAsm`, exiting
    non-zero when the import or the elaboration fails. -/
def emitSponge : IO UInt32 := do
  let asm := KeccakJincImport.keccakSpongeAsm
  if asm.startsWith ";" then
    IO.eprintln s!"keccak-jinc-emit: {asm}"
    return 1
  IO.FS.createDirAll KeccakJincEmit.outDir
  let path : System.FilePath :=
    System.FilePath.mk KeccakJincEmit.outDir / KeccakJincEmit.spongeOutFile
  IO.FS.writeFile path asm
  let n := ((asm.splitOn "\n").filter KeccakJincEmit.isInstrLine).length
  IO.println s!"keccak-jinc-emit: wrote {path} ({n} instruction lines)"
  return 0

open CatCrypt.Crypto.Jasmin in
/-- Imports `keccak_f1600` with its round loop kept rolled
    (`KeccakJincImport.keccakF1600Rolled`), or fully unrolled under `--unrolled`,
    renders it through the owned backend and writes the text, exiting non-zero
    when the import or the elaboration fails; `--sponge` writes the sponges
    (`emitSponge`) and `--x4` the four-way permutation (`emitX4`) instead. -/
def main (args : List String) : IO UInt32 := do
  if args.contains "--sponge" then return ← emitSponge
  if args.contains "--x4" then return ← emitX4
  let imported : Except String (JincToCom.JFun × String) :=
    if args.contains "--unrolled" then
      KeccakJincImport.keccakF1600JFun.map fun f =>
        (f, JincElab.emitJFunAsm f KeccakJincImport.keccakF1600Sym)
    else
      KeccakJincImport.keccakF1600Rolled.map fun r =>
        (r.fn, JincElab.emitJFunRolledAsm r.fn r.tables KeccakJincImport.keccakF1600Sym)
  match imported with
  | .error e =>
      IO.eprintln s!"keccak-jinc-emit: import failed: {e}"
      return 1
  | .ok (f, asm) =>
      IO.println s!"keccak-jinc-emit: imported {f.body.length} statements"
      if asm.startsWith ";" then
        IO.eprintln s!"keccak-jinc-emit: {asm}"
        return 1
      IO.FS.createDirAll KeccakJincEmit.outDir
      let path : System.FilePath :=
        System.FilePath.mk KeccakJincEmit.outDir / KeccakJincEmit.outFile
      IO.FS.writeFile path asm
      let n := ((asm.splitOn "\n").filter KeccakJincEmit.isInstrLine).length
      IO.println s!"keccak-jinc-emit: wrote {path} ({n} instruction lines)"
      return 0
