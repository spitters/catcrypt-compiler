/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit

/-!
# WOTS+ position-tweaked CHAIN `wots_chain_n(x) = fold W over pos n..1`, OWNED x86

```
fn wots_chain(x, n) { for pos in n..1 { x = W(x, pos) } ; x }
```

Each step's tweak depends on the chain position: `W(x, pos) = ((x + GOLDEN) ^
(x >> 29)) ^ pos` (the treehash `Th` stand-in with the chain position mixed in),
`GOLDEN = 0x9E3779B97F4A7C15`, `SHIFT = 29`. An `n`-step chain visits positions
`n, n-1, …, 1`. FRONT-GENERATED via `rolledForLoopN` (value-ABI `ComL.toLprogPhys`,
`x → %rdi`, result → `%rax`); the front's ascending loop index `idx = 0..n-1` gives
`pos = n − idx` (so positions `n` down to `1`, matching the reference).

Byte-checked by `bench/wots_chain_owned/wots_kat.c` (`wots-owned-kat`): counts
`{0,1,2,8,16}` × (corners + 200k random) vs the folded `W` C reference.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.WotsChainEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit (occursIn)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- The WOTS `W` tweak constant `GOLDEN = 0x9E3779B97F4A7C15`. -/
def goldenNat : Nat := 11400714819323198485

/-- The leaf shift amount. -/
def wShift : Nat := 29

/-- The position counts the owned KAT exercises. -/
def levelCounts : List Nat := [0, 1, 2, 8, 16]

/-! ## 1. The position-tweaked rolled body + front-compiled chain -/

/-- The identity leaf body (`acc := acc`), for the `n = 0` empty chain. -/
def idBody : LowCT := .RScalarSetExpr "acc" (.SVar "acc")

/-- The WOTS leaf body at chain length `n`: `acc := ((acc + GOLDEN) ^ (acc >> 29))
    ^ pos` with `pos = n − idx` (the front index ascends `0..n-1`, so `pos` runs
    `n, n-1, …, 1`). -/
def wBody (n : Nat) : LowCT :=
  .RScalarSetExpr "acc"
    (.SXor
      (.SXor (.SAdd (.SVar "acc") (.SLit goldenNat)) (.SShr (.SVar "acc") (.SLit wShift)))
      (.SSub (.SLit n) (.SVar "idx")))

/-- The body `VarMap`: `acc` (accumulator, head) then `idx` (loop index). -/
def vmBody : VarMap (.sword 64 :: .sword 64 :: ([] : Ctx)) :=
  (VarMap.empty.bind "idx").bind "acc"

/-- The front-compiled `n`-step chain as a `ComL`. `n = 0` is a 1-trip loop over
    the identity body (seeds `%rax` from `%rdi`); `n ≥ 1` iterates `W` with the
    per-step position tweak. -/
def wChainComLOpt (n : Nat) : Option (ComL [r64] r64) :=
  if n = 0 then rolledForLoopN (Γouter := [r64]) (accCTy := .sword 64) (invCTys := [])
        1 vmBody "acc" idBody .here .nil
  else rolledForLoopN (Γouter := [r64]) (accCTy := .sword 64) (invCTys := [])
        n vmBody "acc" (wBody n) .here .nil

/-- The front translates + lowers all deployed position counts. -/
theorem wChain_all_isSome :
    levelCounts.all (fun n => (wChainComLOpt n).isSome) = true := by native_decide

/-- The deployed chain `ComL` (identity fallback, never taken). -/
def wChainComL (n : Nat) : ComL [r64] r64 := (wChainComLOpt n).getD (ComL.ret .here)

/-- The owned value-ABI `Lprog` for `wots_chain_n` (`%rdi` → `%rax`). -/
def wChainLprog (n : Nat) : Lprog :=
  ComL.toLprogPhys (wChainComL n) ("wots_chain_" ++ toString n)

/-- The rendered AT&T `.s` for `wots_chain_n`. -/
def wChainAsm (n : Nat) : String := renderLprogAtt (wChainLprog n)

/-! ## 2. Independent reference + emit -/

/-- One `W` step at position `pos`: `((x + GOLDEN) ^ (x >> 29)) ^ pos`. -/
def wStep (x : BitVec 64) (pos : Nat) : BitVec 64 :=
  (((x + BitVec.ofNat 64 goldenNat) ^^^ (x >>> wShift)) ^^^ BitVec.ofNat 64 pos)

/-- The independent folded reference: apply `W` at positions `n, n-1, …, 1`. -/
def wSpecN (n : Nat) (x : BitVec 64) : BitVec 64 :=
  (List.range n).foldl (fun acc i => wStep acc (n - i)) x

/-- Write the front-generated looped `.s` for every position count. -/
def emitMain : IO Unit := do
  let dir := "bench/wots_chain_owned/gen"
  IO.FS.createDirAll dir
  let body := String.intercalate "\n" (levelCounts.map wChainAsm)
  IO.FS.writeFile (dir ++ "/wots_chain_owned.s") (body ++ "\n")
  IO.println "WROTE bench/wots_chain_owned/gen/wots_chain_owned.s (front-generated, no jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.WotsChainEmit
