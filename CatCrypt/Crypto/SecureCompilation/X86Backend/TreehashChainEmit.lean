/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit

/-!
# Treehash CHAIN `treehash_chain_n(node) = (Th)^n(node)`, OWNED x86 (front-generated)

```
fn treehash_chain(node, N) { for _ in 0..N { node = Th(node) } ; node }
```

The FAEST/SPHINCS-style treehash chain iterates a single-input leaf-commitment
stand-in `Th(x) = (x + GOLDEN) ^ (x >> 29)` (`GOLDEN = 11400714819323198485`)
`N` times. FRONT-GENERATED: the leaf body is a covered `LowCT` compiled by
`rolledForLoopN` (= `translateDialectControl` + `cryptoDialectToJasminCom` wrapped
in `ComL.forLoopN`), a real one-body-copy counted loop with a `jne` back-edge, then
lowered value-ABI via `ComL.toLprogPhys` (scalar arg `%rdi` → result `%rax`). No
jasminc, no hand-`Lcmd`.

## ABI

`uint64_t treehash_chain_n(uint64_t node0);` — `node0 → %rdi`, result → `%rax`.
`n = 0` is the straight-line identity (`movq %rdi, %rax`). Byte-checked by
`bench/thir_front_treehash_owned/` (`treehash-owned-kat`, corners + 200k random per
count, byte-identical to the N-fold `Th` C reference).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.TreehashChainEmit

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

/-- The leaf-commitment stand-in constant `GOLDEN`. -/
def goldenNat : Nat := 11400714819323198485

/-- The leaf shift amount. -/
def thShift : Nat := 29

/-- The level counts the owned KAT exercises (baked into each function's bound). -/
def levelCounts : List Nat := [0, 1, 2, 8, 16]

/-! ## 1. The rolled leaf body + front-compiled chain -/

/-- The covered `LowCT` leaf body: `acc := (acc + GOLDEN) ^ (acc >> 29) = Th(acc)`. -/
def thBody : LowCT :=
  .RScalarSetExpr "acc"
    (.SXor (.SAdd (.SVar "acc") (.SLit goldenNat)) (.SShr (.SVar "acc") (.SLit thShift)))

/-- The body `VarMap`: `acc` (the accumulator, head) then `idx` (the loop index). -/
def vmBody : VarMap (.sword 64 :: .sword 64 :: ([] : Ctx)) :=
  (VarMap.empty.bind "idx").bind "acc"

/-- The identity leaf body (`acc := acc`): the `RScalarSetExpr` arm force-binds a
    copy, so a 1-trip loop over it threads `init` through unchanged. -/
def idBody : LowCT := .RScalarSetExpr "acc" (.SVar "acc")

/-- The front-compiled `n`-trip chain as a `ComL` (`none` if the front declines).
    `n = 0` is a 1-trip loop over the IDENTITY body (a bare `ComL.ret` of the arg
    does not seed `%rax` from `%rdi` under `toLprogPhys`), so it threads `node0`
    through unchanged; `n ≥ 1` iterates `Th`. -/
def thChainComLOpt (n : Nat) : Option (ComL [r64] r64) :=
  if n = 0 then rolledForLoopN (Γouter := [r64]) (accCTy := .sword 64) (invCTys := [])
        1 vmBody "acc" idBody .here .nil
  else rolledForLoopN (Γouter := [r64]) (accCTy := .sword 64) (invCTys := [])
        n vmBody "acc" thBody .here .nil

/-- The front translates + lowers all deployed level counts. -/
theorem thChain_all_isSome :
    levelCounts.all (fun n => (thChainComLOpt n).isSome) = true := by native_decide

/-- The deployed chain `ComL` (identity fallback, never taken by `isSome`). -/
def thChainComL (n : Nat) : ComL [r64] r64 := (thChainComLOpt n).getD (ComL.ret .here)

/-- The owned value-ABI `Lprog` for `treehash_chain_n` (`%rdi` → `%rax`). -/
def thChainLprog (n : Nat) : Lprog :=
  ComL.toLprogPhys (thChainComL n) ("treehash_chain_" ++ toString n)

/-- The rendered AT&T `.s` for `treehash_chain_n` (function-scoped `.L` labels). -/
def thChainAsm (n : Nat) : String := renderLprogAtt (thChainLprog n)

/-! ## 2. The independent leaf reference + emit -/

/-- `Th(x) = (x + GOLDEN) ^ (x >> 29)` in `BitVec 64`. -/
def thStep (x : BitVec 64) : BitVec 64 :=
  (x + BitVec.ofNat 64 goldenNat) ^^^ (x >>> thShift)

/-- The independent `n`-fold reference `(Th)^n`. -/
def thSpecN : Nat → BitVec 64 → BitVec 64
  | 0, x => x
  | n + 1, x => thSpecN n (thStep x)

/-- Write the front-generated looped `.s` for every level count into the harness
    directory. Each `treehash_chain_n` has a per-function label prefix, so the
    local `.L` labels are unique across the functions concatenated into one `.s`. -/
def emitMain : IO Unit := do
  let dir := "bench/thir_front_treehash_owned/gen"
  IO.FS.createDirAll dir
  let body := String.intercalate "\n" (levelCounts.map thChainAsm)
  IO.FS.writeFile (dir ++ "/treehash_chain_owned.s") (body ++ "\n")
  IO.println "WROTE bench/thir_front_treehash_owned/gen/treehash_chain_owned.s (front-generated, no jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.TreehashChainEmit
