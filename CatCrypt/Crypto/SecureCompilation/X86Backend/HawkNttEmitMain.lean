/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.HawkNttEmit

/-!
# Compiled HAWK mod-18433 NTT owned-emit producer

`lake exe hawknttowned` renders the three verified `HawkNttEmit` Coms
(`nttBflyCom` / `inttBflyCom` / `pointwiseCom`) straight to AT&T `.s` through the
owned backend (`toLprogPhysAbi → renderLprogAtt`), no jasminc. The 512-coeff
`pointwiseCom` overflows the `lean --run` interpreter stack, so native is
required (as `poseidon2scalarowned` / `plonky3owned`). The emitted `.s` symbols
(`hawk18433_ntt_bfly` etc.) and the `reg ptr u32 out, reg const ptr u32 inp` ABI
match `bench/hawk_compare/hawk_ntt_kat.c`'s externs exactly.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.HawkNttEmit

def main : IO Unit := do
  IO.FS.createDirAll "bench/hawk_compare/gen"
  IO.FS.writeFile "bench/hawk_compare/gen/hawk18433_ntt_bfly.s" hawkNttBflyAsm
  IO.FS.writeFile "bench/hawk_compare/gen/hawk18433_intt_bfly.s" hawkInttBflyAsm
  IO.FS.writeFile "bench/hawk_compare/gen/hawk18433_pointwise_montymul.s" hawkPointwiseAsm
  IO.println "wrote bench/hawk_compare/gen/hawk18433_{ntt_bfly,intt_bfly,pointwise_montymul}.s (OWNED, no jasminc)"
