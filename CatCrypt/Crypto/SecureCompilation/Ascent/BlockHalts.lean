/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem

/-!
# A straight-line block followed by `ret` halts on the address machine

A decoded straight-line function is a block `blk` of `JInstr 64` followed by `ret`: the
program `blk.map .op ++ [.ret]` of `LprogBytesDecode.RInstr`. Run on the address machine
`RInstrAddrMem.aMachine` from index `0`, it halts, through the relation
`RInstrSemantics.Halts` of the headline machine, in the state `AddrMem.runBlockA sa blk`
of the block fold. The statement holds for every block; the block condition
`InMovRegSubset` of the ascent route is a hypothesis of the transport to `x86Isa` only.

## Main results

* `reaches_runBlockA`: a segment of `op`s inside a program runs as `runBlockA`.
* `halts_of_runBlockA`: the program `blk.map .op ++ [.ret]` halts from index `0` in
  `runBlockA sa blk`.
* `halts_of_decodeLprog_block`: bytes that `decodeLprog` decodes to `blk.map .op ++ [.ret]`
  decode to a program that halts from index `0` in `runBlockA sa blk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.BlockHalts

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine aMachine_runBlock)

/-- A segment of `op`s inside a program runs on `aMachine` as the block fold `runBlockA`:
    from its first index the machine reaches the index after it in `runBlockA sa blk`. -/
theorem reaches_runBlockA (pre : List RInstr) (blk : List (JInstr 64)) (rest : List RInstr)
    (sa : AState) :
    Reaches aMachine (pre ++ blk.map .op ++ rest) pre.length sa (pre.length + blk.length)
      (runBlockA sa blk) := by
  rw [← aMachine_runBlock]
  exact reaches_ops aMachine pre blk rest sa

/-- **A straight-line block followed by `ret` halts in the block fold.** On `aMachine`, the
    program `blk.map .op ++ [.ret]` halts from index `0` and state `sa` in
    `runBlockA sa blk`. -/
theorem halts_of_runBlockA (blk : List (JInstr 64)) (sa : AState) :
    Halts aMachine (blk.map .op ++ [.ret]) 0 sa (runBlockA sa blk) := by
  refine halts_of_reaches (pc' := blk.length) ?_ ?_
  · simpa using reaches_runBlockA [] blk [.ret] sa
  · simp

/-- **Bytes decoding to a straight-line function halt in the block fold.** When
    `decodeLprog bs` is the block `blk` followed by `ret`, the decoded program halts on
    `aMachine` from index `0` and state `sa` in `runBlockA sa blk`. -/
theorem halts_of_decodeLprog_block {bs : List (BitVec 8)} {blk : List (JInstr 64)}
    (hdec : decodeLprog bs = some (blk.map .op ++ [.ret])) (sa : AState) :
    ∃ prog, decodeLprog bs = some prog ∧ Halts aMachine prog 0 sa (runBlockA sa blk) :=
  ⟨_, hdec, halts_of_runBlockA blk sa⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.BlockHalts
