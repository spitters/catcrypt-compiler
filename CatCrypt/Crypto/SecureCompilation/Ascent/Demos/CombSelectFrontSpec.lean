/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront

/-!
# A shared value specification for the two Ed25519 comb selects

The comb table select has two implementations: the conditional-move block
`CombSelectKernel.combSelectBlock = selBlock 16`, whose value result is
`Fe25519AddSubSelectProof.selBlock_correct` over `runBlock`, and the mask/and/xor
scan `CombSelectFront.combSelectFront N`, whose value result is
`CombSelectFront.combSelectFront_denote` over `Com.denote`. The two are different
algorithms over different semantics; this module states one specification both
meet and derives their agreement from it.

The specification is `selectedWord`: over a table read as a flat word-indexed
array, word `k` of entry `d` is array cell `4·d + k`. The machine side reads the
bank `"tbl"` at byte offset `8·j`, which turns `selBlock_correct`'s
`32·D + 8·k` into `selectedWord` at `4·D + k`; the denotation side reads the
`memref (4·N)` argument at word index `j`.

## Scope

Both sides are stated for an index below the entry count. Outside that range the
two implementations still agree (both leave the accumulators at zero) but the
statements here do not cover it: `selectedWord` is the in-range specification
only.

`combSelectFront_selBlock_agree` relates the two implementations only under a
hypothesis equating their table images cell by cell. It is a statement about
values, not about aliasing or calling convention: the machine model keys memory
by base-register name, so the output bank `"z"` is disjoint from `"tbl"` by
construction.

## Main results

* `selectedWord`: the shared specification, word `k` of entry `d`.
* `combSelectFront_meets_spec`: the front output's denotation is `selectedWord`
  of the table argument.
* `selBlock_meets_spec`: `selBlock n` stores `selectedWord` of the `"tbl"` bank.
* `combSelectFront_selBlock_agree`: for tables with equal images, the front
  output's denotation is word for word what `selBlock N` stores.
* `combSelectFront2_witness`: a two-entry table with distinct concrete words, at
  both indices, with the four selected words named as constants.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectFrontSpec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel (selBlock)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof (selBlock_correct)

/-! ## 1. The specification -/

/-- Word `k` of entry `d` of a table read as a flat word-indexed array: cell
    `4·d + k`. -/
def selectedWord (read : Nat → BitVec 64) (d k : Nat) : BitVec 64 :=
  read (4 * d + k)

/-! ## 2. The front output meets it -/

/-- **The front output denotes the specification.** For an index below the entry
    count, the program `combSelectFront N` produces returns, in word `k`, cell
    `4·D + k` of the table argument. -/
theorem combSelectFront_meets_spec (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64)
    (hD : D.toNat < N) :
    ∃ com, combSelectFront N = some com
      ∧ ∀ k : Fin 4, com.denote (selVal N O D T) k
          = selectedWord (memGetDyn T) D.toNat k.val := by
  obtain ⟨com, hf, -, hden⟩ := combSelectFront_denote N hN O D T
  refine ⟨com, hf, fun k => ?_⟩
  rw [hden]
  simp only [if_pos hD, selectedWord]

/-! ## 3. The conditional-move block meets it -/

/-- **The conditional-move block stores the specification.** Reading the bank
    `"tbl"` at byte offset `8·j` as array cell `j`, `selBlock n` stores at
    `[z + 8·k]` cell `4·D + k`. -/
theorem selBlock_meets_spec (n : Nat) (hn : n ≤ 2 ^ 64) (st : JState 64)
    (hd : (st.regs "d").toNat < n) (k : Nat) (hk : k < 4) :
    (runBlock st (selBlock n)).mem "z" (8 * (k : Int))
      = selectedWord (fun j => st.mem "tbl" (8 * (j : Int))) (st.regs "d").toNat k := by
  rw [(selBlock_correct n hn st hd).1 k hk]
  simp only [selectedWord]
  congr 1
  push_cast
  ring

/-! ## 4. Agreement -/

/-- **The two implementations agree on values.** When the machine table bank
    holds the image of the denotation's table argument, the front output denotes
    word for word what `selBlock N` stores. -/
theorem combSelectFront_selBlock_agree (N : Nat) (hN : 4 * N ≤ 2 ^ 64)
    (O : Fin 4 → BitVec 64) (D : BitVec 64) (T : Fin (4 * N) → BitVec 64)
    (hD : D.toNat < N) (st : JState 64) (hreg : st.regs "d" = D)
    (htbl : ∀ j : Nat, j < 4 * N → st.mem "tbl" (8 * (j : Int)) = memGetDyn T j) :
    ∃ com, combSelectFront N = some com
      ∧ ∀ k : Fin 4, com.denote (selVal N O D T) k
          = (runBlock st (selBlock N)).mem "z" (8 * (k.val : Int)) := by
  obtain ⟨com, hf, hden⟩ := combSelectFront_meets_spec N hN O D T hD
  refine ⟨com, hf, fun k => ?_⟩
  have hdreg : (st.regs "d").toNat < N := by rw [hreg]; exact hD
  rw [hden k, selBlock_meets_spec N (by omega) st hdreg k.val k.isLt, hreg]
  simp only [selectedWord]
  have hk : k.val < 4 := k.isLt
  exact (htbl (4 * D.toNat + k.val) (by omega)).symm

/-! ## 5. A concrete witness

`witTbl` is the two-entry table whose entry `j` holds the words
`0x1000·(j+1) + 0 … 0x1000·(j+1) + 3`, so every one of its eight cells is a
distinct constant. `combSelectFront2_witness` names the four selected words at
both indices; a scan selecting the other entry, or reading one cell off, gives
different constants. -/

/-- The two-entry table with eight distinct cells: cell `i` holds
    `0x1000 · (i / 4 + 1) + i % 4`. -/
def witTbl : Fin 8 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (0x1000 * (i.val / 4 + 1) + i.val % 4)

/-- **A pinned selection.** At index `0` the two-entry front output denotes
    `0x1000, 0x1001, 0x1002, 0x1003`, and at index `1` it denotes
    `0x2000, 0x2001, 0x2002, 0x2003`. -/
theorem combSelectFront2_witness (O : Fin 4 → BitVec 64) :
    ∃ com, combSelectFront 2 = some com
      ∧ (com.denote (selVal 2 O 0#64 witTbl) 0 = 0x1000#64
        ∧ com.denote (selVal 2 O 0#64 witTbl) 1 = 0x1001#64
        ∧ com.denote (selVal 2 O 0#64 witTbl) 2 = 0x1002#64
        ∧ com.denote (selVal 2 O 0#64 witTbl) 3 = 0x1003#64)
      ∧ (com.denote (selVal 2 O 1#64 witTbl) 0 = 0x2000#64
        ∧ com.denote (selVal 2 O 1#64 witTbl) 1 = 0x2001#64
        ∧ com.denote (selVal 2 O 1#64 witTbl) 2 = 0x2002#64
        ∧ com.denote (selVal 2 O 1#64 witTbl) 3 = 0x2003#64) := by
  obtain ⟨com0, hf0, h0⟩ :=
    combSelectFront_denote_entry 2 (by norm_num) O 0#64 witTbl (by decide)
  obtain ⟨com1, hf1, h1⟩ :=
    combSelectFront_denote_entry 2 (by norm_num) O 1#64 witTbl (by decide)
  have hcom : com0 = com1 := Option.some_inj.mp (hf0.symm.trans hf1)
  subst hcom
  exact ⟨com0, hf0,
    ⟨(h0 0).trans (by decide), (h0 1).trans (by decide), (h0 2).trans (by decide),
      (h0 3).trans (by decide)⟩,
    ⟨(h1 0).trans (by decide), (h1 1).trans (by decide), (h1 2).trans (by decide),
      (h1 3).trans (by decide)⟩⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectFrontSpec
