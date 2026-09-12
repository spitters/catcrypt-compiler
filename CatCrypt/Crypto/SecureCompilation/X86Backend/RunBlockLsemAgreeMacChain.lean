/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree

/-!
# The N-column ADX MAC chain: `runBlock ↔ lsemStraightMem` block agreement

`RunBlockLsemAgree.mac_column_lsem_agree` (repackaged as `macColumn_agree`)
bridges one dual-carry `mulx`/`adcx`/`adox` MAC column over `runBlock` to its
lsem image `macColumnL`, migrating the designated carry namespace `(cfN, ofN)` to
a fresh pair `(cfNew, ofNew)`. `mac2_columns_lsem_agree` composes exactly two such
columns through `runBlock_lsem_agreeF_seq_migrate`.

This module lifts the per-column bridge over a **whole list** of columns sharing
the accumulator, carry-word, and scratch registers `(acc, cy, hi, lo)` with a
per-column input pair `(a_i, b_i)` and a fresh CF/OF slot pair `(cf_i, of_i)`:
`runBlock_lsem_agreeF_chain` is the arbitrary-length generalisation of
`mac2_columns_lsem_agree`, the `JLstateCorrF` (dual-carry) analogue of the
`sbb`-chain lift `Ascent.runBlock_lsem_agreeCF`. Straight-line induction on the
column list, each column via `macColumn_agree`, composed with
`runBlock_lsem_agreeF_seq_migrate`.

## Main results

* `runBlock_lsem_agreeF_chain`: an arbitrary-length ADX MAC column chain agrees
  between `runBlock` and `lsemStraightMem` on the register/memory/CF/OF axes,
  migrating the carry namespace `(cf0, of0)` to `finalPair`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMacChain

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-- The source-side ADX MAC chain: one `macColumnJ acc a b cy hi lo` per input
    pair `(a, b)`, over the shared accumulator/carry/scratch registers. -/
def macChainJ (acc cy hi lo : String) : List (String × String) → List (JInstr 64)
  | [] => []
  | (a, b) :: rest => macColumnJ acc a b cy hi lo ++ macChainJ acc cy hi lo rest

/-- The lsem lowering of the ADX MAC chain, threading the fresh CF/OF slot pairs
    `slots` (one pair per column) from the initial pair `(cf0, of0)`. -/
def macChainL (acc cy hi lo : String) :
    String → String → List (String × String) → List (String × String) → List LinstrRM
  | cf0, of0, (a, b) :: cols, (cf, of) :: slots =>
      macColumnL acc a b cy hi lo cf0 of0 cf of ++ macChainL acc cy hi lo cf of cols slots
  | _, _, _, _ => []

/-- The final CF/OF slot pair a chain reaches: the initial pair if empty, else the
    last consumed fresh pair. -/
def finalPair : String × String → List (String × String) → String × String
  | p, [] => p
  | _, q :: rest => finalPair q rest

/-- Per-column freshness / non-aliasing side-conditions of the ADX MAC chain: at
    each column `(a, b)` with fresh CF/OF pair `(cf, of)` and current carry-in
    slots `(cf0, of0)`, the inputs are off the flag namespace and not aliased by the
    `MULX` low temporary `lo`, and the fresh slots are flag names distinct from the
    accumulator/scratch and from the current namespace — exactly the hypotheses
    `macColumn_agree` consumes. `cols` and `slots` are one-to-one. -/
def MacChainFresh (flg : String → Prop) (acc cy hi lo : String) :
    String → String → List (String × String) → List (String × String) → Prop
  | _, _, [], [] => True
  | cf0, of0, (a, b) :: cols, (cf, of) :: slots =>
      ¬ flg a ∧ ¬ flg b ∧ lo ≠ a ∧ lo ≠ b ∧
      flg cf ∧ cf ≠ acc ∧ cf ≠ lo ∧ cf ≠ cf0 ∧ cf ≠ of0 ∧
      flg of ∧ of ≠ acc ∧ of ≠ cy ∧ of ≠ of0 ∧ of ≠ cf ∧ of ≠ cf0 ∧
      MacChainFresh flg acc cy hi lo cf of cols slots
  | _, _, _, _ => False

/-- **The N-column ADX MAC-chain lift.** Under the shared-register off-flag
    conditions and the per-column freshness `MacChainFresh`, the whole source MAC
    chain `macChainJ acc cy hi lo cols` over `runBlock` corresponds — on the
    register (off flag), memory, `CF` and `OF` axes — to its lsem lowering
    `macChainL` run to completion under `lsemStraightMem` (TOTALITY), migrating the
    designated carry namespace `(cf0, of0)` to `finalPair (cf0, of0) slots`. The
    arbitrary-length generalisation of `mac2_columns_lsem_agree`; straight-line
    induction, each column via `macColumn_agree`, composed with
    `runBlock_lsem_agreeF_seq_migrate`. -/
theorem runBlock_lsem_agreeF_chain (flg : String → Prop) (acc cy hi lo : String)
    (hAcc : ¬ flg acc) (hCy : ¬ flg cy) (hHi : ¬ flg hi) (hLo : ¬ flg lo) (hHiLo : hi ≠ lo) :
    ∀ (cols slots : List (String × String)) (cf0 of0 : String),
      MacChainFresh flg acc cy hi lo cf0 of0 cols slots →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf0 of0 →
        ∃ ls', lsemStraightMem (macChainL acc cy hi lo cf0 of0 cols slots) ls = some ls' ∧
          JLstateCorrF (runBlock s (macChainJ acc cy hi lo cols)) ls' flg
            (finalPair (cf0, of0) slots).1 (finalPair (cf0, of0) slots).2 := by
  intro cols
  induction cols with
  | nil =>
    intro slots cf0 of0 hfresh s ls h
    match slots, hfresh with
    | [], _ => exact ⟨ls, rfl, h⟩
  | cons pr ps ih =>
    intro slots cf0 of0 hfresh s ls h
    obtain ⟨a, b⟩ := pr
    match slots, hfresh with
    | (cf, of) :: rest, hfresh =>
      obtain ⟨hA, hB, hLoA, hLoB, hcf, hcf_acc, hcf_lo, hcf_cf, hcf_of,
        hof, hof_acc, hof_cy, hof_of, hof_cf, hof_cfN, htail⟩ := hfresh
      have hcol := macColumn_agree flg cf0 of0 acc a b cy hi lo cf of
        hAcc hA hB hCy hHi hLo hLoA hLoB hHiLo
        hcf hcf_acc hcf_lo hcf_cf hcf_of hof hof_acc hof_cy hof_of hof_cf hof_cfN
      have htl := ih rest cf of htail
      have hcomp := runBlock_lsem_agreeF_seq_migrate
        (macColumnJ acc a b cy hi lo) (macChainJ acc cy hi lo ps)
        (macColumnL acc a b cy hi lo cf0 of0 cf of) (macChainL acc cy hi lo cf of ps rest)
        flg cf0 of0 cf of (finalPair (cf, of) rest).1 (finalPair (cf, of) rest).2
        hcol htl s ls h
      simpa only [macChainL, macChainJ, finalPair] using hcomp

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMacChain
