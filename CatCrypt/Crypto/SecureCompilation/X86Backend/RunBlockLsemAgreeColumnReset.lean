/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMatCarry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMacChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock

/-!
# The flag-resetting schoolbook column, row, and product: `runBlock ↔ lsemStraightMem`

The per-gadget bridges cover the three legs of one flag-resetting schoolbook
column `SchoolbookRunBlock.emitColumnReset acc a b cy hi lo` — the dual-carry
MAC (`RunBlockLsemAgree.macColumn_agree`; `MulxSelect.selectMulxMac` is the same
instruction list as `macColumnJ`), the carry-materialise gadget
(`RunBlockLsemAgreeMatCarry.materialiseCarry_lsem_agree`), and the trailing
`MOV cy, hi` (`RunBlockLsemAgreeMovReg.movRegWire_agree`) — each under the
designated-slot correspondence `JLstateCorrF`, the first two migrating the
carry namespace to a fresh slot pair.

This module glues the three legs into the column bridge
(`emitColumnReset_lsem_agree`, two applications of
`runBlock_lsem_agreeF_seq_migrate`), lifts the column bridge over the column
list of one schoolbook row `SchoolbookRunBlock.emitRowBlock`
(`emitRowBlock_lsem_agree`), and lifts the row bridge over the row list of the
full schoolbook product `SchoolbookProductRunBlock.emitProductBlock`
(`emitProductBlock_lsem_agree`, with the 4-limb instance
`emitProductBlock4_lsem_agree`). Each level is a straight-line induction in the
shape of `RunBlockLsemAgreeMacChain.runBlock_lsem_agreeF_chain`: a per-item
freshness predicate over the threaded slot names, a wire-list fold, a
final-namespace fold, and a migrating sequential composition per item.

## The slot threading

One column consumes two fresh CF/OF slot pairs: `(cf1, of1)` for the MAC
(`macColumnL` reads the carry-in slots and writes the fresh pair) and
`(cf2, of2)` for the gadget (each of its two immediate-carry lowerings
allocates one fresh slot). The column therefore migrates the namespace
`(cfN, ofN) → (cf2, of2)`; the trailing `MOV` migrates nothing. A row threads
the column migrations in sequence, and the product threads the row migrations,
so the slot data of the product is a list of per-row lists of per-column pair
pairs `((cf1, of1), (cf2, of2))`.

## Main results

* `columnResetL` / `ColumnResetFresh` / `emitColumnReset_lsem_agree`: the
  wire list, freshness side condition, and bridge of one flag-resetting column.
* `rowResetL` / `rowFinal` / `RowResetFresh` / `rowReset_lsem_agree` /
  `emitRowBlock_lsem_agree`: the same for one schoolbook row.
* `prodResetL` / `prodFinal` / `ProdResetFresh` /
  `emitProductBlock_lsem_agree` / `emitProductBlock4_lsem_agree`: the same for
  the full schoolbook product.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeColumnReset

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMovReg
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMatCarry
open CatCrypt.Crypto.SecureCompilation.X86Backend.MulxSelect
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookProductRunBlock
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. One flag-resetting column -/

/-- The lsem wire list of one flag-resetting column
    `emitColumnReset acc a b cy hi lo`: the MAC column wires (carry-in
    `(cfN, ofN)`, fresh pair `(cf1, of1)`), the carry-materialise gadget wires
    (zero-materialise register `z`, fresh pair `(cf2, of2)`), then the
    register-source `MOV cy, hi` wire. -/
def columnResetL (z acc a b cy hi lo cfN ofN cf1 of1 cf2 of2 : String) : List LinstrRM :=
  macColumnL acc a b cy hi lo cfN ofN cf1 of1
    ++ matCarryWires z
        [(JInstr.adcx hi (JOperand.imm 0), cf2), (JInstr.adox hi (JOperand.imm 0), of2)]
        (cf1, of1)
    ++ [ (LinstrR.Lopn [LOperand.reg cy] (withWidthTag 64 "MOV")
           [LOperand.reg hi], MemTag.reg none) ]

/-- The name side condition of one flag-resetting column: the six column
    registers are off the flag namespace, the `MULX` low temporary does not
    alias the inputs, and the zero-materialise register `z` and the two fresh
    slot pairs `(cf1, of1)` / `(cf2, of2)` are flag names avoiding the
    registers and slots each leg reads or keeps live. -/
structure ColumnResetFresh (flg : String → Prop)
    (z acc a b cy hi lo cfN ofN cf1 of1 cf2 of2 : String) : Prop where
  /-- the column registers are real (off the flag namespace) -/
  accR : ¬ flg acc
  aR : ¬ flg a
  bR : ¬ flg b
  cyR : ¬ flg cy
  hiR : ¬ flg hi
  loR : ¬ flg lo
  /-- `mulx` aliasing -/
  lo_a : lo ≠ a
  lo_b : lo ≠ b
  hi_lo : hi ≠ lo
  /-- the zero-materialise register is a flag name off every slot it crosses -/
  zF : flg z
  z_cf1 : z ≠ cf1
  z_of1 : z ≠ of1
  z_cf2 : z ≠ cf2
  z_of2 : z ≠ of2
  /-- the MAC fresh pair -/
  cf1F : flg cf1
  cf1_acc : cf1 ≠ acc
  cf1_lo : cf1 ≠ lo
  cf1_cfN : cf1 ≠ cfN
  cf1_ofN : cf1 ≠ ofN
  of1F : flg of1
  of1_acc : of1 ≠ acc
  of1_cy : of1 ≠ cy
  of1_ofN : of1 ≠ ofN
  of1_cf1 : of1 ≠ cf1
  of1_cfN : of1 ≠ cfN
  /-- the gadget fresh pair -/
  cf2F : flg cf2
  cf2_cf1 : cf2 ≠ cf1
  cf2_of1 : cf2 ≠ of1
  of2F : flg of2
  of2_cf2 : of2 ≠ cf2
  of2_of1 : of2 ≠ of1

/-- **One flag-resetting column bridges on all axes.** Under
    `ColumnResetFresh`, the column `emitColumnReset acc a b cy hi lo` over
    `runBlock` corresponds — on the register (off flag), memory, `CF` and `OF`
    axes — to its wire list `columnResetL` run to completion under
    `lsemStraightMem`, migrating the designated carry namespace `(cfN, ofN)` to
    the gadget's fresh pair `(cf2, of2)`. Two migrating sequential compositions
    gluing `macColumn_agree`, `materialiseCarry_lsem_agree`, and
    `movRegWire_agree`. -/
theorem emitColumnReset_lsem_agree (flg : String → Prop)
    (z acc a b cy hi lo cfN ofN cf1 of1 cf2 of2 : String)
    (hfresh : ColumnResetFresh flg z acc a b cy hi lo cfN ofN cf1 of1 cf2 of2) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cfN ofN →
      ∃ ls', lsemStraightMem
          (columnResetL z acc a b cy hi lo cfN ofN cf1 of1 cf2 of2) ls = some ls' ∧
        JLstateCorrF (runBlock s (emitColumnReset acc a b cy hi lo)) ls' flg cf2 of2 := by
  intro s ls h
  have hmac := macColumn_agree flg cfN ofN acc a b cy hi lo cf1 of1
    hfresh.accR hfresh.aR hfresh.bR hfresh.cyR hfresh.hiR hfresh.loR
    hfresh.lo_a hfresh.lo_b hfresh.hi_lo
    hfresh.cf1F hfresh.cf1_acc hfresh.cf1_lo hfresh.cf1_cfN hfresh.cf1_ofN
    hfresh.of1F hfresh.of1_acc hfresh.of1_cy hfresh.of1_ofN hfresh.of1_cf1 hfresh.of1_cfN
  have hmat := materialiseCarry_lsem_agree hi z cf2 of2 flg cf1 of1
    ⟨hfresh.hiR, hfresh.zF, hfresh.cf2F, hfresh.z_cf1, hfresh.z_of1, hfresh.z_cf2,
      hfresh.cf2_cf1, hfresh.cf2_of1⟩
    ⟨hfresh.hiR, hfresh.zF, hfresh.of2F, hfresh.z_cf2, hfresh.z_of1, hfresh.z_of2,
      hfresh.of2_cf2, hfresh.of2_of1⟩
  have hmov := movRegWire_agree flg cf2 of2 cy hi hfresh.cyR hfresh.hiR
  have h12 := runBlock_lsem_agreeF_seq_migrate
    (macColumnJ acc a b cy hi lo) (materialiseCarry hi)
    (macColumnL acc a b cy hi lo cfN ofN cf1 of1)
    (matCarryWires z
      [(JInstr.adcx hi (JOperand.imm 0), cf2), (JInstr.adox hi (JOperand.imm 0), of2)]
      (cf1, of1))
    flg cfN ofN cf1 of1 cf2 of2 hmac hmat
  have hall := runBlock_lsem_agreeF_seq_migrate
    (macColumnJ acc a b cy hi lo ++ materialiseCarry hi) [.mov cy (.reg hi)]
    (macColumnL acc a b cy hi lo cfN ofN cf1 of1
      ++ matCarryWires z
          [(JInstr.adcx hi (JOperand.imm 0), cf2), (JInstr.adox hi (JOperand.imm 0), of2)]
          (cf1, of1))
    [ (LinstrR.Lopn [LOperand.reg cy] (withWidthTag 64 "MOV")
        [LOperand.reg hi], MemTag.reg none) ]
    flg cfN ofN cf2 of2 cf2 of2 h12 hmov s ls h
  have hJ : emitColumnReset acc a b cy hi lo
      = macColumnJ acc a b cy hi lo ++ materialiseCarry hi
          ++ [JInstr.mov cy (JOperand.reg hi)] := rfl
  simp only [columnResetL]
  rw [hJ]
  exact hall

/-! ## 2. One schoolbook row -/

/-- The source-side column list of one schoolbook row, over the per-column
    `(acc, a)` register pairs and the shared `(cReg, cy, hi, lo)`: one
    `emitColumnReset` per pair. `rowResetJ_zip` ties it to `emitRowBlock`. -/
def rowResetJ (cReg cy hi lo : String) : List (String × String) → List (JInstr 64)
  | [] => []
  | (acc, a) :: cols => emitColumnReset acc a cReg cy hi lo ++ rowResetJ cReg cy hi lo cols

/-- `emitRowBlock` over parallel register lists is `rowResetJ` over their zip. -/
theorem rowResetJ_zip (accs as : List String) (cReg cy hi lo : String) :
    rowResetJ cReg cy hi lo (accs.zip as) = emitRowBlock accs as cReg cy hi lo := by
  induction accs generalizing as with
  | nil => cases as <;> rfl
  | cons acc accs ih =>
    cases as with
    | nil => rfl
    | cons a as => simp only [List.zip_cons_cons, rowResetJ, emitRowBlock, ih]

/-- The lsem wire list of one schoolbook row: one `columnResetL` per column,
    threading the carry namespace through each column's slot pair pair
    `((cf1, of1), (cf2, of2))`. -/
def rowResetL (z cReg cy hi lo : String) :
    String → String → List (String × String) →
      List ((String × String) × (String × String)) → List LinstrRM
  | cf0, of0, (acc, a) :: cols, ((cf1, of1), (cf2, of2)) :: slots =>
      columnResetL z acc a cReg cy hi lo cf0 of0 cf1 of1 cf2 of2
        ++ rowResetL z cReg cy hi lo cf2 of2 cols slots
  | _, _, _, _ => []

/-- The carry namespace a row ends in: the initial pair if the slot list is
    empty, else the last column's gadget pair. -/
def rowFinal : String × String →
    List ((String × String) × (String × String)) → String × String
  | p, [] => p
  | _, (_, q) :: rest => rowFinal q rest

/-- The per-column freshness fold of one row: each column's
    `ColumnResetFresh` at the namespace it runs from. The column list and the
    slot list are one-to-one. -/
def RowResetFresh (flg : String → Prop) (z cReg cy hi lo : String) :
    String → String → List (String × String) →
      List ((String × String) × (String × String)) → Prop
  | _, _, [], [] => True
  | cf0, of0, (acc, a) :: cols, ((cf1, of1), (cf2, of2)) :: slots =>
      ColumnResetFresh flg z acc a cReg cy hi lo cf0 of0 cf1 of1 cf2 of2 ∧
      RowResetFresh flg z cReg cy hi lo cf2 of2 cols slots
  | _, _, _, _ => False

/-- **One schoolbook row bridges on all axes.** Under the per-column freshness
    fold `RowResetFresh`, the row's column list over `runBlock` corresponds to
    its wire list `rowResetL` run to completion under `lsemStraightMem`,
    migrating the carry namespace `(cf0, of0)` to `rowFinal`. Straight-line
    induction on the column list, each column via `emitColumnReset_lsem_agree`,
    composed with `runBlock_lsem_agreeF_seq_migrate`. -/
theorem rowReset_lsem_agree (flg : String → Prop) (z cReg cy hi lo : String) :
    ∀ (cols : List (String × String))
      (slots : List ((String × String) × (String × String))) (cf0 of0 : String),
      RowResetFresh flg z cReg cy hi lo cf0 of0 cols slots →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf0 of0 →
        ∃ ls', lsemStraightMem (rowResetL z cReg cy hi lo cf0 of0 cols slots) ls = some ls' ∧
          JLstateCorrF (runBlock s (rowResetJ cReg cy hi lo cols)) ls' flg
            (rowFinal (cf0, of0) slots).1 (rowFinal (cf0, of0) slots).2 := by
  intro cols
  induction cols with
  | nil =>
    intro slots cf0 of0 hfresh s ls h
    match slots, hfresh with
    | [], _ => exact ⟨ls, rfl, h⟩
  | cons pr ps ih =>
    intro slots cf0 of0 hfresh s ls h
    obtain ⟨acc, a⟩ := pr
    match slots, hfresh with
    | ((cf1, of1), (cf2, of2)) :: rest, hfresh =>
      obtain ⟨hcolF, htail⟩ := hfresh
      have hcol := emitColumnReset_lsem_agree flg z acc a cReg cy hi lo cf0 of0
        cf1 of1 cf2 of2 hcolF
      have htl := ih rest cf2 of2 htail
      have hcomp := runBlock_lsem_agreeF_seq_migrate
        (emitColumnReset acc a cReg cy hi lo) (rowResetJ cReg cy hi lo ps)
        (columnResetL z acc a cReg cy hi lo cf0 of0 cf1 of1 cf2 of2)
        (rowResetL z cReg cy hi lo cf2 of2 ps rest)
        flg cf0 of0 cf2 of2 (rowFinal (cf2, of2) rest).1 (rowFinal (cf2, of2) rest).2
        hcol htl s ls h
      simpa only [rowResetL, rowResetJ, rowFinal] using hcomp

/-- **`emitRowBlock` bridges on all axes.** The row bridge restated over the
    parallel register lists of `emitRowBlock`: the per-column pairs are the zip
    of the accumulator window and the multiplicand sources. -/
theorem emitRowBlock_lsem_agree (flg : String → Prop) (z cReg cy hi lo : String)
    (accs as : List String)
    (slots : List ((String × String) × (String × String))) (cf0 of0 : String)
    (hfresh : RowResetFresh flg z cReg cy hi lo cf0 of0 (accs.zip as) slots) :
    ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf0 of0 →
      ∃ ls', lsemStraightMem
          (rowResetL z cReg cy hi lo cf0 of0 (accs.zip as) slots) ls = some ls' ∧
        JLstateCorrF (runBlock s (emitRowBlock accs as cReg cy hi lo)) ls' flg
          (rowFinal (cf0, of0) slots).1 (rowFinal (cf0, of0) slots).2 := by
  intro s ls h
  have hrow := rowReset_lsem_agree flg z cReg cy hi lo (accs.zip as) slots cf0 of0 hfresh s ls h
  rwa [rowResetJ_zip] at hrow

/-! ## 3. The full schoolbook product -/

/-- The lsem wire list of the full schoolbook product: one `rowResetL` per
    `y`-limb, over the same accumulator window / carry register / recursion
    shift as `emitProductBlock` (window `accs.take |as|`, carry register
    `accs[|as|]`, tail shift), threading the carry namespace through the
    per-row slot lists. -/
def prodResetL (z hi lo : String) :
    String → String → List String → List String → List String →
      List (List ((String × String) × (String × String))) → List LinstrRM
  | cf0, of0, accs, as, y :: ys, rs :: rss =>
      rowResetL z y (accs.getD as.length default) hi lo cf0 of0
          ((accs.take as.length).zip as) rs
        ++ prodResetL z hi lo (rowFinal (cf0, of0) rs).1 (rowFinal (cf0, of0) rs).2
            accs.tail as ys rss
  | _, _, _, _, _, _ => []

/-- The carry namespace the product ends in: the row-final fold over the
    per-row slot lists. -/
def prodFinal : String × String →
    List (List ((String × String) × (String × String))) → String × String
  | p, [] => p
  | p, rs :: rss => prodFinal (rowFinal p rs) rss

/-- The per-row freshness fold of the product: each row's `RowResetFresh` at
    the window, carry register, and namespace it runs from. The `y`-limb list
    and the per-row slot lists are one-to-one. -/
def ProdResetFresh (flg : String → Prop) (z hi lo : String) :
    String → String → List String → List String → List String →
      List (List ((String × String) × (String × String))) → Prop
  | _, _, _, _, [], [] => True
  | cf0, of0, accs, as, y :: ys, rs :: rss =>
      RowResetFresh flg z y (accs.getD as.length default) hi lo cf0 of0
        ((accs.take as.length).zip as) rs ∧
      ProdResetFresh flg z hi lo (rowFinal (cf0, of0) rs).1 (rowFinal (cf0, of0) rs).2
        accs.tail as ys rss
  | _, _, _, _, _, _ => False

/-- **The full schoolbook product bridges on all axes.** Under the per-row
    freshness fold `ProdResetFresh`, the emitted product
    `emitProductBlock accs as ys hi lo` over `runBlock` corresponds — on the
    register (off flag), memory, `CF` and `OF` axes — to its wire list
    `prodResetL` run to completion under `lsemStraightMem`, migrating the carry
    namespace `(cf0, of0)` to `prodFinal`. Straight-line induction on the
    `y`-limb list, each row via `emitRowBlock_lsem_agree`, composed with
    `runBlock_lsem_agreeF_seq_migrate`. -/
theorem emitProductBlock_lsem_agree (flg : String → Prop) (z hi lo : String) :
    ∀ (ys : List String) (slotss : List (List ((String × String) × (String × String))))
      (accs as : List String) (cf0 of0 : String),
      ProdResetFresh flg z hi lo cf0 of0 accs as ys slotss →
      ∀ (s : JState 64) (ls : LstateM), JLstateCorrF s ls flg cf0 of0 →
        ∃ ls', lsemStraightMem (prodResetL z hi lo cf0 of0 accs as ys slotss) ls = some ls' ∧
          JLstateCorrF (runBlock s (emitProductBlock accs as ys hi lo)) ls' flg
            (prodFinal (cf0, of0) slotss).1 (prodFinal (cf0, of0) slotss).2 := by
  intro ys
  induction ys with
  | nil =>
    intro slotss accs as cf0 of0 hfresh s ls h
    match slotss, hfresh with
    | [], _ => exact ⟨ls, rfl, h⟩
  | cons y ys ih =>
    intro slotss accs as cf0 of0 hfresh s ls h
    match slotss, hfresh with
    | rs :: rss, hfresh =>
      obtain ⟨hrowF, htail⟩ := hfresh
      have hrow := emitRowBlock_lsem_agree flg z y (accs.getD as.length default) hi lo
        (accs.take as.length) as rs cf0 of0 hrowF
      have htl := ih rss accs.tail as (rowFinal (cf0, of0) rs).1 (rowFinal (cf0, of0) rs).2 htail
      have hcomp := runBlock_lsem_agreeF_seq_migrate
        (emitRowBlock (accs.take as.length) as y (accs.getD as.length default) hi lo)
        (emitProductBlock accs.tail as ys hi lo)
        (rowResetL z y (accs.getD as.length default) hi lo cf0 of0
          ((accs.take as.length).zip as) rs)
        (prodResetL z hi lo (rowFinal (cf0, of0) rs).1 (rowFinal (cf0, of0) rs).2
          accs.tail as ys rss)
        flg cf0 of0 (rowFinal (cf0, of0) rs).1 (rowFinal (cf0, of0) rs).2
        (prodFinal (rowFinal (cf0, of0) rs) rss).1 (prodFinal (rowFinal (cf0, of0) rs) rss).2
        hrow htl s ls h
      simpa only [prodResetL, emitProductBlock, prodFinal] using hcomp

/-- **The 4-limb (256×256) instance.** `emitProductBlock_lsem_agree` at the
    `emitProductBlock4` shape. -/
theorem emitProductBlock4_lsem_agree (flg : String → Prop) (z hi lo : String)
    (ys : List String) (slotss : List (List ((String × String) × (String × String))))
    (accs as : List String) (cf0 of0 : String)
    (hfresh : ProdResetFresh flg z hi lo cf0 of0 accs as ys slotss)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cf0 of0) :
    ∃ ls', lsemStraightMem (prodResetL z hi lo cf0 of0 accs as ys slotss) ls = some ls' ∧
      JLstateCorrF (runBlock s (emitProductBlock4 accs as ys hi lo)) ls' flg
        (prodFinal (cf0, of0) slotss).1 (prodFinal (cf0, of0) slotss).2 := by
  simpa only [emitProductBlock4] using
    emitProductBlock_lsem_agree flg z hi lo ys slotss accs as cf0 of0 hfresh s ls h

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeColumnReset
