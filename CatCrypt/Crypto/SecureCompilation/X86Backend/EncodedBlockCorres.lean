/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public meta import CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
public import CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
public meta import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul

/-!
# The abstract specification carried onto the encoded byte stream

`SailX86BlockRoundtrip.roundtrip_block` decodes `encodeJBlock alloc block` back to
`block.map (renameJ alloc)`, the block with every register name resolved through the
allocation. `Ascent.CorresJ` states that running a `JInstr` block under `runBlock`
refines an abstract transition `fa`. The two speak about different blocks: the
`CorresJ` fact is about the block-level names, the decoded block about the physical
`%rN` names. This module joins them by reading `renameJ alloc` as the register
renaming `renameInstr (nameOf alloc)` and transporting `CorresJ` along it with the
scoped register-allocation simulation `JInstrRegAllocScoped.runBlock_renameBlock_rel_on`.

## Main results

* `renameJ_eq_renameInstr` / `map_renameJ_eq_renameBlock` — on a `loadSym`-free
  instruction, resolving names through the allocation is the register renaming
  `nameOf alloc`; `loadSymFree_of_blockCovered` supplies the side condition from
  the covered set.
* `corresJ_renameBlock` — `CorresJ` transports along a renaming that is injective on
  the block's register names, at the pulled-back state relation `SRalloc`.
* `BytesCorresJ` — the byte stream `bs`, decoded as `n` instructions, refines the
  abstract transition `fa`.
* `encodeJBlock_bytesCorresJ` — the encoded bytes of a covered block satisfy
  `BytesCorresJ` at `SRalloc`, given a `CorresJ` for the block and injectivity of
  `nameOf alloc` on its names.
* `bignumMulColumn_bytesCorresJ`, `add2adcx_bytesCorresJ` — the capstone at two
  concrete `mulx`/`adcx`/`adox` blocks under an allocation produced by `allocGp`.
* `allocGp_not_renInjOn_poolOverflow`, `allocGp_not_renInjOn_pinnedAlias` — two
  `allocGp` allocations under which `nameOf` is not injective: a block whose distinct
  name count exceeds the free pool, and a `pinned` list sending two names to one
  register.
* `renInjOn_nameOf_of_encodableJBlock` — `ScalarEncoder.encodableJBlock`, the decidable
  gate `encodeJBlock?` applies, implies that injectivity hypothesis.
* `encodeJBlock?_bytesCorresJ` — the capstone off the checked entry point.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.Optimizer
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. The allocation read as a register renaming -/

/-- The instruction is not a `loadSym`. `loadSym` is the one arm on which `renameJ`
    and `renameInstr` differ: `renameJ` leaves the `.rodata` label alone, while
    `renameInstr` carries it through the renaming. -/
def loadSymFree : JInstr 64 → Bool
  | .loadSym _ _ => false
  | _ => true

/-- Every instruction of the covered set is `loadSymFree`. -/
theorem loadSymFree_of_blockCovered (i : JInstr 64) (hc : blockCovered i = true) :
    loadSymFree i = true := by
  unfold blockCovered decodableJ at hc
  split at hc <;> simp_all [loadSymFree]

/-- Resolving an operand through the allocation is renaming it by `nameOf alloc`. -/
theorem operandOf_eq_renameOperand (alloc : GpAlloc) (s : JOperand) :
    operandOf alloc s = renameOperand (nameOf alloc) s := by
  cases s <;> rfl

/-- On a `loadSym`-free instruction, resolving every register name through the
    allocation is the register renaming by `nameOf alloc`. -/
theorem renameJ_eq_renameInstr (alloc : GpAlloc) (i : JInstr 64)
    (hs : loadSymFree i = true) :
    renameJ alloc i = renameInstr (nameOf alloc) i := by
  cases i <;> simp_all [loadSymFree, renameJ, renameInstr, operandOf_eq_renameOperand]

/-- The decoded block of `roundtrip_block` is the block renamed by `nameOf alloc`. -/
theorem map_renameJ_eq_renameBlock (alloc : GpAlloc) (block : List (JInstr 64))
    (hs : ∀ i ∈ block, loadSymFree i = true) :
    block.map (renameJ alloc) = renameBlock (nameOf alloc) block :=
  List.map_congr_left (fun i hi => renameJ_eq_renameInstr alloc i (hs i hi))

/-! ## 2. Transporting `CorresJ` along a renaming -/

/-- The state relation pulled back along a register renaming: a machine state of the
    renamed run is related to an abstract state when it is `StateRelOn`-related to
    some state of the original run that `SR` relates to it. Registers and memory of
    the renamed run are read at `ρ n` where the original run reads at `n`; flags are
    read unchanged. -/
def SRalloc {AState : Type} (ns : List String) (ρ : String → String)
    (SR : JState 64 → AState → Prop) (st : JState 64) (a : AState) : Prop :=
  ∃ st₀, StateRelOn ns ρ st st₀ ∧ SR st₀ a

/-- **`CorresJ` transports along a register renaming.** For `ρ` injective on a name
    list covering every name the block mentions, a `CorresJ` for `block` at `SR` is a
    `CorresJ` for the renamed block at the pulled-back relation `SRalloc ns ρ SR`.
    Injectivity is what rules out two block-level names colliding on one physical
    register, which would let a write clobber a live value. -/
theorem corresJ_renameBlock {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {ns : List String} {ρ : String → String}
    (hinj : RenInjOn ns ρ) (block : List (JInstr 64))
    (hsub : ∀ n ∈ blockNamesXsym block, n ∈ ns)
    (h : CorresJ SR P fa block) :
    CorresJ (SRalloc ns ρ SR) P fa (renameBlock ρ block) := by
  intro st a hSR hP
  obtain ⟨st₀, hrel, hSR₀⟩ := hSR
  exact ⟨runBlock st₀ block,
    runBlock_renameBlock_rel_on hinj hrel block hsub, h st₀ a hSR₀ hP⟩

/-! ## 3. The byte stream as the subject -/

/-- `BytesCorresJ SR P fa n bs`: the byte stream `bs` decodes as exactly `n`
    instructions, and running the decoded block under `runBlock` refines the abstract
    transition `fa` through the state relation `SR`. The subject is the byte string. -/
def BytesCorresJ {AState : Type} (SR : JState 64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (n : Nat) (bs : List (BitVec 8)) : Prop :=
  ∃ c, decodeJStream n bs = some c ∧ CorresJ SR P fa c

/-- **The encoded bytes implement the abstract transition.** For a block in the
    covered set whose `MULX` first sources are allocated to `%rdx`, and an allocation
    whose `nameOf` is injective on the block's register names, the byte stream
    `encodeJBlock alloc block` decodes as `block.length` instructions and the decoded
    block refines the abstract transition `fa` that the block's `CorresJ` names, at
    the pulled-back state relation `SRalloc`.

    The three side conditions are the covered set (`blockCovered`), the `MULX`
    implicit-operand condition (`mulxRdxOk`), and injectivity of the allocation on the
    block's names (`RenInjOn`); all three are decidable on a concrete block. -/
theorem encodeJBlock_bytesCorresJ {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState}
    (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true)
    (hr : ∀ i ∈ block, mulxRdxOk alloc i = true)
    (hinj : RenInjOn (blockNamesXsym block) (nameOf alloc))
    (h : CorresJ SR P fa block) :
    BytesCorresJ (SRalloc (blockNamesXsym block) (nameOf alloc) SR) P fa
      block.length (encodeJBlock alloc block) := by
  refine ⟨block.map (renameJ alloc), roundtrip_block alloc block hc hr, ?_⟩
  rw [map_renameJ_eq_renameBlock alloc block
    (fun i hi => loadSymFree_of_blockCovered i (hc i hi))]
  exact corresJ_renameBlock hinj block (fun _ hn => hn) h

/-! ## 4. The capstone at concrete `mulx`/`adcx`/`adox` blocks

`EcMultiLimbMul.corresJ_adxBlock` refines an arbitrary interleaving of widening
multiplies and the two carry-chain adds — the `bignum_mul_4_8` repertoire — against
the abstract fold `adxAbs` over the dual-carry relation `SRcarry2`. Every instruction
of `adxBlock` lies in the covered set, so the capstone applies once the allocation
pins each `MULX` first source to `%rdx`. -/

/-- One column of an operand-scanning multiply: two widening products of the
    multiplier `x` against the multiplicand limbs `y0`, `y1`, accumulated through the
    `CF` chain (`adcx`) and the `OF` chain (`adox`). -/
def bignumMulColumnOps : List AdxOp :=
  [ .mulx "h0" "l0" "x" "y0",
    .mulx "h1" "l1" "x" "y1",
    .adcx "acc1" "l1",
    .adox "acc2" "h0" ]

/-- The emitted block of `bignumMulColumnOps`. -/
def bignumMulColumn : List (JInstr 64) := adxBlock bignumMulColumnOps

/-- The allocation of `bignumMulColumn`, with the `MULX` multiplier `x` pinned to
    `%rdx` (the register `MULX` reads implicitly and does not encode). -/
def bignumMulColumnAlloc : GpAlloc := allocGp [("x", "%rdx")] bignumMulColumn

/-- The allocation maps every name of `bignumMulColumn` to a pool register. -/
theorem bignumMulColumn_no_overflow :
    allocOverflow [("x", "%rdx")] bignumMulColumn = none := by decide

/-- Every instruction of `bignumMulColumn` lies in the covered set. -/
theorem bignumMulColumn_covered :
    ∀ i ∈ bignumMulColumn, blockCovered i = true := by decide

/-- Every `MULX` of `bignumMulColumn` reads its implicit first source from `%rdx`. -/
theorem bignumMulColumn_mulxRdxOk :
    ∀ i ∈ bignumMulColumn, mulxRdxOk bignumMulColumnAlloc i = true := by decide

/-- The allocation assigns the names of `bignumMulColumn` distinct physical
    registers. -/
theorem bignumMulColumn_renInjOn :
    RenInjOn (blockNamesXsym bignumMulColumn) (nameOf bignumMulColumnAlloc) := by decide

/-- **The capstone at a concrete multiply column.** The bytes
    `encodeJBlock bignumMulColumnAlloc bignumMulColumn` decode as four instructions
    whose `runBlock` refines the abstract dual-carry fold
    `adxAbs bignumMulColumnOps` — the widening products and both carry chains — at
    the allocation-pulled-back `SRcarry2`. -/
theorem bignumMulColumn_bytesCorresJ :
    BytesCorresJ
      (SRalloc (blockNamesXsym bignumMulColumn) (nameOf bignumMulColumnAlloc) SRcarry2)
      (fun _ => True) (adxAbs bignumMulColumnOps) bignumMulColumn.length
      (encodeJBlock bignumMulColumnAlloc bignumMulColumn) :=
  encodeJBlock_bytesCorresJ bignumMulColumnAlloc bignumMulColumn
    bignumMulColumn_covered bignumMulColumn_mulxRdxOk bignumMulColumn_renInjOn
    (corresJ_adxBlock bignumMulColumnOps)

/-- A two-limb add-with-carry chain over the `CF` chain. -/
def add2adcx : List (JInstr 64) := adcxBlock [("a0", "b0"), ("a1", "b1")]

/-- The allocation of `add2adcx`. -/
def add2adcxAlloc : GpAlloc := allocGp [] add2adcx

/-- Every instruction of `add2adcx` lies in the covered set. -/
theorem add2adcx_covered : ∀ i ∈ add2adcx, blockCovered i = true := by decide

/-- `add2adcx` contains no `MULX`, so the implicit-operand condition is vacuous. -/
theorem add2adcx_mulxRdxOk : ∀ i ∈ add2adcx, mulxRdxOk add2adcxAlloc i = true := by decide

/-- The allocation assigns the names of `add2adcx` distinct physical registers. -/
theorem add2adcx_renInjOn :
    RenInjOn (blockNamesXsym add2adcx) (nameOf add2adcxAlloc) := by decide

/-- **The capstone at the two-limb carry chain.** The bytes
    `encodeJBlock add2adcxAlloc add2adcx` decode as two instructions whose `runBlock`
    refines the abstract add-with-carry fold `adcxAbs [("a0","b0"), ("a1","b1")]` at
    the allocation-pulled-back `SRcarry`. -/
theorem add2adcx_bytesCorresJ :
    BytesCorresJ (SRalloc (blockNamesXsym add2adcx) (nameOf add2adcxAlloc) SRcarry)
      (fun _ => True) (adcxAbs [("a0", "b0"), ("a1", "b1")]) add2adcx.length
      (encodeJBlock add2adcxAlloc add2adcx) :=
  encodeJBlock_bytesCorresJ add2adcxAlloc add2adcx add2adcx_covered
    add2adcx_mulxRdxOk add2adcx_renInjOn (corresJ_adcxChain [("a0", "b0"), ("a1", "b1")])

/-! ## 5. The scope of the injectivity hypothesis

`regOf` maps a name the allocation leaves unmapped to the sentinel
`<UNALLOCATED:n>`, which the assembler rejects. The byte encoder does not read
`regOf` directly: it reads `gpNum (regOf alloc n)`, and `gpNum` sends every
non-canonical string to `0`. So on the byte path each unmapped name resolves to
`%rax`, and `nameOf alloc` is not injective as soon as the free pool is exhausted.
`ScalarEncoder.gpNum?` is the same resolution with that failure exposed, and
`encodeJBlock?` refuses such an allocation; §6 connects the two. -/

/-- A block with fifteen distinct register names — one more than `gpPool` has
    entries. -/
def poolOverflowBlock : List (JInstr 64) :=
  [ .neg "v0", .neg "v1", .neg "v2", .neg "v3", .neg "v4", .neg "v5", .neg "v6",
    .neg "v7", .neg "v8", .neg "v9", .neg "v10", .neg "v11", .neg "v12", .neg "v13",
    .neg "v14" ]

/-- `allocGp` leaves one name of `poolOverflowBlock` unmapped. -/
theorem poolOverflowBlock_overflows :
    allocOverflow ([] : GpAlloc) poolOverflowBlock = some ["v14"] := by decide

/-- The unmapped name and the name allocated `%rax` resolve to the same physical
    register on the byte path. -/
theorem poolOverflowBlock_nameOf_collision :
    nameOf (allocGp [] poolOverflowBlock) "v8"
      = nameOf (allocGp [] poolOverflowBlock) "v14" := by decide

/-- **`allocGp` can violate the capstone's injectivity hypothesis.** On a block whose
    distinct name count exceeds the free pool, `nameOf` of the resulting allocation is
    not injective on the block's register names, so `encodeJBlock_bytesCorresJ` does
    not apply. The hypothesis is decidable and must be checked per block. -/
theorem allocGp_not_renInjOn_poolOverflow :
    ¬ RenInjOn (blockNamesXsym poolOverflowBlock) (nameOf (allocGp [] poolOverflowBlock)) := by
  intro h
  have hv : ("v8" : String) = "v14" :=
    h "v8" (by decide) "v14" (by decide) poolOverflowBlock_nameOf_collision
  exact absurd hv (by decide)

/-! ## 6. The gate that discharges the injectivity hypothesis

`ScalarEncoder.encodableJBlock` decides, on an allocation and a block, that every
register name the block mentions resolves to a canonical `%rN` and that distinct
names resolve to distinct registers. It implies the `RenInjOn` hypothesis
`encodeJBlock_bytesCorresJ` carries, so the checked entry point `encodeJBlock?`
delivers the capstone off one decidable check on the allocation rather than a
separate per-block injectivity check. -/

/-- On a name the allocation resolves, `nameOf` is the physical register the
    allocation assigns it: `regName ∘ gpNum` is the identity on the canonical
    `%rN` names. -/
theorem nameOf_eq_regOf (alloc : GpAlloc) (n : String)
    (h : regResolvable alloc n = true) : nameOf alloc n = regOf alloc n := by
  have h' : (gpNum? (regOf alloc n)).isSome = true := h
  have hm : regOf alloc n ∈ gpNames := mem_gpNames_of_gpNum?_isSome _ h'
  exact regName_gpNum _ (by simpa [gpNames] using hm)

/-- The first-seen dedup fold that builds `blockNames` keeps every name it is
    given. -/
theorem mem_blockNamesFold : ∀ (l acc : List String) (n : String),
    (n ∈ acc ∨ n ∈ l) →
    n ∈ l.foldl (fun acc m => if acc.contains m then acc else acc ++ [m]) acc
  | [], acc, _, h => by simpa using h
  | m :: l, acc, n, h => by
      refine mem_blockNamesFold l _ n ?_
      show n ∈ (if acc.contains m then acc else acc ++ [m]) ∨ n ∈ l
      by_cases hc : (acc.contains m) = true
      · rw [ite_eq_left hc]
        have hm : m ∈ acc := by simpa using hc
        rcases h with h | h
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hm
          · exact Or.inr h
      · rw [ite_eq_right hc]
        rcases h with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (List.mem_append_right _ (by simp))
          · exact Or.inr h

/-- Every name an instruction of the block mentions survives into `blockNames`. -/
theorem mem_blockNames {block : List (JInstr 64)} {n : String}
    (h : n ∈ block.flatMap jinstrNames) : n ∈ blockNames block :=
  mem_blockNamesFold _ [] n (Or.inr h)

/-- On a `loadSym`-free instruction the scoped name list `bNamesXsym` is contained
    in the allocator's name list `jinstrNames`. The two differ only at `loadSym`,
    whose `.rodata` label the scoped relation carries and the allocator does
    not. -/
theorem mem_jinstrNames_of_mem_bNamesXsym (i : JInstr 64) (hs : loadSymFree i = true)
    {n : String} (hn : n ∈ bNamesXsym i) : n ∈ jinstrNames i := by
  cases i <;>
    simp_all [loadSymFree, bNamesXsym, bNamesX, jinstrNames,
      SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames]
  -- `xchg a b` lists both operands as written and as read.
  all_goals tauto

/-- Every scoped name of a `loadSym`-free block is a name the allocator sees. -/
theorem mem_blockNames_of_mem_blockNamesXsym {block : List (JInstr 64)}
    (hs : ∀ i ∈ block, loadSymFree i = true) {n : String}
    (hn : n ∈ blockNamesXsym block) : n ∈ blockNames block := by
  simp only [blockNamesXsym, List.mem_flatMap] at hn
  obtain ⟨i, hi, hni⟩ := hn
  exact mem_blockNames (List.mem_flatMap.mpr
    ⟨i, hi, mem_jinstrNames_of_mem_bNamesXsym i (hs i hi) hni⟩)

/-- A function whose image of a list is duplicate-free is injective on that list. -/
theorem eq_of_mem_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha; simp at ha
  | cons x l ih =>
      intro hn a b ha hb hf
      rw [List.map_cons, List.nodup_cons] at hn
      have hx : ∀ c ∈ l, f x ≠ f c := by
        intro c hc hxc
        exact hn.1 (by rw [hxc]; exact List.mem_map_of_mem hc)
      rcases List.mem_cons.mp ha with rfl | hal
      · rcases List.mem_cons.mp hb with rfl | hbl
        · rfl
        · exact absurd hf (hx b hbl)
      · rcases List.mem_cons.mp hb with rfl | hbl
        · exact absurd hf.symm (hx a hal)
        · exact ih hn.2 hal hbl hf

/-- **The encodable gate discharges the capstone's injectivity hypothesis.** On a
    `loadSym`-free block, an allocation the gate accepts resolves the block's
    scoped names injectively — the condition that rules out two block-level names
    landing on one physical register. -/
theorem renInjOn_nameOf_of_encodableJBlock (alloc : GpAlloc) (block : List (JInstr 64))
    (hs : ∀ i ∈ block, loadSymFree i = true)
    (h : encodableJBlock alloc block = true) :
    RenInjOn (blockNamesXsym block) (nameOf alloc) := by
  intro a ha b hb hab
  have ha' : a ∈ blockNames block := mem_blockNames_of_mem_blockNamesXsym hs ha
  have hb' : b ∈ blockNames block := mem_blockNames_of_mem_blockNamesXsym hs hb
  have hra : nameOf alloc a = regOf alloc a :=
    nameOf_eq_regOf alloc a (regResolvable_of_encodable h ha')
  have hrb : nameOf alloc b = regOf alloc b :=
    nameOf_eq_regOf alloc b (regResolvable_of_encodable h hb')
  refine eq_of_mem_of_nodup_map (regOf alloc) (regOf_nodup_of_encodable h) ha' hb' ?_
  rw [← hra, ← hrb]; exact hab

/-- **The capstone off the checked entry point.** For a block in the covered set
    whose `MULX` first sources are allocated to `%rdx`, and an allocation the
    encodable gate accepts, `encodeJBlock?` returns a byte stream that decodes as
    `block.length` instructions refining the abstract transition `fa`. The
    injectivity hypothesis of `encodeJBlock_bytesCorresJ` is discharged from the
    gate rather than assumed. -/
theorem encodeJBlock?_bytesCorresJ {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState}
    (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true)
    (hr : ∀ i ∈ block, mulxRdxOk alloc i = true)
    (henc : encodableJBlock alloc block = true)
    (h : CorresJ SR P fa block) :
    ∃ bs, encodeJBlock? alloc block = some bs ∧
      BytesCorresJ (SRalloc (blockNamesXsym block) (nameOf alloc) SR) P fa
        block.length bs :=
  ⟨encodeJBlock alloc block, encodeJBlock?_eq_some alloc block henc,
    encodeJBlock_bytesCorresJ alloc block hc hr
      (renInjOn_nameOf_of_encodableJBlock alloc block
        (fun i hi => loadSymFree_of_blockCovered i (hc i hi)) henc) h⟩

/-! ## 7. The allocations the gate rejects

Three ways an allocation reaches the byte encoder without naming a register.
`allocOverflow` sees only the first. -/

-- The gate rejects the pool-overflow allocation: `allocGp` leaves `"v14"`
-- unmapped, `regOf` returns the `<UNALLOCATED:v14>` sentinel, and `gpNum?` does
-- not resolve it.
#guard encodableJBlock (allocGp ([] : GpAlloc) poolOverflowBlock) poolOverflowBlock
  == false

/-- Two names pinned to one physical register. -/
def pinnedAliasPins : GpAlloc := [("a", "%rdx"), ("b", "%rdx")]

/-- A block over the two aliased names. -/
def pinnedAliasBlock : List (JInstr 64) := [JInstr.mov "a" (.reg "b")]

/-- `allocOverflow` accepts the aliasing pin: both names are mapped. -/
theorem pinnedAliasBlock_no_overflow :
    allocOverflow pinnedAliasPins pinnedAliasBlock = none := by decide

/-- The two pinned names resolve to one physical register. -/
theorem pinnedAliasBlock_nameOf_collision :
    nameOf (allocGp pinnedAliasPins pinnedAliasBlock) "a"
      = nameOf (allocGp pinnedAliasPins pinnedAliasBlock) "b" := by decide

/-- `allocGp` can violate the capstone's injectivity hypothesis through `pinned`
    alone, on a block that fits the pool. -/
theorem allocGp_not_renInjOn_pinnedAlias :
    ¬ RenInjOn (blockNamesXsym pinnedAliasBlock)
        (nameOf (allocGp pinnedAliasPins pinnedAliasBlock)) := by
  intro h
  have hv : ("a" : String) = "b" :=
    h "a" (by decide) "b" (by decide) pinnedAliasBlock_nameOf_collision
  exact absurd hv (by decide)

-- The gate rejects the aliasing pin.
#guard encodableJBlock (allocGp pinnedAliasPins pinnedAliasBlock) pinnedAliasBlock
  == false

/-- A pinned register spelled outside the canonical sixteen. -/
def pinnedMisspelledPins : GpAlloc := [("a", "rdx")]

/-- A block over the mis-spelled pinned name. -/
def pinnedMisspelledBlock : List (JInstr 64) := [JInstr.neg "a"]

/-- `allocOverflow` accepts the mis-spelled pin: the name is mapped. -/
theorem pinnedMisspelledBlock_no_overflow :
    allocOverflow pinnedMisspelledPins pinnedMisspelledBlock = none := by decide

/-- The mis-spelled pin resolves to `%rax` on the byte path. -/
theorem pinnedMisspelledBlock_nameOf_rax :
    nameOf (allocGp pinnedMisspelledPins pinnedMisspelledBlock) "a" = "%rax" := by
  decide

-- The gate rejects the mis-spelled pin.
#guard encodableJBlock (allocGp pinnedMisspelledPins pinnedMisspelledBlock)
  pinnedMisspelledBlock == false

-- The gate accepts the two capstone blocks: it rejects the aliasing allocations
-- without rejecting the allocations the capstone already applies to.
#guard encodableJBlock bignumMulColumnAlloc bignumMulColumn

#guard encodableJBlock add2adcxAlloc add2adcx

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
