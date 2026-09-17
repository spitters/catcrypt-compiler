/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes

/-!
# The comb table selects, carried to their encoded bytes

`Fe25519AddSubSelectProof.selBlock_correct` states that the `n`-entry constant-time select
`selBlock n` stores the table entry at the index, over symbolic names (`"tbl"`, `"d"`,
`"z"`, `"a0"`, …). This module states the same result over the byte string that the owned
scalar encoder `encodeJBlock` produces for the block over physical register names, in the
form of `Fe25519KernelsBytes.feAddFramedBytes_correct`, for every `n ≤ 2^26` and for the
three kernels `CombSelectKernel.combSelectBlock`, `combSelect5Block`, `combSelect6Block`
(`n = 16, 32, 64`).

## Construction

* `selAllocL` is the allocation `allocGp combSelectPinned` computes for `selBlock n`,
  `n ≥ 1`, written out as a literal list; `allocGp_selBlock` proves it for every `n ≥ 1`
  from the order in which the names first occur (`blockNames_selBlock`), and
  `combSelectAlloc_eq` and its two siblings are the instances.
* `selPhys n` is `renameBlock (nameOf selAllocL) (selBlock n)`. `selPhys_eq` writes it as
  `physPre ++ (List.range n).flatMap physEntry ++ physPost` with literal `%rN` names, so
  every per-instruction side condition is a statement about the ten instructions of
  `physEntry j` with `j` a variable, closed once by `simp` and `omega` (`all_scan`). No
  side condition evaluates the 648-instruction block.
* The block writes only `%rcx`, `%r8`–`%r11` and `%rax`, so no callee-saved register and
  not `%rsp` is written, and no `LeafFrame` frame is placed around it
  (`selPhys_notWritten`).
* The encoded bytes are `encodeJBlock s2nAlloc (selPhys n)`; `decode_phys` shows that they
  decode to `selPhys n` itself.

## ABI

| kernel | symbol | entries | arguments | output bank |
|---|---|---|---|---|
| `combSelectPhys` | `ed25519_comb_select_x86_from_lean` | 16 | `tbl = %rdi`, `d = %rsi`, `z = %rdx` | `%rdx` |
| `combSelect5Phys` | `ed25519_comb5_select_x86_from_lean` | 32 | `tbl = %rdi`, `d = %rsi`, `z = %rdx` | `%rdx` |
| `combSelect6Phys` | `ed25519_comb6_select_x86_from_lean` | 64 | `tbl = %rdi`, `d = %rsi`, `z = %rdx` | `%rdx` |

The accumulators `a0`–`a3` are `%rcx`, `%r8`, `%r9`, `%r10`; the comparison scratch `mask`
is `%r11`; the candidate `c` is `%rax`.

## Trust points

* That `decodeJStream` and `JasminModel.evalInstr` agree with an x86-64 processor on these
  instructions is not proved here.
* `JasminModel` keys memory by the base register's name. The table is the bank `"%rdi"`
  and the output the bank `"%rdx"`; that they do not alias is assumed.
* The artifact lines `endbr64`, `retq` and the assembler directives are literal text and
  are not described; `ret` is outside `JInstr`.

## Main results

* `selPhys_correct`, `selBytes_correct`: for an index in `%rsi` below `n`, the four words
  stored at `%rdx` are the words of that entry of the table at `%rdi`, the table is
  unchanged, and `%rsp` and the callee-saved registers end at their entry values.
* `selBytes_constant_time`: the leakage trace of the decoded instructions is the same from
  any two states.
* `combSelectBytes_correct`, `combSelect5Bytes_correct`, `combSelect6Bytes_correct` and
  `combSelectBytes_constant_time`, `combSelect5Bytes_constant_time`,
  `combSelect6Bytes_constant_time`: the instances `n = 16, 32, 64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc s2nInstrOk)
open CatCrypt.Crypto.Optimizer.GenericRegAlloc (RenInjOn)
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameBlock renameInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes
  (pullState runBlock_renameBlock_mem decode_phys phys_constant_time
    frameRegs_of_not_written)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddSubSelectProof
  (selEntry selPre selPost selBlock selBlock_correct combSelectBlock_eq combSelect5Block_eq
    combSelect6Block_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectKernel
  (entryStride combSelectPinned combSelectAlloc combSelect5Alloc combSelect6Alloc
    combSelectBlock combSelect5Block combSelect6Block)

/-! ## 1. A property of every instruction of a scan -/

/-- A Boolean property holds on `pre ++ (List.range n).flatMap f ++ post` when it holds on
    `pre`, on `post`, and on `f j` for every `j < n`. -/
theorem all_scan (P : JInstr 64 → Bool) (pre post : List (JInstr 64))
    (f : Nat → List (JInstr 64)) (n : Nat) (hpre : pre.all P = true)
    (hpost : post.all P = true) (hf : ∀ j < n, (f j).all P = true) :
    (pre ++ (List.range n).flatMap f ++ post).all P = true := by
  simp only [List.all_append, hpre, hpost, Bool.true_and, Bool.and_true, List.all_eq_true,
    List.mem_flatMap, List.mem_range]
  rintro i ⟨j, hj, hi⟩
  exact List.all_eq_true.mp (hf j hj) i hi

/-! ## 2. The allocation -/

/-- A left fold that leaves its accumulator fixed on each element leaves it fixed. -/
theorem foldl_stable {α β : Type} (f : β → α → β) (acc : β) (xs : List α)
    (h : ∀ x ∈ xs, f acc x = acc) : xs.foldl f acc = acc := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, h x List.mem_cons_self]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- The names of `selBlock n` in order of first occurrence, for `n ≥ 1`. -/
def selNameOrder : List String := ["a0", "a1", "a2", "a3", "mask", "d", "c", "tbl", "z"]

/-- Every name of a scan entry is one of the first eight names of `selNameOrder`. -/
theorem selEntry_jinstrNames (j : Nat) :
    ∀ x ∈ (selEntry j).flatMap jinstrNames,
      x ∈ ["a0", "a1", "a2", "a3", "mask", "d", "c", "tbl"] := by
  simp [selEntry, jinstrNames, srcNames]

/-- The names of `selBlock (n + 1)` in order of first occurrence are `selNameOrder`. -/
theorem blockNames_selBlock (n : Nat) : blockNames (selBlock (n + 1)) = selNameOrder := by
  unfold blockNames
  rw [selBlock, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_append,
    List.flatMap_append, List.flatMap_append, List.foldl_append, List.foldl_append,
    List.foldl_append]
  have h0 : List.foldl (fun (acc : List String) n => if acc.contains n then acc else acc ++ [n])
      (List.foldl (fun (acc : List String) n => if acc.contains n then acc else acc ++ [n]) []
        (selPre.flatMap jinstrNames)) ((selEntry 0).flatMap jinstrNames)
      = ["a0", "a1", "a2", "a3", "mask", "d", "c", "tbl"] := by decide
  rw [h0, foldl_stable (xs := List.flatMap jinstrNames
    (List.flatMap selEntry (List.map Nat.succ (List.range n))))]
  · decide
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
    have := selEntry_jinstrNames _ x (List.mem_flatMap.mpr ⟨i, hj, hxi⟩)
    simp only [List.contains_iff_mem, this, if_true]

/-- The allocation of `selBlock n`: `tbl = %rdi`, `d = %rsi`, `z = %rdx`, the accumulators
    `a0`–`a3` in `%rcx`, `%r8`, `%r9`, `%r10`, the comparison scratch `mask` in `%r11`, the
    candidate `c` in `%rax`. -/
def selAllocL : GpAlloc :=
  [("tbl", "%rdi"), ("d", "%rsi"), ("z", "%rdx"), ("a0", "%rcx"), ("a1", "%r8"),
    ("a2", "%r9"), ("a3", "%r10"), ("mask", "%r11"), ("c", "%rax")]

/-- `selAllocL` is the allocation `allocGp combSelectPinned` computes for `selBlock n`,
    `n ≥ 1`. -/
theorem allocGp_selBlock (n : Nat) (hn : 0 < n) :
    allocGp combSelectPinned (selBlock n) = selAllocL := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, allocGp, blockNames_selBlock]
  decide

/-- `selAllocL` is the allocation `CombSelectKernel.combSelectAlloc` computes. -/
theorem combSelectAlloc_eq : combSelectAlloc = selAllocL :=
  allocGp_selBlock 16 (by decide)

/-- `selAllocL` is the allocation `CombSelectKernel.combSelect5Alloc` computes. -/
theorem combSelect5Alloc_eq : combSelect5Alloc = selAllocL :=
  allocGp_selBlock 32 (by decide)

/-- `selAllocL` is the allocation `CombSelectKernel.combSelect6Alloc` computes. -/
theorem combSelect6Alloc_eq : combSelect6Alloc = selAllocL :=
  allocGp_selBlock 64 (by decide)

theorem nameOf_tbl : nameOf selAllocL "tbl" = "%rdi" := by decide
theorem nameOf_d : nameOf selAllocL "d" = "%rsi" := by decide
theorem nameOf_z : nameOf selAllocL "z" = "%rdx" := by decide
theorem nameOf_a0 : nameOf selAllocL "a0" = "%rcx" := by decide
theorem nameOf_a1 : nameOf selAllocL "a1" = "%r8" := by decide
theorem nameOf_a2 : nameOf selAllocL "a2" = "%r9" := by decide
theorem nameOf_a3 : nameOf selAllocL "a3" = "%r10" := by decide
theorem nameOf_mask : nameOf selAllocL "mask" = "%r11" := by decide
theorem nameOf_c : nameOf selAllocL "c" = "%rax" := by decide

/-! ## 3. The physical block -/

/-- `selPre` under `selAllocL`. -/
def physPre : List (JInstr 64) :=
  [ .mov "%rcx" (.imm 0), .mov "%r8" (.imm 0), .mov "%r9" (.imm 0), .mov "%r10" (.imm 0) ]

/-- `selPost` under `selAllocL`. -/
def physPost : List (JInstr 64) :=
  [ .storeMem "%rdx" 0 (.reg "%rcx"), .storeMem "%rdx" 8 (.reg "%r8")
  , .storeMem "%rdx" 16 (.reg "%r9"), .storeMem "%rdx" 24 (.reg "%r10") ]

/-- `selEntry j` under `selAllocL`. -/
def physEntry (j : Nat) : List (JInstr 64) :=
  let base : Int := Int.ofNat j * entryStride
  [ .mov "%r11" (.reg "%rsi")
  , .sub "%r11" (.imm j)
  , .loadMem "%rax" "%rdi" (base + 0),  .cmove "%rcx" (.reg "%rax")
  , .loadMem "%rax" "%rdi" (base + 8),  .cmove "%r8" (.reg "%rax")
  , .loadMem "%rax" "%rdi" (base + 16), .cmove "%r9" (.reg "%rax")
  , .loadMem "%rax" "%rdi" (base + 24), .cmove "%r10" (.reg "%rax") ]

/-- `selBlock n` with every name replaced by its register under `selAllocL`. -/
def selPhys (n : Nat) : List (JInstr 64) := renameBlock (nameOf selAllocL) (selBlock n)

theorem map_selEntry (j : Nat) :
    (selEntry j).map (renameInstr (nameOf selAllocL)) = physEntry j := by
  simp only [selEntry, physEntry, List.map_cons, List.map_nil, renameInstr,
    Optimizer.RandomizedRegAlloc.renameOperand, nameOf_tbl, nameOf_d, nameOf_a0, nameOf_a1,
    nameOf_a2, nameOf_a3, nameOf_mask, nameOf_c]

theorem selPhys_eq (n : Nat) :
    selPhys n = physPre ++ (List.range n).flatMap physEntry ++ physPost := by
  simp only [selPhys, selBlock, renameBlock, List.map_append, List.map_flatMap, map_selEntry]
  rfl

theorem selPhys_length (n : Nat) : (selPhys n).length = 8 + 10 * n := by
  simp only [selPhys, renameBlock, List.length_map, selBlock, List.length_append,
    List.length_flatMap, selEntry, selPre, selPost, List.length_cons, List.length_nil,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

/-- Each physical scan entry for `j < 2^26` satisfies the encoder's side conditions: the
    immediate `j` fits 32 bits and each displacement `32·j + 8·k` fits 32 signed bits. -/
theorem physEntry_instrOk (j : Nat) (hj : j < 2 ^ 26) : (physEntry j).all s2nInstrOk = true := by
  simp [physEntry, s2nInstrOk, blockCovered, decodableJ, dispOk32, mulxRdxOk, bNamesXsym,
    Optimizer.JInstrRegAllocValidated.bNamesX, Optimizer.SpillingRegAlloc.writtenNames,
    Optimizer.SpillingRegAlloc.readNames, srcNames, gpNames,
    entryStride]
  omega

theorem selPhys_instrOk (n : Nat) (hn : n ≤ 2 ^ 26) : (selPhys n).all s2nInstrOk = true := by
  rw [selPhys_eq]
  exact all_scan _ _ _ _ _ (by decide) (by decide) fun j hj => physEntry_instrOk j (by omega)

/-- No instruction of `selPhys n` writes `%rsp` or a callee-saved register. -/
theorem selPhys_notWritten (n : Nat) :
    (selPhys n).all (fun i => ("%rsp" :: calleeSavedRegs).all
      (fun r => decide (r ∉ Optimizer.SpillingRegAlloc.writtenNames i))) = true := by
  rw [selPhys_eq]
  refine all_scan _ _ _ _ _ (by decide) (by decide) fun j _ => ?_
  simp only [physEntry, List.all_cons, List.all_nil, calleeSavedRegs,
    Optimizer.SpillingRegAlloc.writtenNames]
  simp

theorem selPhys_allDirect (n : Nat) : allDirect (selPhys n) = true := by
  rw [selPhys_eq]
  refine all_scan _ _ _ _ _ (by decide) (by decide) fun j _ => ?_
  simp only [physEntry, List.all_cons, List.all_nil, Bool.and_true]
  rfl

/-! ## 4. Transport of `selBlock_correct` -/

/-- The names of `selBlock n`. -/
def selNames : List String := ["tbl", "d", "z", "a0", "a1", "a2", "a3", "mask", "c"]

theorem selBlock_names (n : Nat) : ∀ x ∈ blockNamesXsym (selBlock n), x ∈ selNames := by
  have h := all_scan (fun i => (bNamesXsym i).all (· ∈ selNames)) selPre selPost selEntry n
    (by decide) (by decide) fun j _ => by
      simp [selEntry, bNamesXsym, Optimizer.JInstrRegAllocValidated.bNamesX,
        Optimizer.SpillingRegAlloc.writtenNames, Optimizer.SpillingRegAlloc.readNames,
        srcNames, selNames]
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h i hi) x hxi)

theorem selNames_renInjOn : RenInjOn selNames (nameOf selAllocL) := by decide

theorem selBlock_renInjOn (n : Nat) :
    RenInjOn (blockNamesXsym (selBlock n)) (nameOf selAllocL) :=
  fun a ha b hb => selNames_renInjOn a (selBlock_names n a ha) b (selBlock_names n b hb)

theorem z_mem_selBlock (n : Nat) : "z" ∈ blockNamesXsym (selBlock n) :=
  List.mem_flatMap.mpr ⟨.storeMem "z" 0 (.reg "a0"), by simp [selBlock, selPost], by decide⟩

theorem tbl_mem_selBlock (n : Nat) (hn : 0 < n) : "tbl" ∈ blockNamesXsym (selBlock n) :=
  List.mem_flatMap.mpr ⟨.loadMem "c" "tbl" (Int.ofNat 0 * entryStride + 0),
    List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hn, by simp [selEntry]⟩)),
    by decide⟩

/-- **The physical `n`-entry select stores the table entry at the index.** For every
    machine state whose register `%rsi` holds an index `D < n`, running `selPhys n` stores
    at `[%rdx + 8·k]` the word at `[%rdi + 32·D + 8·k]`, for `k < 4`, leaves the bank
    `%rdi` unchanged, and ends with `%rsp` and each callee-saved register at its entry
    value. -/
theorem selPhys_correct (n : Nat) (hn : n ≤ 2 ^ 26) (st : JState 64)
    (hd : (st.regs "%rsi").toNat < n) :
    (∀ k : Nat, k < 4 →
      (runBlock st (selPhys n)).mem "%rdx" (8 * (k : Int))
        = st.mem "%rdi" (32 * ((st.regs "%rsi").toNat : Int) + 8 * (k : Int))) ∧
      (runBlock st (selPhys n)).mem "%rdi" = st.mem "%rdi" ∧
      ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st (selPhys n)).regs r = st.regs r := by
  have hPd : (pullState (nameOf selAllocL) st).regs "d" = st.regs "%rsi" := by
    simp only [pullState, nameOf_d]
  have hPt : (pullState (nameOf selAllocL) st).mem "tbl" = st.mem "%rdi" := by
    simp only [pullState, nameOf_tbl]
  obtain ⟨h1, h2⟩ :=
    selBlock_correct n (by omega) (pullState (nameOf selAllocL) st) (by rw [hPd]; exact hd)
  have hz := runBlock_renameBlock_mem _ (selBlock n) (selBlock_renInjOn n) st "z"
    (z_mem_selBlock n)
  have ht := runBlock_renameBlock_mem _ (selBlock n) (selBlock_renInjOn n) st "tbl"
    (tbl_mem_selBlock n (by omega))
  rw [nameOf_z] at hz
  rw [nameOf_tbl] at ht
  refine ⟨fun k hk => ?_, ?_, fun r hr => ?_⟩
  · rw [selPhys, hz, h1 k hk, hPd, hPt]
  · rw [selPhys, ht, ← hPt]
    funext o
    exact h2 "tbl" o (by decide)
  · exact frameRegs_of_not_written st _ (selPhys_notWritten n) r hr

/-! ## 5. The byte theorems -/

theorem selPhys_decode (n : Nat) (hn : n ≤ 2 ^ 26) :
    decodeJStream (8 + 10 * n) (encodeJBlock s2nAlloc (selPhys n)) = some (selPhys n) :=
  selPhys_length n ▸ decode_phys _ (selPhys_instrOk n hn)

/-- **The encoded `n`-entry select.** For `n ≤ 2^26`, the byte string
    `encodeJBlock s2nAlloc (selPhys n)` decodes as `8 + 10·n` instructions `c` such that,
    for every machine state whose register `%rsi` holds an index `D < n`, running `c`
    stores at `[%rdx + 8·k]` the word at `[%rdi + 32·D + 8·k]`, for `k < 4`, leaves the
    bank `%rdi` unchanged, and ends with `%rsp` and each callee-saved register at its entry
    value. -/
theorem selBytes_correct (n : Nat) (hn : n ≤ 2 ^ 26) :
    ∃ c, decodeJStream (8 + 10 * n) (encodeJBlock s2nAlloc (selPhys n)) = some c ∧
      ∀ st : JState 64, (st.regs "%rsi").toNat < n →
        (∀ k : Nat, k < 4 →
          (runBlock st c).mem "%rdx" (8 * (k : Int))
            = st.mem "%rdi" (32 * ((st.regs "%rsi").toNat : Int) + 8 * (k : Int))) ∧
          (runBlock st c).mem "%rdi" = st.mem "%rdi" ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r :=
  ⟨selPhys n, selPhys_decode n hn, selPhys_correct n hn⟩

/-- **Constant time over the encoded `n`-entry select.** The instructions that
    `encodeJBlock s2nAlloc (selPhys n)` decodes to have the same leakage trace from any two
    states. -/
theorem selBytes_constant_time (n : Nat) (hn : n ≤ 2 ^ 26) (c : List (JInstr 64))
    (hdec : decodeJStream (8 + 10 * n) (encodeJBlock s2nAlloc (selPhys n)) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c :=
  phys_constant_time _ (selPhys_instrOk n hn) (selPhys_allDirect n) c
    (by rw [selPhys_length]; exact hdec) s₁ s₂

/-! ## 6. The three shipped kernels -/

/-- `CombSelectKernel.combSelectBlock` with every name replaced by its register under
    `selAllocL`. -/
def combSelectPhys : List (JInstr 64) := renameBlock (nameOf selAllocL) combSelectBlock

/-- `CombSelectKernel.combSelect5Block` with every name replaced by its register under
    `selAllocL`. -/
def combSelect5Phys : List (JInstr 64) := renameBlock (nameOf selAllocL) combSelect5Block

/-- `CombSelectKernel.combSelect6Block` with every name replaced by its register under
    `selAllocL`. -/
def combSelect6Phys : List (JInstr 64) := renameBlock (nameOf selAllocL) combSelect6Block

theorem combSelectPhys_eq : combSelectPhys = selPhys 16 := by
  rw [combSelectPhys, combSelectBlock_eq]; rfl
theorem combSelect5Phys_eq : combSelect5Phys = selPhys 32 := by
  rw [combSelect5Phys, combSelect5Block_eq]; rfl
theorem combSelect6Phys_eq : combSelect6Phys = selPhys 64 := by
  rw [combSelect6Phys, combSelect6Block_eq]; rfl

/-- **The encoded 16-entry comb select.** The byte string
    `encodeJBlock s2nAlloc combSelectPhys` decodes as 168 instructions `c` such that, for
    every machine state whose register `%rsi` holds an index `D < 16`, running `c` stores
    at `[%rdx + 8·k]` the word at `[%rdi + 32·D + 8·k]`, for `k < 4`, leaves the bank
    `%rdi` unchanged, and ends with `%rsp` and each callee-saved register at its entry
    value. -/
theorem combSelectBytes_correct :
    ∃ c, decodeJStream 168 (encodeJBlock s2nAlloc combSelectPhys) = some c ∧
      ∀ st : JState 64, (st.regs "%rsi").toNat < 16 →
        (∀ k : Nat, k < 4 →
          (runBlock st c).mem "%rdx" (8 * (k : Int))
            = st.mem "%rdi" (32 * ((st.regs "%rsi").toNat : Int) + 8 * (k : Int))) ∧
          (runBlock st c).mem "%rdi" = st.mem "%rdi" ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r := by
  rw [combSelectPhys_eq]
  exact selBytes_correct 16 (by norm_num)

/-- **The encoded 32-entry comb select**: `combSelectBytes_correct` for
    `combSelect5Phys`, 328 instructions and an index `D < 32`. -/
theorem combSelect5Bytes_correct :
    ∃ c, decodeJStream 328 (encodeJBlock s2nAlloc combSelect5Phys) = some c ∧
      ∀ st : JState 64, (st.regs "%rsi").toNat < 32 →
        (∀ k : Nat, k < 4 →
          (runBlock st c).mem "%rdx" (8 * (k : Int))
            = st.mem "%rdi" (32 * ((st.regs "%rsi").toNat : Int) + 8 * (k : Int))) ∧
          (runBlock st c).mem "%rdi" = st.mem "%rdi" ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r := by
  rw [combSelect5Phys_eq]
  exact selBytes_correct 32 (by norm_num)

/-- **The encoded 64-entry comb select**: `combSelectBytes_correct` for
    `combSelect6Phys`, 648 instructions and an index `D < 64`. -/
theorem combSelect6Bytes_correct :
    ∃ c, decodeJStream 648 (encodeJBlock s2nAlloc combSelect6Phys) = some c ∧
      ∀ st : JState 64, (st.regs "%rsi").toNat < 64 →
        (∀ k : Nat, k < 4 →
          (runBlock st c).mem "%rdx" (8 * (k : Int))
            = st.mem "%rdi" (32 * ((st.regs "%rsi").toNat : Int) + 8 * (k : Int))) ∧
          (runBlock st c).mem "%rdi" = st.mem "%rdi" ∧
          ∀ r ∈ "%rsp" :: calleeSavedRegs, (runBlock st c).regs r = st.regs r := by
  rw [combSelect6Phys_eq]
  exact selBytes_correct 64 (by norm_num)

/-- **Constant time over the encoded 16-entry comb select.** -/
theorem combSelectBytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 168 (encodeJBlock s2nAlloc combSelectPhys) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c := by
  rw [combSelectPhys_eq] at hdec
  exact selBytes_constant_time 16 (by norm_num) c hdec s₁ s₂

/-- **Constant time over the encoded 32-entry comb select.** -/
theorem combSelect5Bytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 328 (encodeJBlock s2nAlloc combSelect5Phys) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c := by
  rw [combSelect5Phys_eq] at hdec
  exact selBytes_constant_time 32 (by norm_num) c hdec s₁ s₂

/-- **Constant time over the encoded 64-entry comb select.** -/
theorem combSelect6Bytes_constant_time (c : List (JInstr 64))
    (hdec : decodeJStream 648 (encodeJBlock s2nAlloc combSelect6Phys) = some c)
    (s₁ s₂ : JState 64) : blockLeak s₁ c = blockLeak s₂ c := by
  rw [combSelect6Phys_eq] at hdec
  exact selBytes_constant_time 64 (by norm_num) c hdec s₁ s₂

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes
