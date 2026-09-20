/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384Proof
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

/-!
# The imported `bignum_montmul_p384` block, carried to its encoded bytes

`S2nMontmulP384Proof.s2nMontmulP384_corresJ` proves that the imported s2n-bignum block
`s2nMontmulP384Block` refines the abstract Montgomery multiplication `montAbs` under
`runBlock`. This module carries that result to the byte string
`encodeJBlock s2nAlloc s2nMontmulP384Block` produced by the owned scalar encoder, through
`EncodedBlockCorres.encodeJBlock_bytesCorresJ`.

The allocation `s2nAlloc` sends each of the sixteen canonical `%rN` names to itself, so the
encoded program uses the registers of the s2n-bignum source. The three side conditions of
`encodeJBlock_bytesCorresJ` (the covered set, `MULX` reading `%rdx`, injectivity of the
allocation on the block's names) are checked per instruction by `s2nInstrOk`, evaluated on
each of the seventeen segments separately and combined over the segment concatenation with
`List.all_append`.

## What the byte theorem gives

* The bytes decode, by `SailX86Decoder.decodeJStream`, to exactly 264 instructions, and those
  instructions are `s2nMontmulP384Block` itself (`s2nMontmulP384_decode`).
* Running the decoded instructions under `JasminModel`'s `runBlock` stores at `%rdi` the
  Montgomery product of the words at `%rsi` and `%rcx` (`s2nMontmulP384Bytes_correct`).

## What it does not give

* That `decodeJStream` and `JasminModel.evalInstr` agree with an x86-64 processor on these
  instructions is not proved here. That agreement is the trust edge of the result; the
  known-answer gate of `bench/p384_ecdsa_rust` (`fieldbench`, arm `s2n-encoded`) runs these
  bytes against s2n-bignum's object on 100 361 input pairs.
* The frame (`endbr64`, the six `pushq`, the six `popq`, `retq`) is outside the block and is
  not described.
* Memory in `JasminModel` is keyed by the base register's name. The assumptions stated in
  `S2nMontmulP384Proof` carry over unchanged: the output buffer does not alias an input
  buffer, and the bank named `"%rcx"` holds the buffer the caller passes in `%rdx`.

## Main results

* `s2nAlloc`: the identity allocation on the canonical register names.
* `s2nMontmulP384Block_instrOk`: every instruction of the block satisfies `s2nInstrOk`.
* `s2nMontmulP384_bytesCorresJ`: the encoded bytes satisfy `BytesCorresJ` against `montAbs`.
* `s2nMontmulP384_decode`: the encoded bytes decode to `s2nMontmulP384Block`.
* `s2nMontmulP384Bytes_correct`: the instructions the bytes decode to compute the
  Montgomery product modulo `p384`.
-/

@[expose] public section

set_option autoImplicit false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres
open CatCrypt.Crypto.Optimizer
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc
open CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated
open CatCrypt.Crypto.Optimizer.JInstrRegAllocScoped

/-! ## The allocation -/

/-- The allocation sending each of the sixteen canonical `%rN` names to itself. -/
def s2nAlloc : GpAlloc := gpNames.map fun r => (r, r)

/-- On a canonical `%rN` name, `nameOf s2nAlloc` is the identity. -/
theorem nameOf_s2nAlloc (n : String) (h : n ∈ gpNames) : nameOf s2nAlloc n = n := by
  simp only [gpNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

/-- A renaming fixing every register name of an operand leaves the operand unchanged. -/
theorem renameOperand_eq_self_of_fix (ρ : String → String) (o : JOperand)
    (h : ∀ n ∈ srcNames o, ρ n = n) : renameOperand ρ o = o := by
  cases o <;> simp_all [renameOperand, srcNames]

/-- A renaming fixing every name `bNamesXsym i` lists leaves the instruction unchanged. -/
theorem renameInstr_eq_self_of_fix (ρ : String → String) (i : JInstr 64)
    (h : ∀ n ∈ bNamesXsym i, ρ n = n) : renameInstr ρ i = i := by
  cases i <;> simp_all [renameInstr, bNamesXsym, bNamesX,
    SpillingRegAlloc.writtenNames, SpillingRegAlloc.readNames, renameOperand_eq_self_of_fix]

/-! ## The side conditions, per segment -/

/-- The side conditions of `encodeJBlock_bytesCorresJ` for one instruction under
    `s2nAlloc`: the instruction is in the covered set, a `MULX` reads its first source
    from `%rdx`, and every name the instruction mentions is a canonical `%rN` name. -/
def s2nInstrOk (i : JInstr 64) : Bool :=
  blockCovered i && mulxRdxOk s2nAlloc i && (bNamesXsym i).all (· ∈ gpNames)

theorem seg01_instrOk : s2nMontmulP384Seg01.all s2nInstrOk = true := by decide
theorem seg02_instrOk : s2nMontmulP384Seg02.all s2nInstrOk = true := by decide
theorem seg03_instrOk : s2nMontmulP384Seg03.all s2nInstrOk = true := by decide
theorem seg04_instrOk : s2nMontmulP384Seg04.all s2nInstrOk = true := by decide
theorem seg05_instrOk : s2nMontmulP384Seg05.all s2nInstrOk = true := by decide
theorem seg06_instrOk : s2nMontmulP384Seg06.all s2nInstrOk = true := by decide
theorem seg07_instrOk : s2nMontmulP384Seg07.all s2nInstrOk = true := by decide
theorem seg08_instrOk : s2nMontmulP384Seg08.all s2nInstrOk = true := by decide
theorem seg09_instrOk : s2nMontmulP384Seg09.all s2nInstrOk = true := by decide
theorem seg10_instrOk : s2nMontmulP384Seg10.all s2nInstrOk = true := by decide
theorem seg11_instrOk : s2nMontmulP384Seg11.all s2nInstrOk = true := by decide
theorem seg12_instrOk : s2nMontmulP384Seg12.all s2nInstrOk = true := by decide
theorem seg13_instrOk : s2nMontmulP384Seg13.all s2nInstrOk = true := by decide
theorem seg14_instrOk : s2nMontmulP384Seg14.all s2nInstrOk = true := by decide
theorem seg15_instrOk : s2nMontmulP384Seg15.all s2nInstrOk = true := by decide
theorem seg16_instrOk : s2nMontmulP384Seg16.all s2nInstrOk = true := by decide
theorem seg17_instrOk : s2nMontmulP384Seg17.all s2nInstrOk = true := by decide

/-- Every instruction of `s2nMontmulP384Block` satisfies `s2nInstrOk`: the segment checks
    combined over the concatenation. -/
theorem s2nMontmulP384Block_instrOk : ∀ i ∈ s2nMontmulP384Block, s2nInstrOk i = true := by
  have h : s2nMontmulP384Block.all s2nInstrOk = true := by
    simp only [s2nMontmulP384Block, List.all_append, seg01_instrOk, seg02_instrOk,
      seg03_instrOk, seg04_instrOk, seg05_instrOk, seg06_instrOk, seg07_instrOk,
      seg08_instrOk, seg09_instrOk, seg10_instrOk, seg11_instrOk, seg12_instrOk,
      seg13_instrOk, seg14_instrOk, seg15_instrOk, seg16_instrOk, seg17_instrOk,
      Bool.and_self]
  exact List.all_eq_true.mp h

theorem s2nMontmulP384Block_covered : ∀ i ∈ s2nMontmulP384Block, blockCovered i = true :=
  fun i hi => by
    have := s2nMontmulP384Block_instrOk i hi
    simp only [s2nInstrOk, Bool.and_eq_true] at this
    exact this.1.1

theorem s2nMontmulP384Block_mulxRdxOk :
    ∀ i ∈ s2nMontmulP384Block, mulxRdxOk s2nAlloc i = true :=
  fun i hi => by
    have := s2nMontmulP384Block_instrOk i hi
    simp only [s2nInstrOk, Bool.and_eq_true] at this
    exact this.1.2

/-- Every name the block mentions is a canonical `%rN` name. -/
theorem s2nMontmulP384Block_names :
    ∀ n ∈ blockNamesXsym s2nMontmulP384Block, n ∈ gpNames := by
  intro n hn
  obtain ⟨i, hi, hni⟩ := List.mem_flatMap.mp hn
  have := s2nMontmulP384Block_instrOk i hi
  simp only [s2nInstrOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.2 n hni

/-- `nameOf s2nAlloc` is the identity on the block's names. -/
theorem nameOf_s2nAlloc_block (n : String) (hn : n ∈ blockNamesXsym s2nMontmulP384Block) :
    nameOf s2nAlloc n = n :=
  nameOf_s2nAlloc n (s2nMontmulP384Block_names n hn)

/-- `nameOf s2nAlloc` is injective on the block's names. -/
theorem s2nMontmulP384Block_renInjOn :
    RenInjOn (blockNamesXsym s2nMontmulP384Block) (nameOf s2nAlloc) := by
  intro a ha b hb hab
  rwa [nameOf_s2nAlloc_block a ha, nameOf_s2nAlloc_block b hb] at hab

/-! ## The precondition of the byte-level result is satisfiable -/

/-- **`s2nMontmulP384_bytesCorresJ`'s precondition is satisfiable.** The all-zero
    machine state pulls back to itself along the identity allocation `s2nAlloc` (it fixes
    every name of `s2nMontmulP384Block`, by `nameOf_s2nAlloc_block`), and the underlying
    `SRm` witness `srm_stage0_satisfiable` meets it and the entry guard. So the
    `SRalloc`-pulled-back relation `s2nMontmulP384_bytesCorresJ` is stated over is not the
    empty relation, and its byte-level `CorresJ` is not a claim about no reachable
    state. -/
theorem srAlloc_stage0_satisfiable :
    ∃ st a, SRalloc (blockNamesXsym s2nMontmulP384Block) (nameOf s2nAlloc) SRm st a ∧
      a.stage = 0 ∧ a.x < 2 ^ 384 := by
  obtain ⟨st, a, hSR, hstage, hx⟩ := srm_stage0_satisfiable
  refine ⟨st, a, ⟨st, ⟨fun n hn => by rw [nameOf_s2nAlloc_block n hn], rfl,
    fun b hb _ => by rw [nameOf_s2nAlloc_block b hb]⟩, hSR⟩, hstage, hx⟩

/-! ## The byte-level results -/

/-- **The encoded bytes refine the abstract Montgomery multiplication.** The byte string
    `encodeJBlock s2nAlloc s2nMontmulP384Block` decodes as `s2nMontmulP384Block.length`
    instructions whose `runBlock` refines `montAbs` at the relation `SRm` pulled back along
    `nameOf s2nAlloc`. -/
theorem s2nMontmulP384_bytesCorresJ :
    BytesCorresJ (SRalloc (blockNamesXsym s2nMontmulP384Block) (nameOf s2nAlloc) SRm)
      (fun a => a.stage = 0 ∧ a.x < 2 ^ 384)
      (fun a => { stage := 17, x := a.x, y := a.y, acc := montAbs a.x a.y })
      s2nMontmulP384Block.length (encodeJBlock s2nAlloc s2nMontmulP384Block) :=
  encodeJBlock_bytesCorresJ s2nAlloc s2nMontmulP384Block s2nMontmulP384Block_covered
    s2nMontmulP384Block_mulxRdxOk s2nMontmulP384Block_renInjOn s2nMontmulP384_corresJ

/-- **The encoded bytes decode to the block.** `decodeJStream` reads
    `encodeJBlock s2nAlloc s2nMontmulP384Block` as exactly 264 instructions, and they are
    `s2nMontmulP384Block`. -/
theorem s2nMontmulP384_decode :
    decodeJStream 264 (encodeJBlock s2nAlloc s2nMontmulP384Block)
      = some s2nMontmulP384Block := by
  rw [← s2nMontmulP384Block_length, roundtrip_block _ _ s2nMontmulP384Block_covered
    s2nMontmulP384Block_mulxRdxOk]
  refine congrArg some ((List.map_congr_left fun i hi => ?_).trans (List.map_id _))
  rw [renameJ_eq_renameInstr _ _ (loadSymFree_of_blockCovered _
    (s2nMontmulP384Block_covered i hi))]
  exact renameInstr_eq_self_of_fix _ _ fun n hn =>
    nameOf_s2nAlloc_block n (List.mem_flatMap.mpr ⟨i, hi, hn⟩)

/-- `%rdi`, the output base register, is a name of the block. -/
theorem rdi_mem_blockNamesXsym : "%rdi" ∈ blockNamesXsym s2nMontmulP384Block :=
  List.mem_flatMap.mpr ⟨.storeMem "%rdi" 0 (.reg "%r14"),
    List.mem_append_right _ (by simp [s2nMontmulP384Seg17]), by decide⟩

/-- **The encoded bytes compute the Montgomery product modulo p384.** The byte string
    `encodeJBlock s2nAlloc s2nMontmulP384Block` decodes as 264 instructions `c` such that,
    for every machine state whose six words at `%rsi` hold `x` and whose six words at `%rcx`
    hold `y` with `x · y ≤ 2^384 · p384`, running `c` under `runBlock` stores at
    `[%rdi + 0], …, [%rdi + 40]` a value `z < p384` with `z = x · y · (2^384)⁻¹` in
    `ZMod p384`. Obtained from `s2nMontmulP384_bytesCorresJ`. -/
theorem s2nMontmulP384Bytes_correct :
    ∃ c, decodeJStream 264 (encodeJBlock s2nAlloc s2nMontmulP384Block) = some c ∧
      ∀ st : JState 64, mem6 st.mem "%rsi" * mem6 st.mem "%rcx" ≤ 2 ^ 384 * p384 →
        mem6 (runBlock st c).mem "%rdi" < p384 ∧
          ((mem6 (runBlock st c).mem "%rdi" : Nat) : ZMod p384)
            = (mem6 st.mem "%rsi" : ZMod p384) * (mem6 st.mem "%rcx" : Nat)
              * ((2 ^ 384 : Nat) : ZMod p384)⁻¹ := by
  obtain ⟨c, hdec, hcor⟩ := s2nMontmulP384_bytesCorresJ
  rw [s2nMontmulP384Block_length] at hdec
  refine ⟨c, hdec, fun st hxy => ?_⟩
  have hrel0 : StateRelOn (blockNamesXsym s2nMontmulP384Block) (nameOf s2nAlloc) st st :=
    ⟨fun n hn => by rw [nameOf_s2nAlloc_block n hn], rfl,
      fun b hb o => by rw [nameOf_s2nAlloc_block b hb]⟩
  obtain ⟨st₀, hrel, -, -, hz⟩ := hcor st
    ⟨0, mem6 st.mem "%rsi", mem6 st.mem "%rcx", 0⟩ ⟨st, hrel0, rfl, rfl, trivial⟩
    ⟨rfl, mem6_lt _ _⟩
  have hm : mem6 (runBlock st c).mem "%rdi" = mem6 st₀.mem "%rdi" := by
    have h := hrel.memOn "%rdi" rdi_mem_blockNamesXsym
    rw [nameOf_s2nAlloc_block _ rdi_mem_blockNamesXsym] at h
    simp only [mem6, h]
  have hz' : mem6 st₀.mem "%rdi" = montAbs (mem6 st.mem "%rsi") (mem6 st.mem "%rcx") := hz
  rw [hm, hz']
  exact montAbs_spec _ _ (mem6_lt _ _) hxy

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384
