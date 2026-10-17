/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ContractOfCorres
public import CatCrypt.Crypto.SecureCompilation.SepLogic.ContractX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519BytesLeafCalls
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTKernels

/-!
# The contract of the byte-decoded field addition `fe25519_add`

The shipped bytes `fe25519_add_x86_from_lean` are `encodeJBlock s2nAlloc feAddFramed`, and
they decode to the block `feAddFramed` (`Fe25519BytesLeaves.feAddFramed_decode`). Its callee
is the leaky run `runOf .doitm (feAddFramed.map .op ++ [.ret])` of the block followed by
`ret`. The contract `feAddContract` over the locations `SepLogic.X86.Loc` has the entry state
as its logical variable. Its precondition is that the two argument buffers at `%rsi` and
`%rdx` and the output buffer at `%rdi` lie outside the 48 bytes below `%rsp` and that both
arguments are below `2 ^ 255 - 19`; its postcondition is that the four-limb value at the
entry `%rdi` is the sum of the arguments modulo that prime; its write set is made of the 32
bytes at `%rdi`, the 48 bytes below `%rsp`, the flags and the registers other than `%rsp`
and the callee-saved ones; and its public relation is agreement on the pointer registers and
`%rsp` (`DecodedCT.fePubA`).

The postcondition and the write set follow from `feAddFramed_correct_addr`; the constant
time of the runs follows from the acceptance of the block by the byte-level checker
(`DecodedCT.feAddFramed_bytesCT`) under DOITM.

## Main definitions

* `FeAddPre`: the precondition of the field addition at an entry state.
* `feAddWrites`: the locations the field addition may change.
* `feAddContract`: the contract of the field addition.

## Main results

* `not_inRange8_of_not_mem`: a byte outside a range of `8 * n` bytes lies outside each of its
  eight-byte words.
* `feAdd_contract`: the shipped bytes of `fe25519_add` decode to a block whose leaky run under
  DOITM meets `feAddContract`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddContract

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc stateAssert)
open CatCrypt.Crypto.SecureCompilation.Ascent (contract_of_runBlockA ctRel_of_bytesCTCheck)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
  (feO pM RangeDisj addI)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519KernelsBytes (feAddFramed)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519BytesLeaves
  (feAddFramed_decode feAddFramed_correct_addr)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.S2nMontmulP384 (s2nAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (fePubA feAddFramed_bytesCT)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (decodeJStream)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (encodeJBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)
open Footprinted

/-- The precondition of the field addition at the entry state `s`: the argument buffers at
    `%rsi` and `%rdx` and the output buffer at `%rdi` lie outside the 48 bytes below `%rsp`,
    and both arguments are below `2 ^ 255 - 19`. -/
def FeAddPre (s : AState) : Prop :=
  RangeDisj (s.regs "%rsi") 0 24 (s.regs "%rsp") (-48) (-8)
    ∧ RangeDisj (s.regs "%rdx") 0 24 (s.regs "%rsp") (-48) (-8)
    ∧ RangeDisj (s.regs "%rdi") 0 24 (s.regs "%rsp") (-48) (-8)
    ∧ feO s.mem (s.regs "%rsi") 0 < pM ∧ feO s.mem (s.regs "%rdx") 0 < pM

/-- The locations the field addition may change from the entry state `s`: the registers
    other than `%rsp` and the callee-saved ones, the flags, the 32 bytes at `%rdi` and the 48
    bytes below `%rsp`. -/
def feAddWrites (s : AState) : Set Loc := fun l =>
  match l with
  | .reg r => r ≠ "%rsp" ∧ r ∉ calleeSavedRegs
  | .flag _ => True
  | .mem x => x ∈ (⟨s.regs "%rdi", 32⟩ : Rng 64)
      ∨ x ∈ (⟨s.regs "%rsp" + BitVec.ofInt 64 (-48), 48⟩ : Rng 64)

/-- The contract of the field addition, with the entry state as logical variable: the
    precondition `FeAddPre`, the sum modulo `2 ^ 255 - 19` at the entry `%rdi`, the write set
    `feAddWrites` and agreement on the pointer registers and `%rsp`. -/
def feAddContract : ContractSpec AState Loc AState where
  pre a := stateAssert fun s => s = a ∧ FeAddPre s
  post a := stateAssert fun s' => feO s'.mem (a.regs "%rdi") 0
    = (feO a.mem (a.regs "%rsi") 0 + feO a.mem (a.regs "%rdx") 0) % pM
  writes _ s := feAddWrites s
  pub := fePubA.Agree

/-- A byte outside the `8 * n` bytes from `a` lies outside the eight-byte word at
    `a + 8 * i` for every `i < n`. -/
theorem not_inRange8_of_not_mem {a x : BitVec 64} {n i : Nat}
    (h : x ∉ (⟨a, 8 * n⟩ : Rng 64)) (hi : i < n) :
    ¬ InRange8 (a + BitVec.ofInt 64 (8 * i : Nat)) x := by
  change ¬ (x - a).toNat < 8 * n at h
  unfold InRange8
  rw [BitVec.ofInt_natCast]
  bv_omega

/-- **The contract of the byte-decoded `fe25519_add`.** The shipped bytes decode to a block
    `c` such that the leaky run of `c` followed by `ret` under DOITM meets `feAddContract`. -/
theorem feAdd_contract :
    ∃ c, decodeJStream 57 (encodeJBlock s2nAlloc feAddFramed) = some c ∧
      SContract (runOf .doitm (c.map .op ++ [.ret])) feAddContract := by
  refine ⟨feAddFramed, feAddFramed_decode, contract_of_runBlockA ?_ ?_ ?_⟩
  · rintro a s ⟨rfl, hi, hj, ho, h1, h2⟩
    exact (feAddFramed_correct_addr s hi hj ho).1 h1 h2
  · rintro a s ⟨rfl, hi, hj, ho, -, -⟩ l hl
    obtain ⟨-, hf, hr, hs⟩ := feAddFramed_correct_addr s hi hj ho
    cases l with
    | reg r =>
      change s.regs r = (runBlockA s feAddFramed).regs r
      by_cases hsp : r = "%rsp"
      · subst hsp
        exact hr.symm
      · change ¬ (r ≠ "%rsp" ∧ r ∉ calleeSavedRegs) at hl
        exact (hs r (Classical.not_not.1 fun h => hl ⟨hsp, h⟩)).symm
    | flag f => exact absurd trivial hl
    | mem x =>
      change s.mem x = (runBlockA s feAddFramed).mem x
      have hx : x ∉ (⟨s.regs "%rdi", 8 * 4⟩ : Rng 64)
          ∧ x ∉ (⟨s.regs "%rsp" + BitVec.ofInt 64 (-48), 8 * 6⟩ : Rng 64) := not_or.1 hl
      refine (hf x (fun i hi => not_inRange8_of_not_mem hx.1 hi) fun i hi => ?_).symm
      have e := not_inRange8_of_not_mem hx.2 (show 5 - i < 6 by omega)
      rwa [addI, show (-48 : Int) + ((8 * (5 - i) : Nat) : Int)
        = (-(8 * (i + 1) : Nat) : Int) from by omega] at e
  · obtain ⟨c, hc, hct⟩ := feAddFramed_bytesCT
    rw [feAddFramed_decode, Option.some.injEq] at hc
    subst hc
    exact ctRel_of_bytesCTCheck hct fun _ _ h => h

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Fe25519AddContract
