/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64

/-!
# RV64 blocks as bytes: constants, encoding and a decoded stream

`RiscvEncoder64.encodeWord64` encodes every `RInst64` except `li`, which the assembler
expands to a sequence whose length depends on the constant. This module gives `li` an
expansion of its own and states the block round trip at the byte level.

The machine instructions are `MInst64`: an `RInst64` other than `li`, or `ADDI rd, rs1,
imm` with a nonzero 12-bit immediate, sign-extended as in the RISC-V `ITYPE` encoding
(`ADDI` with immediate 0 is `mv`, already an `RInst64`). `liSeq d v` loads `v` into `d`
with one `ADDI` of a signed 12-bit top chunk, then pairs `slli d, d, 11; addi d, d, c`
for each lower 11-bit chunk `c` (the `addi` left out when `c = 0`). It is at most eleven
instructions and one for a constant in `[-2048, 2048)`; it is not the sequence `as`
chooses. `expandLi` replaces every `li` of a block by its `liSeq`.

`decodeMStream64 n bs` reads `n` little-endian words from `bs` and decodes each with
`decodeM64`: `SailRiscvDecoder64.riscvDecode64`, and the `ADDI` case where that returns
`none`.

## Main definitions

* `MInst64`, `evalMInst64`, `runM64`: the machine instructions and their execution.
* `liSeq`, `expandLi`: the constant loads.
* `encodeMWord64`, `encodeMBlock64`, `leWord`, `decodeM64`, `decodeMStream64`.
* `MInstOK`, `MInstOKb`: the side conditions of the round trip.

## Main results

* `runM64_liSeq`: `liSeq d v` has the effect of `li d v`.
* `runM64_expandLi`: `expandLi b` runs as `b`.
* `decodeM64_encode`: each instruction satisfying `MInstOK` decodes from its word.
* `decodeMStream64_encode`, `decodeMStream64_encode_b`: a block of such instructions
  decodes from its bytes.
* `runM64_phys`: a renamed block, with its constants expanded, computes the live-out
  values of the symbolic block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvRename64

/-! ## 1. Machine instructions -/

/-- An RV64 machine instruction: an `RInst64` (the round trip excludes `li`), or `ADDI`. -/
inductive MInst64 where
  | base (i : RInst64)
  | addi (d a : String) (imm : BitVec 12)

/-- Execute one machine instruction. `ADDI` adds the sign-extended immediate. -/
def evalMInst64 (s : RState64) : MInst64 → RState64
  | .base i => evalRInst64 s i
  | .addi d a imm => s.set d (s.get a + imm.signExtend 64)

/-- Execute a block of machine instructions, left to right. -/
def runM64 (s : RState64) : List MInst64 → RState64
  | [] => s
  | i :: is => runM64 (evalMInst64 s i) is

theorem runM64_append (s : RState64) (xs ys : List MInst64) :
    runM64 s (xs ++ ys) = runM64 (runM64 s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih _

/-! ## 2. Constant loads -/

/-- One lower chunk: shift the partial constant up by 11 bits and add `c`. -/
def liStep (d : String) (c : Int) : List MInst64 :=
  .base (.slli d d 11) :: (if c = 0 then [] else [.addi d d (BitVec.ofInt 12 c)])

/-- Load the integer `w` into `d`, most significant chunk first, in at most `n` lower
    chunks. Correct when `w` has at most `n` lower chunks (`runM64_liGo`). -/
def liGo : Nat → String → Int → List MInst64
  | 0, d, w => [if w = 0 then .base (.mv d "zero") else .addi d "zero" (BitVec.ofInt 12 w)]
  | n + 1, d, w =>
    if -2048 ≤ w ∧ w < 2048 then liGo 0 d w
    else liGo n d (w / 2048) ++ liStep d (w % 2048)

/-- `v mod 2^64` as a signed 64-bit integer. -/
def toSigned64 (v : Nat) : Int :=
  if v % 2 ^ 64 < 2 ^ 63 then ((v % 2 ^ 64 : Nat) : Int) else ((v % 2 ^ 64 : Nat) : Int) - 2 ^ 64

/-- The load of the constant `v` into `d`. -/
def liSeq (d : String) (v : Nat) : List MInst64 := liGo 5 d (toSigned64 v)

/-- Replace every `li` of a block by its `liSeq`. -/
def expandLi (b : List RInst64) : List MInst64 :=
  b.flatMap fun i => match i with
    | .li d v => liSeq d v
    | i => [.base i]

theorem set_set (s : RState64) (d : String) (x y : X64R) :
    (s.set d x).set d y = s.set d y := by
  unfold RState64.set
  by_cases h : d = "zero" ∨ d = "x0"
  · simp [h]
  · simp only [h, if_false]
    congr 1
    funext r
    by_cases hr : r = d <;> simp [hr]

theorem set_zero (s : RState64) (d : String) (h : d = "zero" ∨ d = "x0") (x : X64R) :
    s.set d x = s := by
  simp [RState64.set, h]

theorem signExtend_ofInt (c : Int) (h1 : -2048 ≤ c) (h2 : c < 2048) :
    (BitVec.ofInt 12 c).signExtend 64 = BitVec.ofInt 64 c := by
  rw [BitVec.signExtend, BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]

theorem shl11 (x : BitVec 64) : x <<< 11 = x * BitVec.ofInt 64 2048 := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1

theorem runM64_liGo_zero (d : String) (w : Int) (h1 : -2048 ≤ w) (h2 : w < 2048)
    (s : RState64) : runM64 s (liGo 0 d w) = s.set d (BitVec.ofInt 64 w) := by
  rw [liGo]
  by_cases hw : w = 0
  · subst hw
    simp only [if_true, runM64, evalMInst64, evalRInst64]
    rfl
  · simp only [hw, if_false, runM64, evalMInst64]
    rw [signExtend_ofInt w h1 h2]
    simp [RState64.get]

/-- **`liGo n d w` loads `w`** when `w` has at most `n` lower chunks. -/
theorem runM64_liGo (n : Nat) (d : String) (w : Int)
    (h1 : -(2048 * 2048 ^ n) ≤ w) (h2 : w < 2048 * 2048 ^ n) (s : RState64) :
    runM64 s (liGo n d w) = s.set d (BitVec.ofInt 64 w) := by
  induction n generalizing w s with
  | zero => exact runM64_liGo_zero d w (by simpa using h1) (by simpa using h2) s
  | succ n ih =>
    rw [liGo]
    split
    · rename_i h
      exact runM64_liGo_zero d w h.1 h.2 s
    rw [runM64_append, ih (w / 2048) (by rw [pow_succ] at h1; omega)
      (by rw [pow_succ] at h2; omega)]
    by_cases hz : d = "zero" ∨ d = "x0"
    · rw [set_zero _ _ hz, liStep]
      split <;> simp [runM64, evalMInst64, evalRInst64, set_zero _ _ hz]
    · have hget : (s.set d (BitVec.ofInt 64 (w / 2048))).get d = BitVec.ofInt 64 (w / 2048) :=
        RState64.get_set_same _ _ _ hz
      unfold liStep
      split
      · simp only [runM64, evalMInst64, evalRInst64, hget, set_set]
        congr 1
        rw [shl11, ← BitVec.ofInt_mul]
        congr 1
        omega
      · simp only [runM64, evalMInst64, evalRInst64, hget, set_set,
          RState64.get_set_same _ _ _ hz]
        rw [signExtend_ofInt _ (by omega) (by omega), shl11, ← BitVec.ofInt_mul,
          ← BitVec.ofInt_add]
        congr 2
        omega

theorem toSigned64_range (v : Nat) :
    -(2048 * 2048 ^ 5) ≤ toSigned64 v ∧ toSigned64 v < 2048 * 2048 ^ 5 := by
  unfold toSigned64
  have := Nat.mod_lt v (show 0 < 2 ^ 64 by decide)
  split <;> omega

theorem ofInt_toSigned64 (v : Nat) : BitVec.ofInt 64 (toSigned64 v) = BitVec.ofNat 64 v := by
  unfold toSigned64
  split
  · rw [BitVec.ofInt_natCast]
    exact BitVec.eq_of_toNat_eq (by simp)
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

/-- **`liSeq d v` has the effect of `li d v`.** -/
theorem runM64_liSeq (d : String) (v : Nat) (s : RState64) :
    runM64 s (liSeq d v) = evalRInst64 s (.li d v) := by
  rw [liSeq, runM64_liGo 5 d _ (toSigned64_range v).1 (toSigned64_range v).2,
    ofInt_toSigned64]
  rfl

/-- **`expandLi b` runs as `b`.** -/
theorem runM64_expandLi (b : List RInst64) (s : RState64) :
    runM64 s (expandLi b) = runRBlock64 s b := by
  induction b generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [expandLi, List.flatMap_cons] at ih ⊢
    rw [runM64_append]
    cases i <;> first
      | (rw [runM64_liSeq, ih]; rfl)
      | (simp only [runM64]; exact ih _)

/-! ## 3. Encoding and decoding one instruction -/

/-- The 32-bit word of a machine instruction (`none` for `li`). -/
def encodeMWord64 : MInst64 → Option (BitVec 32)
  | .base i => encodeWord64 i
  | .addi d a imm => some (encI imm (reg5 a) 0b000 (reg5 d) 0x13)

/-- The little-endian bytes of a block. -/
def encodeMBlock64 (b : List MInst64) : List (BitVec 8) :=
  b.flatMap fun i => match encodeMWord64 i with
    | some w => wordLE w
    | none => []

/-- Decode one word: `riscvDecode64`, and otherwise `ADDI` (opcode `0x13`, `funct3 = 0`). -/
def decodeM64 (w : BitVec 32) : Option MInst64 :=
  match riscvDecode64 w with
  | some i => some (.base i)
  | none =>
    if fOpcode w = 0x13 ∧ fFunct3 w = 0 then
      some (.addi (regName (fRd w)) (regName (fRs1 w)) (BitVec.ofNat 12 (fImm12 w)))
    else none

/-- The side conditions of the round trip: register names in `emittedRegs64`, no `li`,
    shift counts below 64, and a nonzero `ADDI` immediate. -/
def MInstOK : MInst64 → Prop
  | .base i => (∀ d imm, i ≠ .li d imm) ∧
      ((rinst64DstSrcs i).1 ∈ emittedRegs64 ∧ ∀ r ∈ (rinst64DstSrcs i).2, r ∈ emittedRegs64) ∧
      (∀ d a sh, i = .srli d a sh ∨ i = .slli d a sh → sh < 64)
  | .addi d a imm => d ∈ emittedRegs64 ∧ a ∈ emittedRegs64 ∧ imm ≠ 0

/-- `MInstOK` as a `Bool`, for `decide` over a whole block. -/
def MInstOKb : MInst64 → Bool
  | .base (.li _ _) => false
  | .base (.srli d a sh) => decide (d ∈ emittedRegs64) && decide (a ∈ emittedRegs64) && decide (sh < 64)
  | .base (.slli d a sh) => decide (d ∈ emittedRegs64) && decide (a ∈ emittedRegs64) && decide (sh < 64)
  | .base i => decide ((rinst64DstSrcs i).1 ∈ emittedRegs64) &&
      (rinst64DstSrcs i).2.all (fun r => decide (r ∈ emittedRegs64))
  | .addi d a imm => decide (d ∈ emittedRegs64) && decide (a ∈ emittedRegs64) && imm != 0

theorem MInstOK_of_b (i : MInst64) (h : MInstOKb i = true) : MInstOK i := by
  cases i with
  | base i =>
    cases i <;>
      simp_all [MInstOKb, MInstOK, rinst64DstSrcs, decide_eq_true_eq] <;>
      exact of_decide_eq_true h.1
  | addi d a imm => simp_all [MInstOKb, MInstOK, decide_eq_true_eq]

theorem riscvDecode64_addi (d a : String) (imm : BitVec 12) (h : imm ≠ 0) :
    riscvDecode64 (encI imm (reg5 a) 0b000 (reg5 d) 0x13) = none := by
  have D := decConsts64
  have hi : imm.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp only [riscvDecode64, fOpcode, fRd, fRs1, fFunct3, fImm12, fFunct7,
    (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
    (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2, D.2.1, D.2.2.2.2.2.1]
  split <;> simp_all

/-- **One instruction decodes from its word.** -/
theorem decodeM64_encode (i : MInst64) (h : MInstOK i) :
    ∃ w, encodeMWord64 i = some w ∧ decodeM64 w = some i := by
  cases i with
  | base i =>
    obtain ⟨hli, hregs, hsh⟩ := h
    have hrt := roundtrip_RInst64 i hli hregs hsh
    cases hw : encodeWord64 i with
    | none => cases i <;> simp_all [encodeWord64]
    | some w =>
      refine ⟨w, hw, ?_⟩
      rw [hw] at hrt
      simp only [Option.get!] at hrt
      simp [decodeM64, hrt]
  | addi d a imm =>
    obtain ⟨hd, ha, hi⟩ := h
    refine ⟨_, rfl, ?_⟩
    have D := decConsts64
    simp only [decodeM64, riscvDecode64_addi d a imm hi, fOpcode, fRd, fRs1, fFunct3, fImm12,
      (encI_slices ..).1, (encI_slices ..).2.1, (encI_slices ..).2.2.1,
      (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2, D.2.1, D.2.2.2.2.2.1,
      regName_reg5_64 d hd, regName_reg5_64 a ha, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp

/-! ## 4. The byte stream -/

/-- The word with little-endian bytes `b0 b1 b2 b3`. -/
def leWord (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  BitVec.ofNat 32 (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat)

/-- Decode `n` instructions from `bs`, which must be used up exactly. -/
def decodeMStream64 : Nat → List (BitVec 8) → Option (List MInst64)
  | 0, bs => if bs.isEmpty then some [] else none
  | n + 1, b0 :: b1 :: b2 :: b3 :: rest =>
    match decodeM64 (leWord b0 b1 b2 b3) with
    | some i => (decodeMStream64 n rest).map (i :: ·)
    | none => none
  | _ + 1, _ => none

theorem wordLE_leWord (w : BitVec 32) :
    ∃ b0 b1 b2 b3, wordLE w = [b0, b1, b2, b3] ∧ leWord b0 b1 b2 b3 = w := by
  refine ⟨_, _, _, _, rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [leWord, BitVec.toNat_ofNat, Nat.and_two_pow_sub_one_eq_mod _ 8,
    Nat.shiftRight_eq_div_pow]
  omega

/-- **A block decodes from its bytes.** -/
theorem decodeMStream64_encode (b : List MInst64) (h : ∀ i ∈ b, MInstOK i) :
    decodeMStream64 b.length (encodeMBlock64 b) = some b := by
  induction b with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨w, hw, hd⟩ := decodeM64_encode i (h i (by simp))
    obtain ⟨b0, b1, b2, b3, hle, hlw⟩ := wordLE_leWord w
    have ih' := ih fun j hj => h j (by simp [hj])
    simp only [encodeMBlock64, List.flatMap_cons, hw, hle, List.length_cons] at ih' ⊢
    simp only [List.cons_append, List.nil_append, decodeMStream64, hlw, hd, ih', Option.map_some]

/-! ## 5. Physical blocks

A kernel over symbolic names reaches the bytes as `expandLi (renameRBlock64 ρ b)`. When
`renGo` accepts `ρ` on `b`, each live-out name `x` of the symbolic run is read at `ρ x`
after the physical run, from the state `pull ρ t` read back from the physical one. -/

theorem pull_get (ρ : String → String) (hz : ρ "zero" = "zero") (hx0 : ρ "x0" = "x0")
    (t : RState64) (x : String) : (pull ρ t).get x = t.get (ρ x) :=
  pull_relOn ρ hz hx0 [x] t x (List.mem_singleton_self x) |>.symm

/-- **The physical block computes the symbolic block's live-out values.** -/
theorem runM64_phys (ρ : String → String) (hz : ρ "zero" = "zero") (hx0 : ρ "x0" = "x0")
    (b : List RInst64) (L Lin : List String) (hok : renGo ρ b L = some Lin) (t : RState64)
    (x : String) (hx : x ∈ L) :
    (runM64 t (expandLi (renameRBlock64 ρ b))).get (ρ x) = (runRBlock64 (pull ρ t) b).get x := by
  rw [runM64_expandLi]
  exact runRBlock64_rename ρ b L Lin hok (pull ρ t) t (pull_relOn ρ hz hx0 Lin t) x hx

/-- A block whose instructions pass `MInstOKb` decodes from its bytes. -/
theorem decodeMStream64_encode_b (b : List MInst64) (h : b.all MInstOKb = true) :
    decodeMStream64 b.length (encodeMBlock64 b) = some b :=
  decodeMStream64_encode b fun i hi => MInstOK_of_b i (List.all_eq_true.1 h i hi)

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
