/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64

/-!
# An RV64 program counter: branches, loops, calls and returns

`RiscvMem64.runX` runs a straight-line block. This module runs a program: a list of
`PInst64` loaded at an address `base`, where an instruction is a straight-line
`XInst64`, a branch `bne a, b, off`, a jump-and-link `jal d, off`, or an indirect
jump-and-link `jalr d, off(b)`. `step` fetches the instruction at `pc` (`fetch`, word
aligned) and executes it; `steps n` runs `n` steps, and is `none` if the `pc` leaves
the program first. Branch and jump offsets are relative to `pc`, as in RISC-V;
`jalr` clears bit 0 of its target.

## Main definitions

* `PInst64`, `PState64`, `fetch`, `step`, `steps`.
* `FnSpec`: a function at an address, with a precondition and a relation between entry
  and return states; it returns to the address in `ra`.
* `encodePWord64`, `encodePBlock64`, `decodeP64`, `decodePStream64`, `PInstOKb`.

## Main results

* `steps_add`: runs compose.
* `steps_block`: a straight-line block placed in a program runs as `runX`.
* `steps_loop`: a counted loop, a body that decrements a counter followed by the
  decoded back-edge `bne ctr, zero`, runs the body `n` times from counter `n`.
* `fnSpec_leaf`: a straight-line block followed by `jalr zero, 0(ra)` meets `FnSpec`
  when it leaves `ra` unchanged.
* `steps_call`: `jal ra` to a function meeting `FnSpec` returns to the next instruction.
* `steps_x`, `steps_call_at`, `steps_loop_inv`: the same rules stated by the instruction
  fetched at an index, and a loop with an invariant.
* `decodePStream64_encode_b`: the decode round trip for programs. Its proof uses the
  `bv_decide` slice lemmas `encJ_slices` and `SailRiscvDecoder.encB_slices`, so it depends on
  the native-evaluation axioms `bv_decide` adds; a concrete program can instead be checked by
  `decide +kernel` on `decodePStream64` itself.

That `step` agrees with an RV64 processor (instruction-address-misaligned traps,
compressed instructions, interrupts) is not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64

/-! ## 1. The machine -/

/-- A program instruction. Offsets are byte offsets from the instruction's own address. -/
inductive PInst64 where
  | x (i : XInst64)
  | bne (a b : String) (off : BitVec 13)
  | jal (d : String) (off : BitVec 21)
  | jalr (d b : String) (off : BitVec 12)

deriving instance DecidableEq for MInst64
deriving instance DecidableEq for XInst64
deriving instance DecidableEq for PInst64

/-- The program counter and the machine state. -/
structure PState64 where
  pc : BitVec 64
  st : MState64

/-- The instruction at `pc` of a program loaded at `base`: `none` off a word boundary or
    outside the program. -/
def fetch (prog : List PInst64) (base pc : BitVec 64) : Option PInst64 :=
  if (pc - base).toNat % 4 = 0 then prog[(pc - base).toNat / 4]? else none

/-- Execute the instruction at `pc`; `none` when there is none. -/
def step (prog : List PInst64) (base : BitVec 64) (s : PState64) : Option PState64 :=
  match fetch prog base s.pc with
  | none => none
  | some (.x i) => some ⟨s.pc + 4, evalX s.st i⟩
  | some (.bne a b off) =>
    some ⟨if s.st.regs.get a = s.st.regs.get b then s.pc + 4 else s.pc + off.signExtend 64,
      s.st⟩
  | some (.jal d off) =>
    some ⟨s.pc + off.signExtend 64, ⟨s.st.regs.set d (s.pc + 4), s.st.mem⟩⟩
  | some (.jalr d b off) =>
    some ⟨(s.st.regs.get b + off.signExtend 64) &&& ~~~1, ⟨s.st.regs.set d (s.pc + 4), s.st.mem⟩⟩

/-- Run `n` steps. -/
def steps (prog : List PInst64) (base : BitVec 64) : Nat → PState64 → Option PState64
  | 0, s => some s
  | n + 1, s => (step prog base s).bind (steps prog base n)

theorem steps_add (prog : List PInst64) (base : BitVec 64) (m n : Nat) (s : PState64) :
    steps prog base (m + n) s = (steps prog base m s).bind (steps prog base n) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih =>
    rw [Nat.add_right_comm, steps, steps]
    cases step prog base s with
    | none => rfl
    | some s' => exact ih s'

theorem steps_trans {prog : List PInst64} {base : BitVec 64} {m n : Nat} {s t u : PState64}
    (h1 : steps prog base m s = some t) (h2 : steps prog base n t = some u) :
    steps prog base (m + n) s = some u := by
  rw [steps_add, h1, Option.bind_some, h2]

/-- The address of instruction `k`. -/
def addrOf (base : BitVec 64) (k : Nat) : BitVec 64 := base + BitVec.ofNat 64 (4 * k)

theorem toNat_four : (4 : BitVec 64).toNat = 4 := rfl
theorem toNat_one : (1 : BitVec 64).toNat = 1 := rfl

theorem addrOf_sub (base : BitVec 64) (k : Nat) (hk : 4 * k < 2 ^ 64) :
    (addrOf base k - base).toNat = 4 * k := by
  have := base.isLt
  simp only [addrOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fetch_addrOf (prog : List PInst64) (base : BitVec 64) (k : Nat) (hk : 4 * k < 2 ^ 64) :
    fetch prog base (addrOf base k) = prog[k]? := by
  simp only [fetch, addrOf_sub base k hk]
  simp

theorem addrOf_succ (base : BitVec 64) (k : Nat) : addrOf base k + 4 = addrOf base (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  have := base.isLt
  simp only [addrOf, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_four]
  omega

theorem getElem?_mid (pre mid post : List PInst64) (j : Nat) (hj : j < mid.length) :
    (pre ++ mid ++ post)[pre.length + j]? = mid[j]? := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

/-! ## 2. Straight-line blocks -/

/-- **A straight-line block runs as `runX`.** -/
theorem steps_block (pre post : List PInst64) (base : BitVec 64) (b : List XInst64)
    (hk : 4 * (pre.length + b.length) < 2 ^ 64) (st : MState64) :
    steps (pre ++ b.map .x ++ post) base b.length ⟨addrOf base pre.length, st⟩
      = some ⟨addrOf base (pre.length + b.length), runX st b⟩ := by
  induction b generalizing pre st with
  | nil => simp [steps]
  | cons i is ih =>
    have hf : fetch (pre ++ (i :: is).map .x ++ post) base (addrOf base pre.length)
        = some (.x i) := by
      rw [fetch_addrOf _ _ _ (by simp at hk; omega)]
      simp
    have e : pre ++ (i :: is).map PInst64.x ++ post = (pre ++ [.x i]) ++ is.map .x ++ post := by
      simp
    simp only [List.length_cons, steps, step, hf, Option.bind_some, runX_cons, addrOf_succ]
    rw [e]
    have := ih (pre ++ [.x i]) (by simp at hk ⊢; omega) (evalX st i)
    simp only [List.length_append, List.length_singleton] at this
    rw [this]
    congr 3
    omega

/-! ## 3. Counted loops -/

/-- The body run `n` times. -/
def iterX (body : List XInst64) : Nat → MState64 → MState64
  | 0, st => st
  | n + 1, st => iterX body n (runX st body)

theorem signExtend_back (L : Nat) (hc : 4 * L < 4096) :
    (BitVec.ofInt 13 (-(4 * L : Int))).signExtend 64 = BitVec.ofInt 64 (-(4 * L : Int)) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> split <;> omega

theorem addrOf_back (base : BitVec 64) (k L : Nat) :
    addrOf base (k + L) + BitVec.ofInt 64 (-(4 * L : Int)) = addrOf base k := by
  apply BitVec.eq_of_toNat_eq
  have := base.isLt
  simp only [addrOf, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem toNat_pred (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one]
  omega

/-- **A counted loop.** In a program with the block `body` at instruction `pre.length`
    followed by `bne ctr, zero, -4·|body|`, where `body` decrements `ctr` by one, a run from
    counter `n ≥ 1` executes the body `n` times and leaves the loop. -/
theorem steps_loop (pre post : List PInst64) (base : BitVec 64) (body : List XInst64)
    (ctr : String) (hL : 4 * body.length < 4096)
    (hk : 4 * (pre.length + body.length + 1) < 2 ^ 64)
    (hdec : ∀ st : MState64, (runX st body).regs.get ctr = st.regs.get ctr - 1) :
    ∀ (n : Nat) (st : MState64), 1 ≤ n → n < 2 ^ 64 → st.regs.get ctr = BitVec.ofNat 64 n →
      steps (pre ++ body.map .x ++
          (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * body.length : Int))) :: post))
          base ((body.length + 1) * n) ⟨addrOf base pre.length, st⟩
        = some ⟨addrOf base (pre.length + body.length + 1), iterX body n st⟩ := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    intro st _ hn hc
    have hblk := steps_block pre
      (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * body.length : Int))) :: post) base body
      (by omega) st
    have hv : (runX st body).regs.get ctr = BitVec.ofNat 64 n := by
      rw [hdec, hc, toNat_pred n]
    have hfb : fetch (pre ++ body.map .x ++
        (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * body.length : Int))) :: post)) base
        (addrOf base (pre.length + body.length))
        = some (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * body.length : Int)))) := by
      rw [fetch_addrOf _ _ _ (by omega), List.getElem?_append_right (by simp)]
      simp
    have hz : (runX st body).regs.get "zero" = 0 := by simp [RState64.get]
    have hstep : steps (pre ++ body.map .x ++
        (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * body.length : Int))) :: post)) base 1
        ⟨addrOf base (pre.length + body.length), runX st body⟩ =
        some ⟨if n = 0 then addrOf base (pre.length + body.length + 1)
          else addrOf base pre.length, runX st body⟩ := by
      simp only [steps, step, hfb, Option.bind_some, hz, hv]
      by_cases h0 : n = 0
      · subst h0
        simp only [if_true]
        exact congrArg (fun pc => some (PState64.mk pc (runX st body))) (addrOf_succ _ _)
      · have hne : BitVec.ofNat 64 n ≠ 0 := by
          intro h
          have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
          omega
        simp only [hne, if_false, h0]
        rw [signExtend_back _ hL, addrOf_back base pre.length body.length]
    rw [show (body.length + 1) * (n + 1) = body.length + (1 + (body.length + 1) * n) by
        rw [Nat.mul_succ]; omega,
      steps_add, hblk, Option.bind_some, steps_add, hstep, Option.bind_some]
    by_cases h0 : n = 0
    · subst h0
      simp [iterX, steps]
    · simp only [h0, if_false]
      exact ih (runX st body) (by omega) (by omega) hv

/-! ## 4. Functions, calls and returns -/

/-- A function at address `f`: from every state satisfying `P`, some run returns to the
    address in `ra` (bit 0 cleared, as `jalr` does) in a state related to the entry state
    by `Q`. -/
def FnSpec (prog : List PInst64) (base f : BitVec 64) (P : MState64 → Prop)
    (Q : MState64 → MState64 → Prop) : Prop :=
  ∀ st, P st → ∃ n st', steps prog base n ⟨f, st⟩ = some ⟨st.regs.get "ra" &&& ~~~1, st'⟩ ∧
    Q st st'

theorem fnSpec_weaken {prog : List PInst64} {base f : BitVec 64} {P P' : MState64 → Prop}
    {Q Q' : MState64 → MState64 → Prop} (h : FnSpec prog base f P Q)
    (hP : ∀ st, P' st → P st) (hQ : ∀ st st', P' st → Q st st' → Q' st st') :
    FnSpec prog base f P' Q' := by
  intro st hst
  obtain ⟨n, st', hrun, hq⟩ := h st (hP st hst)
  exact ⟨n, st', hrun, hQ st st' hst hq⟩

/-- **A leaf function.** A straight-line block followed by `jalr zero, 0(ra)` returns to
    `ra` in the state `runX st b`, when the block leaves `ra` unchanged. -/
theorem fnSpec_leaf (pre post : List PInst64) (base : BitVec 64) (b : List XInst64)
    (hk : 4 * (pre.length + b.length + 1) < 2 ^ 64)
    (hra : ∀ st : MState64, (runX st b).regs.get "ra" = st.regs.get "ra") :
    FnSpec (pre ++ b.map .x ++ (.jalr "zero" "ra" 0 :: post)) base (addrOf base pre.length)
      (fun _ => True) (fun st st' => st' = runX st b) := by
  intro st _
  refine ⟨b.length + 1, runX st b, ?_, rfl⟩
  rw [steps_add, steps_block pre _ base b (by omega) st, Option.bind_some]
  have hf : fetch (pre ++ b.map .x ++ (.jalr "zero" "ra" 0 :: post)) base
      (addrOf base (pre.length + b.length)) = some (.jalr "zero" "ra" 0) := by
    rw [fetch_addrOf _ _ _ (by omega), List.getElem?_append_right (by simp)]
    simp
  simp only [steps, step, hf, Option.bind_some, hra]
  rw [set_zero _ _ (Or.inl rfl)]
  simp

theorem ofNat_four_mul (k : Nat) : BitVec.ofNat 64 (4 * k) = 4 * BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul, toNat_four]
  omega

/-- On a word-aligned `base`, every instruction address has bit 0 clear. -/
theorem addrOf_clear (base : BitVec 64) (hb : base &&& 3 = 0) (k : Nat) :
    addrOf base k &&& ~~~1 = addrOf base k := by
  have h4 : base.toNat % 4 = 0 := by
    have := congrArg BitVec.toNat hb
    rw [BitVec.toNat_and, show (3 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  have h2 : (addrOf base k).toNat % 2 = 0 := by
    simp only [addrOf, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0
    have : (addrOf base k).getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; simp [h2]
    rw [this, Bool.false_and]
  · simp [h0, hi]

/-- **A call.** `jal ra` to a function meeting `FnSpec` returns to the next instruction, in
    a state related by `Q` to the state with `ra` set to the return address. -/
theorem steps_call (pre post : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (off : BitVec 21) (hk : 4 * (pre.length + 1) < 2 ^ 64) {P : MState64 → Prop}
    {Q : MState64 → MState64 → Prop}
    (hspec : FnSpec (pre ++ .jal "ra" off :: post) base
      (addrOf base pre.length + off.signExtend 64) P Q)
    (st : MState64)
    (hP : P ⟨st.regs.set "ra" (addrOf base (pre.length + 1)), st.mem⟩) :
    ∃ n st', steps (pre ++ .jal "ra" off :: post) base (1 + n) ⟨addrOf base pre.length, st⟩
        = some ⟨addrOf base (pre.length + 1), st'⟩ ∧
      Q ⟨st.regs.set "ra" (addrOf base (pre.length + 1)), st.mem⟩ st' := by
  obtain ⟨n, st', hrun, hq⟩ := hspec _ hP
  refine ⟨n, st', ?_, hq⟩
  have hf : fetch (pre ++ .jal "ra" off :: post) base (addrOf base pre.length)
      = some (.jal "ra" off) := by
    rw [fetch_addrOf _ _ _ (by omega), List.getElem?_append_right (by simp)]
    simp
  rw [steps_add]
  simp only [steps, step, hf, Option.bind_some]
  rw [addrOf_succ]
  rw [RState64.get_set_same _ _ _ (by decide), addrOf_clear base hb] at hrun
  exact hrun

/-! ## 5. Encoding -/

/-- A J-type word: `imm[20] @ imm[10:1] @ imm[11] @ imm[19:12] @ rd @ opcode`. -/
def encJ (imm : BitVec 21) (rd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (imm.extractLsb' 20 1 ++ imm.extractLsb' 1 10 ++ imm.extractLsb' 11 1 ++
    imm.extractLsb' 12 8 ++ rd ++ opcode).cast rfl

/-- The J-type immediate of a word, bit 0 zero. -/
def sImmJ (w : BitVec 32) : BitVec 21 :=
  (w.extractLsb' 31 1 ++ w.extractLsb' 12 8 ++ w.extractLsb' 20 1 ++ w.extractLsb' 21 10 ++
    (0 : BitVec 1)).cast rfl

theorem encJ_slices (imm : BitVec 21) (rd : BitVec 5) (opcode : BitVec 7) :
    sOpcode (encJ imm rd opcode) = opcode ∧ sRd (encJ imm rd opcode) = rd ∧
    sImmJ (encJ imm rd opcode) = imm &&& 0x1ffffe := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [sOpcode, sRd, sImmJ, encJ] <;> bv_decide

/-- The word of an instruction (`none` for `li`). -/
def encodePWord64 : PInst64 → Option (BitVec 32)
  | .x i => encodeXWord64 i
  | .bne a b off => some (encB off (reg5 b) (reg5 a) 0b001 0x63)
  | .jal d off => some (encJ off (reg5 d) 0x6f)
  | .jalr d b off => some (encI off (reg5 b) 0b000 (reg5 d) 0x67)

/-- The little-endian bytes of a program. -/
def encodePBlock64 (b : List PInst64) : List (BitVec 8) :=
  b.flatMap fun i => match encodePWord64 i with
    | some w => wordLE w
    | none => []

/-- Decode one word: `decodeX64`, and otherwise `bne`, `jal` or `jalr`. -/
def decodeP64 (w : BitVec 32) : Option PInst64 :=
  match decodeX64 w with
  | some i => some (.x i)
  | none =>
    if fOpcode w = 0x63 ∧ fFunct3 w = 1 then
      some (.bne (regName (fRs1 w)) (regName (fRs2 w)) (sImmB w))
    else if fOpcode w = 0x6f then some (.jal (regName (fRd w)) (sImmJ w))
    else if fOpcode w = 0x67 ∧ fFunct3 w = 0 then
      some (.jalr (regName (fRd w)) (regName (fRs1 w)) (sImm12 w))
    else none

/-- The side conditions of the round trip: register names in `memRegs64`, and branch and
    jump offsets even and in range. -/
def PInstOKb : PInst64 → Bool
  | .x i => XInstOKb i
  | .bne a b off => decide (a ∈ memRegs64) && decide (b ∈ memRegs64) && (off &&& 0x1ffe == off)
  | .jal d off => decide (d ∈ memRegs64) && (off &&& 0x1ffffe == off)
  | .jalr d b _ => decide (d ∈ memRegs64) && decide (b ∈ memRegs64)

theorem decodeX64_none_of_opcode (w : BitVec 32)
    (h : fOpcode w ≠ 0x33 ∧ fOpcode w ≠ 0x13 ∧ fOpcode w ≠ 0x03 ∧ fOpcode w ≠ 0x23) :
    decodeX64 w = none := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hm : decodeM64 w = none := by
    simp only [decodeM64, riscvDecode64]
    split <;> simp_all
  simp [decodeX64, hm, h3, h4]

/-- **One instruction decodes from its word.** -/
theorem decodeP64_encode (i : PInst64) (h : PInstOKb i = true) :
    ∃ w, encodePWord64 i = some w ∧ decodeP64 w = some i := by
  cases i with
  | x i =>
    obtain ⟨w, hw, hd⟩ := decodeX64_encode i (XInstOK_of_b i h)
    exact ⟨w, hw, by simp [decodeP64, hd]⟩
  | bne a b off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨ha, hb⟩, hoff⟩ := h
    obtain ⟨ho, hf3, hr1, hr2, hi⟩ := encB_slices off (reg5 b) (reg5 a) 0b001 0x63
    refine ⟨_, rfl, ?_⟩
    rw [decodeP64, decodeX64_none_of_opcode _ (by simp only [fOpcode, ho]; decide)]
    simp only [fOpcode, fFunct3, fRs1, fRs2, ho, hf3, hr1, hr2, hi, hoff,
      regName_reg5_mem a ha, regName_reg5_mem b hb]
    simp
  | jal d off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hd, hoff⟩ := h
    obtain ⟨ho, hrd, hi⟩ := encJ_slices off (reg5 d) 0x6f
    refine ⟨_, rfl, ?_⟩
    rw [decodeP64, decodeX64_none_of_opcode _ (by simp only [fOpcode, ho]; decide)]
    simp only [fOpcode, fRd, ho, hrd, hi, hoff, regName_reg5_mem d hd]
    simp
  | jalr d b off =>
    simp only [PInstOKb, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hd, hb⟩ := h
    refine ⟨_, rfl, ?_⟩
    rw [decodeP64, decodeX64_none_of_opcode _ (by simp only [fOpcode, (encI_slices ..).1]; decide)]
    simp only [fOpcode, fFunct3, fRd, fRs1, (encI_slices ..).1, (encI_slices ..).2.1,
      (encI_slices ..).2.2.1, (encI_slices ..).2.2.2.1, (encI_slices ..).2.2.2.2,
      regName_reg5_mem d hd, regName_reg5_mem b hb]
    simp

/-- Decode `n` instructions from `bs`, which must be used up exactly. -/
def decodePStream64 : Nat → List (BitVec 8) → Option (List PInst64)
  | 0, bs => if bs.isEmpty then some [] else none
  | n + 1, b0 :: b1 :: b2 :: b3 :: rest =>
    match decodeP64 (leWord b0 b1 b2 b3) with
    | some i => (decodePStream64 n rest).map (i :: ·)
    | none => none
  | _ + 1, _ => none

/-- **A program decodes from its bytes.** -/
theorem decodePStream64_encode_b (b : List PInst64) (h : b.all PInstOKb = true) :
    decodePStream64 b.length (encodePBlock64 b) = some b := by
  induction b with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨w, hw, hd⟩ := decodeP64_encode i h.1
    obtain ⟨b0, b1, b2, b3, hle, hlw⟩ := wordLE_leWord w
    have ih' := ih h.2
    simp only [encodePBlock64, List.flatMap_cons, hw, hle, List.length_cons] at ih' ⊢
    simp only [List.cons_append, List.nil_append, decodePStream64, hlw, hd, ih',
      Option.map_some]

/-! ## 6. Rules by fetch, and loops with an invariant -/

/-- One straight-line instruction. -/
theorem steps_x (prog : List PInst64) (base : BitVec 64) (k : Nat) (hk : 4 * k < 2 ^ 64)
    (i : XInst64) (hf : prog[k]? = some (.x i)) (st : MState64) :
    steps prog base 1 ⟨addrOf base k, st⟩ = some ⟨addrOf base (k + 1), evalX st i⟩ := by
  simp only [steps, step, fetch_addrOf prog base k hk, hf, Option.bind_some, addrOf_succ]

/-- `addrOf base k` plus the offset `4·(j − k)` is `addrOf base j`. -/
theorem addrOf_rel21 (base : BitVec 64) (k j : Nat) (h1 : 4 * k < 2 ^ 20) (h2 : 4 * j < 2 ^ 20) :
    addrOf base k + (BitVec.ofInt 21 (4 * (j : Int) - 4 * k)).signExtend 64 = addrOf base j := by
  have hs : (BitVec.ofInt 21 (4 * (j : Int) - 4 * k)).signExtend 64
      = BitVec.ofInt 64 (4 * (j : Int) - 4 * k) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
    simp only [Int.bmod]
    split <;> split <;> omega
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  have := base.isLt
  simp only [addrOf, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- **A call, by fetch.** -/
theorem steps_call_at (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (k j : Nat) (h1 : 4 * k < 2 ^ 20) (h2 : 4 * j < 2 ^ 20)
    (hf : prog[k]? = some (.jal "ra" (BitVec.ofInt 21 (4 * (j : Int) - 4 * k))))
    {P : MState64 → Prop} {Q : MState64 → MState64 → Prop}
    (hspec : FnSpec prog base (addrOf base j) P Q) (st : MState64)
    (hP : P ⟨st.regs.set "ra" (addrOf base (k + 1)), st.mem⟩) :
    ∃ n st', steps prog base (1 + n) ⟨addrOf base k, st⟩ = some ⟨addrOf base (k + 1), st'⟩ ∧
      Q ⟨st.regs.set "ra" (addrOf base (k + 1)), st.mem⟩ st' := by
  obtain ⟨n, st', hrun, hq⟩ := hspec _ hP
  refine ⟨n, st', ?_, hq⟩
  rw [steps_add]
  simp only [steps, step, fetch_addrOf prog base k (by omega), hf, Option.bind_some,
    addrOf_rel21 base k j h1 h2, addrOf_succ]
  rw [RState64.get_set_same _ _ _ (by decide), addrOf_clear base hb] at hrun
  exact hrun

/-- **A loop with an invariant.** The body is the code from instruction `kb` to the
    back-edge `bne ctr, zero` at instruction `ke`. If every run of the body from counter
    `c ≥ 1` and `I c` reaches the back-edge with counter `c - 1` and `I (c - 1)`, then a run
    from counter `n ≥ 1` and `I n` leaves the loop with `I 0`. -/
theorem steps_loop_inv (prog : List PInst64) (base : BitVec 64) (kb ke : Nat) (ctr : String)
    (hke : kb ≤ ke) (hL : 4 * (ke - kb) < 4096) (hk : 4 * (ke + 1) < 2 ^ 64)
    (hbne : prog[ke]? = some (.bne ctr "zero" (BitVec.ofInt 13 (-(4 * (ke - kb : Nat) : Int)))))
    (I : Nat → MState64 → Prop)
    (hbody : ∀ c st, 1 ≤ c → I c st → st.regs.get ctr = BitVec.ofNat 64 c →
      ∃ m st', steps prog base m ⟨addrOf base kb, st⟩ = some ⟨addrOf base ke, st'⟩ ∧
        I (c - 1) st' ∧ st'.regs.get ctr = BitVec.ofNat 64 (c - 1)) :
    ∀ n st, 1 ≤ n → n < 2 ^ 64 → I n st → st.regs.get ctr = BitVec.ofNat 64 n →
      ∃ m st', steps prog base m ⟨addrOf base kb, st⟩ = some ⟨addrOf base (ke + 1), st'⟩ ∧
        I 0 st' := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    intro st _ hn hI hc
    obtain ⟨m, st', hrun, hI', hc'⟩ := hbody (n + 1) st (by omega) hI hc
    simp only [Nat.add_sub_cancel] at hI' hc'
    have hz : st'.regs.get "zero" = 0 := by simp [RState64.get]
    have hstep : steps prog base 1 ⟨addrOf base ke, st'⟩ =
        some ⟨if n = 0 then addrOf base (ke + 1) else addrOf base kb, st'⟩ := by
      simp only [steps, step, fetch_addrOf prog base ke (by omega), hbne, Option.bind_some, hz,
        hc']
      by_cases h0 : n = 0
      · subst h0
        simp only [if_true]
        exact congrArg (fun pc => some (PState64.mk pc st')) (addrOf_succ _ _)
      · have hne : BitVec.ofNat 64 n ≠ 0 := by
          intro h
          have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
          omega
        simp only [hne, if_false, h0]
        have e := addrOf_back base kb (ke - kb)
        rw [Nat.add_sub_cancel' hke] at e
        rw [signExtend_back _ hL, e]
    by_cases h0 : n = 0
    · subst h0
      refine ⟨m + 1, st', ?_, hI'⟩
      rw [steps_trans hrun hstep]
      rfl
    · obtain ⟨m', st'', hrun', hI''⟩ := ih st' (by omega) (by omega) hI' hc'
      refine ⟨m + 1 + m', st'', ?_, hI''⟩
      rw [steps_add, steps_trans hrun hstep]
      simp only [h0, if_false, Option.bind_some]
      exact hrun'

/-- The destination register of an instruction, if any. -/
def xDst : XInst64 → Option String
  | .m i => some (mDst i)
  | .ld d _ _ => some d
  | .sd _ _ _ => none

/-- The registers a block writes. -/
def xWrites (b : List XInst64) : List String := b.filterMap xDst

/-- **A block leaves every register it does not write.** -/
theorem runX_frame (b : List XInst64) (st : MState64) (r : String) (h : r ∉ xWrites b) :
    (runX st b).regs.get r = st.regs.get r := by
  induction b generalizing st with
  | nil => rfl
  | cons i is ih =>
    simp only [runX_cons]
    cases i with
    | m i =>
      simp only [xWrites, List.filterMap_cons, xDst, List.mem_cons, not_or] at h
      obtain ⟨h1, h2⟩ := h
      rw [ih _ h2]
      exact evalMInst64_get_other _ _ _ h1
    | ld d b off =>
      simp only [xWrites, List.filterMap_cons, xDst, List.mem_cons, not_or] at h
      obtain ⟨h1, h2⟩ := h
      rw [ih _ h2]
      exact RState64.get_set_other _ _ _ _ h1
    | sd v b off =>
      simp only [xWrites, List.filterMap_cons, xDst] at h
      exact ih _ h

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
