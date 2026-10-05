/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAbiEncoder
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachineBlock
public import CatCrypt.Crypto.SecureCompilation.CT.IsaRegime

@[expose] public section

set_option autoImplicit false

/-!
# The AArch64 machine level of the instruction-set record

`armMach r` is the `LprogIsa.IsaMachine` of AArch64 under the timing regime `r`. A decoded
program is a list of `ArmInstr`: an instruction `BMInst` of the memory-and-branch fragment,
or `RET`. The state is `BMState`, the effect of an operation is `evalBMInst`, and the decoder
`decodeArmProg` reads 4-byte words with `SailArmDecoder.decodeBM64` and reads the word of
`ArmAbiEncoder.encRet` as `RET`. The action `armAct` of a straight-line instruction is the
instruction; `CBNZ` and `B.cond` are branches whose outcome is the test of `evalBMInst` and
whose target is the index `LprogIsa.wordTarget` of their byte displacement.

The index of a run of `IsaMachine` is the program counter. The field `pc` of `BMState` is
written by `evalBMInst` and read by no operation and no action; `armAct_cbnz_pc` and
`armAct_bcond_pc` state that, from a state whose `pc` is the byte address of the index, the
`pc` after the `evalBMInst` step of a branch is the byte address of the index the action
continues at.

The leakage `armOpLeak r` of an operation is the effective address of its memory access, as
an `addr` event with the empty region and the address as offset, followed by its register
operands when the regime `r` makes the operands of its mnemonic observable. `ArmRegime.dit`
is the regime with `PSTATE.DIT = 1`, whose table is `CT.ArmMnem.leaksOperands`; under
`ArmRegime.unguaranteed` every straight-line instruction leaks its operands. The operand
event is `CTLeak.vtCall` named by the mnemonic, the event `CTLeak.vt` being indexed by the
x86 mnemonic table.

The two channels of a load or store are separate events. The address channel is the `addr`
event of the effective address, emitted under every regime (`armOpLeak_addrEvents`): the DIT
register description makes no statement about the address of an access. The data channel is
the operand event, which carries the value loaded or stored; the clause "the timing of every
load and store instruction is insensitive to the value of the data being loaded or stored"
of the DIT register description removes it under `ArmRegime.dit` (`armOpLeak_dit_mem`).
`ArmRegime` is a `CT.TimingRegime` over `CT.ArmMnem`, with `dit` the regime of the
specification.

## Main definitions

* `ArmInstr`, `decodeArmWord`, `decodeArmProg`: the decoded instructions and the decoder.
* `ArmRegime`, `ArmRegime.leaksOperands`, `bmMnem`, `armOpLeak`: the timing regime and the
  leakage of one operation.
* `bmStraight`, `armAct`, `armMach`: the straight-line instructions, the action and the
  machine.

## Main results

* `decodeArmProg_block`, `decodeArmProg_encRet`: the decoder on a block followed by `RET`.
* `armOpLeak_dit`: under `ArmRegime.dit` an operation leaks the address of its memory access
  and nothing else.
* `armOpLeak_addrEvents`, `armOpLeak_mem`, `armOpLeak_dit_mem`, `armOpLeak_dataEvents_dit`: the
  address channel of an operation is the effective address of its memory access under every
  regime, and the data channel is empty under `ArmRegime.dit`.
* `armIsa_leaksOperands_dit`, `armIsa_leaksOperands_none`: the field `leaksOperands` of
  `armIsa` is the table under `ArmRegime.dit` at the mnemonic of a base of `armMnemOfBase`,
  and `true` at any other base.
* `armMach_halts_block`, `armMach_runL_block`: a straight-line block followed by `RET` halts
  in the state `runBMBlock`, with the leakage of the block.
* `armAct_cbnz`, `armAct_bcond_ne`: the branch actions take the `armIsa` branch condition of a
  related state.
* `armSelX_straight`, `arm_mach_step`, `arm_mach_x`: the decode-and-step simulation of the
  selection `armSelX`. The bytes of the selected block followed by `RET` decode to the
  selected program, one machine step simulates one `armIsa` step, and the machine run halts
  in a state related to the `armIsa` run.
* `arm_and_mach`, `armAndCode_leak_dit`: the `mpn_and_n` body at `armMach`, and its leakage
  under `ArmRegime.dit`, the three addresses of its limb accesses.
-/

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.SailArmDecoder
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa
open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## Decoded programs -/

/-- A decoded AArch64 instruction: an instruction of the memory-and-branch fragment, or
    `RET`. -/
inductive ArmInstr where
  /-- An instruction of `BMInst`. -/
  | op (i : BMInst)
  /-- `RET` (through `x30`). -/
  | ret
  deriving DecidableEq, Repr

/-- Decode one 4-byte word: an instruction of `decodeBM64`, and otherwise `RET` on the word
    of `ArmAbiEncoder.encRet`. -/
def decodeArmWord (w : List (BitVec 8)) : Option ArmInstr :=
  match decodeBM64 w with
  | some i => some (.op i)
  | none => if w = ArmAbiEncoder.encRet then some .ret else none

/-- Decode a byte stream of 4-byte AArch64 words with `decodeArmWord`; `none` on a word
    outside the decoder or a trailing partial word. -/
def decodeArmProg : List (BitVec 8) → Option (List ArmInstr)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (decodeArmWord [b0, b1, b2, b3]).bind
        (fun i => (decodeArmProg rest).map (fun is => i :: is))
  | _ => none

/-- A four-byte word followed by a stream decodes as the word followed by the stream. -/
theorem decodeArmProg_cons (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    decodeArmProg (b0 :: b1 :: b2 :: b3 :: rest) =
      (decodeArmWord [b0, b1, b2, b3]).bind
        (fun i => (decodeArmProg rest).map (fun is => i :: is)) := rfl

/-- A word `decodeBM64` decodes is decoded by `decodeArmWord` as the same instruction. -/
theorem decodeArmWord_of_decodeBM64 {w : List (BitVec 8)} {i : BMInst}
    (h : decodeBM64 w = some i) : decodeArmWord w = some (.op i) := by
  unfold decodeArmWord
  rw [h]

/-- **The decoder on a block followed by a tail**: bytes that `decodeBMBlock` decodes to a
    block, followed by bytes that decode to a program, decode to the block followed by the
    program. -/
theorem decodeArmProg_block (tail : List (BitVec 8)) (is : List ArmInstr)
    (ht : decodeArmProg tail = some is) :
    ∀ (bytes : List (BitVec 8)) (bs : List BMInst), decodeBMBlock bytes = some bs →
      decodeArmProg (bytes ++ tail) = some (bs.map .op ++ is)
  | [], bs, h => by
      cases h
      exact ht
  | b0 :: b1 :: b2 :: b3 :: rest, bs, h => by
      have h1 : (decodeBM64 [b0, b1, b2, b3]).bind
          (fun i => (decodeBMBlock rest).map (fun is => i :: is)) = some bs := h
      obtain ⟨i, hi, h'⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨is', hs, rfl⟩ := Option.map_eq_some_iff.mp h'
      have ih := decodeArmProg_block tail is ht rest is' hs
      rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        decodeArmProg_cons, ih, decodeArmWord_of_decodeBM64 hi]
      rfl
  | [_], _, h => by cases h
  | [_, _], _, h => by cases h
  | [_, _, _], _, h => by cases h

/-- The word of `RET` is outside `decodeBM64`. -/
theorem decodeBM64_encRet : decodeBM64 ArmAbiEncoder.encRet = none := by decide +kernel

/-- The bytes of `RET` decode to `RET`. -/
theorem decodeArmProg_encRet : decodeArmProg ArmAbiEncoder.encRet = some [.ret] := by
  have h : ArmAbiEncoder.encRet
      = [ArmAbiEncoder.encRet[0]!, ArmAbiEncoder.encRet[1]!, ArmAbiEncoder.encRet[2]!,
         ArmAbiEncoder.encRet[3]!] := by decide +kernel
  rw [h]
  simp only [decodeArmProg, decodeArmWord]
  rw [← h, decodeBM64_encRet]
  simp

/-! ## The timing regime and the leakage of an operation -/

/-- The hardware regime of a run. `dit`: `PSTATE.DIT = 1`, so the FEAT_DIT list of
    `CT.ArmMnem.isDIT` applies. `unguaranteed`: no vendor timing guarantee holds. -/
inductive ArmRegime where
  | dit
  | unguaranteed
  deriving DecidableEq, Repr

/-- Whether an instruction with mnemonic `m` makes its data operands observable under the
    regime: the table `CT.ArmMnem.leaksOperands` under `dit`, and every instruction other
    than a control transfer under `unguaranteed`. -/
def ArmRegime.leaksOperands : ArmRegime → ArmMnem → Bool
  | .dit, m => m.leaksOperands
  | .unguaranteed, m => !m.isControl

/-- The table mnemonic of an instruction of the memory-and-branch fragment: `ADD`/`SUB`
    immediate are forms of `ADD`/`SUB`, `CMP` is `SUBS`, and both addressing forms of a load
    or store are `LDR`/`STR`. -/
def bmMnem : BMInst → ArmMnem
  | .alu i => i.mnem
  | .addi .. => .add
  | .subi .. => .sub
  | .cmp .. => .subs
  | .ldr .. => .ldr
  | .str .. => .str
  | .ldrr .. => .ldr
  | .strr .. => .str
  | .cbnz .. => .cbnz
  | .bcond .. => .bcond

/-- No instruction of the memory-and-branch fragment leaks its data operands under
    `PSTATE.DIT = 1`. -/
theorem bmMnem_leaksOperands (i : BMInst) : (bmMnem i).leaksOperands = false := by
  cases i with
  | alu i => exact BInst.mnem_leaksOperands i
  | _ => rfl

/-- The effective address of the memory access of an instruction, `none` for an instruction
    without one. -/
def bmAddr? (s : BMState) : BMInst → Option (BitVec 64)
  | .ldr _ n pimm => some (armAddrI s.regs n pimm)
  | .str _ n pimm => some (armAddrI s.regs n pimm)
  | .ldrr _ n m => some (armAddrR s.regs n m)
  | .strr _ n m => some (armAddrR s.regs n m)
  | _ => none

/-- The data operands of an instruction: the values of the registers it reads and, for a
    load, the value it loads. -/
def bmDataArgs (s : BMState) : BMInst → List Nat
  | .alu i => (binstDstSrcs i).2.map (fun r => (s.regs.get r).toNat)
  | .addi _ a _ => [(s.regs.get a).toNat]
  | .subi _ a _ => [(s.regs.get a).toNat]
  | .cmp a b => [(s.regs.get a).toNat, (s.regs.get b).toNat]
  | .ldr _ n pimm =>
      [(s.regs.get n).toNat, (MachineMem64.read64 s.mem (armAddrI s.regs n pimm)).toNat]
  | .str t n _ => [(s.regs.get t).toNat, (s.regs.get n).toNat]
  | .ldrr _ n m =>
      [(s.regs.get n).toNat, (s.regs.get m).toNat,
       (MachineMem64.read64 s.mem (armAddrR s.regs n m)).toNat]
  | .strr t n m => [(s.regs.get t).toNat, (s.regs.get n).toNat, (s.regs.get m).toNat]
  | .cbnz t _ => [(s.regs.get t).toNat]
  | .bcond .. => []

/-- The address event of an instruction: the effective address of its memory access. -/
def bmAddrLeak (s : BMState) (i : BMInst) : List CTLeak :=
  ((bmAddr? s i).map (fun a => CTLeak.addr "" (a.toNat : Int))).toList

/-- **The leakage of one operation** under the regime `r`: the address of its memory access,
    then its register operands when the regime makes them observable. -/
def armOpLeak (r : ArmRegime) (s : BMState) (i : BMInst) : List CTLeak :=
  bmAddrLeak s i ++
    (if r.leaksOperands (bmMnem i) then [.vtCall ("a64." ++ reprStr (bmMnem i)) [bmDataArgs s i]]
     else [])

/-- **Under `PSTATE.DIT = 1` an operation leaks the address of its memory access and nothing
    else.** -/
theorem armOpLeak_dit (s : BMState) (i : BMInst) : armOpLeak .dit s i = bmAddrLeak s i := by
  simp [armOpLeak, ArmRegime.leaksOperands, bmMnem_leaksOperands]

/-! ## The regime interface and the two channels -/

/-- **The AArch64 timing regimes**: `ArmRegime.dit` is the regime of the specification. -/
instance : TimingRegime ArmRegime ArmMnem where
  leaks := ArmRegime.leaksOperands
  isControl := ArmMnem.isControl
  guaranteed := .dit
  unguaranteed := .unguaranteed
  leaks_unguaranteed := fun _ => rfl
  leaks_le_unguaranteed := fun r m => by cases r <;> cases m <;> decide

/-- **The address channel of an operation** is the effective address of its memory access,
    under every regime. -/
theorem armOpLeak_addrEvents (r : ArmRegime) (s : BMState) (i : BMInst) :
    addrEvents (armOpLeak r s i) = bmAddrLeak s i := by
  unfold armOpLeak
  rw [addrEvents_append]
  have h1 : addrEvents (bmAddrLeak s i) = bmAddrLeak s i := by
    unfold bmAddrLeak
    cases bmAddr? s i <;> rfl
  rw [h1]
  split <;> simp [addrEvents, CTLeak.isAddr]

/-- **A load or store emits its effective address as one event**, followed by its operand
    event when the regime makes the operands of its mnemonic observable. -/
theorem armOpLeak_mem (r : ArmRegime) (s : BMState) (i : BMInst) {a : BitVec 64}
    (h : bmAddr? s i = some a) :
    armOpLeak r s i = .addr "" (a.toNat : Int) ::
      (if r.leaksOperands (bmMnem i) then [.vtCall ("a64." ++ reprStr (bmMnem i)) [bmDataArgs s i]]
       else []) := by
  simp [armOpLeak, bmAddrLeak, h]

/-- **Under `PSTATE.DIT = 1` a load or store emits exactly its effective address.** -/
theorem armOpLeak_dit_mem (s : BMState) (i : BMInst) {a : BitVec 64} (h : bmAddr? s i = some a) :
    armOpLeak .dit s i = [.addr "" (a.toNat : Int)] := by
  rw [armOpLeak_dit]
  simp [bmAddrLeak, h]

/-- **Under `PSTATE.DIT = 1` the data channel of an operation is empty.** -/
theorem armOpLeak_dataEvents_dit (s : BMState) (i : BMInst) :
    dataEvents (armOpLeak .dit s i) = [] := by
  rw [armOpLeak_dit]
  unfold bmAddrLeak
  cases bmAddr? s i <;> rfl

/-- **The record field at a base of the table**: for a base `armMnemOfBase` names, the field
    `leaksOperands` of `armIsa` is the regime `ArmRegime.dit` at the mnemonic. -/
theorem armIsa_leaksOperands_dit {base : String} {m : ArmMnem} (h : armMnemOfBase base = some m) :
    armIsa.leaksOperands base = TimingRegime.leaks ArmRegime.dit m := by
  rw [armIsa_leaksOperands, armLeaksOperands, h]
  rfl

/-- At a base outside `armMnemOfBase` the field `leaksOperands` of `armIsa` is `true`. -/
theorem armIsa_leaksOperands_none {base : String} (h : armMnemOfBase base = none) :
    armIsa.leaksOperands base = true := by
  rw [armIsa_leaksOperands, armLeaksOperands, h]
  rfl

/-! ## The machine -/

/-- An instruction other than a branch. -/
def bmStraight : BMInst → Bool
  | .cbnz .. => false
  | .bcond .. => false
  | _ => true

/-- The action of the decoded instruction at `pc`: a straight-line instruction is an
    operation, `CBNZ` and `B.cond` are branches with the outcome of their test and the target
    index of their displacement, and `RET` is `ret`. -/
def armAct (prog : List ArmInstr) (pc : Nat) (s : BMState) : Option (MAct BMInst) :=
  match prog[pc]? with
  | none => none
  | some .ret => some .ret
  | some (.op (.cbnz t off)) =>
      (wordTarget pc off).map (fun tgt => .branch (decide (s.regs.get t ≠ 0)) tgt)
  | some (.op (.bcond c off)) =>
      (wordTarget pc off).map (fun tgt => .branch (c.holds s.zf s.regs.cf) tgt)
  | some (.op i) => some (.op i)

/-- **The AArch64 machine** under the timing regime `r`: decoded programs `List ArmInstr` of
    `BMInst` operations on `BMState` with the step `evalBMInst`, the decoder `decodeArmProg`
    and the leakage `armOpLeak r`. The fragment has no call. -/
@[reducible] def armMach (r : ArmRegime) : IsaMachine where
  Instr := ArmInstr
  Op := BMInst
  MState := BMState
  exec := evalBMInst
  decode := decodeArmProg
  act := armAct
  callOps := fun _ => []
  retOps := []
  opLeak := armOpLeak r

variable (r : ArmRegime)

theorem armMach_decode : (armMach r).decode = decodeArmProg := rfl

/-- The block fold at `armMach` is `runBMBlock`, by unfolding both definitions. -/
theorem armMach_runBlock : (armMach r).runBlock = runBMBlock := by
  delta IsaMachine.runBlock runBMBlock; rfl

theorem armAct_op {prog : List ArmInstr} {pc : Nat} {i : BMInst} (h : prog[pc]? = some (.op i))
    (hs : bmStraight i = true) (s : BMState) : armAct prog pc s = some (.op i) := by
  unfold armAct
  rw [h]
  cases i <;> first | rfl | cases hs

theorem armAct_ret {prog : List ArmInstr} {pc : Nat} (h : prog[pc]? = some .ret) (s : BMState) :
    armAct prog pc s = some .ret := by
  unfold armAct
  rw [h]

/-- A straight-line block is a straight-line segment of the program that holds it. -/
theorem armMach_opsAt (pre : List ArmInstr) (bs : List BMInst) (post : List ArmInstr)
    (hs : ∀ bi ∈ bs, bmStraight bi = true) :
    (armMach r).OpsAt (pre ++ bs.map .op ++ post) pre.length bs := by
  intro k hk s
  have hget : (pre ++ bs.map ArmInstr.op ++ post)[pre.length + k]? = some (.op bs[k]) := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp [List.getElem?_append_left, hk]
  exact armAct_op hget (hs _ (List.getElem_mem hk)) s

/-- **A straight-line block followed by `RET` halts** in the state `runBMBlock`. -/
theorem armMach_halts_block (bs : List BMInst) (hs : ∀ bi ∈ bs, bmStraight bi = true)
    (b : BMState) : (armMach r).Halts (bs.map .op ++ [.ret]) 0 b (runBMBlock b bs) := by
  have h := IsaMachine.halts_ops (M := armMach r) (prog := bs.map .op ++ [.ret]) bs 0 b
    (by simpa using armMach_opsAt r [] bs [.ret] hs) (armAct_ret (by simp) _)
  rwa [armMach_runBlock] at h

/-- **The leakage of a straight-line block followed by `RET`** is the leakage of the
    block. -/
theorem armMach_runL_block (bs : List BMInst) (hs : ∀ bi ∈ bs, bmStraight bi = true)
    (b : BMState) :
    (armMach r).RunL (fun _ _ => True) (bs.map .op ++ [.ret]) 0 b ((armMach r).blockLeak b bs)
      (runBMBlock b bs) := by
  have h := IsaMachine.runL_ops (M := armMach r) (ok := fun _ _ => True)
    (prog := bs.map .op ++ [.ret]) bs 0 b (by simpa using armMach_opsAt r [] bs [.ret] hs)
    ((armMach r).blockOk_true _ _) (armAct_ret (by simp) _)
  rwa [armMach_runBlock] at h

/-! ## The branches -/

/-- **The `CBNZ` action**: for a register of `armRegs` of related states, the action of
    `CBNZ r, off` is the branch on the `armIsa` condition of `Lcond (.reg r)`. -/
theorem armAct_cbnz {prog : List ArmInstr} {pc : Nat} {t : String} {off : Int} {tgt : Nat}
    (h : prog[pc]? = some (.op (.cbnz t off))) (htgt : wordTarget pc off = some tgt)
    (s : LstateMF) (b : BMState) (hrel : RegRel armRegs s b.regs.get) (ht : t ∈ armRegs) :
    armAct prog pc b = some (.branch (armIsa.condEval s (.reg t)) tgt) := by
  unfold armAct
  rw [h]
  simp only [htgt, Option.map_some, armIsa_condEval, (armCond_cbnz s b hrel ht off).1]

/-- **The `B.NE` action**: when the zero flags agree, the action of `B.NE off` is the branch
    on the `armIsa` condition of `Lcond (.reg "NZ")`. -/
theorem armAct_bcond_ne {prog : List ArmInstr} {pc : Nat} {off : Int} {tgt : Nat}
    (h : prog[pc]? = some (.op (.bcond .ne off))) (htgt : wordTarget pc off = some tgt)
    (s : LstateMF) (b : BMState) (hz : s.zf = b.zf) :
    armAct prog pc b = some (.branch (armIsa.condEval s (.reg "NZ")) tgt) := by
  unfold armAct
  rw [h]
  simp only [htgt, Option.map_some, armIsa_condEval, (armCond_bne s b hz off).1]

/-- **The program counter of `CBNZ`**: from a state whose `pc` is the byte address of the
    index `pc`, the `evalBMInst` step of `CBNZ` ends at the byte address of the index the
    branch action continues at. -/
theorem armAct_cbnz_pc {pc : Nat} {t : String} {off : Int} {tgt : Nat}
    (htgt : wordTarget pc off = some tgt) (b : BMState) (base : BitVec 64)
    (hpc : b.pc = base + BitVec.ofNat 64 (4 * pc)) :
    (evalBMInst b (.cbnz t off)).pc
      = base + BitVec.ofNat 64 (4 * (if b.regs.get t ≠ 0 then tgt else pc + 1)) := by
  simp only [evalBMInst]
  split
  · rw [hpc, wordTarget_ofNat htgt]
  · rw [hpc, BitVec.add_assoc]
    congr 1
    rw [Nat.mul_add, BitVec.ofNat_add]
    rfl

/-- **The program counter of `B.cond`**: from a state whose `pc` is the byte address of the
    index `pc`, the `evalBMInst` step of `B.cond` ends at the byte address of the index the
    branch action continues at. -/
theorem armAct_bcond_pc {pc : Nat} {c : BCond} {off : Int} {tgt : Nat}
    (htgt : wordTarget pc off = some tgt) (b : BMState) (base : BitVec 64)
    (hpc : b.pc = base + BitVec.ofNat 64 (4 * pc)) :
    (evalBMInst b (.bcond c off)).pc
      = base + BitVec.ofNat 64 (4 * (if c.holds b.zf b.regs.cf then tgt else pc + 1)) := by
  simp only [evalBMInst]
  split
  · rw [hpc, wordTarget_ofNat htgt]
  · rw [hpc, BitVec.add_assoc]
    congr 1
    rw [Nat.mul_add, BitVec.ofNat_add]
    rfl

/-! ## The decode-and-step simulation of `armSelX` -/

/-- The memory selection selects straight-line instructions. -/
theorem armSelM_straight {arrs : List String} {sz : String → Nat} {i : LinstrRM} {bi : BMInst}
    (h : armSelM arrs sz i = some bi) : bmStraight bi = true := by
  rcases armSelM_inv h with ⟨_, _, _, _, -, -, -, -, -, -, rfl⟩
    | ⟨_, _, _, _, -, -, -, -, -, rfl⟩
    | ⟨_, _, _, _, -, -, -, -, -, hbop⟩
    | ⟨_, _, _, _, _, -, -, -, rfl⟩
  · rfl
  · rfl
  · rcases hbop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · rfl

/-- The selection `armSelX` selects straight-line instructions. -/
theorem armSelX_straight {arrs : List String} {sz : String → Nat} {cells : List (String × Nat)}
    {i : LinstrRM} {bi : BMInst} (h : armSelX arrs sz cells i = some bi) :
    bmStraight bi = true := by
  unfold armSelX at h
  split at h
  · rename_i bi' hc
    cases h
    rcases armSelC_inv hc with ⟨_, _, _, _, -, -, -, rfl⟩
      | ⟨_, _, _, -, -, -, -, -, -, -, -, rfl⟩ | ⟨_, _, _, -, -, -, -, -, -, rfl⟩ <;> rfl
  · split at h
    · exact armSelM_straight h
    · cases h

/-- The instructions of a selected block are straight-line. -/
theorem armSelX_straight_block {arrs : List String} {sz : String → Nat}
    {cells : List (String × Nat)} :
    ∀ (is : List LinstrRM) (bs : List BMInst), is.mapM (armSelX arrs sz cells) = some bs →
      ∀ bi ∈ bs, bmStraight bi = true
  | [], bs, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | i :: is, bs, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨bi, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact armSelX_straight hi
      · exact armSelX_straight_block is bs' hs x hx

/-- **One machine step simulates one `armIsa` step.** For an instruction `i` that `armSelX`
    maps to `bi`: the bytes of `bi` decode to it; at an index of a decoded program that holds
    `bi`, the machine step runs `evalBMInst` and advances; and from states related on
    `armRegs`, on the arrays, on the word cells and on the flags, with the layouts and the
    index bound, the `armIsa` step of `i` succeeds in a state related to the machine state
    after the step in the same four relations. -/
theorem arm_mach_step (P : LprogM) {arrs : List String} {sz : String → Nat}
    {cells : List (String × Nat)} {i : LinstrRM} {bi : BMInst}
    (h : armSelX arrs sz cells i = some bi) (prog : List ArmInstr) (pc : Nat)
    (hpc : prog[pc]? = some (.op bi)) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel arrs sz s b)
    (hword : ArmWordRel cells s b) (hflag : ArmFlagRel s b)
    (hsep : ArmArrsSep arrs sz b.regs.get) (hcs : ArmCellsSep arrs sz cells b.regs.get)
    (hbd : IdxBound sz i b.regs.get) :
    decodeArmWord (encodeBMInst armAlloc bi) = some (.op bi) ∧
    ∃ b', (armMach r).mstep prog pc b = some (.go (pc + 1) b') ∧ b' = evalBMInst b bi ∧
      ∃ s', armIsa.step P i s = some s' ∧ RegRel armRegs s' b'.regs.get
        ∧ ArmMemRel arrs sz s' b' ∧ ArmWordRel cells s' b' ∧ ArmFlagRel s' b'
        ∧ FrameX 1 s s' := by
  refine ⟨by simp only [decodeArmWord, armSelX_decode h], _, ?_, rfl, ?_⟩
  · simp only [IsaMachine.mstep, armAct_op hpc (armSelX_straight h) b]
  · obtain ⟨s', hs', h1, h2, h3, h4, -, -, h5⟩ :=
      armSelX_step P h s b hrel hmem hword hflag hsep hcs hbd
    exact ⟨s', hs', h1, h2, h3, h4, h5⟩

/-- **The decode-and-step simulation of the AArch64 fragment.** For a block `is` that
    `armSelX arrs sz cells` maps to `bs`: the bytes `encodeBMBlock armAlloc bs` followed by
    the bytes of `RET` decode at `armMach r` to the program `bs` followed by `RET`; and from
    an `LstateMF` related to a machine state `b` on `armRegs`, on the arrays, on the word
    cells and on the flags, with the layouts and in-range indices along the run, the `armIsa`
    run of `is` succeeds, the decoded program halts from index 0 in a state `b'` with the
    leakage of the block, and the two final states are related in the same four relations. -/
theorem arm_mach_x (P : LprogM) (arrs : List String) (sz : String → Nat)
    (cells : List (String × Nat)) (is : List LinstrRM) (bs : List BMInst)
    (h : is.mapM (armSelX arrs sz cells) = some bs) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel arrs sz s b)
    (hword : ArmWordRel cells s b) (hflag : ArmFlagRel s b)
    (hsep : ArmArrsSep arrs sz b.regs.get) (hcs : ArmCellsSep arrs sz cells b.regs.get)
    (hbd : BoundsOKX arrs sz cells is b) :
    (armMach r).decode (encodeBMBlock armAlloc bs ++ ArmAbiEncoder.encRet)
        = some (bs.map .op ++ [.ret]) ∧
    ∃ s' b', armIsa.runL P is s = some s'
      ∧ (armMach r).Halts (bs.map .op ++ [.ret]) 0 b b'
      ∧ (armMach r).RunL (fun _ _ => True) (bs.map .op ++ [.ret]) 0 b
          ((armMach r).blockLeak b bs) b'
      ∧ RegRel armRegs s' b'.regs.get ∧ ArmMemRel arrs sz s' b' ∧ ArmWordRel cells s' b'
      ∧ ArmFlagRel s' b' ∧ FrameX is.length s s' := by
  obtain ⟨hdec, s', hs', h1, h2, h3, h4, h5⟩ :=
    arm_asm_x P arrs sz cells is bs h s b hrel hmem hword hflag hsep hcs hbd
  have hst := armSelX_straight_block is bs h
  exact ⟨decodeArmProg_block _ _ decodeArmProg_encRet _ _ hdec, s', runBMBlock b bs, hs',
    armMach_halts_block r bs hst b, armMach_runL_block r bs hst b, h1, h2, h3, h4, h5⟩

/-! ## The `mpn_and_n` body at the machine -/

/-- The instructions of the `mpn_and_n` body are straight-line. -/
theorem armAndCode_straight : ∀ bi ∈ armAndCode, bmStraight bi = true := by
  simp [armAndCode, bmStraight]

/-- **The `mpn_and_n` body at `armMach`.** The bytes of `armAndCode` followed by the bytes of
    `RET` decode to `armAndCode` followed by `RET`; and from an `LstateMF` related to a machine
    state on `armRegs` and on the arrays `x0`, `x1`, `x3` of `n` limbs, laid out separately,
    with the index `x4` below `n`, the `armIsa` run of the body succeeds, the decoded program
    halts from index 0 with the leakage of the block, and the final states are related. -/
theorem arm_and_mach (P : LprogM) (n : Nat) (s : LstateMF) (b : BMState)
    (hrel : RegRel armRegs s b.regs.get) (hmem : ArmMemRel armAndArrs (fun _ => n) s b)
    (hsep : ArmArrsSep armAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "x4").toNat < n) :
    (armMach r).decode (encodeBMBlock armAlloc armAndCode ++ ArmAbiEncoder.encRet)
        = some (armAndCode.map .op ++ [.ret]) ∧
    ∃ s' b', armIsa.runL P (armAndBody n) s = some s'
      ∧ (armMach r).Halts (armAndCode.map .op ++ [.ret]) 0 b b'
      ∧ (armMach r).RunL (fun _ _ => True) (armAndCode.map .op ++ [.ret]) 0 b
          ((armMach r).blockLeak b armAndCode) b'
      ∧ RegRel armRegs s' b'.regs.get ∧ ArmMemRel armAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s' := by
  obtain ⟨hdec, s', hs', h1, h2, h3⟩ := arm_and_body P n s b hrel hmem hsep hidx
  have hd := decodeArmProg_block ArmAbiEncoder.encRet [.ret] decodeArmProg_encRet
    (encodeBMBlock armAlloc armAndCode) armAndCode hdec
  have hh := armMach_halts_block r armAndCode armAndCode_straight b
  have hl := armMach_runL_block r armAndCode armAndCode_straight b
  exact ⟨(congrFun (armMach_decode r) _).trans hd, s', runBMBlock b armAndCode, hs', hh, hl,
    h1, h2, h3⟩

/-- **The leakage of the `mpn_and_n` body under `PSTATE.DIT = 1`**: the addresses of the two
    limb loads and of the limb store, which depend on the array bases `x1`, `x0`, `x3` and
    the index `x4` only. -/
theorem armAndCode_leak_dit (b : BMState) :
    (armMach .dit).blockLeak b armAndCode =
      [ .addr "" ((b.regs.get "x1" + (b.regs.get "x4" <<< 3)).toNat : Int)
      , .addr "" ((b.regs.get "x0" + (b.regs.get "x4" <<< 3)).toNat : Int)
      , .addr "" ((b.regs.get "x3" + (b.regs.get "x4" <<< 3)).toNat : Int) ] := by
  simp [armAndCode, IsaMachine.blockLeak, armOpLeak_dit, bmAddrLeak, bmAddr?, armAddrR,
    evalBMInst, evalBInst, BState.set]

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmMach
