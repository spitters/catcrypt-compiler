/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvElfObject
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachineBlock
public import CatCrypt.Crypto.SecureCompilation.CT.IsaRegime

@[expose] public section

set_option autoImplicit false

/-!
# The RV64 machine level of the instruction-set record

`rvMach r` is the `LprogIsa.IsaMachine` of RV64 under the timing regime `r`. A decoded
program is a list of `RvInstr`: an instruction `RMInst64` of the memory-and-branch fragment,
or `ret` (`JALR zero, 0(ra)`). The state is `RMState64`, the effect of an operation is
`evalRMInst64`, and the decoder `decodeRvProg` reads 4-byte words with
`SailRiscvDecoder64.riscvDecodeM64` and reads the word `RiscvElfObject.encRet` as `ret`. The
action `rvAct` of a straight-line instruction is the instruction; `BNE` is a branch whose
outcome is the test of `evalRMInst64` and whose target is the index `LprogIsa.wordTarget` of
its byte displacement.

The index of a run of `IsaMachine` is the program counter. The field `pc` of `RMState64` is
written by `evalRMInst64` and read by no operation and no action; `rvAct_bne_pc` states
that, from a state whose `pc` is the byte address of the index, the `pc` after the
`evalRMInst64` step of `BNE` is the byte address of the index the action continues at.

The leakage `rvOpLeak r` of an operation is the effective address of its memory access, as an
`addr` event with the empty region and the address as offset, followed by its data operands
when the regime `r` makes them observable. The two channels of a load or store are separate
events: the address channel is the `addr` event, emitted under every regime
(`rvOpLeak_addrEvents`), and the data channel is the operand event, which carries the value
loaded or stored.

There are three regimes. `RvRegime.zkt` is an implementation of Zkt, the regime the
specification gives; its table `CT.RvMnem.leaksOperands` classes `LD` and `SD` as variable
time, Zkt excluding loads and stores, so a load or store leaks the value it transfers
(`rvOpLeak_zkt_ld`, `rvOpLeak_zkt_sd`). `RvRegime.zktMemData` is Zkt with the assumption that
the latency of a load or store is independent of the data value transferred, which the
ratified text does not state; under it an operation leaks the address of its memory access
and nothing else. Under `RvRegime.unguaranteed` every straight-line instruction leaks its
operands. `RvRegime` is a `CT.TimingRegime` over `CT.RvMnem`, with `zkt` the regime of the
specification. The operand event is `CTLeak.vtCall` named by the mnemonic, the event
`CTLeak.vt` being indexed by the x86 mnemonic table.

## Main definitions

* `RvInstr`, `decodeRvWord`, `decodeRvProg`: the decoded instructions and the decoder.
* `RvRegime`, `RvRegime.leaksOperands`, `RvRegime.leaksMnem`, `rmMnem`, `rmZktLeaks`,
  `rvOpLeak`: the timing regime and the leakage of one operation.
* `rmStraight`, `rvAct`, `rvMach`: the straight-line instructions, the action and the
  machine.

## Main results

* `decodeRvProg_block`, `decodeRvProg_encRet`: the decoder on a block followed by `ret`.
* `rvOpLeak_zktMemData`, `rvOpLeak_zkt_sd`, `rvOpLeak_zkt_ld`, `rvOpLeak_zkt_of_not_mem`: under
  `RvRegime.zktMemData` an operation leaks the address of its memory access and nothing else;
  under `RvRegime.zkt` a load or store also leaks its operands, and any other instruction
  has no event.
* `rvOpLeak_addrEvents`, `rvOpLeak_mem`, `rvOpLeak_zktMemData_mem`,
  `rvOpLeak_dataEvents_zktMemData`, `rvOpLeak_dataEvents_zkt_mem`: the address channel of an
  operation is the effective address of its memory access under every regime; the data
  channel is empty under `RvRegime.zktMemData` and is the operand event of a load or store
  under `RvRegime.zkt`.
* `rvIsa_leaksOperands_zkt`, `rvIsa_leaksOperands_none`: the field `leaksOperands` of `rvIsa`
  is the table under `RvRegime.zkt` at the mnemonic of a base of `rvMnemOfBase`, and `true`
  at any other base except the keep marker.
* `rvMach_halts_block`, `rvMach_runL_block`: a straight-line block followed by `ret` halts in
  the state `runRMBlock64`, with the leakage of the block.
* `rvAct_bne`: the action of `BNE r, zero` takes the `rvIsa` branch condition of a related
  state.
* `rvSelM_straight`, `rv_mach_step`, `rv_mach_mem`: the decode-and-step simulation of the
  selection `rvSelM`. The bytes of the selected block followed by `ret` decode to the
  selected program, the machine steps of the selection of one instruction simulate one
  `rvIsa` step, and the machine run halts in a state related to the `rvIsa` run.
* `rv_and_mach`, `rvAndCode_leak_zktMemData`: the `mpn_and_n` body at `rvMach`, and its
  leakage under `RvRegime.zktMemData`, the three addresses of its limb accesses.
-/

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.SailRiscvDecoder64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
open CatCrypt.Crypto.SecureCompilation.MachineMem64
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## Decoded programs -/

/-- A decoded RV64 instruction: an instruction of the memory-and-branch fragment, or `ret`. -/
inductive RvInstr where
  /-- An instruction of `RMInst64`. -/
  | op (i : RMInst64)
  /-- `ret` (`JALR zero, 0(ra)`). -/
  | ret
  deriving DecidableEq, Repr

/-- Decode one 32-bit word: an instruction of `riscvDecodeM64`, and otherwise `ret` on the
    word `RiscvElfObject.encRet`. -/
def decodeRvWord (w : BitVec 32) : Option RvInstr :=
  match riscvDecodeM64 w with
  | some i => some (.op i)
  | none => if w = RiscvElfObject.encRet then some .ret else none

/-- A word `riscvDecodeM64` decodes is decoded by `decodeRvWord` as the same instruction. -/
theorem decodeRvWord_of_decodeM64 {w : BitVec 32} {i : RMInst64}
    (h : riscvDecodeM64 w = some i) : decodeRvWord w = some (.op i) := by
  unfold decodeRvWord
  rw [h]

/-- Decode a byte stream of 4-byte RV64 words with `decodeRvWord`; `none` on a word outside
    the decoder or a trailing partial word. -/
def decodeRvProg : List (BitVec 8) → Option (List RvInstr)
  | [] => some []
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (decodeRvWord (leWord32 b0 b1 b2 b3)).bind
        (fun i => (decodeRvProg rest).map (fun is => i :: is))
  | _ => none

/-- A four-byte word followed by a stream decodes as the word followed by the stream. -/
theorem decodeRvProg_cons (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    decodeRvProg (b0 :: b1 :: b2 :: b3 :: rest) =
      (decodeRvWord (leWord32 b0 b1 b2 b3)).bind
        (fun i => (decodeRvProg rest).map (fun is => i :: is)) := rfl

/-- **The decoder on a block followed by a tail**: bytes that `decodeRMBlock64` decodes to a
    block, followed by bytes that decode to a program, decode to the block followed by the
    program. -/
theorem decodeRvProg_block (tail : List (BitVec 8)) (is : List RvInstr)
    (ht : decodeRvProg tail = some is) :
    ∀ (bytes : List (BitVec 8)) (bs : List RMInst64), decodeRMBlock64 bytes = some bs →
      decodeRvProg (bytes ++ tail) = some (bs.map .op ++ is)
  | [], bs, h => by
      cases h
      exact ht
  | b0 :: b1 :: b2 :: b3 :: rest, bs, h => by
      have h1 : (riscvDecodeM64 (leWord32 b0 b1 b2 b3)).bind
          (fun i => (decodeRMBlock64 rest).map (fun is => i :: is)) = some bs := h
      obtain ⟨i, hi, h'⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨is', hs, rfl⟩ := Option.map_eq_some_iff.mp h'
      have ih := decodeRvProg_block tail is ht rest is' hs
      rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        decodeRvProg_cons, ih, decodeRvWord_of_decodeM64 hi]
      rfl
  | [_], _, h => by cases h
  | [_, _], _, h => by cases h
  | [_, _, _], _, h => by cases h

/-- The word of `ret` is outside `riscvDecodeM64`. -/
theorem riscvDecodeM64_encRet : riscvDecodeM64 RiscvElfObject.encRet = none := by
  decide +kernel

/-- The bytes of `ret` decode to `ret`. -/
theorem decodeRvProg_encRet : decodeRvProg (wordLE RiscvElfObject.encRet) = some [.ret] := by
  have hw : ∀ w : BitVec 32, decodeRvProg (wordLE w) = (decodeRvWord w).map (fun i => [i]) := by
    intro w
    have h := decodeRMBlock64_wordLE w []
    have hle : leWord32 (BitVec.ofNat 8 (w.toNat &&& 0xff))
        (BitVec.ofNat 8 ((w.toNat >>> 8) &&& 0xff)) (BitVec.ofNat 8 ((w.toNat >>> 16) &&& 0xff))
        (BitVec.ofNat 8 ((w.toNat >>> 24) &&& 0xff)) = w := by
      apply BitVec.eq_of_toNat_eq
      have hlt := w.isLt
      simp only [leWord32, show (0xff : Nat) = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    simp only [wordLE, List.map_cons, List.map_nil, decodeRvProg, hle]
    cases decodeRvWord w <;> rfl
  rw [hw, decodeRvWord, riscvDecodeM64_encRet]
  simp

/-! ## The timing regime and the leakage of an operation -/

/-- The hardware regime of a run.

    * `zkt`: an implementation of Zkt, so the table `CT.RvMnem.isZkt` applies. This is the
      regime the specification gives (RISC-V Cryptography Extensions 1.0.1, Zkt).
    * `zktMemData`: Zkt, with the assumption that the latency of a load or store is
      independent of the data value transferred. The assumption is not part of the ratified
      text: section "Scope and Goal" of Zkt states "Loads, stores, conditional branches are
      excluded". A statement under `zktMemData` holds on an implementation for which the
      assumption is established separately.
    * `unguaranteed`: no vendor timing guarantee holds. -/
inductive RvRegime where
  | zkt
  | zktMemData
  | unguaranteed
  deriving DecidableEq, Repr

/-- An instruction other than a branch. -/
def rmStraight : RMInst64 → Bool
  | .bne .. => false
  | _ => true

/-- The table mnemonic of an instruction of the memory-and-branch fragment. -/
def rmMnem : RMInst64 → RvMnem
  | .alu i => i.mnem
  | .addi .. => .addi
  | .ld .. => .ld
  | .sd .. => .sd
  | .bne .. => .bne

/-- Whether an instruction of the memory-and-branch fragment makes its data operands
    observable on an implementation of Zkt: the table `CT.RvMnem.leaksOperands` at the
    mnemonic. -/
def rmZktLeaks : RMInst64 → Bool
  | .alu i => i.mnem.leaksOperands
  | .addi .. => RvMnem.addi.leaksOperands
  | .ld .. => RvMnem.ld.leaksOperands
  | .sd .. => RvMnem.sd.leaksOperands
  | .bne .. => RvMnem.bne.leaksOperands

/-- Whether an instruction makes its data operands observable under the regime: the Zkt
    table under `zkt`, no instruction of the fragment under `zktMemData`, and every
    straight-line instruction under `unguaranteed`. -/
def RvRegime.leaksOperands : RvRegime → RMInst64 → Bool
  | .zkt, i => rmZktLeaks i
  | .zktMemData, _ => false
  | .unguaranteed, i => rmStraight i

/-- Whether an instruction with mnemonic `m` makes its data operands observable under the
    regime: the Zkt table under `zkt`; the Zkt table outside the loads and stores under
    `zktMemData`; and every instruction other than a control transfer under `unguaranteed`. -/
def RvRegime.leaksMnem : RvRegime → RvMnem → Bool
  | .zkt, m => m.leaksOperands
  | .zktMemData, m => m.leaksOperands && !m.isMem
  | .unguaranteed, m => !m.isControl

/-- The regime of an instruction is the regime of its mnemonic. -/
theorem RvRegime.leaksOperands_eq (r : RvRegime) (i : RMInst64) :
    r.leaksOperands i = r.leaksMnem (rmMnem i) := by
  cases r <;> cases i with
  | alu j => first | exact (RInst64.mnem_leaksOperands j).symm | rfl | (cases j <;> rfl)
  | _ => rfl

/-- **The RV64 timing regimes**: `RvRegime.zkt` is the regime of the specification. -/
instance : TimingRegime RvRegime RvMnem where
  leaks := RvRegime.leaksMnem
  isControl := RvMnem.isControl
  guaranteed := .zkt
  unguaranteed := .unguaranteed
  leaks_unguaranteed := fun _ => rfl
  leaks_le_unguaranteed := fun r m => by cases r <;> cases m <;> decide

/-- **The assumption of `zktMemData` concerns the loads and stores only**: the regimes `zkt`
    and `zktMemData` agree at every mnemonic without a memory access. -/
theorem RvRegime.leaksMnem_zktMemData_of_not_mem {m : RvMnem} (h : m.isMem = false) :
    RvRegime.zktMemData.leaksMnem m = RvRegime.zkt.leaksMnem m := by
  simp [RvRegime.leaksMnem, h]

/-- Outside the loads and stores, the regimes `zkt` and `zktMemData` agree on the fragment: no
    register instruction, `ADDI` or `BNE` leaks its operands on an implementation of Zkt. -/
theorem rmZktLeaks_eq_false (i : RMInst64) (hld : ∀ d b o, i ≠ .ld d b o)
    (hsd : ∀ s b o, i ≠ .sd s b o) : rmZktLeaks i = false := by
  cases i with
  | alu j => exact RInst64.mnem_leaksOperands j
  | addi => rfl
  | ld d b o => exact absurd rfl (hld d b o)
  | sd s b o => exact absurd rfl (hsd s b o)
  | bne => rfl

/-- The name of the mnemonic of an instruction. -/
def rmName : RMInst64 → String
  | .alu i => reprStr i.mnem
  | .addi .. => "addi"
  | .ld .. => "ld"
  | .sd .. => "sd"
  | .bne .. => "bne"

/-- The effective address of the memory access of an instruction, `none` for an instruction
    without one. -/
def rmAddr? (s : RMState64) : RMInst64 → Option (BitVec 64)
  | .ld _ base off => some (rvAddr s.regs base off)
  | .sd _ base off => some (rvAddr s.regs base off)
  | _ => none

/-- The data operands of an instruction: the values of the registers it reads and, for a
    load, the value it loads. -/
def rmDataArgs (s : RMState64) : RMInst64 → List Nat
  | .alu i => (rinst64DstSrcs i).2.map (fun r => (s.regs.get r).toNat)
  | .addi _ a _ => [(s.regs.get a).toNat]
  | .ld _ base off =>
      [(s.regs.get base).toNat, (MachineMem64.read64 s.mem (rvAddr s.regs base off)).toNat]
  | .sd src base _ => [(s.regs.get src).toNat, (s.regs.get base).toNat]
  | .bne a b _ => [(s.regs.get a).toNat, (s.regs.get b).toNat]

/-- The address event of an instruction: the effective address of its memory access. -/
def rmAddrLeak (s : RMState64) (i : RMInst64) : List CTLeak :=
  ((rmAddr? s i).map (fun a => CTLeak.addr "" (a.toNat : Int))).toList

/-- **The leakage of one operation** under the regime `r`: the address of its memory access,
    then its register operands when the regime makes them observable. -/
def rvOpLeak (r : RvRegime) (s : RMState64) (i : RMInst64) : List CTLeak :=
  rmAddrLeak s i ++
    (if r.leaksOperands i then [.vtCall ("rv64." ++ rmName i) [rmDataArgs s i]] else [])

/-- **Under `RvRegime.zktMemData` an operation leaks the address of its memory access and
    nothing else.** -/
theorem rvOpLeak_zktMemData (s : RMState64) (i : RMInst64) :
    rvOpLeak .zktMemData s i = rmAddrLeak s i := by
  simp [rvOpLeak, RvRegime.leaksOperands]

/-- **Under `RvRegime.zkt` a store leaks its address and its operands**, the stored value
    among them. -/
theorem rvOpLeak_zkt_sd (s : RMState64) (src base : String) (off : Int) :
    rvOpLeak .zkt s (.sd src base off) =
      [ .addr "" ((rvAddr s.regs base off).toNat : Int)
      , .vtCall "rv64.sd" [[(s.regs.get src).toNat, (s.regs.get base).toNat]] ] := by
  simp [rvOpLeak, RvRegime.leaksOperands, rmZktLeaks, RvMnem.leaksOperands, RvMnem.isZkt,
    RvMnem.isControl, rmAddrLeak, rmAddr?, rmName, rmDataArgs]

/-- **Under `RvRegime.zkt` a load leaks its address and its operands**, the loaded value
    among them. -/
theorem rvOpLeak_zkt_ld (s : RMState64) (d base : String) (off : Int) :
    rvOpLeak .zkt s (.ld d base off) =
      [ .addr "" ((rvAddr s.regs base off).toNat : Int)
      , .vtCall "rv64.ld" [[(s.regs.get base).toNat,
          (MachineMem64.read64 s.mem (rvAddr s.regs base off)).toNat]] ] := by
  simp [rvOpLeak, RvRegime.leaksOperands, rmZktLeaks, RvMnem.leaksOperands, RvMnem.isZkt,
    RvMnem.isControl, rmAddrLeak, rmAddr?, rmName, rmDataArgs]

/-- **Under `RvRegime.zkt` an instruction other than a load or store has no event.** -/
theorem rvOpLeak_zkt_of_not_mem (s : RMState64) (i : RMInst64) (hld : ∀ d b o, i ≠ .ld d b o)
    (hsd : ∀ x b o, i ≠ .sd x b o) : rvOpLeak .zkt s i = [] := by
  have h : rmAddr? s i = none := by
    cases i with
    | ld d b o => exact absurd rfl (hld d b o)
    | sd x b o => exact absurd rfl (hsd x b o)
    | _ => rfl
  simp [rvOpLeak, RvRegime.leaksOperands, rmZktLeaks_eq_false i hld hsd, rmAddrLeak, h]

/-! ## The address channel and the data channel -/

/-- **The address channel of an operation** is the effective address of its memory access,
    under every regime. -/
theorem rvOpLeak_addrEvents (r : RvRegime) (s : RMState64) (i : RMInst64) :
    addrEvents (rvOpLeak r s i) = rmAddrLeak s i := by
  unfold rvOpLeak
  rw [addrEvents_append]
  have h1 : addrEvents (rmAddrLeak s i) = rmAddrLeak s i := by
    unfold rmAddrLeak
    cases rmAddr? s i <;> rfl
  rw [h1]
  split <;> simp [addrEvents, CTLeak.isAddr]

/-- **A load or store emits its effective address as one event**, followed by its operand
    event when the regime makes its operands observable. -/
theorem rvOpLeak_mem (r : RvRegime) (s : RMState64) (i : RMInst64) {a : BitVec 64}
    (h : rmAddr? s i = some a) :
    rvOpLeak r s i = .addr "" (a.toNat : Int) ::
      (if r.leaksOperands i then [.vtCall ("rv64." ++ rmName i) [rmDataArgs s i]] else []) := by
  simp [rvOpLeak, rmAddrLeak, h]

/-- **Under `RvRegime.zktMemData` a load or store emits exactly its effective address.** -/
theorem rvOpLeak_zktMemData_mem (s : RMState64) (i : RMInst64) {a : BitVec 64}
    (h : rmAddr? s i = some a) : rvOpLeak .zktMemData s i = [.addr "" (a.toNat : Int)] := by
  rw [rvOpLeak_zktMemData]
  simp [rmAddrLeak, h]

/-- **Under `RvRegime.zktMemData` the data channel of an operation is empty.** -/
theorem rvOpLeak_dataEvents_zktMemData (s : RMState64) (i : RMInst64) :
    dataEvents (rvOpLeak .zktMemData s i) = [] := by
  rw [rvOpLeak_zktMemData]
  unfold rmAddrLeak
  cases rmAddr? s i <;> rfl

/-- **Under `RvRegime.zkt` the data channel of a load or store is its operand event**: the
    specification gives no guarantee for the value transferred. -/
theorem rvOpLeak_dataEvents_zkt_mem (s : RMState64) (i : RMInst64) {a : BitVec 64}
    (h : rmAddr? s i = some a) :
    dataEvents (rvOpLeak .zkt s i) = [.vtCall ("rv64." ++ rmName i) [rmDataArgs s i]] := by
  cases i with
  | ld d b o => simp [rvOpLeak_zkt_ld, dataEvents, CTLeak.isAddr, rmName, rmDataArgs]
  | sd x b o => simp [rvOpLeak_zkt_sd, dataEvents, CTLeak.isAddr, rmName, rmDataArgs]
  | _ => cases h

/-! ## The record field -/

/-- **The record field at a base of the table**: for a base `rvMnemOfBase` names, the field
    `leaksOperands` of `rvIsa` is the regime `RvRegime.zkt` at the mnemonic. -/
theorem rvIsa_leaksOperands_zkt {base : String} {m : RvMnem} (h : rvMnemOfBase base = some m) :
    rvIsa.leaksOperands base = TimingRegime.leaks RvRegime.zkt m := by
  have hk : (base != "KEEP") = true := by
    cases hb : base != "KEEP" with
    | true => rfl
    | false =>
        have : base = "KEEP" := by simpa using hb
        subst this
        simp [rvMnemOfBase] at h
  rw [rvIsa_leaksOperands, rvLeaksOperands, h, hk]
  rfl

/-- At a base outside `rvMnemOfBase` other than the keep marker, the field `leaksOperands` of
    `rvIsa` is `true`. -/
theorem rvIsa_leaksOperands_none {base : String} (h : rvMnemOfBase base = none)
    (hk : base ≠ "KEEP") : rvIsa.leaksOperands base = true := by
  rw [rvIsa_leaksOperands, rvLeaksOperands, h]
  simpa using hk

/-! ## The machine -/

/-- The action of the decoded instruction at `pc`: a straight-line instruction is an
    operation, `BNE` is a branch with the outcome of its test and the target index of its
    displacement, and `ret` is `ret`. -/
def rvAct (prog : List RvInstr) (pc : Nat) (s : RMState64) : Option (MAct RMInst64) :=
  match prog[pc]? with
  | none => none
  | some .ret => some .ret
  | some (.op (.bne a c off)) =>
      (wordTarget pc off).map
        (fun tgt => .branch (decide (s.regs.get a ≠ s.regs.get c)) tgt)
  | some (.op i) => some (.op i)

/-- **The RV64 machine** under the timing regime `r`: decoded programs `List RvInstr` of
    `RMInst64` operations on `RMState64` with the step `evalRMInst64`, the decoder
    `decodeRvProg` and the leakage `rvOpLeak r`. The fragment has no call. -/
@[reducible] def rvMach (r : RvRegime) : IsaMachine where
  Instr := RvInstr
  Op := RMInst64
  MState := RMState64
  exec := evalRMInst64
  decode := decodeRvProg
  act := rvAct
  callOps := fun _ => []
  retOps := []
  opLeak := rvOpLeak r

variable (r : RvRegime)

theorem rvMach_decode : (rvMach r).decode = decodeRvProg := rfl

/-- The block fold at `rvMach` is `runRMBlock64`, by unfolding both definitions. -/
theorem rvMach_runBlock : (rvMach r).runBlock = runRMBlock64 := by
  delta IsaMachine.runBlock runRMBlock64; rfl

theorem rvAct_op {prog : List RvInstr} {pc : Nat} {i : RMInst64} (h : prog[pc]? = some (.op i))
    (hs : rmStraight i = true) (s : RMState64) : rvAct prog pc s = some (.op i) := by
  unfold rvAct
  rw [h]
  cases i <;> first | rfl | cases hs

theorem rvAct_ret {prog : List RvInstr} {pc : Nat} (h : prog[pc]? = some .ret) (s : RMState64) :
    rvAct prog pc s = some .ret := by
  unfold rvAct
  rw [h]

/-- A straight-line block is a straight-line segment of the program that holds it. -/
theorem rvMach_opsAt (pre : List RvInstr) (bs : List RMInst64) (post : List RvInstr)
    (hs : ∀ bi ∈ bs, rmStraight bi = true) :
    (rvMach r).OpsAt (pre ++ bs.map .op ++ post) pre.length bs := by
  intro k hk s
  have hget : (pre ++ bs.map RvInstr.op ++ post)[pre.length + k]? = some (.op bs[k]) := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp [List.getElem?_append_left, hk]
  exact rvAct_op hget (hs _ (List.getElem_mem hk)) s

/-- **A straight-line block followed by `ret` halts** in the state `runRMBlock64`. -/
theorem rvMach_halts_block (bs : List RMInst64) (hs : ∀ bi ∈ bs, rmStraight bi = true)
    (b : RMState64) : (rvMach r).Halts (bs.map .op ++ [.ret]) 0 b (runRMBlock64 b bs) := by
  have h := IsaMachine.halts_ops (M := rvMach r) (prog := bs.map .op ++ [.ret]) bs 0 b
    (by simpa using rvMach_opsAt r [] bs [.ret] hs) (rvAct_ret (by simp) _)
  rwa [rvMach_runBlock] at h

/-- **The leakage of a straight-line block followed by `ret`** is the leakage of the
    block. -/
theorem rvMach_runL_block (bs : List RMInst64) (hs : ∀ bi ∈ bs, rmStraight bi = true)
    (b : RMState64) :
    (rvMach r).RunL (fun _ _ => True) (bs.map .op ++ [.ret]) 0 b ((rvMach r).blockLeak b bs)
      (runRMBlock64 b bs) := by
  have h := IsaMachine.runL_ops (M := rvMach r) (ok := fun _ _ => True)
    (prog := bs.map .op ++ [.ret]) bs 0 b (by simpa using rvMach_opsAt r [] bs [.ret] hs)
    ((rvMach r).blockOk_true _ _) (rvAct_ret (by simp) _)
  rwa [rvMach_runBlock] at h

/-! ## The branch -/

/-- **The `BNE` action**: for a related register `t`, the action of `BNE t, zero, off` is the
    branch on the `rvIsa` condition of `Lcond (.reg t)`. -/
theorem rvAct_bne {prog : List RvInstr} {pc : Nat} {t : String} {off : Int} {tgt : Nat}
    (h : prog[pc]? = some (.op (.bne t "zero" off))) (htgt : wordTarget pc off = some tgt)
    {regs : List String} (s : LstateMF) (b : RMState64) (hrel : RegRel regs s b.regs.get)
    (ht : t ∈ regs) :
    rvAct prog pc b = some (.branch (rvIsa.condEval s (.reg t)) tgt) := by
  unfold rvAct
  rw [h]
  simp only [htgt, Option.map_some, rvIsa_condEval, (rvCond_bne hrel ht off).1]

/-- **The program counter of `BNE`**: from a state whose `pc` is the byte address of the
    index `pc`, the `evalRMInst64` step of `BNE` ends at the byte address of the index the
    branch action continues at. -/
theorem rvAct_bne_pc {pc : Nat} {a c : String} {off : Int} {tgt : Nat}
    (htgt : wordTarget pc off = some tgt) (b : RMState64) (base : BitVec 64)
    (hpc : b.pc = base + BitVec.ofNat 64 (4 * pc)) :
    (evalRMInst64 b (.bne a c off)).pc
      = base + BitVec.ofNat 64 (4 * (if b.regs.get a ≠ b.regs.get c then tgt else pc + 1)) := by
  simp only [evalRMInst64]
  split
  · rw [hpc, wordTarget_ofNat htgt]
  · rw [hpc, BitVec.add_assoc]
    congr 1
    rw [Nat.mul_add, BitVec.ofNat_add]
    rfl

/-! ## The decode-and-step simulation of `rvSelM` -/

/-- The memory selection selects straight-line instructions. -/
theorem rvSelM_straight {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {rs : List RMInst64} (h : rvSelM arrs sz i = some rs) : ∀ x ∈ rs, rmStraight x = true := by
  rcases rvSelM_inv h with ⟨_, _, _, _, -, -, -, -, -, -, rfl⟩
    | ⟨_, _, _, _, -, -, -, -, -, rfl⟩
    | ⟨_, _, _, -, -, -, -, -, -, rfl⟩
    | ⟨_, _, _, -, -, -, -, -, -, rfl⟩
    | ⟨_, -, -, -, -, rfl⟩ <;>
    simp [rvIdxAddr, rmStraight]

/-- The instructions of a selected block are straight-line. -/
theorem rvSelM_straight_block {arrs : List String} {sz : String → Nat} :
    ∀ (is : List LinstrRM) (rss : List (List RMInst64)), is.mapM (rvSelM arrs sz) = some rss →
      ∀ x ∈ rss.flatten, rmStraight x = true
  | [], rss, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h; simp
  | i :: is, rss, h => by
      simp only [List.mapM_cons, bind, pure] at h
      obtain ⟨rs, hi, h'⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rss', hs, h''⟩ := Option.bind_eq_some_iff.mp h'
      cases h''
      intro x hx
      rw [List.flatten_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact rvSelM_straight hi x hx
      · exact rvSelM_straight_block is rss' hs x hx

/-- **The machine steps of a selection simulate one `rvIsa` step.** For an instruction `i`
    that `rvSelM` maps to the instructions `rs`: each instruction of `rs` round trips through
    its bytes; from the index of a decoded program that holds `rs`, the machine reaches the
    index after it in the state `runRMBlock64 b rs`; and from states related on `rvMemRegs`
    and on the arrays, with the array layout and the index bound, the `rvIsa` step of `i`
    succeeds in a state related to that machine state in the same two relations. -/
theorem rv_mach_step (P : LprogM) {arrs : List String} {sz : String → Nat} {i : LinstrRM}
    {rs : List RMInst64} (h : rvSelM arrs sz i = some rs) (pre post : List RvInstr)
    (s : LstateMF) (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get)
    (hmem : RvMemRel arrs sz s b) (hsep : RvArrsSep arrs sz b.regs.get)
    (hb : IdxBound sz i b.regs.get) :
    (∀ x ∈ rs, RMRoundTrip x) ∧
    (rvMach r).Reaches (pre ++ rs.map .op ++ post) pre.length b (pre.length + rs.length)
      (runRMBlock64 b rs) ∧
    ∃ s', rvIsa.step P i s = some s' ∧ RegRel rvMemRegs s' (runRMBlock64 b rs).regs.get
      ∧ RvMemRel arrs sz s' (runRMBlock64 b rs) ∧ FrameM 1 s s' := by
  refine ⟨rvSelM_roundTrip h, ?_, ?_⟩
  · have hr := IsaMachine.reaches_ops (M := rvMach r) rs pre.length b
      (rvMach_opsAt r pre rs post (rvSelM_straight h))
    rwa [rvMach_runBlock] at hr
  · obtain ⟨s', hs', h1, h2, -, h3⟩ := rvSelM_step P h s b hrel hmem hsep hb
    exact ⟨s', hs', h1, h2, h3⟩

/-- **The decode-and-step simulation of the RV64 fragment.** For a block `is` that the memory
    selection maps to the instruction lists `rss`: the bytes of the concatenation followed by
    the bytes of `ret` decode at `rvMach r` to the concatenation followed by `ret`; and from
    an `LstateMF` related to a machine state `b` on `rvMemRegs` and on the arrays, with the
    array layout and the index bounds of the block, the `rvIsa` run of `is` succeeds, the
    decoded program halts from index 0 in a state `b'` with the leakage of the block, and the
    two final states are related in the same two relations. -/
theorem rv_mach_mem (P : LprogM) (arrs : List String) (sz : String → Nat) (is : List LinstrRM)
    (rss : List (List RMInst64)) (h : is.mapM (rvSelM arrs sz) = some rss) (s : LstateMF)
    (b : RMState64) (hrel : RegRel rvMemRegs s b.regs.get) (hmem : RvMemRel arrs sz s b)
    (hsep : RvArrsSep arrs sz b.regs.get) (hbd : MemBounds arrs sz is b) :
    (rvMach r).decode (encodeRMBlock64 rss.flatten ++ wordLE RiscvElfObject.encRet)
        = some (rss.flatten.map .op ++ [.ret]) ∧
    ∃ s' b', rvIsa.runL P is s = some s'
      ∧ (rvMach r).Halts (rss.flatten.map .op ++ [.ret]) 0 b b'
      ∧ (rvMach r).RunL (fun _ _ => True) (rss.flatten.map .op ++ [.ret]) 0 b
          ((rvMach r).blockLeak b rss.flatten) b'
      ∧ RegRel rvMemRegs s' b'.regs.get ∧ RvMemRel arrs sz s' b' ∧ FrameM is.length s s' := by
  obtain ⟨hdec, s', hs', h1, h2, h3⟩ := rv_asm_mem P arrs sz is rss h s b hrel hmem hsep hbd
  have hst := rvSelM_straight_block is rss h
  have hd := decodeRvProg_block (wordLE RiscvElfObject.encRet) [.ret] decodeRvProg_encRet
    (encodeRMBlock64 rss.flatten) rss.flatten hdec
  have hh := rvMach_halts_block r rss.flatten hst b
  have hl := rvMach_runL_block r rss.flatten hst b
  exact ⟨(congrFun (rvMach_decode r) _).trans hd, s', runRMBlock64 b rss.flatten, hs', hh, hl,
    h1, h2, h3⟩

/-! ## The `mpn_and_n` body at the machine -/

/-- **The `mpn_and_n` body at `rvMach`.** The bytes of `rvAndCode` followed by the bytes of
    `ret` decode to `rvAndCode` followed by `ret`; and from an `LstateMF` related to a machine
    state on `rvMemRegs` and on the arrays `a0`, `a1`, `a3` of `n` limbs, laid out separately,
    with the index `a4` below `n`, the `rvIsa` run of the body succeeds, the decoded program
    halts from index 0 with the leakage of the block, and the final states are related. -/
theorem rv_and_mach (P : LprogM) (n : Nat) (s : LstateMF) (b : RMState64)
    (hrel : RegRel rvMemRegs s b.regs.get) (hmem : RvMemRel rvAndArrs (fun _ => n) s b)
    (hsep : RvArrsSep rvAndArrs (fun _ => n) b.regs.get) (hidx : (b.regs.get "a4").toNat < n) :
    (rvMach r).decode (encodeRMBlock64 rvAndCode.flatten ++ wordLE RiscvElfObject.encRet)
        = some (rvAndCode.flatten.map .op ++ [.ret]) ∧
    ∃ s' b', rvIsa.runL P (rvAndBody n) s = some s'
      ∧ (rvMach r).Halts (rvAndCode.flatten.map .op ++ [.ret]) 0 b b'
      ∧ (rvMach r).RunL (fun _ _ => True) (rvAndCode.flatten.map .op ++ [.ret]) 0 b
          ((rvMach r).blockLeak b rvAndCode.flatten) b'
      ∧ RegRel rvMemRegs s' b'.regs.get ∧ RvMemRel rvAndArrs (fun _ => n) s' b'
      ∧ FrameM 6 s s' :=
  rv_mach_mem r P rvAndArrs (fun _ => n) (rvAndBody n) rvAndCode (rvAndBody_sel n) s b hrel hmem
    hsep (rvAndBody_bounds n b hidx)

/-- **The leakage of the `mpn_and_n` body under `RvRegime.zktMemData`**: the addresses of the
    two limb loads and of the limb store, which depend on the array bases `a1`, `a0`, `a3` and
    the index `a4` only. -/
theorem rvAndCode_leak_zktMemData (b : RMState64) :
    (rvMach .zktMemData).blockLeak b rvAndCode.flatten =
      [ .addr "" ((b.regs.get "a1" + (b.regs.get "a4" <<< 3)).toNat : Int)
      , .addr "" ((b.regs.get "a0" + (b.regs.get "a4" <<< 3)).toNat : Int)
      , .addr "" ((b.regs.get "a3" + (b.regs.get "a4" <<< 3)).toNat : Int) ] := by
  simp [rvAndCode, rvIdxAddr, IsaMachine.blockLeak, rvOpLeak_zktMemData, rmAddrLeak, rmAddr?,
    rvAddr, evalRMInst64, evalRInst64, RState64.set, opAdd64]

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvMach
