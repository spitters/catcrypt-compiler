/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame

@[expose] public section

set_option autoImplicit false

/-!
# The bytes of the stack-array instructions and their machine steps

`LprogBytes.encodeLopn` encodes the constant-index store `STOREIMM [d] <- [B; V; imm k]` as
`movq %V, 8k(%B)` and the zeroing `ZEROARR [D] <- [imm n; imm 64]` as the `n` stores
`movq $0, 8i(%D)`, `i < n`. The bytes of each instruction decode, piece by piece, to machine
stores, and the run of the decoded stores on the address machine writes the value register at
the byte offset `8 k` from the base register, or the zero word at the byte offsets `8 i`,
`i < n`, from the destination register, in order, with the registers and flags unchanged.
The addresses the zeroing writes are a function of the destination register and of `n`.

## Main definitions

* `stPieces`, `zPieces`: the byte pieces of the two instructions, with their machine
  instructions.

## Main results

* `stPieces_bytes`, `zPieces_bytes`: the bytes of the instructions are their pieces, and each
  piece decodes to its machine instruction.
* `run_stPieces`, `run_zPieces`: the runs of the decoded instructions on the address machine.
* `sim_storeImm`: from `ACorrW`, the step of the address semantics `fstepA` at the tag
  `.storeImm 64 n` with `k < n` is matched by the run of the decoded store.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.StackArrDecode

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-! ## 1. The constant-index store -/

/-- The byte piece of `STOREIMM [d] <- [B; V; imm k]`: `movq %V, 8k(%B)`. -/
def stPieces (B V : String) (k : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(encMemMovw 1 0x89 (gpNumU V) (gpNumU B) (Int.ofNat (8 * k)),
    .storeMem (phys B) (Int.ofNat (8 * k)) (.reg (phys V)))]

/-- An element offset `stackDispOk` admits is a signed 32-bit displacement. -/
theorem dispOk32_of_stackDispOk {k : Nat} (hk : stackDispOk k = true) :
    dispOk32 (Int.ofNat (8 * k)) = true := by
  simp only [stackDispOk, decide_eq_true_eq] at hk
  simp only [dispOk32, decide_eq_true_eq, Int.ofNat_eq_natCast]
  omega

/-- The 64-bit image of the byte offset `8 k` read as an integer. -/
theorem ofInt_eight_mul (k : Nat) : BitVec.ofInt 64 (8 * (k : Int)) = BitVec.ofNat 64 (8 * k) := by
  rw [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl]
  exact BitVec.ofInt_natCast _ _

/-- **The bytes of the constant-index store.** Over a general-purpose base and value and an
    offset `stackDispOk` admits, the bytes of `STOREIMM [d] <- [B; V; imm k]` are its piece,
    which decodes to the store of `V` at `8 k` from `B`. -/
theorem stPieces_bytes (F W Q : Nat) (a : LOperand) (B V : String) (k : Nat)
    (hB : isGpName B = true) (hV : isGpName V = true) (hk : stackDispOk k = true) :
    encodeLopn F W (.Lopn [a] "STOREIMM" [.reg B, .reg V, .imm k]) Q
        = (stPieces B V k).flatMap Prod.fst
      ∧ ∀ q ∈ stPieces B V k, PieceDec q := by
  refine ⟨by simp [stPieces, encodeLopn_storeImm F W a B V k Q hB hV hk], ?_⟩
  intro q hq
  simp only [stPieces, List.mem_singleton] at hq
  subst hq
  exact pieceDec_storeMem _ _ _ (gpNumU_lt_16 V) (gpNumU_lt_16 B) (dispOk32_of_stackDispOk hk)

/-- **The run of the constant-index store**: the decoded store writes the value register at
    the byte offset `8 k` from the base register, and leaves the registers and flags. -/
theorem run_stPieces (sa : AState) (B V : String) (k : Nat) :
    runBlockA sa ((stPieces B V k).map Prod.snd)
      = { sa with
          mem := write64 sa.mem (sa.regs (phys B) + BitVec.ofNat 64 (8 * k)) (sa.regs (phys V)) }
      := by
  simp [stPieces, CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame.evalInstrA_storeMem,
    JOperand.eval, AState.view, ofInt_eight_mul]

/-- **The simulation of the constant-index store.** From `ACorrW`, with the base `B` and the
    value `V` general-purpose names at width `64` and `k < n`, the step of the address
    semantics of `STOREIMM d, [B, V, #k]` at the tag `.storeImm 64 n` is matched by the run of
    the decoded store `movq %V, 8k(%B)`. -/
theorem sim_storeImm (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (d B V : String)
    {k n : Nat} (hk : k < n) (hB : gpOk B = true) (hV : gpOk V = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64)
    (hwV : (s.reg.lvm V).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA frame (.Lopn [.reg d] "STOREIMM" [.reg B, .reg V, .imm k], .storeImm 64 n)
      s zf = some (s', zf')) :
    ACorrW rsp (runBlockA sa ((stPieces B V k).map Prod.snd)) s' ∧ zf' = zf := by
  rw [fstepA_storeImm _ hk (hc.wide hB hwB) (hc.wide hV hwV)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  rw [run_stPieces]
  refine ⟨⟨fun r hr => ?_, hc.sp, fun x hx => ?_⟩, rfl⟩
  · have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · exact agree_write64 hc.mem _ _ x hx

/-! ## 2. The zeroing -/

/-- The byte pieces of `ZEROARR [D] <- [imm n; imm 64]`: `movq $0, 8i(%D)` for `i < n`. -/
def zPieces (D : String) (n : Nat) : List (List (BitVec 8) × JInstr 64) :=
  (List.range n).map fun i =>
    (ScalarEncoder.encMemMovImm (gpNumU D) (Int.ofNat (8 * i)) 0,
      .storeMem (phys D) (Int.ofNat (8 * i)) (.imm 0))

/-- `movq $0, off(%b)` with a signed 32-bit displacement decodes to the store of `0` at `off`
    from `%b`. -/
theorem pieceDec_storeZero (b : Nat) (off : Int) (hb : b < 16) (h : dispOk32 off = true) :
    PieceDec (ScalarEncoder.encMemMovImm b off 0,
      .storeMem (SailX86Decoder.regName b) off (.imm 0)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_storeMemImm32 (canonAlloc ()) (SailX86Decoder.regName b) off 0 rest
    (by decide) (by decide) h
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon b hb,
    gpNum_regName b hb] using e

/-- **The bytes of the zeroing.** Over a general-purpose destination, a positive count and a
    last element offset `stackDispOk` admits, the bytes of `ZEROARR [D] <- [imm n; imm 64]`
    are its pieces, each of which decodes to the store of `0` at `8 i` from `D`. -/
theorem zPieces_bytes (F W Q : Nat) (D : String) (n : Nat) (hD : isGpName D = true)
    (hn : 0 < n) (hk : stackDispOk (n - 1) = true) :
    encodeLopn F W (.Lopn [.reg D] "ZEROARR" [.imm n, .imm 64]) Q
        = (zPieces D n).flatMap Prod.fst
      ∧ ∀ q ∈ zPieces D n, PieceDec q := by
  refine ⟨by simp [zPieces, encodeLopn_zeroArr F W D n Q hD hn hk, encZeroArr,
    List.flatMap_map], ?_⟩
  intro q hq
  simp only [zPieces, List.mem_map, List.mem_range] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  refine pieceDec_storeZero _ _ (gpNumU_lt_16 D) (dispOk32_of_stackDispOk (k := i) ?_)
  simp only [stackDispOk, decide_eq_true_eq] at hk ⊢
  omega

/-- **The run of the zeroing**: the decoded stores write the zero word at the byte offsets
    `8 i`, `i < n`, from the destination register, in order (`JasminLsemAddrMem.zeroWords`),
    and leave the registers and flags. -/
theorem run_zPieces (sa : AState) (D : String) (n : Nat) :
    runBlockA sa ((zPieces D n).map Prod.snd)
      = { sa with mem := zeroWords sa.mem (sa.regs (phys D)) n } := by
  induction n with
  | zero => simp [zPieces, zeroWords]
  | succ n ih =>
    simp only [zPieces, List.range_succ, List.map_append, List.map_map] at ih ⊢
    rw [runBlockA_append]
    simp only [Function.comp_def] at ih ⊢
    rw [ih]
    simp [CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame.evalInstrA_storeMem,
      JOperand.eval, zeroWords, ofInt_eight_mul]

end CatCrypt.Crypto.SecureCompilation.X86Backend.StackArrDecode
