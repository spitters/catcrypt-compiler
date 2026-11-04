/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

@[expose] public section

set_option autoImplicit false

/-!
# The gate of the x86 assembly simulation on legal forms

The x86 back end `VIR.LprogIsa.x86Backend` gates a body by `printedAddrWB`, which checks every
instruction before the closing return with `instrOKWB`, and calls an instruction legal when it
has a legal form `LegalForm` of the x86 encoder. This module compares the two per instruction.

`instrOKWB` is narrower than `LegalForm`. The gate reads 64-bit instructions over the
general-purpose names other than `RSP` (`gpOk`), and among those only the arms of the address
simulation. `GateForm` lists the sub-forms of the legal forms that the gate accepts, one
constructor per accepted shape.

## The legal forms outside `GateForm`

The following families of legal forms lie outside `GateForm`, and `instrOKWB` refuses each of
them in its one-instruction body:

* untagged (32-bit) forms: two-address operations (`ADD`), register moves (`MOV`), the
  materialised comparison (`SETE`), the carry-chain add (`ADCX`), the load `LOAD` from a cell,
  the count-in-mnemonic shift `SHR:k`, and the immediate move `MOV` of a value at or above
  `2^31`;
* a 64-bit operation reading `RSP` as a data register;
* `LOAD:64` from a register;
* the immediate move `MOVQ` of an immediate and `MOV:64` of a value at or above `2^64`;
* a select whose condition is its destination;
* the three-register arithmetic right shift `SAR:64 D, [A, B]`, the count-in-mnemonic `SAR:k:64`
  and the negation `NEG:64`;
* `MUL:64` by an immediate, `CMP:64` against an immediate outside the sign-extended `imm8`
  range, a shift by an immediate of at least `64`, and `SHR:64` by `0`;
* an indexed load at a stride other than `8` or at the tag `LOADIDX:64`, and an indexed store
  whose array operand is no register name;
* a carry-chain add whose carry-in is one of its word sources, the overflow-chain binding
  `ADOXHI:64`, a carry-out binding with two sources, and the flag materialisation `SETC`;
* the widening multiplication at the tag `MULX:64`, the high-word binding `MULXHI`, the keep
  marker `KEEP` and the frame directive `FRAMEADD`;
* the stack-array zeroing `ZEROARR D, [#n, #w]` into a destination register, a zeroing
  through a base register at a width other than `64` or of no words, a constant-index store
  `STOREIMM` whose destination is no general-purpose name, and a stack-array access through a
  base whose word offset `stackDispOk` refuses;
* `Lgoto`, `Lcall`, `Lalign`, a conditional branch on a condition other than the zero flag,
  and a conditional branch to a label the body does not define.

## Main definitions

* `GateForm body` — the legal forms the gate accepts in the body `body`.

## Main results

* `instrOKWB_of_gateForm`, `legalForm_of_gateForm`, `instrOKWB_of_legalForm`: every sub-form of
  `GateForm` is a legal form and passes `instrOKWB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (condPol labelAt castTagW)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (LegalForm isMovMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct?)

/-- The count-in-mnemonic shift `b:k:64` of base `b` by `k`. -/
def tagMnem (b : String) (k : Nat) : String := b ++ ":" ++ toString k ++ ":64"

/-- The width casts the gate reads: the `CASTW_<w>_<w'>` mnemonics with both a source width
    `castMovBits` and a destination width `castTagW`. -/
def castMnems : List String :=
  ["CASTW_64_16", "CASTW_16_64", "CASTW_16_16", "CASTW_16_32", "CASTW_32_16", "CASTW_64_32",
    "CASTW_32_64", "CASTW_32_32"]

/-- **The sub-forms of the legal forms that the gate `instrOKWB` accepts**, in the body `body`
    with the body parameters `P = Params.ofBody body`. -/
inductive GateForm (body : Lcmd) : LinstrR → Prop
  /-- A 64-bit register move between general-purpose names. -/
  | movRR (m d s : String) : m ∈ ["MOV:64", "MOVQ"] → gpOk d = true → gpOk s = true →
      GateForm body (.Lopn [.reg d] m [.reg s])
  /-- A 64-bit store of a general-purpose name into a frame slot with a `rel32` offset. -/
  | movStore (m q s : String) : m ∈ ["MOV:64", "MOVQ"] → isSpillOrQsave q = true →
      (spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
        (Params.ofBody body).qsaveB).isSome = true →
      dispOk32 (slotOff (Params.ofBody body) q) = true → gpOk s = true →
      GateForm body (.Lopn [.reg q] m [.reg s])
  /-- A 64-bit load of a frame slot whose word is disjoint from the red-zone word. -/
  | movLoad (m d q : String) : m ∈ ["MOV:64", "MOVQ"] → gpOk d = true →
      isSpillOrQsave q = true → kOk (Params.ofBody body) q = true →
      GateForm body (.Lopn [.reg d] m [.reg q])
  /-- An untagged immediate move below `2^31` into a general-purpose name. -/
  | movImm32 (d : String) (n : Nat) : gpOk d = true → n < 2 ^ 31 →
      GateForm body (.Lopn [.reg d] "MOV" [.imm n])
  /-- A 64-bit immediate move of a 64-bit value into a general-purpose name. -/
  | movImm64 (d : String) (v : Nat) : gpOk d = true → v < 2 ^ 64 →
      GateForm body (.Lopn [.reg d] "MOV:64" [.imm v])
  /-- A 64-bit immediate move of a 64-bit value into a frame slot with a `rel32` offset, the
      value sign-extending from 32 bits or the slot word disjoint from the red-zone word. -/
  | movImmSlot (q : String) (v : Nat) : isSpillOrQsave q = true →
      (spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
        (Params.ofBody body).qsaveB).isSome = true →
      dispOk32 (slotOff (Params.ofBody body) q) = true → v < 2 ^ 64 →
      (ScalarEncoder.fitsImm32S v = true ∨ sepB cmovRedZone (slotOff (Params.ofBody body) q) = true) →
      GateForm body (.Lopn [.reg q] "MOV:64" [.imm v])
  /-- The 64-bit select over general-purpose names with a condition distinct from the other
      three operands. -/
  | select (d c a b : String) : gpOk d = true → gpOk c = true → gpOk a = true → gpOk b = true →
      d ≠ c → a ≠ c → b ≠ c → GateForm body (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
  /-- A 64-bit materialised comparison over general-purpose names. -/
  | setcc (m d a b : String) : m ∈ ["SETE:64", "SETNE:64"] → gpOk d = true → gpOk a = true →
      gpOk b = true → GateForm body (.Lopn [.reg d] m [.reg a, .reg b])
  /-- A 64-bit materialised comparison against an immediate below `2^31`. -/
  | setccImm (m d a : String) (v : Nat) : m ∈ ["SETE:64", "SETNE:64"] → gpOk d = true →
      gpOk a = true → v < 2 ^ 31 → GateForm body (.Lopn [.reg d] m [.reg a, .imm v])
  /-- A 64-bit two-address operation over general-purpose names. -/
  | alu (m d s : String) :
      m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64", "CMP:64"] →
      gpOk d = true → gpOk s = true → GateForm body (.Lopn [.reg d] m [.reg d, .reg s])
  /-- A 64-bit two-address group-1 operation against a 64-bit immediate that sign-extends from
      32 bits. -/
  | aluImm (m d : String) (v : Nat) : m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64"] →
      gpOk d = true → v < 2 ^ 64 → ScalarEncoder.fitsImm32S v = true →
      GateForm body (.Lopn [.reg d] m [.reg d, .imm v])
  /-- The 64-bit compare against an immediate that sign-extends from 8 bits. -/
  | cmpImm (d : String) (v : Nat) : gpOk d = true → fitsImm8S 1 v = true →
      GateForm body (.Lopn [.reg d] "CMP:64" [.reg d, .imm v])
  /-- A 64-bit two-address shift by an immediate below `64`, nonzero for `SHR:64`. -/
  | shiftImm (m d : String) (k : Nat) : m ∈ ["SHL:64", "SHR:64"] → gpOk d = true → k < 64 →
      (0 < k ∨ m = "SHL:64") → GateForm body (.Lopn [.reg d] m [.reg d, .imm k])
  /-- A 64-bit two-address arithmetic right shift by an immediate `0 < k < 64`. -/
  | sarImm (d : String) (k : Nat) : gpOk d = true → 0 < k → k < 64 →
      GateForm body (.Lopn [.reg d] "SAR:64" [.reg d, .imm k])
  /-- A 64-bit three-register left or logical right shift. -/
  | shiftReg (m d a b : String) : m ∈ ["SHL:64", "SHR:64"] → gpOk d = true → gpOk a = true →
      gpOk b = true → GateForm body (.Lopn [.reg d] m [.reg a, .reg b])
  /-- A width cast between general-purpose names. -/
  | cast (o d a : String) : o ∈ castMnems → gpOk d = true → gpOk a = true →
      GateForm body (.Lopn [.reg d] o [.reg a])
  /-- A 64-bit count-in-mnemonic left or logical right shift by `1 … 63`. -/
  | tagShift (b : String) (k : Nat) (d s : String) : b ∈ ["SHL", "SHR"] → 0 < k → k < 64 →
      gpOk d = true → gpOk s = true → GateForm body (.Lopn [.reg d] (tagMnem b k) [.reg s])
  /-- The 64-bit count-in-mnemonic shift by `0`, a copy. -/
  | shl0 (d s : String) : gpOk d = true → gpOk s = true →
      GateForm body (.Lopn [.reg d] "SHL:0:64" [.reg s])
  /-- The whole-word load of a cell `mem.B.off` with a general-purpose base and a `rel32`
      offset. -/
  | load (d n b : String) (off : Nat) : cellParts? n = some (b, off) → gpOk d = true →
      gpOk b = true → dispOk32 (Int.ofNat off) = true →
      GateForm body (.Lopn [.reg d] "LOAD:64" [.reg n])
  /-- The whole-word store into a cell `mem.B.off` with a general-purpose base and a `rel32`
      offset. -/
  | store (n b : String) (off : Nat) (s : String) : cellParts? n = some (b, off) →
      gpOk s = true → gpOk b = true → dispOk32 (Int.ofNat off) = true →
      GateForm body (.Lopn [.reg n] "STORE:64" [.reg s])
  /-- The 64-bit move into a cell `mem.B.off` with a general-purpose base and a `rel32`
      offset. -/
  | storeMov (n b : String) (off : Nat) (s : String) : cellParts? n = some (b, off) →
      gpOk s = true → gpOk b = true → dispOk32 (Int.ofNat off) = true →
      GateForm body (.Lopn [.reg n] "MOV:64" [.reg s])
  /-- The 64-bit move out of a cell `mem.B.off` into a general-purpose name, with a
      general-purpose base and a `rel32` offset. -/
  | loadMov (d n b : String) (off : Nat) : cellParts? n = some (b, off) → gpOk d = true →
      gpOk b = true → dispOk32 (Int.ofNat off) = true →
      GateForm body (.Lopn [.reg d] "MOV:64" [.reg n])
  /-- The indexed address `LEA:64 D, [B + X · sc]` over general-purpose names at a stride of
      `1`, `2`, `4` or `8`. -/
  | leaIdx (d b x : String) (sc : Nat) : gpOk d = true → gpOk b = true → gpOk x = true →
      sc ∈ [1, 2, 4, 8] → GateForm body (.Lopn [.reg d] "LEA:64" [.arrIdx b x sc])
  /-- The indexed load at stride `8` over general-purpose names. -/
  | loadIdx (d b x : String) : gpOk d = true → gpOk b = true → gpOk x = true →
      GateForm body (.Lopn [.reg d] "LOADIDX" [.arrIdx b x 8])
  /-- The indexed store at stride `8` over general-purpose names into a named array. -/
  | storeIdx (a b x v : String) : gpOk b = true → gpOk x = true → gpOk v = true →
      GateForm body (.Lopn [.reg a] "STOREIDX" [.arrIdx b x 8, .reg v])
  /-- The zeroing `ZEROARR [], [B, #n, #64]` of `0 < n` words from a general-purpose base,
      the offset of the last word admitted by `stackDispOk`. -/
  | zeroArr (b : String) (n : Nat) : gpOk b = true → 0 < n → stackDispOk (n - 1) = true →
      GateForm body (.Lopn [] "ZEROARR" [.reg b, .imm n, .imm 64])
  /-- The constant-index store `STOREIMM D, [B, V, #k]` over general-purpose names, the
      offset of word `k` admitted by `stackDispOk`. -/
  | storeImm (d b v : String) (k : Nat) : gpOk d = true → gpOk b = true → gpOk v = true →
      stackDispOk k = true → GateForm body (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k])
  /-- The frame-array address `LEA:64 D, fa.<o>.<n>` into a general-purpose name, the base
      offset `o` in `rel32` range. -/
  | leaFa (d q : String) : gpOk d = true → faB q = true → dispOk32 (faOff q) = true →
      GateForm body (.Lopn [.reg d] "LEA:64" [.reg q])
  /-- The 64-bit carry-chain add over general-purpose names whose carry-in is none of the word
      sources, and whose destination is the first source or none of the other sources. -/
  | adcx (d a s c : String) : gpOk d = true → gpOk a = true → gpOk s = true → gpOk c = true →
      a ≠ c → s ≠ c → (a = d ∨ (d ≠ s ∧ d ≠ c)) →
      GateForm body (.Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
  /-- The carry-out binding of a 64-bit add into a general-purpose name, each source a
      general-purpose name or a frame slot of `kOk`, the carry-in none of the word sources. -/
  | adcxhi (o a s c : String) : gpOk o = true → kOk (Params.ofBody body) a = true →
      kOk (Params.ofBody body) s = true → kOk (Params.ofBody body) c = true → a ≠ c → s ≠ c →
      GateForm body (.Lopn [.reg o] "ADCXHI:64" [.reg a, .reg s, .reg c])
  /-- The widening multiplication into general-purpose names. -/
  | mulx (l h s : String) : gpOk l = true → gpOk h = true → gpOk s = true →
      GateForm body (.Lopn [.reg l, .reg h] "MULX" [.reg s])
  /-- A label. -/
  | label (k : LabelKind) (l : LLabel) : GateForm body (.Llabel k l)
  /-- A conditional branch on the zero flag to a label the body defines. -/
  | cond (cc : String) (l : LLabel) : (condPol cc).isSome = true →
      (labelAt body l).isSome = true → GateForm body (.Lcond (.reg cc) l)

/-! ## 1. The gate accepts the sub-forms -/

/-- A general-purpose name is no frame-slot name. -/
theorem gpOk_not_slot {r : String} (h : gpOk r = true) : isSpillOrQsave r = false :=
  (gpFacts h).notSlot

/-- A frame-slot name is no general-purpose name. -/
theorem not_gpOk_of_slot {r : String} (h : isSpillOrQsave r = true) : gpOk r = false := by
  cases hg : gpOk r
  · rfl
  · rw [gpOk_not_slot hg] at h; cases h

/-- A frame-slot name of `kOk` has a frame offset in `rel32` range whose word is disjoint from
    the red-zone word. -/
theorem kOk_slot {P : Params} {q : String} (hk : kOk P q = true) (hq : isSpillOrQsave q = true) :
    (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome = true ∧ dispOk32 (slotOff P q) = true
      ∧ sepB cmovRedZone (slotOff P q) = true := by
  rcases kOk_cases hk with hg | ⟨off, hoff, hd, hs⟩
  · rw [not_gpOk_of_slot hq] at hg; cases hg
  · simp [slotOff, hoff, hd, hs]

theorem repr_zero_eq : Nat.repr 0 = "0" := by
  rw [Nat.repr_of_lt (show 0 < 10 by decide)]
  simp [← String.toList_inj]

theorem withWidthTag_shl0 : withWidthTag 64 ("SHL" ++ ":" ++ toString 0) = "SHL:0:64" := by
  simp only [withWidthTag, ite_true, Nat.toString_eq_repr, Nat.repr_of_lt (show 0 < 10 by decide)]
  simp [← String.toList_inj]

/-- The count-`0` shift passes the closed conditions of its arm. -/
theorem arm_shl0_ok (P : Params) (Q : List (String × Int)) (d s : String) :
    Arm.ok P Q (.shl0 "SHL:0:64" d s) = (gpOk d && gpOk s) := by
  simp only [Arm.ok, withWidthTag_shl0, beq_self_eq_true, Bool.and_true]
  cases gpOk d <;> cases gpOk s <;> decide +kernel

theorem gpOk_of_kOk {P : Params} {x : String} (hk : kOk P x = true)
    (hs : isSpillOrQsave x = false) : gpOk x = true := by
  simpa [kOk, hs] using hk

/-! ### The count-in-mnemonic shifts -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem
  (stripWidthTag_append64 hasSuffix_append charsToNat?_toString)

theorem toList_tagMnem (b : String) (k : Nat) :
    (tagMnem b k).toList = b.toList ++ ':' :: ((toString k).toList ++ [':', '6', '4']) := by
  simp only [tagMnem, String.toList_append,
    show (":" : String).toList = [':'] from by decide,
    show (":64" : String).toList = [':', '6', '4'] from by decide]
  simp

theorem stripWidthTag_tagMnem {b : String} (hb : b ∈ ["SHL", "SHR"]) (k : Nat) :
    stripWidthTag (tagMnem b k) = b ++ ":" ++ toString k := by
  have hbc : '^' ∉ b.toList := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> decide
  have hkc : '^' ∉ Nat.toDigits 10 k := by
    have := (sep_not_mem_toString k).2
    rwa [toString_toList_eq] at this
  exact stripWidthTag_append64 _ (by simp [hbc, hkc])

theorem toList_tagBase (b : String) (k : Nat) :
    (b ++ ":" ++ toString k).toList = b.toList ++ ':' :: (toString k).toList := by
  simp only [String.toList_append, show (":" : String).toList = [':'] from by decide]
  simp

theorem mnemWidth_tagMnem (b : String) (k : Nat) : mnemWidth (tagMnem b k) = 64 := by
  simp [mnemWidth, tagMnem, hasSuffix_append]

theorem tagShiftCount_tagBase {b : String} (hb : b.toList.length = 3) (k : Nat) :
    tagShiftCount (b ++ ":" ++ toString k) = k := by
  rw [tagShiftCount, strDropToNat?, toList_tagBase]
  obtain ⟨x, y, z, hxyz⟩ : ∃ x y z, b.toList = [x, y, z] := by
    match h : b.toList, hb with
    | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
  rw [hxyz]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [charsToNat?_toString]
  rfl

/-- Two strings whose character lists differ in their first `n` characters are distinct. -/
theorem ne_of_take {x t : String} (n : Nat) (h : x.toList.take n ≠ t.toList.take n) :
    x ≠ t := by
  rintro rfl
  exact h rfl

theorem take2_tagMnem {b : String} (hb : b ∈ ["SHL", "SHR"]) (k : Nat) :
    (tagMnem b k).toList.take 2 = ['S', 'H'] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [toList_tagMnem]
  rcases hb with rfl | rfl <;>
    simp [show ("SHL" : String).toList = ['S', 'H', 'L'] from by decide,
      show ("SHR" : String).toList = ['S', 'H', 'R'] from by decide]

theorem take2_tagBase {b : String} (hb : b ∈ ["SHL", "SHR"]) (k : Nat) :
    (b ++ ":" ++ toString k).toList.take 2 = ['S', 'H'] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [toList_tagBase]
  rcases hb with rfl | rfl <;>
    simp [show ("SHL" : String).toList = ['S', 'H', 'L'] from by decide,
      show ("SHR" : String).toList = ['S', 'H', 'R'] from by decide]

theorem tagShiftExt_tagBase {b : String} (hb : b ∈ ["SHL", "SHR"]) (k : Nat) :
    tagShiftExt (b ++ ":" ++ toString k) = if b = "SHL" then some 4 else some 5 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  unfold tagShiftExt
  rw [toList_tagBase]
  rcases hb with rfl | rfl <;>
    simp [show ("SHL" : String).toList = ['S', 'H', 'L'] from by decide,
      show ("SHR" : String).toList = ['S', 'H', 'R'] from by decide,
      show ("SHL:" : String).toList = ['S', 'H', 'L', ':'] from by decide,
      show ("SHR:" : String).toList = ['S', 'H', 'R', ':'] from by decide]

/-- A tactic that proves a count-in-mnemonic shift or its base distinct from a string
    literal whose first two characters differ from `SH`. -/
macro "tag_ne " h:ident : tactic => `(tactic| first
  | exact ne_of_take 2 (by rw [take2_tagMnem $h]; decide)
  | exact ne_of_take 2 (by rw [take2_tagBase $h]; decide))

/-- **The closed facts of a count-in-mnemonic shift** `SHL:k:64` or `SHR:k:64` with
    `1 ≤ k ≤ 63`: it is no cast, move, cell access, multiplication or indexed access, it is no
    count-`0` shift, and its register arm passes exactly when its operands are
    general-purpose names. -/
theorem tagMnem_facts {b : String} (hb : b ∈ ["SHL", "SHR"]) {k : Nat} (hk0 : 0 < k)
    (hk : k < 64) (P : Params) (Q : List (String × Int)) (d s : String) :
    castMovBits (tagMnem b k) = none ∧ castTagW (tagMnem b k) = none
      ∧ isMovM (tagMnem b k) = false ∧ tagMnem b k ≠ "MOV" ∧ tagMnem b k ≠ "LOAD:64"
      ∧ tagMnem b k ≠ "STORE:64" ∧ tagMnem b k ≠ "SHL:0:64" ∧ tagMnem b k ≠ "MULX"
      ∧ tagMnem b k ≠ "LOADIDX" ∧ tagMnem b k ≠ "STOREIDX"
      ∧ Arm.ok P Q (.shr (tagMnem b k) d s) = (gpOk d && gpOk s) := by
  have h0 : tagMnem b k ≠ "SHL:0:64" := by
    intro h
    have h1 := congrArg (fun m => tagShiftCount (stripWidthTag m)) h
    simp only [stripWidthTag_tagMnem hb] at h1
    have hl : b.toList.length = 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> decide
    rw [tagShiftCount_tagBase hl,
      show stripWidthTag "SHL:0:64" = "SHL:0" from by decide +kernel,
      show tagShiftCount "SHL:0" = 0 from by decide +kernel] at h1
    omega
  refine ⟨?_, ?_, ?_, by tag_ne hb, by tag_ne hb, by tag_ne hb, h0, by tag_ne hb, by tag_ne hb, by tag_ne hb, ?_⟩
  · have : ∀ t ∈ ["CASTW_64_16", "CASTW_16_64", "CASTW_16_16", "CASTW_16_32", "CASTW_32_16",
        "CASTW_64_32", "CASTW_32_64", "CASTW_32_32"], tagMnem b k ≠ t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tag_ne hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at this
    simp [castMovBits, this]
  · have : ∀ t ∈ ["CASTW_64_16", "CASTW_32_16", "CASTW_16_16", "CASTW_64_32", "CASTW_32_32",
        "CASTW_16_32", "CASTW_64_64", "CASTW_32_64", "CASTW_16_64"], tagMnem b k ≠ t := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tag_ne hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at this
    simp [castTagW, this]
  · have h1 : tagMnem b k ≠ "MOV:64" := by tag_ne hb
    have h2 : tagMnem b k ≠ "MOVQ" := by tag_ne hb
    simp [isMovM, h1, h2]
  · have hl : b.toList.length = 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> decide
    have e1 : b ++ ":" ++ toString k ≠ "ADCXHI" := by tag_ne hb
    have e2 : b ++ ":" ++ toString k ≠ "ADOXHI" := by tag_ne hb
    have e3 : b ++ ":" ++ toString k ≠ "MULXHI" := by tag_ne hb
    have e4 : b ++ ":" ++ toString k ≠ "MULX" := by tag_ne hb
    have e5 : b ++ ":" ++ toString k ≠ "MULXMEM" := by tag_ne hb
    have e6 : b ++ ":" ++ toString k ≠ "ADCX" := by tag_ne hb
    have e7 : b ++ ":" ++ toString k ≠ "ADOX" := by tag_ne hb
    have hadx : adxPrefix (b ++ ":" ++ toString k) = none := by
      unfold adxPrefix
      split <;> simp_all
    have hcount := tagShiftCount_tagBase hl k
    have hext := tagShiftExt_tagBase hb k
    have hst := stripWidthTag_tagMnem hb k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rw [ite_eq_left rfl] at hext
      simp only [Arm.ok, isCarryOutBinding, isMulHiBinding, shrK, tagShExt, tagShl, tagRor,
        tagShName, hst, mnemWidth_tagMnem, hcount, hext, hadx]
      simp only [Nat.toString_eq_repr, String.reduceAppend] at e1 e2 e3 e4 e5
      simp [beq_eq_false_iff_ne.2 e1, beq_eq_false_iff_ne.2 e2, beq_eq_false_iff_ne.2 e3,
        beq_eq_false_iff_ne.2 e4, beq_eq_false_iff_ne.2 e5, LprogBytes.rexW, withWidthTag, tagMnem,
        hk0, hk]
    · rw [ite_eq_right (by decide)] at hext
      simp only [Arm.ok, isCarryOutBinding, isMulHiBinding, shrK, tagShExt, tagShl, tagRor,
        tagShName, hst, mnemWidth_tagMnem, hcount, hext, hadx]
      simp only [Nat.toString_eq_repr, String.reduceAppend] at e1 e2 e3 e4 e5
      simp [beq_eq_false_iff_ne.2 e1, beq_eq_false_iff_ne.2 e2, beq_eq_false_iff_ne.2 e3,
        beq_eq_false_iff_ne.2 e4, beq_eq_false_iff_ne.2 e5, LprogBytes.rexW, withWidthTag, tagMnem,
        hk0, hk]

/-- The simplification set that evaluates `instrOKWB` on a concrete mnemonic. -/
macro "gate_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [instrOKWB, classifyK, movImmStruct?, classifyS,
    classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX, classifyEI,
    classifyR, classifyA, classify, AArm.ok, Arm.ok, Arm.instr, regArmB, plainB, isMovM,
    castMovBits, castTagW, CArm.ok, SArm.ok, MArm.ok, imm32Ok, lOk, iOk, vOk, eOk, xOk, eiOk,
    rOk, castOk, isShI,
    aluArm, gpOk_not_slot, withWidthTag_shl0, repr_zero_eq, withWidthTag, arm_shl0_ok, *] <;>
    first | omega | tauto | (intro h; exact ⟨by omega, h⟩))

/-- A frame-array name is no general-purpose name. -/
theorem not_gpOk_of_faB {q : String} (h : faB q = true) : gpOk q = false := by
  cases hg : gpOk q
  · rfl
  · have hp := faParts?_gp hg
    simp [faB, hp] at h

/-- A frame-array name is no frame-slot name. -/
theorem not_slot_of_faB {q : String} (h : faB q = true) : isSpillOrQsave q = false := by
  have hq := hasPrefix_fa_of_faB h
  unfold isSpillOrQsave
  unfold VIR.JasminLprogExport.hasPrefix at hq ⊢
  rcases hl : q.toList with _ | ⟨c, t⟩ <;> simp_all [List.isPrefixOf]
  grind

/-- **The frame-array address is covered**: `instrOKWB` accepts `LEA:64 D, q` for a
    general-purpose `D` and a frame-array name `q` whose base offset is in `rel32` range. -/
theorem instrOKWB_leaFa (body : Lcmd) (P : Params) {d q : String} (hd : gpOk d = true)
    (hq : faB q = true) (hdisp : dispOk32 (faOff q) = true) :
    instrOKWB body P (.Lopn [.reg d] "LEA:64" [.reg q]) = true := by
  have hg := not_gpOk_of_faB hq
  have hs := not_slot_of_faB hq
  have hc := VIR.JasminLsemAddrMem.cellParts?_of_faB hq
  have hcd := cellParts?_gp hd
  gate_simp

/-- **`instrOKWB` accepts every sub-form of `GateForm`** at the parameters of its body. -/
theorem instrOKWB_of_gateForm {body : Lcmd} {i : LinstrR} (h : GateForm body i) :
    instrOKWB body (Params.ofBody body) i = true := by
  cases h with
  | movRR m d s hm hd hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have hcd := cellParts?_gp hd
    have hcs := cellParts?_gp hs
    rcases hm with rfl | rfl <;> gate_simp
  | movStore m q s hm hq hsome hdisp hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have hq' := not_gpOk_of_slot hq
    have hcq := cellParts?_of_spillOff hsome
    have hcs := cellParts?_gp hs
    rcases hm with rfl | rfl <;> gate_simp
  | movLoad m d q hm hd hq hk =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have hq' := not_gpOk_of_slot hq
    have hcd := cellParts?_gp hd
    obtain ⟨h1, h2, h3⟩ := kOk_slot hk hq
    have hcq := cellParts?_of_spillOff h1
    rcases hm with rfl | rfl <;> gate_simp
  | movImm32 d n hd hn => gate_simp
  | movImm64 d v hd hv =>
    have hq := gpOk_not_slot hd
    cases hf : ScalarEncoder.fitsImm32S v <;> gate_simp
  | movImmSlot q v hq hsome hdisp hv hor =>
    have hq' := not_gpOk_of_slot hq
    revert hor
    gate_simp
  | select d c a b hd hc ha hb h1 h2 h3 =>
    have h1' : (d != c) = true := bne_iff_ne.2 h1
    have h2' : (a != c) = true := bne_iff_ne.2 h2
    have h3' : (b != c) = true := bne_iff_ne.2 h3
    gate_simp
  | setcc m d a b hm hd ha hb =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> gate_simp
  | setccImm m d a v hm hd ha hv =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> gate_simp
  | alu m d s hm hd hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> gate_simp
  | aluImm m d v hm hd hv hf =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> gate_simp
  | cmpImm d v hd hv => gate_simp
  | shiftImm m d k hm hd hk h0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    revert h0
    rcases hm with rfl | rfl <;> gate_simp
  | sarImm d k hd hk0 hk => exact instrOKWB_sarImm body _ hd hk0 hk
  | shiftReg m d a b hm hd ha hb =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> gate_simp
  | cast o d a ho hd ha =>
    simp only [castMnems, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> gate_simp
  | tagShift b k d s hb hk0 hk hd hs =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      tagMnem_facts hb hk0 hk (Params.ofBody body) [] d s
    have hmv : tagMnem b k ≠ "MOV:64" := by tag_ne hb
    have hlea : tagMnem b k ≠ "LEA:64" := by tag_ne hb
    simp (config := { decide := true }) only [instrOKWB, classifyK, h1, h2, movImmStruct?,
      classifyS, classifyC, classifyM, classifyI, classifyL, classifyV, classifyE, classifyX,
      classifyEI, classifyR, classifyA, classify, AArm.ok, regArmB, plainB, h3, h5, h6, hmv,
      withWidthTag_shl0, hd, hs, Option.map_some, ite_false, Bool.false_and, beq_iff_eq, h7,
      Bool.and_self]
    simp [Arm.instr, h8, h9, h10, h2, hlea, h11, hd, hs]
  | shl0 d s hd hs => gate_simp
  | load d n b off hn hd hb hoff => gate_simp
  | store n b off s hn hs hb hoff => gate_simp
  | storeMov n b off s hn hs hb hoff => gate_simp
  | loadMov d n b off hn hd hb hoff =>
    have hcd := cellParts?_gp hd
    gate_simp
  | leaIdx d b x sc hd hb hx hsc =>
    have h4 := (gpFacts hx).ne4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsc
    rcases hsc with rfl | rfl | rfl | rfl <;> gate_simp
  | loadIdx d b x hd hb hx =>
    have h4 := (gpFacts hx).ne4
    gate_simp
  | storeIdx a b x v hb hx hv =>
    have h4 := (gpFacts hx).ne4
    gate_simp
  | zeroArr b n hb hn hk => gate_simp
  | storeImm d b v k hd hb hv hk => gate_simp
  | leaFa d q hd hq hdisp => exact instrOKWB_leaFa body _ hd hq hdisp
  | adcx d a s c hd ha hs hc h1 h2 h3 =>
    have hd' := gpOk_not_slot hd
    have ha' := gpOk_not_slot ha
    have hs' := gpOk_not_slot hs
    have hc' := gpOk_not_slot hc
    revert h1 h2 h3
    gate_simp
  | adcxhi o a s c ho ha hs hc h1 h2 =>
    have h1' : (a != c) = true := bne_iff_ne.2 h1
    have h2' : (s != c) = true := bne_iff_ne.2 h2
    cases hsl : (isSpillOrQsave a || isSpillOrQsave s || isSpillOrQsave c)
    · simp only [Bool.or_eq_false_iff] at hsl
      obtain ⟨⟨hsa, hss⟩, hsc⟩ := hsl
      have ha' := gpOk_of_kOk ha hsa
      have hs' := gpOk_of_kOk hs hss
      have hc' := gpOk_of_kOk hc hsc
      gate_simp
    · gate_simp
  | mulx l h s hl hh hs =>
    by_cases he : l = h
    · subst he; gate_simp
    · gate_simp
  | label k l => rfl
  | cond cc l h1 h2 => simp [instrOKWB, h1, h2]

/-! ## 2. The sub-forms are legal forms -/

theorem isGp_of_gpOk {r : String} (h : gpOk r = true) : isGpName r = true := (gpFacts h).isGp

/-- The simplification set that evaluates `x86LegalB` on a concrete mnemonic. -/
macro "legal_simp" : tactic => `(tactic|
  (apply x86LegalB_iff.1
   simp (config := { decide := true }) [x86LegalB, x86MovB, x86SelectB, x86SetccB,
    x86SetccImmB, x86MovImmB, x86AluB, x86AluImmB, x86ShiftRegB, x86UnaryB, x86MemMovB,
    x86SibLoadB, x86SibStoreB, x86Carry3B, x86FlagOutB, x86WideMulB, x86Fixed, x86Alu,
    x86AluImm, x86ShiftReg, x86Unary, x86MemMov, x86SibLoad, x86SibStore, x86SibScale, x86Carry3,
    x86FlagOut, x86WideMul, x86SlotImm, isSetccEncMnem, isSetccImmEnc, isMovMnem, opResolvesB,
    isGp_of_gpOk, encMemName_of_isGpName, castMovBits, *] <;>
   first | omega | tauto))

/-- **Every sub-form of `GateForm` is a legal form** of the x86 encoder in the context of the
    body. -/
theorem legalForm_of_gateForm {body : Lcmd} {i : LinstrR} (h : GateForm body i) :
    LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx body) i := by
  cases h with
  | movRR m d s hm hd hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd; have := isGp_of_gpOk hs
    rcases hm with rfl | rfl <;> legal_simp
  | movStore m q s hm hq hsome hdisp hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hs
    rcases hm with rfl | rfl <;> legal_simp
  | movLoad m d q hm hd hq hk =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd
    have hsome := (kOk_slot hk hq).1
    rcases hm with rfl | rfl <;> legal_simp
  | movImm32 d n hd hn => have := isGp_of_gpOk hd; legal_simp
  | movImm64 d v hd hv => have := isGp_of_gpOk hd; legal_simp
  | movImmSlot q v hq hsome hdisp hv hor =>
    have hg : isGpName q = false := by
      cases h : isGpName q
      · rfl
      · rw [(notSlotMem_of_isGpName h).1] at hq; cases hq
    legal_simp
  | select d c a b hd hc ha hb h1 h2 h3 =>
    have := isGp_of_gpOk hd; have := isGp_of_gpOk hc
    have := isGp_of_gpOk ha; have := isGp_of_gpOk hb
    legal_simp
  | setcc m d a b hm hd ha hb =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd; have := isGp_of_gpOk ha; have := isGp_of_gpOk hb
    rcases hm with rfl | rfl <;> legal_simp
  | setccImm m d a v hm hd ha hv =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd; have := isGp_of_gpOk ha
    rcases hm with rfl | rfl <;> legal_simp
  | alu m d s hm hd hs =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd; have := isGp_of_gpOk hs
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> legal_simp
  | aluImm m d v hm hd hv hf =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> legal_simp
  | cmpImm d v hd hv =>
    refine .aluImm _ d v ?_ (isGp_of_gpOk hd)
    show x86AluImm "CMP:64" v = true
    simp only [fitsImm8S, ite_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hv
    simp (config := { decide := true }) [x86AluImm, x86Alu, imm32Fits, LprogBytes.rexW]
    omega
  | shiftImm m d k hm hd hk h0 =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd
    rcases hm with rfl | rfl <;> legal_simp
  | sarImm d k hd hk0 hk => have := isGp_of_gpOk hd; legal_simp
  | shiftReg m d a b hm hd ha hb =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have := isGp_of_gpOk hd; have := isGp_of_gpOk ha; have := isGp_of_gpOk hb
    rcases hm with rfl | rfl <;> legal_simp
  | cast o d a ho hd ha =>
    simp only [castMnems, List.mem_cons, List.not_mem_nil, or_false] at ho
    have := isGp_of_gpOk hd; have := isGp_of_gpOk ha
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> legal_simp
  | tagShift b k d s hb hk0 hk hd hs =>
    refine .unary _ d s ?_ (isGp_of_gpOk hd) (isGp_of_gpOk hs)
    show x86Unary (tagMnem b k) = true
    have hx := tagShiftExt_tagBase hb k
    simp only [x86Unary, stripWidthTag_tagMnem hb, hx]
    split <;> simp
  | shl0 d s hd hs => have := isGp_of_gpOk hd; have := isGp_of_gpOk hs; legal_simp
  | load d n b off hn hd hb hoff =>
    have := isGp_of_gpOk hd
    have hpm : parseMemNameGp n = some (gpNumU b, Int.ofNat off) := by
      rw [parseMemNameGp_cellParts, hn]; simp [isGp_of_gpOk hb]
    refine .memMov _ d n (by decide +kernel) (Or.inl (isGp_of_gpOk hd))
      (Or.inr (Or.inr (by simp [hpm]))) ?_
    show (encMemName d && encMemName n) = false
    simp [encMemName_of_isGpName (isGp_of_gpOk hd)]
  | store n b off s hn hs hb hoff =>
    have hpm : parseMemNameGp n = some (gpNumU b, Int.ofNat off) := by
      rw [parseMemNameGp_cellParts, hn]; simp [isGp_of_gpOk hb]
    refine .memMov _ n s (by decide +kernel) (Or.inr (Or.inr (by simp [hpm])))
      (Or.inl (isGp_of_gpOk hs)) ?_
    show (encMemName n && encMemName s) = false
    simp [encMemName_of_isGpName (isGp_of_gpOk hs)]
  | storeMov n b off s hn hs hb hoff =>
    have hpm : parseMemNameGp n = some (gpNumU b, Int.ofNat off) := by
      rw [parseMemNameGp_cellParts, hn]; simp [isGp_of_gpOk hb]
    refine .mov _ n s (by decide +kernel) (Or.inr (Or.inr (by simp [hpm])))
      (Or.inl (isGp_of_gpOk hs)) ?_
    show (encMemName n && encMemName s) = false
    simp [encMemName_of_isGpName (isGp_of_gpOk hs)]
  | loadMov d n b off hn hd hb hoff =>
    have hpm : parseMemNameGp n = some (gpNumU b, Int.ofNat off) := by
      rw [parseMemNameGp_cellParts, hn]; simp [isGp_of_gpOk hb]
    refine .mov _ d n (by decide +kernel) (Or.inl (isGp_of_gpOk hd))
      (Or.inr (Or.inr (by simp [hpm]))) ?_
    show (encMemName d && encMemName n) = false
    simp [encMemName_of_isGpName (isGp_of_gpOk hd)]
  | leaIdx d b x sc hd hb hx hsc =>
    exact .sibLoad _ d b x sc
      (show x86SibLoad "LEA:64" x sc = true by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsc
        rcases hsc with rfl | rfl | rfl | rfl <;>
          simp (config := { decide := true }) [x86SibLoad, x86SibScale, (gpFacts hx).ne4])
      (isGp_of_gpOk hd)
      (isGp_of_gpOk hb) (isGp_of_gpOk hx)
  | loadIdx d b x hd hb hx =>
    exact .sibLoad _ d b x 8
      (show x86SibLoad "LOADIDX" x 8 = true by
        simp (config := { decide := true }) [x86SibLoad, x86SibScale, (gpFacts hx).ne4])
      (isGp_of_gpOk hd) (isGp_of_gpOk hb) (isGp_of_gpOk hx)
  | storeIdx a b x v hb hx hv =>
    exact .sibStore _ _ b x v 8
      (show x86SibStore "STOREIDX" x 8 = true by
        simp (config := { decide := true }) [x86SibStore, x86SibScale, (gpFacts hx).ne4])
      (isGp_of_gpOk hb) (isGp_of_gpOk hx) (isGp_of_gpOk hv)
  | zeroArr b n hb hn hk =>
    exact .zeroArrSrc b n 64 (show x86ZeroArr n 64 = true by simp [x86ZeroArr, hn, hk])
      (isGp_of_gpOk hb)
  | storeImm d b v k hd hb hv hk =>
    exact .storeImm _ b v k hk (isGp_of_gpOk hb) (isGp_of_gpOk hv)
  | leaFa d q hd hq hdisp =>
    exact .leaFa _ d q (show x86LeaFa "LEA:64" q = true by simp [x86LeaFa, hq])
      (isGp_of_gpOk hd)
  | adcx d a s c hd ha hs hc h1 h2 h3 =>
    exact .carry3 _ d a s c (by decide +kernel) (isGp_of_gpOk hd) (isGp_of_gpOk ha)
      (isGp_of_gpOk hs) (isGp_of_gpOk hc)
  | adcxhi o a s c ho ha hs hc h1 h2 =>
    exact .flagOut _ o _ (show x86FlagOut "ADCXHI:64" [.reg a, .reg s, .reg c] = true by
      simp (config := { decide := true }) [x86FlagOut, isCarryOutBinding]) (isGp_of_gpOk ho)
  | mulx l h s hl hh hs =>
    exact .wideMul _ l h s (by decide +kernel) (isGp_of_gpOk hl) (isGp_of_gpOk hh)
      (isGp_of_gpOk hs)
  | label k l => exact .fixed _ rfl
  | cond cc l h1 h2 => exact .fixed _ rfl

/-- **The gate accepts the legal forms of `GateForm`**: every instruction of `GateForm body`
    other than the return has a legal form of the x86 encoder in the context of `body`, and
    `instrOKWB` accepts it at the parameters of `body`. -/
theorem instrOKWB_of_legalForm {body : Lcmd} {i : LinstrR} (h : GateForm body i) :
    LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx body) i
      ∧ instrOKWB body (Params.ofBody body) i = true :=
  ⟨legalForm_of_gateForm h, instrOKWB_of_gateForm h⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal
