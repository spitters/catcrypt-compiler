/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

/-!
# Byte images with vector instructions

The scalar decoder `LprogBytesDecode.decodeLinstr` accepts no byte string that begins with
the EVEX escape byte `0x62` (`decodeLinstr_evex`) or with the two-byte VEX escape byte `0xC5`
(`decodeLinstr_vex2`). A table of vector encodings whose entries all begin with one of these
bytes can therefore be decoded beside the scalar instructions without ambiguity. The
three-byte VEX escape `0xC4` is not admitted: `decodeLinstr` reads it as the head of the
BMI2 shifts.

`VecAsm` is the table: for each vector instruction `VecMach.VInstr`, its byte string or none
when the instruction has no encoding. The table carries no proof that its entries are the
encodings of the instruction set; the conditions `VecAsm.Lawful` (every entry begins with
`0x62` or `0xC5`, no entry is a prefix of another) are the ones the decoder needs.
`VecAsm.lookup` inverts the table on the front of a byte stream, and `mixedHead` decodes one
instruction of a mixed stream: the table when the next byte is `0x62` or `0xC5`,
`decodeLinstr` otherwise.

`mixedDecode A` extends `LprogBytesDecode.decodeLprog` to mixed streams and `mixedEncode A`
extends `LprogBytesDecode.itemBytes` to programs of scalar positions and vector
instructions. The round trip holds for programs whose vector instructions all have an entry
(`VecAsm.Encodable`). A decoded mixed program is a list over `RInstr ⊕ VInstr`, the
instruction type of `VecMach.x86VecMach`. Offsets are prefix sums of the byte lengths of the
positions, as in the scalar development, so a branch may cross vector instructions when its
displacement lands on the byte offset of its label (`mixedBranchOK`).

`VecAsm.Faithful` states that a processor, given as a relation between a byte image and two
machine states, runs every image as `x86VecMach` runs the program `mixedDecode` reads from
it. It is a definition, used as a hypothesis.

`IsaMachine.withDecode M d` is the machine `M` with the decoder `d`; the runs of a decoded
program do not mention the decoder, so they are those of `M`. `mixedMach A r m` is
`x86VecMach r m` with the decoder `mixedDecode A`: the machine of mixed images. On a byte
string the scalar decoder accepts it decodes the same program, so a halting run of a scalar
image on `X86Isa.x86Mach` is a halting run on `mixedMach`, the vector state unchanged, and
`VecAsm.Faithful` is the statement that the processor runs every image as `mixedMach` does.

## Main definitions

* `evexEscape`, `vex2Escape`: the bytes `0x62` and `0xC5`.
* `VecAsm`, `VecAsm.bytes`, `VecAsm.Encodable`, `VecAsm.Lawful`, `VecAsm.lookup`: the
  table of vector encodings, the bytes of an entry, the instructions with an entry, the
  side conditions of the table, and its inverse on the front of a stream.
* `mixedHead`, `mixedStream`, `mixedResolve`, `mixedDecode`: the decoder of mixed streams.
* `MixedItem`, `MixedItemOK`, `mixedLayout`, `mixedExpected`, `mixedBranchOK`: positions of
  an assembled mixed program, the program they denote and the well-formedness of branches.
* `mixedItems`, `mixedEncode`: the encoder of a program of scalar positions and vector
  instructions.
* `VecAsm.Faithful`: the processor runs a mixed image as `x86VecMach` runs its decoding.
* `IsaMachine.withDecode`, `mixedMach`: a machine with another decoder, and the x86 machine
  with vector registers and the mixed decoder.

## Main results

* `decodeLinstr_evex`, `decodeLinstr_vex2`: `decodeLinstr (0x62 :: bs) = none` and
  `decodeLinstr (0xC5 :: bs) = none`.
* `ItemOK.ne_evex`, `ItemOK.ne_vex2`: the bytes of a scalar position do not begin with
  `0x62` or `0xC5`.
* `VecAsm.Lawful.unique`: a stream has at most one table entry in front.
* `VecAsm.Lawful.lookup_enc`, `VecAsm.lookup_sound`: the table inverse on an entry, and the
  bytes of an instruction it returns.
* `mixedHead_of_decodeLinstr`, `VecAsm.Lawful.mixedHead_enc`: the mixed decoder on a scalar
  instruction and on a table entry.
* `mixedDecode_items`: the stream of a well-formed list of mixed positions decodes to the
  program the list denotes.
* `mixedDecode_mixedEncode`: the round trip of `mixedEncode`.
* `mixedDecode_of_decodeLprog`: on a stream `decodeLprog` decodes, `mixedDecode` returns the
  same program.
* `mixedEncode_scalar`, `mixedEncode_itemsFrom`, `mixedDecode_encodeLcmd`: on a program
  without vector instructions the encoder is the scalar one, and the scalar body round trip
  is an instance.
* `VecAsm.Faithful.scalar`: a faithful processor runs every scalar image as `x86VecMach`
  runs the program `decodeLprog` reads from it.
* `VecAsm.Faithful.vexec`: a faithful processor runs the entry of `v` followed by `ret` as
  `vexec v`.
* `IsaMachine.withDecode_runL`, `IsaMachine.withDecode_haltsC`,
  `IsaMachine.withDecode_halts`: the runs of a machine do not depend on its decoder.
* `IsaMachine.withOps_halts_inl`: a call-free halting run of the base machine on the
  extended machine.
* `mixedMach_decode`, `mixedMach_runL`, `mixedMach_haltsC`, `mixedMach_halts`: the decoder
  of `mixedMach` is `mixedDecode`, and its runs are those of `x86VecMach`.
* `mixedMach_decode_of_decodeLprog`, `mixedMach_decode_of_x86VecMach`: `mixedMach` decodes
  a scalar image to the program the scalar decoder reads.
* `mixedMach_haltsC_of_x86Mach`, `mixedMach_halts_of_x86Mach`, `mixedMach_runL_of_x86Mach`:
  a decoded halting run of a scalar image on `x86Mach` is one on `mixedMach`, the vector
  state unchanged.
* `VecAsm.faithful_iff_mixedMach`: `VecAsm.Faithful` as a statement about `mixedMach`.
* `mixedMach_decode_mixedEncode`: the round trip of `mixedEncode` on `mixedMach`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LLabel Lcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (isRex decodeJ1 decodeJ1_6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (VInstr VState vexec x86VecMach
  x86VecMach_decode)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime)

/-! ## 1. The scalar decoder rejects the EVEX escape byte -/

/-- The EVEX escape byte `0x62`. -/
def evexEscape : BitVec 8 := BitVec.ofNat 8 0x62

/-- `decodeJ1_6` rejects every stream that begins with `0x62`. -/
theorem decodeJ1_6_evex (bs : List (BitVec 8)) : decodeJ1_6 (evexEscape :: bs) = none := by
  rw [decodeJ1_6_of_not_rex (show isRex evexEscape = false by decide)]
  rfl

/-- **The scalar decoder rejects the EVEX escape byte.** No byte string that begins with
    `0x62` decodes to a scalar instruction. -/
theorem decodeLinstr_evex (bs : List (BitVec 8)) : decodeLinstr (evexEscape :: bs) = none := by
  simp only [decodeLinstr, decodeJ1_6_evex]
  rfl

/-- A stream the scalar decoder accepts does not begin with `0x62`. -/
theorem head?_ne_evex {bs : List (BitVec 8)} {p : DInstr × List (BitVec 8)}
    (h : decodeLinstr bs = some p) : bs.head? ≠ some evexEscape := by
  intro hh
  cases bs with
  | nil => simp at hh
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [decodeLinstr_evex] at h
    cases h

/-- The bytes of a scalar position do not begin with `0x62`. -/
theorem ItemOK.ne_evex {it : Item} (h : ItemOK it) : it.bytes.head? ≠ some evexEscape := by
  unfold ItemOK at h
  cases hdec : it.dec with
  | none =>
    rw [hdec] at h
    rw [show it.bytes = [] from h]
    simp
  | some x =>
    rw [hdec] at h
    have h0 := h.2 []
    rw [List.append_nil] at h0
    exact head?_ne_evex h0

/-- The two-byte VEX escape byte `0xC5`. -/
def vex2Escape : BitVec 8 := BitVec.ofNat 8 0xc5

/-- `decodeJ1_6` rejects every stream that begins with `0xC5`. -/
theorem decodeJ1_6_vex2 (bs : List (BitVec 8)) : decodeJ1_6 (vex2Escape :: bs) = none := by
  rw [decodeJ1_6_of_not_rex (show isRex vex2Escape = false by decide)]
  rfl

/-- **The scalar decoder rejects the two-byte VEX escape byte.** No byte string that begins
    with `0xC5` decodes to a scalar instruction. -/
theorem decodeLinstr_vex2 (bs : List (BitVec 8)) : decodeLinstr (vex2Escape :: bs) = none := by
  simp only [decodeLinstr, decodeJ1_6_vex2]
  rfl

/-- A stream the scalar decoder accepts does not begin with `0xC5`. -/
theorem head?_ne_vex2 {bs : List (BitVec 8)} {p : DInstr × List (BitVec 8)}
    (h : decodeLinstr bs = some p) : bs.head? ≠ some vex2Escape := by
  intro hh
  cases bs with
  | nil => simp at hh
  | cons b t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [decodeLinstr_vex2] at h
    cases h

/-- The bytes of a scalar position do not begin with `0xC5`. -/
theorem ItemOK.ne_vex2 {it : Item} (h : ItemOK it) : it.bytes.head? ≠ some vex2Escape := by
  unfold ItemOK at h
  cases hdec : it.dec with
  | none =>
    rw [hdec] at h
    rw [show it.bytes = [] from h]
    simp
  | some x =>
    rw [hdec] at h
    have h0 := h.2 []
    rw [List.append_nil] at h0
    exact head?_ne_vex2 h0

/-- A byte that opens a vector instruction: `0x62` or `0xC5`. -/
def VecHead (bs : List (BitVec 8)) : Prop :=
  bs.head? = some evexEscape ∨ bs.head? = some vex2Escape

instance (bs : List (BitVec 8)) : Decidable (VecHead bs) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A stream the scalar decoder accepts does not open a vector instruction. -/
theorem not_vecHead {bs : List (BitVec 8)} {p : DInstr × List (BitVec 8)}
    (h : decodeLinstr bs = some p) : ¬ VecHead bs := by
  rintro (hh | hh)
  · exact head?_ne_evex h hh
  · exact head?_ne_vex2 h hh

/-! ## 2. The table of vector encodings -/

/-- **The table of vector encodings**: the byte string of each vector instruction, or none
    when the instruction has no encoding. -/
structure VecAsm where
  /-- The bytes of a vector instruction. -/
  enc : VInstr → Option (List (BitVec 8))

namespace VecAsm

variable {A : VecAsm}

/-- The bytes of the entry of `v`, empty when `v` has no entry. -/
def bytes (A : VecAsm) (v : VInstr) : List (BitVec 8) := (A.enc v).getD []

/-- The instruction `v` has an entry. -/
def Encodable (A : VecAsm) (v : VInstr) : Prop := ∃ bs, A.enc v = some bs

/-- The entry of an encodable instruction is its bytes. -/
theorem Encodable.enc_eq {v : VInstr} (h : A.Encodable v) : A.enc v = some (A.bytes v) := by
  obtain ⟨bs, hb⟩ := h
  simp [bytes, hb]

/-- The side conditions of a table: every entry begins with the EVEX escape byte `0x62` or
    the two-byte VEX escape byte `0xC5`, and an entry that is a prefix of another is that
    entry. -/
structure Lawful (A : VecAsm) : Prop where
  /-- Every entry begins with `0x62` or `0xC5`. -/
  escape : ∀ v bs, A.enc v = some bs →
    ∃ t, bs = evexEscape :: t ∨ bs = vex2Escape :: t
  /-- An entry that is a prefix of the entry of `w` is the entry of `w`, for `w` itself. -/
  prefixFree : ∀ v w bv bw, A.enc v = some bv → A.enc w = some bw → bv <+: bw → v = w

/-- An entry opens a vector instruction. -/
theorem Lawful.vecHead (hA : A.Lawful) {v : VInstr} {bs : List (BitVec 8)}
    (h : A.enc v = some bs) (rest : List (BitVec 8)) : VecHead (bs ++ rest) := by
  obtain ⟨t, ht | ht⟩ := hA.escape v bs h <;> subst ht
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An entry is not empty. -/
theorem Lawful.ne_nil (hA : A.Lawful) {v : VInstr} {bs : List (BitVec 8)}
    (h : A.enc v = some bs) : bs ≠ [] := by
  obtain ⟨t, ht | ht⟩ := hA.escape v bs h <;> subst ht <;> exact List.cons_ne_nil _ _

/-- Distinct instructions have distinct entries. -/
theorem Lawful.enc_inj (hA : A.Lawful) {v w : VInstr} {bs : List (BitVec 8)}
    (hv : A.enc v = some bs) (hw : A.enc w = some bs) : v = w :=
  hA.prefixFree v w bs bs hv hw (List.prefix_refl _)

/-- **Unique decodability.** Two entries in front of two continuations give the same stream
    only when the instructions and the continuations agree. -/
theorem Lawful.unique (hA : A.Lawful) {v w : VInstr} {bv bw r s : List (BitVec 8)}
    (hv : A.enc v = some bv) (hw : A.enc w = some bw) (h : bv ++ r = bw ++ s) :
    v = w ∧ r = s := by
  have hvw : v = w := by
    rcases List.append_eq_append_iff.mp h with ⟨a, ha, _⟩ | ⟨c, hc, _⟩
    · exact hA.prefixFree v w bv bw hv hw ⟨a, ha.symm⟩
    · exact (hA.prefixFree w v bw bv hw hv ⟨c, hc.symm⟩).symm
  subst hvw
  rw [hv] at hw
  cases hw
  exact ⟨rfl, List.append_cancel_left h⟩

open Classical in
/-- The inverse of the table on the front of a stream: an instruction whose entry is a
    prefix of the stream, with the bytes that follow. -/
noncomputable def lookup (A : VecAsm) (bs : List (BitVec 8)) :
    Option (VInstr × List (BitVec 8)) :=
  if h : ∃ p : VInstr × List (BitVec 8) × List (BitVec 8),
      A.enc p.1 = some p.2.1 ∧ bs = p.2.1 ++ p.2.2 then
    some ((Classical.choose h).1, (Classical.choose h).2.2)
  else none

/-- The stream of an instruction `lookup` returns is its entry and the remaining bytes. -/
theorem lookup_sound {bs : List (BitVec 8)} {p : VInstr × List (BitVec 8)}
    (h : A.lookup bs = some p) : ∃ e, A.enc p.1 = some e ∧ bs = e ++ p.2 := by
  unfold lookup at h
  split at h
  · rename_i hex
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, Classical.choose_spec hex⟩
  · cases h

/-- `lookup` on an entry in front of a continuation returns the instruction and the
    continuation. -/
theorem Lawful.lookup_enc (hA : A.Lawful) {v : VInstr} {bs : List (BitVec 8)}
    (hv : A.enc v = some bs) (rest : List (BitVec 8)) :
    A.lookup (bs ++ rest) = some (v, rest) := by
  have hex : ∃ p : VInstr × List (BitVec 8) × List (BitVec 8),
      A.enc p.1 = some p.2.1 ∧ bs ++ rest = p.2.1 ++ p.2.2 :=
    ⟨(v, bs, rest), hv, rfl⟩
  obtain ⟨h1, h2⟩ := hA.unique hv (Classical.choose_spec hex).1 (Classical.choose_spec hex).2
  unfold lookup
  rw [dif_pos hex]
  exact congrArg some (Prod.ext h1.symm h2.symm)

end VecAsm

/-! ## 3. One instruction of a mixed stream -/

/-- Decode the instruction at the front of a mixed stream: the table when the next byte is
    `0x62` or `0xC5`, the scalar decoder `decodeLinstr` otherwise. -/
noncomputable def mixedHead (A : VecAsm) (bs : List (BitVec 8)) :
    Option ((DInstr ⊕ VInstr) × List (BitVec 8)) :=
  if VecHead bs then (A.lookup bs).map fun p => (Sum.inr p.1, p.2)
  else (decodeLinstr bs).map fun p => (Sum.inl p.1, p.2)

/-- `mixedHead` extends `decodeLinstr`: on a stream the scalar decoder accepts, it returns
    the same instruction and the same remaining bytes. -/
theorem mixedHead_of_decodeLinstr (A : VecAsm) {bs r : List (BitVec 8)} {x : DInstr}
    (h : decodeLinstr bs = some (x, r)) : mixedHead A bs = some (Sum.inl x, r) := by
  simp only [mixedHead, if_neg (not_vecHead h), h, Option.map_some]

/-- `mixedHead` on a table entry in front of a continuation returns the instruction and the
    continuation. -/
theorem VecAsm.Lawful.mixedHead_enc {A : VecAsm} (hA : A.Lawful) {v : VInstr}
    {bs : List (BitVec 8)} (hv : A.enc v = some bs) (rest : List (BitVec 8)) :
    mixedHead A (bs ++ rest) = some (Sum.inr v, rest) := by
  simp only [mixedHead, if_pos (hA.vecHead hv rest), hA.lookup_enc hv, Option.map_some]

/-- A vector instruction `mixedHead` returns was read from its table entry. -/
theorem mixedHead_inr {A : VecAsm} {bs r : List (BitVec 8)} {v : VInstr}
    (h : mixedHead A bs = some (Sum.inr v, r)) : ∃ e, A.enc v = some e ∧ bs = e ++ r := by
  unfold mixedHead at h
  split at h
  · cases hl : A.lookup bs with
    | none => rw [hl] at h; simp at h
    | some p =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact VecAsm.lookup_sound hl
  · cases hd : decodeLinstr bs with
    | none => rw [hd] at h; simp at h
    | some p => rw [hd] at h; simp at h

/-- A scalar instruction `mixedHead` returns is the one `decodeLinstr` returns. -/
theorem mixedHead_inl {A : VecAsm} {bs r : List (BitVec 8)} {x : DInstr}
    (h : mixedHead A bs = some (Sum.inl x, r)) : decodeLinstr bs = some (x, r) := by
  unfold mixedHead at h
  split at h
  · cases hl : A.lookup bs with
    | none => rw [hl] at h; simp at h
    | some p => rw [hl] at h; simp at h
  · cases hd : decodeLinstr bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      rw [hd] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-! ## 4. Mixed positions and the stream decoder -/

/-- One position of an assembled mixed program: its bytes, the scalar or vector instruction
    they decode to (none for a position that carries no bytes), the label the position
    defines, and the label a branch at the position targets. -/
structure MixedItem where
  /-- The bytes of the position. -/
  bytes : List (BitVec 8)
  /-- The instruction the bytes decode to. -/
  dec : Option (DInstr ⊕ VInstr)
  /-- The label the position defines. -/
  label : Option LLabel := none
  /-- The label a branch at the position targets. -/
  target : Option LLabel := none

/-- A position without bytes decodes to nothing; a position with bytes decodes, in front of
    any continuation, to its instruction and that continuation. -/
def MixedItemOK (A : VecAsm) (it : MixedItem) : Prop :=
  match it.dec with
  | none => it.bytes = []
  | some x => it.bytes ≠ [] ∧ ∀ rest, mixedHead A (it.bytes ++ rest) = some (x, rest)

/-- The byte stream of a list of mixed positions. -/
def mixedBytes (items : List MixedItem) : List (BitVec 8) := items.flatMap (·.bytes)

/-- The decoded instructions of a list of mixed positions with their start and end
    offsets. -/
def mixedLayout : Nat → List MixedItem → List (Nat × Nat × (DInstr ⊕ VInstr))
  | _, [] => []
  | off, it :: rest =>
      match it.dec with
      | none => mixedLayout (off + it.bytes.length) rest
      | some x =>
          (off, off + it.bytes.length, x) :: mixedLayout (off + it.bytes.length) rest

/-- Decode a whole mixed stream into instructions tagged with their start and end offsets;
    the fuel bounds the instruction count. -/
noncomputable def mixedStream (A : VecAsm) :
    Nat → Nat → List (BitVec 8) → Option (List (Nat × Nat × (DInstr ⊕ VInstr)))
  | 0, _, bs => if bs.isEmpty then some [] else none
  | n + 1, off, bs =>
      if bs.isEmpty then some []
      else
        match mixedHead A bs with
        | some (x, r) =>
            (mixedStream A n (off + (bs.length - r.length)) r).map
              ((off, off + (bs.length - r.length), x) :: ·)
        | none => none

/-- Replace each branch displacement of a mixed layout by the index of the instruction that
    starts at the target offset; a vector instruction is kept. -/
def mixedResolve (xs : List (Nat × Nat × (DInstr ⊕ VInstr))) :
    List (Nat × Nat × (DInstr ⊕ VInstr)) → Option (List (RInstr ⊕ VInstr))
  | [] => some []
  | (_, e, x) :: rest =>
      match x with
      | .inr v => (mixedResolve xs rest).map (Sum.inr v :: ·)
      | .inl (.op i) => (mixedResolve xs rest).map (Sum.inl (.op i) :: ·)
      | .inl .ret => (mixedResolve xs rest).map (Sum.inl .ret :: ·)
      | .inl (.push r) => (mixedResolve xs rest).map (Sum.inl (.push r) :: ·)
      | .inl (.pop r) => (mixedResolve xs rest).map (Sum.inl (.pop r) :: ·)
      | .inl (.jcc cc d) =>
          match xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
          | some j => (mixedResolve xs rest).map (Sum.inl (.jcc cc j) :: ·)
          | none => none
      | .inl (.call d) =>
          match xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
          | some j => (mixedResolve xs rest).map (Sum.inl (.call j) :: ·)
          | none => none

/-- Decode a mixed byte stream to a program with index-resolved branches. It extends
    `LprogBytesDecode.decodeLprog` by the table arm of `mixedHead`. -/
noncomputable def mixedDecode (A : VecAsm) (bs : List (BitVec 8)) :
    Option (List (RInstr ⊕ VInstr)) :=
  (mixedStream A bs.length 0 bs).bind fun xs => mixedResolve xs xs

/-- The number of decoded instructions of a list of mixed positions. -/
def mixedCount : List MixedItem → Nat
  | [] => 0
  | it :: rest => (if it.dec.isSome then 1 else 0) + mixedCount rest

/-- The position of the first definition of label `l`: the index of the next decoded
    instruction and the byte offset, counted from `j` and `off`. -/
def mixedLabelPos (l : LLabel) : Nat → Nat → List MixedItem → Option (Nat × Nat)
  | _, _, [] => none
  | j, off, it :: rest =>
      if it.label = some l then some (j, off)
      else mixedLabelPos l (if it.dec.isSome then j + 1 else j) (off + it.bytes.length) rest

/-- The program a list of mixed positions denotes: each branch carries the index of the
    instruction following its target label's definition. -/
def mixedExpected (all : List MixedItem) : List MixedItem → Option (List (RInstr ⊕ VInstr))
  | [] => some []
  | it :: rest =>
      match it.dec with
      | none => mixedExpected all rest
      | some (.inr v) => (mixedExpected all rest).map (Sum.inr v :: ·)
      | some (.inl (.op i)) => (mixedExpected all rest).map (Sum.inl (.op i) :: ·)
      | some (.inl .ret) => (mixedExpected all rest).map (Sum.inl .ret :: ·)
      | some (.inl (.push r)) => (mixedExpected all rest).map (Sum.inl (.push r) :: ·)
      | some (.inl (.pop r)) => (mixedExpected all rest).map (Sum.inl (.pop r) :: ·)
      | some (.inl (.jcc cc _)) =>
          match it.target.bind (fun l => mixedLabelPos l 0 0 all) with
          | some (j, _) => (mixedExpected all rest).map (Sum.inl (.jcc cc j) :: ·)
          | none => none
      | some (.inl (.call _)) =>
          match it.target.bind (fun l => mixedLabelPos l 0 0 all) with
          | some (j, _) => (mixedExpected all rest).map (Sum.inl (.call j) :: ·)
          | none => none

/-- Well-formedness of the branches of `items`, laid out from offset `off` inside `all`:
    every branch names a label that `all` defines, an instruction follows that definition,
    and the branch displacement added to the end of the branch is the byte offset of the
    definition. The offsets count the bytes of vector instructions too. -/
def mixedBranchOK (all : List MixedItem) : Nat → List MixedItem → Bool
  | _, [] => true
  | off, it :: rest =>
      (match it.dec with
        | some (.inl (.jcc _ d)) =>
            match it.target.bind (fun l => mixedLabelPos l 0 0 all) with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && decide (j < mixedCount all)
            | none => false
        | some (.inl (.call d)) =>
            match it.target.bind (fun l => mixedLabelPos l 0 0 all) with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && decide (j < mixedCount all)
            | none => false
        | _ => true)
      && mixedBranchOK all (off + it.bytes.length) rest

theorem mixedStream_nil (A : VecAsm) (n off : Nat) : mixedStream A n off [] = some [] := by
  cases n <;> rfl

/-- The stream of a list of mixed positions decodes to its layout. -/
theorem mixedStream_items (A : VecAsm) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it) :
    ∀ n off, (mixedLayout off items).length ≤ n →
      mixedStream A n off (mixedBytes items) = some (mixedLayout off items) := by
  induction items with
  | nil => intro n off _; exact mixedStream_nil A n off
  | cons it rest ih =>
    intro n off hn
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold MixedItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      simp only [mixedLayout, hdec, hit, List.length_nil, Nat.add_zero] at hn ⊢
      simpa [mixedBytes, hit] using ih' n off hn
    | some x =>
      rw [hdec] at hit
      obtain ⟨hne, hdecode⟩ := hit
      simp only [mixedLayout, hdec, List.length_cons] at hn ⊢
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hbs : mixedBytes (it :: rest) = it.bytes ++ mixedBytes rest := by
        simp [mixedBytes]
      have hemp : (it.bytes ++ mixedBytes rest).isEmpty = false := by
        cases hb : it.bytes with
        | nil => exact absurd hb hne
        | cons b t => rfl
      have hlen : (it.bytes ++ mixedBytes rest).length - (mixedBytes rest).length
          = it.bytes.length := by
        rw [List.length_append]; omega
      rw [hbs, mixedStream, hemp]
      simp only [Bool.false_eq_true, if_false, hdecode, hlen]
      rw [ih' m (off + it.bytes.length) (by omega)]
      rfl

theorem mixedLayout_length (items : List MixedItem) :
    ∀ off, (mixedLayout off items).length = mixedCount items := by
  induction items with
  | nil => intro off; rfl
  | cons it rest ih =>
    intro off
    cases hdec : it.dec with
    | none => simp [mixedLayout, mixedCount, hdec, ih]
    | some x => simp [mixedLayout, mixedCount, hdec, ih]; omega

theorem mixedLayout_start_ge (items : List MixedItem) :
    ∀ off y, y ∈ mixedLayout off items → off ≤ y.1 := by
  induction items with
  | nil => intro off y hy; simp [mixedLayout] at hy
  | cons it rest ih =>
    intro off y hy
    cases hdec : it.dec with
    | none =>
      simp only [mixedLayout, hdec] at hy
      have := ih _ y hy; omega
    | some x =>
      simp only [mixedLayout, hdec, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · have := ih _ y hy; omega

theorem mixedLayout_pairwise (A : VecAsm) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it) :
    ∀ off, (mixedLayout off items).Pairwise (fun a b => a.1 < b.1) := by
  induction items with
  | nil => intro off; simp [mixedLayout]
  | cons it rest ih =>
    intro off
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold MixedItemOK at hit
    cases hdec : it.dec with
    | none => simpa [mixedLayout, hdec] using ih' _
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp only [mixedLayout, hdec, List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih' _⟩
      have := mixedLayout_start_ge rest _ y hy
      show off < y.1
      omega

theorem mixedLayout_head_start (A : VecAsm) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it) :
    ∀ off y, (mixedLayout off items)[0]? = some y → y.1 = off := by
  induction items with
  | nil => intro off y hy; simp [mixedLayout] at hy
  | cons it rest ih =>
    intro off y hy
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold MixedItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      simp only [mixedLayout, hdec, hit, List.length_nil, Nat.add_zero] at hy
      exact ih' off y hy
    | some x =>
      simp only [mixedLayout, hdec, List.getElem?_cons_zero, Option.some.injEq] at hy
      rw [← hy]

theorem mixedLayout_labelPos (A : VecAsm) (l : LLabel) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it) :
    ∀ j0 off0 j t, mixedLabelPos l j0 off0 items = some (j, t) →
      j0 ≤ j ∧ ∀ y, (mixedLayout off0 items)[j - j0]? = some y → y.1 = t := by
  induction items with
  | nil => intro j0 off0 j t h; simp [mixedLabelPos] at h
  | cons it rest ih =>
    intro j0 off0 j t h
    have hit := hok it List.mem_cons_self
    have hrest : ∀ j ∈ rest, MixedItemOK A j := fun j hj => hok j (List.mem_cons_of_mem _ hj)
    have ih' := ih hrest
    simp only [mixedLabelPos] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, fun y hy => ?_⟩
      rw [Nat.sub_self] at hy
      exact mixedLayout_head_start A (it :: rest) hok _ y hy
    · unfold MixedItemOK at hit
      cases hdec : it.dec with
      | none =>
        rw [hdec] at hit
        simp only [hdec, Option.isSome_none, Bool.false_eq_true, if_false, hit,
          List.length_nil, Nat.add_zero] at h
        obtain ⟨hle, hy⟩ := ih' j0 off0 j t h
        refine ⟨hle, fun y hyy => hy y ?_⟩
        simpa [mixedLayout, hdec, hit] using hyy
      | some x =>
        simp only [hdec, Option.isSome_some, if_true] at h
        obtain ⟨hle, hy⟩ := ih' (j0 + 1) _ j t h
        refine ⟨by omega, fun y hyy => hy y ?_⟩
        have hj : j - j0 = (j - (j0 + 1)) + 1 := by omega
        simpa [mixedLayout, hdec, hj] using hyy

/-- In a list with strictly increasing first components, the first entry whose first
    component is that of the entry at index `k` is at index `k`. -/
theorem findIdx?_start_of_pairwise {α : Type} (xs : List (Nat × α))
    (hp : xs.Pairwise (fun a b => a.1 < b.1)) :
    ∀ k y, xs[k]? = some y →
      xs.findIdx? (fun z => decide ((z.1 : Int) = (y.1 : Int))) = some k := by
  induction xs with
  | nil => intro k y h; simp at h
  | cons a t ih =>
    intro k y h
    rw [List.pairwise_cons] at hp
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [List.findIdx?_cons]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have hmem : y ∈ t := List.mem_of_getElem? h
      have hlt := hp.1 y hmem
      have hne : ¬ ((a.1 : Int) = (y.1 : Int)) := by omega
      rw [List.findIdx?_cons]
      simp only [hne, decide_false, Bool.false_eq_true, if_false, ih hp.2 k y h,
        Option.map_some]

/-- The instruction that follows the definition of a branch target is found in the layout
    by the byte offset of the definition. -/
theorem mixedLayout_find (A : VecAsm) (all : List MixedItem)
    (hok : ∀ it ∈ all, MixedItemOK A it) {tgt : Option LLabel} {j t : Nat}
    (htgt : tgt.bind (fun l => mixedLabelPos l 0 0 all) = some (j, t))
    (hj : j < mixedCount all) :
    (mixedLayout 0 all).findIdx? (fun y => decide ((y.1 : Int) = (t : Int))) = some j := by
  obtain ⟨l, hl⟩ : ∃ l, mixedLabelPos l 0 0 all = some (j, t) := by
    cases htg : tgt with
    | none => rw [htg] at htgt; simp at htgt
    | some l => exact ⟨l, by simpa [htg] using htgt⟩
  have hlen := mixedLayout_length all 0
  obtain ⟨y, hy⟩ : ∃ y, (mixedLayout 0 all)[j]? = some y := by
    have : j < (mixedLayout 0 all).length := by omega
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have hy1 : y.1 = t := (mixedLayout_labelPos A l all hok 0 0 j t hl).2 y (by simpa using hy)
  have hfind := findIdx?_start_of_pairwise _ (mixedLayout_pairwise A all hok 0) j y hy
  rwa [hy1] at hfind

/-- Resolving the layout of `items` inside `all` yields the program `items` denotes. -/
theorem mixedResolve_layout (A : VecAsm) (all : List MixedItem)
    (hok : ∀ it ∈ all, MixedItemOK A it) :
    ∀ items off, mixedBranchOK all off items = true →
      mixedResolve (mixedLayout 0 all) (mixedLayout off items) = mixedExpected all items := by
  intro items
  induction items with
  | nil => intro off _; rfl
  | cons it rest ih =>
    intro off hbr
    simp only [mixedBranchOK, Bool.and_eq_true] at hbr
    obtain ⟨hhead, htail⟩ := hbr
    have ih' := ih _ htail
    cases hdec : it.dec with
    | none => simpa [mixedLayout, mixedExpected, hdec] using ih'
    | some x =>
      cases x with
      | inr v => simp [mixedLayout, mixedExpected, hdec, mixedResolve, ih']
      | inl x =>
        cases x with
        | op i => simp [mixedLayout, mixedExpected, hdec, mixedResolve, ih']
        | ret => simp [mixedLayout, mixedExpected, hdec, mixedResolve, ih']
        | push r => simp [mixedLayout, mixedExpected, hdec, mixedResolve, ih']
        | pop r => simp [mixedLayout, mixedExpected, hdec, mixedResolve, ih']
        | jcc cc d =>
          rw [hdec] at hhead
          simp only at hhead
          cases htgt : it.target.bind (fun l => mixedLabelPos l 0 0 all) with
          | none => rw [htgt] at hhead; simp at hhead
          | some p =>
            obtain ⟨j, t⟩ := p
            rw [htgt] at hhead
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
            obtain ⟨ht, hj⟩ := hhead
            have hfind := mixedLayout_find A all hok htgt hj
            rw [ht] at hfind
            simp only [mixedLayout, mixedExpected, hdec, mixedResolve, htgt, hfind, ih']
        | call d =>
          rw [hdec] at hhead
          simp only at hhead
          cases htgt : it.target.bind (fun l => mixedLabelPos l 0 0 all) with
          | none => rw [htgt] at hhead; simp at hhead
          | some p =>
            obtain ⟨j, t⟩ := p
            rw [htgt] at hhead
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
            obtain ⟨ht, hj⟩ := hhead
            have hfind := mixedLayout_find A all hok htgt hj
            rw [ht] at hfind
            simp only [mixedLayout, mixedExpected, hdec, mixedResolve, htgt, hfind, ih']

theorem mixedCount_le_bytes (A : VecAsm) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it) :
    mixedCount items ≤ (mixedBytes items).length := by
  induction items with
  | nil => simp [mixedCount]
  | cons it rest ih =>
    have hit := hok it List.mem_cons_self
    have ih' := ih (fun j hj => hok j (List.mem_cons_of_mem _ hj))
    unfold MixedItemOK at hit
    have hbs : mixedBytes (it :: rest) = it.bytes ++ mixedBytes rest := by simp [mixedBytes]
    rw [hbs, List.length_append]
    cases hdec : it.dec with
    | none => simp [mixedCount, hdec]; omega
    | some x =>
      rw [hdec] at hit
      have hpos : 0 < it.bytes.length := List.length_pos_iff.mpr hit.1
      simp [mixedCount, hdec]; omega

/-- **Round trip of mixed positions.** The byte stream of a well-formed list of mixed
    positions decodes to the program the list denotes. -/
theorem mixedDecode_items (A : VecAsm) (items : List MixedItem)
    (hok : ∀ it ∈ items, MixedItemOK A it)
    (hbr : mixedBranchOK items 0 items = true) :
    mixedDecode A (mixedBytes items) = mixedExpected items items := by
  have hfuel : (mixedLayout 0 items).length ≤ (mixedBytes items).length := by
    rw [mixedLayout_length]; exact mixedCount_le_bytes A items hok
  rw [mixedDecode, mixedStream_items A items hok _ 0 hfuel]
  exact mixedResolve_layout A items hok items 0 hbr

/-! ## 5. The encoder of mixed programs and its round trip -/

/-- A scalar position as a mixed position. -/
def MixedItem.ofScalar (it : Item) : MixedItem :=
  { bytes := it.bytes, dec := it.dec.map Sum.inl, label := it.label, target := it.target }

/-- The position of a vector instruction: the bytes of its table entry. -/
def VecAsm.item (A : VecAsm) (v : VInstr) : MixedItem :=
  { bytes := A.bytes v, dec := some (Sum.inr v) }

/-- The mixed positions of a program of scalar positions and vector instructions. A label
    in front of a vector instruction is a scalar position without bytes. -/
def mixedItems (A : VecAsm) (prog : List (Item ⊕ VInstr)) : List MixedItem :=
  prog.map (Sum.elim MixedItem.ofScalar A.item)

/-- The bytes of a program of scalar positions and vector instructions: the bytes of each
    scalar position, which the scalar encoder produced, and the bytes of the table entry of
    each vector instruction. It extends `LprogBytesDecode.itemBytes`. -/
def mixedEncode (A : VecAsm) (prog : List (Item ⊕ VInstr)) : List (BitVec 8) :=
  prog.flatMap (Sum.elim Item.bytes A.bytes)

theorem mixedBytes_mixedItems (A : VecAsm) (prog : List (Item ⊕ VInstr)) :
    mixedBytes (mixedItems A prog) = mixedEncode A prog := by
  induction prog with
  | nil => rfl
  | cons a rest ih =>
    have h : mixedBytes (mixedItems A (a :: rest))
        = Sum.elim Item.bytes A.bytes a ++ mixedBytes (mixedItems A rest) := by
      cases a <;> simp [mixedBytes, mixedItems, MixedItem.ofScalar, VecAsm.item]
    rw [h, ih]
    simp [mixedEncode]

/-- A well-formed scalar position is a well-formed mixed position. -/
theorem MixedItemOK.ofScalar (A : VecAsm) {it : Item} (h : ItemOK it) :
    MixedItemOK A (MixedItem.ofScalar it) := by
  unfold ItemOK at h
  unfold MixedItemOK MixedItem.ofScalar
  cases hdec : it.dec with
  | none => rw [hdec] at h; exact h
  | some x =>
    rw [hdec] at h
    exact ⟨h.1, fun rest => mixedHead_of_decodeLinstr A (h.2 rest)⟩

/-- The position of an encodable vector instruction of a lawful table is well formed. -/
theorem VecAsm.Lawful.item_ok {A : VecAsm} (hA : A.Lawful) {v : VInstr}
    (hv : A.Encodable v) : MixedItemOK A (A.item v) :=
  ⟨hA.ne_nil hv.enc_eq, fun rest => hA.mixedHead_enc hv.enc_eq rest⟩

/-- **Round trip of mixed programs.** For a lawful table, the bytes of a program of
    well-formed scalar positions and encodable vector instructions, with well-formed
    branches, decode to the program its positions denote. -/
theorem mixedDecode_mixedEncode {A : VecAsm} (hA : A.Lawful) (prog : List (Item ⊕ VInstr))
    (hok : ∀ it, Sum.inl it ∈ prog → ItemOK it)
    (hv : ∀ v, Sum.inr v ∈ prog → A.Encodable v)
    (hbr : mixedBranchOK (mixedItems A prog) 0 (mixedItems A prog) = true) :
    mixedDecode A (mixedEncode A prog)
      = mixedExpected (mixedItems A prog) (mixedItems A prog) := by
  rw [← mixedBytes_mixedItems]
  refine mixedDecode_items A _ ?_ hbr
  intro it hit
  simp only [mixedItems, List.mem_map] at hit
  obtain ⟨src, hsrc, rfl⟩ := hit
  cases src with
  | inl i => exact MixedItemOK.ofScalar A (hok i hsrc)
  | inr v => exact hA.item_ok (hv v hsrc)

/-! ## 6. Programs without vector instructions -/

/-- A scalar layout entry as a mixed layout entry. -/
def liftLayout (y : Nat × Nat × DInstr) : Nat × Nat × (DInstr ⊕ VInstr) :=
  (y.1, y.2.1, Sum.inl y.2.2)

/-- On a stream the scalar stream decoder accepts, the mixed stream decoder returns the
    same layout. -/
theorem mixedStream_of_decodeAt (A : VecAsm) :
    ∀ (n off : Nat) (bs : List (BitVec 8)) (xs : List (Nat × Nat × DInstr)),
      decodeAt n off bs = some xs → mixedStream A n off bs = some (xs.map liftLayout) := by
  intro n
  induction n with
  | zero =>
    intro off bs xs h
    simp only [decodeAt] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      simp [mixedStream, he]
    · cases h
  | succ n ih =>
    intro off bs xs h
    simp only [decodeAt] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      simp [mixedStream, he]
    · rename_i he
      cases hd : decodeLinstr bs with
      | none => rw [hd] at h; simp at h
      | some p =>
        obtain ⟨x, r⟩ := p
        rw [hd] at h
        simp only at h
        cases hr : decodeAt n (off + (bs.length - r.length)) r with
        | none => rw [hr] at h; simp at h
        | some ys =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          simp [mixedStream, he, mixedHead_of_decodeLinstr A hd, ih _ _ _ hr, liftLayout]

/-- Resolution of a scalar layout read as a mixed layout is scalar resolution. -/
theorem mixedResolve_liftLayout (xs : List (Nat × Nat × DInstr)) :
    ∀ ys : List (Nat × Nat × DInstr),
      mixedResolve (xs.map liftLayout) (ys.map liftLayout)
        = (resolveAll xs ys).map (List.map Sum.inl) := by
  intro ys
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    obtain ⟨s, e, x⟩ := y
    have hf : ∀ d : Int,
        (xs.map liftLayout).findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d))
          = xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) := by
      intro d
      rw [List.findIdx?_map]
      rfl
    cases x with
    | op i =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs rest <;> rfl
    | ret =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs rest <;> rfl
    | push r =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs rest <;> rfl
    | pop r =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs rest <;> rfl
    | jcc cc d =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih, hf]
      cases xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
      | none => rfl
      | some j => cases resolveAll xs rest <;> rfl
    | call d =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih, hf]
      cases xs.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
      | none => rfl
      | some j => cases resolveAll xs rest <;> rfl

/-- **The mixed decoder on scalar streams.** On a stream `decodeLprog` decodes, `mixedDecode`
    returns the same program, for every table. -/
theorem mixedDecode_of_decodeLprog (A : VecAsm) {bs : List (BitVec 8)} {p : List RInstr}
    (h : decodeLprog bs = some p) : mixedDecode A bs = some (p.map Sum.inl) := by
  unfold decodeLprog at h
  cases hx : decodeAt bs.length 0 bs with
  | none => rw [hx] at h; simp at h
  | some xs =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    rw [mixedDecode, mixedStream_of_decodeAt A _ _ _ _ hx]
    simp only [Option.bind_some]
    rw [mixedResolve_liftLayout, h]
    rfl

/-- On a program without vector instructions the mixed encoder is `itemBytes`. -/
theorem mixedEncode_scalar (A : VecAsm) (items : List Item) :
    mixedEncode A (items.map Sum.inl) = itemBytes items := by
  simp [mixedEncode, itemBytes, List.flatMap_map]

/-- On the positions of a scalar body the mixed encoder is `encodeLcmd`. -/
theorem mixedEncode_itemsFrom (A : VecAsm) (body : Lcmd) (shs : List Shape)
    (h : List.Forall₂ (fun instr sh => ShapeOK (Params.ofBody body) instr.li_i sh) body shs) :
    mixedEncode A ((itemsFrom (Params.ofBody body) 0 body shs).map Sum.inl)
      = encodeLcmd body := by
  rw [mixedEncode_scalar, itemBytes_itemsFrom _ h 0, encodeLcmd_eq_encodeFrom]

/-- **The scalar body round trip as an instance.** Under the conditions of
    `decodeLprog_encodeLcmd`, the mixed decoder reads the program of the body from the
    bytes of `encodeLcmd`, for every table. -/
theorem mixedDecode_encodeLcmd (A : VecAsm) (body : Lcmd) (shs : List Shape)
    (h : List.Forall₂ (fun instr sh => ShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hbr : branchOK (itemsFrom (Params.ofBody body) 0 body shs) 0
      (itemsFrom (Params.ofBody body) 0 body shs) = true)
    {p : List RInstr}
    (hp : expectedFrom (itemsFrom (Params.ofBody body) 0 body shs)
      (itemsFrom (Params.ofBody body) 0 body shs) = some p) :
    mixedDecode A (encodeLcmd body) = some (p.map Sum.inl) :=
  mixedDecode_of_decodeLprog A ((decodeLprog_encodeLcmd body shs h hbr).trans hp)

/-! ## 7. The statement that the processor runs the table as `vexec` -/

/-- **The processor runs a mixed image as `x86VecMach` runs its decoding.** `cpu bs s s'`
    reads: the processor, started at the first byte of the image `bs` in a state that `s`
    describes, returns from the image in a state that `s'` describes. The statement is that
    every halting run of `x86VecMach` on the program `mixedDecode A` reads from an image is
    a run of the processor on the image. At a vector instruction `v` the machine runs
    `vexec v`, so the statement contains: the processor executes the entry of `v` as
    `vexec v`.

    The statement constrains the processor only on the entries of the table. Each entry is
    one instruction of the instruction set (a table with a missing instruction leaves it
    without an entry), and the entry determines the instruction: an instruction that reads
    a read-only vector reads it from an address its bytes contain, so the relation `cpu`
    names the states in which that address holds the vector. A processor whose execution of
    each entry is `vexec` on the states `cpu` relates, as the Intel SDM specifies for the
    instructions `X86Backend.VecAsmZmm.zmmAsm` encodes in `Mode.zmm`, is faithful. -/
def VecAsm.Faithful (A : VecAsm) (r : DoitRegime) (m : Mode)
    (cpu : List (BitVec 8) → AState × VState → AState × VState → Prop) : Prop :=
  ∀ (bs : List (BitVec 8)) (prog : List (RInstr ⊕ VInstr)) (s s' : AState × VState),
    mixedDecode A bs = some prog → (x86VecMach r m).HaltsC prog 0 s s' → cpu bs s s'

variable {A : VecAsm} {r : DoitRegime} {m : Mode}
  {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}

/-- A faithful processor runs every scalar image as `x86VecMach` runs the program its own
    decoder, `decodeLprog` lifted, reads from it. -/
theorem VecAsm.Faithful.scalar (hF : A.Faithful r m cpu) {bs : List (BitVec 8)}
    {prog : List (RInstr ⊕ VInstr)} {s s' : AState × VState}
    (hd : (x86VecMach r m).decode bs = some prog)
    (hh : (x86VecMach r m).HaltsC prog 0 s s') : cpu bs s s' := by
  rw [x86VecMach_decode] at hd
  cases hp : decodeLprog bs with
  | none => rw [hp] at hd; simp at hd
  | some p =>
    rw [hp] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    exact hF bs _ s s' (mixedDecode_of_decodeLprog A hp) hh

/-- The table entry of `v` followed by `ret` decodes to the program of `v` and `ret`. -/
theorem VecAsm.Lawful.mixedDecode_entry_ret (hA : A.Lawful) {v : VInstr}
    (hv : A.Encodable v) :
    mixedDecode A (A.bytes v ++ LeafBytes.encRet) = some [Sum.inr v, Sum.inl RInstr.ret] := by
  have h := mixedDecode_mixedEncode hA [Sum.inr v, Sum.inl mkRet]
    (by
      intro it hit
      simp only [List.mem_cons, reduceCtorEq, Sum.inl.injEq, List.not_mem_nil, or_false,
        false_or] at hit
      subst hit
      exact mkRet_ok)
    (by
      intro w hw
      simp only [List.mem_cons, Sum.inr.injEq, reduceCtorEq, List.not_mem_nil, or_false] at hw
      subst hw
      exact hv)
    (by simp [mixedBranchOK, mixedItems, MixedItem.ofScalar, VecAsm.item, mkRet])
  simpa [mixedEncode, mixedItems, mixedExpected, MixedItem.ofScalar, VecAsm.item, mkRet]
    using h

/-- **A faithful processor executes the entry of `v` as `vexec v`**: on the image of the
    entry followed by `ret`, from the state `s`, it returns in the state `vexec m s v`. -/
theorem VecAsm.Faithful.vexec (hF : A.Faithful r m cpu) (hA : A.Lawful) {v : VInstr}
    (hv : A.Encodable v) (s : AState × VState) :
    cpu (A.bytes v ++ LeafBytes.encRet) s (vexec m s v) := by
  refine hF _ _ s _ (hA.mixedDecode_entry_ret hv) ?_
  exact IsaMachine.HaltsC.go (pc' := 1) (s' := VecMach.vexec m s v) rfl
    (IsaMachine.HaltsC.ret rfl)

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage

/-! ## 8. A machine with another decoder -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.IsaMachine

open CatCrypt.Crypto.SecureCompilation.CT

/-- **The machine `M` with the decoder `d`.** Every other component is that of `M`; the
    runs of a decoded program do not mention the decoder, so they are those of `M`. -/
@[reducible] def withDecode (M : IsaMachine) (d : List (BitVec 8) → Option (List M.Instr)) :
    IsaMachine :=
  { M with decode := d }

variable {M : IsaMachine} {d : List (BitVec 8) → Option (List M.Instr)}

theorem withDecode_decode (bs : List (BitVec 8)) : (M.withDecode d).decode bs = d bs := rfl

theorem withDecode_runBlock (s : M.MState) (ops : List M.Op) :
    (M.withDecode d).runBlock s ops = M.runBlock s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (M.exec s i)

theorem withDecode_blockLeak (s : M.MState) (ops : List M.Op) :
    (M.withDecode d).blockLeak s ops = M.blockLeak s ops := by
  induction ops generalizing s with
  | nil => rfl
  | cons i is ih => exact congrArg (M.opLeak s i ++ ·) (ih (M.exec s i))

theorem withDecode_blockOk (ok : M.MState → M.Op → Prop) (s : M.MState) (ops : List M.Op) :
    (M.withDecode d).BlockOk ok s ops ↔ M.BlockOk ok s ops := by
  induction ops generalizing s with
  | nil => exact Iff.rfl
  | cons i is ih => exact and_congr Iff.rfl (ih (M.exec s i))

theorem withDecode_mstep (prog : List M.Instr) (pc : Nat) (s : M.MState) :
    (M.withDecode d).mstep prog pc s = M.mstep prog pc s := by
  simp only [mstep, withDecode_runBlock (d := d)]
  rcases M.act prog pc s with _ | (i | ops | ⟨c, t⟩ | t | _) <;> rfl

/-- A run with leakage of `M` is a run of `M` with another decoder. -/
theorem RunL.withDecode {ok : M.MState → M.Op → Prop} {prog : List M.Instr} {pc : Nat}
    {s : M.MState} {t : List CTLeak} {s' : M.MState} (h : M.RunL ok prog pc s t s') :
    (M.withDecode d).RunL ok prog pc s t s' := by
  induction h with
  | ret h => exact .ret h
  | op h hok _ ih => exact .op h hok ih
  | @block pc s ops t s' h hok _ ih =>
    have hb := IsaMachine.RunL.block (M := M.withDecode d) (ok := ok) (s := s) h
      ((withDecode_blockOk ok s ops).mpr hok) (by rw [withDecode_runBlock (d := d)];exact ih)
    rwa [withDecode_blockLeak (d := d)] at hb
  | branch h _ ih => exact .branch h ih
  | @call pc tgt s sc tc tr s' h hok _ hokr _ ihc ihr =>
    have hb := IsaMachine.RunL.call (M := M.withDecode d) (ok := ok) (s := s) (sc := sc) h
      ((withDecode_blockOk ok s _).mpr hok) (by rw [withDecode_runBlock (d := d)];exact ihc)
      ((withDecode_blockOk ok sc _).mpr hokr) (by rw [withDecode_runBlock (d := d)];exact ihr)
    rwa [withDecode_blockLeak (d := d), withDecode_blockLeak (d := d)] at hb

/-- **The runs with leakage of a machine do not depend on its decoder.** -/
theorem withDecode_runL {ok : M.MState → M.Op → Prop} {prog : List M.Instr} {pc : Nat}
    {s : M.MState} {t : List CTLeak} {s' : M.MState} :
    (M.withDecode d).RunL ok prog pc s t s' ↔ M.RunL ok prog pc s t s' :=
  ⟨fun h => RunL.withDecode (M := M.withDecode d) (d := M.decode) h, RunL.withDecode⟩

/-- A halting run through calls of `M` is one of `M` with another decoder. -/
theorem HaltsC.withDecode {prog : List M.Instr} {pc : Nat} {s s' : M.MState}
    (h : M.HaltsC prog pc s s') : (M.withDecode d).HaltsC prog pc s s' := by
  induction h with
  | ret h => exact .ret h
  | go h _ ih => exact .go ((withDecode_mstep _ _ _).trans h) ih
  | call h _ _ ihc ihr =>
    exact .call h (by rw [withDecode_runBlock (d := d)];exact ihc)
      (by rw [withDecode_runBlock (d := d)];exact ihr)

/-- **The halting runs through calls of a machine do not depend on its decoder.** -/
theorem withDecode_haltsC {prog : List M.Instr} {pc : Nat} {s s' : M.MState} :
    (M.withDecode d).HaltsC prog pc s s' ↔ M.HaltsC prog pc s s' :=
  ⟨fun h => HaltsC.withDecode (M := M.withDecode d) (d := M.decode) h, HaltsC.withDecode⟩

theorem Reaches.withDecode {prog : List M.Instr} {pc : Nat} {s : M.MState} {pc' : Nat}
    {s' : M.MState} (h : M.Reaches prog pc s pc' s') :
    (M.withDecode d).Reaches prog pc s pc' s' := by
  induction h with
  | refl => exact .refl _ _
  | next h _ ih => exact .next ((withDecode_mstep _ _ _).trans h) ih

/-- **The call-free halting runs of a machine do not depend on its decoder.** -/
theorem withDecode_halts {prog : List M.Instr} {pc : Nat} {s s' : M.MState} :
    (M.withDecode d).Halts prog pc s s' ↔ M.Halts prog pc s s' :=
  ⟨fun ⟨pc', hr, hret⟩ =>
      ⟨pc', Reaches.withDecode (M := M.withDecode d) (d := M.decode) hr, hret⟩,
    fun ⟨pc', hr, hret⟩ => ⟨pc', hr.withDecode, hret⟩⟩

variable {S V : Type} {vexec : M.MState × S → V → M.MState × S}
  {vleak : M.MState × S → V → List CTLeak}

theorem withOps_reaches_inl (hM : M.ActLocal) {prog : List M.Instr} {pc : Nat} {s : M.MState}
    {pc' : Nat} {s' : M.MState} (v : S) (h : M.Reaches prog pc s pc' s') :
    (M.withOps S V vexec vleak).Reaches (prog.map Sum.inl) pc (s, v) pc' (s', v) := by
  induction h with
  | refl => exact .refl _ _
  | @next pc s pc₁ s₁ pc₂ s₂ h _ ih =>
    exact IsaMachine.Reaches.next (M := M.withOps S V vexec vleak) (s := (s, v))
      (s' := (s₁, v)) ((withOps_mstep_inl_go hM).mpr ⟨h, rfl⟩) ih

/-- A call-free halting run of the base machine is one of the extended machine on the same
    program, the second state component unchanged. -/
theorem withOps_halts_inl (hM : M.ActLocal) {prog : List M.Instr} {pc : Nat}
    {s s' : M.MState} (v : S) (h : M.Halts prog pc s s') :
    (M.withOps S V vexec vleak).Halts (prog.map Sum.inl) pc (s, v) (s', v) := by
  obtain ⟨pc', hr, hret⟩ := h
  exact ⟨pc', withOps_reaches_inl hM v hr, (withOps_act_inl_eq_some hM).mpr ⟨_, hret, rfl⟩⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.IsaMachine

/-! ## 9. The machine of mixed images -/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (VInstr VState x86VecMach
  x86VecMach_decode x86Mach_actLocal)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime CTLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Mach)

/-- **The x86 machine with vector registers and the mixed decoder**: the machine
    `x86VecMach r m` with the decoder `mixedDecode A`. A byte image may contain the table
    entries of vector instructions; the execution of a decoded program is that of
    `x86VecMach r m`. -/
@[reducible] noncomputable def mixedMach (A : VecAsm) (r : DoitRegime) (m : Mode) :
    IsaMachine :=
  (x86VecMach r m).withDecode (mixedDecode A)

variable {A : VecAsm} {r : DoitRegime} {m : Mode}
  {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}

/-- The decoder of `mixedMach` is `mixedDecode`. -/
theorem mixedMach_decode (bs : List (BitVec 8)) :
    (mixedMach A r m).decode bs = mixedDecode A bs := rfl

/-- The halting runs through calls of `mixedMach` are those of `x86VecMach`. -/
theorem mixedMach_haltsC {prog : List (RInstr ⊕ VInstr)} {pc : Nat}
    {s s' : AState × VState} :
    (mixedMach A r m).HaltsC prog pc s s' ↔ (x86VecMach r m).HaltsC prog pc s s' :=
  IsaMachine.withDecode_haltsC

/-- The call-free halting runs of `mixedMach` are those of `x86VecMach`. -/
theorem mixedMach_halts {prog : List (RInstr ⊕ VInstr)} {pc : Nat}
    {s s' : AState × VState} :
    (mixedMach A r m).Halts prog pc s s' ↔ (x86VecMach r m).Halts prog pc s s' :=
  IsaMachine.withDecode_halts

/-- The runs with leakage of `mixedMach` are those of `x86VecMach`. -/
theorem mixedMach_runL {ok : AState × VState → JInstr 64 ⊕ VInstr → Prop}
    {prog : List (RInstr ⊕ VInstr)} {pc : Nat} {s : AState × VState} {t : List CTLeak}
    {s' : AState × VState} :
    (mixedMach A r m).RunL ok prog pc s t s' ↔ (x86VecMach r m).RunL ok prog pc s t s' :=
  IsaMachine.withDecode_runL

/-- **`mixedMach` is conservative over the scalar decoder.** A byte string `decodeLprog`
    decodes is decoded by `mixedMach` to the same program, for every table. -/
theorem mixedMach_decode_of_decodeLprog (A : VecAsm) (r : DoitRegime) (m : Mode)
    {bs : List (BitVec 8)} {p : List RInstr} (h : decodeLprog bs = some p) :
    (mixedMach A r m).decode bs = some (p.map Sum.inl) :=
  mixedDecode_of_decodeLprog A h

/-- A program `x86VecMach` decodes from a byte string is the program `mixedMach` decodes
    from it. -/
theorem mixedMach_decode_of_x86VecMach (A : VecAsm) {bs : List (BitVec 8)}
    {prog : List (RInstr ⊕ VInstr)} (hd : (x86VecMach r m).decode bs = some prog) :
    (mixedMach A r m).decode bs = some prog := by
  rw [x86VecMach_decode] at hd
  cases hp : decodeLprog bs with
  | none => rw [hp] at hd; simp at hd
  | some p =>
    rw [hp] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    exact mixedDecode_of_decodeLprog A hp

/-- **A halting run through calls of a scalar image is a run on `mixedMach`.** When the
    scalar machine `x86Mach r` decodes a byte string to a program that halts from `s` in
    `s'`, `mixedMach` decodes the same byte string to a program that halts from `(s, v)` in
    `(s', v)`, for every table and every vector state `v`. -/
theorem mixedMach_haltsC_of_x86Mach (A : VecAsm) (m : Mode) {bs : List (BitVec 8)}
    {s s' : AState}
    (h : ∃ prog, (x86Mach r).decode bs = some prog ∧ (x86Mach r).HaltsC prog 0 s s')
    (v : VState) :
    ∃ prog, (mixedMach A r m).decode bs = some prog ∧
      (mixedMach A r m).HaltsC prog 0 (s, v) (s', v) := by
  obtain ⟨p, hd, hh⟩ := h
  exact ⟨p.map Sum.inl, mixedDecode_of_decodeLprog A hd,
    mixedMach_haltsC.mpr ((IsaMachine.withOps_haltsC_inl (x86Mach_actLocal r)).mpr ⟨hh, rfl⟩)⟩

/-- **A call-free halting run of a scalar image is a run on `mixedMach`**, the vector state
    unchanged. -/
theorem mixedMach_halts_of_x86Mach (A : VecAsm) (m : Mode) {bs : List (BitVec 8)}
    {s s' : AState}
    (h : ∃ prog, (x86Mach r).decode bs = some prog ∧ (x86Mach r).Halts prog 0 s s')
    (v : VState) :
    ∃ prog, (mixedMach A r m).decode bs = some prog ∧
      (mixedMach A r m).Halts prog 0 (s, v) (s', v) := by
  obtain ⟨p, hd, hh⟩ := h
  exact ⟨p.map Sum.inl, mixedDecode_of_decodeLprog A hd,
    mixedMach_halts.mpr (IsaMachine.withOps_halts_inl (x86Mach_actLocal r) v hh)⟩

/-- **A run with leakage of a scalar image is a run on `mixedMach`**, with the same trace
    and the vector state unchanged. -/
theorem mixedMach_runL_of_x86Mach (A : VecAsm) (m : Mode) {bs : List (BitVec 8)}
    {ok : AState → JInstr 64 → Prop} {s s' : AState} {t : List CTLeak}
    (h : ∃ prog, (x86Mach r).decode bs = some prog ∧ (x86Mach r).RunL ok prog 0 s t s')
    (okV : AState × VState → VInstr → Prop) (v : VState) :
    ∃ prog, (mixedMach A r m).decode bs = some prog ∧
      (mixedMach A r m).RunL ((x86Mach r).okLift ok okV) prog 0 (s, v) t (s', v) := by
  obtain ⟨p, hd, hh⟩ := h
  exact ⟨p.map Sum.inl, mixedDecode_of_decodeLprog A hd,
    mixedMach_runL.mpr ((IsaMachine.withOps_runL_inl (x86Mach_actLocal r)).mpr ⟨hh, rfl⟩)⟩

/-- **`VecAsm.Faithful` is a statement about `mixedMach`**: the processor runs every image
    as `mixedMach` runs the program it decodes from the image. -/
theorem VecAsm.faithful_iff_mixedMach :
    A.Faithful r m cpu ↔
      ∀ (bs : List (BitVec 8)) (prog : List (RInstr ⊕ VInstr)) (s s' : AState × VState),
        (mixedMach A r m).decode bs = some prog → (mixedMach A r m).HaltsC prog 0 s s' →
          cpu bs s s' :=
  ⟨fun hF bs prog s s' hd hh => hF bs prog s s' hd (mixedMach_haltsC.mp hh),
    fun hF bs prog s s' hd hh => hF bs prog s s' hd (mixedMach_haltsC.mpr hh)⟩

/-- **Round trip on `mixedMach`.** For a lawful table, `mixedMach` decodes the bytes of a
    program of well-formed scalar positions and encodable vector instructions, with
    well-formed branches, to the program its positions denote. -/
theorem mixedMach_decode_mixedEncode (r : DoitRegime) (m : Mode) (hA : A.Lawful)
    (prog : List (Item ⊕ VInstr)) (hok : ∀ it, Sum.inl it ∈ prog → ItemOK it)
    (hv : ∀ v, Sum.inr v ∈ prog → A.Encodable v)
    (hbr : mixedBranchOK (mixedItems A prog) 0 (mixedItems A prog) = true) :
    (mixedMach A r m).decode (mixedEncode A prog)
      = mixedExpected (mixedItems A prog) (mixedItems A prog) :=
  mixedDecode_mixedEncode hA prog hok hv hbr

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
