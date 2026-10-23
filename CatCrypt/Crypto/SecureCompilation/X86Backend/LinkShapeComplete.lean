/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable

@[expose] public section

set_option autoImplicit false

/-!
# Template covers of the encoder primitives

`LinkOfEncodable.TemplateCover bs` says that the byte string `bs` splits into nonempty pieces,
each one of the byte templates `DecodeGen.pieceTemplates` of its instruction; the piece
splitter `DecodeGen.splitPieces` accepts exactly such strings
(`LinkOfEncodable.shapeOfBytes_isSome_iff`). This module proves a template cover for the
bytes of each encoder primitive `LprogBytes.encodeLopn` lays down, under the operand
conditions of the corresponding template.

## Main results

* `LinkOfEncodable.TemplateCover.append`, `.flatMap`, `.nil`: covers compose, so a sequence of
  primitives is covered by the covers of its parts and a new encoder sequence adds one theorem
  built from these; `TemplateCover.single` covers one template piece.
* `cover_J`: an instruction that `decodableJ` accepts covers its `encodeJInstr` image at the
  identity allocation.
* `cover_encZeroArrOp`, `cover_encStoreImmOp`: the zero-array and store-immediate sequences are
  covered for every operand.
* Membership: `mem_pieceTemplates_rr`, `mem_pieceTemplates_rsp`, … place a template of one of
  the families of `pieceTemplates` (register pairs, immediates, single registers, `%rsp`
  displacements, indexed moves, three registers, casts, and the `encodeJInstr` image `tmplJ`)
  at an instruction whose `guess` proposes its registers, immediates and displacements.
* Primitives: one cover theorem per encoder primitive of `encodeLopn` at `REX.W = 1`
  (`cover_encRspMem`, `cover_encCmovRspMem`, `cover_encAluRRw`, `cover_test`, `cover_enc0FRRw`,
  …), and the composite sequences built from them (`cover_encCmovSelect`,
  `cover_encCmovSelectSlotFE`, `cover_encZeroArrOp`, `cover_encStoreImmOp`, …).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable

/-! ## 1. Covers compose -/

/-- The empty byte string has the empty cover. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.nil :
    TemplateCover [] :=
  ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- Covers of two byte strings concatenate to a cover of their concatenation. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.append
    {a b : List (BitVec 8)} (ha : TemplateCover a) (hb : TemplateCover b) :
    TemplateCover (a ++ b) := by
  obtain ⟨p, rfl, hp⟩ := ha
  obtain ⟨q, rfl, hq⟩ := hb
  exact ⟨p ++ q, List.flatMap_append, fun x hx => (List.mem_append.1 hx).elim (hp x) (hq x)⟩

/-- A template of an instruction is a cover of its bytes. The bytes are nonempty, since a
    template decodes (`pieceTemplates_sound`) and the empty string does not. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.single
    {bs : List (BitVec 8)} {j : JInstr 64} (h : (bs, j) ∈ pieceTemplates j) :
    TemplateCover bs := by
  have hne : bs ≠ [] := by
    rintro rfl
    have hd := pieceTemplates_sound j _ h []
    simp [decodeLinstr] at hd
  exact ⟨[(bs, j)], by simp, fun q hq => by
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨hne, h⟩⟩

/-- A concatenation of covered byte strings is covered. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.flatMap
    {α : Type} (f : α → List (BitVec 8)) :
    ∀ l : List α, (∀ x ∈ l, TemplateCover (f x)) → TemplateCover (l.flatMap f) := by
  intro l
  induction l with
  | nil => exact fun _ => TemplateCover.nil
  | cons x l ih =>
    intro h
    rw [List.flatMap_cons]
    exact TemplateCover.append (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-! ## 2. Register names -/

/-- `regNum?` inverts `regName` on the sixteen register numbers. -/
theorem regNum?_regName {r : Nat} (hr : r < 16) : regNum? (regName r) = some r := by
  interval_cases r <;> rfl

/-- Renaming through the identity allocation fixes each canonical name. -/
theorem nameOf_canon {r : Nat} (hr : r < 16) :
    nameOf (canonAlloc ()) (regName r) = regName r := by
  rw [nameOf, regOf_canon hr, gpNum_regName hr]

/-! ## 3. Membership in the templates of an instruction -/

/-- The register numbers `pieceTemplates` instantiates its templates at. -/
abbrev nums (j : JInstr 64) : List Nat := (guess j).1.filterMap regNum?

theorem mem_pieceTemplates_rr {j : JInstr 64} {d s : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hq : q ∈ tmplRR d s) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl (Or.inl hq)⟩))⟩

theorem mem_pieceTemplates_cast {j : JInstr 64} {d s : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hq : q ∈ tmplCast d s) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl (Or.inr hq)⟩))⟩

theorem mem_pieceTemplates_idx {j : JInstr 64} {d s c : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hc : c ∈ nums j) (hq : q ∈ tmplIdx d s c) :
    q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inr ⟨c, hc, Or.inl hq⟩⟩))⟩

theorem mem_pieceTemplates_three {j : JInstr 64} {d s c : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hc : c ∈ nums j) (hq : q ∈ tmpl3 d s c) :
    q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inr ⟨c, hc, Or.inr hq⟩⟩))⟩

theorem mem_pieceTemplates_imm {j : JInstr 64} {d v : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hv : v ∈ (guess j).2.1) (hq : q ∈ tmplImm d v) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inr ⟨v, hv, hq⟩))⟩

theorem mem_pieceTemplates_one {j : JInstr 64} {d : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hq : q ∈ tmpl1 d) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inr hq)⟩

theorem mem_pieceTemplates_rsp {j : JInstr 64} {d : Nat} {off : Int}
    {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hoff : off ∈ (guess j).2.2) (hq : q ∈ tmplRsp d off) :
    q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inr ⟨off, hoff, hq⟩⟩

theorem mem_pieceTemplates_lea {j : JInstr 64} {q : List (BitVec 8) × JInstr 64}
    (hq : q ∈ tmplLea j) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append]
  exact Or.inl (Or.inr hq)

/-- An instruction in the covered set of `tmplJ` has its `encodeJInstr` image at the identity
    allocation among its templates. -/
theorem mem_pieceTemplates_J {j : JInstr 64} (h1 : decodableJ j = true)
    (h2 : mulxRdxOk (canonAlloc ()) j = true) (h3 : renameJ (canonAlloc ()) j = j) :
    (encodeJInstr (canonAlloc ()) j, j) ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append]
  exact Or.inl (Or.inl (by simp [tmplJ, h1, h2, h3]))

/-- A register number whose canonical name `guess` proposes is among the numbers the
    templates are instantiated at. -/
theorem mem_nums_of {j : JInstr 64} {r : Nat} (hr : r < 16) (h : regName r ∈ (guess j).1) :
    r ∈ nums j :=
  List.mem_filterMap.2 ⟨_, h, regNum?_regName hr⟩

/-- An instruction in the covered set of `tmplJ` covers its `encodeJInstr` image at the
    identity allocation. -/
theorem cover_J {j : JInstr 64} {bs : List (BitVec 8)} (h1 : decodableJ j = true)
    (h2 : mulxRdxOk (canonAlloc ()) j = true) (h3 : renameJ (canonAlloc ()) j = j)
    (he : encodeJInstr (canonAlloc ()) j = bs) : TemplateCover bs :=
  he ▸ TemplateCover.single (mem_pieceTemplates_J h1 h2 h3)

/-! ## 4. Covers of the single-instruction primitives -/

/-- The `%rsp`-relative load, store and compare at `REX.W = 1`. -/
theorem cover_encRspMem {op r : Nat} {off : Int} (hop : op = 0x8b ∨ op = 0x89 ∨ op = 0x3b)
    (hr : r < 16) (hoff : dispOk32 off = true) : TemplateCover (encRspMem 1 op r off) := by
  rcases hop with rfl | rfl | rfl
  · exact TemplateCover.single (j := .loadMem (regName r) "%rsp" off)
      (mem_pieceTemplates_rsp (off := off) (mem_nums_of hr (by simp [guess])) (by simp [guess])
        (by simp [tmplRsp, hoff]))
  · exact TemplateCover.single (j := .storeMem "%rsp" off (.reg (regName r)))
      (mem_pieceTemplates_rsp (off := off) (mem_nums_of hr (by simp [guess, opNames])) (by simp [guess])
        (by simp [tmplRsp, hoff]))
  · exact TemplateCover.single (j := .cmpMem (regName r) "%rsp" off)
      (mem_pieceTemplates_rsp (off := off) (mem_nums_of hr (by simp [guess])) (by simp [guess])
        (by simp [tmplRsp, hoff]))

/-- The conditional moves `cmove` and `cmovne` from a frame word at `REX.W = 1`. -/
theorem cover_encCmovRspMem {op r : Nat} {off : Int} (hop : op = 0x44 ∨ op = 0x45)
    (hr : r < 16) (hoff : dispOk32 off = true) : TemplateCover (encCmovRspMem 1 op r off) := by
  rcases hop with rfl | rfl
  · exact TemplateCover.single (j := .cmovccMem .e (regName r) "%rsp" off)
      (mem_pieceTemplates_rsp (off := off) (mem_nums_of hr (by simp [guess])) (by simp [guess])
        (by simp [tmplRsp, hoff]))
  · exact TemplateCover.single (j := .cmovccMem .ne (regName r) "%rsp" off)
      (mem_pieceTemplates_rsp (off := off) (mem_nums_of hr (by simp [guess])) (by simp [guess])
        (by simp [tmplRsp, hoff]))

/-- The register-register `mov`, `cmp` and group-1 `ALU` forms at `REX.W = 1`. -/
theorem cover_encAluRRw {op d s : Nat} (hop : op ∈ 0x89 :: 0x39 :: aluOps) (hd : d < 16)
    (hs : s < 16) : TemplateCover (encAluRRw 1 op d s) := by
  have hm : ∀ mk : String → JOperand → JInstr 64,
      guess (mk (regName d) (.reg (regName s))) = ([regName d, regName s], [], []) →
      (encAluRRw 1 op d s, mk (regName d) (.reg (regName s))) ∈ tmplRR d s →
      TemplateCover (encAluRRw 1 op d s) := fun mk hg hq =>
    TemplateCover.single (mem_pieceTemplates_rr (mem_nums_of hd (by simp [hg]))
      (mem_nums_of hs (by simp [hg])) hq)
  simp only [aluOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hm JInstr.mov rfl (by simp [tmplRR])
  · exact hm JInstr.cmp rfl (by simp [tmplRR])
  · exact hm JInstr.add rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.or_ rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.adc rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.sbb rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.and_ rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.sub rfl (by simp [tmplRR, aluOps, aluMnemonic])
  · exact hm JInstr.xor_ rfl (by simp [tmplRR, aluOps, aluMnemonic])

/-- The register-register `test` (`85 /r`) at `REX.W = 1`. -/
theorem cover_test {a b : Nat} (ha : a < 16) (hb : b < 16) :
    TemplateCover (encAluRRw 1 0x85 a b) :=
  cover_J (j := .test (regName a) (.reg (regName b))) rfl rfl
    (by simp [renameJ, operandOf, nameOf_canon ha, nameOf_canon hb])
    (by simp [encodeJInstr, regOf_canon ha, regOf_canon hb, gpNum_regName ha, gpNum_regName hb,
      encAluRRw, encAluRR, rexOpt])

/-- The `0F`-map register-register `cmove`, `cmovne` and `imul` at `REX.W = 1`. -/
theorem cover_enc0FRRw {op d s : Nat} (hop : op = 0x44 ∨ op = 0x45 ∨ op = 0xaf) (hd : d < 16)
    (hs : s < 16) : TemplateCover (enc0FRRw 1 op d s) := by
  rcases hop with rfl | rfl | rfl
  · exact cover_J (j := .cmove (regName d) (.reg (regName s))) rfl rfl
      (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
      (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd,
        gpNum_regName hs, enc0FRRw, enc0FRR, rexOpt])
  · exact cover_J (j := .cmovne (regName d) (.reg (regName s))) rfl rfl
      (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
      (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd,
        gpNum_regName hs, enc0FRRw, enc0FRR, rexOpt])
  · exact cover_J (j := .imul (regName d) (.reg (regName s))) rfl rfl
      (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
      (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd,
        gpNum_regName hs, enc0FRRw, enc0FRR, rexOpt])

/-- The `MOV` immediate forms: the sign-extended `imm32` at `REX.W = 1` and the
    zero-extending `imm32` at `REX.W = 0`. -/
theorem cover_encMovImmw {w d v : Nat} (hd : d < 16)
    (hv : (w = 1 ∧ v < 2 ^ 64 ∧ fitsImm32S v = true) ∨ (w = 0 ∧ v < 2 ^ 32)) :
    TemplateCover (encMovImmw w d v) := by
  refine TemplateCover.single (j := .mov (regName d) (.imm v))
    (mem_pieceTemplates_imm (v := v) (mem_nums_of hd (by simp [guess]))
      (by simp [guess, opImms]) ?_)
  rcases hv with ⟨rfl, h1, h2⟩ | ⟨rfl, h1⟩
  · simp only [tmplImm, h1, h2, decide_true, Bool.and_self, if_true, List.mem_append,
      List.mem_singleton, true_or]
  · simp only [tmplImm, h1, decide_true, if_true, List.mem_append, List.mem_singleton,
      true_or, or_true]

/-- The sign-extended `imm8` group-1 forms (`83 /digit ib`) at `REX.W = 1`. -/
theorem cover_encAluImm8 {dig d v : Nat} (hdig : dig < 8) (hd : d < 16)
    (hv : fitsImm8S 1 v = true) : TemplateCover (encAluImm8 1 dig d v) := by
  have hm : ∀ mk : String → JOperand → JInstr 64,
      guess (mk (regName d) (.imm v)) = ([regName d], [v], []) →
      aluImm8Mnemonic dig = some mk → TemplateCover (encAluImm8 1 dig d v) := fun mk hg hmk =>
    TemplateCover.single (j := mk (regName d) (.imm v))
      (mem_pieceTemplates_imm (v := v) (mem_nums_of hd (by simp [hg]))
      (by simp [hg]) (by
        simp only [tmplImm, hv, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff,
          List.mem_range, List.mem_singleton, if_true]
        exact Or.inl (Or.inr (Or.inl ⟨dig, hdig, mk, hmk, rfl⟩))))
  interval_cases dig
  · exact hm JInstr.add rfl rfl
  · exact hm JInstr.or_ rfl rfl
  · exact hm JInstr.adc rfl rfl
  · exact hm JInstr.sbb rfl rfl
  · exact hm JInstr.and_ rfl rfl
  · exact hm JInstr.sub rfl rfl
  · exact hm JInstr.xor_ rfl rfl
  · exact hm JInstr.cmp rfl rfl

/-- `IMUL` by a sign-extended `imm8` at `REX.W = 1`. -/
theorem cover_encImulImm8w {d v : Nat} (hd : d < 16) (hv : fitsImm8S 1 v = true) :
    TemplateCover (encImulImm8w 1 d v) :=
  TemplateCover.single (j := .imulri (regName d) (regName d) v)
    (mem_pieceTemplates_imm (v := v) (mem_nums_of hd (by simp [guess])) (by simp [guess])
      (by simp [tmplImm, hv]))

/-- The `D1` shifts by one at `REX.W = 1`. -/
theorem cover_encShift1 {ext d : Nat} (hext : ext = 4 ∨ ext = 5 ∨ ext = 7) (hd : d < 16) :
    TemplateCover (encShift1 1 ext d) := by
  rcases hext with rfl | rfl | rfl
  · exact TemplateCover.single (j := .shl (regName d) (.imm 1))
      (mem_pieceTemplates_imm (v := 1) (mem_nums_of hd (by simp [guess])) (by simp [guess, opImms])
        (by simp [tmplImm]))
  · exact TemplateCover.single (j := .shr (regName d) (.imm 1))
      (mem_pieceTemplates_imm (v := 1) (mem_nums_of hd (by simp [guess])) (by simp [guess, opImms])
        (by simp [tmplImm]))
  · exact TemplateCover.single (j := .sar (regName d) (.imm 1))
      (mem_pieceTemplates_imm (v := 1) (mem_nums_of hd (by simp [guess])) (by simp [guess, opImms])
        (by simp [tmplImm]))

/-- `neg`. -/
theorem cover_neg {d : Nat} (hd : d < 16) : TemplateCover (ScalarEncoder.encUnaryF7 3 d) :=
  TemplateCover.single (j := .neg (regName d))
    (mem_pieceTemplates_one (mem_nums_of hd (by simp [guess])) (by simp [tmpl1]))

/-- The byte `sete` and `setne`. -/
theorem cover_encSetccReg {op d : Nat} (hop : op = 0x94 ∨ op = 0x95) (hd : d < 16) :
    TemplateCover (encSetccReg op d) := by
  rcases hop with rfl | rfl
  · exact TemplateCover.single (j := .setcc .e (regName d))
      (mem_pieceTemplates_one (mem_nums_of hd (by simp [guess])) (by simp [tmpl1]))
  · exact TemplateCover.single (j := .setcc .ne (regName d))
      (mem_pieceTemplates_one (mem_nums_of hd (by simp [guess])) (by simp [tmpl1]))

/-- `setc` with its zero-extending `movzbq`, one template. -/
theorem cover_setc {d : Nat} (hd : d < 16) : TemplateCover (encSetccMovzx 0x92 d) :=
  cover_J (j := .setc (regName d)) rfl rfl (by simp [renameJ, nameOf_canon hd])
    (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd, encSetccMovzx_setc_agree])

/-- The indexed load and store at stride `8` and `REX.W = 1`. -/
theorem cover_encMemMovSibw {op r b i : Nat} (hop : op = 0x8b ∨ op = 0x89) (hr : r < 16)
    (hb : b < 16) (hi : i < 16) (hi4 : i ≠ 4) : TemplateCover (encMemMovSibw 1 op r b i 8) := by
  have hq : i != 4 := by simpa using hi4
  rcases hop with rfl | rfl
  · exact TemplateCover.single (j := .loadMemIdx (regName r) (regName b) (regName i) 8)
      (mem_pieceTemplates_idx (mem_nums_of hr (by simp [guess])) (mem_nums_of hb (by simp [guess]))
        (mem_nums_of hi (by simp [guess])) (by simp [tmplIdx, hq]))
  · exact TemplateCover.single (j := .storeMemIdx (regName b) (regName i) 8 (.reg (regName r)))
      (mem_pieceTemplates_idx (mem_nums_of hr (by simp [guess, opNames]))
        (mem_nums_of hb (by simp [guess])) (mem_nums_of hi (by simp [guess]))
        (by simp [tmplIdx, hq]))

/-- The indexed `lea` at a stride SIB encodes and `REX.W = 1`. -/
theorem cover_leaSib {r b i s : Nat} (hr : r < 16) (hb : b < 16) (hi : i < 16) (hi4 : i ≠ 4)
    (hs : scaleOk s = true) : TemplateCover (encMemMovSibw 1 0x8d r b i s) :=
  TemplateCover.single (j := .lea (regName r) (regName b) (regName i) s 0)
    (mem_pieceTemplates_lea (by
      simp [tmplLea, regNum?_regName hr, regNum?_regName hb, regNum?_regName hi, hi4, hs]))

/-- The BMI2 variable shifts. -/
theorem cover_encShiftX {ext d s c : Nat} (hext : ext = 4 ∨ ext = 5 ∨ ext = 7) (hd : d < 16)
    (hs : s < 16) (hc : c < 16) : TemplateCover (encShiftX ext d s c) := by
  rcases hext with rfl | rfl | rfl
  · exact TemplateCover.single (j := .shlx (regName d) (regName s) (regName c))
      (mem_pieceTemplates_three (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess])) (mem_nums_of hc (by simp [guess])) (by simp [tmpl3]))
  · exact TemplateCover.single (j := .shrx (regName d) (regName s) (regName c))
      (mem_pieceTemplates_three (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess])) (mem_nums_of hc (by simp [guess])) (by simp [tmpl3]))
  · exact TemplateCover.single (j := .sarx (regName d) (regName s) (regName c))
      (mem_pieceTemplates_three (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess])) (mem_nums_of hc (by simp [guess])) (by simp [tmpl3]))

/-- The width casts. -/
theorem cover_encCastW {m d s : Nat} (hd : d < 16) (hs : s < 16) :
    TemplateCover (encCastW m d s) := by
  unfold encCastW
  split
  · exact TemplateCover.single (j := .movzx (regName d) 16 (regName s))
      (mem_pieceTemplates_cast (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess])) (by simp [tmplCast]))
  · exact TemplateCover.single (j := .movzx (regName d) 32 (regName s))
      (mem_pieceTemplates_cast (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess])) (by simp [tmplCast]))

/-- The `ADX` carry chains `adcx` and `adox` on registers. -/
theorem cover_encAdxCarry {pfx d s : Nat} (hpfx : pfx = 0x66 ∨ pfx = 0xf3) (hd : d < 16)
    (hs : s < 16) : TemplateCover (encAdxCarry pfx d s) := by
  rcases hpfx with rfl | rfl
  · exact cover_J (j := .adcx (regName d) (.reg (regName s))) rfl rfl
      (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
      (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd, gpNum_regName hs])
  · exact cover_J (j := .adox (regName d) (.reg (regName s))) rfl rfl
      (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
      (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd, gpNum_regName hs])

/-- `bt $imm, %d` at `REX.W = 1`. -/
theorem cover_encBtImm {d imm : Nat} (hd : d < 16) (himm : imm < 256) :
    TemplateCover (encBtImm 1 d imm) :=
  cover_J (j := .bt (regName d) (.imm imm)) (by simp [decodableJ, himm]) rfl
    (by simp [renameJ, operandOf, nameOf_canon hd])
    (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd, encBtImm, encBtImm8, rexOpt])

/-- The store of a sign-extended `imm32` to a frame word at `REX.W = 1`. -/
theorem cover_encMovImmRspMem {off : Int} {v : Nat} (hv : v < 2 ^ 64)
    (hf : fitsImm32S v = true) (hoff : dispOk32 off = true) :
    TemplateCover (encMovImmRspMem 1 off v) := by
  have e : encMovImmRspMem 1 off v = encMemMovImm 4 off v := by
    simp only [encMovImmRspMem, encMemMovImm, encMemMov, memTail, rexOpt_w1]
    split_ifs <;> simp_all [rex]
  rw [e]
  exact cover_J (j := .storeMem (regName 4) off (.imm v)) (by simp [decodableJ, hf, hoff]; omega) rfl
    (by simp [renameJ, operandOf, nameOf_canon (r := 4) (by omega)])
    (by simp [encodeJInstr, regOf_canon (r := 4) (by omega), gpNum_regName (r := 4) (by omega)])

/-- The store of zero to `off(%b)`. -/
theorem cover_encMemMovImm_zero {b : Nat} {off : Int} (hb : b < 16)
    (hoff : dispOk32 off = true) : TemplateCover (encMemMovImm b off 0) :=
  cover_J (j := .storeMem (regName b) off (.imm 0)) (by simp [decodableJ, hoff]) rfl
    (by simp [renameJ, operandOf, nameOf_canon hb])
    (by simp [encodeJInstr, regOf_canon hb, gpNum_regName hb])

/-- The `[base + disp]` load, store and `lea` at `REX.W = 1`. -/
theorem cover_encMemMovw {op r b : Nat} {off : Int} (hop : op = 0x8b ∨ op = 0x89 ∨ op = 0x8d)
    (hr : r < 16) (hb : b < 16) (hoff : dispOk32 off = true) :
    TemplateCover (encMemMovw 1 op r b off) := by
  have e : ∀ op, encMemMovw 1 op r b off = encMemMov op r b off := fun op => by
    simp [encMemMovw, encMemMov, rexOpt]
  rw [e]
  rcases hop with rfl | rfl | rfl
  · exact cover_J (j := .loadMem (regName r) (regName b) off) (by simp [decodableJ, hoff]) rfl
      (by simp [renameJ, nameOf_canon hr, nameOf_canon hb])
      (by simp [encodeJInstr, regOf_canon hr, regOf_canon hb, gpNum_regName hr, gpNum_regName hb])
  · exact cover_J (j := .storeMem (regName b) off (.reg (regName r)))
      (by simp [decodableJ, hoff]) rfl
      (by simp [renameJ, operandOf, nameOf_canon hr, nameOf_canon hb])
      (by simp [encodeJInstr, regOf_canon hr, regOf_canon hb, gpNum_regName hr, gpNum_regName hb])
  · exact cover_J (j := .lea (regName r) (regName b) (regName b) 0 off)
      (by simp [decodableJ, hoff]) rfl
      (by simp [renameJ, nameOf_canon hr, nameOf_canon hb])
      (by simp [encodeJInstr, regOf_canon hr, regOf_canon hb, gpNum_regName hr, gpNum_regName hb])

/-- `mulx` on registers. -/
theorem cover_encMulxRR {h l s : Nat} (hh : h < 16) (hl : l < 16) (hs : s < 16) :
    TemplateCover (encMulxRR h l s) :=
  cover_J (j := .mulx (regName h) (regName l) (.reg (regName 2)) (.reg (regName s))) rfl
    (by simp [mulxRdxOk, regOf_canon (r := 2) (by omega), gpNum_regName (r := 2) (by omega)])
    (by simp [renameJ, operandOf, nameOf_canon hh, nameOf_canon hl, nameOf_canon hs,
      nameOf_canon (r := 2) (by omega)])
    (by simp [encodeJInstr, regOf_canon hh, regOf_canon hl, regOf_canon hs, gpNum_regName hh,
      gpNum_regName hl, gpNum_regName hs])

/-- `mulx` from `off(%b)`. -/
theorem cover_encMulxMem {h l b : Nat} {off : Int} (hh : h < 16) (hl : l < 16) (hb : b < 16)
    (hoff : dispOk32 off = true) : TemplateCover (encMulxMem h l b off) :=
  cover_J (j := .mulxMem (regName h) (regName l) (.reg (regName 2)) (regName b) off)
    (by simp [decodableJ, hoff])
    (by simp [mulxRdxOk, regOf_canon (r := 2) (by omega), gpNum_regName (r := 2) (by omega)])
    (by simp [renameJ, operandOf, nameOf_canon hh, nameOf_canon hl, nameOf_canon hb,
      nameOf_canon (r := 2) (by omega)])
    (by simp [encodeJInstr, regOf_canon hh, regOf_canon hl, regOf_canon hb, gpNum_regName hh,
      gpNum_regName hl, gpNum_regName hb])

/-- The `movabs` of a value that needs all 64 bits. -/
theorem cover_encMovImm64 {d v : Nat} (hd : d < 16) (hlo : 2 ^ 31 ≤ v) (hv : v < 2 ^ 64) :
    TemplateCover (encMovImm64 d v) :=
  cover_J (j := .mov (regName d) (.imm v)) (by simp [decodableJ]; omega) rfl
    (by simp [renameJ, operandOf, nameOf_canon hd])
    (by simp only [encodeJInstr, regOf_canon hd, gpNum_regName hd]; rw [if_neg (by omega)])

/-- `adcx` and `adox` from a frame word. -/
theorem cover_encAdxRspMem {pfx d : Nat} {off : Int} (hpfx : pfx = 0x66 ∨ pfx = 0xf3)
    (hd : d < 16) (hoff : dispOk32 off = true) : TemplateCover (encAdxRspMem pfx d off) := by
  have e : ∀ p, encAdxRspMem p d off
      = ([p, rex 1 (bit d 3) 0 (bit 4 3), 0x0f, 0x38, 0xf6].map (BitVec.ofNat 8))
        ++ memTail d 4 off := fun p => by
    simp only [encAdxRspMem, memTail]
    split_ifs <;> simp_all
  rw [e]
  rcases hpfx with rfl | rfl
  · exact cover_J (j := .adcxMem (regName d) (regName 4) off) (by simp [decodableJ, hoff]) rfl
      (by simp [renameJ, nameOf_canon hd, nameOf_canon (r := 4) (by omega)])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd, regOf_canon (r := 4) (by omega),
        gpNum_regName (r := 4) (by omega)])
  · exact cover_J (j := .adoxMem (regName d) (regName 4) off) (by simp [decodableJ, hoff]) rfl
      (by simp [renameJ, nameOf_canon hd, nameOf_canon (r := 4) (by omega)])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd, regOf_canon (r := 4) (by omega),
        gpNum_regName (r := 4) (by omega)])

/-! ## 5. Covers of the composite sequences -/

/-- The register select `CMOV` (`encCmovSelect`) at `REX.W = 1`. -/
theorem cover_encCmovSelect {dn cn tn fn : Nat} (hd : dn < 16) (hc : cn < 16) (ht : tn < 16)
    (hf : fn < 16) : TemplateCover (encCmovSelect 1 dn cn tn fn) := by
  unfold encCmovSelect
  split_ifs
  · exact (cover_test hc hc).append (cover_enc0FRRw (Or.inl rfl) hd hf)
  · exact (cover_test hc hc).append (cover_enc0FRRw (Or.inr (Or.inl rfl)) hd ht)
  · exact ((cover_encAluRRw List.mem_cons_self hd hf).append (cover_test hc hc)).append
      (cover_enc0FRRw (Or.inr (Or.inl rfl)) hd ht)

/-- The red-zone cell `-128(%rsp)` is in signed 32-bit displacement range. -/
theorem dispOk32_cmovRedZone : dispOk32 cmovRedZone = true := by decide

/-- The scratch of a spilled-destination select is a register number. -/
theorem cmovScratchNum_lt (cn tn fn : Nat) : cmovScratchNum cn tn fn < 16 := by
  unfold cmovScratchNum
  split_ifs <;> omega

/-- The select into a frame slot through a red-zone scratch at `REX.W = 1`. -/
theorem cover_encCmovSelectMem {off : Int} {cn tn fn : Nat} (hoff : dispOk32 off = true)
    (hc : cn < 16) (ht : tn < 16) (hf : fn < 16) :
    TemplateCover (encCmovSelectMem 1 off cn tn fn) := by
  have hs := cmovScratchNum_lt cn tn fn
  unfold encCmovSelectMem
  exact (((((cover_encRspMem (Or.inr (Or.inl rfl)) hs dispOk32_cmovRedZone).append
    (cover_encAluRRw List.mem_cons_self hs hf)).append (cover_test hc hc)).append
    (cover_enc0FRRw (Or.inr (Or.inl rfl)) hs ht)).append
    (cover_encRspMem (Or.inr (Or.inl rfl)) hs hoff)).append
    (cover_encRspMem (Or.inl rfl) hs dispOk32_cmovRedZone)

/-- The select with a slot true value at `REX.W = 1`. -/
theorem cover_encCmovSelectSlotT {dn cn fn : Nat} {off : Int} (hd : dn < 16) (hc : cn < 16)
    (hf : fn < 16) (hoff : dispOk32 off = true) :
    TemplateCover (encCmovSelectSlotT 1 dn cn fn off) := by
  unfold encCmovSelectSlotT
  refine (TemplateCover.append ?_ (cover_test hc hc)).append
    (cover_encCmovRspMem (Or.inr rfl) hd hoff)
  split
  · exact TemplateCover.nil
  · exact cover_encAluRRw List.mem_cons_self hd hf

/-- The select with a slot false value at `REX.W = 1`. -/
theorem cover_encCmovSelectSlotF {dn cn tn : Nat} {off : Int} (hd : dn < 16) (hc : cn < 16)
    (ht : tn < 16) (hoff : dispOk32 off = true) :
    TemplateCover (encCmovSelectSlotF 1 dn cn tn off) :=
  ((cover_encRspMem (Or.inl rfl) hd hoff).append (cover_test hc hc)).append
    (cover_enc0FRRw (Or.inr (Or.inl rfl)) hd ht)

/-- The select with a slot false value and the destination equal to the true value (`cmove`
    from the slot) at `REX.W = 1`. -/
theorem cover_encCmovSelectSlotFE {dn cn : Nat} {off : Int} (hd : dn < 16) (hc : cn < 16)
    (hoff : dispOk32 off = true) : TemplateCover (encCmovSelectSlotFE 1 dn cn off) :=
  (cover_test hc hc).append (cover_encCmovRspMem (Or.inl rfl) hd hoff)

/-- The select with both values in slots at `REX.W = 1`. -/
theorem cover_encCmovSelectSlotTF {dn cn : Nat} {offT offF : Int} (hd : dn < 16) (hc : cn < 16)
    (hT : dispOk32 offT = true) (hF : dispOk32 offF = true) :
    TemplateCover (encCmovSelectSlotTF 1 dn cn offT offF) :=
  ((cover_encRspMem (Or.inl rfl) hd hF).append (cover_test hc hc)).append
    (cover_encCmovRspMem (Or.inr rfl) hd hT)

/-- The materialised register comparison `sete`/`setne` at `REX.W = 1`. -/
theorem cover_encSetccCmp {op d a b : Nat} (hop : op = 0x94 ∨ op = 0x95) (hd : d < 16)
    (ha : a < 16) (hb : b < 16) : TemplateCover (encSetccCmp 1 op d a b) :=
  ((cover_encAluRRw (List.mem_cons_of_mem _ List.mem_cons_self) ha hb).append
    (cover_encMovImmw hd (Or.inl ⟨rfl, by norm_num, by decide⟩))).append
    (cover_encSetccReg hop hd)

/-- The scratch of a coincident-destination `mulx` is a register number. -/
theorem mulxSameScratch_lt (h s : Nat) : mulxSameScratch h s < 16 := by
  unfold mulxSameScratch
  cases hf : List.find? _ _ with
  | none => simp
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Option.getD_some]
    omega

/-- The coincident-destination `mulx` through a red-zone scratch. -/
theorem cover_encMulxSameDst {h s : Nat} (hh : h < 16) (hs : s < 16) :
    TemplateCover (encMulxSameDst h s) := by
  have hr := mulxSameScratch_lt h s
  unfold encMulxSameDst
  exact ((cover_encRspMem (Or.inr (Or.inl rfl)) hr dispOk32_cmovRedZone).append
    (cover_encMulxRR hh hr hs)).append (cover_encRspMem (Or.inl rfl) hr dispOk32_cmovRedZone)

/-- The coincident-destination `mulx` from `off(%b)` through a red-zone scratch. -/
theorem cover_encMulxSameDstMem {h b : Nat} {off : Int} (hh : h < 16) (hb : b < 16)
    (hoff : dispOk32 off = true) : TemplateCover (encMulxSameDstMem h b off) := by
  have hr := mulxSameScratch_lt h 16
  unfold encMulxSameDstMem
  exact ((cover_encRspMem (Or.inr (Or.inl rfl)) hr dispOk32_cmovRedZone).append
    (cover_encMulxMem hh hr hb hoff)).append
    (cover_encRspMem (Or.inl rfl) hr dispOk32_cmovRedZone)

/-- The zeroing stores of `n` words from register `b`. -/
theorem cover_encZeroArr {b n : Nat} (hb : b < 16) (hn : stackDispOk (n - 1) = true) :
    TemplateCover (encZeroArr b n) := by
  unfold encZeroArr
  refine TemplateCover.flatMap _ _ fun i hi => cover_encMemMovImm_zero hb ?_
  simp only [List.mem_range] at hi
  simp only [stackDispOk, decide_eq_true_eq] at hn
  simp only [dispOk32, decide_eq_true_eq, Int.ofNat_eq_natCast]
  omega

/-- The bytes of `ZEROARR` have a cover at every operand. -/
theorem cover_encZeroArrOp (d a : JasminLprogExport.LOperand) (v : Nat) :
    TemplateCover (encZeroArrOp d a v) := by
  unfold encZeroArrOp
  split
  · split_ifs with h
    · simp only [Bool.and_eq_true] at h
      exact cover_encZeroArr (gpNumU_lt_16 _) h.2
    · exact TemplateCover.nil
  · exact TemplateCover.nil

/-- The bytes of `STOREIMM` have a cover at every operand. -/
theorem cover_encStoreImmOp (a s k : JasminLprogExport.LOperand) :
    TemplateCover (encStoreImmOp a s k) := by
  unfold encStoreImmOp
  split
  · split_ifs with h
    · simp only [Bool.and_eq_true, stackDispOk, decide_eq_true_eq] at h
      refine cover_encMemMovw (Or.inr (Or.inl rfl)) (gpNumU_lt_16 _) (gpNumU_lt_16 _) ?_
      simp only [dispOk32, decide_eq_true_eq, Int.ofNat_eq_natCast]
      omega
    · exact TemplateCover.nil
  · exact TemplateCover.nil

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete
