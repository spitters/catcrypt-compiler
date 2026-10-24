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
* Sub-encoders: `cover_encTwoAddr` (the two-address forms, with a memory operand one
  instruction for `ADD`, `MOV`, `LOAD` and `STORE` and the red-zone scratch sequence
  `cover_encAluViaScratch` for the other operations), `cover_encImmOp` (the immediate forms at
  every immediate),
  `cover_encTagShift`, `cover_twoByte`, `cover_encSetccCmpImm`.
* `linkFormB`: the link forms, the conditions under which `encodeLopn` has a cover beyond
  encodability: not `ADOXHI`, displacements in signed 32-bit range, and the conjuncts
  `narrowFreeB`, `narrowIdxFreeB`, each excluding a form the decoder does not read.
* `encodeLopn_cover`: the bytes of an instruction of a link form have a template cover.
* `shapeOf_complete`, `shapesOf_isSome_of_encodableLcmd`: an encodable instruction other than
  `Lgoto` of a link form has a computed shape, and an encodable body of such instructions has
  computed shapes.
* `x86LinkB_of_encodable`: the link check accepts an encodable body of link forms without
  conditional branches, calling only the callee and saving no register by `push`, within the
  call range.
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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LOperand LinstrR Linstr Lcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (calleeSavedToSave mnemWidth isCarryOutBinding)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (stripWidthTag)

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

/-- A conditional of two covered byte strings is covered, each branch under its condition. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.ite
    {c : Prop} {_ : Decidable c} {a b : List (BitVec 8)} (ha : c → TemplateCover a)
    (hb : ¬ c → TemplateCover b) : TemplateCover (if c then a else b) := by
  grind only

/-- A dependent conditional of two covered byte strings is covered, each branch under its
    condition. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable.TemplateCover.dite
    {c : Prop} {_ : Decidable c} {a : c → List (BitVec 8)} {b : ¬ c → List (BitVec 8)}
    (ha : ∀ h : c, TemplateCover (a h)) (hb : ∀ h : ¬ c, TemplateCover (b h)) :
    TemplateCover (if h : c then a h else b h) := by
  grind only

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
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl (Or.inl (Or.inl (Or.inl hq)))⟩))⟩

theorem mem_pieceTemplates_cmovRR {j : JInstr 64} {d s : Nat}
    {q : List (BitVec 8) × JInstr 64} (hd : d ∈ nums j) (hs : s ∈ nums j)
    (hq : q ∈ tmplCmovRR d s) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl (Or.inr hq)⟩))⟩

theorem mem_pieceTemplates_memAdd {j : JInstr 64} {r b : Nat} {off : Int}
    {q : List (BitVec 8) × JInstr 64} (hr : r ∈ nums j) (hb : b ∈ nums j)
    (hoff : off ∈ (guess j).2.2) (hq : q ∈ tmplMemAdd r b off) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨r, hr, Or.inl (Or.inl (Or.inl ⟨b, hb, Or.inr ⟨off, hoff, hq⟩⟩))⟩

theorem mem_pieceTemplates_cast {j : JInstr 64} {d s : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hq : q ∈ tmplCast d s) : q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs, Or.inl (Or.inl (Or.inl (Or.inr hq)))⟩))⟩

theorem mem_pieceTemplates_idx {j : JInstr 64} {d s c : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hc : c ∈ nums j) (hq : q ∈ tmplIdx d s c) :
    q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs,
    Or.inl (Or.inl (Or.inr ⟨c, hc, Or.inl hq⟩))⟩))⟩

theorem mem_pieceTemplates_three {j : JInstr 64} {d s c : Nat} {q : List (BitVec 8) × JInstr 64}
    (hd : d ∈ nums j) (hs : s ∈ nums j) (hc : c ∈ nums j) (hq : q ∈ tmpl3 d s c) :
    q ∈ pieceTemplates j := by
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨d, hd, Or.inl (Or.inl (Or.inl ⟨s, hs,
    Or.inl (Or.inl (Or.inr ⟨c, hc, Or.inr hq⟩))⟩))⟩

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
  · simp only [tmplImm, h1, h2, decide_true, Bool.and_self, ite_true, List.mem_append,
      List.mem_singleton, true_or]
  · simp only [tmplImm, h1, decide_true, ite_true, List.mem_append, List.mem_singleton,
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
          List.mem_range, List.mem_singleton, ite_true]
        exact Or.inl (Or.inl (Or.inr (Or.inl ⟨dig, hdig, mk, hmk, rfl⟩)))))
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
    (by simp only [encodeJInstr, regOf_canon hd, gpNum_regName hd]; rw [ite_eq_right (by omega)])

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

/-- The `setc` carry-out into a frame slot: `%rax` saved in the red zone, `setc` with its
    `movzbq` into `%rax`, the store to the slot and the restore. -/
theorem cover_encCarryOutRspMem {off : Int} (hoff : dispOk32 off = true) :
    TemplateCover (encCarryOutRspMem 0x92 off) := by
  unfold encCarryOutRspMem
  exact (((cover_encRspMem (Or.inr (Or.inl rfl)) (by decide) dispOk32_cmovRedZone).append
    (cover_setc (by decide))).append
    (cover_encRspMem (Or.inr (Or.inl rfl)) (by decide) hoff)).append
    (cover_encRspMem (Or.inl rfl) (by decide) dispOk32_cmovRedZone)

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

/-! ## 6. Covers of the sub-encoders of `encodeLopn` -/

/-- The displacement of an operand the encoder addresses as memory is in signed 32-bit
    range. -/
def opdDispB (F W Q : Nat) : LOperand → Bool
  | .reg n => (spillQsaveOff F W n Q).all dispOk32 && (parseMemNameGp n).all (fun p => dispOk32 p.2)
  | _ => true

/-- The base register `parseMemNameGp` resolves is a register number. -/
theorem parseMemNameGp_fst_lt {n : String} {p : Nat × Int} (h : parseMemNameGp n = some p) :
    p.1 < 16 := by
  unfold parseMemNameGp at h
  split at h
  · split at h
    · split at h
      · split at h
        · cases h
          exact gpNumU_lt_16 _
        · cases h
      · cases h
    · cases h
  · cases h

/-- The sign-extension of the low 32 bits of a value has the `imm32` bytes of the value. -/
theorem imm32LE_sext32 (v : Nat) : imm32LE (sext32 (v % 2 ^ 32)) = imm32LE v := by
  simp only [imm32LE, Nat.shiftRight_eq_div_pow, show (0xff : Nat) = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, sext32]
  split <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega

/-- The sign-extension of the low 32 bits of a value is a 64-bit value that a sign-extended
    `imm32` denotes. -/
theorem sext32_fits (v : Nat) :
    sext32 (v % 2 ^ 32) < 2 ^ 64 ∧ fitsImm32S (sext32 (v % 2 ^ 32)) = true := by
  simp only [sext32, fitsImm32S]
  split <;> simp <;> omega

/-- `CMOVB` on registers at `REX.W = 1`. -/
theorem cover_cmovb {d s : Nat} (hd : d < 16) (hs : s < 16) :
    TemplateCover (enc0FRRw 1 0x42 d s) :=
  cover_J (j := .cmovb (regName d) (.reg (regName s))) rfl rfl
    (by simp [renameJ, operandOf, nameOf_canon hd, nameOf_canon hs])
    (by simp [encodeJInstr, regOf_canon hd, regOf_canon hs, gpNum_regName hd,
      gpNum_regName hs, enc0FRRw, enc0FRR, rexOpt])

/-- The register conditional moves `CMOVAE`, `CMOVL` and `CMOVGE` at `REX.W = 1`. -/
theorem cover_cmovccRR {op d s : Nat} (hop : op = 0x43 ∨ op = 0x4c ∨ op = 0x4d) (hd : d < 16)
    (hs : s < 16) : TemplateCover (enc0FRRw 1 op d s) := by
  have hm : ∀ c : Condt, c = .nb ∨ c = .l ∨ c = .nl → 0x40 + ScalarEncoder.condCode c = op →
      TemplateCover (enc0FRRw 1 op d s) := fun c hc he =>
    he ▸ TemplateCover.single (j := .cmovcc c (regName d) (.reg (regName s)))
      (mem_pieceTemplates_cmovRR (mem_nums_of hd (by simp [guess]))
        (mem_nums_of hs (by simp [guess, opNames])) (by
          simp only [tmplCmovRR, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
          exact ⟨c, hc, rfl⟩))
  rcases hop with rfl | rfl | rfl
  · exact hm .nb (Or.inl rfl) rfl
  · exact hm .l (Or.inr (Or.inl rfl)) rfl
  · exact hm .nl (Or.inr (Or.inr rfl)) rfl

/-- Every `0F`-map register form of `twoByteOpcode` at `REX.W = 1`. -/
theorem cover_twoByte {b : String} {op d s : Nat} (h : twoByteOpcode b = some op) (hd : d < 16)
    (hs : s < 16) : TemplateCover (enc0FRRw 1 op d s) := by
  have hop : op = 0xaf ∨ op = 0x44 ∨ op = 0x45 ∨ op = 0x42 ∨ op = 0x43 ∨ op = 0x4c
      ∨ op = 0x4d := by
    unfold twoByteOpcode at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cover_enc0FRRw (Or.inr (Or.inr rfl)) hd hs
  · exact cover_enc0FRRw (Or.inl rfl) hd hs
  · exact cover_enc0FRRw (Or.inr (Or.inl rfl)) hd hs
  · exact cover_cmovb hd hs
  · exact cover_cmovccRR (Or.inl rfl) hd hs
  · exact cover_cmovccRR (Or.inr (Or.inl rfl)) hd hs
  · exact cover_cmovccRR (Or.inr (Or.inr rfl)) hd hs

/-- `ADD` with a `[base + disp]` operand in either direction at `REX.W = 1`. -/
theorem cover_addMemw {op r b : Nat} {off : Int} (hop : op = 0x03 ∨ op = 0x01) (hr : r < 16)
    (hb : b < 16) (hoff : dispOk32 off = true) : TemplateCover (encMemMovw 1 op r b off) := by
  rcases hop with rfl | rfl
  · exact TemplateCover.single (j := .addMem (regName r) (regName b) off)
      (mem_pieceTemplates_memAdd (off := off) (mem_nums_of hr (by simp [guess]))
        (mem_nums_of hb (by simp [guess])) (by simp [guess]) (by simp [tmplMemAdd, hoff]))
  · exact TemplateCover.single (j := .addToMem (regName b) off (.reg (regName r)))
      (mem_pieceTemplates_memAdd (off := off) (mem_nums_of hr (by simp [guess, opNames]))
        (mem_nums_of hb (by simp [guess])) (by simp [guess]) (by simp [tmplMemAdd, hoff]))

/-- `encRspMem` at `REX.W = 1` is the `[base + disp]` form at base `%rsp`. -/
theorem encRspMem_eq_encMemMovw (op r : Nat) (off : Int) :
    encRspMem 1 op r off = encMemMovw 1 op r 4 off := by
  rw [encRspMem_eq_memTail]
  simp [encMemMovw, rexOpt, bit]

/-- A two-address operation with a memory operand through a red-zone scratch at
    `REX.W = 1`: the scratch save, the load, the register-register operation, the store when
    the memory operand is the destination, and the restore. -/
theorem cover_encAluViaScratch {op r scr : Nat} {ld st : List (BitVec 8)}
    (hop : op ∈ 0x89 :: 0x39 :: aluOps) (hr : r < 16) (hscr : scr < 16)
    (hld : TemplateCover ld) (hst : TemplateCover st) (m : Bool) :
    TemplateCover (encAluViaScratch 1 op r scr m ld st) := by
  unfold encAluViaScratch
  refine (((cover_encRspMem (Or.inr (Or.inl rfl)) hscr dispOk32_cmovRedZone).append hld).append
    ?_).append (cover_encRspMem (Or.inl rfl) hscr dispOk32_cmovRedZone)
  cases m
  · exact cover_encAluRRw hop hr hscr
  · exact (cover_encAluRRw hop hscr hr).append hst

/-- `encAluRspScratch` at `REX.W = 1` over a frame word of in-range offset. -/
theorem cover_encAluRspScratch {op r : Nat} {off : Int} (hop : op ∈ 0x89 :: 0x39 :: aluOps)
    (hr : r < 16) (hoff : dispOk32 off = true) (m : Bool) :
    TemplateCover (encAluRspScratch 1 op r off m) :=
  cover_encAluViaScratch hop hr (aluMemScratch_lt r 4)
    (cover_encRspMem (Or.inl rfl) (aluMemScratch_lt r 4) hoff)
    (cover_encRspMem (Or.inr (Or.inl rfl)) (aluMemScratch_lt r 4) hoff) m

/-- `encAluMemScratch` at `REX.W = 1` over a cell of in-range offset. -/
theorem cover_encAluMemScratch {op r b : Nat} {off : Int} (hop : op ∈ 0x89 :: 0x39 :: aluOps)
    (hr : r < 16) (hb : b < 16) (hoff : dispOk32 off = true) (m : Bool) :
    TemplateCover (encAluMemScratch 1 op r b off m) :=
  cover_encAluViaScratch hop hr (aluMemScratch_lt r b)
    (cover_encMemMovw (Or.inl rfl) (aluMemScratch_lt r b) hb hoff)
    (cover_encMemMovw (Or.inr (Or.inl rfl)) (aluMemScratch_lt r b) hb hoff) m

/-- The two-address forms at `REX.W = 1` of the opcodes `aluOpcode` names, at every operand
    pair of in-range displacements. A memory operand (a frame slot or a `mem.*` cell) is one
    decoded instruction for `ADD`, `MOV`, `LOAD` and `STORE`, and the scratch sequence of
    `encAluViaScratch` for the other operations. -/
theorem cover_encTwoAddr (F W Q : Nat) {b : String} {op : Nat} (d s : LOperand)
    (hop : aluOpcode b = some op)
    (hdD : opdDispB F W Q d = true) (hdS : opdDispB F W Q s = true) :
    TemplateCover (encTwoAddr F W 1 op d s Q) := by
  have hops : op = 0x01 ∨ op = 0x09 ∨ op = 0x11 ∨ op = 0x19 ∨ op = 0x21 ∨ op = 0x29
      ∨ op = 0x31 ∨ op = 0x89 ∨ op = 0x8b := by
    unfold aluOpcode at hop
    split at hop <;> simp only [Option.some.injEq, reduceCtorEq] at hop <;> omega
  have hscr : ¬(op = 0x01 ∨ op = 0x89 ∨ op = 0x8b) → op ∈ 0x89 :: 0x39 :: aluOps := by
    intro h
    simp only [aluOps, List.mem_cons, List.not_mem_nil, or_false]
    omega
  unfold encTwoAddr
  split
  · rename_i dn sn
    split
    · rename_i off hoffD _
      split
      · have hd : dispOk32 off = true := by simp_all [opdDispB]
        split
        · rename_i h3
          rcases h3 with rfl | rfl | rfl
          · simpa [memDstOp, encRspMem_eq_encMemMovw] using
              cover_addMemw (Or.inr rfl) (gpNumU_lt_16 sn) (by decide) hd
          · exact cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 sn) hd
          · exact cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 sn) hd
        · rename_i h3
          exact cover_encAluRspScratch (hscr h3) (gpNumU_lt_16 sn) hd true
      · exact TemplateCover.nil
    · rename_i off _ hoffS
      split
      · have hd : dispOk32 off = true := by simp_all [opdDispB]
        split
        · rename_i h3
          rcases h3 with rfl | rfl | rfl
          · simpa [memSrcOp, encRspMem_eq_encMemMovw] using
              cover_addMemw (Or.inl rfl) (gpNumU_lt_16 dn) (by decide) hd
          · exact cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 dn) hd
          · exact cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 dn) hd
        · rename_i h3
          exact cover_encAluRspScratch (hscr h3) (gpNumU_lt_16 dn) hd false
      · exact TemplateCover.nil
    · exact TemplateCover.nil
    · rename_i hoffD hoffS
      split
      · split
        · rcases hops with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact cover_encAluRRw (by simp [memDstOp, aluOps]) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
        · exact TemplateCover.nil
      · rename_i bb off hp _
        split
        · have hd : dispOk32 off = true := by simp_all [opdDispB]
          have hb := parseMemNameGp_fst_lt hp
          split
          · rename_i h3
            rcases h3 with rfl | rfl | rfl
            · exact cover_addMemw (Or.inr rfl) (gpNumU_lt_16 sn) hb hd
            · exact cover_encMemMovw (Or.inr (Or.inl rfl)) (gpNumU_lt_16 sn) hb hd
            · exact cover_encMemMovw (Or.inr (Or.inl rfl)) (gpNumU_lt_16 sn) hb hd
          · rename_i h3
            exact cover_encAluMemScratch (hscr h3) (gpNumU_lt_16 sn) hb hd true
        · exact TemplateCover.nil
      · rename_i bb off _ hp
        split
        · have hd : dispOk32 off = true := by simp_all [opdDispB]
          have hb := parseMemNameGp_fst_lt hp
          split
          · rename_i h3
            rcases h3 with rfl | rfl | rfl
            · exact cover_addMemw (Or.inl rfl) (gpNumU_lt_16 dn) hb hd
            · exact cover_encMemMovw (Or.inl rfl) (gpNumU_lt_16 dn) hb hd
            · exact cover_encMemMovw (Or.inl rfl) (gpNumU_lt_16 dn) hb hd
          · rename_i h3
            exact cover_encAluMemScratch (hscr h3) (gpNumU_lt_16 dn) hb hd false
        · exact TemplateCover.nil
      · exact TemplateCover.nil
  · exact TemplateCover.nil

/-- The group-1 forms with a sign-extended `imm32` (`81 /digit id`) at `REX.W = 1`. -/
theorem cover_encAluImmw {dig d v : Nat} (hdig : dig < 8) (hd : d < 16) (hv : v < 2 ^ 64)
    (hf : fitsImm32S v = true) : TemplateCover (encAluImmw 1 dig d v) := by
  have e : encAluImmw 1 dig d v = encAluImm dig d v := by
    simp [encAluImmw, encAluImm, rexOpt]
  have hJ : ∀ mk : String → JOperand → JInstr 64,
      decodableJ (mk (regName d) (.imm v)) = true →
      mulxRdxOk (canonAlloc ()) (mk (regName d) (.imm v)) = true →
      renameJ (canonAlloc ()) (mk (regName d) (.imm v)) = mk (regName d) (.imm v) →
      encodeJInstr (canonAlloc ()) (mk (regName d) (.imm v)) = encAluImm dig d v →
      TemplateCover (encAluImmw 1 dig d v) := fun mk h1 h2 h3 he =>
    e ▸ cover_J h1 h2 h3 he
  have hdec : (decide (v < 2 ^ 64) && fitsImm32S v) = true := by
    simp only [hf, Bool.and_true, decide_eq_true_eq]; exact hv
  interval_cases dig
  · exact hJ JInstr.add hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.or_ hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.adc hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.sbb hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.and_ hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.sub hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact hJ JInstr.xor_ hdec rfl (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact TemplateCover.single (j := .cmp (regName d) (.imm v))
      (mem_pieceTemplates_imm (v := v) (mem_nums_of hd (by simp [guess]))
        (by simp [guess, opImms]) (by simp [tmplImm, hf]; exact Or.inr hv))

/-- `IMUL` by a sign-extended `imm32` (`69 /r id`) at `REX.W = 1`. -/
theorem cover_encImulImm32w {d v : Nat} (hd : d < 16) (hv : v < 2 ^ 64)
    (hf : fitsImm32S v = true) : TemplateCover (encImulImm32w 1 d v) := by
  have e : encImulImm32w 1 d v = encImulImm d v := by
    simp [encImulImm32w, encImulImm, rexOpt]
  rw [e]
  exact cover_J (j := .imul (regName d) (.imm v)) (by simpa [decodableJ, hf] using hv) rfl
    (by simp [renameJ, operandOf, nameOf_canon hd])
    (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])

/-- The group-1 forms with an `imm32` at `REX.W = 1`, for every value: the bytes are those
    of the sign-extension of its low 32 bits. -/
theorem cover_encAluImmw_any {dig d v : Nat} (hdig : dig < 8) (hd : d < 16) :
    TemplateCover (encAluImmw 1 dig d v) := by
  have e : encAluImmw 1 dig d v = encAluImmw 1 dig d (sext32 (v % 2 ^ 32)) := by
    simp only [encAluImmw, imm32LE_sext32]
  rw [e]
  exact cover_encAluImmw hdig hd (sext32_fits v).1 (sext32_fits v).2

/-- `IMUL` by an `imm32` at `REX.W = 1`, for every value. -/
theorem cover_encImulImm32w_any {d v : Nat} (hd : d < 16) :
    TemplateCover (encImulImm32w 1 d v) := by
  have e : encImulImm32w 1 d v = encImulImm32w 1 d (sext32 (v % 2 ^ 32)) := by
    simp only [encImulImm32w, imm32LE_sext32]
  rw [e]
  exact cover_encImulImm32w hd (sext32_fits v).1 (sext32_fits v).2

/-- The sign-extended `MOV $imm32` at `REX.W = 1`, for every value. -/
theorem cover_encMovImmw1_any {d v : Nat} (hd : d < 16) :
    TemplateCover (encMovImmw 1 d v) := by
  have e : encMovImmw 1 d v = encMovImmw 1 d (sext32 (v % 2 ^ 32)) := by
    simp only [encMovImmw, imm32LE_sext32]
  rw [e]
  exact cover_encMovImmw hd (Or.inl ⟨rfl, (sext32_fits v).1, (sext32_fits v).2⟩)

/-- The store of a sign-extended `imm32` to a frame word at `REX.W = 1`, for every value. -/
theorem cover_encMovImmRspMem_any {off : Int} {v : Nat} (hoff : dispOk32 off = true) :
    TemplateCover (encMovImmRspMem 1 off v) := by
  have e : encMovImmRspMem 1 off v = encMovImmRspMem 1 off (sext32 (v % 2 ^ 32)) := by
    simp only [encMovImmRspMem, imm32LE_sext32]
  rw [e]
  exact cover_encMovImmRspMem (sext32_fits v).1 (sext32_fits v).2 hoff

/-- The shifts by an `imm8` (`C1 /ext ib`) at `REX.W = 1`, for every count: the encoder keeps
    the low eight bits of the count. -/
theorem cover_encShiftImmw {ext d v : Nat} (hext : ext = 4 ∨ ext = 5 ∨ ext = 7)
    (hd : d < 16) : TemplateCover (encShiftImmw 1 ext d v) := by
  have hlt : v &&& 0xff < 256 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have e : encShiftImmw 1 ext d v = encShiftImm ext d (v &&& 0xff) := by
    simp [encShiftImmw, encShiftImm, rexOpt, Nat.and_assoc]
  rw [e]
  rcases hext with rfl | rfl | rfl
  · exact cover_J (j := .shl (regName d) (.imm (v &&& 0xff))) (by simp [decodableJ, hlt]) rfl
      (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact cover_J (j := .shr (regName d) (.imm (v &&& 0xff))) (by simp [decodableJ, hlt]) rfl
      (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])
  · exact cover_J (j := .sar (regName d) (.imm (v &&& 0xff))) (by simp [decodableJ, hlt]) rfl
      (by simp [renameJ, operandOf, nameOf_canon hd])
      (by simp [encodeJInstr, regOf_canon hd, gpNum_regName hd])

/-- The group-2 extension `shiftImmExt` names is `4`, `5` or `7`. -/
theorem shiftImmExt_cases {b : String} {ext : Nat} (h : shiftImmExt b = some ext) :
    ext = 4 ∨ ext = 5 ∨ ext = 7 := by
  unfold shiftImmExt at h
  split at h <;> simp_all

/-- The group-2 extension `tagShiftExt` names is `4`, `5` or `7`. -/
theorem tagShiftExt_cases {b : String} {ext : Nat} (h : tagShiftExt b = some ext) :
    ext = 4 ∨ ext = 5 ∨ ext = 7 := by
  simp only [tagShiftExt] at h
  split_ifs at h <;> simp_all

/-- The group-1 digit `aluImmDigit` names is below `8`. -/
theorem aluImmDigit_lt {b : String} {dig : Nat} (h : aluImmDigit b = some dig) : dig < 8 := by
  unfold aluImmDigit at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The count-in-tag shift at `REX.W = 1`. -/
theorem cover_encTagShift {ext dn : Nat} {b : String} (hext : ext = 4 ∨ ext = 5 ∨ ext = 7)
    (hd : dn < 16) : TemplateCover (encTagShift 1 ext dn b) := by
  simp only [encTagShift]
  split
  · exact cover_encShift1 hext hd
  · exact cover_encShiftImmw hext hd

/-- The `movabs` of a value outside the sign-extended `imm32` range. -/
theorem cover_encMovImm64_of_not_fits {d v : Nat} (hd : d < 16)
    (h : ¬ ((decide (v < 2 ^ 31) || decide (2 ^ 64 - 2 ^ 31 ≤ v)) = true)) :
    TemplateCover (encMovImm64 d v) := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, not_le] at h
  exact cover_encMovImm64 hd h.1 (by omega)

/-- The immediate-source forms at `REX.W = 1`, for every immediate. -/
theorem cover_encImmOp (b : String) (d : LOperand) (v : Nat) :
    TemplateCover (encImmOp 1 b d v) := by
  unfold encImmOp
  split
  · rename_i dn
    have hn := gpNumU_lt_16 dn
    split
    · exact TemplateCover.nil
    · dsimp only
      split
      · split
        · exact cover_encMovImmw1_any hn
        · exact cover_encMovImm64_of_not_fits hn ‹_›
      · split
        · exact cover_encMovImmw1_any hn
        · exact cover_encMovImm64_of_not_fits hn ‹_›
      · split
        · exact cover_encImulImm8w hn ‹_›
        · split
          · exact cover_encImulImm32w_any hn
          · exact TemplateCover.nil
      · split
        · rename_i ext hext
          split
          · subst_vars
            exact cover_encShift1 (shiftImmExt_cases hext) hn
          · exact cover_encShiftImmw (shiftImmExt_cases hext) hn
        · split
          · rename_i dig hdig
            split
            · exact cover_encAluImm8 (aluImmDigit_lt hdig) hn ‹_›
            · split
              · exact cover_encAluImmw_any (aluImmDigit_lt hdig) hn
              · exact TemplateCover.nil
          · exact TemplateCover.nil
  · exact TemplateCover.nil

/-! ## 7. The link forms and the cover of `encodeLopn` -/

/-- The mnemonic bases whose bytes do not depend on the operand width: the width casts, the
    widening multiplies and `SETC`. -/
def widthFreeBase (b : String) : Bool :=
  (castMovBits b).isSome || b == "MULX" || b == "MULXMEM" || b == "SETC"

/-- The operation is a 64-bit one (`REX.W = 1`), a carry-out binding, or of a base whose bytes
    do not depend on the width. The 32-bit forms (`REX.W = 0`, a mnemonic without `:64`, and
    the narrow `MOV:16`, `MOV:8`) have no decoded form: `JInstr 64` has no 32-bit
    operation. -/
def narrowFreeB (o : String) : Bool :=
  LprogBytes.rexW (mnemWidth o) == 1 || isCarryOutBinding o || widthFreeBase (stripWidthTag o)

/-- A register-indexed element access other than an address computation has the stride `8`.
    The loads and stores at the strides `1`, `2` and `4` (`movzbl`, `movzwl`, `movl`, `movb`,
    `movw`) have no decoded form: `loadMemIdx` and `storeMemIdx` move 64-bit words. -/
def narrowIdxFreeB (b : String) (ss : List LOperand) : Bool :=
  b == "LEA" || ss.all (fun o => match o with | .arrIdx _ _ sc => sc == 8 | _ => true)

/-- **The link forms.** The conditions under which the bytes of an instruction have a template
    cover (`encodeLopn_cover`), beyond its encodability: the base is not `ADOXHI` (`seto` has no
    decoder), every displacement of a memory operand is in signed 32-bit range, and the
    conditions `narrowFreeB` and `narrowIdxFreeB`, each of which excludes a form the decoder
    does not read. -/
def linkFormB (F W Q : Nat) : LinstrR → Bool
  | .Lopn ds o ss =>
      stripWidthTag o != "ADOXHI" && (ds ++ ss).all (opdDispB F W Q) && narrowFreeB o
        && narrowIdxFreeB (stripWidthTag o) ss
  | _ => true

/-- A frame slot among operands of in-range displacements has an in-range offset. -/
theorem disp_of_spill {F W Q : Nat} {L : List LOperand} {n : String} {off : Int}
    (hL : L.all (opdDispB F W Q) = true) (he : spillQsaveOff F W n Q = some off)
    (hn : LOperand.reg n ∈ L) : dispOk32 off = true := by
  have := List.all_eq_true.mp hL _ hn
  simp only [opdDispB, he, Option.all_some, Bool.and_eq_true] at this
  exact this.1

/-- A `mem.*` cell among operands of in-range displacements has an in-range offset. -/
theorem disp_of_mem {F W Q : Nat} {L : List LOperand} {n : String} {p : Nat × Int}
    (hL : L.all (opdDispB F W Q) = true) (he : parseMemNameGp n = some p)
    (hn : LOperand.reg n ∈ L) : dispOk32 p.2 = true := by
  have := List.all_eq_true.mp hL _ hn
  simp only [opdDispB, he, Option.all_some, Bool.and_eq_true] at this
  exact this.2

/-- The carry-out opcode of a base other than `ADOXHI` is `setc`. -/
theorem carryOutSetccOp_of_ne {b : String} (h : ¬ b = "ADOXHI") : carryOutSetccOp b = 0x92 := by
  simp [carryOutSetccOp, h]

/-- The two-address forms of an operation of a link form. -/
theorem cover_encTwoAddr_of (F W Q : Nat) {b : String} {op : Nat} {ds ss : List LOperand}
    (d s : LOperand) (hop : aluOpcode b = some op)
    (hopd : (ds ++ ss).all (opdDispB F W Q) = true) (hd : d ∈ ds ++ ss) (hs : s ∈ ds ++ ss) :
    TemplateCover (encTwoAddr F W 1 op d s Q) :=
  cover_encTwoAddr F W Q d s hop (List.all_eq_true.mp hopd _ hd) (List.all_eq_true.mp hopd _ hs)

/-- The materialised comparison opcodes `setccCmpOp` names are `sete` and `setne`. -/
theorem setccCmpOp_cases {b : String} {op : Nat} (h : setccCmpOp b = some op) :
    op = 0x94 ∨ op = 0x95 := by
  unfold setccCmpOp at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The materialised comparison with an immediate at `REX.W = 1`. -/
theorem cover_encSetccCmpImm {op d a v : Nat} (hop : op = 0x94 ∨ op = 0x95) (hd : d < 16)
    (ha : a < 16) : TemplateCover (encSetccCmpImm 1 op d a v) := by
  unfold encSetccCmpImm
  refine TemplateCover.append (TemplateCover.append ?_ (cover_encMovImmw1_any hd))
    (cover_encSetccReg hop hd)
  split
  · exact cover_encAluImm8 (by decide) ha ‹_›
  · exact cover_encAluImmw_any (by decide) ha

/-- The `ADX` prefixes `adxPrefix` names. -/
theorem adxPrefix_cases {b : String} {p : Nat} (h : adxPrefix b = some p) :
    p = 0x66 ∨ p = 0xf3 := by
  unfold adxPrefix at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> omega

/-- The memory source of a `MULX` has a register base. -/
theorem mulxSrcMem?_fst_lt {F W Q : Nat} {s : String} {p : Nat × Int}
    (h : mulxSrcMem? F W s Q = some p) : p.1 < 16 := by
  unfold mulxSrcMem? at h
  split at h
  · obtain ⟨off, -, rfl⟩ := Option.map_eq_some_iff.mp h
    show 4 < 16
    omega
  · exact parseMemNameGp_fst_lt h

/-- The memory source of a `MULX` among operands of in-range displacements has an in-range
    offset. -/
theorem mulxSrcMem?_disp {F W Q : Nat} {L : List LOperand} {s : String} {p : Nat × Int}
    (hL : L.all (opdDispB F W Q) = true) (h : mulxSrcMem? F W s Q = some p)
    (hn : LOperand.reg s ∈ L) : dispOk32 p.2 = true := by
  unfold mulxSrcMem? at h
  split at h
  · obtain ⟨off, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact disp_of_spill hL he hn
  · exact disp_of_mem hL h hn

/-- The accumulator move of the three-source `ADCX` sequence. -/
theorem cover_accInto {F W Q x : Nat} {an : String} {c : Bool} {mv : List (BitVec 8)}
    (hx : x < 16)
    (h : (if isSpillOrQsave an = true then
        Option.map (fun offA => encRspMem 1 0x8b x offA) (spillQsaveOff F W an Q)
      else if c = true then some [] else some (encAluRRw 1 0x89 x (gpNumU an))) = some mv)
    (hd : ∀ off, spillQsaveOff F W an Q = some off → dispOk32 off = true) :
    TemplateCover mv := by
  split_ifs at h
  · obtain ⟨off, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact cover_encRspMem (Or.inl rfl) hx (hd off he)
  · cases h
    exact TemplateCover.nil
  · cases h
    exact cover_encAluRRw List.mem_cons_self hx (gpNumU_lt_16 _)

/-- The carry addition of the three-source `ADCX` sequence. -/
theorem cover_adxInto {F W Q x pfx : Nat} {sn : String} {ad : List (BitVec 8)}
    (hp : pfx = 0x66 ∨ pfx = 0xf3) (hx : x < 16)
    (h : (if isSpillOrQsave sn = true then
        Option.map (fun offS => encAdxRspMem pfx x offS) (spillQsaveOff F W sn Q)
      else some (encAdxCarry pfx x (gpNumU sn))) = some ad)
    (hd : ∀ off, spillQsaveOff F W sn Q = some off → dispOk32 off = true) :
    TemplateCover ad := by
  split_ifs at h
  · obtain ⟨off, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact cover_encAdxRspMem hp hx (hd off he)
  · cases h
    exact cover_encAdxCarry hp hx (gpNumU_lt_16 _)

/-- The immediate-source form of a base that names no immediate operation has no bytes. -/
theorem cover_encImmOp_other {w : Nat} {b : String} (d : LOperand) (v : Nat)
    (h1 : b ≠ "MOV") (h2 : b ≠ "MOVQ") (h3 : b ≠ "MUL") (h4 : shiftImmExt b = none)
    (h5 : aluImmDigit b = none) : TemplateCover (encImmOp w b d v) := by
  unfold encImmOp
  split
  · split
    · exact TemplateCover.nil
    · dsimp only
      split
      · exact absurd rfl h1
      · exact absurd rfl h2
      · exact absurd rfl h3
      · simp only [h4, h5]
        exact TemplateCover.nil
  · exact TemplateCover.nil

/-- The bases of `widthFreeBase`. -/
theorem widthFreeBase_cases {b : String} (h : widthFreeBase b = true) :
    b = "CASTW_64_16" ∨ b = "CASTW_16_64" ∨ b = "CASTW_16_16" ∨ b = "CASTW_16_32"
      ∨ b = "CASTW_32_16" ∨ b = "CASTW_64_32" ∨ b = "CASTW_32_64" ∨ b = "CASTW_32_32"
      ∨ b = "MULX" ∨ b = "MULXMEM" ∨ b = "SETC" := by
  simp only [widthFreeBase, castMovBits, Bool.or_eq_true, beq_iff_eq] at h
  split at h
  · rename_i hc
    tauto
  · split at h
    · rename_i hc
      tauto
    · simp only [Option.isSome_none, Bool.false_eq_true, false_or] at h
      tauto

/-- The stride of an element access of a link form. -/
theorem idx_of_linkForm {b : String} {ss : List LOperand} {bn i : String} {sc : Nat}
    (hb : (b == "LEA") = false) (hidx : narrowIdxFreeB b ss = true)
    (hm : LOperand.arrIdx bn i sc ∈ ss) : sc = 8 := by
  simp only [narrowIdxFreeB, hb, Bool.false_or, List.all_eq_true] at hidx
  simpa only [beq_iff_eq] using hidx _ hm

/-- The register-indexed load of a link form. -/
theorem cover_encLoadIdx {dn bn i sc : Nat} (hsc : sc = 8) (hi : i < 16) (hi4 : i ≠ 4)
    (hd : dn < 16) (hb : bn < 16) : TemplateCover (encLoadIdx dn bn i sc) := by
  subst hsc
  exact cover_encMemMovSibw (Or.inl rfl) hd hb hi hi4

/-- The register-indexed store of a link form. -/
theorem cover_encStoreIdx {vn bn i sc : Nat} (hsc : sc = 8) (hi : i < 16) (hi4 : i ≠ 4)
    (hv : vn < 16) (hb : bn < 16) : TemplateCover (encStoreIdx vn bn i sc) := by
  subst hsc
  exact cover_encMemMovSibw (Or.inr rfl) hv hb hi hi4

/-- A base that is `LOADIDX` or `STOREIDX` is not `LEA`. -/
theorem ne_lea_of_beq {b c : String} (h : (b == c) = true) (hc : (c == "LEA") = false) :
    (b == "LEA") = false := by
  rw [beq_iff_eq] at h
  subst h
  exact hc

/-- Splits a cover goal: a goal `TemplateCover (if c then a else b)` (or its dependent form)
    by `TemplateCover.ite` (`TemplateCover.dite`), leaving the branch goals under an anonymous
    hypothesis of the condition, and any other head by `split`. -/
local syntax "cover_split" : tactic
local macro_rules
  | `(tactic| cover_split) => `(tactic| first
      | with_reducible refine TemplateCover.ite (fun _ => ?_) (fun _ => ?_)
      | with_reducible refine TemplateCover.dite (fun _ => ?_) (fun _ => ?_)
      | split)

/-- The cover of the bytes of a width cast at a cast base, whose other arms carry no
    bytes. -/
local syntax "lopn_cast_cover" : tactic
local macro_rules
  | `(tactic| lopn_cast_cover) => `(tactic|
    (cover_split
     · exact TemplateCover.nil
     · cover_split
       · cover_split
         · cover_split
           · rename_i hc
             simp only [Bool.and_eq_true] at hc
             exact absurd hc.2 (by decide)
           · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
         · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
       · cover_split
         · cover_split
           · exact cover_encCastW (gpNumU_lt_16 _) (gpNumU_lt_16 _)
           · exact TemplateCover.nil
         · exact TemplateCover.nil
     · cover_split
       · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
       · exact TemplateCover.nil
     · exact TemplateCover.nil
     · exact TemplateCover.nil
     · exact TemplateCover.nil))

/-- The cover of the bytes of a 64-bit instruction of a link form. -/
theorem encodeLopn_cover_w1 {F W Q : Nat} {ds : List LOperand} {o : String}
    {ss : List LOperand} (hadox : ¬ stripWidthTag o = "ADOXHI")
    (hopd : (ds ++ ss).all (opdDispB F W Q) = true)
    (hidx : narrowIdxFreeB (stripWidthTag o) ss = true)
    (hw : LprogBytes.rexW (mnemWidth o) = 1) :
    TemplateCover (encodeLopn F W (.Lopn ds o ss) Q) := by
  · unfold encodeLopn
    simp only [hw]
    cases hco : isCarryOutBinding o
    · cases hmh : LprogAsmPrinter.isMulHiBinding o
      · simp only [Bool.or_self, Bool.false_eq_true, ite_false]
        cases hmx : (stripWidthTag o == "MULX")
        · cases hmm : (stripWidthTag o == "MULXMEM")
          · simp only [Bool.false_eq_true, ite_false]
            cases hax : adxPrefix (stripWidthTag o)
            · dsimp only
              have hR : dispOk32 (-128) = true := by decide
              cover_split
              · cover_split
                · exact cover_setc (gpNumU_lt_16 _)
                · exact TemplateCover.nil
              · cover_split
                · cover_split
                  · cover_split
                    · cover_split
                      · exact TemplateCover.nil
                      · cover_split
                        · rw [ite_self]
                          exact cover_encMovImmRspMem_any (disp_of_spill hopd ‹_› (by simp))
                        · cover_split
                          · exact (((cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 _)
                              hR).append (cover_encMovImm64_of_not_fits (gpNumU_lt_16 _)
                              ‹_›)).append (cover_encRspMem (Or.inr (Or.inl rfl))
                              (gpNumU_lt_16 _) (disp_of_spill hopd ‹_› (by simp)))).append
                              (cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 _) hR)
                          · exact TemplateCover.nil
                    · exact cover_encImmOp _ _ _
                  · exact cover_encImmOp _ _ _
                · cover_split
                  · cover_split
                    · cover_split
                      · cover_split
                        · exact TemplateCover.nil
                        · exact cover_encAluRRw List.mem_cons_self (gpNumU_lt_16 _)
                            (gpNumU_lt_16 _)
                      · refine TemplateCover.append ?_
                          (cover_encTagShift (tagShiftExt_cases ‹_›) (gpNumU_lt_16 _))
                        cover_split
                        · exact TemplateCover.nil
                        · exact cover_encAluRRw List.mem_cons_self (gpNumU_lt_16 _)
                            (gpNumU_lt_16 _)
                    · exact TemplateCover.nil
                  · cover_split
                    · exact cover_encTwoAddr_of F W Q _ _ ‹_› hopd (by simp) (by simp)
                    · cover_split
                      · exact cover_twoByte ‹_› (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                      · cover_split
                        · cover_split
                          · cover_split
                            · cover_split
                              · exact cover_encMemMovw (Or.inr (Or.inr rfl)) (gpNumU_lt_16 _)
                                  (parseMemNameGp_fst_lt ‹_›) (disp_of_mem hopd ‹_› (by simp))
                              · exact TemplateCover.nil
                            · exact TemplateCover.nil
                          · cover_split
                            · rename_i hc
                              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
                              exact cover_leaSib (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                hc.1.2 hc.2
                            · exact TemplateCover.nil
                          · exact TemplateCover.nil
                        · cover_split
                          · cover_split
                            · cover_split
                              · rename_i hc
                                simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
                                have hi4 := hc.2
                                have hsc := idx_of_linkForm
                                  (ne_lea_of_beq ‹_› (by decide)) hidx
                                  (List.mem_singleton_self _)
                                exact cover_encLoadIdx hsc (gpNumU_lt_16 _) hi4 (gpNumU_lt_16 _)
                                  (gpNumU_lt_16 _)
                              · exact TemplateCover.nil
                            · exact TemplateCover.nil
                          · cover_split
                            · cover_split
                              · cover_split
                                · refine TemplateCover.append ?_ (cover_neg (gpNumU_lt_16 _))
                                  cover_split
                                  · exact TemplateCover.nil
                                  · exact cover_encAluRRw List.mem_cons_self (gpNumU_lt_16 _)
                                      (gpNumU_lt_16 _)
                                · exact TemplateCover.nil
                              · exact TemplateCover.nil
                            · cover_split
                              · cover_split
                                · exact cover_encCastW (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                · exact TemplateCover.nil
                              · exact TemplateCover.nil
              · cover_split
                · cover_split
                  · rename_i hse
                    cover_split
                    · cover_split
                      · have hop : (setccCmpOp (stripWidthTag o)).getD 0x94 = 0x94
                            ∨ (setccCmpOp (stripWidthTag o)).getD 0x94 = 0x95 := by
                          simp only [Bool.or_eq_true, beq_iff_eq] at hse
                          rcases hse with h | h <;> simp [h, setccCmpOp]
                        exact cover_encSetccCmpImm hop (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                      · exact TemplateCover.nil
                    · exact TemplateCover.nil
                  · cover_split
                    · exact cover_encZeroArrOp _ _ _
                    · exact cover_encImmOp _ _ _
                · cover_split
                  · exact cover_encTagShift (tagShiftExt_cases ‹_›) (gpNumU_lt_16 _)
                  · cover_split
                    · exact cover_encTwoAddr_of F W Q _ _ ‹_› hopd (by simp) (by simp)
                    · cover_split
                      · exact cover_twoByte ‹_› (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                      · cover_split
                        · cover_split
                          · cover_split
                            · rename_i hc
                              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
                              have hi4 := hc.2
                              have hsc := idx_of_linkForm
                                (ne_lea_of_beq ‹_› (by decide)) hidx List.mem_cons_self
                              exact cover_encStoreIdx hsc (gpNumU_lt_16 _) hi4 (gpNumU_lt_16 _)
                                (gpNumU_lt_16 _)
                            · exact TemplateCover.nil
                          · exact TemplateCover.nil
                        · cover_split
                          · cover_split
                            · cover_split
                              · exact cover_encAluRRw (List.mem_cons_of_mem _ List.mem_cons_self)
                                  (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                              · cover_split
                                · cover_split
                                  · exact cover_encRspMem (Or.inr (Or.inr rfl)) (gpNumU_lt_16 _)
                                      (disp_of_spill hopd ‹_› (by simp))
                                  · exact TemplateCover.nil
                                · exact TemplateCover.nil
                            · exact TemplateCover.nil
                          · cover_split
                            · cover_split
                              · cover_split
                                · cover_split
                                  · exact cover_encShiftX (Or.inl rfl) (gpNumU_lt_16 _)
                                      (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                  · cover_split
                                    · exact cover_encShiftX (Or.inr (Or.inr rfl))
                                        (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                    · exact cover_encShiftX (Or.inr (Or.inl rfl))
                                        (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                · exact TemplateCover.nil
                              · exact TemplateCover.nil
                            · cover_split
                              · cover_split
                                · exact cover_encSetccCmp (setccCmpOp_cases ‹_›) (gpNumU_lt_16 _)
                                    (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                · exact TemplateCover.nil
                              · exact TemplateCover.nil
              · cover_split
                · cover_split
                  · cover_split
                    · exact cover_encCmovSelect (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                        (gpNumU_lt_16 _)
                    · cover_split
                      · cover_split
                        · exact cover_encCmovSelectMem (disp_of_spill hopd ‹_› (by simp))
                            (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                        · exact TemplateCover.nil
                      · cover_split
                        · cover_split
                          · cover_split
                            · cover_split
                              · exact cover_encCmovSelectSlotFE (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                  (disp_of_spill hopd ‹_› (by simp))
                              · exact cover_encCmovSelectSlotF (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                  (gpNumU_lt_16 _) (disp_of_spill hopd ‹_› (by simp))
                            · cover_split
                              · exact cover_encCmovSelectSlotTF (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                  (disp_of_spill hopd ‹_› (by simp))
                                  (disp_of_spill hopd ‹_› (by simp))
                              · exact TemplateCover.nil
                          · cover_split
                            · cover_split
                              · exact cover_encCmovSelectSlotT (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                                  (gpNumU_lt_16 _) (disp_of_spill hopd ‹_› (by simp))
                              · exact TemplateCover.nil
                            · exact TemplateCover.nil
                        · exact TemplateCover.nil
                  · exact TemplateCover.nil
                · cover_split
                  · exact cover_encStoreImmOp _ _ _
                  · exact TemplateCover.nil
              · cover_split
                · exact cover_encZeroArrOp _ _ _
                · exact TemplateCover.nil
              · exact TemplateCover.nil
            · rename_i pfx
              dsimp only
              have hp := adxPrefix_cases hax
              have hR : dispOk32 (-128) = true := by decide
              cover_split
              · cover_split
                · exact TemplateCover.nil
                · cover_split
                  · exact TemplateCover.nil
                  · cover_split
                    · cover_split
                      · exact TemplateCover.nil
                      · cover_split
                        · exact TemplateCover.nil
                        · cover_split
                          · exact TemplateCover.nil
                          · cover_split
                            · cover_split
                              · exact TemplateCover.nil
                              · cover_split
                                · exact ((((((cover_encRspMem (Or.inr (Or.inl rfl))
                                    (gpNumU_lt_16 _) hR).append (cover_encRspMem (Or.inl rfl)
                                    (gpNumU_lt_16 _) (disp_of_spill hopd ‹_› (by simp)))).append
                                    (cover_encBtImm (gpNumU_lt_16 _) (by decide))).append
                                    (cover_accInto (gpNumU_lt_16 _)
                                      ‹_› (fun _ he => disp_of_spill hopd he (by simp)))).append
                                    (cover_adxInto hp (gpNumU_lt_16 _)
                                      ‹_› (fun _ he => disp_of_spill hopd he (by simp)))).append
                                    (cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 _)
                                      (disp_of_spill hopd ‹_› (by simp)))).append
                                    (cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 _) hR)
                                · exact TemplateCover.nil
                            · cover_split
                              · exact (((((cover_encRspMem (Or.inr (Or.inl rfl))
                                  (gpNumU_lt_16 _) hR).append (cover_encRspMem (Or.inl rfl)
                                  (gpNumU_lt_16 _) (disp_of_spill hopd ‹_› (by simp)))).append
                                  (cover_encBtImm (gpNumU_lt_16 _) (by decide))).append
                                  (cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 _) hR)).append
                                  (cover_accInto (gpNumU_lt_16 _)
                                    ‹_› (fun _ he => disp_of_spill hopd he (by simp)))).append
                                  (cover_adxInto hp (gpNumU_lt_16 _)
                                    ‹_› (fun _ he => disp_of_spill hopd he (by simp)))
                              · exact TemplateCover.nil
                    · cover_split
                      · cover_split
                        · exact TemplateCover.nil
                        · cover_split
                          · exact TemplateCover.nil
                          · cover_split
                            · exact TemplateCover.nil
                            · cover_split
                              · exact (((((cover_encBtImm (gpNumU_lt_16 _) (by decide)).append
                                  (cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 _)
                                    hR)).append
                                  (cover_accInto (gpNumU_lt_16 _)
                                    ‹_› (fun _ he => disp_of_spill hopd he (by simp)))).append
                                  (cover_adxInto hp (gpNumU_lt_16 _)
                                    ‹_› (fun _ he => disp_of_spill hopd he (by simp)))).append
                                  (cover_encRspMem (Or.inr (Or.inl rfl)) (gpNumU_lt_16 _)
                                    (disp_of_spill hopd ‹_› (by simp)))).append
                                  (cover_encRspMem (Or.inl rfl) (gpNumU_lt_16 _) hR)
                              · exact TemplateCover.nil
                      · cover_split
                        · exact ((cover_accInto (gpNumU_lt_16 _)
                            ‹_› (fun _ he => disp_of_spill hopd he (by simp))).append
                            (cover_encBtImm (gpNumU_lt_16 _) (by decide))).append
                            (cover_adxInto hp (gpNumU_lt_16 _)
                              ‹_› (fun _ he => disp_of_spill hopd he (by simp)))
                        · exact TemplateCover.nil
              · exact cover_encAdxCarry hp (gpNumU_lt_16 _) (gpNumU_lt_16 _)
              · exact cover_encAdxCarry hp (gpNumU_lt_16 _) (gpNumU_lt_16 _)
              · exact TemplateCover.nil
          · simp only [Bool.false_eq_true, ite_false, ite_true]
            cover_split
            · cover_split
              · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _)
                  (parseMemNameGp_fst_lt ‹_›) (disp_of_mem hopd ‹_› (by simp))
              · exact TemplateCover.nil
            · exact TemplateCover.nil
        · simp only [ite_true]
          cover_split
          · split_ifs
            · exact TemplateCover.nil
            · cover_split
              · exact cover_encMulxSameDstMem (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
                  (mulxSrcMem?_disp hopd ‹_› (by simp))
              · exact TemplateCover.nil
            · cover_split
              · exact cover_encMulxSameDstMem (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
                  (mulxSrcMem?_disp hopd ‹_› (by simp))
              · exact cover_encMulxSameDst (gpNumU_lt_16 _) (gpNumU_lt_16 _)
            · cover_split
              · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
                  (mulxSrcMem?_disp hopd ‹_› (by simp))
              · exact TemplateCover.nil
            · cover_split
              · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
                  (mulxSrcMem?_disp hopd ‹_› (by simp))
              · exact cover_encMulxRR (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
          · exact TemplateCover.nil
      · simp only [Bool.or_true, ite_true, Bool.false_eq_true, ite_false]
        exact TemplateCover.nil
    · simp only [Bool.true_or, ite_true, carryOutSetccOp_of_ne hadox]
      cover_split
      · split_ifs
        · exact cover_setc (gpNumU_lt_16 _)
        · cover_split
          · exact cover_encCarryOutRspMem (disp_of_spill hopd ‹_› (by simp))
          · exact TemplateCover.nil
        · exact TemplateCover.nil
      · exact TemplateCover.nil

/-- The cover of the bytes of a carry-out binding other than `ADOXHI`. -/
theorem encodeLopn_cover_carry {F W Q : Nat} {ds : List LOperand} {o : String}
    {ss : List LOperand} (hadox : ¬ stripWidthTag o = "ADOXHI")
    (hopd : (ds ++ ss).all (opdDispB F W Q) = true) (hcar : isCarryOutBinding o = true) :
    TemplateCover (encodeLopn F W (.Lopn ds o ss) Q) := by
  · unfold encodeLopn
    simp only [hcar, Bool.true_or, ite_true, carryOutSetccOp_of_ne hadox]
    cover_split
    · split_ifs
      · exact cover_setc (gpNumU_lt_16 _)
      · cover_split
        · exact cover_encCarryOutRspMem (disp_of_spill hopd ‹_› (by simp))
        · exact TemplateCover.nil
      · exact TemplateCover.nil
    · exact TemplateCover.nil

/-- The cover of the bytes of an instruction whose base does not depend on the width. -/
theorem encodeLopn_cover_free {F W Q : Nat} {ds : List LOperand} {o : String}
    {ss : List LOperand} (hopd : (ds ++ ss).all (opdDispB F W Q) = true)
    (hfree : widthFreeBase (stripWidthTag o) = true) :
    TemplateCover (encodeLopn F W (.Lopn ds o ss) Q) := by
  · have hb := widthFreeBase_cases hfree
    unfold encodeLopn
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
      simp (config := { decide := true }) only [hb, LprogAsmPrinter.isCarryOutBinding,
        LprogAsmPrinter.isMulHiBinding, adxPrefix, aluOpcode, twoByteOpcode, tagShiftExt,
        castMovBits, setccCmpOp, ite_false, ite_true]
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · lopn_cast_cover
    · cover_split
      · split_ifs
        · exact TemplateCover.nil
        · cover_split
          · exact cover_encMulxSameDstMem (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
              (mulxSrcMem?_disp hopd ‹_› (by simp))
          · exact TemplateCover.nil
        · cover_split
          · exact cover_encMulxSameDstMem (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
              (mulxSrcMem?_disp hopd ‹_› (by simp))
          · exact cover_encMulxSameDst (gpNumU_lt_16 _) (gpNumU_lt_16 _)
        · cover_split
          · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
              (mulxSrcMem?_disp hopd ‹_› (by simp))
          · exact TemplateCover.nil
        · cover_split
          · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _) (mulxSrcMem?_fst_lt ‹_›)
              (mulxSrcMem?_disp hopd ‹_› (by simp))
          · exact cover_encMulxRR (gpNumU_lt_16 _) (gpNumU_lt_16 _) (gpNumU_lt_16 _)
      · exact TemplateCover.nil
    · cover_split
      · cover_split
        · exact cover_encMulxMem (gpNumU_lt_16 _) (gpNumU_lt_16 _)
            (parseMemNameGp_fst_lt ‹_›) (disp_of_mem hopd ‹_› (by simp))
        · exact TemplateCover.nil
      · exact TemplateCover.nil
    · cover_split
      · exact cover_setc (gpNumU_lt_16 _)
      · cover_split
        · cover_split
          · cover_split
            · rename_i hc
              simp only [Bool.and_eq_true] at hc
              exact absurd hc.2 (by decide)
            · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
          · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
        · exact TemplateCover.nil
      · cover_split
        · exact cover_encImmOp_other _ _ (by decide) (by decide) (by decide) rfl rfl
        · exact TemplateCover.nil
      · exact TemplateCover.nil
      · exact TemplateCover.nil
      · exact TemplateCover.nil

/-- **The bytes of an instruction of a link form have a template cover.** -/
theorem encodeLopn_cover (F W Q : Nat) (ds : List LOperand) (o : String) (ss : List LOperand)
    (h : linkFormB F W Q (.Lopn ds o ss) = true) :
    TemplateCover (encodeLopn F W (.Lopn ds o ss) Q) := by
  simp only [linkFormB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hadox, hopd⟩, hnar⟩, hidx⟩ := h
  simp only [narrowFreeB, Bool.or_eq_true, beq_iff_eq] at hnar
  rcases hnar with (hw | hcar) | hfree
  · exact encodeLopn_cover_w1 hadox hopd hidx hw
  · exact encodeLopn_cover_carry hadox hopd hcar
  · exact encodeLopn_cover_free hopd hfree

/-- **Completeness of the piece decoder on the encoder's image.** An encodable instruction
    that is not an `Lgoto` and has a link form has a computed shape. -/
theorem shapeOf_complete (P : Params) (i : LinstrR)
    (henc : encodableLinstrR P.frame P.spillW i P.qsaveB = true) (hgoto : ∀ t, i ≠ .Lgoto t)
    (hform : linkFormB P.frame P.spillW P.qsaveB i = true) :
    (shapeOf P i).isSome = true :=
  shapeOf_isSome_of_encodable P i henc hgoto fun ds o ss hi => by
    subst hi
    exact encodeLopn_cover _ _ _ ds o ss hform

/-- **The shapes of an encodable body of link forms.** A body accepted by `encodableLcmd`,
    with no `Lgoto`, whose instructions have link forms at the parameters of the body, has
    shapes. -/
theorem shapesOf_isSome_of_encodableLcmd (body : Lcmd) (henc : encodableLcmd body = true)
    (hgoto : ∀ i ∈ body, ∀ t, i.li_i ≠ .Lgoto t)
    (hform : ∀ i ∈ body, linkFormB (Params.ofBody body).frame (Params.ofBody body).spillW
      (Params.ofBody body).qsaveB i.li_i = true) :
    (shapesOf (Params.ofBody body) body).isSome = true :=
  shapesOf_isSome_of_encodable body henc hgoto fun i hi ds o ss he => by
    have h := hform i hi
    rw [he] at h
    exact encodeLopn_cover _ _ _ ds o ss h

/-- **The conditions on a body of a caller of `name`** under which the link check accepts it:
    no `Lgoto`, a link form for every instruction, no conditional branch, every call a call of
    `name`, and no register saved by `push`. -/
structure LinkFormBody (name : String) (body : Lcmd) : Prop where
  /-- No instruction is an `Lgoto`. -/
  noGoto : ∀ i ∈ body, ∀ t, i.li_i ≠ .Lgoto t
  /-- Every instruction has a link form at the parameters of the body. -/
  form : ∀ i ∈ body, linkFormB (Params.ofBody body).frame (Params.ofBody body).spillW
    (Params.ofBody body).qsaveB i.li_i = true
  /-- No instruction is a conditional branch. -/
  noCond : ∀ i ∈ body, ∀ c l, i.li_i ≠ .Lcond c l
  /-- Every call calls `name`. -/
  callName : ∀ i ∈ body, ∀ ra t, i.li_i = .Lcall ra t → t.1 = name
  /-- No register is saved by `push`. -/
  noSaves : calleeSavedToSave body = []

/-- A body of `LinkFormBody` satisfies `LinkBody`: the template covers follow from the link
    forms (`encodeLopn_cover`). -/
theorem LinkFormBody.linkBody {name : String} {body : Lcmd} (hb : LinkFormBody name body) :
    LinkBody name body :=
  ⟨hb.noGoto, fun i hi ds o ss he => by
    have h := hb.form i hi
    rw [he] at h
    exact encodeLopn_cover _ _ _ ds o ss h, hb.noCond, hb.callName, hb.noSaves⟩

/-- **(2) The x86 link check on an encodable body of link forms.** The check
    `x86LinkB name code body` accepts a body accepted by `encodableLcmd` that satisfies
    `LinkFormBody name body`, at a nonempty code and a nonempty symbol, when the function bytes
    of the relocating encoder are shorter than `2 ^ 31`. -/
theorem x86LinkB_of_encodable (name : String) (code : List (BitVec 8)) (body : Lcmd)
    (hcode : code ≠ []) (hname : name ≠ "") (henc : encodableLcmd body = true)
    (hb : LinkFormBody name body)
    (hdist : (encodeLfundefBytesReloc (VIR.LprogIsa.x86LinkSym name body) body).length
      < 2 ^ 31) :
    VIR.LprogIsa.x86LinkB name code body = true :=
  x86LinkB_of_cover name code body hcode hname henc hb.linkBody hdist

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkShapeComplete
