/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

@[expose] public section

set_option autoImplicit false

/-!
# Computed decode shapes of a body

`PhysAbiShape.decodeLprog_encodeLfundefBytes_shapes` decodes the function bytes of a body
given one list-valued shape `DShape` per instruction, each satisfying `DShapeOK`. This module
computes that list from the body.

## The shape of one instruction

`shapeOf P i` reads the bytes the encoder lays down for an `Lopn` and splits them into
pieces, one decoded instruction each (`splitPieces`). The decoder `decodeLinstr` proposes the
instruction and the length of each piece; a piece is accepted only when it is the image of
its instruction under one of the byte templates `pieceTemplates`, each of which carries a
round-trip lemma of the form `decodeLinstr (bytes ++ rest) = some (.op j, rest)` for every
continuation `rest` (`pieceTemplates_sound`). The templates are the encoder forms of
`LprogBytesDecode` over register numbers (register copies and the group-1 `ALU` forms, the
compares, the sign-extended `imm8` forms, the `%rsp`-relative loads, stores, compares and
`cmovne`, the indexed moves, the `D1` shifts, `neg`, `setcc`, the BMI2 variable shifts, the
indexed `lea`) and every instruction
`SailX86Decoder.encodeJInstr` encodes and `decodeJ1` inverts (`roundtrip_decodeJ1`), at the
identity allocation on the canonical `%rN` names. The template set is a closed list, so the
proposal of the decoder is checked rather than trusted. Labels, `Lret` and `Lalign` carry no
bytes; conditional branches and calls take the branch shapes of `LprogBytesDecode`.

## Main results

* `pieceTemplates_sound`: every template decodes, in front of every continuation, to its
  instruction.
* `splitPieces_sound`: the accepted pieces concatenate to the input bytes and each decodes to
  its instruction in front of every continuation.
* `shapeOf_ok`: every shape `shapeOf` returns satisfies `DShapeOK`.
* `shapesOf_forall₂`: the computed shape list of a body satisfies `DShapeOK` instruction by
  instruction.
* `decodeLprog_encodeLfundefBytes_gen`: the function bytes of a body whose shapes are
  computed decode to the program of its item list.
* `decodeLprog_node_gen`: the function bytes of a guarded loop node whose prefix, loop body
  and suffix have computed straight-line shapes decode to `nodeLayout` over the computed
  decoded instructions.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (LinstrR Linstr Lcmd LLabel LabelKind LOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop)

/-! ## 1. Register numbers -/

/-- The register number whose canonical name is `r`. -/
def regNum? (r : String) : Option Nat := (List.range 16).find? (fun n => regName n == r)

theorem regNum?_spec {r : String} {n : Nat} (h : regNum? r = some n) :
    n < 16 ∧ regName n = r := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.mp h2, by simpa using h1⟩

/-- The identity allocation on the sixteen canonical `%rN` names. -/
def canonAlloc (_ : Unit) : GpAlloc := (List.range 16).map (fun n => (regName n, regName n))

/-! ## 2. Byte templates -/

/-- A byte string and an instruction: the string decodes, in front of every continuation,
    to the instruction and that continuation. -/
def PieceDec (q : List (BitVec 8) × JInstr 64) : Prop :=
  ∀ rest, decodeLinstr (q.1 ++ rest) = some (.op q.2, rest)

/-- The legacy `ALU` opcodes of the register-register forms. -/
def aluOps : List Nat := [0x01, 0x09, 0x11, 0x19, 0x21, 0x29, 0x31]

/-- The register-register templates on registers `d` (the `r/m` field) and `s`. -/
def tmplRR (d s : Nat) : List (List (BitVec 8) × JInstr 64) :=
  (encAluRRw 1 0x89 d s, .mov (regName d) (.reg (regName s)))
    :: (encAluRRw 1 0x39 d s, .cmp (regName d) (.reg (regName s)))
    :: aluOps.filterMap (fun op => (aluMnemonic op).map
        (fun mk => (encAluRRw 1 op d s, mk (regName d) (.reg (regName s)))))

/-- The immediate templates on register `d` and value `v`: the two `MOV` immediate forms,
    the sign-extended `imm8` group-1 forms and `IMUL`, and the `D1` shifts by one. -/
def tmplImm (d v : Nat) : List (List (BitVec 8) × JInstr 64) :=
  (if decide (v < 2 ^ 64) && fitsImm32S v then [(encMovImmw 1 d v, .mov (regName d) (.imm v))]
    else [])
  ++ (if decide (v < 2 ^ 32) then
      [(encMovImmw 0 d v, .mov (regName d) (.imm v))] else [])
  ++ (if fitsImm8S 1 v then
      (List.range 8).filterMap (fun dig => (aluImm8Mnemonic dig).map
        (fun mk => (encAluImm8 1 dig d v, mk (regName d) (.imm v))))
      ++ [(encImulImm8w 1 d v, .imulri (regName d) (regName d) v)] else [])
  ++ (if v == 1 then [4, 5, 7].map (fun ext => (encShift1 1 ext d,
      (if ext = 4 then JInstr.shl else if ext = 5 then JInstr.shr else JInstr.sar)
        (regName d) (.imm 1))) else [])

/-- The one-register templates: `neg` and the byte `setcc` of the zero flag. -/
def tmpl1 (d : Nat) : List (List (BitVec 8) × JInstr 64) :=
  (ScalarEncoder.encUnaryF7 3 d, .neg (regName d))
    :: [0x94, 0x95].map (fun op =>
      (encSetccReg op d, .setcc (if op = 0x94 then .e else .ne) (regName d)))

/-- The `%rsp`-relative templates on register `r` at displacement `off`: load, store,
    compare, and the conditional move `cmovne` from the frame word. -/
def tmplRsp (r : Nat) (off : Int) : List (List (BitVec 8) × JInstr 64) :=
  if dispOk32 off then
    [(encRspMem 1 0x8b r off, .loadMem (regName r) "%rsp" off),
     (encRspMem 1 0x89 r off, .storeMem "%rsp" off (.reg (regName r))),
     (encRspMem 1 0x3b r off, .cmpMem (regName r) "%rsp" off),
     (encCmovRspMem 1 0x45 r off, .cmovccMem .ne (regName r) "%rsp" off)]
  else []

/-- The indexed-move templates at scale `8`: register `r`, base `b`, index `i`. -/
def tmplIdx (r b i : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if b &&& 7 != 5 && i != 4 then
    [(encMemMovSibw 1 0x8b r b i 8, .loadMemIdx (regName r) (regName b) (regName i) 8),
     (encMemMovSibw 1 0x89 r b i 8, .storeMemIdx (regName b) (regName i) 8 (.reg (regName r)))]
  else []

/-- The three-register templates: the BMI2 variable shifts. -/
def tmpl3 (d s c : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [4, 5, 7].map (fun ext => (encShiftX ext d s c,
    (if ext = 4 then JInstr.shlx else if ext = 5 then JInstr.shrx else JInstr.sarx)
      (regName d) (regName s) (regName c)))

/-- The width-cast templates on registers `d` (the destination) and `s`: the zero-extending
    moves of the low 16 and the low 32 bits behind a `REX` prefix at `REX.W = 0`. -/
def tmplCast (d s : Nat) : List (List (BitVec 8) × JInstr 64) :=
  [(encMovzx16RR d s, .movzx (regName d) 16 (regName s)),
   (encMov32RR d s, .movzx (regName d) 32 (regName s))]

/-- The template of `encodeJInstr` at the identity allocation, for an instruction in the
    covered set of `roundtrip_decodeJ1` over canonical names. -/
def tmplJ (j : JInstr 64) : List (List (BitVec 8) × JInstr 64) :=
  if decodableJ j && mulxRdxOk (canonAlloc ()) j && decide (renameJ (canonAlloc ()) j = j) then
    [(encodeJInstr (canonAlloc ()) j, j)]
  else []

/-- The template of the indexed address computation `LEA (%b,%i,s), %d` (`REX.W 8D /r` with a
    SIB byte, no displacement) at the register numbers of the names of `j`, for `j` an `lea`
    with displacement `0`, an index other than `%rsp` and a stride SIB encodes. -/
def tmplLea : JInstr 64 → List (List (BitVec 8) × JInstr 64)
  | .lea d b i s 0 =>
      match regNum? d, regNum? b, regNum? i with
      | some r, some bn, some x =>
          if x != 4 && scaleOk s then
            [(encMemMovSibw 1 0x8d r bn x s, .lea (regName r) (regName bn) (regName x) s 0)]
          else []
      | _, _, _ => []
  | _ => []

/-- The register names of an operand. -/
def opNames : JOperand → List String
  | .reg r => [r]
  | .imm _ => []

/-- The immediates of an operand. -/
def opImms : JOperand → List Nat
  | .reg _ => []
  | .imm v => [v]

/-- The register names, immediates and displacements of an instruction that the templates
    are instantiated at. The lists are proposals: a template is accepted only when its
    instruction equals the decoded one. -/
def guess : JInstr 64 → List String × List Nat × List Int
  | .mov d s | .add d s | .sub d s | .adc d s | .sbb d s | .imul d s | .and_ d s
  | .or_ d s | .xor_ d s | .cmp d s | .shl d s | .shr d s | .sar d s =>
      (d :: opNames s, opImms s, [])
  | .neg d | .setcc _ d => ([d], [], [])
  | .imulri d s v => ([d, s], [v], [])
  | .loadMem d b off | .cmpMem d b off | .cmovccMem _ d b off => ([d, b], [], [off])
  | .storeMem b off s => (b :: opNames s, [], [off])
  | .loadMemIdx d b i _ => ([d, b, i], [], [])
  | .storeMemIdx b i _ s => (b :: i :: opNames s, [], [])
  | .shlx d s c | .shrx d s c | .sarx d s c => ([d, s, c], [], [])
  | .movzx d _ s => ([d, s], [], [])
  | _ => ([], [], [])

/-- The byte templates an instruction is checked against. -/
def pieceTemplates (j : JInstr 64) : List (List (BitVec 8) × JInstr 64) :=
  let g := guess j
  let ns := g.1.filterMap regNum?
  tmplJ j ++ tmplLea j ++ ns.flatMap (fun d =>
    ns.flatMap (fun s => tmplRR d s ++ tmplCast d s
        ++ ns.flatMap (fun c => tmplIdx d s c ++ tmpl3 d s c))
      ++ g.2.1.flatMap (tmplImm d) ++ tmpl1 d ++ g.2.2.flatMap (tmplRsp d))

/-! ## 3. Soundness of the templates -/

theorem tmplRR_sound (d s : Nat) (hd : d < 16) (hs : s < 16) :
    ∀ q ∈ tmplRR d s, PieceDec q := by
  intro q hq rest
  simp only [tmplRR, List.mem_cons, List.mem_filterMap, Option.map_eq_some_iff] at hq
  rcases hq with rfl | rfl | ⟨op, hop, mk, hmk, rfl⟩
  · exact decodeLinstr_movRR d s rest hd hs
  · exact decodeLinstr_cmpRR d s rest hd hs
  · have htab : aluTableOp op = true := by
      simp only [aluOps, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact decodeLinstr_aluRR op mk d s rest hd hs htab hmk

/-- The 32-bit `MOV $imm32, %r32` with the `REX.B` prefix `41` (`41 B8+rd id`), for a
    destination among `r8`–`r15` and a value below `2 ^ 32`, decodes to the 64-bit `MOV` of
    the value: the 32-bit write zero-extends into the 64-bit register. -/
theorem decodeLinstr_movImm32_rex (d v : Nat) (rest : List (BitVec 8)) (hd8 : 8 ≤ d)
    (hd : d < 16) (hv : v < 2 ^ 32) :
    decodeLinstr (encMovImmw 0 d v ++ rest) = some (.op (.mov (regName d) (.imm v)), rest) := by
  have hb : bit d 3 = 1 := by
    simp only [bit]
    interval_cases d <;> rfl
  have hrex : rexOpt 0 0 0 1 = [BitVec.ofNat 8 0x41] := by decide
  have hop : (BitVec.ofNat 8 (0xb8 + d % 8)).toNat = 0xb8 + (d - 8) := by
    rw [BitVec.toNat_ofNat]; omega
  apply decodeLinstr_of_decodeJ1
  simp only [encMovImmw, if_true, hb, hrex, imm32LE, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append]
  have hr : isRex (BitVec.ofNat 8 0x41) = true := by decide
  have hw : rexW (BitVec.ofNat 8 0x41) = 0 := by decide
  have hB : rexB (BitVec.ofNat 8 0x41) = 1 := by decide
  have e1 : ¬ (BitVec.ofNat 8 0x41 : BitVec 8).toNat = 0x66 := by decide
  have e2 : ¬ (BitVec.ofNat 8 0x41 : BitVec 8).toNat = 0xf3 := by decide
  have e3 : ¬ (BitVec.ofNat 8 0x41 : BitVec 8).toNat = 0xc4 := by decide
  have g1 : ¬ 0xb8 + (d - 8) = 0x0f := by omega
  have g2 : 0xb8 ≤ 0xb8 + (d - 8) ∧ 0xb8 + (d - 8) ≤ 0xbf := by omega
  have hd' : 1 * 8 + (0xb8 + (d - 8) - 0xb8) = d := by omega
  simp only [decodeJ1, e1, e2, e3, hr, hw, decodeRexW0, hop, g1, g2, hB, hd',
    imm32LE_recompose v hv, if_false, if_true, zero_ne_one, and_self]

theorem tmplImm_sound (d v : Nat) (hd : d < 16) : ∀ q ∈ tmplImm d v, PieceDec q := by
  intro q hq rest
  simp only [tmplImm, List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · split at hq
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [List.mem_singleton] at hq
      subst hq
      exact decodeLinstr_movImm d v rest hd hc.1 hc.2
    · simp at hq
  · split at hq
    · rename_i hc
      simp only [decide_eq_true_eq] at hc
      simp only [List.mem_singleton] at hq
      subst hq
      by_cases h8 : d < 8
      · exact decodeLinstr_movImm32 d v rest h8 hc
      · exact decodeLinstr_movImm32_rex d v rest (by omega) hd hc
    · simp at hq
  · split at hq
    · rename_i hc
      simp only [List.mem_append, List.mem_filterMap, Option.map_eq_some_iff,
        List.mem_singleton, List.mem_range] at hq
      rcases hq with ⟨dig, hdig, mk, hmk, rfl⟩ | rfl
      · exact decodeLinstr_aluImm8 dig mk d v rest hdig hd hc hmk
      · exact decodeLinstr_imulImm8 d v rest hd hc
    · simp at hq
  · split at hq
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hq
      obtain ⟨ext, hext, rfl⟩ := hq
      exact decodeLinstr_shift1 ext d rest hext hd
    · simp at hq

theorem tmpl1_sound (d : Nat) (hd : d < 16) : ∀ q ∈ tmpl1 d, PieceDec q := by
  intro q hq rest
  simp only [tmpl1, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | ⟨op, hop, rfl⟩
  · exact decodeLinstr_neg d rest hd
  · exact decodeLinstr_setccReg op d rest hop hd

theorem tmplRsp_sound (r : Nat) (off : Int) (hr : r < 16) :
    ∀ q ∈ tmplRsp r off, PieceDec q := by
  intro q hq rest
  simp only [tmplRsp] at hq
  split at hq
  · rename_i hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact decodeLinstr_rspLoad r off rest hr hoff
    · exact decodeLinstr_rspStore r off rest hr hoff
    · exact decodeLinstr_rspCmp r off rest hr hoff
    · exact decodeLinstr_rspCmov .ne r off rest hr hoff
  · simp at hq

theorem tmplIdx_sound (r b i : Nat) (hr : r < 16) (hb : b < 16) (hi : i < 16) :
    ∀ q ∈ tmplIdx r b i, PieceDec q := by
  intro q hq rest
  simp only [tmplIdx] at hq
  split at hq
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact decodeLinstr_loadIdx8 r b i rest hr hb hi hc.1 hc.2
    · exact decodeLinstr_storeIdx8 r b i rest hr hb hi hc.1 hc.2
  · simp at hq

theorem tmpl3_sound (d s c : Nat) (hd : d < 16) (hs : s < 16) (hc : c < 16) :
    ∀ q ∈ tmpl3 d s c, PieceDec q := by
  intro q hq rest
  simp only [tmpl3, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hq
  obtain ⟨ext, hext, rfl⟩ := hq
  exact decodeLinstr_shiftX ext d s c rest hext hd hs hc

theorem tmplCast_sound (d s : Nat) (hd : d < 16) (hs : s < 16) :
    ∀ q ∈ tmplCast d s, PieceDec q := by
  intro q hq rest
  simp only [tmplCast, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact decodeLinstr_movzx16RR d s rest hd hs
  · exact decodeLinstr_mov32RR d s rest hd hs

theorem tmplJ_sound (j : JInstr 64) : ∀ q ∈ tmplJ j, PieceDec q := by
  intro q hq rest
  simp only [tmplJ] at hq
  split at hq
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [List.mem_singleton] at hq
    subst hq
    have h := roundtrip_decodeJ1 (canonAlloc ()) j rest hc.1.1 hc.1.2
    rw [hc.2] at h
    exact decodeLinstr_of_decodeJ1 h
  · simp at hq

theorem tmplLea_sound (j : JInstr 64) : ∀ q ∈ tmplLea j, PieceDec q := by
  intro q hq rest
  unfold tmplLea at hq
  split at hq
  · split at hq
    · rename_i r bn x hr hb hx
      split at hq
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        simp only [List.mem_singleton] at hq
        subst hq
        exact decodeLinstr_leaIdx r bn x _ rest (regNum?_spec hr).1 (regNum?_spec hb).1
          (regNum?_spec hx).1 hc.1 hc.2
      · simp at hq
    · simp at hq
  · simp at hq

/-- **Every template decodes to its instruction.** -/
theorem pieceTemplates_sound (j : JInstr 64) : ∀ q ∈ pieceTemplates j, PieceDec q := by
  intro q hq
  simp only [pieceTemplates, List.mem_append, List.mem_flatMap] at hq
  have hn : ∀ n ∈ (guess j).1.filterMap regNum?, n < 16 := fun n hn => by
    obtain ⟨r, _, hr⟩ := List.mem_filterMap.mp hn
    exact (regNum?_spec hr).1
  rcases hq with (hq | hq) | ⟨d, hd, hq⟩
  · exact tmplJ_sound j q hq
  · exact tmplLea_sound j q hq
  · rcases hq with (((⟨s, hs, hq⟩ | ⟨v, _, hq⟩) | hq) | ⟨off, _, hq⟩)
    · rcases hq with (hq | hq) | ⟨c, hc, hq⟩
      · exact tmplRR_sound d s (hn d hd) (hn s hs) q hq
      · exact tmplCast_sound d s (hn d hd) (hn s hs) q hq
      · rcases hq with hq | hq
        · exact tmplIdx_sound d s c (hn d hd) (hn s hs) (hn c hc) q hq
        · exact tmpl3_sound d s c (hn d hd) (hn s hs) (hn c hc) q hq
    · exact tmplImm_sound d v (hn d hd) q hq
    · exact tmpl1_sound d (hn d hd) q hq
    · exact tmplRsp_sound d off (hn d hd) q hq

/-! ## 4. Splitting the bytes of one instruction -/

/-- Split a byte string into pieces of one decoded instruction each: `decodeLinstr` proposes
    the instruction and the length of the next piece, and the piece is kept when it is a
    template of its instruction. `none` when a piece is not accepted. -/
def splitPieces : Nat → List (BitVec 8) → Option (List (List (BitVec 8) × JInstr 64))
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, b :: bs =>
      match decodeLinstr (b :: bs) with
      | some (.op j, r) =>
          let k := (b :: bs).length - r.length
          if decide (0 < k) && decide (((b :: bs).take k, j) ∈ pieceTemplates j) then
            (splitPieces n ((b :: bs).drop k)).map (((b :: bs).take k, j) :: ·)
          else none
      | _ => none

/-- **The accepted pieces.** They concatenate to the input bytes, and each decodes, in front
    of every continuation, to its instruction. -/
theorem splitPieces_sound :
    ∀ (n : Nat) (bs : List (BitVec 8)) (pcs : List (List (BitVec 8) × JInstr 64)),
      splitPieces n bs = some pcs → pcs.flatMap Prod.fst = bs ∧ ∀ q ∈ pcs, PieceDec q := by
  intro n
  induction n with
  | zero =>
    intro bs pcs h
    cases bs with
    | nil =>
      simp only [splitPieces, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons b bs => simp [splitPieces] at h
  | succ n ih =>
    intro bs pcs h
    cases bs with
    | nil =>
      simp only [splitPieces, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons b bs =>
      simp only [splitPieces] at h
      split at h
      · rename_i j r _
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨pcs', hs, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hcat, hok⟩ := ih _ _ hs
          refine ⟨?_, ?_⟩
          · simp only [List.flatMap_cons, hcat, List.take_append_drop]
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact pieceTemplates_sound j _ hc.2
            · exact hok q hq
        · simp at h
      · simp at h

/-! ## 5. The shape of an instruction -/

/-- The shape of an instruction whose bytes are `bs`: one decoded instruction as a single
    shape, any other number of pieces as a run. -/
def shapeOfBytes (bs : List (BitVec 8)) : Option DShape :=
  match splitPieces bs.length bs with
  | some [q] => some (.one (.op q.2))
  | some pcs => some (.ops pcs)
  | none => none

/-- The shape of an instruction under the body parameters `P`: the computed pieces of an
    `Lopn`; nothing for a label, `Lret` and `Lalign`; the branch shapes of a conditional
    branch and a call. `none` on every other instruction and when a piece is not accepted. -/
def shapeOf (P : Params) : LinstrR → Option DShape
  | .Lopn ds o ss => shapeOfBytes (encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB)
  | .Llabel _ _ => some (.one .skip)
  | .Lret => some (.one .skip)
  | .Lalign => some (.one .skip)
  | .Lcond (.reg cc) l => some (.one (.jcc (ccNibble cc) l))
  | .Lcall _ (_, l) => some (.one (.call l))
  | _ => none

theorem shapeOfBytes_ok {bs : List (BitVec 8)} {sh : DShape} (h : shapeOfBytes bs = some sh) :
    (∃ q, sh = .one (.op q.2) ∧ bs = q.1 ∧ PieceDec q)
      ∨ (∃ pcs, sh = .ops pcs ∧ pcs.flatMap Prod.fst = bs ∧ ∀ q ∈ pcs, PieceDec q) := by
  unfold shapeOfBytes at h
  split at h
  · rename_i q hs
    obtain ⟨hcat, hok⟩ := splitPieces_sound _ _ _ hs
    simp only [Option.some.injEq] at h
    refine Or.inl ⟨q, h.symm, ?_, hok q (List.mem_singleton_self q)⟩
    simpa using hcat.symm
  · rename_i pcs _ hs
    obtain ⟨hcat, hok⟩ := splitPieces_sound _ _ _ hs
    simp only [Option.some.injEq] at h
    exact Or.inr ⟨pcs, h.symm, hcat, hok⟩
  · simp at h

/-- **Computed shapes are sound.** Every shape `shapeOf` returns satisfies `DShapeOK`. -/
theorem shapeOf_ok (P : Params) (i : LinstrR) (sh : DShape) (h : shapeOf P i = some sh) :
    DShapeOK P i sh := by
  cases i with
  | Lopn ds o ss =>
    rcases shapeOfBytes_ok h with ⟨q, rfl, hb, hq⟩ | ⟨pcs, rfl, hb, hq⟩
    · intro d
      show ItemOK ⟨encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB, some (.op q.2),
        none, none⟩
      rw [hb]
      exact ItemOK_of_decode hq
    · exact ⟨rfl, fun _ => hb.symm, fun q hq' => ItemOK_of_decode (hq q hq')⟩
  | Llabel k l =>
    simp only [shapeOf, Option.some.injEq] at h
    subst h
    exact shapeOK_label P k l
  | Lret =>
    simp only [shapeOf, Option.some.injEq] at h
    subst h
    exact shapeOK_ret P
  | Lalign =>
    simp only [shapeOf, Option.some.injEq] at h
    subst h
    exact fun _ => rfl
  | Lcond c l =>
    cases c with
    | reg cc =>
      simp only [shapeOf, Option.some.injEq] at h
      subst h
      exact shapeOK_cond P cc l
    | _ => simp [shapeOf] at h
  | Lcall ra t =>
    obtain ⟨f, l⟩ := t
    simp only [shapeOf, Option.some.injEq] at h
    subst h
    exact shapeOK_call P ra f l
  | _ => simp [shapeOf] at h

/-- An instruction whose computed shape is one straight-line instruction defines no label. -/
theorem labelOf_of_shapeOf_op {P : Params} {i : LinstrR} {x : JInstr 64}
    (h : shapeOf P i = some (.one (.op x))) : labelOf i = none := by
  cases i with
  | Llabel k l => simp [shapeOf] at h
  | _ => rfl

/-- An instruction whose computed shape is a conditional branch defines no label. -/
theorem labelOf_of_shapeOf_jcc {P : Params} {i : LinstrR} {cc : Nat} {l : LLabel}
    (h : shapeOf P i = some (.one (.jcc cc l))) : labelOf i = none := by
  cases i with
  | Llabel k l => simp [shapeOf] at h
  | _ => rfl

/-! ## 6. The shapes of a body -/

/-- The computed shapes of a body, `none` when one instruction has none. -/
def shapesOf (P : Params) : Lcmd → Option (List DShape)
  | [] => some []
  | i :: b =>
      match shapeOf P i.li_i, shapesOf P b with
      | some sh, some shs => some (sh :: shs)
      | _, _ => none

theorem shapesOf_forall₂ (P : Params) :
    ∀ (body : Lcmd) (shs : List DShape), shapesOf P body = some shs →
      List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh) body shs := by
  intro body
  induction body with
  | nil =>
    intro shs h
    simp only [shapesOf, Option.some.injEq] at h
    subst h
    exact .nil
  | cons i b ih =>
    intro shs h
    simp only [shapesOf] at h
    split at h
    · rename_i sh shs' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      exact .cons (shapeOf_ok P _ _ h1) (ih _ h2)
    · simp at h

/-- The computed shapes of a body, the empty list when there are none. -/
def shapesD (P : Params) (b : Lcmd) : List DShape := (shapesOf P b).getD []

/-- The decoded straight-line instructions of a body's computed shapes. -/
def opsD (P : Params) (b : Lcmd) : List (JInstr 64) := (shapesD P b).flatMap DShape.ops'

/-- **Function round trip over computed shapes.** A body that saves no register by `push`,
    with a non-zero frame in `rel32` range, whose shapes are computed and whose branches are
    well formed, decodes to the program its item list denotes. -/
theorem decodeLprog_encodeLfundefBytes_gen (body : Lcmd)
    (hsh : (shapesOf (Params.ofBody body) body).isSome = true)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : (Int.ofNat (Params.ofBody body).frame) ≠ 0)
    (hF : dispOk32 (Int.ofNat (Params.ofBody body).frame) = true)
    (hF' : dispOk32 (-(Int.ofNat (Params.ofBody body).frame)) = true)
    (hbr : branchOK (fundefItemsL body (shapesD (Params.ofBody body) body)) 0
      (fundefItemsL body (shapesD (Params.ofBody body) body)) = true) :
    decodeLprog (encodeLfundefBytes body)
      = expectedFrom (fundefItemsL body (shapesD (Params.ofBody body) body))
          (fundefItemsL body (shapesD (Params.ofBody body) body)) := by
  obtain ⟨shs, hs⟩ := Option.isSome_iff_exists.mp hsh
  have hD : shapesD (Params.ofBody body) body = shs := by simp [shapesD, hs]
  rw [hD] at hbr ⊢
  exact decodeLprog_encodeLfundefBytes_shapes body shs hsaves hF0 hF hF'
    (shapesOf_forall₂ _ _ _ hs) hbr

/-! ## 7. A guarded loop node -/

/-- A shape that decodes to straight-line instructions only, as a Boolean. -/
def straightB : DShape → Bool
  | .one .skip => true
  | .one (.op _) => true
  | .one (.jcc _ _) => false
  | .one (.call _) => false
  | .ops _ => true

theorem straight_of_straightB {sh : DShape} (h : straightB sh = true) : sh.Straight := by
  cases sh with
  | one s => cases s <;> simp_all [straightB, DShape.Straight]
  | ops _ => trivial

/-- A straight-line segment: its shapes are computed, all straight, and it defines no
    label. -/
def straightOK (P : Params) (b : Lcmd) : Bool :=
  match shapesOf P b with
  | some s => s.all straightB && b.all (fun i => (labelOf i.li_i).isNone)
  | none => false

theorem forall₂_of_straightOK {P : Params} {b : Lcmd} (h : straightOK P b = true) :
    List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh ∧ sh.Straight
      ∧ labelOf instr.li_i = none) b (shapesD P b) := by
  unfold straightOK at h
  split at h
  · rename_i s hs
    have hD : shapesD P b = s := by simp [shapesD, hs]
    rw [hD]
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hst, hlab⟩ := h
    have hF := shapesOf_forall₂ P b s hs
    clear hs hD
    induction hF with
    | nil => exact .nil
    | @cons i sh b s hab _ ih =>
      refine .cons ⟨hab, straight_of_straightB (hst sh (by simp)), ?_⟩
        (ih (fun x hx => hst x (by simp [hx])) (fun x hx => hlab x (by simp [hx])))
      simpa using hlab i (by simp)
  · simp at h

/-- The computed shape list of a guarded loop node: the prefix, the guard, the loop body,
    the back-edge, the suffix and the return. -/
def nodeShapes (P : Params) (P1 L P2 : Lcmd) (ctr : String) (top endL : LLabel) :
    List DShape :=
  shapesD P P1 ++ .one (.op (.cmp ctr (.imm 0))) :: .one (.jcc 4 endL) :: .one .skip
    :: (shapesD P L ++ .one (.op (.cmp ctr (.imm 0))) :: .one (.jcc 5 top) :: .one .skip
      :: (shapesD P P2 ++ [.one .skip]))

/-- **The decoded bytes of a guarded loop node, over computed shapes.** A body that saves no
    register by `push`, with a non-zero frame in `rel32` range, laid out as a straight-line
    prefix `P1`, the guard, a straight-line loop body `L`, the back-edge, a straight-line
    suffix `P2` and the return, whose segments have computed straight-line shapes, whose
    guard and back-edge compares and branches have the computed shapes of the node, and
    whose branches are well formed, decodes to the node layout over the computed decoded
    instructions of the three segments. -/
theorem decodeLprog_node_gen (body P1 L P2 : Lcmd) (g1 g2 g3 b1 b2 b3 r : Linstr)
    (top endL : LLabel) (ctr : String) (k1 k2 : LabelKind)
    (hbody : body = P1 ++ g1 :: g2 :: g3 :: (L ++ b1 :: b2 :: b3 :: (P2 ++ [r])))
    (h1 : straightOK (Params.ofBody body) P1 = true)
    (hL : straightOK (Params.ofBody body) L = true)
    (h2 : straightOK (Params.ofBody body) P2 = true)
    (hg1 : shapeOf (Params.ofBody body) g1.li_i = some (.one (.op (.cmp ctr (.imm 0)))))
    (hg2 : shapeOf (Params.ofBody body) g2.li_i = some (.one (.jcc 4 endL)))
    (hg3 : g3.li_i = .Llabel k1 top)
    (hb1 : shapeOf (Params.ofBody body) b1.li_i = some (.one (.op (.cmp ctr (.imm 0)))))
    (hb2 : shapeOf (Params.ofBody body) b2.li_i = some (.one (.jcc 5 top)))
    (hb3 : b3.li_i = .Llabel k2 endL) (hr : r.li_i = .Lret) (htop : top ≠ endL)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : (Int.ofNat (Params.ofBody body).frame) ≠ 0)
    (hF : dispOk32 (Int.ofNat (Params.ofBody body).frame) = true)
    (hF' : dispOk32 (-(Int.ofNat (Params.ofBody body).frame)) = true)
    (hbr : branchOK (fundefItemsL body (nodeShapes (Params.ofBody body) P1 L P2 ctr top endL))
      0 (fundefItemsL body (nodeShapes (Params.ofBody body) P1 L P2 ctr top endL)) = true) :
    decodeLprog (encodeLfundefBytes body)
      = some (nodeLayout
          (leaFrame (-(Int.ofNat (Params.ofBody body).frame)) :: opsD (Params.ofBody body) P1)
          ⟨top, ctr, opsD (Params.ofBody body) L⟩
          (opsD (Params.ofBody body) P2 ++ [leaFrame (Int.ofNat (Params.ofBody body).frame)])) :=
  decodeLprog_node body _ P1 L P2 _ _ _ g1 g2 g3 b1 b2 b3 r top endL ctr k1 k2 hbody rfl
    (forall₂_of_straightOK h1) (forall₂_of_straightOK hL) (forall₂_of_straightOK h2)
    (shapeOf_ok _ _ _ hg1) (labelOf_of_shapeOf_op hg1)
    (shapeOf_ok _ _ _ hg2) (labelOf_of_shapeOf_jcc hg2) hg3
    (shapeOf_ok _ _ _ hb1) (labelOf_of_shapeOf_op hb1)
    (shapeOf_ok _ _ _ hb2) (labelOf_of_shapeOf_jcc hb2) hb3 hr htop hsaves hF0 hF hF' hbr

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
