/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
public import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData

@[expose] public section

set_option autoImplicit false

/-!
# The link check of the x86 back end on encodable bodies

## Diagnosis

The region back end of dev (`Haxc/RegionBackend.lean`) links a callee `c : CalleeData`
through `calleeBytes`, which appends the code of `c` to the bytes of the relocating encoder
when the check `calleeLinkB c b` accepts the printed body `b`. Its symbol map `calleeSym c b`
is `VIR.LprogIsa.x86LinkSym c.name b`, so `calleeLinkB c b` is
`VIR.LprogIsa.x86LinkB c.name c.bytes b`, the link check of the callee `(c.name, c.bytes)` of
`VIR.LprogIsa.x86Backend`. The callees are the data `LinkedFn.calleeData` of the linked
functions of a module (`compileARegion`): the stubs `CompiledCallee.stub` of the callees the
driver `compileModule` compiles alone, whose code is a result of `compileRegion`; the
region-compiled kernels `stepKernel` (`Haxc/StepKernel.lean`) and `kfaKernel`
(`ZK/Plonky3Orch/KFrontArrRegion.lean`, code a parameter); and the vector kernels of
`LinkedFn.ofVecOut`, such as `x8Out` (`Poseidon2/ZmmKernelLinked.lean`).

| conjunct of `x86LinkB` / `calleeLinkB` | kind |
|---|---|
| `!code.isEmpty` | fact of the code of the callee; refuses an empty code by construction (`x86LinkB_nil`); the bytes `encodeLfundefBytes` gives a compiled callee end in `ret`, so they are nonempty |
| `shapesOf (Params.ofBody b) b` is `some` | fact of the body: for an encodable body it holds exactly when the body has no `Lgoto` and the bytes of each `Lopn` have a template cover (`shapesOf_isSome_of_encodable`, `noGoto_cover_of_shapesOf`); an `Lgoto` is encodable and refused by construction (`x86LinkB_of_goto`); a template cover is a fact of the encoder form of the instruction, which `encodableLcmd` (nonempty bytes) does not give |
| `branchOKReloc`, a conditional branch or a call to a label | fact of the body: the label is defined in the body and the displacement of the relaxed encoding lands on it |
| `branchOKReloc`, a call of a symbol | fact of the call site: the symbol is the name of the callee (any other symbol gets displacement `0`, a refusal by construction), the name is nonempty, the body saves no register by `push` (the symbol map subtracts the pushes, the item list has none), and the callee is within `2 ^ 31` bytes (`callDist < callRange`) |
| `expectedReloc` is `some` | fact of the body: every conditional branch and every call to a label has its label defined; a call of a symbol always resolves |

So the field `IsaBackend.Laws.link_of_encodable` fails at `x86Backend` for every callee:
the body `gotoBody 0` of one `jmp` is encodable, within the call range, and refused
(`x86Backend_link_refuses`, `not_x86Backend_link_of_encodable`). No subtype of the callee
type repairs it; the conditions are on the body and its call sites.

## Main results

* `splitPieces_of_cover`, `cover_of_splitPieces`, `shapeOfBytes_isSome_iff`: the splitter
  `DecodeGen.splitPieces` accepts a byte string exactly at a template cover.
* `shapesOf_isSome_of_encodable` (1): an encodable body without `Lgoto` whose `Lopn` bytes
  have template covers has shapes; `noGoto_cover_of_shapesOf` is the converse.
* `x86Backend_link_refuses`, `not_x86Backend_link_of_encodable`: the field
  `link_of_encodable` fails at `x86Backend`.
* `x86LinkB_of_cover`, `x86Backend_link_of_cover` (2): the link check accepts an
  encodable body within the call range at a callee with nonempty code and nonempty name,
  when the body has template covers, no conditional branch, no `Lgoto`, calls only the
  callee, and saves no register by `push`; `x86Backend_link_callBody` meets these hypotheses
  at a body with a call. `LinkShapeComplete.x86LinkB_of_encodable` replaces the template
  covers by the link forms `LinkShapeComplete.linkFormB`.

A body with a conditional branch is outside (2): its branch check needs the displacement
of the relaxed encoding (`LprogBytes.labelOffsets`) to land on the label, a layout fact of
the encoder that no theorem states; the gates of the code base check it (`branchOK` in
`DecodeLayout.decodableLcmd`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (LinstrR Linstr Lcmd LLabel LabelKind LOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (calleeSavedToSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen

/-! ## 1. Completeness of the piece splitter -/

/-- **A template cover of a byte string**: a list of pieces, each a nonempty byte string
    with an instruction, whose concatenation is the string and each of which is one of the
    byte templates `pieceTemplates` of its instruction. -/
def TemplateCover (bs : List (BitVec 8)) : Prop :=
  ∃ pcs : List (List (BitVec 8) × JInstr 64), pcs.flatMap Prod.fst = bs
    ∧ ∀ q ∈ pcs, q.1 ≠ [] ∧ q ∈ pieceTemplates q.2

/-- **The splitter finds a template cover.** At a fuel no smaller than the length of the
    bytes, `splitPieces` returns the pieces of every template cover. -/
theorem splitPieces_of_cover :
    ∀ (pcs : List (List (BitVec 8) × JInstr 64)) (n : Nat),
      (pcs.flatMap Prod.fst).length ≤ n →
      (∀ q ∈ pcs, q.1 ≠ [] ∧ q ∈ pieceTemplates q.2) →
      splitPieces n (pcs.flatMap Prod.fst) = some pcs := by
  intro pcs
  induction pcs with
  | nil => intro n _ _; cases n <;> rfl
  | cons q pcs ih =>
    intro n hn hq
    obtain ⟨qb, qj⟩ := q
    obtain ⟨hne, hmem⟩ := hq (qb, qj) List.mem_cons_self
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hdec := pieceTemplates_sound qj (b :: bs, qj) hmem (pcs.flatMap Prod.fst)
    cases n with
    | zero => simp at hn
    | succ n =>
      set R := pcs.flatMap Prod.fst with hR
      have hk : (b :: (bs ++ R)).length - R.length = bs.length + 1 := by simp; omega
      have hdec2 : decodeLinstr (b :: (bs ++ R)) = some (.op qj, R) := hdec
      have hn2 : R.length ≤ n := by
        simp only [List.flatMap_cons, ← hR, List.length_append, List.length_cons] at hn; omega
      have hrec := ih n hn2 (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
      simp only [List.flatMap_cons, List.cons_append, ← hR, splitPieces, hdec2, hk]
      simp [hmem, hrec]

/-- **The pieces the splitter returns are a template cover**: they concatenate to the bytes,
    and each is a nonempty template of its instruction. -/
theorem cover_of_splitPieces :
    ∀ (n : Nat) (bs : List (BitVec 8)) (pcs : List (List (BitVec 8) × JInstr 64)),
      splitPieces n bs = some pcs →
        pcs.flatMap Prod.fst = bs ∧ ∀ q ∈ pcs, q.1 ≠ [] ∧ q ∈ pieceTemplates q.2 := by
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
            · refine ⟨?_, hc.2⟩
              simp only [ne_eq, List.take_eq_nil_iff, reduceCtorEq, or_false]
              omega
            · exact hok q hq
        · simp at h
      · simp at h

/-- **The shape of the bytes of an instruction exists exactly at a template cover.** -/
theorem shapeOfBytes_isSome_iff (bs : List (BitVec 8)) :
    (shapeOfBytes bs).isSome = true ↔ TemplateCover bs := by
  constructor
  · intro h
    unfold shapeOfBytes at h
    cases hs : splitPieces bs.length bs with
    | none => simp [hs] at h
    | some pcs => exact ⟨pcs, cover_of_splitPieces _ _ _ hs⟩
  · rintro ⟨pcs, rfl, hq⟩
    unfold shapeOfBytes
    rw [splitPieces_of_cover pcs _ le_rfl hq]
    cases pcs with
    | nil => rfl
    | cons q t => cases t <;> rfl

/-! ## 2. The shapes of an encodable body -/

/-- The shapes of a body exist exactly when the shape of each instruction exists. -/
theorem shapesOf_isSome_iff (P : Params) : ∀ b : Lcmd,
    (shapesOf P b).isSome = true ↔ ∀ i ∈ b, (shapeOf P i.li_i).isSome = true
  | [] => by simp [shapesOf]
  | i :: b => by
    rw [List.forall_mem_cons, ← shapesOf_isSome_iff P b]
    simp only [shapesOf]
    cases shapeOf P i.li_i <;> cases shapesOf P b <;> simp

/-- **The shape of an encodable instruction.** An instruction that reaches the byte stream
    (`encodableLinstrR`), is not a `jmp` (`Lgoto`), and, when it is an `Lopn`, has bytes with
    a template cover, has a shape. -/
theorem shapeOf_isSome_of_encodable (P : Params) {frame spillW qsaveB : Nat} (i : LinstrR)
    (henc : encodableLinstrR frame spillW i qsaveB = true) (hgoto : ∀ t, i ≠ .Lgoto t)
    (hcov : ∀ ds o ss, i = .Lopn ds o ss →
      TemplateCover (encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB)) :
    (shapeOf P i).isSome = true := by
  cases i with
  | Lopn ds o ss => exact (shapeOfBytes_isSome_iff _).2 (hcov ds o ss rfl)
  | Lgoto t => exact absurd rfl (hgoto t)
  | Lcond c l => cases c <;> simp_all [shapeOf, encodableLinstrR, carriesNoBytes, encodeLinstrR]
  | _ => simp_all [shapeOf, encodableLinstrR, carriesNoBytes, encodeLinstrR]

/-- **(1) The shapes of an encodable body.** A body accepted by `encodableLcmd`, with no
    `Lgoto` and with a template cover of the bytes of each `Lopn` at the parameters of the
    body, has shapes (`DecodeGen.shapesOf`). -/
theorem shapesOf_isSome_of_encodable (body : Lcmd) (henc : encodableLcmd body = true)
    (hgoto : ∀ i ∈ body, ∀ t, i.li_i ≠ .Lgoto t)
    (hcov : ∀ i ∈ body, ∀ ds o ss, i.li_i = .Lopn ds o ss →
      TemplateCover (encodeLopn (Params.ofBody body).frame (Params.ofBody body).spillW
        (.Lopn ds o ss) (Params.ofBody body).qsaveB)) :
    (shapesOf (Params.ofBody body) body).isSome = true :=
  (shapesOf_isSome_iff _ body).2 fun i hi =>
    shapeOf_isSome_of_encodable _ i.li_i (List.all_eq_true.mp henc i hi) (hgoto i hi)
      (hcov i hi)

/-- **The hypotheses of (1) are necessary.** A body with shapes has no `Lgoto`, and the bytes
    of each of its `Lopn` have a template cover. -/
theorem noGoto_cover_of_shapesOf {body : Lcmd}
    (h : (shapesOf (Params.ofBody body) body).isSome = true) :
    (∀ i ∈ body, ∀ t, i.li_i ≠ .Lgoto t)
      ∧ ∀ i ∈ body, ∀ ds o ss, i.li_i = .Lopn ds o ss →
        TemplateCover (encodeLopn (Params.ofBody body).frame (Params.ofBody body).spillW
          (.Lopn ds o ss) (Params.ofBody body).qsaveB) := by
  have hi := (shapesOf_isSome_iff _ body).1 h
  refine ⟨fun i hm t ht => ?_, fun i hm ds o ss ho => ?_⟩
  · have := hi i hm
    rw [ht] at this
    simp [shapeOf] at this
  · have := hi i hm
    rw [ho] at this
    exact (shapeOfBytes_isSome_iff _).1 this

/-! ## 3. The link check refuses encodable bodies -/

/-- The body of one local `jmp` to the label `l`. -/
def gotoBody (l : LLabel) : Lcmd := [⟨0, .Lgoto ("", l)⟩]

theorem encodable_gotoBody (l : LLabel) : encodableLcmd (gotoBody l) = true := by
  simp [encodableLcmd, gotoBody, encodableLinstrR, carriesNoBytes, encodeLinstrR]
  split <;> simp [encJmp8, encJmp32]

/-- The function bytes of `gotoBody 0` are shorter than `2 ^ 31` at every symbol map. -/
theorem gotoBody_length_lt (sym : String → Option Int) :
    (encodeLfundefBytesReloc sym (gotoBody 0)).length < 2 ^ 31 := by
  rw [encodeLfundefBytesReloc_of_local sym (by simp [gotoBody, remoteSym])]
  decide +kernel

/-- A body with an `Lgoto` has no shapes. -/
theorem shapesOf_eq_none_of_goto (P : Params) {body : Lcmd} {i : Linstr} (hi : i ∈ body)
    {t : String × LLabel} (ht : i.li_i = .Lgoto t) : shapesOf P body = none := by
  cases h : shapesOf P body with
  | none => rfl
  | some ds =>
    have := (shapesOf_isSome_iff P body).1 (by simp [h]) i hi
    rw [ht] at this
    simp [shapeOf] at this

/-- **The x86 link check refuses an empty code**, for every symbol and every body. -/
theorem x86LinkB_nil (name : String) (b : Lcmd) : VIR.LprogIsa.x86LinkB name [] b = false := by
  simp [VIR.LprogIsa.x86LinkB]

/-- **The x86 link check refuses a body with an `Lgoto`**, for every symbol and code. -/
theorem x86LinkB_of_goto (name : String) (code : List (BitVec 8)) {b : Lcmd} {i : Linstr}
    (hi : i ∈ b) {t : String × LLabel} (ht : i.li_i = .Lgoto t) :
    VIR.LprogIsa.x86LinkB name code b = false := by
  simp [VIR.LprogIsa.x86LinkB, shapesOf_eq_none_of_goto _ hi ht]

/-- **Every callee of the x86 back end is refused at an encodable body within the call
    range**: the body `gotoBody 0` is accepted by `encodableLcmd`, its call distance is below
    `x86ExportData.callRange`, and the link check refuses it. A restriction of the type of
    callees therefore does not make `IsaBackend.Laws.link_of_encodable` hold. -/
theorem x86Backend_link_refuses (c : VIR.LprogIsa.x86Backend.Callee) :
    VIR.LprogIsa.x86Backend.encodable (gotoBody 0) = true
      ∧ VIR.LprogIsa.x86Backend.callDist c (gotoBody 0) < VIR.LprogIsa.x86ExportData.callRange
      ∧ VIR.LprogIsa.x86Backend.link c (gotoBody 0) = false :=
  ⟨encodable_gotoBody 0, gotoBody_length_lt _,
    x86LinkB_of_goto (b := gotoBody 0) (i := ⟨0, .Lgoto ("", 0)⟩) (t := ("", 0)) c.1 c.2
      (List.mem_singleton_self _) rfl⟩

/-- **The field `link_of_encodable` fails at the x86 back end**, at its export data: an
    encodable body within the call range is refused by the link check
    (`x86Backend_link_refuses`). -/
theorem not_x86Backend_link_of_encodable :
    ¬ ∀ (c : VIR.LprogIsa.x86Backend.Callee) (body : Lcmd),
      VIR.LprogIsa.x86Backend.encodable body = true →
      VIR.LprogIsa.x86Backend.callDist c body < VIR.LprogIsa.x86ExportData.callRange →
      VIR.LprogIsa.x86Backend.link c body = true := by
  intro h
  obtain ⟨he, hd, hl⟩ := x86Backend_link_refuses ("", [0])
  have := h ("", [0]) (gotoBody 0) he hd
  rw [hl] at this
  cases this

/-! ## 4. The link check on bodies without branches -/

/-- The branch check of two item lists, one after the other, under a target map. -/
theorem branchOKRelocMap_append (all : List Item) (tgt : Item → Option (Nat × Nat)) :
    ∀ (xs ys : List Item) (off : Nat), branchOKRelocMap all tgt off (xs ++ ys)
      = (branchOKRelocMap all tgt off xs
          && branchOKRelocMap all tgt (off + (itemBytes xs).length) ys) := by
  intro xs
  induction xs with
  | nil => intro ys off; simp [branchOKRelocMap, itemBytes]
  | cons it xs ih =>
    intro ys off
    simp only [List.cons_append, branchOKRelocMap, ih, itemBytes, List.flatMap_cons,
      List.length_append, Bool.and_assoc, Nat.add_assoc]

/-- An item list without conditional branch and without call passes the branch check and
    denotes a program, at every offset and every callee block. -/
theorem plain_link (all : List Item) (k L : Nat) :
    ∀ (xs : List Item) (off : Nat),
      (∀ it ∈ xs, (∀ cc d, it.dec ≠ some (.jcc cc d))
        ∧ ∀ d, it.dec ≠ some (.call d)) →
      branchOKReloc all k L off xs = true ∧ (expectedReloc all k L xs).isSome = true
  | [], _, _ => by simp [branchOKRelocMap, expectedRelocMap]
  | it :: xs, off, h => by
    obtain ⟨hb, he⟩ := plain_link all k L xs (off + it.bytes.length)
      (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨hj, hc⟩ := h it List.mem_cons_self
    rcases hd : it.dec with _ | x
    · simp_all [branchOKRelocMap, expectedRelocMap]
    · cases x with
      | jcc cc d => exact absurd hd (hj cc d)
      | call d => exact absurd hd (hc d)
      | _ => simp_all [branchOKRelocMap, expectedRelocMap]

/-- The items of an instruction that is neither a conditional branch nor a call decode to
    nothing or to a straight-line instruction. -/
theorem plain_dItems (P : Params) (off : Nat) (instr : Linstr) (sh : DShape)
    (hsh : shapeOf P instr.li_i = some sh) (hc : ∀ c l, instr.li_i ≠ .Lcond c l)
    (hl : ∀ ra t, instr.li_i ≠ .Lcall ra t) :
    ∀ it ∈ dItems P off instr sh, it.dec = none ∨ ∃ j, it.dec = some (.op j) := by
  intro it hit
  generalize hi : instr.li_i = i at hsh hc hl
  cases i with
  | Lopn ds o ss =>
    rcases shapeOfBytes_ok hsh with ⟨q, rfl, -, -⟩ | ⟨pcs, rfl, -, -⟩
    · simp only [dItems, List.mem_singleton] at hit
      subst hit
      exact Or.inr ⟨q.2, rfl⟩
    · simp only [dItems, List.mem_map] at hit
      obtain ⟨p, -, rfl⟩ := hit
      exact Or.inr ⟨p.2, rfl⟩
  | Lcond c l => exact absurd rfl (hc c l)
  | Lcall ra t => exact absurd rfl (hl ra t)
  | Llabel _ _ | Lret | Lalign =>
    simp only [shapeOf, Option.some.injEq] at hsh
    subst hsh
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    exact Or.inl rfl
  | _ => simp [shapeOf] at hsh

/-- The byte length the encoder assigns an instruction other than a branch or a call is the
    length of its bytes. -/
theorem lenAt_eq_length_encAt (P : Params) (off : Nat) (i : LinstrR)
    (hc : ∀ c l, i ≠ .Lcond c l) (hg : ∀ t, i ≠ .Lgoto t)
    (hl : ∀ ra t, i ≠ .Lcall ra t) :
    P.lenAt off i = (P.encAt off i).length := by
  cases i <;> simp_all [Params.lenAt, Params.encAt, instrLenAt, encodeLinstrR]

/-- The byte length of the items of a body under the relocating encoder does not depend on
    the symbol map. -/
theorem length_itemBytes_itemsFromReloc (s₁ s₂ : String → Option Int) (P : Params) :
    ∀ (body : Lcmd) (ds : List DShape) (off : Nat),
      (itemBytes (itemsFromReloc s₁ P off body ds)).length
        = (itemBytes (itemsFromReloc s₂ P off body ds)).length := by
  intro body
  induction body with
  | nil => intro ds off; rfl
  | cons i b ih =>
    intro ds off
    cases ds with
    | nil => rfl
    | cons sh ds =>
      simp only [itemsFromReloc]
      cases remoteSym i.li_i with
      | some f =>
        have h := ih ds (off + 5)
        simp only [itemBytes] at h ⊢
        simp only [List.flatMap_cons, List.length_append, h, encCall32_length]
      | none =>
        simp only [itemBytes, List.flatMap_append, List.length_append] at ih ⊢
        rw [ih]

/-- **The items of a body without branches pass the link check.** Under a symbol map that
    places the symbol `name` at `L - pre`, with `L < 2 ^ 31`, the items of a body laid out
    from body offset `off` at byte offset `pre + off` pass the branch check in front of a
    callee block at `L` and denote a program, when every instruction has a shape, none is a
    conditional branch, every call calls `name`, `name` is nonempty, and the items end by
    `L`. -/
theorem itemsFromReloc_link (all : List Item) (k L pre : Nat) (sym : String → Option Int)
    (P : Params) (name : String) (hsym : sym name = some ((L : Int) - (pre : Int)))
    (hL : L < 2 ^ 31) (hname : name ≠ "") :
    ∀ (body : Lcmd) (ds : List DShape) (off : Nat),
      List.Forall₂ (fun i sh => shapeOf P i.li_i = some sh) body ds →
      (∀ i ∈ body, ∀ c l, i.li_i ≠ .Lcond c l) →
      (∀ i ∈ body, ∀ ra t, i.li_i = .Lcall ra t → t.1 = name) →
      pre + off + (itemBytes (itemsFromReloc sym P off body ds)).length ≤ L →
      branchOKReloc all k L (pre + off) (itemsFromReloc sym P off body ds) = true
        ∧ (expectedReloc all k L (itemsFromReloc sym P off body ds)).isSome = true := by
  intro body
  induction body with
  | nil =>
    intro ds off hF _ _ _
    cases hF
    simp [itemsFromReloc, branchOKRelocMap, expectedRelocMap]
  | cons i b ih =>
    intro ds off hF hc hcall hlen
    cases hF with
    | cons hsh hF =>
    rename_i sh ds
    have hc' : ∀ i ∈ b, ∀ c l, i.li_i ≠ .Lcond c l :=
      fun j hj => hc j (List.mem_cons_of_mem _ hj)
    have hcall' : ∀ j ∈ b, ∀ ra t, j.li_i = .Lcall ra t → t.1 = name :=
      fun j hj => hcall j (List.mem_cons_of_mem _ hj)
    cases hr : remoteSym i.li_i with
    | some f =>
      have hf : f = name := by
        revert hr hsh
        cases hi : i.li_i with
        | Lcall ra t =>
          intro _ hr
          have := hcall i List.mem_cons_self ra t hi
          obtain ⟨g, l⟩ := t
          simp only [remoteSym] at hr
          split at hr
          · cases hr
          · exact (Option.some.inj hr).symm.trans this
        | Lgoto t => intro hsh; simp [shapeOf] at hsh
        | _ => intro _ hr; simp [remoteSym] at hr
      subst hf
      simp only [itemsFromReloc, hr, itemBytes, List.flatMap_cons, List.length_append,
        encCall32_length] at hlen ⊢
      have hrest := ih ds (off + 5) hF hc' hcall' (by simp only [itemBytes]; omega)
      have hland := relocDisp_lands sym f L pre off hsym hL (by omega)
      refine ⟨?_, ?_⟩
      · simp only [branchOKRelocMap, callTgtMap, encCall32_length, Option.isNone_none,
          Bool.true_or, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨by push_cast at hland ⊢; omega, ?_⟩
        rw [show pre + off + 5 = pre + (off + 5) by omega]
        exact hrest.1
      · simp only [expectedRelocMap, callTgtMap, Option.isSome_map]
        exact hrest.2
    | none =>
      have hnc : ∀ ra t, i.li_i ≠ .Lcall ra t := by
        intro ra t ht
        have := hcall i List.mem_cons_self ra t ht
        obtain ⟨g, l⟩ := t
        simp only at this
        subst this
        simp [ht, remoteSym, hname] at hr
      have hng : ∀ t, i.li_i ≠ .Lgoto t := by
        intro t ht
        rw [ht] at hsh
        simp [shapeOf] at hsh
      have hpl := plain_dItems P off i sh hsh (hc i List.mem_cons_self) hnc
      have hlenI : (itemBytes (dItems P off i sh)).length = P.lenAt off i.li_i := by
        rw [itemBytes_dItems P off i sh (shapeOf_ok P _ _ hsh),
          lenAt_eq_length_encAt P off i.li_i (hc i List.mem_cons_self) hng hnc]
      simp only [itemsFromReloc, hr] at hlen ⊢
      have hlen2 : pre + (off + P.lenAt off i.li_i)
          + (itemBytes (itemsFromReloc sym P (off + P.lenAt off i.li_i) b ds)).length ≤ L := by
        simp only [itemBytes, List.flatMap_append, List.length_append] at hlen hlenI ⊢
        omega
      have hrest := ih ds _ hF hc' hcall' hlen2
      have hp := plain_link all k L (dItems P off i sh) (pre + off) fun it h => by
        rcases hpl it h with h | ⟨j, h⟩ <;> simp [h]
      refine ⟨?_, ?_⟩
      · have e := branchOKRelocMap_append all (fun _ => some (k, L)) (dItems P off i sh)
          (itemsFromReloc sym P (off + P.lenAt off i.li_i) b ds) (pre + off)
        rw [hlenI, Nat.add_assoc] at e
        show branchOKRelocMap all (fun _ => some (k, L)) (pre + off) _ = true
        rw [e, Bool.and_eq_true]
        exact ⟨hp.1, hrest.1⟩
      rw [expectedReloc_append]
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hp.2
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hrest.2
      simp [ha, hc]

/-- **The conditions on a body of a caller of `name`** under which the link check accepts
    it: no `Lgoto`, a template cover of the bytes of each `Lopn`, no conditional branch,
    every call a call of `name`, and no register saved by `push`. -/
structure LinkBody (name : String) (body : Lcmd) : Prop where
  /-- No instruction is an `Lgoto`. -/
  noGoto : ∀ i ∈ body, ∀ t, i.li_i ≠ .Lgoto t
  /-- The bytes of each `Lopn` have a template cover. -/
  cover : ∀ i ∈ body, ∀ ds o ss, i.li_i = .Lopn ds o ss →
    TemplateCover (encodeLopn (Params.ofBody body).frame (Params.ofBody body).spillW
      (.Lopn ds o ss) (Params.ofBody body).qsaveB)
  /-- No instruction is a conditional branch. -/
  noCond : ∀ i ∈ body, ∀ c l, i.li_i ≠ .Lcond c l
  /-- Every call calls `name`. -/
  callName : ∀ i ∈ body, ∀ ra t, i.li_i = .Lcall ra t → t.1 = name
  /-- No register is saved by `push`. -/
  noSaves : calleeSavedToSave body = []

/-- **(2) The x86 link check on an encodable body.** The check `x86LinkB name code body`
    accepts a body accepted by `encodableLcmd` that satisfies `LinkBody name body`, at a
    nonempty code and a nonempty symbol, when the function bytes of the relocating encoder
    are shorter than `2 ^ 31`. -/
theorem x86LinkB_of_cover (name : String) (code : List (BitVec 8)) (body : Lcmd)
    (hcode : code ≠ []) (hname : name ≠ "") (henc : encodableLcmd body = true)
    (hb : LinkBody name body)
    (hdist : (encodeLfundefBytesReloc (VIR.LprogIsa.x86LinkSym name body) body).length
      < 2 ^ 31) :
    VIR.LprogIsa.x86LinkB name code body = true := by
  obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.mp
    (shapesOf_isSome_of_encodable body henc hb.noGoto hb.cover)
  set P := Params.ofBody body with hP
  set sym := VIR.LprogIsa.x86LinkSym name body with hsymdef
  set L := (encodeLfundefBytesReloc sym body).length with hLdef
  set pre := (encLeaRspFrame (-(Int.ofNat P.frame))).length with hpre
  have hF := shapesOf_forall₂_shapeOf P body ds hds
  have hR := relocDShapeOK_of_shapes P hds
  have hL1 : encodeLfundefBytesReloc sym body = itemBytes (fundefItemsRelocL sym P body ds) :=
    encodeLfundefBytesReloc_eq_itemBytesL sym body ds hb.noSaves hR
  have hL0 : encodeLfundefBytesReloc (fun _ => none) body
      = itemBytes (fundefItemsRelocL (fun _ => none) P body ds) :=
    encodeLfundefBytesReloc_eq_itemBytesL _ body ds hb.noSaves hR
  have hX := length_itemBytes_itemsFromReloc (fun _ => none) sym P body ds 0
  have hLsplit : L = pre + (itemBytes (itemsFromReloc sym P 0 body ds)).length
      + (encLeaRspFrame (Int.ofNat P.frame)).length + LeafBytes.encRet.length := by
    rw [hLdef, hL1]
    simp [fundefItemsRelocL, itemBytes, mkLea, mkRet, hpre]
    omega
  have hL0split : (encodeLfundefBytesReloc (fun _ => none) body).length
      = pre + (itemBytes (itemsFromReloc sym P 0 body ds)).length
        + (encLeaRspFrame (Int.ofNat P.frame)).length + LeafBytes.encRet.length := by
    rw [hL0, ← hX]
    simp [fundefItemsRelocL, itemBytes, mkLea, mkRet, hpre]
    omega
  have hsym : sym name = some ((L : Int) - (pre : Int)) := by
    simp only [hsymdef, VIR.LprogIsa.x86LinkSym, ite_true, prologueLen, hb.noSaves,
      List.flatMap_nil, List.length_nil, Nat.zero_add, hL0split, hLsplit, hpre, hP]
    rfl
  have hit := itemsFromReloc_link (fundefItemsRelocL sym P body ds)
    (decCount (fundefItemsRelocL sym P body ds)) L pre sym P name hsym hdist hname body ds 0
    hF hb.noCond hb.callName (by omega)
  have hcode' : code.isEmpty = false := by cases code <;> simp_all
  simp only [VIR.LprogIsa.x86LinkB, hcode', Bool.not_false, Bool.true_and]
  rw [← hP, ← hsymdef, ← hLdef, hds]
  have hT := plain_link (fundefItemsRelocL sym P body ds)
    (decCount (fundefItemsRelocL sym P body ds)) L
    [mkLea (Int.ofNat P.frame), mkRet] (pre + (itemBytes (itemsFromReloc sym P 0 body ds)).length)
    (by simp [mkLea, mkRet])
  have hH := plain_link (fundefItemsRelocL sym P body ds)
    (decCount (fundefItemsRelocL sym P body ds)) L [mkLea (-(Int.ofNat P.frame))] 0
    (by simp [mkLea])
  have e1 := branchOKRelocMap_append (fundefItemsRelocL sym P body ds)
    (fun _ => some (decCount (fundefItemsRelocL sym P body ds), L))
    [mkLea (-(Int.ofNat P.frame))]
    (itemsFromReloc sym P 0 body ds ++ [mkLea (Int.ofNat P.frame), mkRet]) 0
  have e2 := branchOKRelocMap_append (fundefItemsRelocL sym P body ds)
    (fun _ => some (decCount (fundefItemsRelocL sym P body ds), L))
    (itemsFromReloc sym P 0 body ds) [mkLea (Int.ofNat P.frame), mkRet] (pre + 0)
  have hpre0 : 0 + (itemBytes [mkLea (-(Int.ofNat P.frame))]).length = pre + 0 := by
    simp [itemBytes, mkLea, hpre]
  rw [hpre0, e2] at e1
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · show branchOKRelocMap _ _ 0 ([mkLea (-(Int.ofNat P.frame))]
      ++ (itemsFromReloc sym P 0 body ds ++ [mkLea (Int.ofNat P.frame), mkRet])) = true
    rw [e1]
    simp only [Nat.add_zero] at hit ⊢
    simp only [Bool.and_eq_true]
    exact ⟨hH.1, hit.1, hT.1⟩
  · show (expectedReloc _ _ _ ([mkLea (-(Int.ofNat P.frame))]
      ++ (itemsFromReloc sym P 0 body ds ++ [mkLea (Int.ofNat P.frame), mkRet]))).isSome = true
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hH.2
    obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hit.2
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hT.2
    rw [expectedReloc_append, expectedReloc_append, ha, hb', hc]
    rfl

/-- **(2) The field `link_of_encodable` of the x86 back end, at the callees with nonempty code
    and nonempty symbol and the bodies of `LinkBody`.** At the export data
    `x86ExportData`, a body accepted by the encodability of `x86Backend` whose call distance
    to the callee `c` is below `callRange` passes the link check of `c`. -/
theorem x86Backend_link_of_cover (c : VIR.LprogIsa.x86Backend.Callee) (body : Lcmd)
    (hcode : c.2 ≠ []) (hname : c.1 ≠ "") (hb : LinkBody c.1 body)
    (henc : VIR.LprogIsa.x86Backend.encodable body = true)
    (hd : VIR.LprogIsa.x86Backend.callDist c body < VIR.LprogIsa.x86ExportData.callRange) :
    VIR.LprogIsa.x86Backend.link c body = true :=
  x86LinkB_of_cover c.1 c.2 body hcode hname henc hb hd

/-- The body of one call of the symbol `f` to the label `0` followed by the return. -/
def callBody (f : String) : Lcmd := [⟨0, .Lcall none (f, 0)⟩, ⟨0, .Lret⟩]

/-- **The hypotheses of (2) are met by a calling body**: the link check of the callee `("f",
    [0xc3])` accepts `callBody "f"`. -/
theorem x86Backend_link_callBody :
    VIR.LprogIsa.x86Backend.link ("f", [0xc3]) (callBody "f") = true := by
  refine x86Backend_link_of_cover ("f", [0xc3]) (callBody "f") (by simp) (by decide)
    ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
  · simp [callBody]
  · simp [callBody]
  · simp [callBody]
  · intro i hi ra t ht
    simp only [callBody, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · obtain ⟨-, rfl⟩ := LinstrR.Lcall.inj ht
      rfl
    · cases ht
  · decide +kernel
  · show encodableLcmd (callBody "f") = true
    simp [encodableLcmd, callBody, encodableLinstrR, carriesNoBytes, encodeLinstrR, encCall32]
  · decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkOfEncodable
