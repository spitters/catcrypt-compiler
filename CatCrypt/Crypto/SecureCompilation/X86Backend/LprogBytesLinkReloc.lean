/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig

/-!
# Decoding a function body with cross-function calls, followed by its callee

`LprogBytes.encodeLfundefBytesReloc symBase body` lays down a function whose remote
calls `Lcall _ (f, _)` (`f` nonempty) are the five-byte `call rel32` with displacement
`symBase f - instrEnd`, both counted from the first byte after the frame `leaq`. This
module decodes those bytes followed by the bytes `cb` of a callee block.

## The encoder as an item list

`encodeFromReloc` is the fold of `LprogBytes.encodeLcmdReloc` as a recursion
(`encodeLcmdReloc_eq_encodeFromReloc`). It agrees with `LprogBytesDecode.encodeFrom`
except at a remote call, where the displacement is `relocDisp` and the encoder's offset
advances by five. `itemsFromReloc` is the item list of a body with list-valued shapes
`PhysAbiShape.DShape`: a remote call is an item without target label, every other position
is the run of items `PhysAbiShape.dItems` of its shape. `fundefItemsRelocL` adds the frame
`leaq`, the closing `leaq` and `ret` (`encodeLfundefBytesReloc_eq_itemBytesL`);
`fundefItemsReloc` is `fundefItemsRelocL` at single shapes.

## Resolution

Byte offsets become instruction indices in `LprogBytesDecode.resolveAll`: a call ending
at byte offset `e` with displacement `d` receives the index of the first instruction of
the whole stream that starts at byte `e + d`. A target map `tgt : Item → Option (Nat × Nat)`
sends a call without target label to the index `j` and byte offset `t` of the entry of its
callee block. `branchOKRelocMap all tgt` requires of such a call that `e + d = t`, and of
every other branch what `LprogBytesDecode.branchOK` requires. `expectedRelocMap all tgt` is
the program of an item list in which such a call is `call j`. `branchOKReloc all k L` and
`expectedReloc all k L` are their instances at the constant map `fun _ => some (k, L)`.
With `L` the byte length of the items and `k` their instruction count, the first
instruction of `cb` starts at byte `L` and has index `k` in the decoded stream.

## Main results

* `decodeLprog_items_linkedMap`: the bytes of an item list followed by a stream `cb` of
  callee blocks that decodes to `q` decode to `prog ++ shiftProg prog.length q`, where
  `prog` is `expectedRelocMap` of the items under a target map that sends each call
  without target label to the entry of its block in `cb`.
* `decodeLprog_items_linkedSym`: its instance at the target map `symTgt m`, which sends a
  call to the block entry `m` gives its callee symbol `Item.sym`; the relocating item list
  `itemsFromReloc` records each remote call's symbol there.
* `decodeLprog_items_linked`: its instance at one block, entered at the first instruction
  of `cb`; each call without target label is `call prog.length`.
* `decodeLprog_fundefRelocL_append`: the same for `encodeLfundefBytesReloc symBase body`,
  whose instructions are remote calls or have list-valued shapes;
  `decodeLprog_fundefReloc_append` is its form at single shapes.
* `relocDShapeOK_of_shapes`: the computed shapes `DecodeGen.shapesOf` of a body meet the
  shape condition `RelocDShapeOK` of the relocating encoder.
* `relocDisp_lands`: the displacement of a remote call whose symbol base is the byte
  length of the function, less the frame `leaq`, ends on that byte length.
* `haltsC_fundefReloc_linked`: a run of the decoded caller with the callee block as an
  oracle at the target `prog.length` is a run through calls of the program the linked
  bytes decode to.
* `expectedRelocMap_congr`, `branchOKRelocMap_congr`: the program and the branch condition
  depend on the target map only at the calls without target label;
  `fundefItemsRelocL_sym`: each such call of a relocated function carries the symbol of a
  remote transfer of its body.
* `RegionBlocks cb fs o k q Q`: the callee region `cb` decodes once to `Q`
  (`RegionDecode`), the block of `f ∈ fs` is entered at byte offset `o f` and index `k f`
  and is the call-free block `q f` placed there. `regionBlocks_one` is the region of one
  block; `regionBlocksB` is its Boolean check, sound by `regionBlocks_of_regionBlocksB` at
  the blocks `regionBlock`; `regionDecode_inj` is the injectivity of the entry indices.
* `decodeLinstr_ext`: the prefix property of the one-instruction decoder; an instruction read
  off a stream is read off every extension of it. `decodeAt_append` and
  `decodeLprog_append_streams`: a stream that decodes on its own decodes in front of any
  stream that decodes, with the offsets of the second raised by the length of the first.
* `CalleeBlock`, `regionBlocks_of_decodes`: a list of blocks that each decode is a region at
  the blocks `regionCode`, the offsets `regionOffset` and the indices `regionIndex`, with the
  program `regionProg`.
* `linkedProg_of_itemsMapL`, `linkedProg_of_bytesSymL`: the program of the relocated item
  list of a body with the facts `LinkFacts` satisfies `LinkedProgMap` at `K : String → Nat`:
  the decoded instructions of each instruction of the shape `blkOK` at the index
  `DecodePrintedCFG.posOf`, `call (K f)` at the index of a remote call to `f`, and the
  closing `lea` and `ret`. `LinkedProg` is the instance at one callee block.
* `linked_halt`, `linked_callL`: the byte simulation of the closing return and of a call of
  such a body on a program that satisfies `LinkedProgMap`, under every oracle. The step of the
  address machine at a position of the body and the segments are `LprogBytesLinkW`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
  (DShape DShapeOK dItems dItems_ok itemBytes_dItems)

/-! ## 1. The relocating body encoder as a recursion -/

/-- The displacement `encodeLcmdReloc` writes for a remote transfer to `f` at body offset
    `off`: the symbol base less the end of the five-byte instruction, `0` for a symbol
    without base. -/
def relocDisp (symBase : String → Option Int) (off : Nat) (f : String) : Int :=
  match symBase f with
  | some delta => delta - Int.ofNat (off + 5)
  | none => 0

/-- One step of the fold of `encodeLcmdReloc`. -/
def relocStep (symBase : String → Option Int) (P : Params)
    (acc : Nat × List (BitVec 8) × List (Nat × String)) (instr : Linstr) :
    Nat × List (BitVec 8) × List (Nat × String) :=
  match remoteSym instr.li_i with
  | some f =>
      match symBase f with
      | some delta =>
          (acc.1 + 5,
            acc.2.1 ++ encodeRemoteCF (delta - Int.ofNat (acc.1 + 5)) instr.li_i, acc.2.2)
      | none =>
          (acc.1 + 5, acc.2.1 ++ encodeRemoteCF 0 instr.li_i,
            acc.2.2 ++ [(acc.1 + remoteRel32FieldOff instr.li_i, f)])
  | none =>
      (acc.1 + P.lenAt acc.1 instr.li_i, acc.2.1 ++ P.encAt acc.1 instr.li_i, acc.2.2)

/-- The bytes of `encodeLcmdReloc` as a recursion from a starting offset. -/
def encodeFromReloc (symBase : String → Option Int) (P : Params) : Nat → Lcmd → List (BitVec 8)
  | _, [] => []
  | off, instr :: rest =>
      match remoteSym instr.li_i with
      | some f =>
          encodeRemoteCF (relocDisp symBase off f) instr.li_i
            ++ encodeFromReloc symBase P (off + 5) rest
      | none =>
          P.encAt off instr.li_i ++ encodeFromReloc symBase P (off + P.lenAt off instr.li_i) rest

theorem relocStep_fold_eq (symBase : String → Option Int) (P : Params) :
    ∀ (body : Lcmd) (off : Nat) (acc : List (BitVec 8)) (rl : List (Nat × String)),
      (body.foldl (relocStep symBase P) (off, acc, rl)).2.1
        = acc ++ encodeFromReloc symBase P off body := by
  intro body
  induction body with
  | nil => intro off acc rl; simp [encodeFromReloc]
  | cons instr rest ih =>
    intro off acc rl
    rw [List.foldl_cons]
    cases h : remoteSym instr.li_i with
    | none => simp only [relocStep, h, ih, encodeFromReloc, List.append_assoc]
    | some f =>
      cases hs : symBase f with
      | none => simp only [relocStep, h, hs, ih, encodeFromReloc, relocDisp, List.append_assoc]
      | some delta =>
        simp only [relocStep, h, hs, ih, encodeFromReloc, relocDisp, List.append_assoc]

/-- The bytes of `encodeLcmdReloc` are `encodeFromReloc` at offset `0` under the body's
    own parameters. -/
theorem encodeLcmdReloc_eq_encodeFromReloc (symBase : String → Option Int) (body : Lcmd) :
    (encodeLcmdReloc symBase body).1 = encodeFromReloc symBase (Params.ofBody body) 0 body := by
  have h := relocStep_fold_eq symBase (Params.ofBody body) body 0 [] []
  rw [List.nil_append] at h
  rw [← h]
  rfl

/-- On a body without remote symbol the recursion of the relocating encoder is the
    recursion `LprogBytesDecode.encodeFrom` of `encodeLcmd`, at every symbol map. -/
theorem encodeFromReloc_of_local (symBase : String → Option Int) (P : Params) :
    ∀ (body : Lcmd) (off : Nat), (∀ i ∈ body, remoteSym i.li_i = none) →
      encodeFromReloc symBase P off body = encodeFrom P off body := by
  intro body
  induction body with
  | nil => intro off _; rfl
  | cons instr rest ih =>
    intro off h
    simp only [encodeFromReloc, encodeFrom, h instr List.mem_cons_self,
      ih _ fun i hi => h i (List.mem_cons_of_mem _ hi)]

/-- **On a body without remote symbol the relocating encoder is `encodeLfundefBytes`**, at
    every symbol map. -/
theorem encodeLfundefBytesReloc_of_local (symBase : String → Option Int) {body : Lcmd}
    (h : ∀ i ∈ body, remoteSym i.li_i = none) :
    encodeLfundefBytesReloc symBase body = encodeLfundefBytes body := by
  unfold encodeLfundefBytesReloc encodeLfundefBytes
  rw [encodeLcmdReloc_eq_encodeFromReloc, encodeFromReloc_of_local symBase _ body 0 h,
    ← encodeLcmd_eq_encodeFrom]

/-- **A result of the gated encoder `encodeLfundefBytesChecked` on a body without remote
    symbol is the bytes of the relocating encoder**, at every symbol map. -/
theorem encodeLfundefBytesChecked_eq_reloc (symBase : String → Option Int) {body : Lcmd}
    {bs : List (BitVec 8)} (h : ∀ i ∈ body, remoteSym i.li_i = none)
    (hc : encodeLfundefBytesChecked body = some bs) :
    bs = encodeLfundefBytesReloc symBase body := by
  rw [encodeLfundefBytesReloc_of_local symBase h]
  exact encodeLfundefBytesChecked_eq hc

/-! ## 2. The item list of a body with remote calls -/

/-- What the relocating encoder needs of one body instruction: a remote transfer is a
    call, and every other instruction has the list-valued shape `sh` (`DShapeOK`). -/
def RelocDShapeOK (P : Params) (i : LinstrR) (sh : DShape) : Prop :=
  match remoteSym i with
  | some f => ∃ ra l, i = .Lcall ra (f, l)
  | none => DShapeOK P i sh

/-- `RelocDShapeOK` at a single shape: a remote transfer is a call, and every other
    instruction has the shape `sh`. -/
def RelocShapeOK (P : Params) (i : LinstrR) (sh : Shape) : Prop :=
  match remoteSym i with
  | some f => ∃ ra l, i = .Lcall ra (f, l)
  | none => ShapeOK P i sh

theorem relocShapeOK_iff (P : Params) (i : LinstrR) (sh : Shape) :
    RelocShapeOK P i sh ↔ RelocDShapeOK P i (.one sh) := by
  unfold RelocShapeOK RelocDShapeOK
  cases remoteSym i <;> exact Iff.rfl

theorem relocDShapeOK_forall₂_one (P : Params) {body : Lcmd} {ss : List Shape}
    (h : List.Forall₂ (fun instr sh => RelocShapeOK P instr.li_i sh) body ss) :
    List.Forall₂ (fun instr sh => RelocDShapeOK P instr.li_i sh) body (ss.map DShape.one) :=
  List.forall₂_map_right_iff.mpr (h.imp fun _ _ hs => (relocShapeOK_iff P _ _).mp hs)

/-- The item list of a body under the relocating encoder, laid out from body offset
    `off`: a remote call is one item without target label whose callee symbol `sym` is
    the call's symbol, every other instruction the
    items `dItems` of its list-valued shape. -/
def itemsFromReloc (symBase : String → Option Int) (P : Params) :
    Nat → Lcmd → List DShape → List Item
  | off, instr :: body, sh :: shs =>
      match remoteSym instr.li_i with
      | some f =>
          { bytes := encCall32 (relocDisp symBase off f),
            dec := some (.call (wrap32 (relocDisp symBase off f))),
            label := none, target := none, sym := some f }
            :: itemsFromReloc symBase P (off + 5) body shs
      | none =>
          dItems P off instr sh
            ++ itemsFromReloc symBase P (off + P.lenAt off instr.li_i) body shs
  | _, _, _ => []

theorem itemBytes_itemsFromReloc (symBase : String → Option Int) (P : Params) {body : Lcmd}
    {shs : List DShape}
    (h : List.Forall₂ (fun instr sh => RelocDShapeOK P instr.li_i sh) body shs) :
    ∀ off, itemBytes (itemsFromReloc symBase P off body shs)
      = encodeFromReloc symBase P off body := by
  induction h with
  | nil => intro off; rfl
  | @cons instr sh _ _ hab _ ih =>
    intro off
    unfold RelocDShapeOK at hab
    cases hr : remoteSym instr.li_i with
    | none =>
      rw [hr] at hab
      simp only [itemsFromReloc, encodeFromReloc, hr, itemBytes, List.flatMap_append]
      rw [← itemBytes, ← itemBytes, itemBytes_dItems _ _ _ _ hab, ih]
    | some f =>
      rw [hr] at hab
      obtain ⟨ra, l, hi⟩ := hab
      simp only [itemsFromReloc, encodeFromReloc, hr, itemBytes, List.flatMap_cons]
      rw [hi]
      exact congrArg _ (ih _)

theorem itemsFromReloc_ok (symBase : String → Option Int) (P : Params) {body : Lcmd}
    {shs : List DShape}
    (h : List.Forall₂ (fun instr sh => RelocDShapeOK P instr.li_i sh) body shs) :
    ∀ off, ∀ it ∈ itemsFromReloc symBase P off body shs, ItemOK it := by
  induction h with
  | nil => intro off it hit; cases hit
  | @cons instr sh _ _ hab _ ih =>
    intro off it hit
    unfold RelocDShapeOK at hab
    cases hr : remoteSym instr.li_i with
    | none =>
      rw [hr] at hab
      simp only [itemsFromReloc, hr, List.mem_append] at hit
      rcases hit with hit | hit
      · exact dItems_ok _ _ _ _ hab it hit
      · exact ih _ it hit
    | some f =>
      simp only [itemsFromReloc, hr, List.mem_cons] at hit
      rcases hit with rfl | hit
      · exact ItemOK_of_decode fun rest => decodeLinstr_call32_wrap _ rest
      · exact ih _ it hit

/-- The item list of a function that saves no register by `push`, under the relocating
    encoder, with list-valued shapes: the frame `leaq`, the body, the closing `leaq`,
    `ret`. -/
def fundefItemsRelocL (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List DShape) : List Item :=
  mkLea (-(Int.ofNat P.frame))
    :: (itemsFromReloc symBase P 0 body shs ++ [mkLea (Int.ofNat P.frame), mkRet])

/-- `fundefItemsRelocL` at the single shapes `shs`. -/
def fundefItemsReloc (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List Shape) : List Item :=
  mkLea (-(Int.ofNat P.frame))
    :: (itemsFromReloc symBase P 0 body (shs.map DShape.one)
      ++ [mkLea (Int.ofNat P.frame), mkRet])

theorem fundefItemsReloc_eq (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List Shape) :
    fundefItemsReloc symBase P body shs = fundefItemsRelocL symBase P body (shs.map DShape.one) :=
  rfl

/-- The function bytes of the relocating encoder are the bytes of `fundefItemsRelocL`. -/
theorem encodeLfundefBytesReloc_eq_itemBytesL (symBase : String → Option Int) (body : Lcmd)
    (shs : List DShape) (hsaves : calleeSavedToSave body = [])
    (hsh : List.Forall₂
      (fun instr sh => RelocDShapeOK (Params.ofBody body) instr.li_i sh) body shs) :
    encodeLfundefBytesReloc symBase body
      = itemBytes (fundefItemsRelocL symBase (Params.ofBody body) body shs) := by
  have hb := itemBytes_itemsFromReloc symBase (Params.ofBody body) hsh 0
  have hfr : (Params.ofBody body).frame = frameSize body := rfl
  simp only [itemBytes] at hb
  simp [encodeLfundefBytesReloc, fundefItemsRelocL, hsaves, itemBytes, mkLea, mkRet,
    encodeLcmdReloc_eq_encodeFromReloc, hb, hfr]

/-- The function bytes of the relocating encoder are the bytes of `fundefItemsReloc`. -/
theorem encodeLfundefBytesReloc_eq_itemBytes (symBase : String → Option Int) (body : Lcmd)
    (shs : List Shape) (hsaves : calleeSavedToSave body = [])
    (hsh : List.Forall₂
      (fun instr sh => RelocShapeOK (Params.ofBody body) instr.li_i sh) body shs) :
    encodeLfundefBytesReloc symBase body
      = itemBytes (fundefItemsReloc symBase (Params.ofBody body) body shs) :=
  encodeLfundefBytesReloc_eq_itemBytesL symBase body _ hsaves
    (relocDShapeOK_forall₂_one _ hsh)

theorem fundefItemsRelocL_ok (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List DShape) (hF0 : P.frame ≠ 0) (hF : P.frame < 2 ^ 31)
    (hsh : List.Forall₂ (fun instr sh => RelocDShapeOK P instr.li_i sh) body shs) :
    ∀ it ∈ fundefItemsRelocL symBase P body shs, ItemOK it := by
  intro it hit
  simp only [fundefItemsRelocL, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hit
  rcases hit with rfl | hit | rfl | rfl
  · exact mkLea_ok _ (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [dispOk32, Int.ofNat_eq_natCast, decide_eq_true_eq]; omega)
  · exact itemsFromReloc_ok symBase P hsh 0 it hit
  · exact mkLea_ok _ (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [dispOk32, Int.ofNat_eq_natCast, decide_eq_true_eq]; omega)
  · exact mkRet_ok

theorem fundefItemsReloc_ok (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List Shape) (hF0 : P.frame ≠ 0) (hF : P.frame < 2 ^ 31)
    (hsh : List.Forall₂ (fun instr sh => RelocShapeOK P instr.li_i sh) body shs) :
    ∀ it ∈ fundefItemsReloc symBase P body shs, ItemOK it :=
  fundefItemsRelocL_ok symBase P body _ hF0 hF (relocDShapeOK_forall₂_one P hsh)

/-- **The displacement of a remote call lands on the symbol.** For a symbol whose base is
    `L - pre` (`pre` the bytes in front of the body) and a call at body offset `off`, the
    byte offset `pre + off + 5` of the end of the call plus the decoded displacement is
    `L`, when `L` fits a signed 32-bit displacement. -/
theorem relocDisp_lands (symBase : String → Option Int) (f : String) (L pre off : Nat)
    (hsym : symBase f = some (Int.ofNat L - Int.ofNat pre)) (hL : L < 2 ^ 31)
    (hend : pre + off + 5 ≤ L) :
    ((pre + off + 5 : Nat) : Int) + wrap32 (relocDisp symBase off f) = (L : Int) := by
  have hd : relocDisp symBase off f = (L : Int) - (pre : Int) - ((off + 5 : Nat) : Int) := by
    simp only [relocDisp, hsym, Int.ofNat_eq_natCast]
  rw [hd, wrap32_of_dispOk32 _ (by
    simp only [dispOk32, decide_eq_true_eq]; omega)]
  omega

/-! ## 3. Resolution of an item list in front of callee blocks

A call without target label is resolved by a target map `tgt : Item → Option (Nat × Nat)`,
which sends the call item to the instruction index and the byte offset of the first
instruction of its callee block. The one-callee forms `callTgt`, `expectedReloc` and
`branchOKReloc` are the instances at the constant map `fun _ => some (k, L)`. -/

/-- The target of a call item under the target map `tgt`: `tgt it` for a call without
    target label, the position of the label's definition in `all` otherwise. -/
def callTgtMap (all : List Item) (tgt : Item → Option (Nat × Nat)) (it : Item) :
    Option (Nat × Nat) :=
  match it.target with
  | none => tgt it
  | some l => labelPos l 0 0 all

/-- The target of a call item: the pair `(k, L)` for a call without target label, the
    position of the label's definition in `all` otherwise. -/
abbrev callTgt (all : List Item) (k L : Nat) (it : Item) : Option (Nat × Nat) :=
  callTgtMap all (fun _ => some (k, L)) it

/-- The program an item list denotes in front of callee blocks under the target map
    `tgt`: a call without target label is `call j` for the index `j` that `tgt` gives it;
    every other branch carries the index of the instruction following its target label's
    definition. -/
def expectedRelocMap (all : List Item) (tgt : Item → Option (Nat × Nat)) :
    List Item → Option (List RInstr)
  | [] => some []
  | it :: rest =>
      match it.dec with
      | none => expectedRelocMap all tgt rest
      | some (.op i) => (expectedRelocMap all tgt rest).map (.op i :: ·)
      | some .ret => (expectedRelocMap all tgt rest).map (.ret :: ·)
      | some (.push r) => (expectedRelocMap all tgt rest).map (.push r :: ·)
      | some (.pop r) => (expectedRelocMap all tgt rest).map (.pop r :: ·)
      | some (.jcc cc _) =>
          match it.target.bind (fun l => labelPos l 0 0 all) with
          | some (j, _) => (expectedRelocMap all tgt rest).map (.jcc cc j :: ·)
          | none => none
      | some (.call _) =>
          match callTgtMap all tgt it with
          | some (j, _) => (expectedRelocMap all tgt rest).map (.call j :: ·)
          | none => none

/-- The program an item list denotes in front of a block whose first instruction has
    index `k`: a call without target label is `call k`; every other branch carries the
    index of the instruction following its target label's definition. -/
abbrev expectedReloc (all : List Item) (k L : Nat) : List Item → Option (List RInstr) :=
  expectedRelocMap all (fun _ => some (k, L))

/-- Well-formedness of the branches of `items`, laid out from offset `off` inside `all`,
    under the target map `tgt`: a call without target label ends, with its displacement
    added, on the byte offset that `tgt` gives it; every other branch satisfies the
    condition of `LprogBytesDecode.branchOK`. -/
def branchOKRelocMap (all : List Item) (tgt : Item → Option (Nat × Nat)) :
    Nat → List Item → Bool
  | _, [] => true
  | off, it :: rest =>
      (match it.dec with
        | some (.jcc _ d) =>
            match it.target.bind (fun l => labelPos l 0 0 all) with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && decide (j < decCount all)
            | none => false
        | some (.call d) =>
            match callTgtMap all tgt it with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && (it.target.isNone || decide (j < decCount all))
            | none => false
        | _ => true)
      && branchOKRelocMap all tgt (off + it.bytes.length) rest

/-- Well-formedness of the branches of `items`, laid out from offset `off` inside `all`,
    in front of a block at byte offset `L`: a call without target label ends, with its
    displacement added, on `L`; every other branch satisfies the condition of
    `LprogBytesDecode.branchOK`. -/
abbrev branchOKReloc (all : List Item) (k L : Nat) : Nat → List Item → Bool :=
  branchOKRelocMap all (fun _ => some (k, L))

/-- The definition of a label of `all` is found, in the layout of `all` followed by any
    layout, at the index of the instruction that follows it. -/
theorem findIdx?_label_append (all : List Item) (hok : ∀ it ∈ all, ItemOK it)
    (ys : List (Nat × Nat × DInstr)) (l : LLabel) (j t : Nat)
    (hl : labelPos l 0 0 all = some (j, t)) (hj : j < decCount all) (q : Int)
    (hq : (t : Int) = q) :
    (layoutAt 0 all ++ ys).findIdx? (fun z => decide ((z.1 : Int) = q)) = some j := by
  obtain ⟨y, hy⟩ : ∃ y, (layoutAt 0 all)[j]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by rw [layoutAt_length]; exact hj)⟩
  have hy1 : y.1 = t := (layoutAt_labelPos l all hok 0 0 j t hl).2 y (by simpa using hy)
  have hfind := findIdx?_of_pairwise _ (layoutAt_pairwise all hok 0) j y hy
  rw [hy1, hq] at hfind
  simp [List.findIdx?_append, hfind]

/-- Resolving the layout of `items` inside the layout of `all` followed by a layout `ys`,
    in which the byte offset `t` that `tgt` gives a call without target label has the index
    `j` it gives, yields the program `items` denotes under `tgt`. -/
theorem resolveAll_layout_relocMap (all : List Item) (hok : ∀ it ∈ all, ItemOK it)
    (ys : List (Nat × Nat × DInstr)) (tgt : Item → Option (Nat × Nat))
    (hcross : ∀ it j t, it.target = none → tgt it = some (j, t) → ∀ q : Int, q = (t : Int) →
      (layoutAt 0 all ++ ys).findIdx? (fun z => decide ((z.1 : Int) = q)) = some j) :
    ∀ items off, branchOKRelocMap all tgt off items = true →
      resolveAll (layoutAt 0 all ++ ys) (layoutAt off items)
        = expectedRelocMap all tgt items := by
  intro items
  induction items with
  | nil => intro off _; rfl
  | cons it rest ih =>
    intro off hbr
    simp only [branchOKRelocMap, Bool.and_eq_true] at hbr
    obtain ⟨hhead, htail⟩ := hbr
    have ih' := ih _ htail
    cases hdec : it.dec with
    | none => simpa [layoutAt, expectedRelocMap, hdec] using ih'
    | some x =>
      cases x with
      | op i => simp [layoutAt, expectedRelocMap, hdec, resolveAll, ih']
      | ret => simp [layoutAt, expectedRelocMap, hdec, resolveAll, ih']
      | push r => simp [layoutAt, expectedRelocMap, hdec, resolveAll, ih']
      | pop r => simp [layoutAt, expectedRelocMap, hdec, resolveAll, ih']
      | jcc cc d =>
        rw [hdec] at hhead
        simp only at hhead
        cases htgt : it.target.bind (fun l => labelPos l 0 0 all) with
        | none => rw [htgt] at hhead; simp at hhead
        | some p =>
          obtain ⟨j, t⟩ := p
          rw [htgt] at hhead
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
          obtain ⟨ht, hj⟩ := hhead
          obtain ⟨l, _, hl⟩ :
              ∃ l, it.target = some l ∧ labelPos l 0 0 all = some (j, t) := by
            cases htg : it.target with
            | none => rw [htg] at htgt; simp at htgt
            | some l => exact ⟨l, rfl, by simpa [htg] using htgt⟩
          have hfind := findIdx?_label_append all hok ys l j t hl hj _ ht
          simp only [layoutAt, expectedRelocMap, hdec, resolveAll, htgt, hfind, ih']
      | call d =>
        rw [hdec] at hhead
        simp only at hhead
        cases htgt : callTgtMap all tgt it with
        | none => rw [htgt] at hhead; simp at hhead
        | some p =>
          obtain ⟨j, t⟩ := p
          rw [htgt] at hhead
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hhead
          obtain ⟨ht, hj⟩ := hhead
          have hfind : (layoutAt 0 all ++ ys).findIdx?
              (fun z => decide ((z.1 : Int)
                = ((off + it.bytes.length : Nat) : Int) + d)) = some j := by
            cases htg : it.target with
            | none =>
              simp only [callTgtMap, htg] at htgt
              exact hcross it j t htg htgt _ ht.symm
            | some l =>
              simp only [callTgtMap, htg] at htgt
              simp only [htg, Option.isNone_some, Bool.false_eq_true, false_or] at hj
              exact findIdx?_label_append all hok ys l j t htgt hj _ ht
          simp only [layoutAt, expectedRelocMap, hdec, resolveAll, htgt, hfind, ih']

/-- Resolving the layout of `items` inside the layout of `all` followed by a layout `ys`
    in which byte offset `L` has index `k` yields the program `items` denotes. -/
theorem resolveAll_layout_reloc (all : List Item) (hok : ∀ it ∈ all, ItemOK it)
    (ys : List (Nat × Nat × DInstr)) (k L : Nat)
    (hcross : ∀ q : Int, q = (L : Int) →
      (layoutAt 0 all ++ ys).findIdx? (fun z => decide ((z.1 : Int) = q)) = some k) :
    ∀ items off, branchOKReloc all k L off items = true →
      resolveAll (layoutAt 0 all ++ ys) (layoutAt off items) = expectedReloc all k L items :=
  resolveAll_layout_relocMap all hok ys _ fun _ j t _ h q hq => by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hcross q hq

/-- The layout of a nonempty stream starts with an instruction at the stream's start
    offset. -/
theorem decodeAt_head_start (n off : Nat) (bs : List (BitVec 8))
    (xs : List (Nat × Nat × DInstr)) (hne : bs ≠ []) (h : decodeAt n off bs = some xs) :
    ∃ e x tl, xs = (off, e, x) :: tl := by
  have hemp : bs.isEmpty = false := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b t => rfl
  cases n with
  | zero => simp [decodeAt, hemp] at h
  | succ n =>
    rw [decodeAt] at h
    simp only [hemp, Bool.false_eq_true, ite_false] at h
    cases hd : decodeLinstr bs with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only [hd, Option.map_eq_some_iff] at h
      obtain ⟨tl, _, rfl⟩ := h
      exact ⟨_, _, _, rfl⟩

/-- **Decoding of an item list followed by its callee blocks.** Let `items` satisfy
    `ItemOK`, and let the stream `cb` of the callee blocks decode to the layout `xs₂` and
    the program `q`. Let the target map `tgt` send each call without target label to a
    pair `(decCount items + k, (itemBytes items).length + o)`, where `o` is the byte offset
    in `cb` of the first instruction of its callee block and `k` the index of that
    instruction in `xs₂`. When the items satisfy `branchOKRelocMap` under `tgt` and denote
    `prog`, the concatenated stream decodes to `prog` followed by `q` with its targets
    raised by `prog.length`; each call without target label is `call (prog.length + k)`
    in `prog`, the index of the entry of its block in the result. -/
theorem decodeLprog_items_linkedMap (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (cb : List (BitVec 8)) (xs₂ : List (Nat × Nat × DInstr)) (q prog : List RInstr)
    (tgt : Item → Option (Nat × Nat))
    (hd : decodeAt cb.length 0 cb = some xs₂) (hr : resolveAll xs₂ xs₂ = some q)
    (hentry : ∀ it j t, it.target = none → tgt it = some (j, t) →
      ∃ o k, t = (itemBytes items).length + o ∧ j = decCount items + k
        ∧ xs₂.findIdx? (fun z => decide (z.1 = o)) = some k)
    (hbr : branchOKRelocMap items tgt 0 items = true)
    (hP : expectedRelocMap items tgt items = some prog) :
    prog.length = decCount items ∧
      decodeLprog (itemBytes items ++ cb) = some (prog ++ shiftProg prog.length q) := by
  have hlt : ∀ z ∈ layoutAt 0 items, z.1 < (itemBytes items).length := fun z hz => by
    simpa using layoutAt_start_lt items hok 0 z hz
  have h₁ : resolveAll
      (layoutAt 0 items ++ offsetLayout (itemBytes items).length xs₂)
      (layoutAt 0 items) = some prog := by
    rw [resolveAll_layout_relocMap items hok _ tgt
      (fun it j t htg hit q hq => ?_) items 0 hbr]
    · exact hP
    · obtain ⟨o, k, rfl, rfl, hk⟩ := hentry it j t htg hit
      have := findIdx?_offset_append (layoutAt 0 items) xs₂
        (itemBytes items).length o k q hlt (by simpa using hq) hk
      simpa [layoutAt_length] using this
  have hlen : prog.length = decCount items := by
    rw [← layoutAt_length items 0]
    exact ((resolveAll_eq_some_iff _ _ _).mp h₁).length_eq.symm
  refine ⟨hlen, ?_⟩
  rw [hlen]
  exact decodeLprog_append_resolved items hok cb _ prog q hd hr h₁

/-- **Decoding of an item list followed by its callee block.** Let `items` satisfy
    `ItemOK` and `branchOKReloc` at their own instruction count and byte length, and let
    the nonempty stream `cb` decode to `q`. The concatenated stream decodes to the
    program `prog` of the items followed by `q` with its targets raised by `prog.length`;
    a call without target label is `call prog.length` in `prog`, the index of the first
    instruction of `q` in the result. This is `decodeLprog_items_linkedMap` at the
    constant target map, whose one block starts at offset `0` of `cb`. -/
theorem decodeLprog_items_linked (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (cb : List (BitVec 8)) (q prog : List RInstr)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc items (decCount items) (itemBytes items).length 0 items = true)
    (hP : expectedReloc items (decCount items) (itemBytes items).length items = some prog) :
    prog.length = decCount items ∧
      decodeLprog (itemBytes items ++ cb) = some (prog ++ shiftProg prog.length q) := by
  unfold decodeLprog at hcb
  obtain ⟨xs₂, hd, hr⟩ := Option.bind_eq_some_iff.mp hcb
  obtain ⟨e, x, tl, hxs⟩ := decodeAt_head_start _ _ _ _ hne hd
  refine decodeLprog_items_linkedMap items hok cb xs₂ q prog _ hd hr
    (fun _ j t _ h => ⟨0, 0, ?_⟩) hbr hP
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [hxs, List.findIdx?_cons]

/-- The target map of the callee symbols under `m`: an item goes to the pair `m` gives its
    callee symbol `sym`, and an item without callee symbol to none. -/
abbrev symTgt (m : String → Option (Nat × Nat)) (it : Item) : Option (Nat × Nat) :=
  it.sym.bind m

/-- **Decoding of an item list followed by the blocks of several callees.** Let `items`
    satisfy `ItemOK`, and let the stream `cb` of the callee blocks decode to the layout `xs₂`
    and the program `q`. Let `m` send each callee symbol it maps to a pair
    `(decCount items + k, (itemBytes items).length + o)`, where `o` is the byte offset in `cb`
    of the entry of that callee's block and `k` the index of that entry in `xs₂`. When the
    items satisfy `branchOKRelocMap` under `symTgt m` and denote `prog`, the concatenated
    stream decodes to `prog` followed by `q` with its targets raised by `prog.length`; a call
    without target label to the symbol `f` is `call (prog.length + k)` in `prog` for the
    index `k` of the entry of the block of `f`. This is `decodeLprog_items_linkedMap` at the
    target map `symTgt m`. -/
theorem decodeLprog_items_linkedSym (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (cb : List (BitVec 8)) (xs₂ : List (Nat × Nat × DInstr)) (q prog : List RInstr)
    (m : String → Option (Nat × Nat))
    (hd : decodeAt cb.length 0 cb = some xs₂) (hr : resolveAll xs₂ xs₂ = some q)
    (hentry : ∀ f j t, m f = some (j, t) →
      ∃ o k, t = (itemBytes items).length + o ∧ j = decCount items + k
        ∧ xs₂.findIdx? (fun z => decide (z.1 = o)) = some k)
    (hbr : branchOKRelocMap items (symTgt m) 0 items = true)
    (hP : expectedRelocMap items (symTgt m) items = some prog) :
    prog.length = decCount items ∧
      decodeLprog (itemBytes items ++ cb) = some (prog ++ shiftProg prog.length q) :=
  decodeLprog_items_linkedMap items hok cb xs₂ q prog (symTgt m) hd hr
    (fun it j t _ h => by
      obtain ⟨f, -, hf⟩ := Option.bind_eq_some_iff.mp h
      exact hentry f j t hf) hbr hP

/-! ## 4. A region of several callee blocks

The callee region `cb` is decoded once, to the layout `xs₂` and the program `Q`. The block of
the symbol `f` has its entry at byte offset `o f` and index `k f`, and is the block `q f`
placed at index `k f` of `Q`. No decoding lemma for two appended byte streams is needed. -/

/-- The callee region `cb` decodes, in one pass, to a layout whose resolution is `Q`, and the
    entry of the block of each symbol `f` of `fs`, at byte offset `o f`, has index `k f`. -/
def RegionDecode (cb : List (BitVec 8)) (fs : List String) (o k : String → Nat)
    (Q : List RInstr) : Prop :=
  ∃ xs₂, decodeAt cb.length 0 cb = some xs₂ ∧ resolveAll xs₂ xs₂ = some Q
    ∧ ∀ f ∈ fs, xs₂.findIdx? (fun z => decide (z.1 = o f)) = some (k f)

/-- **The blocks of a callee region.** The region `cb` decodes to `Q` with the entry of the
    block of `f ∈ fs` at byte offset `o f` and index `k f` (`RegionDecode`); `Q` holds, from
    index `k f`, the block `q f` with its targets raised by `k f`; and `q f` has no `call`. -/
structure RegionBlocks (cb : List (BitVec 8)) (fs : List String) (o k : String → Nat)
    (q : String → List RInstr) (Q : List RInstr) : Prop where
  /-- One decode of the region, with the entry index of each block. -/
  decode : RegionDecode cb fs o k Q
  /-- The block of `f` sits at index `k f` of `Q`. -/
  block : ∀ f ∈ fs, ∃ A B, Q = A ++ shiftProg A.length (q f) ++ B ∧ A.length = k f
  /-- The block of `f` has no `call`. -/
  callFree : ∀ f ∈ fs, ∀ tg, RInstr.call tg ∉ q f

/-- **Injectivity of the entries of a region.** Symbols of `fs` told apart by their entry
    offsets are told apart by their entry indices: the entry index of a symbol determines the
    layout element at it, whose offset is the entry offset of the symbol. -/
theorem regionDecode_inj {cb : List (BitVec 8)} {fs : List String} {o k : String → Nat}
    {Q : List RInstr} (h : RegionDecode cb fs o k Q)
    (ho : ∀ f ∈ fs, ∀ g ∈ fs, o f = o g → f = g) :
    ∀ f ∈ fs, ∀ g ∈ fs, k f = k g → f = g := by
  intro f hf g hg hk
  obtain ⟨xs₂, -, -, hx⟩ := h
  have hf' := List.findIdx?_eq_some_iff_getElem.mp (hx f hf)
  have hg' := List.findIdx?_eq_some_iff_getElem.mp (hx g hg)
  refine ho f hf g hg ?_
  grind

/-- A region that decodes to `Q` from a nonempty stream has its first instruction, at byte
    offset `0`, at index `0`; every symbol has its entry there. -/
theorem regionDecode_one (cb : List (BitVec 8)) (Q : List RInstr) (fs : List String)
    (hcb : decodeLprog cb = some Q) (hne : cb ≠ []) :
    RegionDecode cb fs (fun _ => 0) (fun _ => 0) Q := by
  unfold decodeLprog at hcb
  obtain ⟨xs₂, hd, hr⟩ := Option.bind_eq_some_iff.mp hcb
  obtain ⟨e, x, tl, hxs⟩ := decodeAt_head_start _ _ _ _ hne hd
  exact ⟨xs₂, hd, hr, fun _ _ => by simp [hxs, List.findIdx?_cons]⟩

/-- **One callee block.** A nonempty stream that decodes to a block `q` without `call` is a
    region in which every symbol has the block `q`, entered at offset `0` and index `0`. -/
theorem regionBlocks_one (cb : List (BitVec 8)) (q : List RInstr) (fs : List String)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ []) (hq : ∀ tg, RInstr.call tg ∉ q) :
    RegionBlocks cb fs (fun _ => 0) (fun _ => 0) (fun _ => q) q :=
  ⟨regionDecode_one cb q fs hcb hne,
    fun _ _ => ⟨[], [], by simp [shiftProg_zero], rfl⟩, fun _ _ => hq⟩

/-- An instruction with its branch or call target lowered by `k`. -/
def unshiftInstr (k : Nat) : RInstr → RInstr
  | .jcc cc t => .jcc cc (t - k)
  | .call t => .call (t - k)
  | x => x

/-- An instruction of a block placed at index `k`: no `call`, and a branch to index `k` or
    later. -/
def blockInstrB (k : Nat) : RInstr → Bool
  | .jcc _ t => decide (k ≤ t)
  | .call _ => false
  | _ => true

/-- Raising the lowered targets of the instructions of a block placed at index `k`
    restores the block. -/
theorem shiftProg_map_unshift (k : Nat) (p : List RInstr)
    (h : ∀ x ∈ p, blockInstrB k x = true) :
    shiftProg k (p.map (unshiftInstr k)) = p := by
  unfold shiftProg
  rw [List.map_map]
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id p)
  have hx' := h x hx
  cases x <;> simp_all [blockInstrB, unshiftInstr, shiftInstr]

/-- The block of the symbol `f` in the region program `Q`: the `n f` instructions from the
    entry index `k f`, with their targets lowered by `k f`. -/
def regionBlock (Q : List RInstr) (k n : String → Nat) (f : String) : List RInstr :=
  ((Q.drop (k f)).take (n f)).map (unshiftInstr (k f))

/-- The check of a callee region: `cb` decodes in one pass to a layout whose resolution is
    some `Q`; for each `f ∈ fs` the entry at byte offset `o f` has index `k f`, the `n f`
    instructions from `k f` lie in `Q`, and each of them is no `call` and branches to
    index `k f` or later. -/
def regionBlocksB (cb : List (BitVec 8)) (fs : List String) (o k n : String → Nat) : Bool :=
  match decodeAt cb.length 0 cb with
  | none => false
  | some xs₂ =>
    match resolveAll xs₂ xs₂ with
    | none => false
    | some Q => fs.all fun f =>
        decide (xs₂.findIdx? (fun z => decide (z.1 = o f)) = some (k f))
          && decide (k f + n f ≤ Q.length)
          && ((Q.drop (k f)).take (n f)).all (blockInstrB (k f))

/-- **Soundness of `regionBlocksB`.** A region that passes the check decodes to a program
    `Q` whose blocks `regionBlock Q k n` satisfy `RegionBlocks`. -/
theorem regionBlocks_of_regionBlocksB (cb : List (BitVec 8)) (fs : List String)
    (o k n : String → Nat) (h : regionBlocksB cb fs o k n = true) :
    ∃ Q, decodeLprog cb = some Q ∧ RegionBlocks cb fs o k (regionBlock Q k n) Q := by
  unfold regionBlocksB at h
  split at h
  · cases h
  · rename_i xs₂ hd
    split at h
    · cases h
    · rename_i Q hr
      have hall : ∀ f ∈ fs, xs₂.findIdx? (fun z => decide (z.1 = o f)) = some (k f)
          ∧ k f + n f ≤ Q.length
          ∧ ∀ x ∈ (Q.drop (k f)).take (n f), blockInstrB (k f) x = true := fun f hf => by
        have := List.all_eq_true.mp h f hf
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
      refine ⟨Q, by simp [decodeLprog, hd, hr], ⟨⟨xs₂, hd, hr, fun f hf => (hall f hf).1⟩,
        fun f hf => ?_, fun f hf tg htg => ?_⟩⟩
      · obtain ⟨-, hle, hblk⟩ := hall f hf
        refine ⟨Q.take (k f), (Q.drop (k f)).drop (n f), ?_, by simp; omega⟩
        have hl : (Q.take (k f)).length = k f := by simp; omega
        rw [hl, regionBlock, shiftProg_map_unshift _ _ hblk, List.append_assoc,
          List.take_append_drop, List.take_append_drop]
      · obtain ⟨-, -, hblk⟩ := hall f hf
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp htg
        have := hblk x hx
        cases x <;> simp_all [unshiftInstr, blockInstrB]

/-! ### The prefix property of the decoder

`decodeLinstr` reads an instruction off the front of a stream. Every arm reads a number of
bytes fixed by the bytes it has read, and an arm tried after another succeeds only on streams
the earlier arm rejects with any continuation. So an instruction read off a stream is read off
every extension of it (`decodeLinstr_ext`), and a stream that decodes on its own decodes in
front of any stream (`decodeAt_append`, `decodeLprog_append_streams`). The bytes of a callee
code need not come from an item list. -/

/-- A one-instruction decoder that is stable under extension. -/
def ExtStable {α : Type} (f : List (BitVec 8) → Option (α × List (BitVec 8))) : Prop :=
  ∀ bs x r e, f bs = some (x, r) → f (bs ++ e) = some (x, r ++ e)

/-- `decodeDisp` is stable under extension of its input (`ExtStable`). -/
theorem decodeDisp_ext (n : Nat) : ExtStable (decodeDisp n) := by
  intro bs x r e h
  unfold decodeDisp at h
  split at h <;> simp_all [decodeDisp]

/-- `decodeMemTail` is stable under extension of its input. -/
theorem decodeMemTail_ext (xb : Nat) {bs r : List (BitVec 8)} {a b : Nat}
    {c : Option (Nat × Nat)} {d : Int} (e : List (BitVec 8))
    (h : decodeMemTail xb bs = some (a, b, c, d, r)) :
    decodeMemTail xb (bs ++ e) = some (a, b, c, d, r ++ e) := by
  unfold decodeMemTail at h
  split at h
  · rename_i modrm rest
    simp only [List.cons_append, decodeMemTail]
    split at h
    · simp at h
    · rename_i h3
      simp only [h3, ite_false]
      split at h
      · rename_i h4
        simp only [h4, ite_true]
        split at h
        · rename_i sib rest1
          simp only [List.cons_append]
          split at h
          · simp at h
          · rename_i h5
            simp only [h5, ite_false]
            cases hd : decodeDisp (modField modrm) rest1 with
            | none => simp [hd] at h
            | some p =>
              obtain ⟨d', r'⟩ := p
              rw [decodeDisp_ext _ _ _ _ e hd]
              simp_all
        · simp at h
      · rename_i h4
        simp only [h4, ite_false]
        split at h
        · simp at h
        · rename_i h5
          simp only [h5, ite_false]
          cases hd : decodeDisp (modField modrm) rest with
          | none => simp [hd] at h
          | some p =>
            obtain ⟨d', r'⟩ := p
            rw [decodeDisp_ext _ _ _ _ e hd]
            simp_all
  · simp at h

/-- `decodeMovzbq` is stable under extension of its input (`ExtStable`). -/
theorem decodeMovzbq_ext (n : Nat) : ExtStable (decodeMovzbq n) := by
  intro bs x r e h
  unfold decodeMovzbq at h
  split at h
  · simp only [List.cons_append, decodeMovzbq]
    split at h
    · simp_all
    · simp at h
  · simp at h

/-- `decodeRex` is stable under extension of its input (`ExtStable`). -/
theorem decodeRex_ext (rx : BitVec 8) : ExtStable (decodeRex rx) := by
  intro bs x r e h
  fun_cases decodeRex rx bs
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeRex])
  all_goals try (exact decodeMovzbq_ext _ _ _ _ e h)
  all_goals (split at h <;> first | (exfalso; omega) | simp_all)

/-- `decodeAdx` is stable under extension of its input (`ExtStable`). -/
theorem decodeAdx_ext (b : Bool) : ExtStable (decodeAdx b) := by
  intro bs x r e h
  fun_cases decodeAdx b bs
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeAdx])

/-- `decodeSetcBare` is stable under extension of its input (`ExtStable`). -/
theorem decodeSetcBare_ext : ExtStable decodeSetcBare := by
  intro bs x r e h
  fun_cases decodeSetcBare bs
  all_goals (try simp_all [decodeSetcBare])
  all_goals first
    | exact decodeMovzbq_ext _ _ _ _ e h
    | (exfalso; rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h; simp at h)

/-- `decodeMulx` is stable under extension of its input (`ExtStable`). -/
theorem decodeMulx_ext : ExtStable decodeMulx := by
  intro bs x r e h
  fun_cases decodeMulx bs
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeMulx])

/-- `decodeRexW0` is stable under extension of its input (`ExtStable`). -/
theorem decodeRexW0_ext (rx : BitVec 8) : ExtStable (decodeRexW0 rx) := by
  intro bs x r e h
  fun_cases decodeRexW0 rx bs
  all_goals (try simp_all [decodeRexW0])
  all_goals try (exact decodeMovzbq_ext _ _ _ _ e h)
  all_goals (split at h <;> simp_all)

/-- `decodeJ1` is stable under extension of its input (`ExtStable`). -/
theorem decodeJ1_ext : ExtStable decodeJ1 := by
  intro bs x r e h
  fun_cases decodeJ1 bs
  all_goals (try simp_all [decodeJ1])
  all_goals first
    | exact decodeAdx_ext _ _ _ _ e h
    | exact decodeMulx_ext _ _ _ e h
    | exact decodeRex_ext _ _ _ _ e h
    | exact decodeRexW0_ext _ _ _ _ e h
    | exact decodeSetcBare_ext _ _ _ e h

/-- `decodeShift1` is stable under extension of its input (`ExtStable`). -/
theorem decodeShift1_ext : ExtStable decodeShift1 := by
  intro bs x r e h
  fun_cases decodeShift1 bs
  all_goals (try simp_all [decodeShift1])

/-- `decodeCmp` is stable under extension of its input (`ExtStable`). -/
theorem decodeCmp_ext : ExtStable decodeCmp := by
  intro bs x r e h
  fun_cases decodeCmp bs
  all_goals (try simp_all [decodeCmp])

/-- Off a byte that is no `REX` prefix, `decodeShift1` decodes nothing. -/
theorem decodeShift1_nonrex {b0 : BitVec 8} (t : List (BitVec 8)) (hr : isRex b0 = false) :
    decodeShift1 (b0 :: t) = none := by
  unfold decodeShift1; split <;> simp_all

/-- Off a byte that is no `REX` prefix, `decodeCmp` decodes nothing. -/
theorem decodeCmp_nonrex {b0 : BitVec 8} (t : List (BitVec 8)) (hr : isRex b0 = false) :
    decodeCmp (b0 :: t) = none := by
  unfold decodeCmp; split <;> simp_all

/-- Off a `REX` prefix, `decodeJ1` is `decodeRex` at `REX.W = 1` and `decodeRexW0`
    otherwise. -/
theorem decodeJ1_rex {b : BitVec 8} (t : List (BitVec 8)) (hr : isRex b = true) :
    decodeJ1 (b :: t) = if rexW b = 1 then decodeRex b t else decodeRexW0 b t := by
  have hb : 0x40 ≤ b.toNat ∧ b.toNat ≤ 0x4f := by simpa [isRex] using hr
  simp only [decodeJ1, show ¬ b.toNat = 0x66 by omega, show ¬ b.toNat = 0xf3 by omega,
    show ¬ b.toNat = 0xc4 by omega, hr, ↓reduceIte]

/-- A stream `decodeShift1` decodes is, with any continuation, rejected by `decodeJ1`. -/
theorem decodeJ1_none_of_shift1 {bs r : List (BitVec 8)} {x : JInstr 64}
    (e : List (BitVec 8)) (h : decodeShift1 bs = some (x, r)) : decodeJ1 (bs ++ e) = none := by
  fun_cases decodeShift1 bs
  all_goals (try simp_all [decodeShift1])
  all_goals simp_all [decodeJ1_rex, decodeRex, aluMnemonic]

/-- A stream `decodeCmp` decodes is, with any continuation, rejected by `decodeJ1` and by
    `decodeShift1`. -/
theorem decodeJ1_none_of_cmp {bs r : List (BitVec 8)} {x : JInstr 64}
    (e : List (BitVec 8)) (h : decodeCmp bs = some (x, r)) :
    decodeJ1 (bs ++ e) = none ∧ decodeShift1 (bs ++ e) = none := by
  fun_cases decodeCmp bs
  all_goals (try simp_all [decodeCmp])
  all_goals simp_all [decodeJ1_rex, decodeRex, aluMnemonic, aluImmMnemonic, decodeShift1]

/-- `decodeJ1_6` is stable under extension of its input (`ExtStable`). -/
theorem decodeJ1_6_ext : ExtStable decodeJ1_6 := by
  intro bs x r e h
  unfold decodeJ1_6 at h ⊢
  cases h1 : decodeJ1 bs with
  | some p =>
    obtain ⟨i, r'⟩ := p
    simp only [h1, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [decodeJ1_ext _ _ _ e h1]
  | none =>
    simp only [h1] at h
    cases h2 : decodeShift1 bs with
    | some p =>
      obtain ⟨i, r'⟩ := p
      simp only [h2, Option.some_or, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [decodeJ1_none_of_shift1 e h2, decodeShift1_ext _ _ _ e h2]
      rfl
    | none =>
      simp only [h2, Option.none_or] at h
      obtain ⟨hj, hs⟩ := decodeJ1_none_of_cmp e h
      rw [hj, hs, decodeCmp_ext _ _ _ e h]
      rfl

/-- Off a leading byte that is no `REX` prefix and none of `66`, `F3`, `C4`, `0F`,
    `decodeJ1_6` decodes nothing. -/
theorem decodeJ1_6_plain {b0 : BitVec 8} (t : List (BitVec 8)) (hr : isRex b0 = false)
    (h66 : b0.toNat ≠ 0x66) (hf3 : b0.toNat ≠ 0xf3) (hc4 : b0.toNat ≠ 0xc4)
    (h0f : b0.toNat ≠ 0x0f) : decodeJ1_6 (b0 :: t) = none := by
  have h1 : decodeJ1 (b0 :: t) = none := by simp [decodeJ1, h66, hf3, hc4, h0f, hr]
  simp [decodeJ1_6, h1, decodeShift1_nonrex t hr, decodeCmp_nonrex t hr]

/-- `decodeVex3` is stable under extension of its input (`ExtStable`). -/
theorem decodeVex3_ext : ExtStable decodeVex3 := by
  intro bs x r e h
  fun_cases decodeVex3 bs
  all_goals (try simp_all [decodeVex3])
  all_goals (split_ifs at h <;> simp_all)

/-- `decodeRexExt` is stable under extension of its input (`ExtStable`). -/
theorem decodeRexExt_ext (rx : BitVec 8) : ExtStable (decodeRexExt rx) := by
  intro bs x r e h
  fun_cases decodeRexExt rx bs
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeRexExt])
  all_goals (try simp_all [decodeMemTail])
  all_goals (repeat' (split at h))
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals simp_all [decodeMemTail]

/-- `decodeRexPushPop` is stable under extension of its input (`ExtStable`). -/
theorem decodeRexPushPop_ext (rx : BitVec 8) : ExtStable (decodeRexPushPop rx) := by
  intro bs x r e h
  fun_cases decodeRexPushPop rx bs
  all_goals (try simp_all [decodeRexPushPop, decodePushPop])
  all_goals (split at h <;> simp_all)

/-- `decodeRexMov32` is stable under extension of its input (`ExtStable`). -/
theorem decodeRexMov32_ext (rx : BitVec 8) : ExtStable (decodeRexMov32 rx) := by
  intro bs x r e h
  fun_cases decodeRexMov32 rx bs
  all_goals (try simp_all [decodeRexMov32])

/-- After `C4`, a stream `decodeVex3` decodes is, with any continuation, rejected by
    `decodeJ1_6`: its opcode byte `F7` is not the `F6` of `decodeMulx`. -/
theorem decodeJ1_6_c4 {b0 : BitVec 8} {t r : List (BitVec 8)} {x : JInstr 64}
    (e : List (BitVec 8)) (hb : b0.toNat = 0xc4) (h : decodeVex3 t = some (x, r)) :
    decodeJ1_6 (b0 :: (t ++ e)) = none := by
  fun_cases decodeVex3 t
  all_goals (try simp_all [decodeVex3])
  all_goals (try split_ifs at h)
  all_goals simp_all [decodeJ1_6, decodeJ1, decodeMulx, decodeShift1, decodeCmp, isRex]

/-- After `0F`, a byte of `80`..`8F` (the second opcode byte of `jcc rel32`) is rejected by
    `decodeJ1_6`. -/
theorem decodeJ1_6_0f {b0 o : BitVec 8} (t : List (BitVec 8)) (hb : b0.toNat = 0x0f)
    (ho : 0x80 ≤ o.toNat ∧ o.toNat ≤ 0x8f) : decodeJ1_6 (b0 :: o :: t) = none := by
  have h1 : decodeSetcBare (o :: t) = none := by
    unfold decodeSetcBare
    split
    · rename_i heq
      obtain ⟨rfl, -⟩ := List.cons.inj heq
      simp only [show ¬ o.toNat = 0x92 by omega, false_and, ↓reduceIte, setccCond?,
        show ¬ o.toNat = 0x94 by omega, show ¬ o.toNat = 0x95 by omega, Option.map_none]
      split <;> rfl
    · rfl
  have hr : isRex b0 = false := by simp [isRex, hb]
  simp [decodeJ1_6, decodeJ1, hb, h1, decodeShift1_nonrex _ hr, decodeCmp_nonrex _ hr, hr]

/-- The ModRM byte of `decodeMemTail` at `mod = 00` with a SIB byte whose base field is not
    `101`: the operand decodes with displacement `0`, whatever follows. -/
theorem decodeMemTail_sib0 (xb : Nat) {modrm sib : BitVec 8} (t : List (BitVec 8))
    (hmod : modField modrm = 0) (hrm : rmField modrm = 4) (hsib : rmField sib ≠ 5) :
    ∃ c, decodeMemTail xb (modrm :: sib :: t) = some (regField modrm, rmField sib, c, 0, t) := by
  simp [decodeMemTail, hmod, hrm, hsib, decodeDisp]

/-- `decodeRex` decodes the `8B`/`89` forms at `mod = 00` with a SIB byte whose base field is
    not `101`, whatever follows. -/
theorem decodeRex_sib0_ne_none {b0 op modrm sib : BitVec 8} (t : List (BitVec 8))
    (hop : op.toNat = 0x8b ∨ op.toNat = 0x89) (hmod : modField modrm = 0)
    (hrm : rmField modrm = 4)
    (hsib : rmField sib ≠ 5) : decodeRex b0 (op :: modrm :: sib :: t) ≠ none := by
  obtain ⟨c, hc⟩ := decodeMemTail_sib0 (rexX b0) t hmod hrm hsib
  rcases hop with hop | hop
  · cases c <;> simp [decodeRex, hop, hc]
  · cases c <;> simp [decodeRex, hop, hc, hmod]

/-- `decodeRex` at `0F` followed by a byte of `40`..`4F` and a register-direct ModRM byte does
    not read past the ModRM byte. -/
theorem decodeRex_cmov_reg {b0 op modrm m : BitVec 8} (t e : List (BitVec 8))
    (hop : op.toNat = 0x0f) (hc : 0x40 ≤ modrm.toNat ∧ modrm.toNat ≤ 0x4f)
    (hm : modField m = 3)
    (hn : decodeRex b0 (op :: modrm :: m :: t) = none) :
    decodeRex b0 (op :: modrm :: m :: (t ++ e)) = none := by
  by_cases h44 : modrm.toNat = 0x44
  · simp [decodeRex, hop, hm, h44] at hn
  by_cases h45 : modrm.toNat = 0x45
  · simp [decodeRex, hop, hm, h45] at hn
  by_cases h42 : modrm.toNat = 0x42
  · simp [decodeRex, hop, hm, h42] at hn
  simp [decodeRex, hop, hm, h44, h45, h42, show ¬ modrm.toNat = 0xaf by omega,
    show ¬ modrm.toNat = 0xb6 by omega, show ¬ modrm.toNat = 0xb7 by omega,
    show ¬ modrm.toNat = 0x92 by omega, show ¬ modrm.toNat = 0xba by omega]

/-- `decodeRex` at `0F` followed by a ModRM byte of a memory operand decodes nothing. -/
theorem decodeRex_0f_mem {b0 op modrm m : BitVec 8} (t : List (BitVec 8))
    (hop : op.toNat = 0x0f) (hm : modField m ≠ 3) :
    decodeRex b0 (op :: modrm :: m :: t) = none := by
  simp [decodeRex, hop, hm]

/-- A stream that `decodeMemTail` decodes starts with a ModRM byte of a memory operand. -/
theorem decodeMemTail_cons {xb : Nat} {bs r : List (BitVec 8)} {a b : Nat}
    {c : Option (Nat × Nat)} {d : Int} (h : decodeMemTail xb bs = some (a, b, c, d, r)) :
    ∃ m t, bs = m :: t ∧ modField m ≠ 3 := by
  rcases bs with _ | ⟨m, t⟩
  · simp [decodeMemTail] at h
  · refine ⟨m, t, rfl, fun hm => ?_⟩
    simp [decodeMemTail, hm] at h

/-- Off a `REX.W` prefix followed by an opcode byte other than `D1`, `39` and `81`,
    `decodeJ1_6` is `decodeRex`. -/
theorem decodeJ1_6_rexW1 {b0 op : BitVec 8} (t : List (BitVec 8)) (hrex : isRex b0 = true)
    (hw : SailX86Decoder.rexW b0 = 1) (h1 : op.toNat ≠ 0xd1) (h2 : op.toNat ≠ 0x39)
    (h3 : op.toNat ≠ 0x81) : decodeJ1_6 (b0 :: op :: t) = decodeRex b0 (op :: t) := by
  have hs : decodeShift1 (b0 :: op :: t) = none := by
    unfold decodeShift1; split <;> simp_all
  have hc : decodeCmp (b0 :: op :: t) = none := by
    unfold decodeCmp; split <;> simp_all
  unfold decodeJ1_6
  rw [decodeJ1_rex _ hrex]
  simp only [hw, ↓reduceIte]
  cases decodeRex b0 (op :: t) <;> simp [hs, hc]

/-- Off a `REX` prefix, a stream `decodeRexExt` decodes and `decodeJ1_6` rejects is, with any
    continuation, still rejected by `decodeJ1_6`. -/
theorem decodeJ1_6_rexExt {b0 : BitVec 8} {t r : List (BitVec 8)} {x : JInstr 64}
    (e : List (BitVec 8)) (hrex : isRex b0 = true) (h : decodeRexExt b0 t = some (x, r))
    (hn : decodeJ1_6 (b0 :: t) = none) : decodeJ1_6 (b0 :: (t ++ e)) = none := by
  fun_cases decodeRexExt b0 t
  all_goals try (have := decodeMemTail_ext _ e ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeRexExt])
  all_goals
    rw [decodeJ1_6_rexW1 _ hrex (by assumption) (by omega) (by omega) (by omega)] at hn ⊢
  case case2 => clear h hn; simp_all [decodeRex, aluMnemonic]
  case case4 => clear h hn; simp_all [decodeRex, aluMnemonic]
  case case12 => clear h hn; simp_all [decodeRex]
  case case18 => clear h hn; simp_all [decodeRex]
  case case14 => clear h hn; simp_all [decodeRex]
  case case16 => clear h hn; simp_all [decodeRex]
  case case7 =>
    obtain ⟨m, t, heq, hm⟩ := decodeMemTail_cons ‹decodeMemTail _ _ = some _›
    rw [heq]
    exact decodeRex_0f_mem _ ‹_› hm
  case case8 => exact decodeRex_cmov_reg _ _ ‹_› ‹_› ‹_› hn
  case case11 =>
    obtain ⟨hc, h⟩ := h
    split at h
    · rename_i hmt
      obtain ⟨m, t, rfl, hm⟩ := decodeMemTail_cons hmt
      exact decodeRex_0f_mem _ ‹_› hm
    · split at h
      · split at h
        · exact decodeRex_cmov_reg _ _ ‹_› hc ‹_› hn
        · simp at h
      · simp at h
  case case20 => exact absurd ‹_ = 4› h.1.1
  case case21 =>
    exact absurd hn
      (decodeRex_sib0_ne_none _ (Or.inl ‹_›) ‹_ ∧ _›.1 ‹_ ∧ _›.2 ‹_ ∧ _›.2)
  case case22 =>
    exact absurd hn
      (decodeRex_sib0_ne_none _ (Or.inr ‹_›) ‹_ ∧ _›.1 ‹_ ∧ _›.2 ‹_ ∧ _›.2)

/-- Off a `REX` prefix with `REX.W = 0`, `decodeJ1_6` is `decodeRexW0`. -/
theorem decodeJ1_6_rexW0 {b0 : BitVec 8} (t : List (BitVec 8)) (hrex : isRex b0 = true)
    (hw : SailX86Decoder.rexW b0 = 0) : decodeJ1_6 (b0 :: t) = decodeRexW0 b0 t := by
  have hs : decodeShift1 (b0 :: t) = none := by
    unfold decodeShift1; split <;> simp_all
  have hc : decodeCmp (b0 :: t) = none := by
    unfold decodeCmp; split <;> simp_all
  unfold decodeJ1_6
  rw [decodeJ1_rex _ hrex]
  simp only [hw, zero_ne_one, ↓reduceIte]
  cases decodeRexW0 b0 t <;> simp [hs, hc]

/-- Off a `REX` prefix with `REX.W = 0`, `decodeRexExt` decodes nothing. -/
theorem decodeRexExt_w0 {b0 : BitVec 8} (t : List (BitVec 8))
    (hw : SailX86Decoder.rexW b0 = 0) : decodeRexExt b0 t = none := by
  unfold decodeRexExt; split <;> simp_all

/-- Off the prefix `41`, a stream `decodeRexPushPop` decodes is, with any continuation,
    rejected by `decodeJ1_6` and by `decodeRexExt`. -/
theorem decodeJ1_6_rexPushPop {b0 : BitVec 8} {t r : List (BitVec 8)} {x : DInstr}
    (e : List (BitVec 8)) (h : decodeRexPushPop b0 t = some (x, r)) :
    decodeJ1_6 (b0 :: (t ++ e)) = none ∧ decodeRexExt b0 (t ++ e) = none := by
  fun_cases decodeRexPushPop b0 t
  · rename_i op rest hb
    have hrex : isRex b0 = true := by simp [isRex, hb]
    have hw : SailX86Decoder.rexW b0 = 0 := by simp [SailX86Decoder.rexW, hb]
    have hop : 0x50 ≤ op.toNat ∧ op.toNat ≤ 0x5f := by
      simp only [hb, ↓reduceIte, decodeRexPushPop, decodePushPop] at h
      split at h
      · simp at h
      · split at h
        · omega
        · split at h
          · omega
          · simp at h
    refine ⟨?_, decodeRexExt_w0 _ hw⟩
    rw [decodeJ1_6_rexW0 _ hrex hw]
    simp [decodeRexW0, show ¬ op.toNat = 0x0f by omega, show ¬ (0xb8 ≤ op.toNat) by omega]
  · simp_all [decodeRexPushPop]
  · simp [decodeRexPushPop] at h

/-- Off a `REX` prefix, a stream `decodeRexMov32` decodes is, with any continuation, rejected
    by `decodeJ1_6`, `decodeRexExt` and `decodeRexPushPop`. -/
theorem decodeJ1_6_rexMov32 {b0 : BitVec 8} {t r : List (BitVec 8)} {x : DInstr}
    (e : List (BitVec 8)) (hrex : isRex b0 = true) (h : decodeRexMov32 b0 t = some (x, r)) :
    decodeJ1_6 (b0 :: (t ++ e)) = none ∧ decodeRexExt b0 (t ++ e) = none
      ∧ decodeRexPushPop b0 (t ++ e) = none := by
  fun_cases decodeRexMov32 b0 t
  · rename_i op modrm rest hc
    obtain ⟨hw, hop, -⟩ := hc
    refine ⟨?_, decodeRexExt_w0 _ hw, ?_⟩
    · rw [decodeJ1_6_rexW0 _ hrex hw]
      simp [decodeRexW0, hop]
    · simp [decodeRexPushPop, decodePushPop, hop]
  · simp_all [decodeRexMov32]
  · simp [decodeRexMov32] at h

/-- **Prefix property of the one-instruction decoder.** An instruction that `decodeLinstr`
    reads off the front of a stream is read off the front of every extension of that stream,
    with the extension appended to the remaining bytes. Each arm of the decoder reads a fixed
    number of bytes once its leading bytes are fixed, and an arm tried after another succeeds
    only on streams that the earlier arm rejects whatever follows (`decodeJ1_6_plain`,
    `decodeJ1_6_0f`, `decodeJ1_6_c4`, `decodeJ1_6_rexExt`, `decodeJ1_6_rexPushPop`,
    `decodeJ1_6_rexMov32`). -/
theorem decodeLinstr_ext : ExtStable decodeLinstr := by
  intro bs x r e h
  rcases bs with _ | ⟨b0, t⟩
  · simp [decodeLinstr] at h
  cases hj : decodeJ1_6 (b0 :: t) with
  | some p =>
    obtain ⟨i, r'⟩ := p
    simp only [decodeLinstr, hj, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have := decodeJ1_6_ext _ _ _ e hj
    simp only [List.cons_append] at this
    simp only [List.cons_append, decodeLinstr, this]
  | none =>
    simp only [decodeLinstr, hj] at h
    simp only [List.cons_append, decodeLinstr]
    have hplain : isRex b0 = false → b0.toNat ≠ 0x66 → b0.toNat ≠ 0xf3 →
        b0.toNat ≠ 0xc4 → b0.toNat ≠ 0x0f → decodeJ1_6 (b0 :: (t ++ e)) = none :=
      fun a b c d f => decodeJ1_6_plain _ a b c d f
    have hrexB : isRex b0 = true ↔ 0x40 ≤ b0.toNat ∧ b0.toNat ≤ 0x4f := by simp [isRex]
    by_cases h1 : b0.toNat = 0xc3
    · rw [hplain (by simp [isRex, h1]) (by omega) (by omega) (by omega) (by omega)]
      simp only [h1, ↓reduceIte, Option.some.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    by_cases h2 : 0x70 ≤ b0.toNat ∧ b0.toNat ≤ 0x7f
    · rw [hplain (by simp [isRex]; omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [h1, h2, ↓reduceIte, and_self] at h ⊢
      rcases t with _ | ⟨d, t⟩
      · simp at h
      · simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rfl
    by_cases h3 : b0.toNat = 0x0f
    · simp only [h1, h2, ↓reduceIte] at h ⊢
      simp only [h3, ↓reduceIte] at h ⊢
      split at h
      · rename_i o d0 d1 d2 d3 t'
        by_cases ho : 0x80 ≤ o.toNat ∧ o.toNat ≤ 0x8f
        · rw [List.cons_append, decodeJ1_6_0f _ h3 ho]
          simp only [List.cons_append, ho, and_self, ↓reduceIte, Option.some.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          rfl
        · simp [ho] at h
      · simp at h
    by_cases h4 : b0.toNat = 0xc4
    · simp only [h1, h2, h3, ↓reduceIte] at h ⊢
      simp only [h4, ↓reduceIte] at h ⊢
      obtain ⟨⟨i, r'⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [decodeJ1_6_c4 e h4 hs, decodeVex3_ext _ _ _ e hs]
      rfl
    simp only [h1, h2, h3, h4, ↓reduceIte] at h ⊢
    by_cases h5 : isRex b0 = true
    · simp only [h5, ↓reduceIte] at h ⊢
      cases ha : decodeRexExt b0 t with
      | some p =>
        obtain ⟨i, r'⟩ := p
        simp only [ha, Option.map_some, Option.some_or, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [decodeJ1_6_rexExt e h5 ha hj, decodeRexExt_ext _ _ _ _ e ha]
        rfl
      | none =>
        cases hb : decodeRexPushPop b0 t with
        | some p =>
          obtain ⟨y, r'⟩ := p
          simp only [ha, hb, Option.map_none, Option.none_or, Option.some_or,
            Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          obtain ⟨k1, k2⟩ := decodeJ1_6_rexPushPop e hb
          rw [k1, k2, decodeRexPushPop_ext _ _ _ _ e hb]
          rfl
        | none =>
          simp only [ha, hb, Option.map_none, Option.none_or] at h
          obtain ⟨k1, k2, k3⟩ := decodeJ1_6_rexMov32 e h5 h
          rw [k1, k2, k3, decodeRexMov32_ext _ _ _ _ e h]
          rfl
    have h5' : isRex b0 = false := by simpa using h5
    simp only [h5', Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h6 : 0x50 ≤ b0.toNat ∧ b0.toNat ≤ 0x5f
    · rw [hplain h5' (by omega) (by omega) h4 h3]
      simp only [h6, and_self, ↓reduceIte] at h ⊢
      unfold decodePushPop at h ⊢
      split_ifs at h ⊢ <;> simp_all
    simp only [h6, ↓reduceIte] at h ⊢
    by_cases h7 : 0xb8 ≤ b0.toNat ∧ b0.toNat ≤ 0xbf
    · rw [hplain h5' (by omega) (by omega) h4 h3]
      simp only [h7, and_self, ↓reduceIte] at h ⊢
      split at h
      · simp only [List.cons_append, Option.some.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rfl
      · simp at h
    simp only [h7, ↓reduceIte] at h ⊢
    by_cases h8 : b0.toNat = 0xe8
    · rw [hplain h5' (by omega) (by omega) h4 h3]
      simp only [h8, ↓reduceIte] at h ⊢
      split at h
      · simp only [List.cons_append, Option.some.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rfl
      · simp at h
    simp [h8] at h

/-- A one-instruction decoder whose remaining bytes are at most as many as its input bytes. -/
def NoLonger {α : Type} (f : List (BitVec 8) → Option (α × List (BitVec 8))) : Prop :=
  ∀ bs x r, f bs = some (x, r) → r.length ≤ bs.length

/-- `decodeDisp` leaves no more bytes than it reads. -/
theorem decodeDisp_len (n : Nat) : NoLonger (decodeDisp n) := by
  intro bs x r h
  unfold decodeDisp at h
  split at h <;> simp_all
  omega

/-- `decodeMemTail` leaves no more bytes than it reads. -/
theorem decodeMemTail_len (xb : Nat) {bs r : List (BitVec 8)} {a b : Nat}
    {c : Option (Nat × Nat)} {d : Int} (h : decodeMemTail xb bs = some (a, b, c, d, r)) :
    r.length ≤ bs.length := by
  unfold decodeMemTail at h
  split at h
  · rename_i modrm rest
    split at h
    · simp at h
    · split at h
      · split at h
        · rename_i sib rest1
          split at h
          · simp at h
          · obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp h
            have := decodeDisp_len _ _ _ _ hp
            simp only [Prod.mk.injEq] at hpe
            rw [← hpe.2.2.2.2]
            simp only [List.length_cons]
            omega
        · simp at h
      · split at h
        · simp at h
        · obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.mp h
          have := decodeDisp_len _ _ _ _ hp
          simp only [Prod.mk.injEq] at hpe
          rw [← hpe.2.2.2.2]
          simp only [List.length_cons]
          omega
  · simp at h

/-- `decodeMovzbq` leaves no more bytes than it reads. -/
theorem decodeMovzbq_len (n : Nat) : NoLonger (decodeMovzbq n) := by
  intro bs x r h
  fun_cases decodeMovzbq n bs
  all_goals (try simp_all [decodeMovzbq])
  omega

/-- `decodeAdx` leaves no more bytes than it reads. -/
theorem decodeAdx_len (b : Bool) : NoLonger (decodeAdx b) := by
  intro bs x r h
  fun_cases decodeAdx b bs
  all_goals try (have := decodeMemTail_len _ ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeAdx])
  all_goals try omega

/-- `decodeSetcBare` leaves no more bytes than it reads. -/
theorem decodeSetcBare_len : NoLonger decodeSetcBare := by
  intro bs x r h
  fun_cases decodeSetcBare bs
  all_goals (try simp_all [decodeSetcBare])
  all_goals try (have := decodeMovzbq_len _ _ _ _ ‹decodeMovzbq _ _ = some _›; simp; omega)
  all_goals try (split at h <;> simp_all <;> omega)
  all_goals try (obtain ⟨_, _, _, rfl⟩ := h; omega)

/-- `decodeMulx` leaves no more bytes than it reads. -/
theorem decodeMulx_len : NoLonger decodeMulx := by
  intro bs x r h
  fun_cases decodeMulx bs
  all_goals try (have := decodeMemTail_len _ ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeMulx])
  all_goals try omega

/-- `decodeRex` leaves no more bytes than it reads. -/
theorem decodeRex_len (rx : BitVec 8) : NoLonger (decodeRex rx) := by
  intro bs x r h
  fun_cases decodeRex rx bs
  all_goals try (have := decodeMemTail_len _ ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeRex])
  all_goals try omega
  all_goals try (have := decodeMovzbq_len _ _ _ _ ‹decodeMovzbq _ _ = some _›; simp; omega)
  all_goals try (split at h <;> simp_all <;> omega)

/-- `decodeRexW0` leaves no more bytes than it reads. -/
theorem decodeRexW0_len (rx : BitVec 8) : NoLonger (decodeRexW0 rx) := by
  intro bs x r h
  fun_cases decodeRexW0 rx bs
  all_goals (try simp_all [decodeRexW0])
  all_goals try omega
  all_goals try (have := decodeMovzbq_len _ _ _ _ ‹decodeMovzbq _ _ = some _›; simp; omega)
  all_goals try (split at h <;> simp_all; omega)
  all_goals try (obtain ⟨_, _, _, rfl⟩ := h; omega)

/-- `decodeVex3` leaves no more bytes than it reads. -/
theorem decodeVex3_len : NoLonger decodeVex3 := by
  intro bs x r h
  fun_cases decodeVex3 bs
  all_goals (try simp_all [decodeVex3])
  all_goals try (split_ifs at h <;> simp_all)
  all_goals try (obtain ⟨_, _, _, rfl⟩ := h; omega)

/-- `decodeRexExt` leaves no more bytes than it reads. -/
theorem decodeRexExt_len (rx : BitVec 8) : NoLonger (decodeRexExt rx) := by
  intro bs x r h
  fun_cases decodeRexExt rx bs
  all_goals try (have := decodeMemTail_len _ ‹decodeMemTail _ _ = some _›)
  all_goals (try simp_all [decodeRexExt])
  all_goals try omega
  all_goals try (obtain ⟨_, _, _, rfl⟩ := h; omega)
  all_goals
    obtain ⟨-, h⟩ := h
    split at h
    · rename_i hm
      have := decodeMemTail_len _ hm
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      omega
    · split at h
      · split at h
        · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
          obtain ⟨_, _, _, rfl⟩ := h
          simp only [List.length_cons]
          omega
        · simp at h
      · simp at h

/-- `decodeRexPushPop` leaves no more bytes than it reads. -/
theorem decodeRexPushPop_len (rx : BitVec 8) : NoLonger (decodeRexPushPop rx) := by
  intro bs x r h
  fun_cases decodeRexPushPop rx bs
  all_goals (try simp_all [decodeRexPushPop])
  all_goals
    simp only [decodePushPop] at h
    split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h
    all_goals (obtain ⟨-, rfl⟩ := h; simp)

/-- `decodeRexMov32` leaves no more bytes than it reads. -/
theorem decodeRexMov32_len (rx : BitVec 8) : NoLonger (decodeRexMov32 rx) := by
  intro bs x r h
  fun_cases decodeRexMov32 rx bs
  all_goals (try simp_all [decodeRexMov32])
  all_goals try omega

/-- A one-instruction decoder that consumes at least one byte. -/
def Shorter {α : Type} (f : List (BitVec 8) → Option (α × List (BitVec 8))) : Prop :=
  ∀ bs x r, f bs = some (x, r) → r.length < bs.length

/-- `decodeJ1` consumes at least one byte. -/
theorem decodeJ1_len : Shorter decodeJ1 := by
  intro bs x r h
  fun_cases decodeJ1 bs
  all_goals (try simp_all [decodeJ1])
  all_goals first
    | (have := decodeAdx_len _ _ _ _ h; omega)
    | (have := decodeMulx_len _ _ _ h; omega)
    | (have := decodeRex_len _ _ _ _ h; omega)
    | (have := decodeRexW0_len _ _ _ _ h; omega)
    | (have := decodeSetcBare_len _ _ _ h; omega)

/-- `decodeShift1` consumes at least one byte. -/
theorem decodeShift1_len : Shorter decodeShift1 := by
  intro bs x r h
  fun_cases decodeShift1 bs
  all_goals (try simp_all [decodeShift1])
  all_goals omega

/-- `decodeCmp` consumes at least one byte. -/
theorem decodeCmp_len : Shorter decodeCmp := by
  intro bs x r h
  fun_cases decodeCmp bs
  all_goals (try simp_all [decodeCmp])
  all_goals (try omega)

/-- `decodeJ1_6` consumes at least one byte. -/
theorem decodeJ1_6_len : Shorter decodeJ1_6 := by
  intro bs x r h
  unfold decodeJ1_6 at h
  split at h
  · rename_i p hp
    simp only [Option.some.injEq] at h
    subst h
    exact decodeJ1_len _ _ _ hp
  · cases hs : decodeShift1 bs with
    | some p =>
      obtain ⟨i, r'⟩ := p
      simp only [hs, Option.some_or, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact decodeShift1_len _ _ _ hs
    | none =>
      simp only [hs, Option.none_or] at h
      exact decodeCmp_len _ _ _ h

/-- `decodeLinstr` consumes at least one byte. -/
theorem decodeLinstr_len : Shorter decodeLinstr := by
  intro bs x r h
  rcases bs with _ | ⟨b0, t⟩
  · simp [decodeLinstr] at h
  suffices r.length ≤ t.length by simp only [List.length_cons]; omega
  cases hj : decodeJ1_6 (b0 :: t) with
  | some p =>
    obtain ⟨i, r'⟩ := p
    simp only [decodeLinstr, hj, Option.some.injEq] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    have := decodeJ1_6_len _ _ _ hj
    simp only [List.length_cons] at this
    omega
  | none =>
    simp only [decodeLinstr, hj] at h
    split_ifs at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact le_rfl
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [List.length_cons]
        omega
      · simp at h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simp only [List.length_cons]
          omega
        · simp at h
      · simp at h
    · obtain ⟨⟨i, r'⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact decodeVex3_len _ _ _ hs
    · cases ha : decodeRexExt b0 t with
      | some p =>
        obtain ⟨i, r'⟩ := p
        simp only [ha, Option.map_some, Option.some_or, Option.some.injEq] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj h
        exact decodeRexExt_len _ _ _ _ ha
      | none =>
        cases hb : decodeRexPushPop b0 t with
        | some p =>
          obtain ⟨y, r'⟩ := p
          simp only [ha, hb, Option.map_none, Option.none_or, Option.some_or,
            Option.some.injEq] at h
          obtain ⟨-, rfl⟩ := Prod.mk.inj h
          exact decodeRexPushPop_len _ _ _ _ hb
        | none =>
          simp only [ha, hb, Option.map_none, Option.none_or] at h
          exact decodeRexMov32_len _ _ _ _ h
    · simp only [decodePushPop] at h
      split_ifs at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ] at h
      all_goals (obtain ⟨-, rfl⟩ := h; exact le_rfl)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [List.length_cons]
        omega
      · simp at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [List.length_cons]
        omega
      · simp at h

/-- **Decoding of an appended stream.** When `b₁` decodes from `off` to `xs₁` and `b₂`
    decodes from the end of `b₁` to `xs₂`, their concatenation decodes from `off` to
    `xs₁ ++ xs₂`. -/
theorem decodeAt_append :
    ∀ (n off : Nat) (b₁ : List (BitVec 8)) (xs₁ : List (Nat × Nat × DInstr)),
      decodeAt n off b₁ = some xs₁ → ∀ (m : Nat) (b₂ : List (BitVec 8))
      (xs₂ : List (Nat × Nat × DInstr)), decodeAt m (off + b₁.length) b₂ = some xs₂ →
      decodeAt (n + m) off (b₁ ++ b₂) = some (xs₁ ++ xs₂) := by
  intro n
  induction n with
  | zero =>
    intro off b₁ xs₁ h m b₂ xs₂ h₂
    simp only [decodeAt] at h
    split at h
    · rename_i he
      have : b₁ = [] := List.isEmpty_iff.mp he
      subst this
      simp only [Option.some.injEq] at h
      subst h
      simpa using h₂
    · simp at h
  | succ n ih =>
    intro off b₁ xs₁ h m b₂ xs₂ h₂
    rw [decodeAt] at h
    split at h
    · rename_i he
      have : b₁ = [] := List.isEmpty_iff.mp he
      subst this
      simp only [Option.some.injEq] at h
      subst h
      simp only [List.length_nil, Nat.add_zero] at h₂
      simpa using decodeAt_fuel_mono h₂ (by omega)
    · rename_i he
      cases hd : decodeLinstr b₁ with
      | none => simp [hd] at h
      | some q =>
        obtain ⟨x, r⟩ := q
        simp only [hd] at h
        obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
        have hlt := decodeLinstr_len _ _ _ hd
        have hext := decodeLinstr_ext _ _ _ b₂ hd
        have hne : (b₁ ++ b₂).isEmpty = false := by
          cases b₁ with
          | nil => simp at he
          | cons _ _ => rfl
        rw [show n + 1 + m = (n + m) + 1 by omega, decodeAt, hne]
        simp only [Bool.false_eq_true, ↓reduceIte, hext]
        have hl : (b₁ ++ b₂).length - (r ++ b₂).length = b₁.length - r.length := by
          simp only [List.length_append]; omega
        have h₂' : decodeAt m (off + (b₁.length - r.length) + r.length) b₂ = some xs₂ := by
          rw [show off + (b₁.length - r.length) + r.length = off + b₁.length by omega]
          exact h₂
        rw [hl, ih _ _ _ hys m b₂ xs₂ h₂']
        rfl

/-- Every entry of a decoded stream starts before the end of the stream. -/
theorem decodeAt_start_lt :
    ∀ (n off : Nat) (bs : List (BitVec 8)) (xs : List (Nat × Nat × DInstr)),
      decodeAt n off bs = some xs → ∀ z ∈ xs, z.1 < off + bs.length := by
  intro n
  induction n with
  | zero =>
    intro off bs xs h z hz
    simp only [decodeAt] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp at hz
    · simp at h
  | succ n ih =>
    intro off bs xs h z hz
    rw [decodeAt] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp at hz
    · rename_i he
      cases hd : decodeLinstr bs with
      | none => simp [hd] at h
      | some q =>
        obtain ⟨x, r⟩ := q
        simp only [hd] at h
        obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
        have hlt := decodeLinstr_len _ _ _ hd
        rcases List.mem_cons.mp hz with rfl | hz
        · have : bs.length ≠ 0 := by
            cases bs with
            | nil => simp at he
            | cons _ _ => simp
          simp only
          omega
        · have := ih _ _ _ hys z hz
          omega

/-- **Decoding of an appended stream.** When `b₁` decodes to `p₁` and `b₂` decodes to `p₂`,
    their concatenation decodes to `p₁` followed by `p₂` with every branch and call target
    raised by the length of `p₁`, and the layout of the concatenation is that of `b₁`
    followed by that of `b₂` with its offsets raised by the length of `b₁`. -/
theorem decodeLprog_append_streams {b₁ b₂ : List (BitVec 8)}
    {xs₁ xs₂ : List (Nat × Nat × DInstr)}
    {p₁ p₂ : List RInstr} (hd₁ : decodeAt b₁.length 0 b₁ = some xs₁)
    (hr₁ : resolveAll xs₁ xs₁ = some p₁) (hd₂ : decodeAt b₂.length 0 b₂ = some xs₂)
    (hr₂ : resolveAll xs₂ xs₂ = some p₂) :
    decodeAt (b₁ ++ b₂).length 0 (b₁ ++ b₂) = some (xs₁ ++ offsetLayout b₁.length xs₂)
      ∧ resolveAll (xs₁ ++ offsetLayout b₁.length xs₂)
          (xs₁ ++ offsetLayout b₁.length xs₂) = some (p₁ ++ shiftProg p₁.length p₂)
      ∧ xs₁.length = p₁.length ∧ ∀ z ∈ xs₁, z.1 < b₁.length := by
  have hd₂' : decodeAt b₂.length (0 + b₁.length) b₂
      = some (offsetLayout b₁.length xs₂) := by
    rw [decodeAt_offset, hd₂]; rfl
  have hall := decodeAt_append _ _ _ _ hd₁ _ _ _ hd₂'
  rw [← List.length_append] at hall
  have hlt : ∀ z ∈ xs₁, z.1 < b₁.length := fun z hz => by
    simpa using decodeAt_start_lt _ _ _ _ hd₁ z hz
  have hlen : xs₁.length = p₁.length :=
    ((resolveAll_eq_some_iff _ _ _).mp hr₁).length_eq
  refine ⟨hall, ?_, hlen, hlt⟩
  rw [resolveAll_eq_some_iff] at hr₁ hr₂ ⊢
  refine List.rel_append (hr₁.imp fun y r hy => resolveEntry_append_left _ _ y r hy)
    (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (hr₂.imp fun y r hy => ?_)))
  rw [← hlen]
  exact resolveEntry_append_right _ _ _ y r hlt hy

/-- A block of a callee region: its symbol, its bytes and the program they decode to. -/
structure CalleeBlock where
  /-- The symbol of the block. -/
  sym : String
  /-- The bytes of the block. -/
  bytes : List (BitVec 8)
  /-- The program of the block. -/
  code : List RInstr

/-- The program of a region: the program of each block with its targets raised by the
    instruction count of the blocks before it. -/
def regionProg : List CalleeBlock → List RInstr
  | [] => []
  | e :: es => e.code ++ shiftProg e.code.length (regionProg es)

/-- The byte offset of the block of a symbol: the first block with that symbol, and the last
    block for a symbol that no earlier block has. -/
def regionOffset : List CalleeBlock → String → Nat
  | [], _ => 0
  | [_], _ => 0
  | e :: e' :: es, f => if e.sym = f then 0 else e.bytes.length + regionOffset (e' :: es) f

/-- The instruction index of the block of a symbol, as `regionOffset`. -/
def regionIndex : List CalleeBlock → String → Nat
  | [], _ => 0
  | [_], _ => 0
  | e :: e' :: es, f => if e.sym = f then 0 else e.code.length + regionIndex (e' :: es) f

/-- The program of the block of a symbol, as `regionOffset`. -/
def regionCode : List CalleeBlock → String → List RInstr
  | [], _ => []
  | [e], _ => e.code
  | e :: e' :: es, f => if e.sym = f then e.code else regionCode (e' :: es) f

/-- **The blocks of a region.** Let each block of a nonempty list decode to its program, have
    bytes and no `call`. The concatenation of the blocks is a region with the blocks of
    `regionCode` at the offsets `regionOffset` and the indices `regionIndex` in the program
    `regionProg`. At one block this is `regionBlocks_one`. -/
theorem regionBlocks_of_decodes (fs : List String) : ∀ (es : List CalleeBlock), es ≠ [] →
    (∀ e ∈ es, decodeLprog e.bytes = some e.code) → (∀ e ∈ es, e.bytes ≠ []) →
    (∀ e ∈ es, ∀ tg, RInstr.call tg ∉ e.code) →
    RegionBlocks (es.flatMap (·.bytes)) fs (regionOffset es) (regionIndex es) (regionCode es)
      (regionProg es)
  | [], hne, _, _, _ => absurd rfl hne
  | [e], _, hdec, hnb, hq => by
    have h := regionBlocks_one e.bytes e.code fs (hdec e (by simp)) (hnb e (by simp))
      (hq e (by simp))
    have hb : [e].flatMap (·.bytes) = e.bytes := by simp
    have hp : regionProg [e] = e.code := by simp [regionProg, shiftProg]
    rw [hb, hp]
    exact h
  | e :: e' :: es, _, hdec, hnb, hq => by
    have ih := regionBlocks_of_decodes fs (e' :: es) (by simp)
      (fun x hx => hdec x (List.mem_cons_of_mem _ hx))
      (fun x hx => hnb x (List.mem_cons_of_mem _ hx))
      (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have hdecE := hdec e (by simp)
    have hneE := hnb e (by simp)
    generalize hR : (e' :: es).flatMap (·.bytes) = R at ih
    obtain ⟨xs₂, hd, hr, hidx⟩ := ih.decode
    obtain ⟨xs₁, hd₁, hr₁⟩ := Option.bind_eq_some_iff.mp hdecE
    obtain ⟨hall, hres, hlen, hlt⟩ := decodeLprog_append_streams hd₁ hr₁ hd hr
    have hfm : ((e :: e' :: es).flatMap (·.bytes)) = e.bytes ++ R := by
      rw [← hR]; simp
    rw [hfm]
    refine ⟨⟨_, hall, hres, fun f hf => ?_⟩, fun f hf => ?_, fun f hf => ?_⟩
    · by_cases hs : e.sym = f
      · obtain ⟨h, x, tl, hxs⟩ := decodeAt_head_start _ 0 _ _ (by simp [hneE]) hall
        rw [hxs]
        simp [regionOffset, regionIndex, hs, List.findIdx?_cons]
      · have hi := findIdx?_offset_append xs₁ xs₂ e.bytes.length
          (regionOffset (e' :: es) f) _ _ hlt rfl (hidx f hf)
        have hp : (fun z : Nat × Nat × DInstr =>
            decide ((z.1 : Int)
              = ((e.bytes.length + regionOffset (e' :: es) f : Nat) : Int)))
            = fun z => decide (z.1 = e.bytes.length + regionOffset (e' :: es) f) := by
          funext z
          simp only [Int.natCast_inj]
        rw [hp, hlen] at hi
        simpa [regionOffset, regionIndex, hs] using hi
    · by_cases hs : e.sym = f
      · refine ⟨[], shiftProg e.code.length (regionProg (e' :: es)), ?_, ?_⟩
        · simp [regionProg, regionCode, hs, shiftProg_zero]
        · simp [regionIndex, hs]
      · obtain ⟨A, B, hQ', hA⟩ := ih.block f hf
        refine ⟨e.code ++ shiftProg e.code.length A, shiftProg e.code.length B, ?_, ?_⟩
        · rw [show regionProg (e :: e' :: es)
            = e.code ++ shiftProg e.code.length (regionProg (e' :: es)) from rfl, hQ']
          simp only [regionCode, hs, ite_false, shiftProg_append, shiftProg_shiftProg,
            List.length_append, shiftProg_length, List.append_assoc, Nat.add_comm]
        · simp [regionIndex, hs, hA]
    · by_cases hs : e.sym = f
      · simpa [regionCode, hs] using hq e (by simp)
      · simpa [regionCode, hs] using ih.callFree f hf

/-! ## 5. The relocating function encoder in front of its callee -/

/-- **Decoding of a relocated function followed by its callee.** Let `body` save no
    register by `push`, have a nonzero frame below `2 ^ 31`, and consist of remote calls
    and instructions with list-valued shapes. Let its item list satisfy `branchOKReloc` at
    its own instruction count and byte length and denote `prog`, and let the nonempty
    stream `cb` decode to `q`. Then `encodeLfundefBytesReloc symBase body ++ cb` decodes to
    `prog` followed by `q` with its targets raised by `prog.length`, and each remote call
    of `body` is `call prog.length` in `prog`. -/
theorem decodeLprog_fundefRelocL_append (symBase : String → Option Int) (body : Lcmd)
    (shs : List DShape) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hF : frameSize body < 2 ^ 31)
    (hsh : List.Forall₂
      (fun instr sh => RelocDShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsRelocL symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsRelocL symBase (Params.ofBody body) body shs) = true)
    (hP : expectedReloc (fundefItemsRelocL symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsRelocL symBase (Params.ofBody body) body shs) = some prog) :
    prog.length = decCount (fundefItemsRelocL symBase (Params.ofBody body) body shs) ∧
      decodeLprog (encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ shiftProg prog.length q) := by
  have hbytes := encodeLfundefBytesReloc_eq_itemBytesL symBase body shs hsaves hsh
  rw [hbytes] at hbr hP ⊢
  exact decodeLprog_items_linked _
    (fundefItemsRelocL_ok symBase (Params.ofBody body) body shs hF0 hF hsh) cb q prog hcb hne
    hbr hP

/-- `decodeLprog_fundefRelocL_append` at single shapes. -/
theorem decodeLprog_fundefReloc_append (symBase : String → Option Int) (body : Lcmd)
    (shs : List Shape) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hF : frameSize body < 2 ^ 31)
    (hsh : List.Forall₂
      (fun instr sh => RelocShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = true)
    (hP : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = some prog) :
    prog.length = decCount (fundefItemsReloc symBase (Params.ofBody body) body shs) ∧
      decodeLprog (encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ shiftProg prog.length q) :=
  decodeLprog_fundefRelocL_append symBase body _ cb q prog hsaves hF0 hF
    (relocDShapeOK_forall₂_one _ hsh) hcb hne hbr hP

/-! ## 6. The run of the linked bytes -/

/-- **A caller linked with its callee, over bytes.** Under the hypotheses of
    `decodeLprog_fundefRelocL_append`, with `q` a block without `call`, a run of the
    decoded caller `prog` from index `0` under the oracle of the leaky runs of `q` at the
    target `prog.length` is a run through calls of the program the linked bytes decode
    to. -/
theorem haltsC_fundefReloc_linked (r : DoitRegime) (symBase : String → Option Int)
    (body : Lcmd) (shs : List DShape) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hF : frameSize body < 2 ^ 31)
    (hsh : List.Forall₂
      (fun instr sh => RelocDShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsRelocL symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsRelocL symBase (Params.ofBody body) body shs) = true)
    (hP : expectedReloc (fundefItemsRelocL symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsRelocL symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsRelocL symBase (Params.ofBody body) body shs) = some prog)
    (hq : ∀ tg, RInstr.call tg ∉ q) {s s' : AState}
    (h : HaltsO aMachine (oracleAt prog.length (runOf r q)) prog 0 s s') :
    ∃ linked, decodeLprog (encodeLfundefBytesReloc symBase body ++ cb) = some linked ∧
      HaltsC aMachine linked 0 s s' :=
  ⟨_, (decodeLprog_fundefRelocL_append symBase body shs cb q prog hsaves hF0 hF hsh hcb hne
      hbr hP).2, haltsC_append_of_haltsO_runOf r prog q hq h⟩

/-! ## 7. The decoded program of a relocated body, instruction by instruction -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (aMachine_step_op)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI stepA_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (labelAt isLabelB condPol)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-- The program of two item lists, one after the other, under a target map. -/
theorem expectedRelocMap_append (all : List Item) (tgt : Item → Option (Nat × Nat)) :
    ∀ (xs ys : List Item), expectedRelocMap all tgt (xs ++ ys)
      = (expectedRelocMap all tgt xs).bind
          fun a => (expectedRelocMap all tgt ys).map (a ++ ·) := by
  intro xs
  induction xs with
  | nil => intro ys; cases h : expectedRelocMap all tgt ys <;> simp [expectedRelocMap, h]
  | cons it xs ih =>
    intro ys
    rw [List.cons_append, expectedRelocMap, expectedRelocMap]
    split
    · exact ih ys
    · rw [ih ys]; cases expectedRelocMap all tgt xs <;> cases expectedRelocMap all tgt ys <;> simp
    · rw [ih ys]; cases expectedRelocMap all tgt xs <;> cases expectedRelocMap all tgt ys <;> simp
    · rw [ih ys]; cases expectedRelocMap all tgt xs <;> cases expectedRelocMap all tgt ys <;> simp
    · rw [ih ys]; cases expectedRelocMap all tgt xs <;> cases expectedRelocMap all tgt ys <;> simp
    all_goals
      split
      · rw [ih ys]; cases expectedRelocMap all tgt xs <;> cases expectedRelocMap all tgt ys <;> simp
      · rfl

/-- The program of two item lists, one after the other, in front of a callee block. -/
theorem expectedReloc_append (all : List Item) (k L : Nat) :
    ∀ (xs ys : List Item), expectedReloc all k L (xs ++ ys)
      = (expectedReloc all k L xs).bind fun a => (expectedReloc all k L ys).map (a ++ ·) :=
  expectedRelocMap_append all _

/-- The target of a call item under two target maps that agree on it. -/
theorem callTgtMap_congr (all : List Item) {tgt tgt' : Item → Option (Nat × Nat)}
    (it : Item) (h : it.target = none → tgt it = tgt' it) :
    callTgtMap all tgt it = callTgtMap all tgt' it := by
  unfold callTgtMap
  cases ht : it.target with
  | none => exact h ht
  | some l => rfl

/-- **The program of an item list depends on the target map only at its calls without
    target label.** -/
theorem expectedRelocMap_congr (all : List Item) {tgt tgt' : Item → Option (Nat × Nat)} :
    ∀ xs : List Item,
      (∀ it ∈ xs, it.target = none → ∀ d, it.dec = some (.call d) → tgt it = tgt' it) →
      expectedRelocMap all tgt xs = expectedRelocMap all tgt' xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons it xs ih =>
    intro h
    have ih' := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    rw [expectedRelocMap, expectedRelocMap, ih']
    cases hd : it.dec with
    | none => rfl
    | some x =>
      cases x with
      | call d =>
        simp only
        rw [callTgtMap_congr all it fun ht => h it List.mem_cons_self ht d hd]
      | _ => rfl

/-- **The branch condition of an item list depends on the target map only at its calls
    without target label.** -/
theorem branchOKRelocMap_congr (all : List Item) {tgt tgt' : Item → Option (Nat × Nat)} :
    ∀ xs : List Item,
      (∀ it ∈ xs, it.target = none → ∀ d, it.dec = some (.call d) → tgt it = tgt' it) →
      ∀ off, branchOKRelocMap all tgt off xs = branchOKRelocMap all tgt' off xs := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons it xs ih =>
    intro h off
    have ih' := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    rw [branchOKRelocMap, branchOKRelocMap, ih']
    cases hd : it.dec with
    | none => rfl
    | some x =>
      cases x with
      | call d =>
        simp only
        rw [callTgtMap_congr all it fun ht => h it List.mem_cons_self ht d hd]
      | _ => rfl

/-- The program of an item list under a target map has one instruction for each item that
    decodes. -/
theorem expectedRelocMap_length (all : List Item) (tgt : Item → Option (Nat × Nat)) :
    ∀ (xs : List Item) (A : List RInstr), expectedRelocMap all tgt xs = some A →
      A.length = decCount xs := by
  intro xs
  induction xs with
  | nil =>
    intro A h
    obtain rfl := Option.some.inj h
    rfl
  | cons it xs ih =>
    intro A h
    rw [expectedRelocMap] at h
    split at h
    · rename_i hd
      rw [decCount, hd, ih A h]
      simp
    all_goals
      rename_i hd
      first
        | (obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h
           rw [decCount, hd, List.length_cons, ih A' hA']
           simp [Nat.add_comm])
        | (split at h
           · obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h
             rw [decCount, hd, List.length_cons, ih A' hA']
             simp [Nat.add_comm]
           · cases h)

/-- The program of an item list has one instruction for each item that decodes. -/
theorem expectedReloc_length (all : List Item) (k L : Nat) :
    ∀ (xs : List Item) (A : List RInstr), expectedReloc all k L xs = some A →
      A.length = decCount xs :=
  expectedRelocMap_length all _

/-- **The program around a run of items, under a target map.** The program of
    `xs ++ (ms ++ ys)` is the program of `xs`, of length `decCount xs`, the program of
    `ms`, and the program of `ys`. -/
theorem expectedRelocMap_mid (all : List Item) (tgt : Item → Option (Nat × Nat))
    (xs ms ys : List Item) (prog : List RInstr)
    (h : expectedRelocMap all tgt (xs ++ (ms ++ ys)) = some prog) :
    ∃ A X B, expectedRelocMap all tgt ms = some X ∧ expectedRelocMap all tgt ys = some B
      ∧ prog = A ++ X ++ B ∧ A.length = decCount xs := by
  rw [expectedRelocMap_append, Option.bind_eq_some_iff] at h
  obtain ⟨A, hA, h⟩ := h
  obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [expectedRelocMap_append, Option.bind_eq_some_iff] at hR
  obtain ⟨X, hX, hR⟩ := hR
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp hR
  exact ⟨A, X, B, hX, hB, by rw [List.append_assoc], expectedRelocMap_length all tgt xs A hA⟩

/-- **The program around a run of items.** The program of `xs ++ (ms ++ ys)` is the program
    of `xs`, of length `decCount xs`, the program of `ms`, and the program of `ys`. -/
theorem expectedReloc_mid (all : List Item) (k L : Nat) (xs ms ys : List Item)
    (prog : List RInstr) (h : expectedReloc all k L (xs ++ (ms ++ ys)) = some prog) :
    ∃ A X B, expectedReloc all k L ms = some X ∧ expectedReloc all k L ys = some B
      ∧ prog = A ++ X ++ B ∧ A.length = decCount xs :=
  expectedRelocMap_mid all _ xs ms ys prog h

/-- The shapes of a body are the shapes `shapeOf` of its instructions, instruction by
    instruction. -/
theorem shapesOf_forall₂_shapeOf (P : Params) :
    ∀ (b : Lcmd) (ds : List DShape), shapesOf P b = some ds →
      List.Forall₂ (fun i sh => shapeOf P i.li_i = some sh) b ds := by
  intro b
  induction b with
  | nil =>
    intro ds h
    simp only [shapesOf, Option.some.injEq] at h
    subst h
    exact .nil
  | cons i b ih =>
    intro ds h
    simp only [shapesOf] at h
    split at h
    · rename_i sh s' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      exact .cons h1 (ih s' h2)
    · cases h

/-- The shapes of a body are single shapes `ss`, instruction by instruction. -/
theorem shapesOf_one_forall₂ (P : Params) (b : Lcmd) (ss : List Shape)
    (h : shapesOf P b = some (ss.map DShape.one)) :
    List.Forall₂ (fun i sh => shapeOf P i.li_i = some (DShape.one sh)) b ss := by
  have h₂ := shapesOf_forall₂_shapeOf P b _ h
  rwa [List.forall₂_map_right_iff] at h₂

/-- The computed shapes of a body meet the shape condition of the relocating encoder. -/
theorem relocDShapeOK_of_shapes (P : Params) {b : Lcmd} {ds : List DShape}
    (h : shapesOf P b = some ds) :
    List.Forall₂ (fun i sh => RelocDShapeOK P i.li_i sh) b ds := by
  refine (shapesOf_forall₂_shapeOf P b ds h).imp fun i sh hs => ?_
  unfold RelocDShapeOK
  cases hr : remoteSym i.li_i with
  | none => exact shapeOf_ok P _ _ hs
  | some f =>
    revert hs hr
    cases i.li_i with
    | Lcall ra tg =>
      obtain ⟨f', l⟩ := tg
      intro _ hr
      simp only [remoteSym] at hr
      split at hr
      · cases hr
      · obtain rfl := Option.some.inj hr
        exact ⟨ra, l, rfl⟩
    | Lgoto tg => intro hs; simp [shapeOf] at hs
    | _ => intro _ hr; simp [remoteSym] at hr

/-- The single shapes of a body meet the shape condition of the relocating encoder. -/
theorem relocShapeOK_of_shapes (P : Params) {b : Lcmd} {ss : List Shape}
    (h : shapesOf P b = some (ss.map DShape.one)) :
    List.Forall₂ (fun i sh => RelocShapeOK P i.li_i sh) b ss :=
  (List.forall₂_map_right_iff.mp (relocDShapeOK_of_shapes P h)).imp
    fun _ _ hs => (relocShapeOK_iff P _ _).mpr hs

/-- The item list of a body splits at every position. -/
theorem itemsFromReloc_split (symBase : String → Option Int) (P : Params) :
    ∀ (n : Nat) (b : Lcmd) (ss : List DShape) (off : Nat), ∃ off',
      itemsFromReloc symBase P off b ss
        = itemsFromReloc symBase P off (b.take n) (ss.take n)
          ++ itemsFromReloc symBase P off' (b.drop n) (ss.drop n) := by
  intro n
  induction n with
  | zero => intro b ss off; exact ⟨off, by simp [itemsFromReloc]⟩
  | succ n ih =>
    intro b ss off
    cases b with
    | nil => exact ⟨off, by simp [itemsFromReloc]⟩
    | cons i b =>
      cases ss with
      | nil => exact ⟨off, by simp [itemsFromReloc]⟩
      | cons s ss =>
        cases hr : remoteSym i.li_i with
        | none =>
          obtain ⟨off', h⟩ := ih b ss (off + P.lenAt off i.li_i)
          exact ⟨off', by simp only [List.take_succ_cons, List.drop_succ_cons, itemsFromReloc, hr,
            List.append_assoc, h]⟩
        | some f =>
          obtain ⟨off', h⟩ := ih b ss (off + 5)
          exact ⟨off', by simp only [List.take_succ_cons, List.drop_succ_cons, itemsFromReloc, hr,
            List.cons_append, h]⟩

/-- The number of decoded instructions of the item list of a body with computed shapes. -/
theorem decCount_itemsFromReloc (symBase : String → Option Int) (P : Params) {b : Lcmd}
    {ss : List DShape}
    (h : List.Forall₂ (fun i sh => shapeOf P i.li_i = some sh) b ss) :
    ∀ off, decCount (itemsFromReloc symBase P off b ss) = (ss.map nOf).sum := by
  induction h with
  | nil => intro off; rfl
  | @cons i sh _ _ hab _ ih =>
    intro off
    cases hr : remoteSym i.li_i with
    | none =>
      simp only [itemsFromReloc, hr, decCount_append, decCount_dItems, ih, List.map_cons,
        List.sum_cons]
    | some f =>
      simp only [itemsFromReloc, hr, decCount, ih, List.map_cons, List.sum_cons]
      revert hab hr
      cases i.li_i with
      | Lcall ra tg =>
        obtain ⟨f', l⟩ := tg
        intro hab _
        simp only [shapeOf, Option.some.injEq] at hab
        subst hab
        simp [nOf]
      | _ => simp [remoteSym, shapeOf]

/-- No item of a body without a definition of the label `l` defines `l`. -/
theorem itemsFromReloc_noLabel (symBase : String → Option Int) (P : Params) (l : LLabel) :
    ∀ (b : Lcmd) (ss : List DShape) (off : Nat), (∀ i ∈ b, isLabelB l i.li_i = false) →
      ∀ it ∈ itemsFromReloc symBase P off b ss, it.label ≠ some l := by
  intro b
  induction b with
  | nil => intro ss off _ it hit; simp [itemsFromReloc] at hit
  | cons i b ih =>
    intro ss off hb it hit
    cases ss with
    | nil => simp [itemsFromReloc] at hit
    | cons s ss =>
      cases hr : remoteSym i.li_i with
      | none =>
        simp only [itemsFromReloc, hr, List.mem_append] at hit
        rcases hit with hit | hit
        · rcases dItems_label P off i s it hit with h | h
          · rw [h]; simp
          · rw [h]
            intro he
            have := (isLabelB_iff l i.li_i).mpr he
            rw [hb i (by simp)] at this
            cases this
        · exact ih ss _ (fun j hj => hb j (by simp [hj])) it hit
      | some f =>
        simp only [itemsFromReloc, hr, List.mem_cons] at hit
        rcases hit with rfl | hit
        · simp
        · exact ih ss _ (fun j hj => hb j (by simp [hj])) it hit

/-- A call item without target label of the item list of a body carries a callee symbol,
    the symbol of a remote transfer of the body. -/
theorem itemsFromReloc_sym (symBase : String → Option Int) (P : Params) :
    ∀ (b : Lcmd) (ss : List DShape) (off : Nat), ∀ it ∈ itemsFromReloc symBase P off b ss,
      it.target = none → ∀ d, it.dec = some (.call d) →
        ∃ f, it.sym = some f ∧ ∃ i ∈ b, remoteSym i.li_i = some f := by
  intro b
  induction b with
  | nil => intro ss off it hit; simp [itemsFromReloc] at hit
  | cons i b ih =>
    intro ss off it hit ht d hd
    cases ss with
    | nil => simp [itemsFromReloc] at hit
    | cons s ss =>
      cases hr : remoteSym i.li_i with
      | none =>
        simp only [itemsFromReloc, hr, List.mem_append] at hit
        rcases hit with hit | hit
        · cases s with
          | one sh =>
            simp only [dItems, List.mem_singleton] at hit
            subst hit
            cases sh <;> simp_all [Shape.target, Shape.dec]
          | ops pcs =>
            simp only [dItems, List.mem_map] at hit
            obtain ⟨p, -, rfl⟩ := hit
            simp at hd
        · obtain ⟨f, hf, j, hj, hjr⟩ := ih ss _ it hit ht d hd
          exact ⟨f, hf, j, List.mem_cons_of_mem _ hj, hjr⟩
      | some f =>
        simp only [itemsFromReloc, hr, List.mem_cons] at hit
        rcases hit with rfl | hit
        · exact ⟨f, rfl, i, List.mem_cons_self, hr⟩
        · obtain ⟨f, hf, j, hj, hjr⟩ := ih ss _ it hit ht d hd
          exact ⟨f, hf, j, List.mem_cons_of_mem _ hj, hjr⟩

/-- **A call item without target label of the relocated item list of a function carries a
    callee symbol**, the symbol of a remote transfer of the body. -/
theorem fundefItemsRelocL_sym (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (ds : List DShape) :
    ∀ it ∈ fundefItemsRelocL symBase P body ds, it.target = none →
      ∀ d, it.dec = some (.call d) →
        ∃ f, it.sym = some f ∧ ∃ i ∈ body, remoteSym i.li_i = some f := by
  intro it hit ht d hd
  simp only [fundefItemsRelocL, List.mem_cons, List.mem_append] at hit
  rcases hit with rfl | hit | rfl | hit
  · simp [mkLea] at hd
  · exact itemsFromReloc_sym symBase P body ds 0 it hit ht d hd
  · simp [mkLea] at hd
  · simp only [List.not_mem_nil, or_false] at hit
    subst hit
    simp [mkRet] at hd

/-- **A label resolves, in the relocated item list, to the decoded index of its first
    definition.** -/
theorem labelPos_fundefItemsReloc (symBase : String → Option Int) {body : Lcmd}
    {ds : List DShape}
    (hs : shapesOf (Params.ofBody body) body = some ds) {l : LLabel} {p : Nat}
    (hp : labelAt body l = some p) :
    ∃ off, labelPos l 0 0 (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      = some (posOf ds p, off) := by
  have hR := shapesOf_forall₂_shapeOf _ body ds hs
  obtain ⟨hpl, hlab, hbefore⟩ := labelAt_spec hp
  have hlab' := (isLabelB_iff l _).mp hlab
  have hlen : body.length = ds.length := hR.length_eq
  have hskip : ds[p]'(by omega) = .one .skip := by
    have hsp := (shapesOf_spec _ body ds hs).2 p hpl (by omega)
    cases hb : body[p].li_i <;> rw [hb] at hsp hlab' <;> simp [shapeOf, labelOf] at hsp hlab'
    exact hsp.symm
  obtain ⟨off', hsplit⟩ := itemsFromReloc_split symBase (Params.ofBody body) p body ds 0
  have hpre : ∀ i ∈ body.take p, isLabelB l i.li_i = false := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hi
    simp only [List.length_take] at hq
    simpa using hbefore q (by omega)
  have hrem : remoteSym body[p].li_i = none := by
    revert hlab'
    cases body[p].li_i <;> simp [labelOf, remoteSym]
  rw [List.drop_eq_getElem_cons hpl, List.drop_eq_getElem_cons (by omega : p < ds.length),
    hskip] at hsplit
  unfold fundefItemsRelocL
  rw [hsplit]
  simp only [labelPos, mkLea, reduceCtorEq, ite_false, Option.isSome_some, ite_true]
  rw [List.append_assoc, labelPos_append_of_ne _ _ _
    (itemsFromReloc_noLabel symBase _ l _ _ _ hpre),
    decCount_itemsFromReloc symBase _ (List.forall₂_take p hR)]
  simp only [itemsFromReloc, hrem, dItems, List.cons_append, labelPos, hlab', ite_true]
  simp only [posOf, Option.some.injEq, Prod.mk.injEq]
  exact ⟨_, trivial, rfl⟩

/-- The instructions whose decoded block a program with the map `LinkedProgMap` holds, read off
    their shape: an `Lopn`, a label, and a conditional branch on a register condition to a label
    the body defines. Each instruction of the wide class `DecodePrintedAddrW.instrOKWB` has this
    shape. -/
def blkOK (body : Lcmd) : LinstrR → Prop
  | .Lopn _ _ _ => True
  | .Llabel _ _ => True
  | .Lcond (.reg _) l => (labelAt body l).isSome = true
  | _ => False

/-- The facts of a printed body that the map of its decoded program reads, for each class of
    instructions: the list-valued shapes `ds` and the closing return. -/
structure LinkFacts (body : Lcmd) (ds : List DShape) : Prop where
  /-- The shapes of the body are `ds`. -/
  shapes : shapesOf (Params.ofBody body) body = some ds
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret

/-- The decoded program `prog` of a body with shapes `ds` in front of callee blocks whose
    entries have the indices `K : String → Nat`: around an instruction of the shape `blkOK`,
    `prog` holds its decoded instructions `DecodePrintedCFG.blkOf` from the index
    `DecodePrintedCFG.posOf`; the index of a remote transfer to the symbol `f` holds
    `call (K f)`; and the index of the closing return holds the closing `lea` of the frame
    `F`, followed by `ret`. -/
structure LinkedProgMap (body : Lcmd) (ds : List DShape) (K : String → Nat) (F : Nat)
    (prog : List RInstr) : Prop where
  /-- The decoded instructions of an instruction of the shape `blkOK`. -/
  blk : ∀ k (hk : k < body.length) (hs : k < ds.length),
    blkOK body body[k].li_i →
    ∃ A B, prog = A ++ blkOf body ds ds[k] ++ B ∧ A.length = posOf ds k
  /-- The index of a remote transfer to the symbol `f`. -/
  call : ∀ k (hk : k < body.length) (f : String), remoteSym body[k].li_i = some f →
    prog[posOf ds k]? = some (.call (K f))
  /-- The closing `lea` and `ret`. -/
  fin : prog[posOf ds (body.length - 1)]? = some (.op (leaFrame (Int.ofNat F)))
    ∧ prog[posOf ds (body.length - 1) + 1]? = some .ret

/-- `LinkedProgMap` in front of one callee block at index `K`: every remote transfer holds
    `call K`. -/
abbrev LinkedProg (body : Lcmd) (ds : List DShape) (K F : Nat) (prog : List RInstr) : Prop :=
  LinkedProgMap body ds (fun _ => K) F prog

/-- **The decoded program of a relocated body, under a target map.** For a body with the
    facts `LinkFacts`, the program its relocated item list denotes under a target map `tgt`
    that gives each call without target label to the symbol `f` an index `K f` satisfies
    `LinkedProgMap` at `K`. -/
theorem linkedProg_of_itemsMapL (symBase : String → Option Int) {body : Lcmd}
    {ds : List DShape} (hF : LinkFacts body ds) (tgt : Item → Option (Nat × Nat))
    (K : String → Nat)
    (hK : ∀ it f j t, it.target = none → it.sym = some f → tgt it = some (j, t) → j = K f)
    (prog : List RInstr)
    (hP : expectedRelocMap (fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog) :
    LinkedProgMap body ds K (Params.ofBody body).frame prog := by
  have hR := shapesOf_forall₂_shapeOf _ body _ hF.shapes
  have hlen : body.length = ds.length := hR.length_eq
  have hshk : ∀ k (hk : k < body.length) (hs : k < ds.length),
      shapeOf (Params.ofBody body) body[k].li_i = some ds[k] :=
    (shapesOf_spec _ body _ hF.shapes).2
  -- the program around position `k`
  have hpos : ∀ k (hk : k < body.length) (hs : k < ds.length), ∃ off A X B,
      expectedRelocMap (fundefItemsRelocL symBase (Params.ofBody body) body ds)
          tgt (itemsFromReloc symBase (Params.ofBody body) off [body[k]] [ds[k]])
          = some X
        ∧ prog = A ++ X ++ B ∧ A.length = posOf ds k := by
    intro k hk hs
    obtain ⟨off, hsplit⟩ := itemsFromReloc_split symBase (Params.ofBody body) k body ds 0
    rw [List.drop_eq_getElem_cons hk, List.drop_eq_getElem_cons hs] at hsplit
    obtain ⟨off2, h1⟩ := itemsFromReloc_split symBase (Params.ofBody body) 1
      (body[k] :: body.drop (k + 1)) (ds[k] :: ds.drop (k + 1)) off
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      at h1
    have hP' : expectedRelocMap
        (fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt
        ((mkLea (-(Int.ofNat (Params.ofBody body).frame))
            :: itemsFromReloc symBase (Params.ofBody body) 0 (body.take k) (ds.take k))
          ++ (itemsFromReloc symBase (Params.ofBody body) off [body[k]] [ds[k]]
            ++ (itemsFromReloc symBase (Params.ofBody body) off2 (body.drop (k + 1))
                (ds.drop (k + 1))
              ++ [mkLea (Int.ofNat (Params.ofBody body).frame), mkRet]))) = some prog := by
      rw [← hP]
      congr 1
      rw [fundefItemsRelocL, hsplit, h1]
      simp only [List.cons_append, List.append_assoc]
    obtain ⟨A, X, B, hX, -, hprog, hA⟩ := expectedRelocMap_mid _ tgt _ _ _ prog hP'
    refine ⟨off, A, X, B, hX, hprog, ?_⟩
    rw [hA, decCount, decCount_itemsFromReloc symBase _ (List.forall₂_take k hR)]
    simp [posOf, mkLea]
  -- the program of a run of `op` pieces
  have hpcs : ∀ (all : List Item) (pcs : List (List (BitVec 8) × JInstr 64)),
      expectedRelocMap all tgt
          (pcs.map fun p => ({ bytes := p.1, dec := some (.op p.2) } : Item))
        = some (pcs.map fun p => .op p.2) := by
    intro all pcs
    induction pcs with
    | nil => rfl
    | cons p pcs ih => simp [expectedRelocMap, ih]
  refine ⟨fun k hk hs hok => ?_, fun k hk f hf => ?_, ?_⟩
  · obtain ⟨off, A, X, B, hX, hprog, hA⟩ := hpos k hk hs
    have hsh := hshk k hk hs
    refine ⟨A, B, ?_, hA⟩
    rw [hprog]
    congr 2
    revert hX hsh hok
    rcases body[k] with ⟨ii, li⟩
    cases li with
    | Lopn dsts o srcs =>
      intro _ hX hsh
      rcases shapeOfBytes_ok (bs := encodeLopn _ _ (.Lopn dsts o srcs) _) hsh with
        ⟨q, he, -, -⟩ | ⟨pcs, he, -, -⟩
      · rw [he] at hX ⊢
        simp only [itemsFromReloc, remoteSym, dItems, List.append_nil, Shape.dec,
          expectedRelocMap, Option.map_some, Option.some.injEq] at hX
        rw [← hX]
        simp [blkOf, DShape.ops']
      · rw [he] at hX ⊢
        simp only [itemsFromReloc, remoteSym, dItems, List.append_nil, hpcs,
          Option.some.injEq] at hX
        rw [← hX]
        simp [blkOf, DShape.ops']
    | Llabel kd l =>
      intro _ hX hsh
      simp only [shapeOf, Option.some.injEq] at hsh
      rw [← hsh] at hX ⊢
      simp only [itemsFromReloc, remoteSym, dItems, List.append_nil, Shape.dec,
        expectedRelocMap, Option.some.injEq] at hX
      rw [← hX]
      simp [blkOf, DShape.ops']
    | Lcond c l =>
      cases c with
      | reg cc =>
        intro hok hX hsh
        simp only [blkOK, Option.isSome_iff_exists] at hok
        obtain ⟨p, hp⟩ := hok
        obtain ⟨o, ho⟩ := labelPos_fundefItemsReloc symBase hF.shapes hp
        simp only [shapeOf, Option.some.injEq] at hsh
        rw [← hsh] at hX ⊢
        simp only [itemsFromReloc, remoteSym, dItems, List.append_nil, Shape.dec, Shape.target,
          expectedRelocMap, Option.bind_some, ho, Option.map_some, Option.some.injEq] at hX
        rw [← hX]
        simp [blkOf, hp]
      | _ => intro hok; simp [blkOK] at hok
    | _ => intro hok; simp [blkOK] at hok
  · have hs' : k < ds.length := by omega
    obtain ⟨off, A, X, B, hX, hprog, hA⟩ := hpos k hk hs'
    simp only [itemsFromReloc, hf, expectedRelocMap, callTgtMap] at hX
    split at hX
    · rename_i j t htg
      rw [hK _ f j t rfl rfl htg] at hX
      simp only [Option.map_some, Option.some.injEq] at hX
      rw [hprog, ← hX, ← hA]
      simp
    · cases hX
  · have hn : body.length - 1 < ds.length := by have := hF.pos; omega
    have hP' : expectedRelocMap
        (fundefItemsRelocL symBase (Params.ofBody body) body ds) tgt
        ((mkLea (-(Int.ofNat (Params.ofBody body).frame))
            :: itemsFromReloc symBase (Params.ofBody body) 0 body ds)
          ++ ([mkLea (Int.ofNat (Params.ofBody body).frame)] ++ [mkRet])) = some prog := by
      rw [← hP]
      rfl
    obtain ⟨A, X, B, hX, hB, hprog, hA⟩ := expectedRelocMap_mid _ tgt _ _ _ prog hP'
    have hlast : nOf (ds[body.length - 1]'hn) = 0 := by
      have h1 := hshk (body.length - 1) (by have := hF.pos; omega) hn
      rw [hF.last] at h1
      simp only [shapeOf, Option.some.injEq] at h1
      rw [← h1]
      rfl
    have hposL : posOf ds (body.length - 1) = A.length := by
      have h2 : posOf ds body.length = posOf ds (body.length - 1) := by
        have h := posOf_succ ds (body.length - 1) hn
        have e : body.length - 1 + 1 = body.length := by have := hF.pos; omega
        rw [hlast, e] at h
        exact h
      rw [← h2, hA, decCount, decCount_itemsFromReloc symBase _ hR]
      rw [posOf, List.take_of_length_le (by omega)]
      simp [mkLea]
    simp only [expectedRelocMap, mkLea, mkRet, Option.map_some, Option.some.injEq] at hX hB
    rw [hposL, hprog, ← hX, ← hB]
    simp [leaFrame]

/-! ## 8. The byte simulation of the steps of a relocated body -/

/-- A path of the machine followed by a run under an oracle is a run under the oracle. -/
theorem haltsO_of_reaches {σ : Type} {M : Machine σ} {O : Nat → σ → σ → Prop}
    {prog : List RInstr} {pc pc' : Nat} {s s' s'' : σ} (h : Reaches M prog pc s pc' s')
    (hr : HaltsO M O prog pc' s' s'') : HaltsO M O prog pc s s'' := by
  induction h with
  | refl => exact hr
  | next hs _ ih => exact .go hs (ih hr)

/-- **The closing return of a relocated body, on the decoded program**: from the index of
    the last position, `prog` runs the closing `lea` of the frame and halts at `ret`. -/
theorem linked_halt {body : Lcmd} {ds : List DShape} {K : String → Nat}
    {prog : List RInstr}
    (hL : LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (O : Nat → AState → AState → Prop) (sa : LstateA) (sA : AState)
    (hend : sa.reg.lpc + 1 = body.length) :
    HaltsO aMachine O prog (posOf ds sa.reg.lpc) sA
      (evalInstrA sA (leaFrame (Int.ofNat (Params.ofBody body).frame))) := by
  have e : sa.reg.lpc = body.length - 1 := by omega
  rw [e]
  exact .go (aMachine_step_op prog _ sA _ hL.fin.1) (.ret hL.fin.2)

/-- **A remote call of a relocated body, on the decoded program**: the index of a remote call
    to the symbol `t.1` holds `call (K t.1)`, and the index of the next position is the next
    index. -/
theorem linked_callL {body : Lcmd} {ds : List DShape} (hF : LinkFacts body ds)
    {K : String → Nat} {prog : List RInstr}
    (hL : LinkedProgMap body ds K (Params.ofBody body).frame prog)
    (p : Nat) (bi : Linstr) (ra : Option String) (t : String × LLabel)
    (hb : body[p]? = some bi) (hbi : bi.li_i = .Lcall ra t)
    (hrem : remoteSym bi.li_i ≠ none) :
    prog[posOf ds p]? = some (.call (K t.1)) ∧ posOf ds (p + 1) = posOf ds p + 1 := by
  obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body _ hF.shapes
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hrem
  have hft : f = t.1 := by
    have hf' := hf
    rw [hbi] at hf'
    obtain ⟨f', l⟩ := t
    simp only [remoteSym] at hf'
    split at hf' <;> simp_all
  refine ⟨hft ▸ hL.call p hk f (by rw [hbk]; exact hf), ?_⟩
  have h1 := hsh p hk (by omega)
  rw [hbk, hbi] at h1
  obtain ⟨f, l⟩ := t
  simp only [shapeOf, Option.some.injEq] at h1
  rw [posOf_succ _ p (by omega), ← h1]
  rfl

/-- The end of the run of a relocated body: the byte state is the state after the closing
    `lea` of the frame `F`, from a byte state that corresponds to the address state. -/
def FinLea (rsp : BitVec 64) (F : Nat) (sa : LstateA) (sA' : AState) : Prop :=
  ∃ sA, ACorr rsp sA sa ∧ sA' = evalInstrA sA (leaFrame (Int.ofNat F))

/-- The target map of a callee region placed after `n` instructions and `L` bytes: the
    symbol `f ∈ fs` goes to the index `n + k f` and the byte offset `L + o f` of the entry of
    its block, any other symbol to none. -/
def regionTgt (fs : List String) (n L : Nat) (o k : String → Nat) (f : String) :
    Option (Nat × Nat) :=
  if f ∈ fs then some (n + k f, L + o f) else none

/-- **The decoded program of a relocated body linked with a callee region.** Let the body
    have the facts `LinkFacts`, save no register by `push` and have a nonzero frame below
    `2 ^ 31`, and let the region `cb` decode to `Q` with the entry of the block of `f ∈ fs`
    at byte offset `o f` and index `k f` (`RegionDecode`). When the relocated item list
    satisfies `branchOKRelocMap` and denotes `prog` under the target map `symTgt` of
    `regionTgt`, the linked bytes decode to `prog` followed by `Q` with its targets raised by
    `prog.length`, and `prog` satisfies `LinkedProgMap` at `fun f => prog.length + k f`. -/
theorem linkedProg_of_bytesSymL (symBase : String → Option Int) {body : Lcmd}
    {ds : List DShape} (hF : LinkFacts body ds) (cb : List (BitVec 8)) (fs : List String)
    (o k : String → Nat) (Q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hFr : frameSize body < 2 ^ 31)
    (hcb : RegionDecode cb fs o k Q)
    (hbr : branchOKRelocMap (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (symTgt (regionTgt fs (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
        (encodeLfundefBytesReloc symBase body).length o k)) 0
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = true)
    (hP : expectedRelocMap (fundefItemsRelocL symBase (Params.ofBody body) body ds)
      (symTgt (regionTgt fs (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
        (encodeLfundefBytesReloc symBase body).length o k))
      (fundefItemsRelocL symBase (Params.ofBody body) body ds) = some prog) :
    decodeLprog (encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ shiftProg prog.length Q)
      ∧ LinkedProgMap body ds (fun f => prog.length + k f) (Params.ofBody body).frame prog := by
  have hsh := relocDShapeOK_of_shapes _ hF.shapes
  have hbytes := encodeLfundefBytesReloc_eq_itemBytesL symBase body ds hsaves hsh
  have hok := fundefItemsRelocL_ok symBase (Params.ofBody body) body ds hF0 hFr hsh
  obtain ⟨xs₂, hd, hr, hent⟩ := hcb
  rw [hbytes] at hbr hP ⊢
  have hentry : ∀ f j t,
      regionTgt fs (decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds))
        (itemBytes (fundefItemsRelocL symBase (Params.ofBody body) body ds)).length o k f
        = some (j, t) →
      ∃ o' k', t = (itemBytes (fundefItemsRelocL symBase (Params.ofBody body) body ds)).length
          + o' ∧ j = decCount (fundefItemsRelocL symBase (Params.ofBody body) body ds) + k'
        ∧ xs₂.findIdx? (fun z => decide (z.1 = o')) = some k' := by
    intro f j t hm
    simp only [regionTgt] at hm
    split at hm
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      exact ⟨o f, k f, hm.2.symm, hm.1.symm, hent f hf⟩
    · cases hm
  obtain ⟨hlen, hdec⟩ := decodeLprog_items_linkedSym _ hok cb xs₂ Q prog _ hd hr hentry hbr hP
  refine ⟨hdec, linkedProg_of_itemsMapL symBase hF _ _ (fun it f j t _ hs ht => ?_) prog hP⟩
  simp only [symTgt, hs, Option.bind_some, regionTgt] at ht
  split at ht
  · simp only [Option.some.injEq, Prod.mk.injEq] at ht
    omega
  · cases ht

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
