/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86BlockRoundtrip
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.CallSeg

/-!
# Byte-stream round trip for runs separated by calls

A `call rel32` (`E8 cd`) carries a displacement, not the name of its callee. A
call to a symbol outside the object carries the displacement `0`, which the linker
patches, and a relocation at the offset of its `rel32` field, which names the
callee. A call to a function of the same object carries the displacement to that
function's entry, and the object's symbol table names the function at the target.
This is the convention of `LprogBytes.encodeLcmdReloc`, whose relocation list holds
`(offset, symbol)` pairs with offsets counted from the start of the body.

`encodeCallSegs` encodes a list of `CallSeg` runs under that convention, with the
straight-line runs encoded by `encodeJBlock`, and `decodeCallSegs` reads the bytes
and the relocation list back into runs, decoding instructions with
`SailX86Decoder.decodeJ1`. The first byte `E8` of a call starts no instruction
`decodeJ1` reads, so the decoder finds the calls without a separate scan.

## Main definitions

* `callRel32`: the bytes of `call rel32`, those of `LprogBytes.encCall32`.
* `encodeCallSegs`, `decodeCallSegs`: the encoder and the decoder.
* `normSegs`: the normal form of a list of runs, in which every run but the last
  ends in a call.
* `callsFit`: every displacement to a function of the object fits `rel32`.
* `decodeFramed`: `decodeCallSegs` after dropping a prologue and an epilogue of
  known lengths and making the relocation offsets body-relative.

## Main results

* `roundtrip_callSegs`: runs of covered instructions decode back from their bytes
  and relocations, up to `normSegs` and the register resolution `renameSeg`. A
  call to a function of the object is named through a resolver `nameAt` that
  names each function at its entry; distinct entries are what make such a
  resolver exist.
* `instrs_normSegs`, `callees_normSegs`: `normSegs` keeps the instructions and the
  called symbols, so the decoded runs have the instructions and calls of the
  encoded ones. The decoder cannot see where a run whose `callee` is `none` ends,
  which is why the round trip holds up to `normSegs`.
* `decodeFramed_eq`, `roundtrip_callSegs_framed`: the same through a function's
  framing, for a prologue and an epilogue of known lengths (the push, pop, frame
  and `ret` bytes of `LprogBytes.encodeLfundefBytesReloc` around the body).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86CallSeg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported

/-! ## 1. Encoder and decoder -/

/-- `call rel32` (`E8 cd`) with displacement `d`: the bytes of
    `LprogBytes.encCall32 d`. -/
def callRel32 (d : Int) : List (BitVec 8) := BitVec.ofNat 8 0xe8 :: disp32LE d

/-- `call rel32` is five bytes. -/
theorem callRel32_length (d : Int) : (callRel32 d).length = 5 := by
  simp [callRel32, disp32LE, imm32LE]

/-- A run with its instructions resolved through the allocation. -/
def renameSeg (alloc : GpAlloc) (s : CallSeg) : CallSeg :=
  { s with body := s.body.map (renameJ alloc) }

/-- The bytes of a list of runs starting at body offset `off`, and the relocations
    of their external calls. A call to `f` with `symBase f = some δ` (`δ` the body
    offset of `f`'s entry) is resolved to the displacement from the end of the call
    to `δ`; a call to `f` with `symBase f = none` carries displacement `0` and a
    relocation `(offset of the rel32 field, f)`. -/
def encodeCallSegsFrom (alloc : GpAlloc) (symBase : String → Option Int) :
    Nat → List CallSeg → List (BitVec 8) × List (Nat × String)
  | _, [] => ([], [])
  | off, s :: ss =>
      match s.callee with
      | none =>
          let r := encodeCallSegsFrom alloc symBase
            (off + (encodeJBlock alloc s.body).length) ss
          (encodeJBlock alloc s.body ++ r.1, r.2)
      | some f =>
          let e := off + (encodeJBlock alloc s.body).length
          let r := encodeCallSegsFrom alloc symBase (e + 5) ss
          match symBase f with
          | some δ => (encodeJBlock alloc s.body ++ (callRel32 (δ - ↑(e + 5)) ++ r.1), r.2)
          | none => (encodeJBlock alloc s.body ++ (callRel32 0 ++ r.1), (e + 1, f) :: r.2)

/-- `encodeCallSegsFrom` from body offset `0`. -/
def encodeCallSegs (alloc : GpAlloc) (symBase : String → Option Int) (ss : List CallSeg) :
    List (BitVec 8) × List (Nat × String) :=
  encodeCallSegsFrom alloc symBase 0 ss

/-- The run a decoder closes at the end of the bytes: none when no instruction is
    pending. -/
def flushRun (acc : List (JInstr 64)) : List CallSeg :=
  if acc.isEmpty then [] else [⟨acc, none⟩]

/-- The callee of a call at body offset `off` with displacement `disp`, and the
    relocations left after it. The next relocation names the callee when the
    displacement is `0` and the relocation sits at the call's `rel32` field;
    otherwise `nameAt` names the function whose entry is the target,
    `off + 5 + disp`. -/
def callTarget (nameAt : Int → Option String) (off : Nat) (disp : Int) :
    List (Nat × String) → Option (String × List (Nat × String))
  | (o, f) :: rs =>
      if disp = 0 ∧ o = off + 1 then some (f, rs)
      else (nameAt (↑off + 5 + disp)).map (fun g => (g, (o, f) :: rs))
  | [] => (nameAt (↑off + 5 + disp)).map (fun g => (g, []))

/-- The decoding step after `decodeJ1` declines the bytes: at the end of the bytes
    close the current run; at a `call rel32` close the run with its callee and
    continue with `k` from the bytes and relocations after the call. -/
def callStep (nameAt : Int → Option String) (off : Nat) (acc : List (JInstr 64))
    (rs : List (Nat × String))
    (k : List (Nat × String) → List (BitVec 8) → Option (List CallSeg)) :
    List (BitVec 8) → Option (List CallSeg)
  | [] => some (flushRun acc)
  | e :: bs1 =>
      if e.toNat = 0xe8 then
        match decodeDisp 2 bs1 with
        | some (disp, rest) =>
            match callTarget nameAt off disp rs with
            | some (f, rs') => (k rs' rest).map (⟨acc, some f⟩ :: ·)
            | none => none
        | none => none
      else none

/-- Decode bytes at body offset `off` into runs, with `acc` the instructions of
    the current run and `rs` the relocations not yet used. Each step decodes one
    instruction with `decodeJ1` or one `call rel32`, which closes the current run;
    `fuel` bounds the number of steps. -/
def decodeCallSegsAux (nameAt : Int → Option String) :
    Nat → Nat → List (JInstr 64) → List (Nat × String) → List (BitVec 8) →
      Option (List CallSeg)
  | 0, _, acc, _, bs => if bs.isEmpty then some (flushRun acc) else none
  | fuel + 1, off, acc, rs, bs =>
      match decodeJ1 bs with
      | some (i, rest) =>
          decodeCallSegsAux nameAt fuel (off + (bs.length - rest.length)) (acc ++ [i]) rs rest
      | none => callStep nameAt off acc rs (decodeCallSegsAux nameAt fuel (off + 5) []) bs

/-- Decode a function body's bytes and its body-relative relocations into runs. -/
def decodeCallSegs (nameAt : Int → Option String) (rs : List (Nat × String))
    (bs : List (BitVec 8)) : Option (List CallSeg) :=
  decodeCallSegsAux nameAt bs.length 0 [] rs bs

/-- Merge each run whose `callee` is `none` into the next run, with `acc` the
    instructions carried into the first run. -/
def normSegsFrom (acc : List (JInstr 64)) : List CallSeg → List CallSeg
  | [] => flushRun acc
  | s :: ss =>
      match s.callee with
      | none => normSegsFrom (acc ++ s.body) ss
      | some f => ⟨acc ++ s.body, some f⟩ :: normSegsFrom [] ss

/-- The normal form of a list of runs: every run but the last ends in a call, and
    a last run that ends in no call is nonempty. -/
def normSegs (ss : List CallSeg) : List CallSeg := normSegsFrom [] ss

/-- The number of decoding steps a list of runs takes: one per instruction and one
    per call. -/
def segsFuel : List CallSeg → Nat
  | [] => 0
  | s :: ss => s.body.length + (if s.callee.isSome then 1 else 0) + segsFuel ss

/-- The displacement of every call to a function of the object fits `rel32`. -/
def callsFit (alloc : GpAlloc) (symBase : String → Option Int) :
    Nat → List CallSeg → Prop
  | _, [] => True
  | off, s :: ss =>
      match s.callee with
      | none => callsFit alloc symBase (off + (encodeJBlock alloc s.body).length) ss
      | some f =>
          (∀ δ, symBase f = some δ →
            dispOk32 (δ - ↑(off + (encodeJBlock alloc s.body).length + 5)) = true) ∧
          callsFit alloc symBase (off + (encodeJBlock alloc s.body).length + 5) ss

/-- Decode the body of a function's bytes: drop a prologue of `pre` bytes and an
    epilogue of `post` bytes, and shift the relocation offsets from function-relative
    to body-relative. -/
def decodeFramed (nameAt : Int → Option String) (pre post : Nat)
    (relocs : List (Nat × String)) (bs : List (BitVec 8)) : Option (List CallSeg) :=
  decodeCallSegs nameAt (relocs.map fun p => (p.1 - pre, p.2))
    ((bs.drop pre).take (bs.length - pre - post))

/-! ## 2. The normal form -/

/-- `normSegsFrom` keeps the instructions, in order, after the carried ones. -/
theorem instrs_normSegsFrom (acc : List (JInstr 64)) (ss : List CallSeg) :
    CallSeg.instrs (normSegsFrom acc ss) = acc ++ CallSeg.instrs ss := by
  induction ss generalizing acc with
  | nil =>
      by_cases h : acc = [] <;> simp [normSegsFrom, flushRun, CallSeg.instrs, h]
  | cons s ss ih =>
      simp only [CallSeg.instrs] at ih ⊢
      cases hs : s.callee <;> simp [normSegsFrom, hs, ih, List.append_assoc]

/-- `normSegsFrom` keeps the called symbols, in order. -/
theorem callees_normSegsFrom (acc : List (JInstr 64)) (ss : List CallSeg) :
    CallSeg.callees (normSegsFrom acc ss) = CallSeg.callees ss := by
  induction ss generalizing acc with
  | nil =>
      by_cases h : acc = [] <;> simp [normSegsFrom, flushRun, CallSeg.callees, h]
  | cons s ss ih =>
      simp only [CallSeg.callees] at ih ⊢
      cases hs : s.callee <;> simp [normSegsFrom, hs, ih]

/-- `normSegs` keeps the instructions. -/
theorem instrs_normSegs (ss : List CallSeg) :
    CallSeg.instrs (normSegs ss) = CallSeg.instrs ss := by
  simp [normSegs, instrs_normSegsFrom]

/-- `normSegs` keeps the called symbols. -/
theorem callees_normSegs (ss : List CallSeg) :
    CallSeg.callees (normSegs ss) = CallSeg.callees ss :=
  callees_normSegsFrom [] ss

/-! ## 3. Decoding steps -/

/-- `E8` starts no instruction `decodeJ1` reads. -/
theorem decodeJ1_e8 (t : List (BitVec 8)) : decodeJ1 (BitVec.ofNat 8 0xe8 :: t) = none := by
  simp [decodeJ1, isRex]

/-- A covered instruction encodes to at least one byte. -/
theorem encodeJInstr_ne_nil (alloc : GpAlloc) (i : JInstr 64)
    (hc : blockCovered i = true) (hr : mulxRdxOk alloc i = true) :
    encodeJInstr alloc i ≠ [] := by
  intro h
  have := roundtrip_decodeJ1 alloc i [] hc hr
  rw [h] at this
  simp [decodeJ1] at this

/-- A covered block encodes to at least as many bytes as it has instructions. -/
theorem length_le_encodeJBlock (alloc : GpAlloc) (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true ∧ mulxRdxOk alloc i = true) :
    block.length ≤ (encodeJBlock alloc block).length := by
  induction block with
  | nil => simp
  | cons i is ih =>
      have h1 := encodeJInstr_ne_nil alloc i (hc i (by simp)).1 (hc i (by simp)).2
      have h2 := ih (fun j hj => hc j (by simp [hj]))
      have h3 : 0 < (encodeJInstr alloc i).length := List.length_pos_iff.mpr h1
      simp only [encodeJBlock, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
      omega

/-- One decoding step on bytes `decodeJ1` reads. -/
theorem decodeCallSegsAux_succ_instr (nameAt : Int → Option String) (fuel off : Nat)
    (acc : List (JInstr 64)) (rs : List (Nat × String)) (bs rest : List (BitVec 8))
    (i : JInstr 64) (h : decodeJ1 bs = some (i, rest)) :
    decodeCallSegsAux nameAt (fuel + 1) off acc rs bs
      = decodeCallSegsAux nameAt fuel (off + (bs.length - rest.length)) (acc ++ [i]) rs rest := by
  simp only [decodeCallSegsAux, h]

/-- One decoding step on bytes `decodeJ1` declines. -/
theorem decodeCallSegsAux_succ_call (nameAt : Int → Option String) (fuel off : Nat)
    (acc : List (JInstr 64)) (rs : List (Nat × String)) (bs : List (BitVec 8))
    (h : decodeJ1 bs = none) :
    decodeCallSegsAux nameAt (fuel + 1) off acc rs bs
      = callStep nameAt off acc rs (decodeCallSegsAux nameAt fuel (off + 5) []) bs := by
  simp only [decodeCallSegsAux, h]

/-- The decoder reads a covered block off the front of the bytes into the current
    run, one step per instruction. -/
theorem decodeCallSegsAux_block (nameAt : Int → Option String) (alloc : GpAlloc)
    (block : List (JInstr 64))
    (hc : ∀ i ∈ block, blockCovered i = true ∧ mulxRdxOk alloc i = true)
    (fuel off : Nat) (acc : List (JInstr 64)) (rs : List (Nat × String))
    (rest : List (BitVec 8)) :
    decodeCallSegsAux nameAt (fuel + block.length) off acc rs
        (encodeJBlock alloc block ++ rest)
      = decodeCallSegsAux nameAt fuel (off + (encodeJBlock alloc block).length)
          (acc ++ block.map (renameJ alloc)) rs rest := by
  induction block generalizing off acc with
  | nil => simp [encodeJBlock]
  | cons i is ih =>
      have hi := roundtrip_decodeJ1 alloc i (encodeJBlock alloc is ++ rest)
        (hc i (by simp)).1 (hc i (by simp)).2
      have ih' := ih (fun j hj => hc j (by simp [hj]))
      simp only [encodeJBlock] at hi ih' ⊢
      rw [List.length_cons, ← Nat.add_assoc, List.flatMap_cons, List.append_assoc,
        decodeCallSegsAux_succ_instr nameAt _ off acc rs _ _ _ hi]
      simp only [List.length_append, Nat.add_sub_cancel]
      rw [ih']
      simp [List.append_assoc, Nat.add_assoc]

/-- Every relocation of runs encoded at body offset `off` lies past `off`. -/
theorem reloc_ge (alloc : GpAlloc) (symBase : String → Option Int) :
    ∀ (ss : List CallSeg) (off : Nat),
      ∀ p ∈ (encodeCallSegsFrom alloc symBase off ss).2, off + 1 ≤ p.1
  | [], _, p, hp => by simp [encodeCallSegsFrom] at hp
  | s :: ss, off, p, hp => by
      have ih := reloc_ge alloc symBase ss
      cases hs : s.callee with
      | none =>
          simp only [encodeCallSegsFrom, hs] at hp
          have := ih _ p hp
          omega
      | some f =>
          cases hb : symBase f with
          | some δ =>
              simp only [encodeCallSegsFrom, hs, hb] at hp
              have := ih _ p hp
              omega
          | none =>
              simp only [encodeCallSegsFrom, hs, hb, List.mem_cons] at hp
              rcases hp with rfl | hp
              · simp
              · have := ih _ p hp
                omega

/-- A call whose target is resolved in the object: no remaining relocation sits at
    its `rel32` field, so `nameAt` names the callee. -/
theorem callTarget_internal (nameAt : Int → Option String) (off : Nat) (disp : Int)
    (rs : List (Nat × String)) (h : ∀ p ∈ rs, off + 1 < p.1) :
    callTarget nameAt off disp rs = (nameAt (↑off + 5 + disp)).map (fun g => (g, rs)) := by
  cases rs with
  | nil => rfl
  | cons p rs =>
      obtain ⟨o, f⟩ := p
      have ho : o ≠ off + 1 := by have := h (o, f) (by simp); simp at this; omega
      simp [callTarget, ho]

/-! ## 4. The round trip -/

/-- The decoder recovers encoded runs, in normal form, from any body offset, with
    any pending run and any surplus of fuel. -/
theorem decodeCallSegsAux_encode (nameAt : Int → Option String) (alloc : GpAlloc)
    (symBase : String → Option Int)
    (hN : ∀ f δ, symBase f = some δ → nameAt δ = some f) :
    ∀ (ss : List CallSeg) (off fuel : Nat) (acc : List (JInstr 64)),
      (∀ s ∈ ss, ∀ i ∈ s.body, blockCovered i = true ∧ mulxRdxOk alloc i = true) →
      callsFit alloc symBase off ss →
      decodeCallSegsAux nameAt (fuel + segsFuel ss) off acc
          (encodeCallSegsFrom alloc symBase off ss).2
          (encodeCallSegsFrom alloc symBase off ss).1
        = some (normSegsFrom acc (ss.map (renameSeg alloc)))
  | [], off, fuel, acc, _, _ => by
      cases fuel with
      | zero => simp [segsFuel, encodeCallSegsFrom, decodeCallSegsAux, normSegsFrom]
      | succ n =>
          simp only [segsFuel, encodeCallSegsFrom, Nat.add_zero, List.map_nil, normSegsFrom]
          rw [decodeCallSegsAux_succ_call nameAt n off acc [] [] (by simp [decodeJ1])]
          rfl
  | s :: ss, off, fuel, acc, hc, hfit => by
      have hcs := hc s (by simp)
      have hcr : ∀ t ∈ ss, ∀ i ∈ t.body, blockCovered i = true ∧ mulxRdxOk alloc i = true :=
        fun t ht => hc t (by simp [ht])
      have ih := decodeCallSegsAux_encode nameAt alloc symBase hN ss
      have hren : (renameSeg alloc s).callee = s.callee := rfl
      cases hs : s.callee with
      | none =>
          simp only [callsFit, hs] at hfit
          simp only [encodeCallSegsFrom, hs, segsFuel, Option.isSome_none,
            Bool.false_eq_true, if_false, Nat.add_zero, List.map_cons, normSegsFrom, hren]
          rw [show fuel + (s.body.length + segsFuel ss) = (fuel + segsFuel ss) + s.body.length
            by omega, decodeCallSegsAux_block nameAt alloc s.body hcs]
          exact ih _ _ _ hcr hfit
      | some f =>
          simp only [callsFit, hs] at hfit
          obtain ⟨hδ, hfit⟩ := hfit
          have hrg := reloc_ge alloc symBase ss
            (off + (encodeJBlock alloc s.body).length + 5)
          simp only [encodeCallSegsFrom, hs, segsFuel, Option.isSome_some, if_true,
            List.map_cons, normSegsFrom, hren]
          rw [show fuel + (s.body.length + 1 + segsFuel ss)
              = ((fuel + segsFuel ss) + 1) + s.body.length by omega]
          cases hb : symBase f with
          | some δ =>
              rw [decodeCallSegsAux_block nameAt alloc s.body hcs,
                decodeCallSegsAux_succ_call _ _ _ _ _ _ (by simp only [callRel32,
                  List.cons_append, decodeJ1_e8])]
              simp only [callRel32, List.cons_append, callStep, BitVec.toNat_ofNat,
                decodeDisp_disp32LE _ _ (hδ δ hb),
                callTarget_internal nameAt (off + (encodeJBlock alloc s.body).length) _ _
                  (fun p hp => by have := hrg p hp; omega)]
              have ht : (↑(off + (encodeJBlock alloc s.body).length) + 5
                  + (δ - ↑(off + (encodeJBlock alloc s.body).length + 5)) : Int) = δ := by
                omega
              simp only [ht, hN f δ hb, Option.map_some, ih _ _ _ hcr hfit, renameSeg,
                if_true]
          | none =>
              rw [decodeCallSegsAux_block nameAt alloc s.body hcs,
                decodeCallSegsAux_succ_call _ _ _ _ _ _ (by simp only [callRel32,
                  List.cons_append, decodeJ1_e8])]
              simp only [callRel32, List.cons_append, callStep, BitVec.toNat_ofNat,
                decodeDisp_disp32LE _ _ (show dispOk32 0 = true by decide), callTarget,
                and_self, if_true, ih _ _ _ hcr hfit, Option.map_some, renameSeg]

/-- The runs take no more decoding steps than they have bytes. -/
theorem segsFuel_le (alloc : GpAlloc) (symBase : String → Option Int) :
    ∀ (ss : List CallSeg) (off : Nat),
      (∀ s ∈ ss, ∀ i ∈ s.body, blockCovered i = true ∧ mulxRdxOk alloc i = true) →
      segsFuel ss ≤ (encodeCallSegsFrom alloc symBase off ss).1.length
  | [], _, _ => by simp [segsFuel]
  | s :: ss, off, hc => by
      have h1 := length_le_encodeJBlock alloc s.body (hc s (by simp))
      have hcr : ∀ t ∈ ss, ∀ i ∈ t.body, blockCovered i = true ∧ mulxRdxOk alloc i = true :=
        fun t ht => hc t (by simp [ht])
      have ih := segsFuel_le alloc symBase ss
      cases hs : s.callee with
      | none =>
          have := ih (off + (encodeJBlock alloc s.body).length) hcr
          simp only [segsFuel, encodeCallSegsFrom, hs, List.length_append,
            Option.isSome_none, Bool.false_eq_true, if_false]
          omega
      | some f =>
          have := ih (off + (encodeJBlock alloc s.body).length + 5) hcr
          cases hb : symBase f <;>
          · simp only [segsFuel, encodeCallSegsFrom, hs, hb, List.length_append,
              callRel32_length, Option.isSome_some, if_true]
            omega

/-- Runs of covered instructions, separated by calls, decode back from their bytes
    and relocations: each instruction resolved through the allocation, each call
    named by its relocation (outside the object) or by `nameAt` at its target
    (inside the object), and the runs in normal form. -/
theorem roundtrip_callSegs (nameAt : Int → Option String) (alloc : GpAlloc)
    (symBase : String → Option Int) (ss : List CallSeg)
    (hN : ∀ f δ, symBase f = some δ → nameAt δ = some f)
    (hc : ∀ s ∈ ss, ∀ i ∈ s.body, blockCovered i = true ∧ mulxRdxOk alloc i = true)
    (hfit : callsFit alloc symBase 0 ss) :
    decodeCallSegs nameAt (encodeCallSegs alloc symBase ss).2
        (encodeCallSegs alloc symBase ss).1
      = some (normSegs (ss.map (renameSeg alloc))) := by
  have hle := segsFuel_le alloc symBase ss 0 hc
  unfold decodeCallSegs encodeCallSegs normSegs
  rw [show (encodeCallSegsFrom alloc symBase 0 ss).1.length
      = ((encodeCallSegsFrom alloc symBase 0 ss).1.length - segsFuel ss) + segsFuel ss
      by omega]
  exact decodeCallSegsAux_encode nameAt alloc symBase hN ss 0 _ [] hc hfit

/-! ## 5. Function framing -/

/-- Dropping a prologue and an epilogue of known lengths, and shifting the
    relocation offsets back by the prologue length, leaves the body and its
    body-relative relocations. -/
theorem decodeFramed_eq (nameAt : Int → Option String)
    (pre body post : List (BitVec 8)) (rs : List (Nat × String)) :
    decodeFramed nameAt pre.length post.length
        (rs.map fun p => (p.1 + pre.length, p.2)) (pre ++ body ++ post)
      = decodeCallSegs nameAt rs body := by
  have hmap : (List.map (fun p : Nat × String => (p.1 - pre.length, p.2))
      (List.map (fun p : Nat × String => (p.1 + pre.length, p.2)) rs)) = rs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id rs]
    apply List.map_congr_left
    intro p _
    simp
  unfold decodeFramed
  rw [hmap, List.append_assoc, List.drop_left, List.length_append, List.length_append,
    show pre.length + (body.length + post.length) - pre.length - post.length = body.length
      by omega, List.take_left]

/-- The round trip through a function's framing: runs encoded between a prologue
    `pre` and an epilogue `post`, with their relocations shifted to function-relative
    offsets, decode back to the runs in normal form. -/
theorem roundtrip_callSegs_framed (nameAt : Int → Option String) (alloc : GpAlloc)
    (symBase : String → Option Int) (ss : List CallSeg) (pre post : List (BitVec 8))
    (hN : ∀ f δ, symBase f = some δ → nameAt δ = some f)
    (hc : ∀ s ∈ ss, ∀ i ∈ s.body, blockCovered i = true ∧ mulxRdxOk alloc i = true)
    (hfit : callsFit alloc symBase 0 ss) :
    decodeFramed nameAt pre.length post.length
        ((encodeCallSegs alloc symBase ss).2.map fun p => (p.1 + pre.length, p.2))
        (pre ++ (encodeCallSegs alloc symBase ss).1 ++ post)
      = some (normSegs (ss.map (renameSeg alloc))) := by
  rw [decodeFramed_eq, roundtrip_callSegs nameAt alloc symBase ss hN hc hfit]

end CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86CallSeg
