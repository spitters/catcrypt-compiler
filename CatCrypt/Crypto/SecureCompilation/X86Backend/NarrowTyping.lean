/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame

@[expose] public section

set_option autoImplicit false

/-!
# A width map for the names of a body

The address machine keeps each name with the width of its value, and an arithmetic
instruction runs at the width of its first source. The exporter writes only the width `64`
into a mnemonic, so the widths `16` and `32` of a body are not on the wire. This module
computes them beside the body: `typeIn frame body k` lists names with the width each holds
before instruction `k`, by one forward pass.

## The pass

A width-carrying cast enters its destination at the destination width. An untagged
immediate move enters its destination at width `32`, or `1` for a carry constant. An
untagged `ADD`, `SUB`, `MUL`, `AND`, `OR`, `XOR` on a register first source and an untagged
register move enter the destination at the width of the first source when that source has an
entry, and remove the destination otherwise. Every other `Lopn` removes the names it writes.
A label empties the map, because a branch may arrive there; a conditional branch keeps it.

## Main definitions

* `WMap`, `wmSet`, `wmDrop`: a width map, the entry of a written name, the removal of names.
* `arithOp`, `srcWidth?`: the instructions whose destination takes the width of the first
  source, untagged or tagged at a width other than `64`.
* `typeStep`, `typeOut`, `typeIn`: one step of the pass, the map after the first `k`
  instructions, and the map before instruction `k`.
* `WTyped`: every name with an entry before the program counter holds a value of that width.
* `castSrcW`, `castPosTB`: the width of a cast source read off the map, and the check that a
  cast keeps the low bits its source and destination widths give.

## Main results

* `fstepA_lvm_of_not_dst`, `stepA_lvm_of_not_dst`: a step of the address machine leaves every
  register its instruction does not write.
* `fstepA_srcWidth`: an instruction of `srcWidth?` writes its destination at the width of its
  first source.
* `wTyped_step`, `runSafe_typed`: every step of the address machine keeps `WTyped`.
* `wTyped_castSrc`: at a cast whose source has an entry, the source holds a value of the
  width of the entry.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.NarrowTyping

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF)

/-! ## 1. The registers a step writes -/

theorem slotMov?_dst {i : LinstrR} {d a : String} (h : slotMov? i = some (d, a)) :
    d ∈ dstNames i := by
  unfold slotMov? at h
  split at h
  · split_ifs at h
    cases h; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
  · cases h

theorem slotCmp?_dst {i : LinstrR} {d x q : String} (h : slotCmp? i = some (d, x, q)) :
    d ∈ dstNames i := by
  unfold slotCmp? at h
  split at h
  · split at h
    · cases h; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

theorem loadIdxA?_dst {i : LinstrR} {d b x : String} {sc : Nat}
    (h : loadIdxA? i = some (d, b, x, sc)) : d ∈ dstNames i := by
  unfold loadIdxA? at h
  split at h
  · split at h
    · cases h; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

theorem cellA?_dst {i : LinstrR} {d b : String} {off : Nat} (h : cellA? i = some (.ld d b off)) :
    d ∈ dstNames i := by
  unfold cellA? at h
  split at h
  · dsimp only at h
    split_ifs at h
    all_goals try split at h
    all_goals first
      | cases h
      | (obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp h
         first
           | (cases hp; simp [dstNames, VIR.JasminLsemExportRewrites.opNames])
           | cases hp)
  · cases h

theorem cellA?_lea_dst {i : LinstrR} {d b : String} {off : Nat}
    (h : cellA? i = some (.lea d b off)) : d ∈ dstNames i := by
  unfold cellA? at h
  split at h
  · dsimp only at h
    split_ifs at h
    all_goals try split at h
    all_goals first
      | cases h
      | (obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp h
         first
           | (cases hp; simp [dstNames, VIR.JasminLsemExportRewrites.opNames])
           | cases hp)
  · cases h

theorem slotCarry?_dst {frame : String → Option (BitVec 64)} {i : LinstrR} {lo : Bool}
    {d a s c : String} (h : slotCarry? frame i = some (lo, d, a, s, c)) : d ∈ dstNames i := by
  unfold slotCarry? at h
  split at h
  · split at h
    · cases h; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

theorem slotCmov?_dst {frame : String → Option (BitVec 64)} {i : LinstrR}
    {d c a b : String} (h : slotCmov? frame i = some (d, c, a, b)) : d ∈ dstNames i := by
  unfold slotCmov? at h
  split at h
  · split at h
    · cases h; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

/-- **A step of the address machine leaves every register its instruction does not write.** -/
theorem fstepA_lvm_of_not_dst {frame : String → Option (BitVec 64)} {i : LinstrRM}
    {s s' : LstateA} {zf z' : Bool} (h : fstepA frame i s zf = some (s', z')) {r : String}
    (hr : r ∉ dstNames i.1) : s'.reg.lvm r = s.reg.lvm r := by
  have hreg : ∀ j : LinstrRM, (∀ x, x ∈ dstNames j.1 → x ∈ dstNames i.1) →
      regStepA j s zf = some (s', z') → s'.reg.lvm r = s.reg.lvm r := by
    intro j hj hs
    unfold regStepA at hs
    obtain ⟨bz, hb, he⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨rfl, -⟩ := Prod.mk.inj he
    exact (fstepF_frame_dst (t := bz.1) (z := bz.2) hb (fun h' => hr (hj _ h'))).1
  unfold fstepA at h
  repeat' split at h
  all_goals first
    | exact hreg _ (fun _ hx => hx) h
    | (rcases orElse_some h with h | ⟨-, h⟩
       · exact hreg _ (fun _ hx => hx) h
       · obtain ⟨d, o, ss, w, v, hx, rfl, rfl⟩ := bitStepA_eq h
         exact setReg_nextPc_lvm _ (fun e => hr (by
           rw [hx, e]
           simp [dstNames, VIR.JasminLsemExportRewrites.opNames])))
    | (refine hreg _ (fun x hx => ?_) h
       simp only [dstNames, VIR.JasminLsemExportRewrites.opNames, List.flatMap_cons,
         List.flatMap_nil, List.append_nil, List.mem_singleton] at hx
       subst hx
       exact slotCmp?_dst (by assumption))
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
       first
         | rfl
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ loadIdxA?_dst (by assumption)))
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ slotMov?_dst (by assumption)))
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ cellA?_dst (by assumption)))
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ cellA?_lea_dst (by assumption)))
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ slotCarry?_dst (by assumption)))
         | exact setReg_nextPc_lvm _ (fun e => hr (e ▸ slotCmov?_dst (by assumption))))
    | simp at h

/-- A step of the address machine on a body leaves every register its instruction does not
    write. -/
theorem stepA_lvm_of_not_dst {frame : String → Option (BitVec 64)} {body : Lcmd}
    {s s' : LstateA} {zf zf' : Bool} (h : stepA frame body s zf = some (s', zf')) {r : String}
    (hr : ∀ i, body[s.reg.lpc]? = some i → r ∉ dstNames i.li_i) :
    s'.reg.lvm r = s.reg.lvm r := by
  unfold stepA at h
  split at h
  · rename_i ii ds o ss hb
    exact fstepA_lvm_of_not_dst h (by simpa [normA, dstNames] using hr _ hb)
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
  · split at h
    · split_ifs at h
      · obtain ⟨p, -, he⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, -⟩ := Prod.mk.inj he; rfl
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h); rfl
    · cases h
  · cases h

/-! ## 2. The destination width of untagged arithmetic -/

/-- The untagged two-source mnemonics whose destination takes the width of the first
    source. -/
def arithBase (o : String) : Bool :=
  o == "ADD" || o == "SUB" || o == "MUL" || o == "AND" || o == "OR" || o == "XOR"

/-- The two-source mnemonics whose destination takes the width of the first source: an
    `arithBase` mnemonic, untagged or tagged at a width other than `64` (read through
    `LprogAsmPrinter.untagCaret`, as `normA` reads it). -/
def arithOp (o : String) : Bool := arithBase (LprogAsmPrinter.untagCaret o)

/-- A mnemonic whose `untagCaret` is `B` differs from every `L` whose `untagCaret` is not
    `B`. -/
theorem ne_of_untagCaret {o L B : String} (hu : LprogAsmPrinter.untagCaret o = B)
    (h : LprogAsmPrinter.untagCaret L ≠ B) : o ≠ L :=
  fun he => h (he ▸ hu)

/-- `normA` of an `Lopn` whose `untagCaret` is a mnemonic `B` other than `MULX` is the
    `Lopn` at `B`. -/
theorem normA_of_untagCaret {ds : List LOperand} {o : String} {ss : List LOperand}
    {B : String} (hu : LprogAsmPrinter.untagCaret o = B) (hB : B ≠ "MULX") :
    normA (.Lopn ds o ss) = .Lopn ds B ss := by
  simp [normA, hu, hB]

/-- **Untagged arithmetic writes at the width of its first source.** -/
theorem fstepA_arithWidth (frame : String → Option (BitVec 64)) (D A o : String) (b : LOperand)
    (ho : arithBase o = true) (s s' : LstateA) (zf zf' : Bool)
    (h : fstepA frame (.Lopn [.reg D] o [.reg A, b], .reg none) s zf = some (s', zf')) :
    (s'.reg.lvm D).1 = (s.reg.lvm A).1 := by
  simp only [arithBase, Bool.or_eq_true, beq_iff_eq] at ho
  rcases ho with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> cases b <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?,
      slotImm?, slotCmov?, regStepA, VIR.JasminLsemMemFlagNestJoin.fstepF,
      VIR.JasminLsemMemFlagGuard.cmpArgs?, VIR.JasminLsemMemFlagGuard.movRegArgs?,
      VIR.JasminLsemMemFlagGuard.stepMemF, VIR.JasminLsemMem.lsemStepMem, lsemStepCast,
      castStruct?, movImmStruct?, VIR.JasminLsemMemFlagGuard.withALUFlags,
      VIR.JasminLsemMemFlagGuard.aluFlagOp?, lsemStepMC, mulhiStruct?, adcxStruct?,
      adcxhiStruct?, sbbStruct?, sbbhiStruct?, VIR.JasminLsemShift.lsemStepSh,
      VIR.JasminLsemShift.sarStruct?, lsemStepN, readReg,
      VIR.JasminLsemMemFlagGuard.carryArgs?, VIR.JasminLsemMemFlagGuard.wideArgs?,
      bitStepA] at h
  all_goals
    obtain ⟨t, ht, rfl, -⟩ := h
    split at ht
    · rename_i b hb
      cases ht
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hb
      repeat' split at hr
      all_goals first
        | (cases hr; done)
        | (rename_i c hc; cases c <;> exact absurd hc (by decide +kernel))
        | (cases hr; simp [LstateN.setReg, LstateN.nextPc])
    · cases ht

/-- **An untagged register move writes at the width of its source.** -/
theorem fstepA_movWidth (frame : String → Option (BitVec 64)) (D A : String)
    (s s' : LstateA) (zf zf' : Bool)
    (h : fstepA frame (.Lopn [.reg D] "MOV" [.reg A], .reg none) s zf = some (s', zf')) :
    (s'.reg.lvm D).1 = (s.reg.lvm A).1 := by
  simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, cellA?, slotCarry?,
    slotImm?, slotCmov?, regStepA, VIR.JasminLsemMemFlagNestJoin.fstepF,
    VIR.JasminLsemMemFlagGuard.cmpArgs?, VIR.JasminLsemMemFlagGuard.movRegArgs?,
    readReg] at h
  obtain ⟨rfl, -⟩ := h
  simp [LstateN.setReg, LstateN.nextPc]

/-- The instruction `o D, [A, b]` of `arithOp` or the register move `MOV D, A` (untagged or
    tagged at a width other than `64`), as `(D, A)`: the destination and the source whose
    width it takes. -/
def srcWidth? : LinstrR → Option (String × String)
  | .Lopn [.reg d] o [.reg a, _] => if arithOp o then some (d, a) else none
  | .Lopn [.reg d] o [.reg a] =>
      if LprogAsmPrinter.untagCaret o = "MOV" then some (d, a) else none
  | _ => none

theorem srcWidth?_spec {i : LinstrR} {d a : String} (h : srcWidth? i = some (d, a)) :
    (∃ o b, i = .Lopn [.reg d] o [.reg a, b] ∧ arithOp o = true)
      ∨ ∃ o, i = .Lopn [.reg d] o [.reg a] ∧ LprogAsmPrinter.untagCaret o = "MOV" := by
  unfold srcWidth? at h
  split at h
  · split at h
    · rename_i ho
      cases h
      exact Or.inl ⟨_, _, rfl, ho⟩
    · cases h
  · split at h
    · rename_i ho
      cases h
      exact Or.inr ⟨_, rfl, ho⟩
    · cases h
  · cases h

/-- An instruction of `srcWidth?` is stepped at the register tag without a descriptor. -/
theorem srcWidth?_tag {i : LinstrR} {d a : String} (h : srcWidth? i = some (d, a))
    (body : Lcmd) (k : Nat) : tagAt body k i = .reg none := by
  rcases srcWidth?_spec h with ⟨o, b, rfl, ho⟩ | ⟨o, rfl, hu⟩
  · simp only [arithOp, arithBase, Bool.or_eq_true, beq_iff_eq] at ho
    rcases ho with ((((hu | hu) | hu) | hu) | hu) | hu <;>
      simp (disch := decide +kernel) [tagAt, bitMovB, movImmStruct?, tagA, ne_of_untagCaret hu]
  · simp (disch := decide +kernel) [tagAt, bitMovB, movImmStruct?, tagA, ne_of_untagCaret hu]

/-- **An instruction of `srcWidth?` writes its destination at the width of its source.** -/
theorem fstepA_srcWidth {frame : String → Option (BitVec 64)} {i : LinstrR} {d a : String}
    (hi : srcWidth? i = some (d, a)) {s s' : LstateA} {zf zf' : Bool}
    (h : fstepA frame (normA i, .reg none) s zf = some (s', zf')) :
    (s'.reg.lvm d).1 = (s.reg.lvm a).1 ∧ dstNames i = [d] := by
  rcases srcWidth?_spec hi with ⟨o, b, rfl, ho⟩ | ⟨o, rfl, hu⟩
  · refine ⟨?_, by simp [dstNames, VIR.JasminLsemExportRewrites.opNames]⟩
    simp only [arithOp, arithBase, Bool.or_eq_true, beq_iff_eq] at ho
    rcases ho with ((((hu | hu) | hu) | hu) | hu) | hu <;>
      (rw [normA_of_untagCaret hu (by decide)] at h
       exact fstepA_arithWidth frame d a _ b (by decide) s s' zf zf' h)
  · refine ⟨?_, by simp [dstNames, VIR.JasminLsemExportRewrites.opNames]⟩
    rw [normA_of_untagCaret hu (by decide)] at h
    exact fstepA_movWidth frame d a s s' zf zf' h

/-! ## 3. The width map -/

/-- A width map: names with the width of the value each holds. -/
abbrev WMap := List (String × Nat)

/-- The map with `d` at width `w`. -/
def wmSet (N : WMap) (d : String) (w : Nat) : WMap := (d, w) :: N.filter (fun p => p.1 != d)

/-- The map without the names `ds`. -/
def wmDrop (N : WMap) (ds : List String) : WMap := N.filter (fun p => !ds.contains p.1)

theorem lookup_wmDrop {N : WMap} {ds : List String} {r : String} {w : Nat}
    (h : (wmDrop N ds).lookup r = some w) : r ∉ ds ∧ N.lookup r = some w := by
  induction N with
  | nil => simp [wmDrop] at h
  | cons p N ih =>
    obtain ⟨x, v⟩ := p
    by_cases hx : x ∈ ds
    · have e : wmDrop ((x, v) :: N) ds = wmDrop N ds := by simp [wmDrop, hx]
      rw [e] at h
      obtain ⟨h1, h2⟩ := ih h
      have hrx : (r == x) = false := by
        simpa using fun e : r = x => h1 (e ▸ hx)
      exact ⟨h1, by simp only [List.lookup, hrx, h2]⟩
    · have e : wmDrop ((x, v) :: N) ds = (x, v) :: wmDrop N ds := by simp [wmDrop, hx]
      rw [e] at h
      by_cases hrx : r = x
      · subst hrx
        simp only [List.lookup, beq_self_eq_true] at h ⊢
        exact ⟨hx, h⟩
      · have hb : (r == x) = false := by simpa using hrx
        simp only [List.lookup, hb] at h ⊢
        exact ih h

theorem lookup_wmSet {N : WMap} {d r : String} {w v : Nat}
    (h : (wmSet N d v).lookup r = some w) : (r = d ∧ w = v) ∨ (r ≠ d ∧ N.lookup r = some w) := by
  by_cases hr : r = d
  · subst hr
    simp only [wmSet, List.lookup, beq_self_eq_true, Option.some.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  · have hb : (r == d) = false := by simpa using hr
    simp only [wmSet, List.lookup, hb, lookup_filter_ne _ hr] at h
    exact Or.inr ⟨hr, h⟩

/-- **One step of the pass** at instruction `k` of a body. -/
def typeStep (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) (N : WMap)
    (i : LinstrR) : WMap :=
  match classifyK i with
  | some (d, _, _, w) => wmSet N d w
  | none =>
      match srcWidth? i with
      | some (d, a) =>
          match N.lookup a with
          | some w => wmSet N d w
          | none => wmDrop N [d]
      | none =>
          match movImmStruct? i with
          | some (d, _) =>
              if (frame d).isNone then wmSet N d (if bitMovB body k i then 1 else 32)
              else wmDrop N [d]
          | none => wmDrop N (dstNames i)

/-- The instruction is a label. -/
def labB : LinstrR → Bool
  | .Llabel _ _ => true
  | _ => false

/-- One step of the pass, emptying the map at a label. -/
def typeStepAt (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) (N : WMap)
    (i : LinstrR) : WMap :=
  if labB i then [] else typeStep frame body k N i

/-- The width map after the first `k` instructions of a body. -/
def typeOut (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : WMap :=
  ((body.take k).zipIdx).foldl (fun N p => typeStepAt frame body p.2 N p.1.li_i) []

/-- **The width map** before instruction `k` of a body: empty at a label, where a branch may
    arrive, and the map after the first `k` instructions elsewhere. -/
def typeIn (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : WMap :=
  if (body[k]?).any (fun i => labB i.li_i) then [] else typeOut frame body k

theorem typeOut_succ {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) :
    typeOut frame body (k + 1) = typeStepAt frame body k (typeOut frame body k) bi.li_i := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp hb).1
  unfold typeOut
  rw [List.take_add_one, hb, Option.toList_some, List.zipIdx_append, List.foldl_append,
    List.length_take, Nat.min_eq_left hk.le]
  simp

/-- An entry before instruction `k + 1` is an entry of the step of instruction `k` from the
    map before `k`. -/
theorem typeIn_succ {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) {r : String} {w : Nat}
    (h : (typeIn frame body (k + 1)).lookup r = some w) :
    (typeStepAt frame body k (typeIn frame body k) bi.li_i).lookup r = some w := by
  unfold typeIn at h
  split_ifs at h with hl
  · simp at h
  · rw [typeOut_succ hb] at h
    by_cases hlab : labB bi.li_i = true
    · simp [typeStepAt, hlab] at h
    · have e : typeIn frame body k = typeOut frame body k := by
        simp [typeIn, hb, hlab]
      rw [e]; exact h

/-- **The typing invariant of the address machine**: every name with an entry in the width
    map before the program counter holds a value of the width of its entry. -/
def WTyped (frame : String → Option (BitVec 64)) (body : Lcmd) (s : LstateA) : Prop :=
  ∀ r w, (typeIn frame body s.reg.lpc).lookup r = some w → (s.reg.lvm r).1 = w

/-- The invariant holds where the width map is empty, in particular at the entry of a body. -/
theorem wTyped_of_nil {frame : String → Option (BitVec 64)} {body : Lcmd} {s : LstateA}
    (h : typeIn frame body s.reg.lpc = []) : WTyped frame body s := by
  intro r w hl
  rw [h] at hl
  simp at hl

theorem typeIn_zero (frame : String → Option (BitVec 64)) (body : Lcmd) :
    typeIn frame body 0 = [] := by
  simp [typeIn, typeOut]

/-- **The width map is an invariant of the address machine**, across every instruction. -/
theorem wTyped_step {frame : String → Option (BitVec 64)} {body : Lcmd} {s s' : LstateA}
    {zf zf' : Bool} (hI : WTyped frame body s)
    (hst : stepA frame body s zf = some (s', zf')) : WTyped frame body s' := by
  -- an entry that survives the removal of the written names
  have hdrop : ∀ (ds : List String) (r : String) (w : Nat),
      (∀ x, x ∉ ds → s'.reg.lvm x = s.reg.lvm x) →
      (wmDrop (typeIn frame body s.reg.lpc) ds).lookup r = some w → (s'.reg.lvm r).1 = w := by
    intro ds r w hfr hl
    obtain ⟨h1, h2⟩ := lookup_wmDrop hl
    rw [hfr r h1]; exact hI r w h2
  -- an entry of the map with the destination at the width it is written at
  have hset : ∀ (d r : String) (v w : Nat), (s'.reg.lvm d).1 = v →
      (∀ x, x ≠ d → s'.reg.lvm x = s.reg.lvm x) →
      (wmSet (typeIn frame body s.reg.lpc) d v).lookup r = some w → (s'.reg.lvm r).1 = w := by
    intro d r v w hd hfr hl
    rcases lookup_wmSet hl with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
    · exact hd
    · rw [hfr r h1]; exact hI r w h2
  unfold stepA at hst
  split at hst
  · rename_i ii ds o ss hb
    have hpc : s'.reg.lpc = s.reg.lpc + 1 := fstepA_lpc _ _ _ _ _ _ hst
    have hfr : ∀ x, x ∉ dstNames (.Lopn ds o ss) → s'.reg.lvm x = s.reg.lvm x := fun x hx =>
      fstepA_lvm_of_not_dst hst (by simpa [normA, dstNames] using hx)
    intro r w hl
    rw [hpc] at hl
    have hl' := typeIn_succ hb hl
    simp only [typeStepAt, labB, Bool.false_eq_true, ite_false, typeStep] at hl'
    cases hk : classifyK (.Lopn ds o ss) with
    | some q =>
      obtain ⟨d, a, m, w0⟩ := q
      simp only [hk] at hl'
      obtain ⟨o', he, hm, hw⟩ := classifyK_spec hk
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hst' := hst
      rw [normA_castW hw, tagAt_castW _ _ hw,
        fstepA_castW _ d a o w0 (castStruct?_of_castMovBits hm d a),
        lsemStepCast_castW d a o w0 (castStruct?_of_castMovBits hm d a)] at hst'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst'
      refine hset d r w0 w ?_ (fun x hx => hfr x (by
        simpa [dstNames, VIR.JasminLsemExportRewrites.opNames] using hx)) hl'
      rw [← hst'.1]
      simp [LstateN.setReg, LstateN.nextPc]
    | none =>
      simp only [hk] at hl'
      cases hsw : srcWidth? (.Lopn ds o ss) with
      | some q =>
        obtain ⟨d, a⟩ := q
        simp only [hsw] at hl'
        rw [srcWidth?_tag hsw body s.reg.lpc] at hst
        obtain ⟨hwd, hdn⟩ := fstepA_srcWidth hsw hst
        rw [hdn] at hfr
        cases hla : (typeIn frame body s.reg.lpc).lookup a with
        | some wa =>
          simp only [hla] at hl'
          exact hset d r wa w (by rw [hwd]; exact hI a wa hla)
            (fun x hx => hfr x (by simpa using hx)) hl'
        | none =>
          simp only [hla] at hl'
          exact hdrop [d] r w hfr hl'
      | none =>
        simp only [hsw] at hl'
        cases hmi : movImmStruct? (.Lopn ds o ss) with
        | some q =>
          obtain ⟨d, n⟩ := q
          simp only [hmi] at hl'
          obtain ⟨o', hi0⟩ := movImmStruct?_spec hmi
          simp only [LinstrR.Lopn.injEq] at hi0
          obtain ⟨hds, rfl, hss⟩ := hi0
          have hi : LinstrR.Lopn ds o ss = .Lopn [.reg d] o [.imm n] := by rw [hds, hss]
          have hform : o = "MOV" ∨ ∃ w, w ≠ 64 ∧ o = withWidthTag w "MOV" :=
            VIR.JasminLsemCast.isMovImmMnem_iff.1 (by simpa [movImmStruct?, hds, hss] using hmi)
          have hnA : normA (.Lopn [.reg d] o [.imm n]) = .Lopn [.reg d] "MOV" [.imm n] := by
            rcases hform with rfl | ⟨w, hw, rfl⟩
            · simp (config := { decide := true }) [normA]
            · rw [normA_untag hw (by decide)]
              simp (config := { decide := true }) [normA]
          have htA : tagA (.Lopn [.reg d] o [.imm n]) = .reg none := by
            rcases hform with rfl | ⟨w, hw, rfl⟩ <;>
              simp (disch := decide +kernel) [tagA, withWidthTag_ne_of_tagSepFree]
          have hdn : dstNames (.Lopn ds o ss) = [d] := by
            rw [hi]; simp [dstNames, VIR.JasminLsemExportRewrites.opNames]
          rw [hdn] at hfr
          split_ifs at hl' with hfd hbm
          · rw [hi] at hst hbm
            have hD : frame d = none := by simpa using hfd
            rw [hnA, show tagAt body s.reg.lpc (.Lopn [.reg d] o [.imm n]) = .reg (some 1) from
                by simp [tagAt, hbm],
              fstepA_bitMov frame d n s zf hD] at hst
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
            exact hset d r 1 w (by simp [LstateN.setReg, LstateN.nextPc])
              (fun x hx => hfr x (by simpa using hx)) hl'
          · rw [hi] at hst hbm
            have hD : frame d = none := by simpa using hfd
            rw [hnA, show tagAt body s.reg.lpc (.Lopn [.reg d] o [.imm n]) = .reg none from
                by simp [tagAt, hbm, htA],
              fstepA_immMov32 frame d n s zf hD] at hst
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
            exact hset d r 32 w (by simp [LstateN.setReg, LstateN.nextPc])
              (fun x hx => hfr x (by simpa using hx)) hl'
          · exact hdrop [d] r w hfr hl'
        | none =>
          simp only [hmi] at hl'
          exact hdrop _ r w hfr hl'
  · rename_i ii kd l hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
    intro r w hl
    have hl' := typeIn_succ hb hl
    simp [typeStepAt, labB] at hl'
  · rename_i ii cc l hb
    split at hst
    · rename_i pol hpol
      split_ifs at hst with hz
      · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp hst
        obtain ⟨rfl, -⟩ := Prod.mk.inj he
        obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
        apply wTyped_of_nil
        show typeIn frame body p = []
        have hlb : labB body[p].li_i = true := by
          revert hlab
          rcases body[p] with ⟨ii', li'⟩
          cases li' <;> simp [isLabelB, labB]
        simp [typeIn, List.getElem?_eq_getElem hpl, hlb]
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
        intro r w hl
        have hl' := typeIn_succ hb hl
        simp only [typeStepAt, labB, Bool.false_eq_true, ite_false, typeStep, classifyK,
          srcWidth?, movImmStruct?, dstNames] at hl'
        exact hI r w (lookup_wmDrop hl').2
    · cases hst
  · cases hst

/-- A run that is safe for a predicate from a state satisfying `WTyped` is safe for the
    predicate with `WTyped`. -/
theorem runSafe_typed {frame : String → Option (BitVec 64)} {body : Lcmd}
    {Q : LstateA → Prop} :
    ∀ (fuel : Nat) (s : LstateA) (zf : Bool), WTyped frame body s →
      RunSafe frame body Q fuel s zf →
      RunSafe frame body (fun t => Q t ∧ WTyped frame body t) fuel s zf
  | 0, _, _, _, _ => trivial
  | fuel + 1, _, _, hI, h =>
      ⟨⟨h.1, hI⟩, fun s' zf' hst =>
        runSafe_typed fuel s' zf' (wTyped_step hI hst) (h.2 s' zf' hst)⟩

/-! ## 4. The cast gate on the width map -/

/-- The width of the source of the cast at instruction `k`, read off the width map; `64`
    without an entry. -/
def castSrcW (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) (a : String) : Nat :=
  ((typeIn frame body k).lookup a).getD 64

/-- The cast at position `k` keeps as many low bits as the smaller of the width of its
    source, read off the width map, and its destination width. -/
def castPosTB (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) : Bool :=
  (body[k]?).all fun j =>
    match classifyK j.li_i with
    | some (_, a, m, w) => m == min (castSrcW frame body k a) w
    | none => true

/-- **A typed source.** A name with an entry in the width map before the program counter
    holds a value of the width `castSrcW` reads. -/
theorem wTyped_castSrc {frame : String → Option (BitVec 64)} {body : Lcmd} {s : LstateA}
    (hI : WTyped frame body s) {a : String}
    (ha : ((typeIn frame body s.reg.lpc).lookup a).isSome = true) :
    (s.reg.lvm a).1 = castSrcW frame body s.reg.lpc a := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ha
  rw [castSrcW, hw]
  exact hI a w hw

end CatCrypt.Crypto.SecureCompilation.X86Backend.NarrowTyping
