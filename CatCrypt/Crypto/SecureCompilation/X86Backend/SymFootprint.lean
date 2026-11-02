/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs

@[expose] public section

set_option autoImplicit false

/-!
# The read and write footprint of the symbolic step

The value checker `OwnedLprogTV.ownedCheckWithR` runs every block of a reference symbolically
(`symStep`, `symRun`) and needs live at the start of the block the start registers that the
final words read (`OwnedLprogTV.blockNeed`). The register liveness table of the region back
end (`RegionBackend.liveRegTab`) is computed syntactically, from the names an instruction
reads (`useNames`) and the names it writes (`regDefs`). This module relates the two: the
symbolic step writes only names of `regDefs`, and every word, array, flag and guard it builds
reads only start registers that the words of the names of `useNames`, the arrays and the flags
read before the step. The liveness table is therefore an upper bound of the symbolic needs,
the footprint condition C1 of the completeness of the checks of a calling body.

The statements hold for an instruction with one register destination when it is an operation
(`OneDst`), the third conjunct of the export shape `RegionAllocMapComplete.CoShape`. The only
instruction the symbolic step knows with an implicit source, the widening multiply `MULX`
(source `mulxSrc`), has two destinations. The base of an indexed operand is a name of
`useNames`, so the load-effective-address `LEA d, [b + x · sc]`, which reads `b` as a
register, is covered without a hypothesis on the operands.

The words are read over a term table `E` (`STerm.varsT`), for every table: the step builds
words from the words of the state without new table entries.

## Main definitions

* `OneDst`: an operation has one register destination.
* `ReadsIn`: the words of a symbolic state at a set of names, its arrays and its flags read
  only start registers of a set.
* `RWithin`, `SWithin`: a step description writes within the destinations and reads
  within a set.

## Main results

* `symN_within`, `symSh_within`, `symMC_within`, `symCast_within`: the register layers.
* `symMem_within`: the memory layer.
* `symStep_regs`: after a step, a register keeps its word or is a name of `regDefs` whose new
  word reads only start registers the sources read.
* `symStep_frame`: a step writes only names of `regDefs`.
* `symStep_readsIn`: the transfer of `ReadsIn` across a step, from the names `useNames` and the
  names live after the step that it does not write.
* `symRun_readsIn`: the transfer across a run of a list of instructions.
* `symStep_shadowCall`: the step of a shadow instruction of a call has no description, so a
  block holding one has no successful run.

Elaboration takes about ten seconds, spent in the case splits over the recognisers of the
step (`symN_within`, `symStep_within`, `symStep_shadowCall`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SymFootprint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs
  memRegDefs storeHit?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (LinstrRT castStruct? movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (cmpOfName? cmpOfName?_eq_none)

/-! ## 1. Sets of names read by words -/

/-- **One register destination**: an operation of the instruction writes one register, the
    destination shape of the export (`RegionAllocMapComplete.CoShape`). -/
def OneDst (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss → ∃ x, ds = [.reg x]

/-- **The words of `ss` read within `X`** over the table `E`: the word of every name of `N`,
    every array and the three flags read only start registers of `X`. -/
structure ReadsIn (E : Array TEnt) (X N : String → Prop) (ss : SSt) : Prop where
  /-- The words of the names of `N`. -/
  regs : ∀ r, N r → ∀ v ∈ (ss.regs r).varsT E, X v
  /-- The arrays. -/
  arrs : ∀ a, ∀ v ∈ (ss.arrs a).varsT E, X v
  /-- The zero flag. -/
  zf : ∀ v ∈ ss.zf.varsT E, X v
  /-- The carry flag. -/
  cf : ∀ v ∈ ss.cf.varsT E, X v
  /-- The overflow flag. -/
  of : ∀ v ∈ ss.of.varsT E, X v

theorem ReadsIn.mono {E : Array TEnt} {X N N' : String → Prop} {ss : SSt}
    (h : ReadsIn E X N ss) (hN : ∀ r, N' r → N r) : ReadsIn E X N' ss :=
  ⟨fun r hr => h.regs r (hN r hr), h.arrs, h.zf, h.cf, h.of⟩

/-- The start state reads, at every name, only that name. -/
theorem readsIn_start (E : Array TEnt) (N : String → Prop) :
    ReadsIn E N N SSt.start := by
  refine ⟨fun r hr v hv => ?_, fun a v hv => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v hv => ?_⟩ <;>
    simp_all [SSt.start, SSt.regs, SArr.varsT, SFlag.varsT, STerm.varsT]

/-- A register-file description `o` of the instruction `x` **writes within its destinations
    and reads within `X`**: a written name is a name of `defNames x`, and the word and the
    guards read only start registers of `X`. -/
def RWithin (E : Array TEnt) (X : String → Prop) (x : LinstrR) : ROut → Prop
  | .set d t gs => d ∈ defNames x ∧ (∀ v ∈ t.varsT E, X v) ∧ ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v
  | .nop => defNames x = []
  | .fail => True
  | .unk => True

/-- The sources of `x` read only start registers of `X`. -/
def SrcsIn (E : Array TEnt) (X : String → Prop) (x : LinstrR) (R : String → STerm) : Prop :=
  ∀ u ∈ useNames x, ∀ v ∈ (R u).varsT E, X v


/-- A memory description `o` of the step of `i` from `ss` **writes within `regDefs i` and
    reads within `X`**: a register outside `regDefs i` keeps its word, the word of a register
    of `regDefs i`, every array, the three flags and the guards read only start registers of
    `X`. -/
def SWithin (E : Array TEnt) (X : String → Prop) (i : LinstrRM) (ss : SSt) : SOut → Prop
  | .ok s gs =>
      (∀ r, r ∉ regDefs i → s.regs r = ss.regs r) ∧
      (∀ r ∈ regDefs i, ∀ v ∈ (s.regs r).varsT E, X v) ∧
      (∀ a, ∀ v ∈ (s.arrs a).varsT E, X v) ∧
      (∀ v ∈ s.zf.varsT E, X v) ∧ (∀ v ∈ s.cf.varsT E, X v) ∧ (∀ v ∈ s.of.varsT E, X v) ∧
      ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v
  | .fail => True
  | .unk => True

/-! ## 2. The recognisers of the step -/

section Shapes

private theorem castStruct?_shape {x : LinstrR} {d a : String}
    (h : castStruct? x = some (d, a)) : ∃ opn, x = .Lopn [.reg d] opn [.reg a] := by
  unfold castStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem movImmStruct?_shape {x : LinstrR} {d : String} {n : Nat}
    (h : movImmStruct? x = some (d, n)) : ∃ opn, x = .Lopn [.reg d] opn [.imm n] := by
  unfold movImmStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem sarStruct?_shape {x : LinstrR} {d a : String} {n : Nat}
    (h : JasminLsemShift.sarStruct? x = some (d, a, n)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .imm n] := by
  unfold JasminLsemShift.sarStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem mulhiStruct?_shape {x : LinstrR} {d a b : String}
    (h : JasminLsemMulCarry.mulhiStruct? x = some (d, a, b)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .reg b] := by
  unfold JasminLsemMulCarry.mulhiStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem adcxStruct?_shape {x : LinstrR} {d a b c : String}
    (h : JasminLsemMulCarry.adcxStruct? x = some (d, a, b, c)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .reg b, .reg c] := by
  unfold JasminLsemMulCarry.adcxStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem adcxhiStruct?_shape {x : LinstrR} {d a b c : String}
    (h : JasminLsemMulCarry.adcxhiStruct? x = some (d, a, b, c)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .reg b, .reg c] := by
  unfold JasminLsemMulCarry.adcxhiStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem sbbStruct?_shape {x : LinstrR} {d a b c : String}
    (h : JasminLsemMulCarry.sbbStruct? x = some (d, a, b, c)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .reg b, .reg c] := by
  unfold JasminLsemMulCarry.sbbStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem sbbhiStruct?_shape {x : LinstrR} {d a b c : String}
    (h : JasminLsemMulCarry.sbbhiStruct? x = some (d, a, b, c)) :
    ∃ opn, x = .Lopn [.reg d] opn [.reg a, .reg b, .reg c] := by
  unfold JasminLsemMulCarry.sbbhiStruct? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

private theorem loadStruct?_shape {x : LinstrR} {d b i : String}
    (h : loadStruct? x = some (d, b, i)) : ∃ sc, x = .Lopn [.reg d] "LOADIDX" [.arrIdx b i sc] := by
  unfold loadStruct? at h
  split at h
  · split_ifs at h with ho
    cases h
    subst ho
    exact ⟨_, rfl⟩
  · cases h

private theorem storeStruct?_shape {x : LinstrR} {d b i v : String}
    (h : storeStruct? x = some (d, b, i, v)) :
    ∃ sc, x = .Lopn [.reg d] "STOREIDX" [.arrIdx b i sc, .reg v] := by
  unfold storeStruct? at h
  split at h
  · split_ifs at h with ho
    cases h
    subst ho
    exact ⟨_, rfl⟩
  · cases h

private theorem storeImmStruct?_shape {x : LinstrR} {d b v : String} {k : Nat}
    (h : storeImmStruct? x = some (d, b, v, k)) :
    x = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k] := by
  unfold storeImmStruct? at h
  split at h
  · split_ifs at h with ho
    cases h
    subst ho
    rfl
  · cases h

private theorem cmpArgs?_shape {i : LinstrRM} {a b : LOperand} (h : cmpArgs? i = some (a, b)) :
    ∃ d, i.1 = .Lopn [d] (withWidthTag 64 "CMP") [a, b] := by
  unfold cmpArgs? at h
  split at h
  · rename_i d opn a' b' he
    split_ifs at h with ho
    cases h
    exact ⟨d, by rw [he, ho]⟩
  · cases h

private theorem movRegArgs?_shape {i : LinstrRM} {d a : String}
    (h : movRegArgs? i = some (d, a)) : ∃ opn, i.1 = .Lopn [.reg d] opn [.reg a] := by
  unfold movRegArgs? at h
  split at h
  · rename_i d' opn a' he
    split_ifs at h <;> cases h <;> exact ⟨opn, he⟩
  · cases h

private theorem carryArgs?_shape {i : LinstrRM} {op : CarryOp} {d : String} {a b : LOperand}
    (h : carryArgs? i = some (op, d, a, b)) :
    ∃ opn, i.1 = .Lopn [.reg d] opn [a, b] ∧
      (opn = withWidthTag 64 "ADC" ∨ opn = withWidthTag 64 "SBB" ∨
        opn = withWidthTag 64 "ADCX" ∨ opn = withWidthTag 64 "ADOX") := by
  unfold carryArgs? at h
  split at h
  · rename_i d' opn a' b' he
    split_ifs at h with h1 h2 h3 h4 <;> cases h
    · exact ⟨opn, he, Or.inl h1⟩
    · exact ⟨opn, he, Or.inr (Or.inl h2)⟩
    · exact ⟨opn, he, Or.inr (Or.inr (Or.inl h3))⟩
    · exact ⟨opn, he, Or.inr (Or.inr (Or.inr h4))⟩
  · cases h

private theorem wideArgs?_shape {i : LinstrRM} {w : WideOp} (h : wideArgs? i = some w) :
    (∃ d x b, w = .mov d b ∧ i.1 = .Lopn [.reg d] (withWidthTag 64 "MOV") [x, b]) ∨
      ∃ lo hi b opn, w = .mulx lo hi b ∧ i.1 = .Lopn [.reg lo, .reg hi] opn [b] := by
  unfold wideArgs? at h
  split at h
  · rename_i d opn x b he
    split_ifs at h with ho
    cases h
    exact Or.inl ⟨d, x, b, rfl, by rw [he, ho]⟩
  · rename_i lo hi opn b he
    split_ifs at h
    cases h
    exact Or.inr ⟨lo, hi, b, opn, rfl, he⟩
  · cases h

/-- The mnemonic of an instruction that writes an array by `storeHit?`. -/
private theorem storeHit?_shape {i : LinstrRM} {a : String} (h : storeHit? i = some a) :
    ∃ ds srcs, i.1 = .Lopn ds "STOREIDX" srcs ∨ i.1 = .Lopn ds "ZEROARR" srcs ∨
      i.1 = .Lopn ds "STOREIMM" srcs := by
  obtain ⟨x, tag⟩ := i
  unfold storeHit? at h
  cases tag with
  | store w n =>
      obtain ⟨⟨d, b, j, v⟩, hp, -⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨sc, rfl⟩ := storeStruct?_shape hp
      exact ⟨_, _, Or.inl rfl⟩
  | zero w n =>
      simp only at h
      unfold zeroStruct? at h
      split at h
      · split_ifs at h with ho
        subst ho
        exact ⟨_, _, Or.inr (Or.inl rfl)⟩
      · cases h
  | storeImm w n =>
      obtain ⟨⟨d, b, v, k⟩, hp, -⟩ := Option.map_eq_some_iff.mp h
      rw [storeImmStruct?_shape hp]
      exact ⟨_, _, Or.inr (Or.inr rfl)⟩
  | reg _ => cases h
  | load _ _ => cases h
  | loadC => cases h
  | storeC => cases h

/-- The registers an instruction writes when it is no compare, no register copy and writes no
    array by `storeHit?`: the names of its destinations. -/
private theorem regDefs_of_none {i : LinstrRM} (h1 : cmpArgs? i = none)
    (h2 : movRegArgs? i = none) (h3 : storeHit? i = none) : regDefs i = defNames i.1 := by
  simp [regDefs, memRegDefs, h1, h2, h3]

/-- An instruction whose mnemonic is none of the three array writes writes no array by
    `storeHit?`. -/
private theorem storeHit?_none_of_opn {i : LinstrRM} {ds srcs : List LOperand} {opn : String}
    (hi : i.1 = .Lopn ds opn srcs) (h1 : opn ≠ "STOREIDX") (h2 : opn ≠ "ZEROARR")
    (h3 : opn ≠ "STOREIMM") : storeHit? i = none := by
  cases hs : storeHit? i with
  | none => rfl
  | some a =>
      obtain ⟨ds', srcs', h | h | h⟩ := storeHit?_shape hs <;> rw [hi] at h <;>
        simp only [LinstrR.Lopn.injEq] at h
      · exact absurd h.2.1 h1
      · exact absurd h.2.1 h2
      · exact absurd h.2.1 h3

end Shapes

/-! ## 3. The register layers -/

section Layers

variable {E : Array TEnt} {X : String → Prop}

/-- A name an operand of the sources mentions is a name of `useNames`. -/
private theorem mem_useNames_of {ds : List LOperand} {opn : String} {srcs : List LOperand}
    {u : String} {o : LOperand} (ho : o ∈ srcs) (hu : u ∈ opNames o) :
    u ∈ useNames (.Lopn ds opn srcs) := by
  simp only [useNames, List.mem_flatMap]
  exact ⟨o, ho, hu⟩

/-- The word of a source register `a` of an operation reads within `X`. -/
private theorem src_reg {ds : List LOperand} {opn : String} {srcs : List LOperand}
    {R : String → STerm} (hR : SrcsIn E X (.Lopn ds opn srcs) R) {a : String}
    (ha : LOperand.reg a ∈ srcs) : ∀ v ∈ (R a).varsT E, X v :=
  hR a (mem_useNames_of ha (by simp [opNames]))

/-- The destination of an operation with the destinations `[.reg d]` is a name of
    `defNames`. -/
private theorem dst_mem {opn : String} {srcs : List LOperand} {d : String} :
    d ∈ defNames (.Lopn [.reg d] opn srcs) := by
  simp [defNames, opNames]

/-- The closing step for a description `.set d t gs` of an operation `[.reg d] opn srcs`: the
    word and the guards read only words of source registers. -/
private theorem within_set {d opn : String} {srcs : List LOperand} {R : String → STerm}
    (hR : SrcsIn E X (.Lopn [.reg d] opn srcs) R) {t : STerm} {gs : List SG}
    (ht : ∀ v ∈ t.varsT E, ∃ a, LOperand.reg a ∈ srcs ∧ v ∈ (R a).varsT E)
    (hg : ∀ g ∈ gs, ∀ v ∈ g.varsT E, ∃ a, LOperand.reg a ∈ srcs ∧ v ∈ (R a).varsT E) :
    RWithin E X (.Lopn [.reg d] opn srcs) (ROut.set d t gs) := by
  refine ⟨dst_mem, fun v hv => ?_, fun g hgm v hv => ?_⟩
  · obtain ⟨a, ha, hv'⟩ := ht v hv
    exact src_reg hR ha v hv'
  · obtain ⟨a, ha, hv'⟩ := hg g hgm v hv
    exact src_reg hR ha v hv'

/-- The closing step for a description `.set d t gs` of an operation `[.reg d] opn srcs`,
    with the names read taken from `useNames`. -/
private theorem within_use {d opn : String} {srcs : List LOperand} {R : String → STerm}
    (hR : SrcsIn E X (.Lopn [.reg d] opn srcs) R) {t : STerm} {gs : List SG}
    (ht : ∀ v ∈ t.varsT E, ∃ u ∈ useNames (.Lopn [.reg d] opn srcs), v ∈ (R u).varsT E)
    (hg : ∀ g ∈ gs, ∀ v ∈ g.varsT E,
      ∃ u ∈ useNames (.Lopn [.reg d] opn srcs), v ∈ (R u).varsT E) :
    RWithin E X (.Lopn [.reg d] opn srcs) (ROut.set d t gs) := by
  refine ⟨dst_mem, fun v hv => ?_, fun g hgm v hv => ?_⟩
  · obtain ⟨u, hu, hv'⟩ := ht v hv
    exact hR u hu v hv'
  · obtain ⟨u, hu, hv'⟩ := hg g hgm v hv
    exact hR u hu v hv'

/-- **The description of `lsemStepN` writes within its destination and reads within `X`.** -/
theorem symN_within (x : LinstrR) (R : String → STerm) (hR : SrcsIn E X x R) :
    RWithin E X x (symN x R) := by
  unfold symN
  split <;> (repeat' split) <;>
    first
    | exact trivial
    | rfl
    | (refine within_use hR (fun v hv => ?_) (fun g hg v hv => ?_) <;>
        simp only [useNames, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          exists_eq_or_imp, exists_eq_left, STerm.varsT, SG.varsT, List.mem_append] at * <;>
        grind)

/-- **The description of `lsemStepSh` writes within its destination and reads within
    `X`.** -/
theorem symSh_within (x : LinstrR) (R : String → STerm) (hR : SrcsIn E X x R) :
    RWithin E X x (symSh x R) := by
  unfold symSh
  split
  · rename_i d a n h
    obtain ⟨opn, rfl⟩ := sarStruct?_shape h
    exact within_set hR (fun v hv => ⟨a, by simp, by simpa [STerm.varsT] using hv⟩)
      (fun g hg => by simp at hg)
  · exact symN_within x R hR

/-- The closing step for the three-source arms of `symMC`. -/
private theorem within_set3 {d opn a b c : String} {R : String → STerm}
    (hR : SrcsIn E X (.Lopn [.reg d] opn [.reg a, .reg b, .reg c]) R) {t : STerm}
    (ht : ∀ v ∈ t.varsT E, v ∈ (R a).varsT E ∨ v ∈ (R b).varsT E ∨ v ∈ (R c).varsT E) :
    RWithin E X (.Lopn [.reg d] opn [.reg a, .reg b, .reg c])
      (ROut.set d t [.eqW (R a) (R b), .wid (R c) 1]) := by
  refine within_set hR (fun v hv => ?_) (fun g hg v hv => ?_)
  · rcases ht v hv with h | h | h
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩
    · exact ⟨c, by simp, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [SG.varsT, List.mem_append] at hv
    · rcases hv with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · exact ⟨c, by simp, hv⟩

/-- **The description of `lsemStepMC` writes within its destination and reads within
    `X`.** -/
theorem symMC_within (x : LinstrR) (R : String → STerm) (hR : SrcsIn E X x R) :
    RWithin E X x (symMC x R) := by
  unfold symMC
  split
  · rename_i d a b h
    obtain ⟨opn, rfl⟩ := mulhiStruct?_shape h
    refine within_set hR (fun v hv => ?_) (fun g hg v hv => ?_)
    · simp only [STerm.varsT, List.mem_append] at hv
      rcases hv with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp only [SG.varsT, List.mem_append] at hv
      rcases hv with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp, h⟩
  · split
    · rename_i d a b c h
      obtain ⟨opn, rfl⟩ := adcxStruct?_shape h
      exact within_set3 hR fun v hv => by
        simp only [STerm.varsT, List.mem_append] at hv
        rcases hv with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · split
      · rename_i d a b c h
        obtain ⟨opn, rfl⟩ := adcxhiStruct?_shape h
        exact within_set3 hR fun v hv => by
          simp only [STerm.varsT, List.mem_append] at hv
          rcases hv with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · split
        · rename_i d a b c h
          obtain ⟨opn, rfl⟩ := sbbStruct?_shape h
          exact within_set3 hR fun v hv => by
            simp only [STerm.varsT, List.mem_append] at hv
            rcases hv with (h | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        · split
          · rename_i d a b c h
            obtain ⟨opn, rfl⟩ := sbbhiStruct?_shape h
            exact within_set3 hR fun v hv => by
              simp only [STerm.varsT, List.mem_append] at hv
              rcases hv with (h | h) | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr h)
          · exact symSh_within x R hR

/-- **The description of `lsemStepCast` writes within its destination and reads within
    `X`.** -/
theorem symCast_within (i : LinstrRT) (R : String → STerm) (hR : SrcsIn E X i.1 R) :
    RWithin E X i.1 (symCast i R) := by
  unfold symCast
  split
  · split
    · rename_i d n w' h _
      obtain ⟨opn, he⟩ := movImmStruct?_shape h
      rw [he]
      exact ⟨dst_mem, fun v hv => by simp [STerm.varsT] at hv, fun g hg => by simp at hg⟩
    · exact symMC_within i.1 R hR
  · rename_i d a h
    split
    · exact symMC_within i.1 R hR
    · obtain ⟨opn, he⟩ := castStruct?_shape h
      rw [he] at hR ⊢
      exact within_set hR (fun v hv => ⟨a, by simp, by simpa [castT, STerm.varsT] using hv⟩)
        (fun g hg => by simp at hg)

/-- The word and the guards of an operand read at width `64` read the names of the
    operand. -/
theorem symOp64_vars {R : String → STerm} {o : LOperand} {t : STerm} {g : List SG}
    (h : symOp64 R o = some (t, g)) :
    (∀ v ∈ t.varsT E, ∃ u ∈ opNames o, v ∈ (R u).varsT E) ∧
      ∀ g' ∈ g, ∀ v ∈ g'.varsT E, ∃ u ∈ opNames o, v ∈ (R u).varsT E := by
  cases o with
  | reg r =>
      simp only [symOp64, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun v hv => ⟨r, by simp [opNames], hv⟩, fun g' hg' v hv => ?_⟩
      simp only [List.mem_singleton] at hg'
      subst hg'
      exact ⟨r, by simp [opNames], by simpa [SG.varsT] using hv⟩
  | imm n =>
      simp only [symOp64, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun v hv => by simp [STerm.varsT] at hv, fun g' hg' => by simp at hg'⟩
  | arr _ _ => cases h
  | arrIdx _ _ _ => cases h

/-- The lift of a register-file description of an instruction that is no compare, no
    register copy and writes no array by `storeHit?`. -/
theorem liftR_within {i : LinstrRM} {ss : SSt} {o : ROut} (hi : OneDst i)
    (hreg : regDefs i = defNames i.1) (hX : ReadsIn E X (· ∈ useNames i.1) ss)
    (ho : RWithin E X i.1 o) : SWithin E X i ss (liftR ss o) := by
  cases o with
  | set d t gs =>
      obtain ⟨hd, ht, hg⟩ := ho
      have hone : ∀ r ∈ defNames i.1, r = d := by
        obtain ⟨x, tag⟩ := i
        cases x with
        | Lopn ds o' ss' =>
            obtain ⟨y, rfl⟩ := hi ds o' ss' rfl
            simp only [defNames, List.flatMap_cons, List.flatMap_nil, opNames, List.append_nil,
              List.mem_singleton] at hd ⊢
            intro r hr
            rw [hr, hd]
        | _ => simp [defNames] at hd
      refine ⟨fun r hr => ?_, fun r hr v hv => ?_, hX.arrs, hX.zf, hX.cf, hX.of, hg⟩
      · rw [SSt.setR_regs, ite_eq_right_iff]
        intro hrd
        exact absurd (hrd ▸ hreg ▸ hd) hr
      · rw [hreg] at hr
        rw [hone r hr, SSt.setR_regs, ite_eq_left rfl] at hv
        exact ht v hv
  | nop =>
      refine ⟨fun r _ => rfl, fun r hr => ?_, hX.arrs, hX.zf, hX.cf, hX.of,
        fun g hg => by simp at hg⟩
      rw [hreg, ho] at hr
      simp at hr
  | fail => trivial
  | unk => trivial

/-! ## 4. The memory layer and the step -/

private theorem aluFlagOp?_shape {i : LinstrRM} {op : AluOp} {a b : LOperand}
    (h : aluFlagOp? i = some (op, a, b)) : ∃ d opn, i.1 = .Lopn [.reg d] opn [a, b] := by
  unfold aluFlagOp? at h
  split at h
  · rename_i d opn a' b' he
    split_ifs at h <;> cases h <;> exact ⟨d, opn, he⟩
  · cases h

/-- The flag word `aluFlT` reads the sources of the instruction and the flag before it. -/
theorem aluFlT_vars {i : LinstrRM} {ss : SSt} (hX : ReadsIn E X (· ∈ useNames i.1) ss)
    (ofl : Bool) : ∀ v ∈ (aluFlT i ss ofl).varsT E, X v := by
  have hold : ∀ v ∈ (if ofl then ss.of else ss.cf).varsT E, X v := by
    cases ofl
    · exact hX.cf
    · exact hX.of
  unfold aluFlT
  split
  · rename_i op a b h
    obtain ⟨d, opn, he⟩ := aluFlagOp?_shape h
    have hsrc : ∀ o ∈ [a, b], ∀ (t : STerm) (g : List SG), symOp64 ss.regs o = some (t, g) →
        ∀ v ∈ t.varsT E, X v := by
      intro o ho t g hs v hv
      obtain ⟨u, hu, hv'⟩ := (symOp64_vars hs).1 v hv
      exact hX.regs u (by rw [he]; exact mem_useNames_of ho hu) v hv'
    split
    · rename_i ta ga tb gb hta htb
      have hA := hsrc a (by simp) _ _ hta
      have hB := hsrc b (by simp) _ _ htb
      have hT : ∀ x y : STerm, (∀ v ∈ x.varsT E, X v) → (∀ v ∈ y.varsT E, X v) →
          ∀ v ∈ (STerm.aluF op ofl x y (if ofl then ss.of else ss.cf)).varsT E, X v := by
        intro x y hx hy v hv
        simp only [STerm.varsT, List.mem_append] at hv
        rcases hv with (hv | hv) | hv
        · exact hx v hv
        · exact hy v hv
        · exact hold v hv
      by_cases hsw : (aluSwap i && op != .sub) = true
      · rw [ite_eq_left hsw]
        exact hT _ _ hB hA
      · rw [ite_eq_right hsw]
        exact hT _ _ hA hB
    · exact hold
  · exact hold

/-- **The flags of `withALUFlags` keep the footprint of a memory description.** -/
theorem aluFl_within {i : LinstrRM} {ss : SSt} {o : SOut}
    (hX : ReadsIn E X (· ∈ useNames i.1) ss) (ho : SWithin E X i ss o) :
    SWithin E X i ss (aluFl i ss o) := by
  cases o with
  | ok s gs =>
      obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := ho
      exact ⟨h1, h2, h3, h4, aluFlT_vars hX false, aluFlT_vars hX true, h7⟩
  | fail => trivial
  | unk => trivial

/-- **The memory step writes within `regDefs` and reads within `X`.** -/
theorem symMem_within {i : LinstrRM} {ss : SSt} (hi : OneDst i)
    (h1 : cmpArgs? i = none) (h2 : movRegArgs? i = none)
    (hX : ReadsIn E X (· ∈ useNames i.1) ss) : SWithin E X i ss (symMem i ss) := by
  have hR : SrcsIn E X i.1 ss.regs := fun u hu => hX.regs u hu
  obtain ⟨x, tag⟩ := i
  unfold symMem
  cases tag with
  | load w n =>
      dsimp only
      split
      · rename_i dst base idx h
        obtain ⟨sc, rfl⟩ := loadStruct?_shape h
        have hreg : regDefs (LinstrR.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx sc],
            MemTag.load w n) = [dst] := by
          rw [regDefs_of_none h1 h2 rfl]
          simp [defNames, opNames]
        have hidx : ∀ v ∈ (ss.regs idx).varsT E, X v :=
          hX.regs idx (mem_useNames_of (List.mem_singleton_self _) (by simp [opNames]))
        refine ⟨fun r hr => ?_, fun r hr v hv => ?_, hX.arrs, hX.zf, hX.cf, hX.of,
          fun g hg v hv => ?_⟩
        · rw [hreg, List.mem_singleton] at hr
          rw [SSt.setR_regs, ite_eq_right hr]
        · rw [hreg, List.mem_singleton] at hr
          subst hr
          rw [SSt.setR_regs, ite_eq_left rfl] at hv
          simp only [STerm.varsT, List.mem_append] at hv
          rcases hv with hv | hv
          · exact hX.arrs _ v hv
          · exact hidx v hv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp only [SG.varsT] at hv
          · exact hX.arrs _ v hv
          · exact hidx v hv
      · exact liftR_within hi (regDefs_of_none h1 h2 rfl) hX (symCast_within _ _ hR)
  | store w n =>
      dsimp only
      split
      · rename_i dst base idx val h
        obtain ⟨sc, rfl⟩ := storeStruct?_shape h
        have hreg : regDefs (LinstrR.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx sc, .reg val],
            MemTag.store w n) = [] := by
          simp [regDefs, memRegDefs, h1, h2, storeHit?, storeStruct?]
        have hidx : ∀ v ∈ (ss.regs idx).varsT E, X v :=
          hX.regs idx (mem_useNames_of (o := .arrIdx base idx sc) (by simp) (by simp [opNames]))
        have hval : ∀ v ∈ (ss.regs val).varsT E, X v :=
          hX.regs val (mem_useNames_of (o := .reg val) (by simp) (by simp [opNames]))
        refine ⟨fun r _ => rfl, fun r hr => by simp [hreg] at hr, fun a v hv => ?_, hX.zf,
          hX.cf, hX.of, fun g hg v hv => ?_⟩
        · simp only [SSt.setA] at hv
          split_ifs at hv
          · simp only [SArr.varsT, List.mem_append] at hv
            rcases hv with (hv | hv) | hv
            · exact hX.arrs _ v hv
            · exact hidx v hv
            · exact hval v hv
          · exact hX.arrs a v hv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl <;> simp only [SG.varsT] at hv
          · exact hX.arrs _ v hv
          · exact hidx v hv
          · exact hval v hv
      · rename_i h
        have h3 : storeHit? (x, MemTag.store w n) = none := by simp [storeHit?, h]
        exact liftR_within hi (regDefs_of_none h1 h2 h3) hX (symCast_within _ _ hR)
  | loadC => trivial
  | storeC => trivial
  | zero w n =>
      dsimp only
      split
      · rename_i dst opn a b
        split_ifs with ho
        · subst ho
          have hreg : regDefs (LinstrR.Lopn [.reg dst] "ZEROARR" [.imm a, .imm b],
              MemTag.zero w n) = [] := by
            simp [regDefs, memRegDefs, h1, h2, storeHit?, zeroStruct?]
          refine ⟨fun r _ => rfl, fun r hr => by simp [hreg] at hr, fun a' v hv => ?_, hX.zf,
            hX.cf, hX.of, fun g hg => by simp at hg⟩
          simp only [SSt.setA] at hv
          split_ifs at hv
          · simp [SArr.varsT] at hv
          · exact hX.arrs a' v hv
        · trivial
      · trivial
  | storeImm w n =>
      dsimp only
      split
      · rename_i dst base val k h
        have he := storeImmStruct?_shape h
        subst he
        split_ifs
        · have hreg : regDefs (LinstrR.Lopn [.reg dst] "STOREIMM" [.reg base, .reg val, .imm k],
              MemTag.storeImm w n) = [] := by
            simp [regDefs, memRegDefs, h1, h2, storeHit?, h]
          have hval : ∀ v ∈ (ss.regs val).varsT E, X v :=
            hX.regs val (mem_useNames_of (o := .reg val) (by simp) (by simp [opNames]))
          refine ⟨fun r _ => rfl, fun r hr => by simp [hreg] at hr, fun a v hv => ?_, hX.zf,
            hX.cf, hX.of, fun g hg v hv => ?_⟩
          · simp only [SSt.setA] at hv
            split_ifs at hv
            · simp only [SArr.varsT, STerm.varsT, List.mem_append, List.not_mem_nil,
                or_false] at hv
              rcases hv with hv | hv
              · exact hX.arrs _ v hv
              · exact hval v hv
            · exact hX.arrs a v hv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl <;> simp only [SG.varsT] at hv
            · exact hX.arrs _ v hv
            · exact hval v hv
        · trivial
      · trivial
  | reg cd =>
      exact liftR_within hi (regDefs_of_none h1 h2 rfl) hX (symCast_within _ _ hR)

/-- The registers an operation with destinations `[.reg d]` writes when it is no compare, no
    register copy and writes no array: `[d]`. -/
private theorem regDefs_single {i : LinstrRM} {d opn : String} {srcs : List LOperand}
    (he : i.1 = .Lopn [.reg d] opn srcs) (h1 : cmpArgs? i = none) (h2 : movRegArgs? i = none)
    (h3 : storeHit? i = none) : regDefs i = [d] := by
  rw [regDefs_of_none h1 h2 h3, he]
  simp [defNames, opNames]

/-- **The symbolic step writes within `regDefs` and reads within `X`**, for an instruction
    with one register destination: from a state whose words at the names `useNames` of the
    instruction, arrays and flags read only start registers of `X`, a register outside
    `regDefs i` keeps its word, and every word of a register of `regDefs i`, every array,
    flag and guard after the step reads only start registers of `X`. -/
theorem symStep_within {i : LinstrRM} {ss : SSt} (hi : OneDst i)
    (hX : ReadsIn E X (· ∈ useNames i.1) ss) : SWithin E X i ss (symStep i ss) := by
  unfold symStep
  split
  · rename_i a b hc
    obtain ⟨d, he⟩ := cmpArgs?_shape hc
    have hreg : regDefs i = [] := by simp [regDefs, hc]
    split
    · rename_i ta ga tb gb hta htb
      have hsrc : ∀ o ∈ [a, b], ∀ (t : STerm) (g : List SG), symOp64 ss.regs o = some (t, g) →
          (∀ v ∈ t.varsT E, X v) ∧ ∀ g' ∈ g, ∀ v ∈ g'.varsT E, X v := by
        intro o ho t g hs
        refine ⟨fun v hv => ?_, fun g' hg' v hv => ?_⟩
        · obtain ⟨u, hu, hv'⟩ := (symOp64_vars hs).1 v hv
          exact hX.regs u (by rw [he]; exact mem_useNames_of ho hu) v hv'
        · obtain ⟨u, hu, hv'⟩ := (symOp64_vars hs).2 g' hg' v hv
          exact hX.regs u (by rw [he]; exact mem_useNames_of ho hu) v hv'
      refine ⟨fun r _ => rfl, fun r hr => by simp [hreg] at hr, hX.arrs, fun v hv => ?_, hX.cf,
        hX.of, fun g hg v hv => ?_⟩
      · simp only [SFlag.varsT, List.mem_append] at hv
        rcases hv with hv | hv
        · exact (hsrc a (by simp) _ _ hta).1 v hv
        · exact (hsrc b (by simp) _ _ htb).1 v hv
      · rcases List.mem_append.mp hg with hg | hg
        · exact (hsrc a (by simp) _ _ hta).2 g hg v hv
        · exact (hsrc b (by simp) _ _ htb).2 g hg v hv
    · trivial
  · rename_i hc
    split
    · rename_i dst src hm
      obtain ⟨opn, he⟩ := movRegArgs?_shape hm
      have hreg : regDefs i = [dst] := by
        simp only [regDefs, hc, hm, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
          ite_false, ite_true, he, defNames, List.flatMap_cons, List.flatMap_nil, opNames,
          List.append_nil]
      refine ⟨fun r hr => ?_, fun r hr v hv => ?_, hX.arrs, hX.zf, hX.cf, hX.of,
        fun g hg => by simp at hg⟩
      · rw [hreg, List.mem_singleton] at hr
        rw [SSt.setR_regs, ite_eq_right hr]
      · rw [hreg, List.mem_singleton] at hr
        subst hr
        rw [SSt.setR_regs, ite_eq_left rfl] at hv
        have hs : src ∈ useNames i.1 := by
          rw [he]
          exact mem_useNames_of (o := .reg src) (by simp) (by simp [opNames])
        exact hX.regs src hs v hv
    · rename_i hm
      split
      · trivial
      · split
        · rename_i k l he
          have hreg : regDefs i = [] := by
            obtain ⟨x, tag⟩ := i
            simp only at he
            subst he
            cases tag <;> simp [regDefs, memRegDefs, hc, hm, storeHit?, defNames, storeStruct?,
              zeroStruct?, storeImmStruct?]
          exact ⟨fun r _ => rfl, fun r hr => by simp [hreg] at hr, hX.arrs, hX.zf, hX.cf, hX.of,
            fun g hg => by simp at hg⟩
        · trivial
        · trivial
        · split
          · rename_i op d a b hca
            obtain ⟨opn, he, hop⟩ := carryArgs?_shape hca
            have h3 : storeHit? i = none := by
              refine storeHit?_none_of_opn he ?_ ?_ ?_ <;> intro ho <;> subst ho <;>
                rcases hop with h | h | h | h <;> exact absurd h (by decide +kernel)
            have hreg := regDefs_single he hc hm h3
            have hsrc : ∀ o ∈ [a, b], ∀ (t : STerm) (g : List SG),
                symOp64 ss.regs o = some (t, g) →
                (∀ v ∈ t.varsT E, X v) ∧ ∀ g' ∈ g, ∀ v ∈ g'.varsT E, X v := by
              intro o ho t g hs
              refine ⟨fun v hv => ?_, fun g' hg' v hv => ?_⟩
              · obtain ⟨u, hu, hv'⟩ := (symOp64_vars hs).1 v hv
                exact hX.regs u (by rw [he]; exact mem_useNames_of ho hu) v hv'
              · obtain ⟨u, hu, hv'⟩ := (symOp64_vars hs).2 g' hg' v hv
                exact hX.regs u (by rw [he]; exact mem_useNames_of ho hu) v hv'
            unfold symCarry
            split
            · rename_i ta ga tb gb hta htb
              have hA := (hsrc a (by simp) _ _ hta).1
              have hB := (hsrc b (by simp) _ _ htb).1
              have hG : ∀ g ∈ ga ++ gb, ∀ v ∈ g.varsT E, X v := fun g hg => by
                rcases List.mem_append.mp hg with hg | hg
                · exact (hsrc a (by simp) _ _ hta).2 g hg
                · exact (hsrc b (by simp) _ _ htb).2 g hg
              have hT : ∀ (c : STerm), (∀ v ∈ c.varsT E, X v) →
                  ∀ v ∈ ta.varsT E ++ tb.varsT E ++ c.varsT E, X v := by
                intro c hc' v hv
                simp only [List.mem_append] at hv
                rcases hv with (hv | hv) | hv
                · exact hA v hv
                · exact hB v hv
                · exact hc' v hv
              have hframe : ∀ (t : STerm) r, r ∉ regDefs i → (ss.setR d t).regs r = ss.regs r :=
                fun t r hr => by
                  rw [hreg, List.mem_singleton] at hr
                  rw [SSt.setR_regs, ite_eq_right hr]
              have hwr : ∀ (t : STerm), (∀ v ∈ t.varsT E, X v) →
                  ∀ r ∈ regDefs i, ∀ v ∈ ((ss.setR d t).regs r).varsT E, X v := by
                intro t ht r hr v hv
                rw [hreg, List.mem_singleton] at hr
                subst hr
                rw [SSt.setR_regs, ite_eq_left rfl] at hv
                exact ht v hv
              cases op
              · exact ⟨hframe _, hwr _ (by simpa [STerm.varsT] using hT ss.cf hX.cf), hX.arrs,
                  hX.zf, by simpa [STerm.varsT] using hT ss.cf hX.cf,
                  by simpa [STerm.varsT] using hT ss.cf hX.cf, hG⟩
              · exact ⟨hframe _, hwr _ (by simpa [STerm.varsT] using hT ss.cf hX.cf), hX.arrs,
                  hX.zf, by simpa [STerm.varsT] using hT ss.cf hX.cf,
                  by simpa [STerm.varsT] using hT ss.cf hX.cf, hG⟩
              · exact ⟨hframe _, hwr _ (by simpa [STerm.varsT] using hT ss.cf hX.cf), hX.arrs,
                  hX.zf, by simpa [STerm.varsT] using hT ss.cf hX.cf, hX.of, hG⟩
              · exact ⟨hframe _, hwr _ (by simpa [STerm.varsT] using hT ss.of hX.of), hX.arrs,
                  hX.zf, hX.cf, by simpa [STerm.varsT] using hT ss.of hX.of, hG⟩
            · trivial
          · rename_i hca
            split
            · rename_i w hw
              rcases wideArgs?_shape hw with ⟨d, x, b, rfl, he⟩ | ⟨lo, hi', b, opn, rfl, he⟩
              · have h3 : storeHit? i = none :=
                  storeHit?_none_of_opn he (by decide +kernel) (by decide +kernel)
                    (by decide +kernel)
                have hreg := regDefs_single he hc hm h3
                simp only [symWide]
                split
                · rename_i tb gb htb
                  have hB : ∀ v ∈ tb.varsT E, X v := fun v hv => by
                    obtain ⟨u, hu, hv'⟩ := (symOp64_vars htb).1 v hv
                    exact hX.regs u (by rw [he]; exact mem_useNames_of (by simp) hu) v hv'
                  refine ⟨fun r hr => ?_, fun r hr v hv => ?_, hX.arrs, hX.zf, hX.cf, hX.of,
                    fun g hg v hv => ?_⟩
                  · rw [hreg, List.mem_singleton] at hr
                    rw [SSt.setR_regs, ite_eq_right hr]
                  · rw [hreg, List.mem_singleton] at hr
                    subst hr
                    rw [SSt.setR_regs, ite_eq_left rfl] at hv
                    exact hB v hv
                  · obtain ⟨u, hu, hv'⟩ := (symOp64_vars htb).2 g hg v hv
                    exact hX.regs u (by rw [he]; exact mem_useNames_of (by simp) hu) v hv'
                · trivial
              · obtain ⟨y, hy⟩ := hi _ _ _ he
                simp at hy
            · exact aluFl_within hX (symMem_within hi hc hm hX)

/-- **A step writes only names of `regDefs`**, for an instruction with one register
    destination. -/
theorem symStep_frame {i : LinstrRM} {ss s : SSt} {gs : List SG} (hi : OneDst i)
    (h : symStep i ss = .ok s gs) {r : String} (hr : r ∉ regDefs i) : s.regs r = ss.regs r := by
  have hw := symStep_within (E := #[]) (X := fun _ => True) hi
    ⟨fun _ _ _ _ => trivial, fun _ _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
      fun _ _ => trivial⟩ (ss := ss)
  rw [h] at hw
  exact hw.1 r hr

/-- **The transfer of `ReadsIn` across a step**: when the words of `ss` at the names that the
    instruction reads and at the names of `N` it does not write read within `X`, the words of
    the state after the step at the names of `N` read within `X`, and so do its guards. This
    is the transfer of the register liveness table (`RegionBackend.liveRegNeed`) against the
    symbolic step. -/
theorem symStep_readsIn {i : LinstrRM} {ss s : SSt} {gs : List SG} (hi : OneDst i)
    (h : symStep i ss = .ok s gs) {N : String → Prop}
    (hX : ReadsIn E X (fun r => r ∈ useNames i.1 ∨ (N r ∧ r ∉ regDefs i)) ss) :
    ReadsIn E X N s ∧ ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v := by
  have hw := symStep_within (E := E) (X := X) hi (hX.mono fun r hr => Or.inl hr)
  rw [h] at hw
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  refine ⟨⟨fun r hr v hv => ?_, h3, h4, h5, h6⟩, h7⟩
  by_cases hd : r ∈ regDefs i
  · exact h2 r hd v hv
  · rw [h1 r hd] at hv
    exact hX.regs r (Or.inr ⟨hr, hd⟩) v hv

/-! ## 5. Runs -/

/-- The name set `N` before the instruction `i` covers the names it reads and the names of
    `N'` after it that it does not write: the transfer of a liveness table at `i`. -/
def Transfer (i : LinstrRM) (N N' : String → Prop) : Prop :=
  ∀ r, r ∈ useNames i.1 ∨ (N' r ∧ r ∉ regDefs i) → N r

/-- **The transfer of `ReadsIn` across a run**: along the instructions of `is`, with the
    name sets `N j` before the instruction at offset `j` and `N (j + 1)` after it related by
    `Transfer`, a successful run from a state whose words at the names of `N 0` read within
    `X` ends in a state whose words at the names of `N is.length` read within `X`, and its
    guards read within `X`. -/
theorem symRun_readsIn : ∀ (is : List LinstrRM) (N : Nat → String → Prop) {ss s : SSt}
    {gs : List SG}, (∀ i ∈ is, OneDst i) →
    (∀ (j : Nat) (h : j < is.length), Transfer is[j] (N j) (N (j + 1))) →
    ReadsIn E X (N 0) ss → symRun is ss = .ok s gs →
    ReadsIn E X (N is.length) s ∧ ∀ g ∈ gs, ∀ v ∈ g.varsT E, X v
  | [], N, ss, s, gs, _, _, hX, h => by
      simp only [symRun, SOut.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hX, fun g hg => by simp at hg⟩
  | i :: is, N, ss, s, gs, hone, htr, hX, h => by
      simp only [symRun] at h
      split at h
      · rename_i ss1 g1 h1
        split at h
        · rename_i ss2 g2 h2
          simp only [SOut.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hX1 := symStep_readsIn (hone i List.mem_cons_self) h1
            (hX.mono fun r hr => htr 0 (by simp) r hr)
          have ih := symRun_readsIn is (fun j => N (j + 1))
            (fun i' hi' => hone i' (List.mem_cons_of_mem _ hi'))
            (fun j hj => htr (j + 1) (by simp; omega)) hX1.1 h2
          refine ⟨by simpa using ih.1, fun g hg => ?_⟩
          rcases List.mem_append.mp hg with hg | hg
          · exact hX1.2 g hg
          · exact ih.2 g hg
        · cases h
        · cases h
      · cases h
      · cases h

/-! ## 6. The shadow instructions of calls -/

/-- The register-file description of a shadow instruction fails. -/
theorem symN_callMnem {dst opn : String} {srcs : List LOperand} (h : LprogIsaProcs.CallMnem opn)
    (R : String → STerm) : symN (.Lopn [.reg dst] opn srcs) R = .fail := by
  have hb : binOk (stripWidthTag opn) = false := by
    simp only [binOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h.strip_ne _ (by decide), h.strip_ne _ (by decide)⟩,
      h.strip_ne _ (by decide)⟩, h.strip_ne _ (by decide)⟩, h.strip_ne _ (by decide)⟩,
      h.strip_ne _ (by decide)⟩, h.strip_ne _ (by decide)⟩, h.strip_ne _ (by decide)⟩,
      h.strip_ne _ (by decide)⟩
  have h1 := h.strip_ne "CMOV" (by decide)
  have h2 := h.strip_ne "MOV" (by decide)
  have h3 := h.strip_ne "NEG" (by decide)
  have h4 := h.strip_ne "LEA" (by decide)
  have h5 : cmpOfName? (stripWidthTag opn) = none :=
    cmpOfName?_eq_none (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide))
      (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide))
      (h.strip_ne _ (by decide))
  have h6 := LprogIsaProcs.immShiftMnem?_callMnem h
  unfold symN
  split <;> first
    | rfl
    | (rename_i heq
       cases heq
       try simp only [h1, h2, h3, h4, h5, h6, hb, ite_false, Option.isSome_none,
         Bool.false_eq_true]
       repeat' (first | rfl | split))

/-- **The symbolic step of a shadow instruction of a call has no description**: it fails or
    is outside the fragment, at every memory tag and from every state. -/
theorem symStep_shadowCall {i : LinstrRM} (h : LprogIsa.shadowCall? i.1 ≠ none) (ss : SSt)
    (s : SSt) (gs : List SG) : symStep i ss ≠ .ok s gs := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨dst, opn, srcs, rfl, hm⟩ := LprogIsaProcs.shadowCall?_wire h
  have e1 : cmpArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold cmpArgs?
    split <;> first
      | rfl
      | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide +kernel)))
  have e2 : movRegArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold movRegArgs?
    split
    · next heq =>
      cases heq
      obtain ⟨t, ht⟩ := hm
      rw [ite_eq_right (LprogIsaProcs.CallMnem.strip_ne ⟨t, ht⟩ "MOV" (by decide)),
        copyQ_eq_false_of_toList ht (by decide)]
      rfl
    · rfl
  have e3 : carryArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold carryArgs?
    split
    · next heq =>
      cases heq
      simp only [hm.ne (withWidthTag 64 "ADC") (by decide +kernel),
        hm.ne (withWidthTag 64 "SBB") (by decide +kernel),
        hm.ne (withWidthTag 64 "ADCX") (by decide +kernel),
        hm.ne (withWidthTag 64 "ADOX") (by decide +kernel), ite_false]
    · rfl
  have e4 : wideArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold wideArgs?
    split
    · next heq =>
      cases heq
      exact ite_eq_right (hm.ne _ (by decide +kernel))
    · next heq =>
      cases heq
    · rfl
  have eN : ∀ R, symN (.Lopn [.reg dst] opn srcs) R = .fail := symN_callMnem hm
  have eSh : ∀ R, symSh (.Lopn [.reg dst] opn srcs) R = .fail := by
    intro R
    have e6 : JasminLsemShift.sarStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemShift.sarStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    simp only [symSh, e6, eN]
  have eMC : ∀ R, symMC (.Lopn [.reg dst] opn srcs) R = .fail := by
    intro R
    have m1 : JasminLsemMulCarry.mulhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemMulCarry.mulhiStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    have m2 : JasminLsemMulCarry.adcxStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemMulCarry.adcxStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    have m3 : JasminLsemMulCarry.adcxhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemMulCarry.adcxhiStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    have m4 : JasminLsemMulCarry.sbbStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemMulCarry.sbbStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    have m5 : JasminLsemMulCarry.sbbhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold JasminLsemMulCarry.sbbhiStruct?
      split <;> first | rfl |
        (rename_i heq; cases heq; exact ite_eq_right (hm.strip_ne _ (by decide)))
    simp only [symMC, m1, m2, m3, m4, m5, eSh]
  have eCast : ∀ (cd : Option Nat) R, symCast (.Lopn [.reg dst] opn srcs, cd) R = .fail := by
    intro cd R
    have c1 : castStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold castStruct?
      split
      · next heq =>
        cases heq
        refine ite_eq_right ?_
        simp only [hm.ne "ZEROEXT" (by decide), hm.ne "TRUNC" (by decide),
          hm.ne "CASTW_32_32" (by decide), hm.ne "CASTW_32_64" (by decide),
          hm.ne "CASTW_64_32" (by decide), hm.ne "CASTW_64_64" (by decide),
          hm.ne "CASTW_64_16" (by decide), hm.ne "CASTW_16_64" (by decide),
          hm.ne "CASTW_16_16" (by decide), hm.ne "CASTW_16_32" (by decide),
          hm.ne "CASTW_32_16" (by decide), or_self, not_false_eq_true]
      · rfl
    have c2 : movImmStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold movImmStruct?
      split
      · next heq =>
        cases heq
        exact ite_eq_right (fun hc => hm.strip_ne "MOV" (by decide)
          (JasminLsemCast.stripWidthTag_of_isMovImm hc))
      · rfl
    simp only [symCast, c1, c2, eMC]
  have eMem : symMem (LinstrR.Lopn [.reg dst] opn srcs, tag) ss = .fail ∨
      symMem (LinstrR.Lopn [.reg dst] opn srcs, tag) ss = .unk := by
    have l1 : loadStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold loadStruct?
      split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide)))
    have l2 : storeStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold storeStruct?
      split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide)))
    have l3 : storeImmStruct? (.Lopn [.reg dst] opn srcs) = none := by
      unfold storeImmStruct?
      split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide)))
    unfold symMem
    cases tag with
    | load w n => left; simp only [l1, eCast, liftR]
    | store w n => left; simp only [l2, eCast, liftR]
    | loadC => right; rfl
    | storeC => right; rfl
    | zero w n =>
        dsimp only
        split
        · next heq =>
          cases heq
          left
          exact ite_eq_right (hm.ne "ZEROARR" (by decide))
        · right; rfl
    | storeImm w n => left; simp only [l3]
    | reg cd => left; simp only [eCast, liftR]
  unfold symStep
  simp only [e1, e2, e3, e4, flagCondCC?]
  rcases eMem with e | e <;> rw [e] <;> simp [aluFl]

end Layers

end CatCrypt.Crypto.SecureCompilation.X86Backend.SymFootprint
