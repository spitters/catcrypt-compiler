/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts
public import CatCrypt.Crypto.SecureCompilation.VIR.Dialects.PackedSlotState

/-!
# A packed-state twin of the flag-aware symbolic executor

`Ed25519PointAddShippedProof.symStep2` keeps the register and cell nodes in association
lists keyed by name (`SSt`), so every read is a scan with a `String` comparison per entry
and every write rebuilds the list. This module carries the same executor over a packed
state: the nodes of the registers and cells are the slots of one natural number
(`VIR.PackedSlotState`), addressed by index.

## Locations and annotations

A half check fixes a location list `locs`; the slot of a location is its position in
`locs`. Each instruction is paired with an annotation, the list of slot indices of its
register and cell operands in the order `ops` gives:

| instruction                  | annotation            |
|------------------------------|-----------------------|
| `mov d (reg r)`              | `[d, r]`              |
| `mov d (imm n)`              | `[d]`                 |
| `loadMem d b o`              | `[d, (b, o)]`         |
| `storeMem b o (reg r)`       | `[(b, o), r]`         |
| `storeMem b o (imm n)`       | `[(b, o)]`            |
| `mulx hd ld (reg a) (reg b)` | `[hd, ld, a, b]`      |
| `imul d (reg r)`             | `[d, r]`              |
| `xor_ d (reg r)`             | `[d, r]`              |
| `or_ d (reg r)`              | `[d, r]`              |
| `bt a (imm k)`               | `[a]`                 |
| `setc d`                     | `[d]`                 |
| `test a (reg b)`             | `[a, b]`              |
| `cmovne d (reg r)`           | `[d, r]`              |
| `adcx d (reg r)`             | `[d, r]`              |
| `adcxMem d b o`              | `[d, (b, o)]`         |

`annOK` checks an annotation pointwise: the entry of `locs` at each annotated index is the
operand's location. The executor itself reads and writes slots only; it compares no names.
A read of an unmapped slot adds the leaf node of the location, named from the instruction,
as `rdR` and `rdM` do. A write of a node that does not fit a slot makes the step `none`.

## Main results

* `symStep2P_sim`, `symRun2P_sim`: a successful packed step (block) is a successful
  `symStep2` (`symRun2`) with the same node table and flags, and the packed state again
  represents the name-keyed one on `locs`.
* `partCheck2P_imp`: a packed part check implies the part check `partCheck2`.
* `partCheck2P_sound`: the conclusion of `partCheck2_sound` from a packed part check.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PackedSlotState (pget pset pget_pset_self pget_pset_ne
  pget_zero Represents Represents.set Represents.get injOnP_idxOf)

deriving instance DecidableEq for Loc

/-! ## 1. Locations of operands and annotations -/

/-- The register and cell operands of an instruction, in annotation order; empty outside
    the forms `symStep2` handles. -/
def ops : JInstr 64 → List Loc
  | .mov d (.reg r) => [.reg d, .reg r]
  | .mov d (.imm _) => [.reg d]
  | .loadMem d b o => [.reg d, .cell b o]
  | .storeMem b o (.reg r) => [.cell b o, .reg r]
  | .storeMem b o (.imm _) => [.cell b o]
  | .mulx hd ld (.reg a) (.reg b) => [.reg hd, .reg ld, .reg a, .reg b]
  | .imul d (.reg r) => [.reg d, .reg r]
  | .xor_ d (.reg r) => [.reg d, .reg r]
  | .or_ d (.reg r) => [.reg d, .reg r]
  | .bt a (.imm _) => [.reg a]
  | .setc d => [.reg d]
  | .test a (.reg b) => [.reg a, .reg b]
  | .cmovne d (.reg r) => [.reg d, .reg r]
  | .adcx d (.reg r) => [.reg d, .reg r]
  | .adcxMem d b o => [.reg d, .cell b o]
  | _ => []

/-- Every location of `ls` is at its annotated index of `locs`, and the two lists have the
    same length. -/
def annOK (locs : List Loc) : List Loc → List Nat → Bool
  | [], [] => true
  | ℓ :: ls, k :: ks => decide (locs[k]? = some ℓ) && annOK locs ls ks
  | _, _ => false

/-- Every instruction of a block is annotated correctly. -/
def annsOK (locs : List Loc) : List (JInstr 64) → List (List Nat) → Bool
  | [], [] => true
  | i :: is, a :: as => annOK locs (ops i) a && annsOK locs is as
  | _, _ => false

/-! ## 2. The packed state and its relation to `SSt2` -/

/-- The packed flag-aware symbolic state: the register and cell nodes as one packed slot
    state, the node of the carry word, and the node whose zero-ness is the zero flag. -/
structure SSt2P where
  /-- The register and cell nodes, slot `k` for location `k` of the location list. -/
  pk : Nat := 0
  /-- The node of the carry word, absent when the carry flag is unknown. -/
  cfw : Option Nat := none
  /-- The node whose zero-ness is the zero flag, absent when it is unknown. -/
  zfn : Option Nat := none

/-- The packed state `σ` represents the name-keyed state `S` on the locations of `locs`,
    each location at its position. -/
def PRep (locs : List Loc) (σ : Nat) (S : SSt) : Prop :=
  Represents (fun ℓ => locs.idxOf ℓ) (fun ℓ => ℓ ∈ locs) σ (fun ℓ => ℓ.node S)

/-- The packed state represents the register and cell nodes of `S` on `locs` and carries
    the same flag nodes. -/
def PRel2 (locs : List Loc) (P : SSt2P) (S : SSt2) : Prop :=
  PRep locs P.pk S.base ∧ P.cfw = S.cfw ∧ P.zfn = S.zfn

theorem idxOf_of_getElem? {locs : List Loc} (hnd : locs.Nodup) {k : Nat} {ℓ : Loc}
    (h : locs[k]? = some ℓ) : locs.idxOf ℓ = k := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact hnd.idxOf_getElem k hk

theorem PRep.get {locs : List Loc} (hnd : locs.Nodup) {σ : Nat} {S : SSt}
    (hR : PRep locs σ S) {k : Nat} {ℓ : Loc} (h : locs[k]? = some ℓ) :
    pget σ k = ℓ.node S := by
  have := Represents.get hR ℓ (List.mem_of_getElem? h)
  rwa [idxOf_of_getElem? hnd h] at this

theorem Loc.node_put (S : SSt) (ℓ e : Loc) (x : Nat) :
    e.node (S.put ℓ x) = if e = ℓ then some x else e.node S := by
  cases ℓ <;> cases e <;> simp [Loc.node, SSt.put, SSt.setR, SSt.setM, lk_insK]

theorem PRep.put {locs : List Loc} (hnd : locs.Nodup) {σ : Nat} {S : SSt}
    (hR : PRep locs σ S) {k : Nat} {ℓ : Loc} (h : locs[k]? = some ℓ) {x : Nat}
    (hx : x + 1 < PackedSlotState.B) : PRep locs (pset σ k x) (S.put ℓ x) := by
  have H := hR.set (injOnP_idxOf locs) ℓ (List.mem_of_getElem? h) x hx
  rw [idxOf_of_getElem? hnd h] at H
  intro e he
  show e.node (S.put ℓ x) = _
  rw [Loc.node_put]
  exact H e he

/-! ## 3. The packed executor -/

/-- The node at slot `k`, added as the leaf `t` when the slot is unmapped. -/
def rdP (T : Tb) (σ k : Nat) (t : Nd) : Tb × Nat :=
  match pget σ k with
  | some x => (T, x)
  | none => T.add t

/-- The packed state with slot `k` set to `x` and flag nodes `c` and `z`; `none` when
    `x + 1` does not fit a slot. -/
def putP (T : Tb) (σ k x : Nat) (c z : Option Nat) : Option (Tb × SSt2P) :=
  if x + 1 < PackedSlotState.B then some (T, ⟨pset σ k x, c, z⟩) else none

theorem rdP_reg {locs : List Loc} (hnd : locs.Nodup) {σ : Nat} {S : SSt}
    (hR : PRep locs σ S) {k : Nat} {r : String} (h : locs[k]? = some (.reg r)) (T : Tb) :
    rdP T σ k (.reg r) = rdR T S r := by
  unfold rdP rdR
  rw [PRep.get hnd hR h]
  rfl

theorem rdP_cell {locs : List Loc} (hnd : locs.Nodup) {σ : Nat} {S : SSt}
    (hR : PRep locs σ S) {k : Nat} {b : String} {o : Int} (h : locs[k]? = some (.cell b o))
    (T : Tb) : rdP T σ k (.cell b o) = rdM T S b o := by
  unfold rdP rdM
  rw [PRep.get hnd hR h]
  rfl

theorem putP_sim {locs : List Loc} (hnd : locs.Nodup) {σ : Nat} {S : SSt}
    (hR : PRep locs σ S) {k : Nat} {ℓ : Loc} (hk : locs[k]? = some ℓ) {T T' : Tb}
    {x : Nat} {c z : Option Nat} {P' : SSt2P} (h : putP T σ k x c z = some (T', P')) :
    T' = T ∧ P' = ⟨pset σ k x, c, z⟩ ∧ PRep locs (pset σ k x) (S.put ℓ x) := by
  unfold putP at h
  split_ifs at h with hx
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm, hR.put hnd hk hx⟩

/-- One annotated instruction on the packed state: `symStep2` with every register and cell
    access at the annotated slot; `none` outside the handled forms, on an annotation of the
    wrong length, and on a node that does not fit a slot. -/
def symStep2P (T : Tb) (S : SSt2P) : JInstr 64 → List Nat → Option (Tb × SSt2P)
  | .mov _ (.reg r), [kd, kr] =>
      match rdP T S.pk kr (.reg r) with
      | (T₁, x) => putP T₁ S.pk kd x S.cfw S.zfn
  | .mov _ (.imm n), [kd] =>
      match T.addN (.lit n) with
      | (T₁, x) => putP T₁ S.pk kd x S.cfw S.zfn
  | .loadMem _ b o, [kd, kc] =>
      match rdP T S.pk kc (.cell b o) with
      | (T₁, x) => putP T₁ S.pk kd x S.cfw S.zfn
  | .storeMem _ _ (.reg r), [kc, kr] =>
      match rdP T S.pk kr (.reg r) with
      | (T₁, x) => putP T₁ S.pk kc x S.cfw S.zfn
  | .storeMem _ _ (.imm n), [kc] =>
      match T.addN (.lit n) with
      | (T₁, x) => putP T₁ S.pk kc x S.cfw S.zfn
  | .mulx _ _ (.reg a) (.reg b), [kh, kl, ka, kb] =>
      if kh = kl then none else
        match rdP T S.pk ka (.reg a) with
        | (T₁, x) =>
          match rdP T₁ S.pk kb (.reg b) with
          | (T₂, y) =>
            match T₂.addN (.mul x y) with
            | (T₃, lo) =>
              match T₃.addN (.mulhi x y) with
              | (T₄, hi) =>
                if lo + 1 < PackedSlotState.B then
                  putP T₄ (pset S.pk kl lo) kh hi S.cfw S.zfn
                else none
  | .imul d (.reg r), [kd, kr] =>
      match rdP T S.pk kd (.reg d) with
      | (T₁, x) =>
        match rdP T₁ S.pk kr (.reg r) with
        | (T₂, y) =>
          match T₂.addN (.mul x y) with
          | (T₃, z) => putP T₃ S.pk kd z none none
  | .xor_ d (.reg r), [kd, kr] =>
      match rdP T S.pk kd (.reg d) with
      | (T₁, x) =>
        match rdP T₁ S.pk kr (.reg r) with
        | (T₂, y) =>
          match T₂.addN (.xor x y) with
          | (T₃, z) => putP T₃ S.pk kd z none none
  | .or_ d (.reg r), [kd, kr] =>
      match rdP T S.pk kd (.reg d) with
      | (T₁, x) =>
        match rdP T₁ S.pk kr (.reg r) with
        | (T₂, y) =>
          match internN T₂ (orNE (.nd x) (.nd y)) with
          | (T₃, z) => putP T₃ S.pk kd z none none
  | .bt a (.imm k), [ka] =>
      if k = 0 then
        match rdP T S.pk ka (.reg a) with
        | (T₁, x) =>
          match internN T₁ (.and (.nd x) (.lit 1)) with
          | (T₂, c) => some (T₂, { S with cfw := some c })
      else none
  | .setc _, [kd] =>
      match S.cfw with
      | none => none
      | some c => putP T S.pk kd c S.cfw S.zfn
  | .test a (.reg b), [ka, kb] =>
      match rdP T S.pk ka (.reg a) with
      | (T₁, x) =>
        match rdP T₁ S.pk kb (.reg b) with
        | (T₂, y) =>
          match T₂.addN (.and x y) with
          | (T₃, z) => some (T₃, { pk := S.pk, cfw := none, zfn := some z })
  | .cmovne d (.reg r), [kd, kr] =>
      match S.zfn with
      | none => none
      | some z =>
        match rdP T S.pk kr (.reg r) with
        | (T₁, x) =>
          match rdP T₁ S.pk kd (.reg d) with
          | (T₂, y) =>
            match internN T₂ (selNE (.nd z) (.nd x) (.nd y)) with
            | (T₃, w) => putP T₃ S.pk kd w S.cfw S.zfn
  | .adcx d (.reg r), [kd, kr] =>
      match S.cfw with
      | none => none
      | some c =>
        match rdP T S.pk kd (.reg d) with
        | (T₁, x) =>
          match rdP T₁ S.pk kr (.reg r) with
          | (T₂, y) =>
            match internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with
            | (T₃, z) =>
              match internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
                  (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with
              | (T₄, w) => putP T₄ S.pk kd z (some w) S.zfn
  | .adcxMem d b o, [kd, kc] =>
      match S.cfw with
      | none => none
      | some c =>
        match rdP T S.pk kd (.reg d) with
        | (T₁, x) =>
          match rdP T₁ S.pk kc (.cell b o) with
          | (T₂, y) =>
            match internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with
            | (T₃, z) =>
              match internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
                  (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with
              | (T₄, w) => putP T₄ S.pk kd z (some w) S.zfn
  | _, _ => none

/-- An annotated block on the packed state; `none` when the block and its annotations
    differ in length. -/
def symRun2P : Tb → SSt2P → List (JInstr 64) → List (List Nat) → Option (Tb × SSt2P)
  | T, S, [], [] => some (T, S)
  | T, S, i :: is, a :: as =>
    match symStep2P T S i a with
    | some (T₁, S₁) => symRun2P T₁ S₁ is as
    | none => none
  | _, _, _, _ => none

/-! ## 4. Simulation -/

theorem symStep2P_sim {locs : List Loc} (hnd : locs.Nodup) {T T' : Tb} {S : SSt2}
    {P P' : SSt2P} (hR : PRel2 locs P S) (i : JInstr 64) (ann : List Nat)
    (ha : annOK locs (ops i) ann = true) (h : symStep2P T P i ann = some (T', P')) :
    ∃ S', symStep2 T S i = some (T', S') ∧ PRel2 locs P' S' := by
  obtain ⟨hp, hc, hz⟩ := hR
  cases i
  case mov d src =>
    cases src with
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp hr] at h
      rcases e1 : rdR T S.base r with ⟨T₁, x⟩
      rw [e1] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ S with base := S.base.setR d x }, by simp only [symStep2, e1], hq, hc, hz⟩
    | imm n =>
      rcases ann with _ | ⟨kd, _ | ⟨_, _⟩⟩ <;> simp [ops, annOK] at ha
      simp only [symStep2P] at h
      rcases e1 : T.addN (.lit n) with ⟨T₁, x⟩
      rw [e1] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp ha h
      exact ⟨{ S with base := S.base.setR d x }, by simp only [symStep2, e1], hq, hc, hz⟩
  case loadMem d b o =>
    rcases ann with _ | ⟨kd, _ | ⟨kc, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
    obtain ⟨hd, hm⟩ := ha
    simp only [symStep2P, rdP_cell hnd hp hm] at h
    rcases e1 : rdM T S.base b o with ⟨T₁, x⟩
    rw [e1] at h
    obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
    exact ⟨{ S with base := S.base.setR d x }, by simp only [symStep2, e1], hq, hc, hz⟩
  case storeMem b o src =>
    cases src with
    | reg r =>
      rcases ann with _ | ⟨kc, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hm, hr⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp hr] at h
      rcases e1 : rdR T S.base r with ⟨T₁, x⟩
      rw [e1] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hm h
      exact ⟨{ S with base := S.base.setM (b, o) x }, by simp only [symStep2, e1], hq, hc, hz⟩
    | imm n =>
      rcases ann with _ | ⟨kc, _ | ⟨_, _⟩⟩ <;> simp [ops, annOK] at ha
      simp only [symStep2P] at h
      rcases e1 : T.addN (.lit n) with ⟨T₁, x⟩
      rw [e1] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp ha h
      exact ⟨{ S with base := S.base.setM (b, o) x }, by simp only [symStep2, e1], hq, hc, hz⟩
  case mulx hd ld a b =>
    cases a with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg a =>
      cases b with
      | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
      | reg b =>
        rcases ann with _ | ⟨kh, _ | ⟨kl, _ | ⟨ka, _ | ⟨kb, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
          simp [ops, annOK] at ha
        obtain ⟨hh, hl, ha', hb'⟩ := ha
        simp only [symStep2P, rdP_reg hnd hp ha', rdP_reg hnd hp hb'] at h
        rcases e1 : rdR T S.base a with ⟨T₁, x⟩
        rcases e2 : rdR T₁ S.base b with ⟨T₂, y⟩
        rcases e3 : T₂.addN (.mul x y) with ⟨T₃, lo⟩
        rcases e4 : T₃.addN (.mulhi x y) with ⟨T₄, hi⟩
        simp only [e1, e2, e3, e4] at h
        split_ifs at h with hkl hlo
        have hne : hd ≠ ld := by
          rintro rfl
          exact hkl ((idxOf_of_getElem? hnd hh).symm.trans (idxOf_of_getElem? hnd hl))
        obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd (hp.put hnd hl hlo) hh h
        exact ⟨{ S with base := (S.base.setR ld lo).setR hd hi },
          by simp only [symStep2, ite_eq_right hne, e1, e2, e3, e4], hq, hc, hz⟩
  case imul d src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp hd, rdP_reg hnd hp hr] at h
      rcases e1 : rdR T S.base d with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base r with ⟨T₂, y⟩
      rcases e3 : T₂.addN (.mul x y) with ⟨T₃, z⟩
      simp only [e1, e2, e3] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ base := S.base.setR d z, cfw := none, zfn := none },
        by simp only [symStep2, symBin, e1, e2, e3], hq, rfl, rfl⟩
  case xor_ d src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp hd, rdP_reg hnd hp hr] at h
      rcases e1 : rdR T S.base d with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base r with ⟨T₂, y⟩
      rcases e3 : T₂.addN (.xor x y) with ⟨T₃, z⟩
      simp only [e1, e2, e3] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ base := S.base.setR d z, cfw := none, zfn := none },
        by simp only [symStep2, symBin, e1, e2, e3], hq, rfl, rfl⟩
  case or_ d src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp hd, rdP_reg hnd hp hr] at h
      rcases e1 : rdR T S.base d with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base r with ⟨T₂, y⟩
      rcases e3 : internN T₂ (orNE (.nd x) (.nd y)) with ⟨T₃, z⟩
      simp only [e1, e2, e3] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ base := S.base.setR d z, cfw := none, zfn := none },
        by simp only [symStep2, e1, e2, e3], hq, rfl, rfl⟩
  case bt a src =>
    cases src with
    | reg _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | imm k =>
      rcases ann with _ | ⟨ka, _ | ⟨_, _⟩⟩ <;> simp [ops, annOK] at ha
      simp only [symStep2P, rdP_reg hnd hp ha] at h
      split_ifs at h with hk
      rcases e1 : rdR T S.base a with ⟨T₁, x⟩
      rcases e2 : internN T₁ (.and (.nd x) (.lit 1)) with ⟨T₂, c⟩
      simp only [e1, e2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨{ S with cfw := some c }, by simp only [symStep2, ite_eq_left hk, e1, e2], hp, rfl, hz⟩
  case setc d =>
    rcases ann with _ | ⟨kd, _ | ⟨_, _⟩⟩ <;> simp [ops, annOK] at ha
    simp only [symStep2P, hc, hz] at h
    rcases ec : S.cfw with _ | c
    · simp [ec] at h
    simp only [ec] at h
    obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp ha h
    exact ⟨{ S with base := S.base.setR d c }, by simp only [symStep2, ec], hq, ec.symm, rfl⟩
  case test a src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg b =>
      rcases ann with _ | ⟨ka, _ | ⟨kb, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨ha', hb'⟩ := ha
      simp only [symStep2P, rdP_reg hnd hp ha', rdP_reg hnd hp hb'] at h
      rcases e1 : rdR T S.base a with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base b with ⟨T₂, y⟩
      rcases e3 : T₂.addN (.and x y) with ⟨T₃, z⟩
      simp only [e1, e2, e3, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨{ base := S.base, cfw := none, zfn := some z },
        by simp only [symStep2, e1, e2, e3], hp, rfl, rfl⟩
  case cmovne d src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, hc, hz, rdP_reg hnd hp hd, rdP_reg hnd hp hr] at h
      rcases ez : S.zfn with _ | z
      · simp [ez] at h
      rcases e1 : rdR T S.base r with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base d with ⟨T₂, y⟩
      rcases e3 : internN T₂ (selNE (.nd z) (.nd x) (.nd y)) with ⟨T₃, w⟩
      simp only [ez, e1, e2, e3] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ S with base := S.base.setR d w },
        by simp only [symStep2, ez, e1, e2, e3], hq, rfl, ez.symm⟩
  case adcx d src =>
    cases src with
    | imm _ => rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h
    | reg r =>
      rcases ann with _ | ⟨kd, _ | ⟨kr, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
      obtain ⟨hd, hr⟩ := ha
      simp only [symStep2P, hc, hz, rdP_reg hnd hp hd, rdP_reg hnd hp hr] at h
      rcases ec : S.cfw with _ | c
      · simp [ec] at h
      rcases e1 : rdR T S.base d with ⟨T₁, x⟩
      rcases e2 : rdR T₁ S.base r with ⟨T₂, y⟩
      rcases e3 : internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with ⟨T₃, z⟩
      rcases e4 : internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
          (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with ⟨T₄, w⟩
      simp only [ec, e1, e2, e3, e4] at h
      obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
      exact ⟨{ base := S.base.setR d z, cfw := some w, zfn := S.zfn },
        by simp only [symStep2, ec, e1, e2, e3, e4], hq, rfl, rfl⟩
  case adcxMem d b o =>
    rcases ann with _ | ⟨kd, _ | ⟨kc, _ | ⟨_, _⟩⟩⟩ <;> simp [ops, annOK] at ha
    obtain ⟨hd, hm⟩ := ha
    simp only [symStep2P, hc, hz, rdP_reg hnd hp hd, rdP_cell hnd hp hm] at h
    rcases ec : S.cfw with _ | c
    · simp [ec] at h
    rcases e1 : rdR T S.base d with ⟨T₁, x⟩
    rcases e2 : rdM T₁ S.base b o with ⟨T₂, y⟩
    rcases e3 : internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with ⟨T₃, z⟩
    rcases e4 : internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
        (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with ⟨T₄, w⟩
    simp only [ec, e1, e2, e3, e4] at h
    obtain ⟨rfl, rfl, hq⟩ := putP_sim hnd hp hd h
    exact ⟨{ base := S.base.setR d z, cfw := some w, zfn := S.zfn },
      by simp only [symStep2, ec, e1, e2, e3, e4], hq, rfl, rfl⟩
  all_goals (rcases ann with _ | ⟨_, _⟩ <;> simp [ops, annOK, symStep2P] at ha h)

theorem symRun2P_sim {locs : List Loc} (hnd : locs.Nodup) :
    ∀ (blk : List (JInstr 64)) (anns : List (List Nat)) (T T' : Tb) (S : SSt2) (P P' : SSt2P),
      PRel2 locs P S → annsOK locs blk anns = true → symRun2P T P blk anns = some (T', P') →
      ∃ S', symRun2 T S blk = some (T', S') ∧ PRel2 locs P' S'
  | [], [], T, T', S, P, P', hR, _, h => by
      simp only [symRun2P, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨S, rfl, hR⟩
  | [], _ :: _, _, _, _, _, _, _, ha, _ => by simp [annsOK] at ha
  | _ :: _, [], _, _, _, _, _, _, ha, _ => by simp [annsOK] at ha
  | i :: is, a :: as, T, T', S, P, P', hR, ha, h => by
      simp only [annsOK, Bool.and_eq_true] at ha
      simp only [symRun2P] at h
      rcases hs : symStep2P T P i a with _ | ⟨T₁, P₁⟩
      · rw [hs] at h; cases h
      rw [hs] at h
      obtain ⟨S₁, hs1, hR1⟩ := symStep2P_sim hnd hR i a ha.1 hs
      obtain ⟨S₂, hs2, hR2⟩ := symRun2P_sim hnd is as T₁ T' S₁ P₁ P' hR1 ha.2 h
      exact ⟨S₂, by simp only [symRun2, hs1, hs2], hR2⟩

/-! ## 5. The packed part check -/

/-- The packed state listing, at position `k + j`, the node `S` lists at entry `j` of `ls`;
    `none` when a node does not fit a slot. -/
def packR (S : SSt) : List Loc → Nat → Option Nat
  | [], _ => some 0
  | ℓ :: ls, k =>
    match packR S ls (k + 1) with
    | none => none
    | some σ =>
      match ℓ.node S with
      | none => some σ
      | some x => if x + 1 < PackedSlotState.B then some (pset σ k x) else none

theorem packR_spec (S : SSt) : ∀ (ls : List Loc) (k σ : Nat), packR S ls k = some σ →
    (∀ j ℓ, ls[j]? = some ℓ → pget σ (k + j) = ℓ.node S) ∧ (∀ j, j < k → pget σ j = none)
  | [], k, σ, h => by
      simp only [packR, Option.some.injEq] at h
      subst h
      exact ⟨fun j ℓ hj => by simp at hj, fun j _ => pget_zero j⟩
  | ℓ :: ls, k, σ, h => by
      simp only [packR] at h
      rcases hr : packR S ls (k + 1) with _ | σ₁
      · rw [hr] at h; cases h
      rw [hr] at h
      obtain ⟨h1, h2⟩ := packR_spec S ls (k + 1) σ₁ hr
      rcases hn : ℓ.node S with _ | x
      · rw [hn] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun j ℓ' hj => ?_, fun j hj => h2 j (by omega)⟩
        rcases j with _ | j
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          rw [Nat.add_zero, hn]
          exact h2 k (by omega)
        · simp only [List.getElem?_cons_succ] at hj
          rw [← h1 j ℓ' hj]
          congr 1
          omega
      · rw [hn] at h
        simp only at h
        split_ifs at h with hx
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun j ℓ' hj => ?_, fun j hj => ?_⟩
        · rcases j with _ | j
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            subst hj
            rw [Nat.add_zero, hn]
            exact pget_pset_self σ₁ k x hx
          · simp only [List.getElem?_cons_succ] at hj
            rw [pget_pset_ne σ₁ k _ x (by omega) hx, ← h1 j ℓ' hj]
            congr 1
            omega
        · rw [pget_pset_ne σ₁ k j x (by omega) hx]
          exact h2 j (by omega)

theorem PRep.of_packR {locs : List Loc} (hnd : locs.Nodup) {S : SSt} {σ : Nat}
    (h : packR S locs 0 = some σ) : PRep locs σ S := by
  intro ℓ hℓ
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hℓ
  have hg : locs[k]? = some locs[k] := List.getElem?_eq_getElem hk
  have := (packR_spec S locs 0 σ h).1 k _ hg
  rw [Nat.zero_add] at this
  show Loc.node S locs[k] = pget σ (locs.idxOf locs[k])
  rw [hnd.idxOf_getElem k hk, this]

/-- Every location of an exit map lists, at its slot of `locs` in the packed state `pk`, the
    node of its expression. -/
def exitOKP (a : Nat) (σ : List Nat) (n : Nat) (locs : List Loc) (pk : Nat) :
    Tb → List (Loc × WE) → Bool
  | _, [] => true
  | T, (l, e) :: m =>
    match internE a σ n T e, pget pk (locs.idxOf l) with
    | some (T₁, y), some x => decide (x = y) && exitOKP a σ n locs pk T₁ m
    | _, _ => false

theorem exitOKP_eq (a : Nat) (σ : List Nat) (n : Nat) {locs : List Loc} {pk : Nat} {S : SSt}
    (hR : PRep locs pk S) :
    ∀ (m : List (Loc × WE)) (T : Tb), (∀ p ∈ m, p.1 ∈ locs) →
      exitOKP a σ n locs pk T m = exitOK a σ n S T m
  | [], _, _ => rfl
  | (l, e) :: m, T, hm => by
      have hl : pget pk (locs.idxOf l) = l.node S :=
        (hR l (hm (l, e) List.mem_cons_self)).symm
      have ih := fun T₁ => exitOKP_eq a σ n hR m T₁
        (fun p hp => hm p (List.mem_cons_of_mem _ hp))
      simp only [exitOKP, exitOK, hl, ih]
      rfl

/-- The packed check of one part: `partCheck2` with the symbolic run on the packed state
    over the location list `locs` and the annotations `anns` of `blk`. The side conditions,
    checked once, are that `locs` is duplicate-free, that every annotation is correct, and
    that `locs` holds every location of the exit map. -/
def partCheck2P (a : Nat) (es : List WE) (mIn : List (Loc × WE)) (cIn zIn : Option WE)
    (mOut : List (Loc × WE)) (cOut zOut : Option WE) (locs : List Loc)
    (blk : List (JInstr 64)) (anns : List (List Nat)) : Bool :=
  decide locs.Nodup && annsOK locs blk anns && mOut.all (fun p => decide (p.1 ∈ locs)) &&
  match enterF a Tb.empty {} mIn cIn zIn with
  | some (T₀, S₀) =>
    match internS a [] a T₀ es with
    | some (T₁, σ) =>
      match packR S₀.base locs 0 with
      | some p₀ =>
        match symRun2P T₁ ⟨p₀, S₀.cfw, S₀.zfn⟩ blk anns with
        | some (T₂, P₂) =>
          match exitOptOK a σ (a + es.length) T₂ P₂.cfw cOut with
          | some T₃ =>
            match exitOptOK a σ (a + es.length) T₃ P₂.zfn zOut with
            | some T₄ => exitOKP a σ (a + es.length) locs P₂.pk T₄ mOut
            | none => false
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

theorem partCheck2P_imp (a : Nat) (es : List WE) (mIn : List (Loc × WE))
    (cIn zIn : Option WE) (mOut : List (Loc × WE)) (cOut zOut : Option WE)
    (locs : List Loc) (blk : List (JInstr 64)) (anns : List (List Nat))
    (h : partCheck2P a es mIn cIn zIn mOut cOut zOut locs blk anns = true) :
    partCheck2 a es mIn cIn zIn mOut cOut zOut blk = true := by
  unfold partCheck2P at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnd, hann⟩, hout⟩, h⟩ := h
  unfold partCheck2
  rcases he : enterF a Tb.empty {} mIn cIn zIn with _ | ⟨T₀, S₀⟩
  · rw [he] at h; cases h
  rw [he] at h
  simp only at h ⊢
  rcases hs : internS a [] a T₀ es with _ | ⟨T₁, σ⟩
  · rw [hs] at h; cases h
  rw [hs] at h
  simp only at h ⊢
  rcases hp : packR S₀.base locs 0 with _ | p₀
  · rw [hp] at h; cases h
  rw [hp] at h
  simp only at h
  rcases hr : symRun2P T₁ ⟨p₀, S₀.cfw, S₀.zfn⟩ blk anns with _ | ⟨T₂, P₂⟩
  · rw [hr] at h; cases h
  rw [hr] at h
  simp only at h
  obtain ⟨S₂, hr2, hR2, hc2, hz2⟩ := symRun2P_sim hnd blk anns T₁ T₂ S₀ _ _
    ⟨PRep.of_packR hnd hp, rfl, rfl⟩ hann hr
  rw [hr2]
  simp only
  rw [← hc2, ← hz2]
  rcases hc : exitOptOK a σ (a + es.length) T₂ P₂.cfw cOut with _ | T₃
  · rw [hc] at h; cases h
  rw [hc] at h
  simp only at h ⊢
  rcases hz : exitOptOK a σ (a + es.length) T₃ P₂.zfn zOut with _ | T₄
  · rw [hz] at h; cases h
  rw [hz] at h
  simp only at h ⊢
  rw [← exitOKP_eq a σ _ hR2 mOut T₄ (fun p hp => hout p hp)]
  exact h

theorem partCheck2P_sound (a : Nat) (es : List WE) (mIn : List (Loc × WE))
    (cIn zIn : Option WE) (mOut : List (Loc × WE)) (cOut zOut : Option WE)
    (locs : List Loc) (blk : List (JInstr 64)) (anns : List (List Nat))
    (h : partCheck2P a es mIn cIn zIn mOut cOut zOut locs blk anns = true)
    (ρ : Nat → BitVec 64) (hH : Holds ρ a es)
    (hK : ∀ j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ mIn s) (hcin : CfHolds ρ cIn s)
    (hzin : ZfHolds ρ zIn s) :
    MapHolds ρ mOut (runBlock s blk) ∧ CfHolds ρ cOut (runBlock s blk) ∧
      ZfHolds ρ zOut (runBlock s blk) :=
  partCheck2_sound a es mIn cIn zIn mOut cOut zOut blk
    (partCheck2P_imp a es mIn cIn zIn mOut cOut zOut locs blk anns h) ρ hH hK s hin hcin hzin

/-! ## 6. Static checks

A three-instruction part, checked by `decide +kernel`: the packed check reduces in the
kernel, accepts the annotations of the table above, and rejects an annotation with two
operands exchanged. -/

example : partCheck2P 0 [] [(.reg "c", .lit 7)] none none
    [(.reg "b", .lit 5), (.cell "p" 8, .lit 7), (.reg "a", .lit 5)] none none
    [.reg "a", .reg "b", .cell "p" 8, .reg "c"]
    [.mov "a" (.imm 5), .mov "b" (.reg "a"), .storeMem "p" 8 (.reg "c")]
    [[0], [1, 0], [2, 3]] = true := by decide +kernel

example : partCheck2P 0 [] [(.reg "c", .lit 7)] none none
    [(.reg "b", .lit 5), (.cell "p" 8, .lit 7), (.reg "a", .lit 5)] none none
    [.reg "a", .reg "b", .cell "p" 8, .reg "c"]
    [.mov "a" (.imm 5), .mov "b" (.reg "a"), .storeMem "p" 8 (.reg "c")]
    [[0], [1, 0], [3, 2]] = false := by decide +kernel

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
