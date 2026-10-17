/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop
public import CatCrypt.Crypto.SecureCompilation.SepLogic.AddrRunSafe

@[expose] public section

set_option autoImplicit false

/-!
# The stores of the address machine in the image simulations

`imgStores frame slotArr base` is the set of the bytes of the frame words and of the array
words `cellAt (base A) j`, `j < n`, of the arrays `(A, n)` of `slotArr`. A step of the address
machine stores to a frame word, to the word of an indexed store or to the word of a cell store
(`storeA?_cases`). Under the relation of an image simulation, at an instruction that passes
the gate and whose checked image step succeeds, the indexed store writes an array word (the
base register holds the base of the array, the index is below its length) and a cell store of
a body with cells writes a frame word, so the step stores in `imgStores` (`StoreIn`).

## Main results

* `storeA?_cases`: the address of the store of one step.
* `storeIn_of_cases`: `StoreIn` from the indexed and the cell stores of an instruction.
* `storeIn_of_imgStep`, `storeIn_of_imgStepW`: a checked image step under `ImgRel`, `ImgRelW`
  stores in `imgStores`.
* `image_addr_sim_store`: `ImageAddrSim.image_addr_sim` with the stores in `imgStores`.
* `image_addr_simB'_store`, `image_addr_simBW'_store`: `ImageAddrCellsLoop.image_addr_simB'`
  and `ImageAddrCellsLoop.image_addr_simBW'` with the stores in `imgStores`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag storeStruct?
  storeImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (accArr imgInstr virtImg
  physImgB)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM singletonProgM
  findInstrMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked (evalInstrPMemFk
  lsemFuelMemFk idxOkB idxBelowB idxOkB_of_checked)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCellsLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (LoadSafeAt RunSafe)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (SafeW carryIns
  classifyK)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (findInstrMem_single)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (evalInstrPMemF_next)
open CatCrypt.Crypto.SecureCompilation.SepLogic (Rng)
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (StoreIn storeIn_lopn_iff stepWrites
  storeA?)

/-- The bytes of the frame words of `frame` and of the words `cellAt (base A) j`, `j < n`, of
    the arrays `(A, n)` of `slotArr`. -/
def imgStores (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) : Set (BitVec 64) :=
  {x | ∃ a, ((∃ q, frame q = some a)
      ∨ ∃ q A n j, slotArr q = some (A, n) ∧ j < n ∧ a = ImageAddrSim.cellAt (base A) j)
    ∧ x ∈ (⟨a, 8⟩ : Rng 64)}

/-! ## 1. The store of one step -/

/-- `normA` keeps the cell access of an instruction. -/
theorem cellA?_normA_eq (x : LinstrR) : cellA? (normA x) = cellA? x := by
  cases x with
  | Lopn ds o ss =>
      simp only [normA]
      split_ifs with hm
      · subst hm
        rw [show withWidthTag 64 "MULX" = "MULX:64" by decide +kernel]
        unfold cellA?
        split <;> split <;> simp_all [eq_comm (a := "MULX:64"), eq_comm (a := "MULX")]
      · rfl
  | _ => rfl

/-- `normA` keeps the indexed store of an instruction. -/
theorem storeIdxA?_normA_eq (x : LinstrR) : storeIdxA? (normA x) = storeIdxA? x := by
  cases x with
  | Lopn ds o ss =>
      simp only [normA]
      split_ifs with hm
      · subst hm
        rw [show withWidthTag 64 "MULX" = "MULX:64" by decide +kernel]
        unfold storeIdxA?
        split <;> split <;> simp_all [eq_comm (a := "MULX:64"), eq_comm (a := "MULX")]
      · rfl
  | _ => rfl

/-- **The address of the store of one step**: a frame word, the word of an indexed store
    `p + sc * vi` with `p` and `vi` in the base and the index register, the word of a cell
    store `p + off` with `p` in the base register, or, at a constant-index store tag, the word
    `storeImmAddr? p n k` with `p` in the base register. -/
theorem storeA?_cases {frame : String → Option (BitVec 64)} {x : LinstrR} {tag : MemTag}
    {r : LstateN} {a : BitVec 64} (h : storeA? frame (x, tag) r = some a) :
    (∃ q, frame q = some a)
      ∨ (∃ b idx sc v p vi, storeIdxA? x = some (b, idx, sc, v) ∧ r.getW b 64 = some p
          ∧ r.getW idx 64 = some vi ∧ a = p + BitVec.ofNat 64 (sc * vi.toNat))
      ∨ (∃ b off v p, cellA? x = some (.st b off v) ∧ r.getW b 64 = some p
          ∧ a = p + BitVec.ofNat 64 off)
      ∨ (∃ n d b v k p, tag = .storeImm 64 n ∧ storeImmStruct? x = some (d, b, v, k)
          ∧ r.getW b 64 = some p ∧ storeImmAddr? p n k = some a) := by
  unfold storeA? at h
  cases tag with
  | store w n =>
    simp only at h
    cases hs : storeIdxA? x with
    | none => rw [hs] at h; cases h
    | some t =>
      obtain ⟨b, idx, sc, v⟩ := t
      rw [hs] at h
      simp only at h
      cases hp : r.getW b 64 with
      | none => rw [hp] at h; cases h
      | some p =>
        cases hvi : r.getW idx 64 with
        | none => rw [hp, hvi] at h; cases h
        | some vi =>
          rw [hp, hvi] at h
          cases h
          exact Or.inr (Or.inl ⟨b, idx, sc, v, p, vi, rfl, hp, hvi, rfl⟩)
  | reg c =>
    simp only at h
    cases hm : slotMov? x with
    | some t =>
      obtain ⟨d, src⟩ := t
      rw [hm] at h
      simp only at h
      cases hsrc : frame src with
      | some _ => rw [hsrc] at h; cases h
      | none => rw [hsrc] at h; exact Or.inl ⟨d, h⟩
    | none =>
      rw [hm] at h
      simp only at h
      cases hk : slotCmp? x with
      | some _ => rw [hk] at h; cases h
      | none =>
        rw [hk] at h
        simp only at h
        cases hc : cellA? x with
        | some op =>
          rw [hc] at h
          cases op with
          | st b off v =>
            simp only at h
            obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
            exact Or.inr (Or.inr (Or.inl ⟨b, off, v, p, rfl, hp, rfl⟩))
          | _ => simp at h
        | none =>
          rw [hc] at h
          simp only at h
          cases hy : slotCarry? frame x with
          | some t =>
            obtain ⟨_, d, _⟩ := t
            rw [hy] at h
            exact Or.inl ⟨d, h⟩
          | none =>
            rw [hy] at h
            simp only at h
            cases hi : slotImm? frame x with
            | some t =>
              obtain ⟨a', v⟩ := t
              rw [hi] at h
              cases h
              obtain ⟨q, -, hq⟩ := SepLogic.Addr.slotImm?_names hi
              exact Or.inl ⟨q, hq⟩
            | none =>
              rw [hi] at h
              simp only at h
              cases hv : slotCmov? frame x with
              | some t =>
                obtain ⟨d, _⟩ := t
                rw [hv] at h
                exact Or.inl ⟨d, h⟩
              | none => rw [hv] at h; cases h
  | storeImm w n =>
    simp only at h
    split at h
    · next hw =>
      subst hw
      cases hs : storeImmStruct? x with
      | none => rw [hs] at h; cases h
      | some t =>
        obtain ⟨d, b, v, k⟩ := t
        rw [hs] at h
        obtain ⟨p, hp, ha⟩ := Option.bind_eq_some_iff.mp h
        exact Or.inr (Or.inr (Or.inr ⟨n, d, b, v, k, p, rfl, rfl, hp, ha⟩))
    · cases h
  | _ => simp at h

/-- **`StoreIn` at an instruction from its indexed and cell stores.** The step at the program
    counter of `s` stores in `M` when `M` holds the bytes of every frame word, of the word of
    an indexed store of the instruction and of the word of a cell store of the instruction. -/
theorem storeIn_of_cases {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {s : LstateA} {bi : Linstr} (hb : c[s.reg.lpc]? = some bi)
    (hF : ∀ q a, frame q = some a → ∀ x ∈ (⟨a, 8⟩ : Rng 64), x ∈ M)
    (hS : ∀ d b idx sc v p vi,
      bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v] →
      s.reg.getW b 64 = some p → s.reg.getW idx 64 = some vi →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64), x ∈ M)
    (hC : ∀ b off v p, cellA? bi.li_i = some (.st b off v) → s.reg.getW b 64 = some p →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 off, 8⟩ : Rng 64), x ∈ M) :
    StoreIn M frame c s := by
  obtain ⟨ii, li⟩ := bi
  cases li with
  | Lopn ds o ss =>
    rw [storeIn_lopn_iff hb]
    intro a ha x hx
    rcases storeA?_cases ha with ⟨q, hq⟩ | ⟨b, idx, sc, v, p, vi, hs, hp, hvi, rfl⟩
      | ⟨b, off, v, p, hcl, hp, rfl⟩ | ⟨n, -, -, -, -, -, ht, -⟩
    · exact hF q a hq x hx
    · rw [storeIdxA?_normA_eq] at hs
      unfold storeIdxA? at hs
      split at hs
      · split_ifs at hs with ho
        subst ho
        rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
        exact hS _ _ _ _ _ p vi he hp hvi x hx
      · cases hs
    · rw [cellA?_normA_eq] at hcl
      exact hC b off v p hcl hp x hx
    · exact absurd ht (tagAt_ne_storeImm _ _ _ _ _)
  | _ =>
    intro x hx
    simp [stepWrites, hb] at hx

/-- A step at a label stores nothing. -/
theorem storeIn_of_label {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {s : LstateA} {bi : Linstr} (hb : c[s.reg.lpc]? = some bi) {ii : _} {l : LLabel}
    (hl : bi.li_i = .Llabel ii l) : StoreIn M frame c s := by
  intro x hx
  obtain ⟨ii', li⟩ := bi
  simp only at hl
  subst hl
  simp [stepWrites, hb] at hx

/-- The bytes of a frame word lie in `imgStores`. -/
theorem frame_mem_imgStores {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} (q : String)
    (a : BitVec 64) (hq : frame q = some a) :
    ∀ x ∈ (⟨a, 8⟩ : Rng 64), x ∈ imgStores frame slotArr base :=
  fun _ hx => ⟨a, Or.inl ⟨q, hq⟩, hx⟩

/-- The bytes of an array word lie in `imgStores`. -/
theorem cell_mem_imgStores {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {q A : String}
    {n j : Nat} (hq : slotArr q = some (A, n)) (hj : j < n) :
    ∀ x ∈ (⟨cellAt (base A) j, 8⟩ : Rng 64), x ∈ imgStores frame slotArr base :=
  fun _ hx => ⟨_, Or.inr ⟨q, A, n, j, hq, hj, rfl⟩, hx⟩

/-- The index of a checked indexed store of the image is below the length of its array. -/
theorem idx_lt_of_checked {P : LprogM} {A idx v : String} {n : Nat} {s t : LstateMF}
    (hs : evalInstrPMemFk true P
      (.Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v], .store 64 n) s = some t)
    {vi : BitVec 64} (hvi : s.prog.base.reg.getW idx 64 = some vi) : vi.toNat < n := by
  have hok := idxOkB_of_checked hs
  simp only [idxOkB, storeStruct?, if_true, idxBelowB, hvi] at hok
  simpa using hok

/-! ## 2. The plain route -/

/-- No instruction that passes `instrGateB` is a cell store. -/
theorem cellA_ne_st_of_instrGateB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {x : LinstrR}
    (hg : instrGateB frame slotArr c k x = true) {b : String} {off : Nat} {v : String}
    (hcl : cellA? x = some (.st b off v)) : False := by
  unfold instrGateB at hg
  cases hc : icase frame x with
  | label => obtain ⟨_, _, rfl⟩ := icase_label hc; simp [cellA?] at hcl
  | cond cc l => rw [icase_cond hc] at hcl; simp [cellA?] at hcl
  | ldx d b' idx => rw [icase_ldx hc] at hcl; simp [cellA?] at hcl
  | stx d b' idx v' => rw [icase_stx hc] at hcl; simp [cellA?] at hcl
  | sload d q =>
      have := (icase_sload hc).1
      rw [slotMov_cell hcl] at this
      cases this
  | sstore q S =>
      have := (icase_sstore hc).1
      rw [slotMov_cell hcl] at this
      cases this
  | scmp d y q => rw [slotCmp?_eq (icase_scmp hc).1] at hcl; simp [cellA?] at hcl
  | reg =>
      rw [hc] at hg
      simp [regGateB, regOkB, cellA?_normA_eq, hcl] at hg
  | other => rw [hc] at hg; cases hg

/-- The gate condition `instrGateB` at the position of an instruction of a body that passes
    `imgGateB`. -/
theorem instrGateB_of_imgGateB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} (hgate : imgGateB frame slotArr c = true)
    {k : Nat} {bi : Linstr} (hb : c[k]? = some bi) (hlt : k < c.length - 1) :
    instrGateB frame slotArr c k bi.li_i = true := by
  simp only [imgGateB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
  have := hgate.1.1 k hlt
  rw [hb] at this
  simpa using this

/-- `icase` classifies an indexed store with a scale other than `8` as `other`. -/
theorem icase_storeIdx_ne {frame : String → Option (BitVec 64)} {d b idx v : String} {sc : Nat}
    (hsc : sc ≠ 8) :
    icase frame (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v]) = .other := by
  unfold icase
  split <;> simp_all

/-- **The indexed store of a checked image step on the plain route** writes an array word:
    under `ImgRel`, at an indexed store before the last instruction of a body that passes
    `imgGateB`, whose checked image step succeeds, the base register holds `base A` and the
    index is below the length `n` of the array. -/
theorem stx_mem_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {d b idx : String} {sc : Nat} {v : String} {p vi : BitVec 64}
    (hx : bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
    (hp : sa.reg.getW b 64 = some p) (hvi : sa.reg.getW idx 64 = some vi) :
    ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64),
      x ∈ imgStores frame slotArr base := by
  have hg := instrGateB_of_imgGateB hgate hb hlt
  unfold instrGateB at hg
  rw [hx] at hg hstep
  by_cases hsc : sc = 8
  · subst hsc
    simp only [icase, if_true, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨A, n⟩, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
    obtain ⟨q, hq, hpb⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [imgInstr_stx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs idx hidx) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep (hidxe.trans hvi))
  · rw [icase_storeIdx_ne hsc] at hg
    cases hg

/-- **The store of a checked image step on the plain route.** Under `ImgRel`, at an
    instruction before the last of a body that passes `imgGateB`, a successful checked step of
    the image stores in `imgStores`: to a frame word, or by an indexed store to the word
    `cellAt (base A) vi` of its array. -/
theorem storeIn_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    StoreIn (imgStores frame slotArr base) frame c sa :=
  storeIn_of_cases hb frame_mem_imgStores
    (fun _ _ _ _ _ _ _ hx hp hvi => stx_mem_of_imgStep hsep hgate P hrel hb hlt hstep hx hp hvi)
    (fun _ _ _ _ hcl _ => (cellA_ne_st_of_instrGateB (instrGateB_of_imgGateB hgate hb hlt)
      hcl).elim)

/-! ## 3. The route with carry chains -/

/-- **The indexed store of a checked image step with carry chains** writes an array word:
    `stx_mem_of_imgStep` under `ImgRelW` and `imgGateBW`. -/
theorem stx_mem_of_imgStepW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateBW frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {d b idx : String} {sc : Nat} {v : String} {p vi : BitVec 64}
    (hx : bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
    (hp : sa.reg.getW b 64 = some p) (hvi : sa.reg.getW idx 64 = some vi) :
    ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64),
      x ∈ imgStores frame slotArr base := by
  have hg : instrGateBW frame slotArr c sa.reg.lpc bi.li_i = true := by
    simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
    have := hgate.1.1 sa.reg.lpc hlt
    rw [hb] at this
    simpa using this
  simp only [instrGateBW, gateAtW, Bool.and_eq_true] at hg
  obtain ⟨hrd0, hg⟩ := hg
  rw [hx] at hg hrd0 hstep
  have hkc : classifyK (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v]) = none := by
    simp [classifyK]
  have hci : carryI? (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v]) = none := by
    simp [carryI?]
  rw [hci] at hg
  by_cases hsc : sc = 8
  · subst hsc
    have hc : icase frame (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v])
        = .stx d b idx v := by
      simp [icase]
    simp only [hc, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨A, n⟩, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
    have hrd : readOkB (gateReadSet frame (oneBitAt frame c sa.reg.lpc)
        (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v]))
        (.Lopn [.reg d] "STOREIDX" [.arrIdx b idx 8, .reg v]) = true := by
      simpa [castReadB, hkc] using hrd0
    simp only [gateReadSet, hc] at hrd
    have hidxW : idx ∉ oneBitAt frame c sa.reg.lpc :=
      readOkB_spec hrd (by simp [readNames, srcNames]) (by simp [carryIns])
    obtain ⟨q, hq, hpb⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [imgInstr_stx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hidx hidxW) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep (hidxe.trans hvi))
  · rw [icase_storeIdx_ne hsc] at hg
    simp [castGateB, hkc] at hg

/-! ## 4. Bodies with cells -/

/-- **The store of a step of a body with cells.** Where the base register of every cell access
    holds the pointer of its array, a cell store of the body writes the frame word of its cell
    name (`CellFrames`); so the step stores in `imgStores` when its indexed store does. -/
theorem storeIn_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hF : CellFrames frame slotArr base rsp body) {sa : LstateA}
    (hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
      DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A))
    {b0 : Linstr} (hb0 : body[sa.reg.lpc]? = some b0)
    (hS : ∀ d b idx sc v p vi,
      b0.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v] →
      sa.reg.getW b 64 = some p → sa.reg.getW idx 64 = some vi →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64),
        x ∈ imgStores frame slotArr base) :
    StoreIn (imgStores frame slotArr base) frame body sa :=
  storeIn_of_cases hb0 frame_mem_imgStores hS (fun B off S p hcl hp => by
    obtain ⟨A, n, hacc, hBf, -, hfr⟩ := hF.st _ _ B off S hb0 hcl
    have hpA := hptr B A n hacc (hF.stGp _ _ B off S hb0 hcl) hBf
    rw [hp] at hpA
    cases hpA
    exact frame_mem_imgStores _ _ hfr)

/-! ## 5. The state after the first of two steps -/

/-- **The state after one step of the address machine on the plain route** is related to the
    image state, or stands at a label and stores nothing. -/
theorem rel_or_storeIn_plain {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr c = true)
    (hgate : imgGateB frame slotArr c = true) (fn : String) {M : Set (BitVec 64)}
    {s t : LstateMF} {sa : LstateA} (hrel : ImgRel frame slotArr base c s sa s.zf)
    {bi : Linstr} (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {sa1 : LstateA} {z1 : Bool} (hst : stepA frame c sa s.zf = some (sa1, z1)) :
    ImgRel frame slotArr base c t sa1 z1 ∨ StoreIn M frame c sa1 := by
  by_cases hcnd : ∃ cc l, bi.li_i = .Lcond cc l
  · obtain ⟨cc, l, hx⟩ := hcnd
    obtain ⟨-, -, sa1', hst', hc⟩ := img_step_cond rsp hphys hgate fn s t sa bi cc l hrel hb hlt
      hx hstep
    rw [hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    rcases hc with h | ⟨⟨bl, ii, l', hbl, hli⟩, -⟩
    · exact Or.inl h
    · exact Or.inr (storeIn_of_label hbl hli)
  · obtain ⟨-, -, sa1', hst', hr⟩ :=
      img_stepStraight hsep hphys hgate _ hrel hb hlt (fun cc l e => hcnd ⟨cc, l, e⟩) hstep
    rw [hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact Or.inl hr

/-- **The state after one step of the address machine on a body with cells** is related to
    the image state by `R`, or stands at a label and stores nothing; from the step of the
    image at a conditional branch (`CondStep`) and at any other instruction. -/
theorem rel_or_storeIn_cells {R : LstateMF → LstateA → Bool → Prop}
    {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd} {fn : String}
    {M : Set (BitVec 64)} (hcond : CondStep R frame slotArr rsp (cellBody slotArr body) fn)
    (hF : CellFrames frame slotArr base rsp body) {s t : LstateMF} {sa : LstateA}
    (hrel : R s sa s.zf)
    (hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
      DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A))
    {bi : Linstr} (hb : (cellBody slotArr body)[sa.reg.lpc]? = some bi)
    (hlt : sa.reg.lpc < (cellBody slotArr body).length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      (imgInstr slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i) s = some t)
    (hstr : (∀ cc l, bi.li_i ≠ .Lcond cc l) →
      ∃ sa1, stepA frame (cellBody slotArr body) sa s.zf = some (sa1, t.zf) ∧ R t sa1 t.zf)
    {sa1 : LstateA} {z1 : Bool} (hst : stepA frame body sa s.zf = some (sa1, z1)) :
    R t sa1 z1 ∨ StoreIn M frame body sa1 := by
  by_cases hcnd : ∃ cc l, bi.li_i = .Lcond cc l
  · obtain ⟨cc, l, hx⟩ := hcnd
    obtain ⟨-, -, sa1', hst', hc⟩ := hcond s t sa bi cc l hrel hb hlt hx hstep
    have hb' := hb
    rw [cellBody_getElem?] at hb'
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb'
    have hx0 := lcond_of_cellMove hx
    have hbC : (cellBody slotArr body)[sa.reg.lpc]? = some b0 := by
      rw [hb, cellMove_lcond slotArr body _ hx0]
    have he : stepA frame body sa s.zf = stepA frame (cellBody slotArr body) sa s.zf := by
      unfold stepA
      rw [hbC, hb0]
      obtain ⟨ii, li⟩ := b0
      simp only at hx0
      subst hx0
      cases cc <;> simp only [labelAt_cellBody]
    rw [he, hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    rcases hc with h | ⟨⟨bl, ii, l', hbl, hli⟩, -⟩
    · exact Or.inl h
    · rw [cellBody_getElem?] at hbl
      obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hbl
      exact Or.inr (storeIn_of_label hb1 (llabel_of_cellMove hli))
  · obtain ⟨sa1', hst', hr⟩ := hstr (fun cc l e => hcnd ⟨cc, l, e⟩)
    obtain ⟨-, he⟩ := stepA_cellBody hF hptr s.zf
    rw [he, hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact Or.inl hr

/-! ## 6. The runs -/

/-- **The image simulated by the address machine, with its stores.**
    `ImageAddrSim.image_addr_sim` with the stores of the run in `imgStores`: every step of the
    address machine stores to a frame word or to an array word `cellAt (base A) j`, `j < n`. -/
theorem image_addr_sim_store {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
        ∧ ImgRel frame slotArr base body t sa' zf'
        ∧ RunSafe frame body (LoadSafeAt rsp body) fuel' sa zf
        ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  intro fuel s t sa zf hfn hrel hrun
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame) (body := body)
    (P := singletonProgM fn (virtImg slotArr body))
    (R := fun s sa zf => s.prog.lfn = fn ∧ ImgRel frame slotArr base body s sa zf)
    (Q := fun x => LoadSafeAt rsp body x ∧ StoreIn (imgStores frame slotArr base) frame body x)
    (fun s sa zf h hf => haltedA_of_img (.of_imgGateB hgate) fn h.1 h.2.pc hf)
    (fun s s1 sa zf i h hf he => by
      obtain ⟨hfn, hrel⟩ := h
      have hz := hrel.zf
      subst hz
      obtain ⟨hh, hsafe, hlfn, sa1, z1, hst1, hc⟩ := img_step hsep hphys hgate fn hfn hrel hf he
      rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
        List.getElem?_dropLast] at hf
      split at hf
      case isFalse => cases hf
      rename_i hlt
      obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
      refine ⟨hh, ⟨hsafe, storeIn_of_imgStep hsep hgate _ hrel hb hlt he⟩, sa1, z1, hst1, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, z2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_storeIn_plain hsep hphys hgate fn hrel hb hlt he hst1 with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, z2, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

/-- **The image of the cell body simulated on the body, with its stores.**
    `ImageAddrCellsLoop.image_addr_simB'` with the stores of the run in `imgStores`: an indexed
    store writes an array word and a cell store `mem.B.off` writes the frame word of its cell
    name. -/
theorem image_addr_simB'_store {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateB frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool)
    (hfn : s.prog.lfn = fn)
    (hrel : ImgRel frame slotArr base (cellBody slotArr body) s sa zf)
    (hrun : lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      fuel s = some t) :
    ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
      ∧ ImgRel frame slotArr base (cellBody slotArr body) t sa' zf'
      ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf
      ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRel frame slotArr base (cellBody slotArr body) s sa zf)
    (Q := fun x => SafeW rsp body x ∧ StoreIn (imgStores frame slotArr base) frame body x)
    (fun s sa zf h hf => by
      have hh := haltedA_of_img (.of_imgGateB hgate) fn h.1 h.2.pc hf
      rwa [haltedA_cellBody] at hh)
    (fun s s1 sa zf i h hf he => by
      obtain ⟨hfn, hrel⟩ := h
      have hlfn : s1.prog.lfn = fn :=
        (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans hfn
      have hz := hrel.zf
      subst hz
      rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
        List.getElem?_dropLast] at hf
      split at hf
      case isFalse => cases hf
      rename_i hlt
      obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
      have hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
          DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A) := by
        intro B A m hacc hg hBf
        obtain ⟨q, -, hpA⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel
          (accArr_cellBody hN (hasPrefix_gpName hg) hacc) hBf
        exact hpA
      have hS : StoreIn (imgStores frame slotArr base) frame body sa := by
        have hb' := hb
        rw [cellBody_getElem?] at hb'
        obtain ⟨b0, hb0, he0⟩ := Option.map_eq_some_iff.mp hb'
        refine storeIn_cellBody hF hptr hb0 fun d b idx sc v p vi hx hp hvi => ?_
        have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
        rw [cellMove_of_none hc0] at he0
        subst he0
        exact stx_mem_of_imgStep hsep hgate _ hrel hb hlt he hx hp hvi
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ := cell_step' hsep hphys hgate hN hF fn hrel hb hlt he
      refine ⟨hh, ⟨hsafe, hS⟩, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_storeIn_cells (img_step_cond rsp hphys hgate fn) hF hrel hptr hb hlt he
          (fun hnc => (img_stepStraight hsep hphys hgate _ hrel hb hlt hnc he).2.2) hst
          with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

/-- **The image of the cell body simulated on the body, with carry chains and with its
    stores.** `ImageAddrCellsLoop.image_addr_simBW'` with the stores of the run in
    `imgStores`: an indexed store writes an array word, a cell store `mem.B.off` writes the
    frame word of its cell name, and a carry-chain destination, an immediate move and a
    select destination in a frame slot write their frame words. -/
theorem image_addr_simBW'_store {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr (cellBody slotArr body) = true)
    (hgate : imgGateBW frame slotArr (cellBody slotArr body) = true)
    (hN : CellNoSlot slotArr body) (hF : CellFrames frame slotArr base rsp body)
    (fn : String) (hcond : ImgStepWCond frame slotArr base rsp (cellBody slotArr body) fn)
    (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool) (hfn : s.prog.lfn = fn)
    (hrel : ImgRelW frame slotArr base (cellBody slotArr body) s sa zf)
    (hrun : lsemFuelMemFk true (singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
      fuel s = some t) :
    ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
      ∧ ImgRelW frame slotArr base (cellBody slotArr body) t sa' zf'
      ∧ RunSafe frame body (SafeW rsp body) fuel' sa zf
      ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRelW frame slotArr base (cellBody slotArr body) s sa zf)
    (Q := fun x => SafeW rsp body x ∧ StoreIn (imgStores frame slotArr base) frame body x)
    (fun s sa zf h hf => by
      have hh := haltedA_of_imgW hgate fn h.1 h.2.pc hf
      rwa [haltedA_cellBody] at hh)
    (fun s s1 sa zf i h hf he => by
      obtain ⟨hfn, hrel⟩ := h
      have hlfn : s1.prog.lfn = fn :=
        (evalInstrPMemF_next _ i s s1 (JasminLsemMemChecked.evalInstrPMemF_of_k he)).1.trans hfn
      have hz := hrel.zf
      subst hz
      rw [findInstrMem_single hfn, JasminLsemAddrImage.virtImg_getElem?, ← hrel.pc,
        List.getElem?_dropLast] at hf
      split at hf
      case isFalse => cases hf
      rename_i hlt
      obtain ⟨bi, hb, rfl⟩ := Option.map_eq_some_iff.mp hf
      have hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
          DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A) := by
        intro B A m hacc hg hBf
        obtain ⟨q, -, hpA⟩ := ptr_of_reloadW hsep hgate hrel
          (accArr_cellBody hN (hasPrefix_gpName hg) hacc) hBf
        exact hpA
      have hS : StoreIn (imgStores frame slotArr base) frame body sa := by
        have hb' := hb
        rw [cellBody_getElem?] at hb'
        obtain ⟨b0, hb0, he0⟩ := Option.map_eq_some_iff.mp hb'
        refine storeIn_cellBody hF hptr hb0 fun d b idx sc v p vi hx hp hvi => ?_
        have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
        rw [cellMove_of_none hc0] at he0
        subst he0
        exact stx_mem_of_imgStepW hsep hgate _ hrel hb hlt he hx hp hvi
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ :=
        cell_stepW' hsep hphys hgate hN hF fn hcond hrel hb hlt he
      refine ⟨hh, ⟨hsafe, hS⟩, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_storeIn_cells hcond hF hrel hptr hb hlt he
          (fun hnc => (img_stepW hsep hphys hgate _ hrel hb hlt hnc he).2.2) hst
          with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore
