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
# The stores and loads of the address machine in the image simulations

`imgStores frame slotArr base` is the set of the bytes of the frame words and of the array
words `cellAt (base A) j`, `j < n`, of the arrays `(A, n)` of `slotArr`. A step of the address
machine stores to a frame word, to the word of an indexed store or to the word of a cell store
(`storeA?_cases`), and loads from frame words, from the word of an indexed load and from the
word of a cell load (`loadsA`). Under the relation of an image simulation, at an instruction
that passes the gate and whose checked image step succeeds, an indexed store or load accesses
an array word (the base register holds the base of the array, the index is below its length)
and a cell store or load of a body with cells accesses a frame word, so the step stores in and
loads from `imgStores` (`AccessIn`).

## Main results

* `storeA?_cases`: the address of the store of one step.
* `accessIn_of_cases`: `AccessIn` from the indexed and the cell accesses of an instruction.
* `idx_mem_of_imgStep`, `idx_mem_of_imgStepW`: the indexed access of a checked image step
  under `ImgRel`, `ImgRelW` accesses an array word.
* `image_addr_sim_access`: `ImageAddrSim.image_addr_sim` with the accesses in `imgStores`.
* `image_addr_simB'_access`, `image_addr_simBW'_access`:
  `ImageAddrCellsLoop.image_addr_simB'` and `ImageAddrCellsLoop.image_addr_simBW'` with the
  accesses in `imgStores`.
* `image_addr_sim_store`, `image_addr_simB'_store`, `image_addr_simBW'_store`: the stores of
  the three runs in `imgStores`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag storeStruct?
  loadStruct? storeImmStruct?)
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
open CatCrypt.Crypto.SecureCompilation.SepLogic.Addr (StoreIn AccessIn storeIn_lopn_iff
  stepWrites stepReads storeA? storeR?_of_ne_zero loadsA idxAddr? cellLdAddr?)

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

/-- `normA` keeps the indexed load of an instruction. -/
theorem loadIdxA?_normA_eq (x : LinstrR) : loadIdxA? (normA x) = loadIdxA? x := by
  cases x with
  | Lopn ds o ss =>
      simp only [normA]
      split_ifs with hm
      · subst hm
        rw [show withWidthTag 64 "MULX" = "MULX:64" by decide +kernel]
        unfold loadIdxA?
        split <;> split <;> simp_all [eq_comm (a := "MULX:64"), eq_comm (a := "MULX")]
      · rfl
  | _ => rfl

/-- The address of an indexed load: the instruction is `LOADIDX d, (b, idx, sc)` and the
    address is `p + sc * vi` with `p` and `vi` in the base and the index register. -/
theorem idxAddr?_eq_some {x : LinstrR} {r : LstateN} {a : BitVec 64}
    (h : idxAddr? x r = some a) :
    ∃ d b idx sc p vi, x = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc]
      ∧ r.getW b 64 = some p ∧ r.getW idx 64 = some vi
      ∧ a = p + BitVec.ofNat 64 (sc * vi.toNat) := by
  unfold idxAddr? at h
  split at h
  · rename_i d b idx sc hl
    split at h
    · rename_i p vi hp hvi
      cases h
      unfold loadIdxA? at hl
      split at hl
      · split_ifs at hl with ho
        subst ho
        simp only [Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
        exact ⟨_, _, _, _, p, vi, rfl, hp, hvi, rfl⟩
      · cases hl
    · cases h
  · cases h

/-- The address of a cell load: the instruction loads from the cell `mem.b.off` and the
    address is `p + off` with `p` in the base register. -/
theorem cellLdAddr?_eq_some {x : LinstrR} {r : LstateN} {a : BitVec 64}
    (h : cellLdAddr? x r = some a) :
    ∃ d b off p, cellA? x = some (.ld d b off) ∧ r.getW b 64 = some p
      ∧ a = p + BitVec.ofNat 64 off := by
  unfold cellLdAddr? at h
  split at h
  · rename_i d b off hc
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨d, b, off, p, hc, hp, rfl⟩
  · cases h

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

/-- **`AccessIn` at an instruction from its indexed and cell accesses.** The step at the
    program counter of `s` stores in and loads from `M` when `M` holds the bytes of every frame
    word, of the word of an indexed store or load of the instruction, of the word of a cell
    store or load of the instruction, of the words an array zeroing `ZEROARR` of the
    instruction writes and of the word of a constant-index store `STOREIMM` of the
    instruction. -/
theorem accessIn_of_cases {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {s : LstateA} {bi : Linstr} (hb : c[s.reg.lpc]? = some bi)
    (hF : ∀ q a, frame q = some a → ∀ x ∈ (⟨a, 8⟩ : Rng 64), x ∈ M)
    (hI : ∀ b idx sc p vi,
      ((∃ d v, bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
        ∨ ∃ d, bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc]) →
      s.reg.getW b 64 = some p → s.reg.getW idx 64 = some vi →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64), x ∈ M)
    (hC : ∀ b off p, ((∃ v, cellA? bi.li_i = some (.st b off v))
        ∨ ∃ d, cellA? bi.li_i = some (.ld d b off)) → s.reg.getW b 64 = some p →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 off, 8⟩ : Rng 64), x ∈ M)
    (hZ : ∀ b n w p, bi.li_i = .Lopn [] "ZEROARR" [.reg b, .imm n, .imm w] →
      s.reg.getW b 64 = some p → ∀ x ∈ (⟨p, 8 * n⟩ : Rng 64), x ∈ M)
    (hS : ∀ d b v k p, bi.li_i = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k] →
      s.reg.getW b 64 = some p → ∀ x ∈ (⟨p + BitVec.ofNat 64 (8 * k), 8⟩ : Rng 64), x ∈ M) :
    AccessIn M frame c s := by
  obtain ⟨ii, li⟩ := bi
  cases li with
  | Lopn ds o ss =>
    refine ⟨?_, ?_⟩
    · rw [storeIn_lopn_iff hb]
      intro R hR x hx
      by_cases hzt : ∃ w n, tagAt c s.reg.lpc (.Lopn ds o ss) = .zero w n
      · obtain ⟨w, n, ht⟩ := hzt
        rw [ht] at hR
        unfold SepLogic.Addr.storeR? at hR
        simp only at hR
        split_ifs at hR
        split at hR
        · rename_i b hza
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hR
          have hshape : ds = [] ∧ o = "ZEROARR" ∧ ∃ n' w', ss = [.reg b, .imm n', .imm w'] := by
            have hm : o ≠ "MULX" := by
              rintro rfl
              unfold normA zeroArrA? at hza
              split at hza
              · rename_i heq
                simp only [LinstrR.Lopn.injEq] at heq
                obtain ⟨-, hop, -⟩ := heq
                simp only [ite_true] at hop
                rw [← hop, if_neg (by decide +kernel)] at hza
                cases hza
              · cases hza
            rw [show normA (.Lopn ds o ss) = .Lopn ds o ss by simp [normA, hm]] at hza
            unfold zeroArrA? at hza
            split at hza
            · rename_i heq
              simp only [LinstrR.Lopn.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              split_ifs at hza with ho
              cases hza
              exact ⟨rfl, ho, _, _, rfl⟩
            · cases hza
          obtain ⟨rfl, rfl, n', w', rfl⟩ := hshape
          rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]), tagA_zeroArr] at ht
          cases ht
          exact hZ _ _ _ p rfl hp x hx
        · cases hR
      have hz : ∀ w n, tagAt c s.reg.lpc (.Lopn ds o ss) ≠ .zero w n :=
        fun w n h => hzt ⟨w, n, h⟩
      rw [storeR?_of_ne_zero (i := (normA (.Lopn ds o ss), tagAt c s.reg.lpc (.Lopn ds o ss)))
        hz] at hR
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hR
      rcases storeA?_cases ha with ⟨q, hq⟩ | ⟨b, idx, sc, v, p, vi, hs, hp, hvi, rfl⟩
        | ⟨b, off, v, p, hcl, hp, rfl⟩ | ⟨n, d, b, v, k, p, ht, hst, hp, hia⟩
      · exact hF q a hq x hx
      · rw [storeIdxA?_normA_eq] at hs
        unfold storeIdxA? at hs
        split at hs
        · split_ifs at hs with ho
          subst ho
          rename_i he
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
          exact hI _ _ _ p vi (.inl ⟨_, _, he⟩) hp hvi x hx
        · cases hs
      · rw [cellA?_normA_eq] at hcl
        exact hC b off p (.inl ⟨v, hcl⟩) hp x hx
      · by_cases hso : o = "STOREIMM"
        · subst hso
          have hn : normA (.Lopn ds "STOREIMM" ss) = .Lopn ds "STOREIMM" ss := by simp [normA]
          rw [hn] at hst
          unfold storeImmStruct? at hst
          split at hst
          · rename_i heq
            simp only [LinstrR.Lopn.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hst
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hst
            rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]), tagA_storeImm] at ht
            cases ht
            rw [storeImmAddr?_of_lt p (Nat.lt_succ_self _)] at hia
            cases hia
            exact hS _ _ _ _ p rfl hp x hx
          · cases hst
        · exact absurd ht (tagAt_ne_storeImm _ _ hso _ _)
    · intro x hx
      unfold stepReads at hx
      rw [hb] at hx
      obtain ⟨a, ha, hx⟩ := hx
      simp only [loadsA, List.mem_append, List.mem_filterMap, Option.mem_toList] at ha
      rcases ha with (⟨q, -, hq⟩ | ha) | ha
      · exact hF q a hq x hx
      · have he : idxAddr? (normA (.Lopn ds o ss)) s.reg = idxAddr? (.Lopn ds o ss) s.reg := by
          simp only [idxAddr?, loadIdxA?_normA_eq]
        rw [he] at ha
        obtain ⟨d, b, idx, sc, p, vi, hl, hp, hvi, rfl⟩ := idxAddr?_eq_some ha
        exact hI b idx sc p vi (.inr ⟨d, hl⟩) hp hvi x hx
      · have he : cellLdAddr? (normA (.Lopn ds o ss)) s.reg
            = cellLdAddr? (.Lopn ds o ss) s.reg := by
          simp only [cellLdAddr?, cellA?_normA_eq]
        rw [he] at ha
        obtain ⟨d, b, off, p, hcl, hp, rfl⟩ := cellLdAddr?_eq_some ha
        exact hC b off p (.inr ⟨d, hcl⟩) hp x hx
  | _ =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp [stepWrites, hb] at hx
    · simp [stepReads, hb] at hx

/-- A step at a label stores and loads nothing. -/
theorem accessIn_of_label {M : Set (BitVec 64)} {frame : String → Option (BitVec 64)}
    {c : Lcmd} {s : LstateA} {bi : Linstr} (hb : c[s.reg.lpc]? = some bi) {ii : _} {l : LLabel}
    (hl : bi.li_i = .Llabel ii l) : AccessIn M frame c s := by
  obtain ⟨ii', li⟩ := bi
  simp only at hl
  subst hl
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp [stepWrites, hb] at hx
  · simp [stepReads, hb] at hx

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

/-- The index of a checked indexed store tagged `.store w n` or of a checked indexed load
    tagged `.load w n` is below `n`. -/
theorem idx_lt_of_checked {P : LprogM} {i : LinstrRM} {idx : String} {n : Nat}
    {s t : LstateMF} (hs : evalInstrPMemFk true P i s = some t)
    (hi : (∃ w d b v, i.2 = .store w n ∧ storeStruct? i.1 = some (d, b, idx, v))
      ∨ ∃ w d b, i.2 = .load w n ∧ loadStruct? i.1 = some (d, b, idx))
    {vi : BitVec 64} (hvi : s.prog.base.reg.getW idx 64 = some vi) : vi.toNat < n := by
  have hok := idxOkB_of_checked hs
  obtain ⟨i1, i2⟩ := i
  rcases hi with ⟨w, d, b, v, h2, h1⟩ | ⟨w, d, b, h2, h1⟩
  all_goals
    simp only at h2 h1
    subst h2
    simp only [idxOkB, h1, idxBelowB, hvi] at hok
    simpa using hok

/-! ## 2. The plain route -/

/-- No instruction that passes `instrGateB` is a cell access. -/
theorem cellA_none_of_instrGateB {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {x : LinstrR}
    (hg : instrGateB frame slotArr c k x = true) : cellA? x = none := by
  by_contra hne
  obtain ⟨op, hcl⟩ := Option.ne_none_iff_exists'.mp hne
  unfold instrGateB at hg
  cases hc : icase frame x with
  | label => obtain ⟨_, _, rfl⟩ := icase_label hc; simp [cellA?] at hcl
  | cond cc l => rw [icase_cond hc] at hcl; simp [cellA?] at hcl
  | ldx d b' idx => rw [icase_ldx hc] at hcl; simp [cellA?] at hcl
  | stx d b' idx v' => rw [icase_stx hc] at hcl; simp [cellA?] at hcl
  | zarr b' n w => rw [icase_zarr hc] at hcl; simp [cellA?] at hcl
  | simm d b' v' j => rw [icase_simm hc] at hcl; simp [cellA?] at hcl
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

/-- `icase` classifies an indexed store or load with a scale other than `8` as `other`. -/
theorem icase_idx_ne {frame : String → Option (BitVec 64)} {x : LinstrR} {b idx : String}
    {sc : Nat} (hsc : sc ≠ 8)
    (hx : (∃ d v, x = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
      ∨ ∃ d, x = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc]) :
    icase frame x = .other := by
  rcases hx with ⟨d, v, rfl⟩ | ⟨d, rfl⟩ <;> unfold icase <;> split <;> simp_all

/-- **The indexed access of a checked image step on the plain route** accesses an array word:
    under `ImgRel`, at an indexed store or load before the last instruction of a body that
    passes `imgGateB`, whose checked image step succeeds, the base register holds `base A` and
    the index is below the length `n` of the array. -/
theorem idx_mem_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {b idx : String} {sc : Nat} {p vi : BitVec 64}
    (hx : (∃ d v, bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
      ∨ ∃ d, bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc])
    (hp : sa.reg.getW b 64 = some p) (hvi : sa.reg.getW idx 64 = some vi) :
    ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64),
      x ∈ imgStores frame slotArr base := by
  have hg := instrGateB_of_imgGateB hgate hb hlt
  unfold instrGateB at hg
  by_cases hsc : sc = 8
  swap
  · rw [icase_idx_ne hsc hx] at hg
    cases hg
  subst hsc
  rcases hx with ⟨d, v, hx⟩ | ⟨d, hx⟩ <;> rw [hx] at hg hstep
  · simp only [icase, if_true, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨A, n⟩, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
    obtain ⟨q, hq, hpb⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [imgInstr_stx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs idx hidx) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep
      (.inl ⟨_, A, A, v, rfl, by simp [storeStruct?]⟩) (hidxe.trans hvi))
  · simp only [icase, if_true, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨⟨A, n⟩, hacc⟩, -⟩, -⟩, hidx⟩, hbf⟩ := hg
    obtain ⟨q, hq, hpb⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [imgInstr_ldx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regs idx hidx) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep
      (.inr ⟨_, d, A, rfl, by simp [loadStruct?]⟩) (hidxe.trans hvi))

/-- The bytes of the `n` words of an array of length `n` from its base lie in `imgStores`. -/
theorem arr_mem_imgStores {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {q A : String}
    {n : Nat} (hq : slotArr q = some (A, n)) :
    ∀ x ∈ (⟨base A, 8 * n⟩ : Rng 64), x ∈ imgStores frame slotArr base := by
  intro x hx
  rw [Rng.mem_def] at hx
  refine cell_mem_imgStores (j := (x - base A).toNat / 8) hq (by simp only at hx; omega) x ?_
  rw [Rng.mem_def]
  grind only [= BitVec.toNat_sub, = BitVec.toNat_add, BitVec.toNat_mod_cancel', = BitVec.toNat_ofNat]

/-- **The zeroing of a checked image step on the plain route** writes the words of an array:
    under `ImgRel`, at an array zeroing `ZEROARR` before the last instruction of a body that
    passes `imgGateB`, the base register holds `base A` and the word count is the length of
    the array. -/
theorem zarr_mem_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1) {b : String} {n w : Nat}
    {p : BitVec 64} (hx : bi.li_i = .Lopn [] "ZEROARR" [.reg b, .imm n, .imm w])
    (hp : sa.reg.getW b 64 = some p) :
    ∀ x ∈ (⟨p, 8 * n⟩ : Rng 64), x ∈ imgStores frame slotArr base := by
  have hg := instrGateB_of_imgGateB hgate hb hlt
  unfold instrGateB at hg
  have hc : icase frame bi.li_i = .zarr b n w := by rw [hx]; simp [icase, castTagW]
  rw [hc] at hg
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
  obtain ⟨⟨hm, -⟩, hbf⟩ := hg
  cases hacc : accArr slotArr c sa.reg.lpc b with
  | none => rw [hacc] at hm; cases hm
  | some An =>
    obtain ⟨A, m⟩ := An
    rw [hacc] at hm
    obtain rfl : n = m := by simpa using hm
    obtain ⟨q, hq, hpb⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    exact arr_mem_imgStores hq

/-- **The constant-index store of a checked image step on the plain route** writes a word of
    an array: under `ImgRel`, at a `STOREIMM` before the last instruction of a body that passes
    `imgGateB`, the base register holds `base A` and the index is below the length of the
    array. -/
theorem simm_mem_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1) {d b v : String}
    {k : Nat} {p : BitVec 64} (hx : bi.li_i = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k])
    (hp : sa.reg.getW b 64 = some p) :
    ∀ x ∈ (⟨p + BitVec.ofNat 64 (8 * k), 8⟩ : Rng 64), x ∈ imgStores frame slotArr base := by
  have hg := instrGateB_of_imgGateB hgate hb hlt
  unfold instrGateB at hg
  have hc : icase frame bi.li_i = .simm d b v k := by rw [hx]; simp [icase, castTagW]
  rw [hc] at hg
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
  obtain ⟨⟨hm, hbf⟩, -⟩ := hg
  cases hacc : accArr slotArr c sa.reg.lpc b with
  | none => rw [hacc] at hm; cases hm
  | some An =>
    obtain ⟨A, m⟩ := An
    rw [hacc] at hm
    have hk : k < m := by simpa using hm
    obtain ⟨q, hq, hpb⟩ := ptr_of_reload hsep (.of_imgGateB hgate) hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    exact cell_mem_imgStores hq hk

/-- **The accesses of a checked image step on the plain route.** Under `ImgRel`, at an
    instruction before the last of a body that passes `imgGateB`, a successful checked step of
    the image stores in and loads from `imgStores`: a frame word, or by an indexed store or
    load the word `cellAt (base A) vi` of its array. -/
theorem accessIn_of_imgStep {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateB frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    AccessIn (imgStores frame slotArr base) frame c sa :=
  accessIn_of_cases hb frame_mem_imgStores
    (fun _ _ _ _ _ hx hp hvi => idx_mem_of_imgStep hsep hgate P hrel hb hlt hstep hx hp hvi)
    (fun _ _ _ hcl _ => by
      have h0 := cellA_none_of_instrGateB (instrGateB_of_imgGateB hgate hb hlt)
      rcases hcl with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h0] at h <;> cases h)
    (fun _ _ _ _ hx hp => zarr_mem_of_imgStep hsep hgate hrel hb hlt hx hp)
    (fun _ _ _ _ _ hx hp => simm_mem_of_imgStep hsep hgate hrel hb hlt hx hp)

/-! ## 3. The route with carry chains -/

/-- **The indexed access of a checked image step with carry chains** accesses an array word:
    `idx_mem_of_imgStep` under `ImgRelW` and `imgGateBW`. -/
theorem idx_mem_of_imgStepW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hgate : imgGateBW frame slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base c s sa zf) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {b idx : String} {sc : Nat} {p vi : BitVec 64}
    (hx : (∃ d v, bi.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
      ∨ ∃ d, bi.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc])
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
  have hkc : classifyK bi.li_i = none := by
    rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [classifyK]
  have hci : carryI? bi.li_i = none := by
    rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [carryI?]
  have hcI : idx ∉ carryIns bi.li_i := by
    rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [carryIns]
  have hiR : idx ∈ readNames bi.li_i := by
    rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [readNames, srcNames]
  rw [hci] at hg
  by_cases hsc : sc = 8
  swap
  · rw [icase_idx_ne hsc hx] at hg
    simp [castGateB, hkc] at hg
  subst hsc
  have hrd : readOkB (gateReadSet frame (oneBitAt frame c sa.reg.lpc) bi.li_i) bi.li_i
      = true := by
    simpa [castReadB, hkc] using hrd0
  rcases hx with ⟨d, v, hx⟩ | ⟨d, hx⟩
  · have hc : icase frame bi.li_i = .stx d b idx v := by rw [hx]; simp [icase]
    simp only [hc, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨A, n⟩, hacc⟩, hidx⟩, hbf⟩, -⟩ := hg
    simp only [gateReadSet, hc] at hrd
    have hidxW : idx ∉ oneBitAt frame c sa.reg.lpc := readOkB_spec hrd hiR hcI
    obtain ⟨q, hq, hpb⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [hx, imgInstr_stx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hidx hidxW) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep
      (.inl ⟨_, A, A, v, rfl, by simp [storeStruct?]⟩) (hidxe.trans hvi))
  · have hc : icase frame bi.li_i = .ldx d b idx := by rw [hx]; simp [icase]
    simp only [hc, Bool.and_eq_true, Option.isNone_iff_eq_none,
      Option.isSome_iff_exists] at hg
    obtain ⟨⟨⟨⟨⟨⟨A, n⟩, hacc⟩, -⟩, -⟩, hidx⟩, hbf⟩ := hg
    simp only [gateReadSet, hc] at hrd
    have hidxW : idx ∉ oneBitAt frame c sa.reg.lpc := readOkB_spec hrd hiR hcI
    obtain ⟨q, hq, hpb⟩ := ptr_of_reloadW hsep hgate hrel hacc hbf
    rw [hp] at hpb
    cases hpb
    rw [hx, imgInstr_ldx slotArr c _ hacc] at hstep
    have hidxe := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hidx hidxW) 64
    exact cell_mem_imgStores hq (idx_lt_of_checked hstep
      (.inr ⟨_, d, A, rfl, by simp [loadStruct?]⟩) (hidxe.trans hvi))

/-! ## 4. Bodies with cells -/

/-- **The accesses of a step of a body with cells.** Where the base register of every cell
    access holds the pointer of its array, a cell store or load of the body accesses the frame
    word of its cell name (`CellFrames`); so the step stores in and loads from `imgStores` when
    its indexed access, its array zeroing and its constant-index store do. -/
theorem accessIn_cellBody {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hF : CellFrames frame slotArr base rsp body) {sa : LstateA}
    (hptr : ∀ B A m, accArr slotArr body sa.reg.lpc B = some (A, m) →
      DecodePrinted.gpOk B = true → frame B = none → sa.reg.getW B 64 = some (base A))
    {b0 : Linstr} (hb0 : body[sa.reg.lpc]? = some b0)
    (hI : ∀ b idx sc p vi,
      ((∃ d v, b0.li_i = .Lopn [.reg d] "STOREIDX" [.arrIdx b idx sc, .reg v])
        ∨ ∃ d, b0.li_i = .Lopn [.reg d] "LOADIDX" [.arrIdx b idx sc]) →
      sa.reg.getW b 64 = some p → sa.reg.getW idx 64 = some vi →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 (sc * vi.toNat), 8⟩ : Rng 64),
        x ∈ imgStores frame slotArr base)
    (hZ : ∀ b n w p, b0.li_i = .Lopn [] "ZEROARR" [.reg b, .imm n, .imm w] →
      sa.reg.getW b 64 = some p → ∀ x ∈ (⟨p, 8 * n⟩ : Rng 64), x ∈ imgStores frame slotArr base)
    (hS : ∀ d b v k p, b0.li_i = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k] →
      sa.reg.getW b 64 = some p →
      ∀ x ∈ (⟨p + BitVec.ofNat 64 (8 * k), 8⟩ : Rng 64), x ∈ imgStores frame slotArr base) :
    AccessIn (imgStores frame slotArr base) frame body sa :=
  accessIn_of_cases hb0 frame_mem_imgStores hI (fun B off p hcl hp => by
    rcases hcl with ⟨S, hcl⟩ | ⟨D, hcl⟩
    · obtain ⟨A, n, hacc, hBf, -, hfr⟩ := hF.st _ _ B off S hb0 hcl
      have hpA := hptr B A n hacc (hF.stGp _ _ B off S hb0 hcl) hBf
      rw [hp] at hpA
      cases hpA
      exact frame_mem_imgStores _ _ hfr
    · obtain ⟨A, n, hacc, hBf, hfr, -⟩ := hF.ld _ _ D B off hb0 hcl
      have hpA := hptr B A n hacc (hF.ldGp _ _ D B off hb0 hcl) hBf
      rw [hp] at hpA
      cases hpA
      exact frame_mem_imgStores _ _ hfr) hZ hS

/-! ## 5. The state after the first of two steps -/

/-- **The state after one step of the address machine on the plain route** is related to the
    image state, or stands at a label and stores and loads nothing. -/
theorem rel_or_accessIn_plain {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr c = true)
    (hgate : imgGateB frame slotArr c = true) (fn : String) {M : Set (BitVec 64)}
    {s t : LstateMF} {sa : LstateA} (hrel : ImgRel frame slotArr base c s sa s.zf)
    {bi : Linstr} (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t)
    {sa1 : LstateA} {z1 : Bool} (hst : stepA frame c sa s.zf = some (sa1, z1)) :
    ImgRel frame slotArr base c t sa1 z1 ∨ AccessIn M frame c sa1 := by
  by_cases hcnd : ∃ cc l, bi.li_i = .Lcond cc l
  · obtain ⟨cc, l, hx⟩ := hcnd
    obtain ⟨-, -, sa1', hst', hc⟩ := img_step_cond rsp hphys hgate fn s t sa bi cc l hrel hb hlt
      hx hstep
    rw [hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    rcases hc with h | ⟨⟨bl, ii, l', hbl, hli⟩, -⟩
    · exact Or.inl h
    · exact Or.inr (accessIn_of_label hbl hli)
  · obtain ⟨-, -, sa1', hst', hr⟩ :=
      img_stepStraight hsep hphys hgate _ hrel hb hlt (fun cc l e => hcnd ⟨cc, l, e⟩) hstep
    rw [hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact Or.inl hr

/-- **The state after one step of the address machine on a body with cells** is related to
    the image state by `R`, or stands at a label and stores and loads nothing; from the step of
    the image at a conditional branch (`CondStep`) and at any other instruction. -/
theorem rel_or_accessIn_cells {R : LstateMF → LstateA → Bool → Prop}
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
    R t sa1 z1 ∨ AccessIn M frame body sa1 := by
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
      exact Or.inr (accessIn_of_label hb1 (llabel_of_cellMove hli))
  · obtain ⟨sa1', hst', hr⟩ := hstr (fun cc l e => hcnd ⟨cc, l, e⟩)
    obtain ⟨-, he⟩ := stepA_cellBody hF hptr s.zf
    rw [he, hst'] at hst
    simp only [Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact Or.inl hr

/-! ## 6. The runs -/

/-- **The image simulated by the address machine, with its accesses.**
    `ImageAddrSim.image_addr_sim` with the stores and loads of the run in `imgStores`: every
    step of the address machine stores to and loads from frame words and array words
    `cellAt (base A) j`, `j < n`. -/
theorem image_addr_sim_access {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (fn : String) :
    ∀ (fuel : Nat) (s t : LstateMF) (sa : LstateA) (zf : Bool), s.prog.lfn = fn →
      ImgRel frame slotArr base body s sa zf →
      lsemFuelMemFk true (singletonProgM fn (virtImg slotArr body)) fuel s = some t →
      ∃ fuel' sa' zf', runA frame body fuel' sa zf = some (sa', zf')
        ∧ ImgRel frame slotArr base body t sa' zf'
        ∧ RunSafe frame body (LoadSafeAt rsp body) fuel' sa zf
        ∧ RunSafe frame body (AccessIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  intro fuel s t sa zf hfn hrel hrun
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame) (body := body)
    (P := singletonProgM fn (virtImg slotArr body))
    (R := fun s sa zf => s.prog.lfn = fn ∧ ImgRel frame slotArr base body s sa zf)
    (Q := fun x => LoadSafeAt rsp body x ∧ AccessIn (imgStores frame slotArr base) frame body x)
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
      refine ⟨hh, ⟨hsafe, accessIn_of_imgStep hsep hgate _ hrel hb hlt he⟩, sa1, z1, hst1, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, z2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_accessIn_plain hsep hphys hgate fn hrel hb hlt he hst1 with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, z2, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

/-- **The image of the cell body simulated on the body, with its accesses.**
    `ImageAddrCellsLoop.image_addr_simB'` with the stores and loads of the run in `imgStores`:
    an indexed store or load accesses an array word and a cell store or load `mem.B.off`
    accesses the frame word of its cell name. -/
theorem image_addr_simB'_access {frame : String → Option (BitVec 64)}
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
      ∧ RunSafe frame body (AccessIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRel frame slotArr base (cellBody slotArr body) s sa zf)
    (Q := fun x => SafeW rsp body x ∧ AccessIn (imgStores frame slotArr base) frame body x)
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
      have hS : AccessIn (imgStores frame slotArr base) frame body sa := by
        have hb' := hb
        rw [cellBody_getElem?] at hb'
        obtain ⟨b0, hb0, he0⟩ := Option.map_eq_some_iff.mp hb'
        refine accessIn_cellBody hF hptr hb0 (fun b idx sc p vi hx hp hvi => ?_)
          (fun b n w p hx hp => ?_) (fun d b v k p hx hp => ?_)
        · have hc0 : cellA? b0.li_i = none := by
            rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          exact idx_mem_of_imgStep hsep hgate _ hrel hb hlt he hx hp hvi
        · have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          exact zarr_mem_of_imgStep hsep hgate hrel hb hlt hx hp
        · have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          exact simm_mem_of_imgStep hsep hgate hrel hb hlt hx hp
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ := cell_step' hsep hphys hgate hN hF fn hrel hb hlt he
      refine ⟨hh, ⟨hsafe, hS⟩, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_accessIn_cells (img_step_cond rsp hphys hgate fn) hF hrel hptr hb hlt he
          (fun hnc => (img_stepStraight hsep hphys hgate _ hrel hb hlt hnc he).2.2) hst
          with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

/-- **The image of the cell body simulated on the body, with carry chains and with its
    accesses.** `ImageAddrCellsLoop.image_addr_simBW'` with the stores and loads of the run in
    `imgStores`: an indexed store or load accesses an array word, a cell store or load
    `mem.B.off` accesses the frame word of its cell name, and a carry-chain destination, an
    immediate move and a select destination in a frame slot write their frame words. -/
theorem image_addr_simBW'_access {frame : String → Option (BitVec 64)}
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
      ∧ RunSafe frame body (AccessIn (imgStores frame slotArr base) frame body) fuel' sa zf := by
  obtain ⟨f, sa', zf', h1, ⟨-, h2⟩, h3⟩ := runA_of_steps_pred (frame := frame)
    (body := body) (P := singletonProgM fn (virtImg slotArr (cellBody slotArr body)))
    (R := fun s sa zf => s.prog.lfn = fn
      ∧ ImgRelW frame slotArr base (cellBody slotArr body) s sa zf)
    (Q := fun x => SafeW rsp body x ∧ AccessIn (imgStores frame slotArr base) frame body x)
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
      have hS : AccessIn (imgStores frame slotArr base) frame body sa := by
        have hb' := hb
        rw [cellBody_getElem?] at hb'
        obtain ⟨b0, hb0, he0⟩ := Option.map_eq_some_iff.mp hb'
        have hgW : instrGateBW frame slotArr (cellBody slotArr body) sa.reg.lpc bi.li_i
            = true := by
          simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hgate
          have := hgate.1.1 sa.reg.lpc hlt
          rw [hb] at this
          simpa using this
        refine accessIn_cellBody hF hptr hb0 (fun b idx sc p vi hx hp hvi => ?_)
          (fun b n w p hx hp => ?_) (fun d b v k p hx hp => ?_)
        · have hc0 : cellA? b0.li_i = none := by
            rcases hx with ⟨_, _, hx⟩ | ⟨_, hx⟩ <;> rw [hx] <;> simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          exact idx_mem_of_imgStepW hsep hgate _ hrel hb hlt he hx hp hvi
        · have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          rw [hx] at hgW
          simp [instrGateBW, gateAtW, carryI?, icase, castTagW] at hgW
        · have hc0 : cellA? b0.li_i = none := by rw [hx]; simp [cellA?]
          rw [cellMove_of_none hc0] at he0
          subst he0
          rw [hx] at hgW
          simp [instrGateBW, gateAtW, carryI?, icase, castTagW] at hgW
      obtain ⟨hh, hsafe, sa1, hst, hc⟩ :=
        cell_stepW' hsep hphys hgate hN hF fn hcond hrel hb hlt he
      refine ⟨hh, ⟨hsafe, hS⟩, sa1, s1.zf, hst, ?_⟩
      rcases hc with hr | ⟨hh1, hsafe1, sa2, hst2, hr⟩
      · exact Or.inl ⟨hlfn, hr⟩
      · rcases rel_or_accessIn_cells hcond hF hrel hptr hb hlt he
          (fun hnc => (img_stepW hsep hphys hgate _ hrel hb hlt hnc he).2.2) hst
          with hr1 | hs1
        · exact Or.inl ⟨hlfn, hr1⟩
        · exact Or.inr ⟨hh1, ⟨hsafe1, hs1⟩, sa2, s1.zf, hst2, hlfn, hr⟩)
    fuel s t sa zf ⟨hfn, hrel⟩ hrun
  exact ⟨f, sa', zf', h1, h2, h3.mono fun _ h => h.1, h3.mono fun _ h => h.2⟩

/-! ## 7. The stores of the runs -/

/-- **The image simulated by the address machine, with its stores**: the stores of
    `image_addr_sim_access`. -/
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
        ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf :=
  fun fuel s t sa zf hfn hrel hrun => by
    obtain ⟨f, sa', zf', h1, h2, h3, h4⟩ :=
      image_addr_sim_access hsep hphys hgate fn fuel s t sa zf hfn hrel hrun
    exact ⟨f, sa', zf', h1, h2, h3, h4.mono fun _ h => h.1⟩

/-- **The image of the cell body simulated on the body, with its stores**: the stores of
    `image_addr_simB'_access`. -/
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
      ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf :=
  by
  obtain ⟨f, sa', zf', h1, h2, h3, h4⟩ :=
    image_addr_simB'_access hsep hphys hgate hN hF fn fuel s t sa zf hfn hrel hrun
  exact ⟨f, sa', zf', h1, h2, h3, h4.mono fun _ h => h.1⟩

/-- **The image of the cell body simulated on the body, with carry chains and with its
    stores**: the stores of `image_addr_simBW'_access`. -/
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
      ∧ RunSafe frame body (StoreIn (imgStores frame slotArr base) frame body) fuel' sa zf :=
  by
  obtain ⟨f, sa', zf', h1, h2, h3, h4⟩ :=
    image_addr_simBW'_access hsep hphys hgate hN hF fn hcond fuel s t sa zf hfn hrel hrun
  exact ⟨f, sa', zf', h1, h2, h3, h4.mono fun _ h => h.1⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrStore
