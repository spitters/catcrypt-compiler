/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx

@[expose] public section

set_option autoImplicit false

/-!
# The window of an indexed store through a cell, found by the uses of its registers

The allocated body of `compileRegion` stores into a word of an array through a cell: it loads
the index register `X` from a frame slot or a literal, computes the address
`LEA:64 D, (B, X, 8)` of the word, loads the value and stores it with `MOV:64 mem.D.0, v`. The
passes after the allocation (spills, the constant-index fold, the scheduling of the gathered
blocks) place other instructions between the load of `X` and the address computation, and the
allocation reuses a register loaded much earlier as the index register. The image reads such a
store as the name-keyed store into the array (`JasminLsemAddrImage.cellIdxStore?`) when the load
of `X` is the last earlier instruction that writes `X` (`JasminLsemAddrImage.cidxStart`) and the
instructions between it and the address computation write neither `X` nor a frame-slot index.

This module states the completeness of the recogniser at this construct, for every body: the
window is recognised whatever instructions stand between the load of the index register and the
address computation, as long as they keep the index register and the index.

## Main results

* `keepsB_of_not_dst`: an `Lopn` whose destinations do not name `r` keeps `r`.
* `lastDefBelow_of_keep`: the last instruction below `n` that does not keep `X`, when every
  later instruction below `n` keeps it.
* `cidxStart_of_window`: the start of the window is the load of the index register.
* `cellIdxStore?_of_window`: a store through a cell whose address computation is two positions
  before it, whose value load is right before it, and whose index register is loaded at an
  earlier position `j` followed only by instructions that keep the index register and the index,
  is an indexed store through a cell.
* `cellIdxStore?_of_window_slotMov`: the same with the index loaded from a frame slot, where the
  load is no stored carry constant.
* `imgInstr_of_window`: its image is the name-keyed store into the array at the index.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CellStoreWindowImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx

/-- An `Lopn` none of whose destinations names `r` keeps `r`. -/
theorem keepsB_of_not_dst {ds : List LOperand} {o : String} {ss : List LOperand} {r : String}
    (h : r ∉ dstNames (.Lopn ds o ss)) : keepsB r (.Lopn ds o ss) = true := by
  simp only [dstNames, List.mem_flatMap, not_exists, not_and] at h
  simp only [keepsB, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false]
  intro op hop hb
  apply h op hop
  cases op <;> simp_all [opNames, opNamesB]

/-- The load of an operand of a window does not keep its destination. -/
theorem keepsB_cellOpMov {x : LinstrR} {d : String} {o : String ⊕ Nat}
    (h : cellOpMov? x = some (d, o)) : keepsB d x = false := by
  rcases cellOpMov?_cases h with ⟨q, hsm, -⟩ | ⟨n, rfl, -⟩
  · rcases slotMov?_cases hsm with rfl | rfl <;> simp [keepsB, opNamesB]
  · simp [keepsB, opNamesB]

/-- **The last instruction below `n` that does not keep `X`** is the instruction at `j < n`
    that does not keep `X`, when every instruction at a position between `j` and `n` keeps it. -/
theorem lastDefBelow_of_keep {X : String} {body : Lcmd} {j : Nat} {r : Linstr}
    (hr : body[j]? = some r) (hX : keepsB X r.li_i = false)
    (hkeep : ∀ p, j < p → ∀ x, body[p]? = some x → keepsB X x.li_i = true) :
    ∀ n, j < n → lastDefBelow X body n = some j := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge j n with hlt | hge
    · have hall : (body[n]?).all (fun i => keepsB X i.li_i) = true := by
        cases hb : body[n]? with
        | none => rfl
        | some x => simpa using hkeep n hlt x hb
      simp only [lastDefBelow, hall, ite_true]
      exact ih hlt
    · have e : n = j := by omega
      subst e
      simp [lastDefBelow, hr, hX]

/-- **The start of the window is the load of the index register**: with the address computation
    `LEA:64 D, (B, X, 8)` at `k - 2` and the load of `X` at `j < k - 2` followed by instructions
    that keep `X`, `cidxStart body k = j`. -/
theorem cidxStart_of_window {body : Lcmd} {k j : Nat} {l r : Linstr} {D B X : String}
    {idx : String ⊕ Nat} (hl : body[k - 2]? = some l)
    (hli : l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8]) (hj : j < k - 2)
    (hr : body[j]? = some r) (hrm : cellOpMov? r.li_i = some (X, idx))
    (hkeep : ∀ p, j < p → p < k - 2 → ∃ x, body[p]? = some x ∧ idxKeepB X idx x.li_i = true) :
    cidxStart body k = j := by
  have hlast : lastDefBelow X body (k - 2) = some j :=
    lastDefBelow_of_keep hr (keepsB_cellOpMov hrm) (fun p hp x hx => by
      by_cases hpk : p < k - 2
      · obtain ⟨x', hx', hk'⟩ := hkeep p hp hpk
        rw [hx] at hx'
        obtain rfl := Option.some.inj hx'
        simp only [idxKeepB, Bool.and_eq_true] at hk'
        exact hk'.1
      · omega) (k - 2) hj
  obtain ⟨ii, li⟩ := l
  simp only at hli
  subst hli
  simp [cidxStart, hl, hlast]

/-- **Completeness of the recogniser at a store through a cell**, for every body: the store
    `MOV:64 c, v` at `k` through the cell `mem.D.0`, with the address computation
    `LEA:64 D, (B, X, 8)` at `k - 2`, `B` holding the pointer of the array `A` of length `n`
    there, the load of the value into `d1 ≠ D` at `k - 1`, and the load of `X` from `idx` at a
    position `j ≤ k - 3` that is no stored carry constant, followed up to the address
    computation only by instructions that keep `X` and `idx`, is the indexed store of `v` into
    `A` at `idx`. -/
theorem cellIdxStore?_of_window {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {k j : Nat} {c D B X v d1 A : String} {src idx : String ⊕ Nat} {n : Nat} {l r m : Linstr}
    (hc : cellParts? c = some (D, 0)) (hv : v ≠ D) (h3 : 3 ≤ k)
    (hl : body[k - 2]? = some l) (hli : l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8])
    (hm : body[k - 1]? = some m) (hmm : cellOpMov? m.li_i = some (d1, src)) (hd1 : d1 ≠ D)
    (hj : j + 3 ≤ k) (hr : body[j]? = some r) (hrm : cellOpMov? r.li_i = some (X, idx))
    (hok : cellIdxOkB slotArr D d1 idx = true) (hbs : bitStore? body j r.li_i = none)
    (hkeep : ∀ p, j < p → p < k - 2 → ∃ x, body[p]? = some x ∧ idxKeepB X idx x.li_i = true)
    (hacc : accArr slotArr body (k - 2) B = some (A, n)) :
    cellIdxStore? slotArr body k (.Lopn [.reg c] "MOV:64" [.reg v]) = some (A, n, idx, v) := by
  have hs := cidxStart_of_window hl hli (by omega) hr hrm hkeep
  have hrun : idxKeepRunB X idx body (cidxStart body k + 1) (k - 2) = true := by
    simp only [idxKeepRunB, List.all_eq_true, List.mem_range, hs]
    intro t ht
    obtain ⟨x, hx, hkx⟩ := hkeep (j + 1 + t) (by omega) (by omega)
    simp [hx, hkx]
  unfold cellIdxStore?
  simp only [hc, hl, hs, hr, hm, hli, hrm, hmm]
  rw [if_pos ⟨rfl, h3, rfl, hv, rfl, rfl, rfl, hd1, hok, by omega, hbs, by rwa [hs] at hrun⟩]
  simp [hacc]

/-- `cellIdxStore?_of_window` at an index loaded from a frame slot by a move between names,
    which is no stored carry constant. -/
theorem cellIdxStore?_of_window_slotMov {slotArr : String → Option (String × Nat)}
    {body : Lcmd} {k j : Nat} {c D B X v d1 A q : String} {src : String ⊕ Nat} {n : Nat}
    {l r m : Linstr}
    (hc : cellParts? c = some (D, 0)) (hv : v ≠ D) (h3 : 3 ≤ k)
    (hl : body[k - 2]? = some l) (hli : l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8])
    (hm : body[k - 1]? = some m) (hmm : cellOpMov? m.li_i = some (d1, src)) (hd1 : d1 ≠ D)
    (hj : j + 3 ≤ k) (hr : body[j]? = some r) (hsm : slotMov? r.li_i = some (X, q))
    (hok : cellIdxOkB slotArr D d1 (.inl q) = true)
    (hkeep : ∀ p, j < p → p < k - 2 → ∃ x, body[p]? = some x ∧ idxKeepB X (.inl q) x.li_i = true)
    (hacc : accArr slotArr body (k - 2) B = some (A, n)) :
    cellIdxStore? slotArr body k (.Lopn [.reg c] "MOV:64" [.reg v]) = some (A, n, .inl q, v) :=
  cellIdxStore?_of_window hc hv h3 hl hli hm hmm hd1 hj hr (by simp [cellOpMov?, hsm]) hok
    (bitStore?_of_slotMov hsm) hkeep hacc

/-- **The image of such a store** is the name-keyed store into the array at the index
    (`cellStoreImg`). -/
theorem imgInstr_of_window {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {k j : Nat} {c D B X v d1 A : String} {src idx : String ⊕ Nat} {n : Nat} {l r m : Linstr}
    (hc : cellParts? c = some (D, 0)) (hv : v ≠ D) (h3 : 3 ≤ k)
    (hl : body[k - 2]? = some l) (hli : l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8])
    (hm : body[k - 1]? = some m) (hmm : cellOpMov? m.li_i = some (d1, src)) (hd1 : d1 ≠ D)
    (hj : j + 3 ≤ k) (hr : body[j]? = some r) (hrm : cellOpMov? r.li_i = some (X, idx))
    (hok : cellIdxOkB slotArr D d1 idx = true) (hbs : bitStore? body j r.li_i = none)
    (hkeep : ∀ p, j < p → p < k - 2 → ∃ x, body[p]? = some x ∧ idxKeepB X idx x.li_i = true)
    (hacc : accArr slotArr body (k - 2) B = some (A, n)) :
    imgInstr slotArr body k (.Lopn [.reg c] "MOV:64" [.reg v]) = cellStoreImg A n idx v :=
  imgInstr_cellIdxStore slotArr
    (cellIdxStore?_of_window hc hv h3 hl hli hm hmm hd1 hj hr hrm hok hbs hkeep hacc)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CellStoreWindowImage
