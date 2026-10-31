/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse

/-!
# The image class under the fusion post-pass of the region route

The post-pass `regionPostFuse` of the region allocation runs the high-product fusion in the
mode that saves `RDX` (`PhysImgFuse.physImgB_fuseMulHiBody`) and then the dead-write
elimination `deadWriteRet` on every function body. The elimination deletes a pure register
write whose register is next accessed by a write of a widening multiply (`killedByMulx`).
The reads the elimination consults (`symReads`) include the base register of every indexed
operand, so the base of a kept access is not next written by a widening multiply. Hence no
deleted instruction is a move into a name that the reload scan of a later kept access
carries across it, and `PhysImgPass.physImgB_kept_of_passed` applies.

## Main results

* `scanExit_cons`: the scan of a body with a first instruction.
* `deadWriteMarks_drop`: the marks of a suffix are the suffix of the marks.
* `scanExit_ne_of_killedByMulx`: the scan of a kept access never carries a name that is next
  written by a widening multiply.
* `killedByMulx_of_mem_symReads`: a name a kept instruction reads is not next written by a
  widening multiply from that instruction on.
* `physImgB_deadWriteRet`: the dead-write elimination keeps the image class.
* `physImgB_regionPostFuse`: the first body of `regionPostFuse P` is in the image class when
  the first body of `P` is and the side conditions of both passes hold.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgPost

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLICM (operandReads instrReadRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFuse
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (idxBases)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (fuseMulHiBody fuseMulHiLprog
  fuseMulHiAux ScratchEnv)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The scan and the marks of a suffix -/

/-- The scan of `s :: rest` from position `n + 1` is the scan of `rest` from `n`, continued
    through `s`. -/
theorem scanExit_cons (s : Linstr) (rest : Lcmd) : ∀ (n : Nat) (x : String),
    scanExit slotArr (s :: rest) (n + 1) x =
      match scanExit slotArr rest n x with
      | some y => scanExit slotArr [s] 1 y
      | none => none
  | 0, x => by
    simp only [scanExit, List.getElem?_cons_zero]
  | n + 1, x => by
    have ih := scanExit_cons s rest n
    rw [scanExit, List.getElem?_cons_succ]
    conv_rhs => rw [scanExit]
    cases rest[n]? with
    | none => rfl
    | some j =>
      simp only
      cases slotMov? j.li_i with
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        split_ifs <;> simp [ih]
      | none =>
        simp only
        cases j.li_i with
        | Lopn ds o ss => simp only; split_ifs <;> simp [ih]
        | _ => rfl

theorem deadWriteMarks_drop : ∀ (L : Lcmd) (n : Nat),
    (deadWriteMarks L).drop n = deadWriteMarks (L.drop n)
  | [], n => by simp [deadWriteMarks]
  | _ :: _, 0 => rfl
  | i :: L, n + 1 => by
    simp only [deadWriteMarks, List.drop_succ_cons]
    exact deadWriteMarks_drop L n

/-- The marks of a body with a first instruction `s`: a mark of `s` that is set records a pure
    register write whose register is next written by a widening multiply. -/
theorem deadWriteMarks_cons (s : Linstr) (rest : Lcmd) :
    ∃ mk, deadWriteMarks (s :: rest) = (s, mk) :: deadWriteMarks rest ∧
      (mk = true → ∀ d, pureWrDst? s.li_i = some d →
        killedByMulx d (deadWriteMarks rest) = true) := by
  refine ⟨_, rfl, fun h d hd => ?_⟩
  simp only [hd, Bool.and_eq_true] at h
  exact h.2

theorem slotMov?_mnem {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q)) :
    ∃ o, x = .Lopn [.reg d] o [.reg q] ∧ (o = "MOVQ" ∨ o = "MOV:64") := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with h1
    cases h
    exact ⟨_, rfl, h1⟩
  · cases h

theorem pureWrDst?_of_slotMov {x : LinstrR} {d q : String} (h : slotMov? x = some (d, q)) :
    pureWrDst? x = some d := by
  obtain ⟨o, rfl, ho⟩ := slotMov?_mnem h
  rcases ho with rfl | rfl
  · simp [pureWrDst?]
  · have : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
    simp [pureWrDst?, this]

/-- One step of the scan through `s` from a name `y` carried out of the rest: the carried name
    is `y`, and `s` is no widening multiply naming `y`, or `s` is a move of `c` into `y`. -/
theorem scanExit_one {s : Linstr} {y c : String} (h : scanExit slotArr [s] 1 y = some c) :
    (c = y ∧ mulxWrites y s.li_i = false) ∨ slotMov? s.li_i = some (y, c) := by
  simp only [scanExit, List.getElem?_cons_zero] at h
  cases hm : slotMov? s.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    rw [hm] at h
    obtain ⟨o, hx, -⟩ := slotMov?_mnem hm
    simp only at h
    split_ifs at h with h1 h2 h3
    · subst h1; cases h; exact Or.inr rfl
    · cases h; exact Or.inl ⟨rfl, by simp [hx, mulxWrites]⟩
  | none =>
    rw [hm] at h
    simp only at h
    cases hx : s.li_i with
    | Lopn ds o ss =>
      rw [hx] at h
      simp only at h
      split_ifs at h with h1
      cases h
      refine Or.inl ⟨rfl, ?_⟩
      unfold mulxWrites
      split
      · rename_i heq
        cases heq
        simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB, Bool.or_eq_true,
          beq_iff_eq, not_or] at h1
        simp [Ne.symm h1.1.1, Ne.symm h1.2.1]
      · rfl
    | _ => rw [hx] at h; cases h

/-! ## 2. The scan of a kept access -/

/-- **A scan never carries a name killed by a widening multiply.** Let the instruction at
    position `n` of `seg` be kept with base `x`, and let `x` not be next written by a widening
    multiply from `n` on. Then the scan of `x` from `n` does not leave `seg` carrying a name `c`
    that is next written by a widening multiply in `seg`. -/
theorem scanExit_ne_of_killedByMulx : ∀ (seg : Lcmd) (n : Nat) (c x : String) (i : Linstr),
    killedByMulx c (deadWriteMarks seg) = true → (deadWriteMarks seg)[n]? = some (i, false) →
    killedByMulx x (deadWriteMarks (seg.drop n)) = false →
    scanExit slotArr seg n x ≠ some c
  | [], n, _, _, _, _, hn, _ => by simp [deadWriteMarks] at hn
  | s :: rest, 0, c, x, _, hk, _, hb => by
    simp only [scanExit, ne_eq, Option.some.injEq]
    rintro rfl
    simp only [List.drop_zero] at hb
    rw [hb] at hk; cases hk
  | s :: rest, n + 1, c, x, i, hk, hn, hb => by
    have ih := scanExit_ne_of_killedByMulx rest n
    obtain ⟨mk, hcons, hmark⟩ := deadWriteMarks_cons s rest
    rw [hcons, List.getElem?_cons_succ] at hn
    rw [hcons] at hk
    simp only [List.drop_succ_cons] at hb
    rw [scanExit_cons]
    cases hy : scanExit slotArr rest n x with
    | none => simp
    | some y =>
      simp only
      intro hc
      refine ih y x i ?_ hn hb hy
      rcases scanExit_one hc with ⟨rfl, hmx⟩ | hmv
      · cases mk
        · simp only [killedByMulx, hmx, Bool.false_or, Bool.and_eq_true] at hk
          exact hk.2.2
        · simpa [killedByMulx] using hk
      · cases mk
        · obtain ⟨o, hx, -⟩ := slotMov?_mnem hmv
          simp [killedByMulx, symReads, instrReadRegs, operandReads, idxBases, hx] at hk
        · exact hmark rfl y (pureWrDst?_of_slotMov hmv)

/-! ## 3. The dead-write elimination -/

/-- **A name a kept instruction reads is not killed.** When the instruction at position `m`
    of `L` is kept and reads `x` (`symReads`), `x` is not next written by a widening multiply
    from `m` on. -/
theorem killedByMulx_of_mem_symReads {L : Lcmd} {m : Nat} {i : Linstr}
    (hm : (deadWriteMarks L)[m]? = some (i, false)) {x : String}
    (hx : x ∈ symReads i.li_i) : killedByMulx x (deadWriteMarks (L.drop m)) = false := by
  have hh : (deadWriteMarks (L.drop m)).head? = some (i, false) := by
    rw [← deadWriteMarks_drop, List.head?_drop, hm]
  cases hM : deadWriteMarks (L.drop m) with
  | nil => rw [hM] at hh; cases hh
  | cons p rest =>
    rw [hM, List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp [killedByMulx, hx]

/-- **The dead-write elimination keeps the image class.** A body in the class `physImgB
    slotArr` keeps the class under `deadWriteRet`. -/
theorem physImgB_deadWriteRet {b : Lcmd} (h : physImgB slotArr b = true) :
    physImgB slotArr (deadWriteRet b) = true := by
  unfold deadWriteRet
  split
  · rename_i r hr
    split_ifs with hc
    · have hb : b = b.dropLast ++ [r] := (List.dropLast_append_getLast? r hr).symm
      set L := b.dropLast with hL
      have hfst := deadWriteMarks_fst L
      let M := deadWriteMarks L ++ [(r, false)]
      have hM : M.map Prod.fst = b := by simp [M, hfst, ← hb]
      have hK : (M.filter (fun p => !p.2)).map Prod.fst = dropDeadWriteBody L ++ [r] := by
        simp [M, dropDeadWriteBody, keptL]
      rw [← hK]
      refine physImgB_kept_of_passed (M := M) (by rw [hM]; exact h) ?_
      intro m i hm x hform _ p j hpm hp y hy d s hmv
      have hxr : x ∈ symReads i.li_i ∧ ∃ ds o ss, i.li_i = .Lopn ds o ss := by
        rcases hform with ⟨ds, o, y', ss, hx⟩ | ⟨ds, o, ss, hx, -⟩
        · exact ⟨by simp [hx, symReads, idxBases], _, _, _, hx⟩
        · exact ⟨by simp [hx, symReads, instrReadRegs, operandReads], _, _, _, hx⟩
      obtain ⟨hxr, ds, o, ss, hx⟩ := hxr
      have hlen : (deadWriteMarks L).length = L.length := by
        rw [← List.length_map (f := Prod.fst), hfst]
      by_cases hmL : m < L.length
      · have hm' : (deadWriteMarks L)[m]? = some (i, false) := by
          rwa [List.getElem?_append_left (by omega)] at hm
        have hp' : (deadWriteMarks L)[p]? = some (j, true) := by
          rwa [List.getElem?_append_left (by omega)] at hp
        have hLp : L.drop p = j :: L.drop (p + 1) := by
          have hpj : L[p]? = some j := by
            rw [← hfst, List.getElem?_map, hp']; rfl
          obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hpj
          rw [List.drop_eq_getElem_cons hlt, hget]
        have hmk := deadWriteMarks_drop L p
        rw [hLp, deadWriteMarks] at hmk
        have h0 := congrArg List.head? hmk
        rw [List.head?_drop, hp'] at h0
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at h0
        rw [pureWrDst?_of_slotMov hmv] at h0
        have hkill : killedByMulx d (deadWriteMarks (L.drop (p + 1))) = true :=
          ((Bool.and_eq_true _ _).mp h0.2.symm).2
        intro hdy
        subst hdy
        set seg := L.drop (p + 1)
        have hnseg : m - (p + 1) ≤ seg.length := by simp [seg]; omega
        have hseg : ((M.map Prod.fst).take m).drop (p + 1) = seg.take (m - (p + 1)) := by
          rw [hM, hb, List.take_append_of_le_length (by omega), List.drop_take]
        rw [hseg] at hy
        have hy' : scanExit slotArr seg (m - (p + 1)) x = some d := by
          rw [← List.take_append_drop (m - (p + 1)) seg, scanExit_append_left _ _ _ _ _
            (by simp; omega)]
          exact hy
        have hmseg : (deadWriteMarks seg)[m - (p + 1)]? = some (i, false) := by
          rw [← deadWriteMarks_drop, List.getElem?_drop]
          rw [show p + 1 + (m - (p + 1)) = m by omega]
          exact hm'
        have hbase : killedByMulx x (deadWriteMarks (seg.drop (m - (p + 1)))) = false :=
          killedByMulx_of_mem_symReads hmseg hxr
        exact scanExit_ne_of_killedByMulx seg (m - (p + 1)) d x i hkill hmseg hbase hy'
      · have hmeq : m = L.length := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          simp [M, hlen] at this; omega
        subst hmeq
        rw [List.getElem?_append_right (by omega)] at hm
        simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hm
        obtain ⟨rfl, -⟩ := hm
        simp [hx] at hc
    · exact h
  · exact h

/-! ## 4. The post-pass -/

/-- **The fusion post-pass keeps the image class.** Let the first body `b` of `P` be in the
    class `physImgB slotArr`, whose array slots are `qsave.` slots, and satisfy the site and
    home conditions of the fusion. Then the first body of `regionPostFuse P` is
    `deadWriteRet (fuseMulHiBody b true)`, and it is in the class. -/
theorem physImgB_regionPostFuse (P : Lprog)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (hb : P.lp_funcs.head?.map (·.2.lfd_body) = some b) (h : physImgB slotArr b = true)
    (hsite : fuseSiteOkB slotArr b = true) (hhome : homeOkB slotArr [] b = true) :
    (regionPostFuse P).lp_funcs.head?.map (·.2.lfd_body) =
        some (deadWriteRet (fuseMulHiBody b true)) ∧
      physImgB slotArr (deadWriteRet (fuseMulHiBody b true)) = true := by
  refine ⟨?_, physImgB_deadWriteRet (physImgB_fuseMulHiBody true hq h hsite hhome)⟩
  cases hP : P.lp_funcs with
  | nil => rw [hP] at hb; cases hb
  | cons f fs =>
    rw [hP] at hb
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hb
    subst hb
    simp [regionPostFuse, X86Backend.LprogOptPipeline.mapBodies, fuseMulHiLprog, hP]

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgPost
