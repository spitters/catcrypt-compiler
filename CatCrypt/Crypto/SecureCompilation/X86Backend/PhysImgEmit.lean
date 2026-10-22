/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysPositionEmitWF

/-!
# The image class of the allocator's output

The image check `physImgB slotArr body` (`JasminLsemAddrImage`) asks of a physical body that
every write to an array slot is the save of a register at its entry value, and that every
indexed access at stride `8` follows a reload of its base register from the slot of an array
(`reloadOf`, `accArr`). This module proves that the looped physical ABI export
`lfundefPhysAbiOfVirtCert` of a call-free body is in the class.

The reload scan is local (`reloadOf_append_left`, `reloadOf_append_right`), so the property
"every access of a block resolves inside the block" (`AccLocal`) is closed under
concatenation and `flatMap`. Each expansion arm of `physPositionEmit` is characterised over
the remapped operands it receives (`ArmOut`: every destination is an operand of the arm,
`R15`, `R14` or a cell name `mem.…`, and every mnemonic is the virtual one or a move); the
two access arms emit the reload `MOVQ R14, q` of the memref base, then only writes to `R15`,
then the access through `R14` (`loadIdx_accLocal`, `storeIdx_accLocal`); a constant-index
array write is emitted unchanged and its constant-shape base reload (`reloadArrImmBody`) is
the window `MOVQ R14, q` followed by the write through `R14`. The prologue is a
prefix of moves whose writes to array slots are saves (`physImgB_of_movePrefix`).

## Main results

* `accArr_of_reload`: a register reloaded from the slot of an array and not written since
  holds the pointer of that array.
* `physImgB_of_movePrefix`: the class of a body whose prefix is moves that save registers
  into their slots, and whose rest writes no array slot and resolves its accesses.
* The arm lemmas `legalizeMov_armOut`, `legalizeBinop_armOut`, `lowerTwoAddr_armOut`,
  `lowerTwoAddrShiftImm_armOut`, `lowerNativeShiftRotate_armOut`, `legalizeOneSrc_armOut`,
  `legalizeSpillDst_armOut`, `legalizeSibElem_armOut`, `reloadMemrefBase_armOut`,
  `legalizeMemLoad_armOut`, `legalizeMemStore_armOut`, `constIdxStore?_armOut`,
  `legalizeMemStoreK_armOut`, and the access windows `loadIdx_accLocal`,
  `storeIdx_accLocal`.
* `physPositionEmit_physImg`, `physBodyWithStores_physImg`: one position, and the stored body
  without its `LIVEPIN` instructions, write no array slot and resolve their accesses.
* `physImgB_lfundefPhysAbiOfVirtCert`: the class of the looped physical ABI export of a
  call-free body whose accesses have reloaded bases.
* `physPositionEmit_dst`, `physBodyWithStores_noQsaveWrite`: the stored body of a call-free
  body, for any argument loads and output stores, writes no register named `qsave.…`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-! ## 1. The reload scan is local -/

/-- A move of `slotMov?` is a single-destination, single-source operation. -/
theorem slotMov?_eq {x : LinstrR} {d s : String} (h : slotMov? x = some (d, s)) :
    ∃ o, x = .Lopn [.reg d] o [.reg s] := by
  unfold slotMov? at h
  split at h
  · split_ifs at h
    cases h
    exact ⟨_, rfl⟩
  · cases h

/-- The scan of `reloadOf` up to position `k` reads only the first `k` instructions. -/
theorem reloadOf_append_left (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (k : Nat) (x : String), k ≤ a.length →
      reloadOf slotArr (a ++ c) k x = reloadOf slotArr a k x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have ih := fun y => reloadOf_append_left slotArr a c k y (by omega)
    simp only [reloadOf, List.getElem?_append_left (by omega : k < a.length), ih]

/-- A reload that `reloadOf` finds inside a block is found at the same place after any
    prefix. -/
theorem reloadOf_append_right (slotArr : String → Option (String × Nat)) (a b : Lcmd) :
    ∀ (k : Nat) (x q : String), reloadOf slotArr b k x = some q →
      reloadOf slotArr (a ++ b) (a.length + k) x = some q
  | 0, _, _, h => by cases h
  | k + 1, x, q, h => by
    have ih := reloadOf_append_right slotArr a b k
    have hg : (a ++ b)[a.length + k]? = b[k]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rw [show a.length + (k + 1) = (a.length + k) + 1 from rfl]
    simp only [reloadOf, hg] at h ⊢
    cases hb : b[k]? with
    | none => simp [hb] at h
    | some j =>
      rw [hb] at h
      simp only at h ⊢
      cases hs : slotMov? j.li_i with
      | some p =>
        obtain ⟨d, s⟩ := p
        rw [hs] at h
        simp only at h ⊢
        split_ifs at h ⊢ <;> first | exact ih _ _ h | exact h
      | none =>
        rw [hs] at h
        simp only at h ⊢
        split at h <;> (try split_ifs at h ⊢) <;> first | exact ih _ _ h | cases h

/-- **The array of a reloaded base register.** Let instruction `j` of `body` be a move
    (`slotMov?`) of the slot `q` of an array into `b`, and let every instruction strictly
    between `j` and `k` be an `Lopn` none of whose destinations names `b` or an array slot
    (`dstHitB`). Then `b` holds the pointer of the array of `q` at `k`. -/
theorem accArr_of_reload {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {j k : Nat} {rl : Linstr} {b q : String} (hj : body[j]? = some rl)
    (hm : slotMov? rl.li_i = some (b, q)) (hq : (slotArr q).isSome = true) (hjk : j < k)
    (hbet : ∀ m, j < m → m < k → ∃ r, body[m]? = some r ∧
      ∃ ds o ss, r.li_i = .Lopn ds o ss ∧ ds.any (dstHitB slotArr b) = false) :
    accArr slotArr body k b = slotArr q := by
  suffices h : reloadOf slotArr body k b = some q by simp [accArr, h]
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = j
    · subst hk
      rw [reloadOf_succ_some hj hm]
      simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.mp hq]
    · obtain ⟨r, hr, ds, o, ss, hx, hd⟩ := hbet k (by omega) (by omega)
      have ih' := ih (by omega) (fun m h1 h2 => hbet m h1 (by omega))
      cases hs : slotMov? r.li_i with
      | none =>
        rw [reloadOf_succ_lopn hr hs hx]
        simp [hd, ih']
      | some p =>
        obtain ⟨d, s⟩ := p
        obtain ⟨o', ho⟩ := slotMov?_eq hs
        rw [ho] at hx
        cases hx
        simp [dstHitB] at hd
        rw [reloadOf_succ_some hr hs]
        simp [hd.1, hd.2, ih']

/-- `accOkB` reads the body only through the `isSome` of `accArr` at its position. -/
theorem accOkB_mono {slotArr : String → Option (String × Nat)} {b1 b2 : Lcmd} {k1 k2 : Nat}
    (hmono : ∀ x, (accArr slotArr b1 k1 x).isSome = true →
      (accArr slotArr b2 k2 x).isSome = true) (i : LinstrR)
    (h : accOkB slotArr b1 k1 i = true) : accOkB slotArr b2 k2 i = true := by
  revert h
  unfold accOkB
  split
  · split_ifs
    · split <;> simp_all
    · split <;> simp_all
    · exact arrImmImg_isSome_mono (fun x _ => hmono x)
    · simp
  · simp

/-- `accArr` is monotone along `reloadOf`. -/
theorem accArr_isSome_mono {slotArr : String → Option (String × Nat)} {b1 b2 : Lcmd}
    {k1 k2 : Nat}
    (h : ∀ x q, reloadOf slotArr b1 k1 x = some q → reloadOf slotArr b2 k2 x = some q)
    (x : String) (hx : (accArr slotArr b1 k1 x).isSome = true) :
    (accArr slotArr b2 k2 x).isSome = true := by
  unfold accArr at hx ⊢
  cases hr : reloadOf slotArr b1 k1 x with
  | none => simp [hr] at hx
  | some q => rw [h x q hr]; simpa [hr] using hx

/-! ## 2. Blocks whose accesses resolve locally -/

/-- The instruction is an indexed access, an `LOADIDX` or a `STOREIDX`. -/
def isAccB : LinstrR → Bool
  | .Lopn _ o _ => o == "LOADIDX" || o == "STOREIDX"
  | _ => false

/-- The instruction is a constant-index array write, a `ZEROARR` or a `STOREIMM`. -/
def isArrImmB : LinstrR → Bool
  | .Lopn _ o _ => o == "ZEROARR" || o == "STOREIMM"
  | _ => false

theorem accOkB_of_not_acc (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    {i : LinstrR} (h : isAccB i = false) (h' : isArrImmB i = false) :
    accOkB slotArr body k i = true := by
  cases i with
  | Lopn ds o ss =>
    simp only [isAccB, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [isArrImmB, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h'
    simp [accOkB, h.1, h.2, h'.1, h'.2]
  | _ => rfl

/-- Every indexed access of the block `l` resolves to an array inside `l`. -/
def AccLocal (slotArr : String → Option (String × Nat)) (l : Lcmd) : Prop :=
  ∀ k i, l[k]? = some i → accOkB slotArr l k i.li_i = true

theorem accLocal_of_noAcc {slotArr : String → Option (String × Nat)} {l : Lcmd}
    (h : ∀ r ∈ l, isAccB r.li_i = false) (h' : ∀ r ∈ l, isArrImmB r.li_i = false) :
    AccLocal slotArr l :=
  fun k _ hk => accOkB_of_not_acc slotArr l k (h _ (List.mem_of_getElem? hk))
    (h' _ (List.mem_of_getElem? hk))

theorem accLocal_nil (slotArr : String → Option (String × Nat)) : AccLocal slotArr [] :=
  accLocal_of_noAcc (by simp) (by simp)

theorem accLocal_append {slotArr : String → Option (String × Nat)} {a b : Lcmd}
    (ha : AccLocal slotArr a) (hb : AccLocal slotArr b) : AccLocal slotArr (a ++ b) := by
  intro k i hk
  by_cases hlt : k < a.length
  · rw [List.getElem?_append_left hlt] at hk
    refine accOkB_mono (accArr_isSome_mono ?_) _ (ha k i hk)
    intro x q h
    rw [reloadOf_append_left slotArr a b k x (by omega)]
    exact h
  · rw [List.getElem?_append_right (by omega)] at hk
    have e : k = a.length + (k - a.length) := by omega
    refine accOkB_mono (accArr_isSome_mono ?_) _ (hb _ i hk)
    intro x q h
    rw [e]
    exact reloadOf_append_right slotArr a b _ x q h

theorem accLocal_flatMap {α : Type} {slotArr : String → Option (String × Nat)} {l : List α}
    {f : α → Lcmd} (h : ∀ a ∈ l, AccLocal slotArr (f a)) :
    AccLocal slotArr (l.flatMap f) := by
  induction l with
  | nil => exact accLocal_nil slotArr
  | cons a l ih =>
    rw [List.flatMap_cons]
    exact accLocal_append (h a List.mem_cons_self)
      (ih fun a' ha' => h a' (List.mem_cons_of_mem a ha'))

theorem accLocal_dropLast {slotArr : String → Option (String × Nat)} {l : Lcmd}
    (h : AccLocal slotArr l) : AccLocal slotArr l.dropLast := by
  intro k i hk
  have hlt : k < l.dropLast.length := (List.getElem?_eq_some_iff.mp hk).1
  have hl : l = l.dropLast ++ l.drop (l.length - 1) := by
    rw [List.dropLast_eq_take, List.take_append_drop]
  have hk' : l[k]? = some i := by
    rw [hl, List.getElem?_append_left hlt]; exact hk
  refine accOkB_mono (accArr_isSome_mono ?_) _ (h k i hk')
  intro x q hx
  rw [← reloadOf_append_left slotArr l.dropLast (l.drop (l.length - 1)) k x (by omega), ← hl]
  exact hx

/-- A move is no indexed access. -/
theorem isAccB_of_slotMov {x : LinstrR} {p : String × String} (h : slotMov? x = some p) :
    isAccB x = false := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with h1
    rcases h1 with rfl | rfl <;> rfl
  · cases h

/-- A move is no constant-index array write. -/
theorem isArrImmB_of_slotMov {x : LinstrR} {p : String × String} (h : slotMov? x = some p) :
    isArrImmB x = false := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with h1
    rcases h1 with rfl | rfl <;> rfl
  · cases h

/-- The access is neither an indexed access nor a constant-index array write, or an indexed
    access at stride `8` through `R14`, or a zeroing or a constant-index store through `R14`,
    each of the form `accOkB` reads. -/
def AccR14 (x : LinstrR) : Prop :=
  (isAccB x = false ∧ isArrImmB x = false) ∨ (∃ d y, x = .Lopn [.reg d] "LOADIDX" [.arrIdx reloadScratch2 y 8]) ∨
    (∃ d y v, x = .Lopn [.reg d] "STOREIDX" [.arrIdx reloadScratch2 y 8, .reg v]) ∨
    (∃ n w, x = .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]) ∨
    ∃ v k, x = .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v, .imm k]

/-- **A reload window.** A block that starts with a move of the slot `q` of an array into
    `R14`, continues with operations that write neither `R14` nor an array slot and are no
    accesses, then has one access through `R14` and then no further access, resolves its
    accesses locally. -/
theorem accLocal_window {slotArr : String → Option (String × Nat)} {rl acc : Linstr}
    {mid post : Lcmd} {q : String} (hrl : slotMov? rl.li_i = some (reloadScratch2, q))
    (hq : (slotArr q).isSome = true)
    (hmid : ∀ r ∈ mid, (∃ ds o ss, r.li_i = .Lopn ds o ss ∧
      ds.any (dstHitB slotArr reloadScratch2) = false) ∧ isAccB r.li_i = false ∧
        isArrImmB r.li_i = false)
    (hacc : AccR14 acc.li_i)
    (hpost : ∀ r ∈ post, isAccB r.li_i = false ∧ isArrImmB r.li_i = false) :
    AccLocal slotArr (rl :: (mid ++ acc :: post)) := by
  intro k i hk
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact accOkB_of_not_acc _ _ _ (isAccB_of_slotMov hrl) (isArrImmB_of_slotMov hrl)
  | succ k =>
    simp only [List.getElem?_cons_succ] at hk
    rcases Nat.lt_trichotomy k mid.length with hlt | heq | hgt
    · rw [List.getElem?_append_left hlt] at hk
      exact accOkB_of_not_acc _ _ _ (hmid _ (List.mem_of_getElem? hk)).2.1
        (hmid _ (List.mem_of_getElem? hk)).2.2
    · subst heq
      rw [List.getElem?_append_right (by omega), Nat.sub_self] at hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      have hA : accArr slotArr (rl :: (mid ++ acc :: post)) (mid.length + 1) reloadScratch2
          = slotArr q := by
        refine accArr_of_reload (j := 0) rfl hrl hq (by omega) ?_
        intro m h1 h2
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [List.getElem?_cons_succ, List.getElem?_append_left (by omega : m' < mid.length)]
        obtain ⟨r, hr⟩ : ∃ r, mid[m']? = some r :=
          ⟨mid[m'], List.getElem?_eq_getElem (by omega)⟩
        exact ⟨r, hr, (hmid r (List.mem_of_getElem? hr)).1⟩
      rcases hacc with h | ⟨d, y, h⟩ | ⟨d, y, v, h⟩ | ⟨n, w, h⟩ | ⟨v, j, h⟩
      · exact accOkB_of_not_acc _ _ _ h.1 h.2
      · rw [h]; simp [accOkB, hA, hq]
      · rw [h]; simp [accOkB, hA, hq]
      · obtain ⟨⟨A, nA⟩, hqA⟩ := Option.isSome_iff_exists.mp hq
        rw [h]; simp [accOkB, arrImmImg, hA, hqA]
      · obtain ⟨⟨A, nA⟩, hqA⟩ := Option.isSome_iff_exists.mp hq
        rw [h]; simp [accOkB, arrImmImg, hA, hqA]
    · rw [List.getElem?_append_right (by omega)] at hk
      obtain ⟨m, hm⟩ : ∃ m, k - mid.length = m + 1 := ⟨k - mid.length - 1, by omega⟩
      rw [hm, List.getElem?_cons_succ] at hk
      exact accOkB_of_not_acc _ _ _ (hpost _ (List.mem_of_getElem? hk)).1
        (hpost _ (List.mem_of_getElem? hk)).2

/-! ## 3. The class of a body with a move prefix -/

/-- **The class `physImgB` of a body with a move prefix**: let every instruction of the
    prefix `pre` be a move (`slotMov?`), let every move of `pre` into an array slot `d` from
    a name `R` be the save into `d = slotOfReg R` of a register that no earlier move of `pre`
    writes, let no instruction of `rest` write an array slot, and let every indexed access of
    `rest` resolve to an array (`accOkB`). Then `physImgB slotArr (pre ++ rest)` holds. -/
theorem physImgB_of_movePrefix {slotArr : String → Option (String × Nat)} {pre rest : Lcmd}
    (hpre : ∀ j ∈ pre, (slotMov? j.li_i).isSome = true)
    (hsave : ∀ (k : Nat) (j : Linstr) (d R : String), pre[k]? = some j →
      slotMov? j.li_i = some (d, R) → (slotArr d).isSome = true → d = slotOfReg R ∧
        ∀ (m : Nat) (j' : Linstr) (d' s' : String), m < k → pre[m]? = some j' →
          slotMov? j'.li_i = some (d', s') → d' ≠ R)
    (hrest : ∀ j ∈ rest, ∀ ds o ss, j.li_i = .Lopn ds o ss → ∀ x ∈ ds,
      (∀ q, x = .reg q → slotArr q = none) ∧ (∀ q n, x = .arr q n → slotArr q = none)
        ∧ (∀ q i sc, x = .arrIdx q i sc → slotArr q = none))
    (hacc : ∀ k i, pre.length ≤ k → (pre ++ rest)[k]? = some i →
      accOkB slotArr (pre ++ rest) k i.li_i = true) :
    physImgB slotArr (pre ++ rest) = true := by
  unfold physImgB
  rw [List.all_eq_true]
  intro k _
  cases hb : (pre ++ rest)[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.and_eq_true]
    by_cases hlt : k < pre.length
    · rw [List.getElem?_append_left hlt] at hb
      have hi := List.mem_of_getElem? hb
      obtain ⟨⟨d, R⟩, hs⟩ := Option.isSome_iff_exists.mp (hpre i hi)
      obtain ⟨o, ho⟩ := slotMov?_eq hs
      refine ⟨accOkB_of_not_acc _ _ _ (isAccB_of_slotMov hs) (isArrImmB_of_slotMov hs), ?_⟩
      rw [ho]
      simp only [slotWriteB, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true]
      rw [← ho, hs]
      by_cases hd : (slotArr d).isSome = true
      · obtain ⟨rfl, hne⟩ := hsave k i d R hb hs hd
        refine Or.inr ?_
        simp only [beq_self_eq_true, Bool.true_and]
        unfold entryRegB
        rw [List.take_append_of_le_length (by omega), List.all_eq_true]
        intro j hj
        obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hj
        have hmk : m < k := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          simp at this; omega
        rw [List.getElem?_take_of_lt hmk] at hm
        obtain ⟨⟨d', s'⟩, hs'⟩ := Option.isSome_iff_exists.mp (hpre j (List.mem_of_getElem? hm))
        simp [hs', hne m j d' s' hmk hm hs']
      · exact Or.inl (by simpa using hd)
    · refine ⟨hacc k i (by omega) hb, ?_⟩
      rw [List.getElem?_append_right (by omega)] at hb
      have hi := List.mem_of_getElem? hb
      unfold slotWriteB
      split
      · rename_i ds o ss heq
        rw [List.all_eq_true]
        intro x hx
        obtain ⟨h1, h2, h3⟩ := hrest i hi ds o ss heq x hx
        cases x with
        | reg q => simp [h1 q rfl]
        | arr q n => simp [h2 q n rfl]
        | arrIdx q j sc => simp [h3 q j sc rfl]
        | imm _ => rfl
      · rfl

/-! ## 4. The arms: destinations and mnemonics -/

/-- The move mnemonics the legalisers add: `MOV`, `MOV:64`, `MOVQ`, `LEA:64`, `STORE:64`. -/
def movMnems : List String := ["MOV", "MOV:64", "MOVQ", "LEA:64", "STORE:64"]

/-- An instruction an arm emits on the operands `ins` for the mnemonic `opn`: an `Lopn` under
    `opn` or a move mnemonic, each of whose destinations is one of `ins`, a scratch register
    `R15` or `R14`, or a cell name `mem.…`. -/
def ArmOut (ins : List LOperand) (opn : String) (r : LinstrR) : Prop :=
  ∃ ds o ss, r = .Lopn ds o ss ∧ (o = opn ∨ o ∈ movMnems) ∧
    ∀ x ∈ ds, x ∈ ins ∨ x = .reg reloadScratch ∨ x = .reg reloadScratch2 ∨
      ∃ c, x = .reg ("mem." ++ c)

theorem armOut_mono {ins ins' : List LOperand} {opn : String} {r : LinstrR}
    (hs : ∀ x ∈ ins, x ∈ ins') (h : ArmOut ins opn r) : ArmOut ins' opn r := by
  obtain ⟨ds, o, ss, rfl, ho, hd⟩ := h
  refine ⟨ds, o, ss, rfl, ho, fun x hx => ?_⟩
  rcases hd x hx with h | h
  · exact Or.inl (hs x h)
  · exact Or.inr h

theorem legalizeMov_armOut (d s : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ legalizeMov d s mov, ArmOut [d] opn r := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov
  unfold legalizeMov
  split <;> simp [ArmOut, movMnems, hmov]

theorem legalizeBinop_armOut (d s : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ legalizeBinop d s opn mov, ArmOut [d] opn r := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov
  unfold legalizeBinop
  split <;> simp [ArmOut, movMnems, hmov]

theorem materializeWideImm_armOut (s : LOperand) (opn mov : String) :
    ∀ r ∈ (materializeWideImm s mov).1, ArmOut [] opn r := by
  unfold materializeWideImm
  split
  · split <;> simp [ArmOut, movMnems]
  · simp

theorem lowerTwoAddr_armOut (d s0 s1 : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ lowerTwoAddr d s0 s1 opn mov, ArmOut [d] opn r := by
  have hpre := materializeWideImm_armOut s1 opn mov
  unfold lowerTwoAddr
  intro x hx
  rcases hmw : materializeWideImm s1 mov with ⟨pre, s1v⟩
  rw [hmw] at hx hpre
  simp only at hx hpre
  have hp : ∀ r ∈ pre, ArmOut [d] opn r := fun r hr =>
    armOut_mono (by simp) (hpre r hr)
  split at hx <;> simp only [List.mem_append] at hx
  · exact hx.elim (hp x) (legalizeBinop_armOut d _ opn mov hmov x)
  · exact hx.elim (fun h => h.elim (legalizeMov_armOut d s0 opn mov hmov x) (hp x))
      (legalizeBinop_armOut d _ opn mov hmov x)

theorem lowerTwoAddrShiftImm_armOut (d s0 : LOperand) (v : Nat) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ lowerTwoAddrShiftImm d s0 v opn mov, ArmOut [d] opn r := by
  have hmov' := hmov
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov'
  unfold lowerTwoAddrShiftImm
  intro x hx
  split at hx
  · simp at hx; rcases hx with rfl | rfl | rfl <;> simp [ArmOut, movMnems, hmov']
  · split at hx
    · simp at hx; subst hx; simp [ArmOut]
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact legalizeMov_armOut d s0 opn mov hmov x hx
      · simp [ArmOut]

theorem lowerNativeShiftRotate_armOut (d s : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ lowerNativeShiftRotate d s opn mov, ArmOut [d] opn r := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov
  unfold lowerNativeShiftRotate
  split <;> simp [ArmOut, movMnems, hmov]

theorem spillImmMovMnem_ok (u64 : Bool) (opn : String) (d s : LOperand) :
    spillImmMovMnem u64 opn d s = opn ∨ spillImmMovMnem u64 opn d s ∈ movMnems := by
  unfold spillImmMovMnem
  split
  · split
    · right; decide
    · left; rfl
  · left; rfl

theorem legalizeOneSrc_armOut (u64 : Bool) (opn : String) (d s : LOperand) :
    ∀ r ∈ legalizeOneSrc u64 opn d s, ArmOut [d] opn r := by
  unfold legalizeOneSrc
  split
  · exact legalizeMov_armOut d s opn _ (spillImmMovMnem_ok u64 opn d s)
  · rcases spillImmMovMnem_ok u64 opn d s with h | h <;> simp [ArmOut, h]

theorem legalizeSpillDst_armOut (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    ∀ r ∈ legalizeSpillDst dsts opn srcs, ArmOut dsts opn r := by
  have hset : ∀ o, setccMov o ∈ movMnems := by
    intro o; unfold setccMov; split <;> decide
  unfold legalizeSpillDst
  split
  · next l h =>
    unfold cmovSpillDst? at h
    split at h
    · split at h
      · cases h
        unfold cmovSpillSeq
        split_ifs <;> simp_all [ArmOut, movMnems]
      · cases h
    · cases h
  · split
    · next l _ h =>
      unfold setccSpill? at h
      split at h
      · split at h
        · cases h
          simp_all [ArmOut]
        · cases h
      · cases h
    · simp +contextual [ArmOut]

theorem legalizeSibElem_armOut (o : LOperand) (opn : String) :
    ∀ r ∈ (legalizeSibElem o).1, ArmOut [] opn r := by
  unfold legalizeSibElem
  split
  · split_ifs <;> simp [ArmOut, movMnems]
  · simp

theorem reloadMemrefBase_armOut (mbr : String → Option String) (o : LOperand) (opn : String) :
    ∀ r ∈ (reloadMemrefBase mbr o).1, ArmOut [] opn r := by
  unfold reloadMemrefBase
  split
  · split <;> simp [ArmOut, movMnems]
  · simp

theorem legalizeMemLoad_armOut (d s : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ legalizeMemLoad d s opn mov, ArmOut [d] opn r := by
  have hpre := legalizeSibElem_armOut s opn
  unfold legalizeMemLoad
  rcases hl : legalizeSibElem s with ⟨pre, s'⟩
  rw [hl] at hpre
  simp only at hpre ⊢
  rw [List.forall_mem_append]
  refine ⟨fun r hr => armOut_mono (by simp) (hpre r hr), ?_⟩
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov
  split <;> (repeat' split) <;> simp_all [ArmOut, movMnems]

theorem memName_eq (b : String) (off : Nat) :
    memName b off = "mem." ++ (b ++ "." ++ toString off) := by
  simp [memName, String.append_assoc]

theorem legalizeMemStore_armOut (dArr addr val : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ legalizeMemStore dArr addr val opn mov, ArmOut [dArr] opn r := by
  have hpre := legalizeSibElem_armOut addr opn
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at hmov
  unfold legalizeMemStore
  rcases hl : legalizeSibElem addr with ⟨pre, a'⟩
  rw [hl] at hpre
  simp only at hpre ⊢
  have hp : ∀ r ∈ pre, ArmOut [dArr] opn r := fun r hr => armOut_mono (by simp) (hpre r hr)
  repeat' split
  all_goals
    rw [List.forall_mem_append]
    refine ⟨hp, ?_⟩
    simp_all [ArmOut, movMnems, String.append_assoc]

theorem constIdxStore?_armOut (k : Option Nat) (addr val : LOperand) (opn : String)
    (l : List LinstrR) (h : constIdxStore? k addr val = some l) :
    ∀ r ∈ l, ArmOut [] opn r := by
  unfold constIdxStore? at h
  split at h
  · split_ifs at h
    all_goals
      split at h
      · split_ifs at h
        cases h
        simp [ArmOut, movMnems, memName_eq, String.append_assoc]
      · cases h
  · cases h

theorem legalizeMemStoreK_armOut (k : Option Nat) (dArr addr val : LOperand) (opn mov : String)
    (hmov : mov = opn ∨ mov ∈ movMnems) :
    ∀ r ∈ legalizeMemStoreK k dArr addr val opn mov, ArmOut [dArr] opn r := by
  unfold legalizeMemStoreK
  split
  · next l h => exact fun r hr => armOut_mono (by simp) (constIdxStore?_armOut k addr val opn l h r hr)
  · exact legalizeMemStore_armOut dArr addr val opn mov hmov

/-! ## 5. The access arms: the reload precedes the access -/

/-- `sibNameSpill` is the prefix test `k.` on the character lists. -/
theorem sibNameSpill_eq_list (n : String) :
    sibNameSpill n = ['k', '.'].isPrefixOf n.toList := by
  rw [Bool.eq_iff_iff, sibNameSpill, String.isPrefixOf, String.startsWith_string_iff,
    List.isPrefixOf_iff_prefix]
  rfl

theorem sibNameSpill_reloadScratch2 : sibNameSpill reloadScratch2 = false := by
  rw [sibNameSpill_eq_list]; decide

theorem dstHitB_r15_r14 {slotArr : String → Option (String × Nat)}
    (hs15 : slotArr reloadScratch = none) :
    dstHitB slotArr reloadScratch2 (.reg reloadScratch) = false := by
  have h : (reloadScratch == reloadScratch2) = false := by decide +kernel
  simp [dstHitB, hs15, h]

theorem constIdxStore?_noAcc (k : Option Nat) (addr val : LOperand) (l : List LinstrR)
    (h : constIdxStore? k addr val = some l) : ∀ r ∈ l, isAccB r = false := by
  unfold constIdxStore? at h
  split at h
  · split_ifs at h
    all_goals
      split at h
      · split_ifs at h
        cases h
        simp [isAccB]
      · cases h
  · cases h

theorem constIdxStore?_noArrImm (k : Option Nat) (addr val : LOperand) (l : List LinstrR)
    (h : constIdxStore? k addr val = some l) : ∀ r ∈ l, isArrImmB r = false := by
  unfold constIdxStore? at h
  split at h
  · split_ifs at h
    all_goals
      split at h
      · split_ifs at h
        cases h
        simp [isArrImmB]
      · cases h
  · cases h

/-- **The load arm after the base reload.** The reload `MOVQ R14, q` of the slot of an array
    followed by `legalizeMemLoad` of an `LOADIDX` from `R14` at stride `8` resolves its access
    locally. -/
theorem loadIdx_accLocal {slotArr : String → Option (String × Nat)}
    (hs15 : slotArr reloadScratch = none) {q : String} (hq : (slotArr q).isSome = true)
    (ii : Nat) (d : LOperand) (n y mov : String) (hd : d = .reg n) :
    AccLocal slotArr (([LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q]].map
        (fun r => (⟨ii, r⟩ : Linstr))) ++
      (legalizeMemLoad d (.arrIdx reloadScratch2 y 8) "LOADIDX" mov).map
        (fun r => (⟨ii, r⟩ : Linstr))) := by
  subst hd
  have hrl : slotMov? (LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q])
      = some (reloadScratch2, q) := by simp [slotMov?]
  have hm15 := dstHitB_r15_r14 hs15
  simp only [legalizeMemLoad, legalizeSibElem, sibNameSpill_reloadScratch2]
  cases hy : sibNameSpill y <;> cases hn : (LOperand.reg n).isSpill <;>
    simp only [Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, ge_iff_le, Nat.le_refl]
  · exact accLocal_window (mid := []) (post := []) hrl hq (by simp)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) (by simp)
  · exact accLocal_window (mid := []) hrl hq (by simp)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) (by simp [isAccB, isArrImmB])
  · exact accLocal_window (mid := [_]) (post := []) hrl hq
      (by simp [isAccB, isArrImmB, hm15]) (Or.inr (Or.inl ⟨_, _, rfl⟩)) (by simp)
  · exact accLocal_window (mid := [_]) hrl hq
      (by simp [isAccB, isArrImmB, hm15]) (Or.inr (Or.inl ⟨_, _, rfl⟩)) (by simp [isAccB, isArrImmB])

/-- **The store arm after the base reload.** The reload `MOVQ R14, q` of the slot of an array
    followed by `legalizeMemStoreK` of an `STOREIDX` of a register to `R14` at stride `8`
    resolves its access locally. -/
theorem storeIdx_accLocal {slotArr : String → Option (String × Nat)}
    (hs15 : slotArr reloadScratch = none) {q : String} (hq : (slotArr q).isSome = true)
    (ii : Nat) (kc : Option Nat) (dA val : LOperand) (na y v mov : String)
    (hda : dA = .reg na) (hv : val = .reg v) :
    AccLocal slotArr (([LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q]].map
        (fun r => (⟨ii, r⟩ : Linstr))) ++
      (legalizeMemStoreK kc dA (.arrIdx reloadScratch2 y 8) val "STOREIDX" mov).map
        (fun r => (⟨ii, r⟩ : Linstr))) := by
  subst hda hv
  have hrl : slotMov? (LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q])
      = some (reloadScratch2, q) := by simp [slotMov?]
  have hm15 := dstHitB_r15_r14 hs15
  cases hc : constIdxStore? kc (.arrIdx reloadScratch2 y 8) (.reg v) with
  | some l =>
    simp only [legalizeMemStoreK, hc]
    refine accLocal_of_noAcc ?_ ?_ <;> intro r hr <;>
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_map] at hr <;>
      rcases hr with rfl | ⟨r', hr', rfl⟩
    · rfl
    · exact constIdxStore?_noAcc _ _ _ l hc r' hr'
    · rfl
    · exact constIdxStore?_noArrImm _ _ _ l hc r' hr'
  | none =>
    rw [legalizeMemStoreK_of_none _ _ _ hc]
    simp only [legalizeMemStore, legalizeSibElem, sibNameSpill_reloadScratch2]
    cases hy : sibNameSpill y <;> cases hn : (LOperand.reg v).isSpill <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.nil_append, List.cons_append,
        List.map_cons, List.map_nil, ge_iff_le, Nat.le_refl, beq_self_eq_true]
    · exact accLocal_window (mid := []) (post := []) hrl hq (by simp)
        (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))) (by simp)
    · split
      · exact accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB])
      · exact accLocal_window (mid := [_]) (post := []) hrl hq
          (by simp [isAccB, isArrImmB, hm15]) (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))) (by simp)
    · exact accLocal_window (mid := [_]) (post := []) hrl hq
        (by simp [isAccB, isArrImmB, hm15]) (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))) (by simp)
    · exact accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB])

/-! ## 6. One position of `physPositionEmit` -/

/-- The operand is no array slot as a destination: a register, array or register-indexed
    operand whose name is no array slot (the destination condition of `slotWriteB`). -/
def OperandOk (slotArr : String → Option (String × Nat)) (x : LOperand) : Prop :=
  (∀ q, x = .reg q → slotArr q = none) ∧ (∀ q n, x = .arr q n → slotArr q = none) ∧
    ∀ q j sc, x = .arrIdx q j sc → slotArr q = none

/-- The mnemonic of an operation; `none` for every other instruction. -/
def opnOf : LinstrR → Option String
  | .Lopn _ o _ => some o
  | _ => none

/-- An instruction emitted for the virtual instruction `i`: an operation whose destinations
    are no array slots, under the mnemonic of `i` or a move mnemonic. -/
def EmitOk (slotArr : String → Option (String × Nat)) (i : LinstrR) (r : LinstrR) : Prop :=
  ∀ ds o ss, r = .Lopn ds o ss → (∀ x ∈ ds, OperandOk slotArr x) ∧
    (some o = opnOf i ∨ o ∈ movMnems)

/-- The emitted block of the virtual instruction `i`: every instruction is `EmitOk` and every
    access resolves inside the block. -/
def BlockOk (slotArr : String → Option (String × Nat)) (i : LinstrR) (L : Lcmd) : Prop :=
  (∀ r ∈ L, EmitOk slotArr i r.li_i) ∧ AccLocal slotArr L

theorem isAccB_of_movMnems {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ∈ movMnems) : isAccB (.Lopn ds o ss) = false := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem isAccB_of_armOut {ins : List LOperand} {opn : String} {r : LinstrR}
    (h : ArmOut ins opn r) (h1 : opn ≠ "LOADIDX") (h2 : opn ≠ "STOREIDX") :
    isAccB r = false := by
  obtain ⟨ds, o, ss, rfl, ho | ho, -⟩ := h
  · subst ho; simp [isAccB, h1, h2]
  · exact isAccB_of_movMnems ho

theorem isArrImmB_of_movMnems {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ∈ movMnems) : isArrImmB (.Lopn ds o ss) = false := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem isArrImmB_of_armOut {ins : List LOperand} {opn : String} {r : LinstrR}
    (h : ArmOut ins opn r) (h34 : opn ≠ "ZEROARR" ∧ opn ≠ "STOREIMM") :
    isArrImmB r = false := by
  obtain ⟨ds, o, ss, rfl, ho | ho, -⟩ := h
  · subst ho; simp [isArrImmB, h34.1, h34.2]
  · exact isArrImmB_of_movMnems ho

theorem emitOk_of_armOut {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {ins : List LOperand} {opn : String} {r : LinstrR}
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none) (hins : ∀ x ∈ ins, OperandOk slotArr x)
    (hopn : opnOf i = some opn) (h : ArmOut ins opn r) : EmitOk slotArr i r := by
  obtain ⟨ds, o, ss, rfl, ho, hd⟩ := h
  intro ds' o' ss' he
  cases he
  refine ⟨fun x hx => ?_, ho.imp (fun h => by rw [h, hopn]) id⟩
  rcases hd x hx with h | rfl | rfl | ⟨c, rfl⟩
  · exact hins x h
  · exact ⟨fun q hq => (by cases hq; exact hs15), nofun, nofun⟩
  · exact ⟨fun q hq => (by cases hq; exact hs14), nofun, nofun⟩
  · exact ⟨fun q hq => (by cases hq; exact hmem c), nofun, nofun⟩

/-- An arm whose instructions are `ArmOut` under a mnemonic other than the two access
    mnemonics and the two constant-index array writes is a block of the instruction. -/
theorem blockOk_of_arm {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {ins : List LOperand} {opn : String} {l : List LinstrR} (ii : Nat)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none) (hins : ∀ x ∈ ins, OperandOk slotArr x)
    (hopn : opnOf i = some opn) (h34 : opn ≠ "ZEROARR" ∧ opn ≠ "STOREIMM")
    (h1 : opn ≠ "LOADIDX") (h2 : opn ≠ "STOREIDX")
    (h : ∀ r ∈ l, ArmOut ins opn r) :
    BlockOk slotArr i (l.map fun r => (⟨ii, r⟩ : Linstr)) := by
  refine ⟨fun r hr => ?_, accLocal_of_noAcc (fun r hr => ?_) (fun r hr => ?_)⟩ <;>
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  · exact emitOk_of_armOut hs15 hs14 hmem hins hopn (h r' hr')
  · exact isAccB_of_armOut (h r' hr') h1 h2
  · exact isArrImmB_of_armOut (h r' hr') h34

theorem emitAll_of_arm {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {ins : List LOperand} {opn : String} {l : List LinstrR} (ii : Nat)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none) (hins : ∀ x ∈ ins, OperandOk slotArr x)
    (hopn : opnOf i = some opn) (h : ∀ r ∈ l, ArmOut ins opn r) :
    ∀ r ∈ l.map (fun r => (⟨ii, r⟩ : Linstr)), EmitOk slotArr i r.li_i := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  exact emitOk_of_armOut hs15 hs14 hmem hins hopn (h r' hr')

theorem isTwoAddrBinop_storeIdx : isTwoAddrBinop "STOREIDX" = false := by decide +kernel

theorem isMemStore_storeIdx : isMemStore "STOREIDX" = true := by decide +kernel

theorem isMemLoad_loadIdx : isMemLoad "LOADIDX" = true := by decide +kernel

theorem isNativeShiftRotate_loadIdx : isNativeShiftRotate "LOADIDX" = false := by
  have hs : stripWidthTag "LOADIDX" = "LOADIDX" := by decide +kernel
  simp only [isNativeShiftRotate, hs, List.any_eq_false]
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rw [Bool.not_eq_true, ← Bool.not_eq_true, String.isPrefixOf, String.startsWith_string_iff]
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

theorem movFor_ok (o : String) :
    (if hasSuffix o ":64" = true then "MOV:64" else "MOV") = o ∨
      (if hasSuffix o ":64" = true then "MOV:64" else "MOV") ∈ movMnems := by
  right; split <;> decide

theorem blockOk_append {slotArr : String → Option (String × Nat)} {i : LinstrR} {a b : Lcmd}
    (ha : BlockOk slotArr i a) (hb : BlockOk slotArr i b) : BlockOk slotArr i (a ++ b) :=
  ⟨fun r hr => (List.mem_append.mp hr).elim (ha.1 r) (hb.1 r), accLocal_append ha.2 hb.2⟩

/-- The base of a register-indexed access is reloaded from the slot of an array: the operand
    map sends `.arrIdx b y 8` to an address at stride `8` whose base the memref reload map
    sends to an array slot. -/
def BaseReloaded (slotArr : String → Option (String × Nat)) (rm : LOperand → LOperand)
    (mbr : String → Option String) (b y : String) : Prop :=
  ∃ b' y' q, rm (.arrIdx b y 8) = .arrIdx b' y' 8 ∧ mbr b' = some q ∧ (slotArr q).isSome = true

/-- The register base `b` of a constant-index array write is reloaded from the slot of an
    array: the operand map sends `.reg b` to a register that the memref reload map sends to an
    array slot. -/
def RegBaseReloaded (slotArr : String → Option (String × Nat)) (rm : LOperand → LOperand)
    (mbr : String → Option String) (b : String) : Prop :=
  ∃ b' q, rm (.reg b) = .reg b' ∧ mbr b' = some q ∧ (slotArr q).isSome = true

/-- The indexed accesses and the constant-index array writes of a virtual instruction have the
    forms the image reads, with a reloaded base: an `LOADIDX` is `[.reg d] [.arrIdx b y 8]`, an
    `STOREIDX` is `[.reg d] [.arrIdx b y 8, .reg v]`, a `ZEROARR` is `[.reg b] [#n, #w]` and an
    `STOREIMM` is `[.reg d] [.reg b, .reg v, #k]`. -/
def AccForm (slotArr : String → Option (String × Nat)) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : LinstrR) : Prop :=
  ∀ ds o ss, i = .Lopn ds o ss →
    (o = "LOADIDX" → ∃ d b y, ds = [.reg d] ∧ ss = [.arrIdx b y 8] ∧
      BaseReloaded slotArr rm mbr b y) ∧
    (o = "STOREIDX" → ∃ d b y v, ds = [.reg d] ∧ ss = [.arrIdx b y 8, .reg v] ∧
      BaseReloaded slotArr rm mbr b y) ∧
    (o = "ZEROARR" → ∃ b n w, ds = [.reg b] ∧ ss = [.imm n, .imm w] ∧
      RegBaseReloaded slotArr rm mbr b) ∧
    (o = "STOREIMM" → ∃ d b v k, ds = [.reg d] ∧ ss = [.reg b, .reg v, .imm k] ∧
      RegBaseReloaded slotArr rm mbr b)

/-- A block of an instruction other than a constant-index array write is its own
    constant-shape base reload. -/
theorem blockOk_reload_of_ne {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {L : Lcmd} (mbr : String → Option String) (h : BlockOk slotArr i L)
    (hne : ∀ o, opnOf i = some o → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    BlockOk slotArr i (reloadArrImmBody mbr L) := by
  rw [reloadArrImmBody_eq_of_noArrImm mbr fun r hr ds o ss hx => ?_]
  · exact h
  rcases (h.1 r hr ds o ss hx).2 with ho | ho
  · exact hne o ho.symm
  · simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> decide

/-- One position of `physPositionEmit` for an instruction other than a constant-index array
    write is a block of the instruction. -/
theorem physPositionEmit_blockOk {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (body : Lcmd) (loadBase storeBase : String) (abiW : Nat)
    (mbr : String → Option String) (callArgBaseReload : List (String × String))
    (reservedVec : List Nat) (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm = if bodyHasCall body = true then
      fun o => remapOperandCalleeSave body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o
      else fun o => remapOperand body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o)
    (hcall : ∀ a b, i.li_i ≠ .Lcall a b)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hok : ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x))
    (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n')
    (hacc : AccForm slotArr rm mbr i.li_i)
    (hne : ∀ ds o ss, i.li_i = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") :
    BlockOk slotArr i.li_i (physPositionEmit shiftImm body (fun _ => none) loadBase []
      storeBase abiW mbr callArgBaseReload reservedVec (i, virtIdx)) := by
  obtain ⟨ii, x⟩ := i
  simp only at hcall hok hacc hne ⊢
  unfold physPositionEmit
  dsimp only
  rw [List.filterMap_eq_nil_iff.mpr (fun s _ => by split <;> (try split) <;> rfl)]
  simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.sub_zero, ← hrm]
  have hst : ∀ (b t : Nat), ¬ (b ≥ t ∧ b < t) := fun b t h => by omega
  simp only [hst, if_false]
  cases x with
  | Lopn ds o ss =>
    have hopn : opnOf (.Lopn ds o ss) = some o := rfl
    have hokd : ∀ x ∈ ds, OperandOk slotArr (rm x) :=
      fun x hx => hok x (by simp [lopnOperands, hx])
    have hoks : ∀ x ∈ ss, OperandOk slotArr (rm x) :=
      fun x hx => hok x (by simp [lopnOperands, hx])
    have hmapd : ∀ x ∈ ds.map rm, OperandOk slotArr x := by
      intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hokd y hy
    obtain ⟨hL, hS, -, -⟩ := hacc ds o ss rfl
    have h34 := hne ds o ss rfl
    -- the generic single instruction
    have hsingle : o ≠ "LOADIDX" → o ≠ "STOREIDX" →
        BlockOk slotArr (.Lopn ds o ss)
          [⟨ii, .Lopn (ds.map rm) o (ss.map rm)⟩] := fun h1 h2 =>
      blockOk_of_arm (l := [.Lopn (ds.map rm) o (ss.map rm)]) ii hs15 hs14 hmem hmapd hopn
        h34 h1 h2 (fun r hr => by
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨_, _, _, rfl, Or.inl rfl, fun x hx => Or.inl hx⟩)
    rcases ds with _ | ⟨d, tail⟩
    · have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, h', -⟩ := hL h; cases h'
      have h2 : o ≠ "STOREIDX" := fun h => by obtain ⟨_, _, _, _, h', -⟩ := hS h; cases h'
      dsimp only
      simpa using hsingle h1 h2
    · have hd : ∀ x ∈ [rm d], OperandOk slotArr x := by simp [hokd d List.mem_cons_self]
      have hnil : ∀ x ∈ ([] : List LOperand), OperandOk slotArr x := by simp
      rcases ss with _ | ⟨s0, _ | ⟨s1, t⟩⟩
      · -- no source
        have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, -, h', -⟩ := hL h; cases h'
        have h2 : o ≠ "STOREIDX" := fun h => by
          obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
        dsimp only
        simpa using hsingle h1 h2
      · rcases tail with _ | ⟨d2, tail2⟩
        · -- one destination, one source
          have h2 : o ≠ "STOREIDX" := fun h => by
            obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
          dsimp only
          simp only [List.append_nil]
          by_cases hnat : isNativeShiftRotate o = true
          · rw [if_pos hnat]
            have h1 : o ≠ "LOADIDX" := by
              rintro rfl; rw [isNativeShiftRotate_loadIdx] at hnat; cases hnat
            exact blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 h2
              (lowerNativeShiftRotate_armOut _ _ _ _ (movFor_ok o))
          rw [if_neg hnat]
          by_cases hld : isMemLoad o = true
          · rw [if_pos hld]
            by_cases hLo : o = "LOADIDX"
            · obtain ⟨dn, b, y, hds, hss, b', y', q, hrmA, hmb, hq⟩ := hL hLo
              simp only [List.cons.injEq, and_true] at hds hss
              subst hds hss
              obtain ⟨n', hn'⟩ := hreg dn
              have hd' : ∀ x ∈ [LOperand.reg n'], OperandOk slotArr x := by
                rw [← hn']; exact hd
              rw [hrmA, hn']
              simp only [reloadMemrefBase, hmb]
              refine ⟨fun r hr => ?_, ?_⟩
              · rcases List.mem_append.mp hr with hr | hr
                · exact emitAll_of_arm ii hs15 hs14 hmem hnil hopn
                    (reloadMemrefBase_armOut mbr (.arrIdx b' y' 8) o) r
                    (by simpa [reloadMemrefBase, hmb] using hr)
                · exact emitAll_of_arm ii hs15 hs14 hmem hd' hopn
                    (legalizeMemLoad_armOut _ _ _ _ (movFor_ok o)) r hr
              · subst hLo
                exact loadIdx_accLocal hs15 hq ii _ n' y' _ rfl
            · exact blockOk_append
                (blockOk_of_arm ii hs15 hs14 hmem hnil hopn h34 hLo h2
                  (reloadMemrefBase_armOut mbr (rm s0) o))
                (blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 hLo h2
                  (legalizeMemLoad_armOut _ _ _ _ (movFor_ok o)))
          · rw [if_neg hld]
            have h1 : o ≠ "LOADIDX" := by
              rintro rfl; exact hld isMemLoad_loadIdx
            exact blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 h2
              (legalizeOneSrc_armOut _ _ _ _)
        · have h1 : o ≠ "LOADIDX" := fun h => by
            obtain ⟨_, _, _, h', -⟩ := hL h; simp at h'
          have h2 : o ≠ "STOREIDX" := fun h => by
            obtain ⟨_, _, _, _, -, h', -⟩ := hS h; cases h'
          dsimp only
          simpa using hsingle h1 h2
      · -- two or more sources
        have h1 : o ≠ "LOADIDX" := fun h => by obtain ⟨_, _, _, -, h', -⟩ := hL h; cases h'
        dsimp only
        simp only [List.append_nil]
        by_cases hbin : isTwoAddrBinop o = true
        · rw [if_pos hbin]
          have h2 : o ≠ "STOREIDX" := by
            rintro rfl; rw [isTwoAddrBinop_storeIdx] at hbin; cases hbin
          split
          · exact blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 h2
              (lowerTwoAddrShiftImm_armOut _ _ _ _ _ (movFor_ok o))
          · exact blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 h2
              (lowerTwoAddr_armOut _ _ _ _ _ (movFor_ok o))
        · rw [if_neg hbin]
          have hgen : (tail ≠ [] ∨ t ≠ []) → BlockOk slotArr (.Lopn (d :: tail) o (s0 :: s1 :: t))
              ((legalizeSpillDst ((d :: tail).map rm) o ((s0 :: s1 :: t).map rm)).map
                fun r => (⟨ii, r⟩ : Linstr)) := by
            intro hne
            have h2 : o ≠ "STOREIDX" := fun h => by
              obtain ⟨_, _, _, _, hds, hss, -⟩ := hS h
              simp only [List.cons.injEq] at hds hss
              rcases hne with hne | hne
              · exact hne hds.2
              · exact hne hss.2.2
            exact blockOk_of_arm ii hs15 hs14 hmem hmapd hopn h34 h1 h2
              (legalizeSpillDst_armOut _ _ _)
          rcases tail with _ | ⟨d2, tail2⟩ <;> rcases t with _ | ⟨s2, t2⟩
          · dsimp only
            by_cases hms : isMemStore o = true
            · rw [if_pos hms]
              by_cases hSo : o = "STOREIDX"
              · obtain ⟨dn, b, y, v, hds, hss, b', y', q, hrmA, hmb, hq⟩ := hS hSo
                simp only [List.cons.injEq, and_true] at hds hss
                obtain ⟨rfl, rfl⟩ := hss
                subst hds
                obtain ⟨n', hn'⟩ := hreg dn
                obtain ⟨v', hv'⟩ := hreg v
                have hd' : ∀ x ∈ [LOperand.reg n'], OperandOk slotArr x := by
                  rw [← hn']; exact hd
                simp only [hrmA, hn', hv', reloadMemrefBase, hmb]
                refine ⟨fun r hr => ?_, ?_⟩
                · rcases List.mem_append.mp hr with hr | hr
                  · exact emitAll_of_arm ii hs15 hs14 hmem hnil hopn
                      (reloadMemrefBase_armOut mbr (.arrIdx b' y' 8) o) r
                      (by simpa [reloadMemrefBase, hmb] using hr)
                  · exact emitAll_of_arm ii hs15 hs14 hmem hd' hopn
                      (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok o)) r hr
                · subst hSo
                  exact storeIdx_accLocal hs15 hq ii _ _ _ n' y' v' _ rfl rfl
              · exact blockOk_append
                  (blockOk_of_arm ii hs15 hs14 hmem hnil hopn h34 h1 hSo
                    (reloadMemrefBase_armOut mbr (rm s0) o))
                  (blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 hSo
                    (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok o)))
            · rw [if_neg hms]
              have h2 : o ≠ "STOREIDX" := by
                rintro rfl; exact hms isMemStore_storeIdx
              exact blockOk_of_arm ii hs15 hs14 hmem hd hopn h34 h1 h2
                (legalizeSpillDst_armOut _ _ _)
          · exact hgen (Or.inr (by simp))
          · exact hgen (Or.inl (by simp))
          · exact hgen (Or.inl (by simp))
  | Lcall a b => exact absurd rfl (hcall a b)
  | _ =>
    dsimp only
    exact ⟨by simp [EmitOk], accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB])⟩

/-- The mnemonics of the constant-index array writes are neither two-address binops, memory
    stores, the select `CMOV:64` nor comparisons. -/
theorem arrImm_mnem_class {o : String} (hz : o = "ZEROARR" ∨ o = "STOREIMM") :
    isTwoAddrBinop o = false ∧ isMemStore o = false ∧ o ≠ "CMOV:64" ∧
      isSetccMnem o = false := by
  rcases hz with rfl | rfl <;> refine ⟨by decide +kernel, by decide +kernel, by decide,
    by decide +kernel⟩

/-- **One position of `physPositionEmit` after the constant-shape base reload** is a block of
    the instruction. A constant-index array write is emitted as the single remapped
    instruction, whose reload (`reloadArrImmBody`) is the window `MOVQ R14, q` followed by the
    write through `R14`; every other instruction is `physPositionEmit_blockOk`. -/
theorem physPositionEmit_physImg {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (body : Lcmd) (loadBase storeBase : String) (abiW : Nat)
    (mbr : String → Option String) (callArgBaseReload : List (String × String))
    (reservedVec : List Nat) (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm = if bodyHasCall body = true then
      fun o => remapOperandCalleeSave body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o
      else fun o => remapOperand body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o)
    (hcall : ∀ a b, i.li_i ≠ .Lcall a b)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hok : ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x))
    (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n')
    (hacc : AccForm slotArr rm mbr i.li_i) :
    BlockOk slotArr i.li_i (reloadArrImmBody mbr (physPositionEmit shiftImm body (fun _ => none)
      loadBase [] storeBase abiW mbr callArgBaseReload reservedVec (i, virtIdx))) := by
  by_cases hz : ∃ ds o ss, i.li_i = .Lopn ds o ss ∧ (o = "ZEROARR" ∨ o = "STOREIMM")
  · obtain ⟨ds, o, ss, hx, hz⟩ := hz
    obtain ⟨ii, x⟩ := i
    simp only at hx hacc ⊢
    subst hx
    have himm : ∀ n, rm (.imm n) = .imm n := by
      intro n; subst hrm; split <;> rfl
    obtain ⟨-, -, hZ, hS⟩ := hacc ds o ss rfl
    obtain ⟨hbin, hms, hcm, hset⟩ := arrImm_mnem_class hz
    have hemit : ss.length ≥ 2 → ds.length = 1 →
        physPositionEmit shiftImm body (fun _ => none) loadBase [] storeBase abiW mbr
          callArgBaseReload reservedVec (⟨ii, .Lopn ds o ss⟩, virtIdx) =
          [⟨ii, .Lopn (ds.map rm) o (ss.map rm)⟩] := by
      intro hss hds
      obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := by
        match ds, hds with | [d], _ => exact ⟨d, rfl⟩
      obtain ⟨s0, s1, t, rfl⟩ : ∃ s0 s1 t, ss = s0 :: s1 :: t := by
        match ss, hss with | s0 :: s1 :: t, _ => exact ⟨s0, s1, t, rfl⟩
      unfold physPositionEmit
      dsimp only
      rw [List.filterMap_eq_nil_iff.mpr (fun s _ => by split <;> (try split) <;> rfl)]
      simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.sub_zero, ← hrm]
      have hst : ∀ (b t : Nat), ¬ (b ≥ t ∧ b < t) := fun b t h => by omega
      simp only [hst, if_false, hbin, Bool.false_eq_true, legalizeSpillDst]
      rcases t with _ | ⟨s2, t⟩ <;>
        simp only [hms, Bool.false_eq_true, if_false, cmovSpillDst?_of_ne _ _ hcm,
          setccSpill?_of_ne _ _ hset, List.map_cons, List.map_nil, List.append_nil]
    have hrl : ∀ q, slotMov? (LinstrR.Lopn [.reg reloadScratch2] "MOVQ" [.reg q])
        = some (reloadScratch2, q) := fun q => by simp [slotMov?]
    rcases hz with rfl | rfl
    · obtain ⟨b, n, w, rfl, rfl, b', q, hb', hq, hqs⟩ := hZ rfl
      rw [hemit (by simp) rfl]
      simp only [List.map_cons, List.map_nil, hb', himm]
      rw [show reloadArrImmBody mbr [⟨ii, .Lopn [.reg b'] "ZEROARR" [.imm n, .imm w]⟩] =
          [⟨ii, .Lopn [.reg reloadScratch2] "MOVQ" [.reg q]⟩,
            ⟨ii, .Lopn [] "ZEROARR" [.reg reloadScratch2, .imm n, .imm w]⟩] by
        simp [reloadArrImmBody, reloadArrImm_zeroArr n w hq]]
      refine ⟨?_, accLocal_window (mid := []) (post := []) (hrl q) hqs (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, w, rfl⟩)))) (by simp)⟩
      intro r hr ds o ss he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> cases he <;> simp [OperandOk, hs14, movMnems, opnOf]
    · obtain ⟨d, b, v, k, rfl, rfl, b', q, hb', hq, hqs⟩ := hS rfl
      obtain ⟨d', hd'⟩ := hreg d
      obtain ⟨v', hv'⟩ := hreg v
      rw [hemit (by simp) rfl]
      simp only [List.map_cons, List.map_nil, hb', hd', hv', himm]
      rw [show reloadArrImmBody mbr [⟨ii, .Lopn [.reg d'] "STOREIMM" [.reg b', .reg v', .imm k]⟩] =
          [⟨ii, .Lopn [.reg reloadScratch2] "MOVQ" [.reg q]⟩,
            ⟨ii, .Lopn [.reg reloadScratch2] "STOREIMM" [.reg reloadScratch2, .reg v', .imm k]⟩] by
        simp [reloadArrImmBody, reloadArrImm_storeImm d' v' k hq]]
      refine ⟨?_, accLocal_window (mid := []) (post := []) (hrl q) hqs (by simp)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨v', k, rfl⟩)))) (by simp)⟩
      intro r hr ds o ss he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> cases he <;> simp [OperandOk, hs14, movMnems, opnOf]
  · refine blockOk_reload_of_ne mbr (physPositionEmit_blockOk shiftImm body loadBase storeBase
      abiW mbr callArgBaseReload reservedVec i virtIdx rm hrm hcall hs15 hs14 hmem hok hreg hacc
      fun ds o ss hx => ?_) fun o ho => ?_
    · exact ⟨fun h => hz ⟨ds, o, ss, hx, Or.inl h⟩, fun h => hz ⟨ds, o, ss, hx, Or.inr h⟩⟩
    · refine ⟨fun h => hz ?_, fun h => hz ?_⟩ <;> cases hx : i.li_i <;> simp_all [opnOf]

/-! ## 7. The stored body -/

/-- The destinations of the instruction are no array slots (`OperandOk`). -/
def DstOk (slotArr : String → Option (String × Nat)) (r : LinstrR) : Prop :=
  ∀ ds o ss, r = .Lopn ds o ss → ∀ x ∈ ds, OperandOk slotArr x

theorem movMnems_ne_livepin {o : String} (h : o ∈ movMnems) : o ≠ "LIVEPIN" := by
  simp only [movMnems, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Removing the `LIVEPIN` instructions from a block of a virtual instruction keeps its
    destinations and its local resolution of accesses. -/
theorem blockOk_filter_livepin {slotArr : String → Option (String × Nat)} {i : LinstrR}
    {L : Lcmd} (h : BlockOk slotArr i L) :
    let L' := L.filter fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true
    (∀ r ∈ L', DstOk slotArr r.li_i) ∧ AccLocal slotArr L' := by
  intro L'
  refine ⟨fun r hr => fun ds o ss he => (h.1 r (List.mem_of_mem_filter hr) ds o ss he).1, ?_⟩
  by_cases hl : opnOf i = some "LIVEPIN"
  · have hmov : ∀ r ∈ L', ∀ ds o ss, r.li_i = .Lopn ds o ss → o ∈ movMnems := by
      intro r hr ds o ss hx
      have hr' := List.mem_of_mem_filter hr
      have := List.of_mem_filter hr
      rw [hx] at this
      simp only [bne_iff_ne, ne_eq] at this
      rcases (h.1 r hr' ds o ss hx).2 with ho | ho
      · rw [hl] at ho; cases ho; exact absurd rfl this
      · exact ho
    refine accLocal_of_noAcc (fun r hr => ?_) (fun r hr => ?_) <;>
      cases hx : r.li_i with
      | Lopn ds o ss =>
        first
          | exact isAccB_of_movMnems (hmov r hr ds o ss hx)
          | exact isArrImmB_of_movMnems (hmov r hr ds o ss hx)
      | _ => rfl
  · have : L' = L := by
      refine List.filter_eq_self.mpr fun r hr => ?_
      cases hx : r.li_i with
      | Lopn ds o ss =>
        simp only [bne_iff_ne, ne_eq]
        rcases (h.1 r hr ds o ss hx).2 with ho | ho
        · rintro rfl; exact hl ho.symm
        · exact movMnems_ne_livepin ho
      | _ => rfl
    rw [this]; exact h.2

/-- **The stored body without `LIVEPIN` has the image class locally.** For a body without
    calls, every instruction of `physBodyWithStores` (no argument loads, no output stores) after
    the `LIVEPIN` instructions are removed writes no array slot, and every indexed access
    resolves to an array inside it, given the per-instruction hypotheses of
    `physPositionEmit_physImg`. -/
theorem physBodyWithStores_physImg {slotArr : String → Option (String × Nat)}
    (shiftImm : ShiftImmOracle) (body : Lcmd) (loadBase storeBase : String) (abiW : Nat)
    (mbr : String → Option String) (callArgBaseReload : List (String × String))
    (reservedVec : List Nat) (rm : LOperand → LOperand)
    (hrm : rm = if bodyHasCall body = true then
      fun o => remapOperandCalleeSave body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o
      else fun o => remapOperand body
        (straightCallComposeTable body (physTableOut body [] reservedVec)) o)
    (hcall : ∀ i ∈ body, ∀ a b, i.li_i ≠ .Lcall a b)
    (hs15 : slotArr reloadScratch = none) (hs14 : slotArr reloadScratch2 = none)
    (hmem : ∀ c, slotArr ("mem." ++ c) = none)
    (hok : ∀ i ∈ body, ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr (rm x))
    (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n')
    (hacc : ∀ i ∈ body, AccForm slotArr rm mbr i.li_i) :
    let L := reloadArrImmBody mbr ((physBodyWithStores shiftImm body (fun _ => none) loadBase []
      storeBase abiW mbr callArgBaseReload reservedVec).filter
        fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true)
    (∀ r ∈ L, DstOk slotArr r.li_i) ∧ AccLocal slotArr L := by
  intro L
  have hL : L = body.zipIdx.flatMap fun p =>
      (reloadArrImmBody mbr (physPositionEmit shiftImm body (fun _ => none) loadBase []
        storeBase abiW mbr callArgBaseReload reservedVec p)).filter
          fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true := by
    simp only [L, physBodyWithStores_eq_flatMap, List.filter_flatMap, reloadArrImmBody_flatMap]
    congr 1
    funext p
    refine (reloadArrImmBody_filter _ _ fun i l' h x hx => ?_).symm
    obtain ⟨b, q, -, ⟨n, w, hi, rfl⟩ | ⟨d, v, k, hi, rfl⟩⟩ := reloadArrImm_eq_some h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl <;> simp [hi]
  have hblk : ∀ p ∈ body.zipIdx, BlockOk slotArr p.1.li_i
      (reloadArrImmBody mbr (physPositionEmit shiftImm body (fun _ => none) loadBase []
        storeBase abiW mbr callArgBaseReload reservedVec p)) := by
    rintro ⟨i, k⟩ hp
    have hi := List.fst_mem_of_mem_zipIdx hp
    exact physPositionEmit_physImg shiftImm body loadBase storeBase abiW mbr callArgBaseReload
      reservedVec i k rm hrm (hcall i hi) hs15 hs14 hmem (hok i hi) hreg (hacc i hi)
  rw [hL]
  refine ⟨fun r hr => ?_, accLocal_flatMap fun p hp => (blockOk_filter_livepin (hblk p hp)).2⟩
  obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
  exact (blockOk_filter_livepin (hblk p hp)).1 r hr

/-! ## 8. Names that are no frame slot -/

/-- A name whose first character is not `q` has no prefix `qsave.`. -/
theorem hasPrefix_qsave_of_head {a : String} {c : Char} (h : a.toList.head? = some c)
    (hc : c ≠ 'q') (s : String) : hasPrefix (a ++ s) "qsave." = false := by
  have e : ("qsave." : String).toList = ['q', 's', 'a', 'v', 'e', '.'] := by decide +kernel
  obtain ⟨t, ht⟩ : ∃ t, a.toList = c :: t := by
    cases hl : a.toList with
    | nil => rw [hl] at h; cases h
    | cons c' t => rw [hl] at h; cases h; exact ⟨t, rfl⟩
  simp [hasPrefix, String.toList_append, e, ht, List.isPrefixOf, Ne.symm hc]

theorem hasPrefix_qsave_k (s : String) : hasPrefix ("k." ++ s) "qsave." = false :=
  hasPrefix_qsave_of_head (c := 'k') (by decide +kernel) (by decide) s

theorem hasPrefix_qsave_kv (s : String) : hasPrefix ("kv." ++ s) "qsave." = false :=
  hasPrefix_qsave_of_head (c := 'k') (by decide +kernel) (by decide) s

theorem hasPrefix_qsave_mem (s : String) : hasPrefix ("mem." ++ s) "qsave." = false :=
  hasPrefix_qsave_of_head (c := 'm') (by decide +kernel) (by decide) s

theorem hasPrefix_qsave_argName (j : Nat) : hasPrefix (argName j) "qsave." = false :=
  hasPrefix_qsave_of_head (c := 'a') (by decide +kernel) (by decide) _

/-- A name of the x86 allocation is no `qsave.` slot. -/
theorem hasPrefix_qsave_physRegName (p : Nat) :
    hasPrefix (physRegName p x86Abi) "qsave." = false := by
  unfold physRegName
  split
  · dsimp only
    split
    · next r hr =>
      have hm := List.mem_of_getElem? hr
      have hall : ∀ r ∈ vectorRegNames, hasPrefix r "qsave." = false := by decide +kernel
      exact hall r hm
    · exact hasPrefix_qsave_kv _
  · split
    · next r hr =>
      have hm := List.mem_of_getElem? hr
      have hall : ∀ r ∈ x86Abi.allocPool, hasPrefix r "qsave." = false := by decide +kernel
      exact hall r hm
    · exact hasPrefix_qsave_k _

/-- The register name `physNameForBody` gives an argument name is no `qsave.` slot. -/
theorem hasPrefix_qsave_physNameForBody (body : Lcmd) (tbl : Array Nat) (j : Nat) :
    hasPrefix (physNameForBody body tbl (argName j)) "qsave." = false := by
  unfold physNameForBody
  split_ifs <;> first | exact hasPrefix_qsave_argName j | exact hasPrefix_qsave_physRegName _

theorem hasPrefix_slotOfReg (R : String) : hasPrefix (slotOfReg R) "qsave." = true := by
  simp [hasPrefix, slotOfReg, String.toList_append]

/-- An array slot has the prefix `qsave.`, so a name without it is no array slot. -/
theorem slotArr_none_of_prefix {slotArr : String → Option (String × Nat)}
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {q : String}
    (h : hasPrefix q "qsave." = false) : slotArr q = none := by
  cases hq : slotArr q with
  | none => rfl
  | some _ => have := hslot q (by simp [hq]); rw [h] at this; cases this

/-! ## 9. The prologue -/

/-- The save slot of an argument register is its `qsave.` slot, and the register is one of
    the six System V argument registers. -/
theorem abiSaveOfExt_spec {r s : String} (h : abiSaveOfExt r = some s) :
    s = slotOfReg r ∧ r ∈ ["RDI", "RSI", "RDX", "RCX", "R8", "R9"] := by
  unfold abiSaveOfExt abiSaveOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;> simp only [beq_iff_eq] at * <;> cases h <;>
    subst_vars <;> exact ⟨by decide +kernel, by simp⟩

/-- The saves of the arguments after the first two other than `RDI` and `RSI` (the prologue
    tail of `lfundefPhysAbiOfVirtCert`, over `extraSaveRegs`). -/
abbrev extraSaves (abiArgs : List String) : Lcmd :=
  (extraSaveRegs abiArgs).filterMap (fun abiReg =>
    match abiSaveOfExt abiReg with
    | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
    | none => none)

/-- **The saves of `extraSaves` repeat no save of the fixed prologue**: a save of `extraSaves`
    reads an argument register other than `RDI` and `RSI`, the two argument registers
    `buildPrologue` saves. -/
theorem mem_extraSaves_ne {abiArgs : List String} {j : Linstr} (h : j ∈ extraSaves abiArgs) :
    ∃ r s, abiSaveOfExt r = some s ∧ r ≠ "RDI" ∧ r ≠ "RSI" ∧
      j = ⟨0, .Lopn [.reg s] "MOVQ" [.reg r]⟩ := by
  obtain ⟨r, hr, hf⟩ := List.mem_filterMap.mp h
  obtain ⟨h1, h2⟩ := not_mem_extraSaveRegs hr
  split at hf
  · next s hs => cases hf; exact ⟨r, s, hs, h1, h2, rfl⟩
  · cases hf

theorem mem_extraSaves {abiArgs : List String} {j : Linstr} (h : j ∈ extraSaves abiArgs) :
    ∃ r s, abiSaveOfExt r = some s ∧ j = ⟨0, .Lopn [.reg s] "MOVQ" [.reg r]⟩ := by
  obtain ⟨r, -, hf⟩ := List.mem_filterMap.mp h
  split at hf
  · next s hs => cases hf; exact ⟨r, s, hs, rfl⟩
  · cases hf

/-- The moves of the prologue: the eight saves, the park of `RSI` in `R14`, then the saves
    of `extraSaves`. -/
theorem prologue_moves (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) :
    let pre := buildPrologue virt tbl (fun _ => none) ++ extraSaves abiArgs
    (∀ j ∈ pre, (slotMov? j.li_i).isSome = true) ∧
    (∀ m j d s, pre[m]? = some j → slotMov? j.li_i = some (d, s) →
      (d = reloadScratch2 ∧ m = 8) ∨ hasPrefix d "qsave." = true) ∧
    (∀ k j d R, pre[k]? = some j → slotMov? j.li_i = some (d, R) → d ≠ reloadScratch2 →
      d = slotOfReg R ∧ hasPrefix R "qsave." = false ∧ (R = reloadScratch2 → k < 8)) := by
  intro pre
  have hlen : (buildPrologue virt tbl (fun _ => none)).length = 9 := rfl
  have hP : buildPrologue virt tbl (fun _ => none) = buildPrologue {} #[] (fun _ => none) := rfl
  have c1 : (List.range 9).all (fun k => match (buildPrologue {} #[] (fun _ => none))[k]? with
      | some j => match slotMov? j.li_i with
        | some (d, R) => (d == reloadScratch2 && k == 8) ||
            (d == slotOfReg R && !hasPrefix R "qsave." && hasPrefix d "qsave." && decide (k < 8))
        | none => false
      | none => false) = true := by decide +kernel
  have hX : ∀ j ∈ extraSaves abiArgs, ∃ r s, slotMov? j.li_i = some (s, r) ∧
      s = slotOfReg r ∧ r ∈ ["RDI", "RSI", "RDX", "RCX", "R8", "R9"] := by
    intro j hj
    obtain ⟨r, s, hs, rfl⟩ := mem_extraSaves hj
    exact ⟨r, s, by simp [slotMov?], abiSaveOfExt_spec hs⟩
  have hidx : ∀ m j, pre[m]? = some j →
      (m < 9 ∧ (buildPrologue {} #[] (fun _ => none))[m]? = some j)
      ∨ (9 ≤ m ∧ j ∈ extraSaves abiArgs) := by
    intro m j hm
    by_cases h9 : m < 9
    · left; rw [List.getElem?_append_left (by omega), hP] at hm; exact ⟨h9, hm⟩
    · right; rw [List.getElem?_append_right (by omega)] at hm
      exact ⟨by omega, List.mem_of_getElem? hm⟩
  refine ⟨fun j hj => ?_, fun m j d s hm hs => ?_, fun k j d R hk hs hd => ?_⟩
  · rcases List.mem_append.mp hj with hj | hj
    · simp only [buildPrologue, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [slotMov?]
    · obtain ⟨r, s, hs, -⟩ := hX j hj; simp [hs]
  · rcases hidx m j hm with ⟨h9, hm⟩ | ⟨-, hj⟩
    · have := List.all_eq_true.mp c1 m (List.mem_range.mpr h9)
      rw [hm] at this; simp only [hs] at this
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      rcases this with h | h
      · exact Or.inl h
      · exact Or.inr h.1.2
    · obtain ⟨r, s', hs', rfl, -⟩ := hX j hj
      rw [hs] at hs'; cases hs'
      exact Or.inr (hasPrefix_slotOfReg _)
  · rcases hidx k j hk with ⟨h9, hk⟩ | ⟨h9, hj⟩
    · have := List.all_eq_true.mp c1 k (List.mem_range.mpr h9)
      rw [hk] at this; simp only [hs] at this
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true'] at this
      rcases this with h | h
      · exact absurd h.1 hd
      · exact ⟨h.1.1.1, h.1.1.2, fun _ => h.2⟩
    · obtain ⟨r, s', hs', rfl, hr⟩ := hX j hj
      rw [hs] at hs'; cases hs'
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      · intro hR; subst hR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h <;> exact absurd h (by decide +kernel)

/-- The save condition of `physImgB_of_movePrefix` on the prologue: a move into an array
    slot is the save of a register that no earlier move of the prologue writes. -/
theorem prologue_hsave {slotArr : String → Option (String × Nat)}
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) :
    let pre := buildPrologue virt tbl (fun _ => none) ++ extraSaves abiArgs
    ∀ (k : Nat) (j : Linstr) (d R : String), pre[k]? = some j →
      slotMov? j.li_i = some (d, R) → (slotArr d).isSome = true → d = slotOfReg R ∧
        ∀ (m : Nat) (j' : Linstr) (d' s' : String), m < k → pre[m]? = some j' →
          slotMov? j'.li_i = some (d', s') → d' ≠ R := by
  intro pre k j d R hk hs hd
  obtain ⟨-, hdst, hsv⟩ := prologue_moves virt tbl abiArgs
  have h14 : hasPrefix reloadScratch2 "qsave." = false := by decide +kernel
  have hd14 : d ≠ reloadScratch2 := by
    rintro rfl; rw [hslot _ hd] at h14; cases h14
  obtain ⟨hdR, hR, hR14⟩ := hsv k j d R hk hs hd14
  refine ⟨hdR, fun m j' d' s' hmk hm hs' => ?_⟩
  rintro rfl
  rcases hdst m j' d' s' hm hs' with ⟨h1, h2⟩ | h
  · have := hR14 h1; omega
  · rw [hR] at h; cases h

/-- The destinations of the argument materialisation are argument registers of
    `physNameForBody` and `R15`. -/
theorem buildArgPtrMaterialize_dstOk {slotArr : String → Option (String × Nat)}
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (virt : Lfundef) (tbl : Array Nat) (abiArgs : List String) (inLoadMap : InLoadMap) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, DstOk slotArr r.li_i := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
  have hP := slotArr_none_of_prefix hslot (hasPrefix_qsave_physNameForBody virt.lfd_body tbl j)
  have h15 : slotArr reloadScratch = none :=
    slotArr_none_of_prefix hslot (by decide +kernel)
  have hok : ∀ n, slotArr n = none → OperandOk slotArr (.reg n) := fun n hn =>
    ⟨fun q hq => by cases hq; exact hn, nofun, nofun⟩
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;>
      intro ds o ss he x hx <;>
      cases he <;>
      simp only [List.mem_singleton] at hx <;>
      subst hx <;>
      first | exact hok _ hP | exact hok _ h15

theorem calleeSaveRestoreEpilogue_dstOk {slotArr : String → Option (String × Nat)}
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    ∀ r ∈ calleeSaveRestoreEpilogue, DstOk slotArr r.li_i := by
  have hok : ∀ n, hasPrefix n "qsave." = false → OperandOk slotArr (.reg n) := fun n hn =>
    ⟨fun q hq => by cases hq; exact slotArr_none_of_prefix hslot hn, nofun, nofun⟩
  intro r hr
  simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro ds o ss he x hx <;> cases he <;> simp only [List.mem_singleton] at hx <;> subst hx <;>
    exact hok _ (by decide +kernel)

theorem buildArgPtrMaterialize_noAcc (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, isAccB r.li_i = false := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;> rfl

theorem buildArgPtrMaterialize_noArrImm (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, isArrImmB r.li_i = false := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, -, hr⟩ := List.mem_flatMap.mp hr
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;> rfl

/-! ## 10. The destinations of every position -/

/-- The destinations of an arm output satisfy every predicate that holds of its operands,
    of the scratch registers and of the cell names. -/
theorem dst_of_armOut {P : LOperand → Prop} {ins : List LOperand} {opn : String} {r : LinstrR}
    (h15 : P (.reg reloadScratch)) (h14 : P (.reg reloadScratch2))
    (hmem : ∀ c, P (.reg ("mem." ++ c))) (hins : ∀ x ∈ ins, P x) (h : ArmOut ins opn r) :
    ∀ ds o ss, r = .Lopn ds o ss → ∀ x ∈ ds, P x := by
  obtain ⟨ds, o, ss, rfl, -, hd⟩ := h
  intro ds' o' ss' he x hx
  cases he
  rcases hd x hx with h | rfl | rfl | ⟨c, rfl⟩
  · exact hins x h
  · exact h15
  · exact h14
  · exact hmem c

/-- **The destinations of one position of `physPositionEmit`**, for any argument loads,
    output stores and post-call reloads: every destination satisfies a predicate `P` that
    holds of the image under the operand map of every operand of the virtual instruction, of
    the argument registers, of the post-call reload registers, of the scratch registers and of
    the cell names. -/
theorem physPositionEmit_dst (P : LOperand → Prop)
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat)
    (mbr : String → Option String) (callArgBaseReload : List (String × String))
    (reservedVec : List Nat) (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm = if bodyHasCall body = true then
      fun o => remapOperandCalleeSave body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) o
      else fun o => remapOperand body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec)) o)
    (hs15 : P (.reg reloadScratch)) (hs14 : P (.reg reloadScratch2))
    (hmem : ∀ c, P (.reg ("mem." ++ c)))
    (hok : ∀ x ∈ lopnOperands i.li_i, P (rm x))
    (hargs : ∀ s, P (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))))
    (hcab : ∀ p ∈ callArgBaseReload, P (.reg p.1)) :
    ∀ r ∈ physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      mbr callArgBaseReload reservedVec (i, virtIdx),
      ∀ ds o ss, r.li_i = .Lopn ds o ss → ∀ x ∈ ds, P x := by
  intro r hr
  obtain ⟨ii, x⟩ := i
  simp only at hok
  have hmemN : ∀ b off, P (.reg (memName b off)) := fun b off => by
    rw [memName_eq]; exact hmem _
  unfold physPositionEmit at hr
  simp only [List.mem_append, ← hrm] at hr
  have hwrap : ∀ (L : List LinstrR) (r : Linstr),
      r ∈ L.map (fun r => ({ li_ii := ii, li_i := r } : Linstr)) → r.li_i ∈ L := by
    intro L r h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact ha
  have harm : ∀ (ins : List LOperand) (opn : String) (L : List LinstrR),
      (∀ x ∈ ins, P x) → (∀ r ∈ L, ArmOut ins opn r) →
      r ∈ L.map (fun r => ({ li_ii := ii, li_i := r } : Linstr)) →
      ∀ ds o ss, r.li_i = .Lopn ds o ss → ∀ x ∈ ds, P x :=
    fun ins opn L hins hL h => dst_of_armOut hs15 hs14 hmem hins (hL _ (hwrap L r h))
  have hnil : ∀ x ∈ ([] : List LOperand), P x := by simp
  have hsingle : ∀ (ds : List LOperand) (o : String) (ss : List LOperand),
      (∀ x ∈ ds, P x) → ∀ ds' o' ss', LinstrR.Lopn ds o ss = .Lopn ds' o' ss' →
        ∀ x ∈ ds', P x := by
    intro ds o ss h ds' o' ss' he
    cases he; exact h
  rcases hr with ((hr | hr) | hr) | hr
  · -- the inline argument loads
    rw [List.mem_flatMap] at hr
    obtain ⟨⟨s, base, off⟩, -, hr⟩ := List.mem_flatMap.mp (List.mem_flatMap.mpr hr)
    split at hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl <;>
      exact hsingle _ _ _ (by simp [hs14, hs15, hargs s])
  · -- the expansion
    split at hr
    · next d tail opn s0 s1 tail1 =>
      have hd : ∀ x ∈ [rm d], P x := by
        simp [hok d (by simp [lopnOperands])]
      split at hr
      · split at hr
        · exact harm _ _ _ hd (lowerTwoAddrShiftImm_armOut _ _ _ _ _ (movFor_ok opn)) hr
        · exact harm _ _ _ hd (lowerTwoAddr_armOut _ _ _ _ _ (movFor_ok opn)) hr
      · split at hr
        · next _ d' opn' addr val heq =>
          simp only [LinstrR.Lopn.injEq, List.cons.injEq] at heq
          obtain ⟨⟨h1, rfl⟩, h2, h3, h4, rfl⟩ := heq
          subst h1 h2 h3 h4
          split at hr
          · rw [List.mem_append] at hr
            rcases hr with hr | hr
            · exact harm _ _ _ hnil (reloadMemrefBase_armOut mbr _ opn) hr
            · exact harm _ _ _ hd (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok _)) hr
          · exact harm _ _ _ hd (legalizeSpillDst_armOut _ _ _) hr
        · next _ dsts opn' srcs _ heq =>
          simp only [LinstrR.Lopn.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          refine harm _ _ _ ?_ (legalizeSpillDst_armOut _ _ _) hr
          intro o ho
          obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
          exact hok o' (List.mem_append_left _ ho')
        · next _ _ hne => exact (hne _ _ _ rfl).elim
    · next _ d opn s =>
      have hd : ∀ x ∈ [rm d], P x := by
        simp [hok d (by simp [lopnOperands])]
      split at hr
      · exact harm _ _ _ hd (lowerNativeShiftRotate_armOut _ _ _ _ (movFor_ok opn)) hr
      · split at hr
        · rw [List.mem_append] at hr
          rcases hr with hr | hr
          · exact harm _ _ _ hnil (reloadMemrefBase_armOut mbr _ opn) hr
          · exact harm _ _ _ hd (legalizeMemLoad_armOut _ _ _ _ (movFor_ok opn)) hr
        · exact harm _ _ _ hd (legalizeOneSrc_armOut _ _ _ _) hr
    · next _ dsts opn srcs _ _ =>
      simp only [List.mem_singleton] at hr
      subst hr
      refine hsingle _ _ _ fun o ho => ?_
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
      exact hok o' (List.mem_append_left _ ho')
    · next _ _ _ hne =>
      simp only [List.mem_singleton] at hr
      subst hr
      intro ds o ss he
      exact absurd he (hne ds o ss)
  · -- the pointer reloads after a call
    split at hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact hsingle _ _ _ (by simp [hcab p hp])
    · simp at hr
  · -- the inline output store
    split at hr
    · repeat' split at hr
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals
        rcases hr with rfl | rfl | rfl <;>
          exact hsingle _ _ _ (by simp [hs14, hs15, hmemN _ _])
    · simp at hr

/-- **The stored body of a call-free body writes no `qsave.` slot**: no destination register
    of `physBodyWithStores` (at the default memref reload, post-call reloads, allocation
    reserve and ABI) has the prefix `qsave.`, for any argument loads and output stores. Its
    instance at the six System V callee-saved registers is the hypothesis
    `physBodyNoQsaveCalleeSavedWrite` of `LprogJasminWellFormed`. -/
theorem physBodyWithStores_noQsaveWrite (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (hcf : bodyHasCall body = false) :
    ∀ i ∈ physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase,
      ∀ dsts opn srcs, i.li_i = LinstrR.Lopn dsts opn srcs →
        ∀ r, LOperand.reg ("qsave." ++ r) ∉ dsts := by
  intro i hi dsts opn srcs he r hr
  rw [physBodyWithStores_eq_flatMap] at hi
  obtain ⟨⟨j, k⟩, -, hi⟩ := List.mem_flatMap.mp hi
  let P : LOperand → Prop := fun x => ∀ q, x = .reg q → hasPrefix q "qsave." = false
  have hPreg : ∀ n, hasPrefix n "qsave." = false → P (.reg n) := fun n hn q hq => by
    cases hq; exact hn
  have hP := physPositionEmit_dst P shiftImm body inLoadMap loadBase outStoreMap storeBase 0
    (fun _ => none) [] [] j k
    (fun o => remapOperand body (straightCallComposeTable body (physTableOut body outStoreMap [])) o)
    (by simp [hcf]) (hPreg _ (by decide +kernel))
    (hPreg _ (by decide +kernel)) (fun c => hPreg _ (hasPrefix_qsave_mem c))
    (fun x _ => by
      cases x with
      | reg n => exact hPreg _ (hasPrefix_qsave_physRegName _)
      | _ => intro q hq; simp [remapOperand] at hq)
    (fun s => hPreg _ (hasPrefix_qsave_physNameForBody _ _ s)) (by simp)
    i hi dsts opn srcs he _ hr ("qsave." ++ r) rfl
  have := hasPrefix_slotOfReg r
  simp only [slotOfReg] at this
  rw [this] at hP
  cases hP

/-! ## 11. The physical ABI export -/

/-- **The image class holds of the call-free looped physical ABI export.** Let `body1` be the
    allocator input body of `lfundefPhysAbiOfVirtCert` (the argument-liveness pin and the
    canonicalised memref threads of the aliased virtual body) and `mbr` its memref base
    reload map. Suppose `body1` has no call (`hcf`), each of its indexed accesses and
    constant-index array writes has one of the forms of `AccForm` and its base is reloaded
    from an array slot (`hshape`), no array operand of `body1`
    names an array slot (`harr`), and every array slot has the prefix `qsave.` (`hslot`).
    Then the export at x86 is in the class `physImgB slotArr`. -/
theorem physImgB_lfundefPhysAbiOfVirtCert {slotArr : String → Option (String × Nat)}
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSaveOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false)
    (hshape : ∀ i ∈ body1, AccForm slotArr
      (fun o => remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o)
      mbr i.li_i)
    (harr : ∀ i ∈ body1, ∀ q n, LOperand.arr q n ∈ lopnOperands i.li_i → slotArr q = none)
    (hslot : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    physImgB slotArr (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body = true := by
  have hb : ∃ sh cab, (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body =
      (buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 []) (fun _ => none)
          ++ extraSaves abiArgs) ++
        buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 []) abiArgs
            (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodyWithStores sh body1 (fun _ => none)
            reloadScratch2 [] reloadScratch2 0 mbr cab).filter
              fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
            calleeSaveRestoreEpilogue := by
    subst hb1 hmbr
    simp only [lfundefPhysAbiOfVirtCert]
    exact ⟨_, _, rfl⟩
  obtain ⟨sh, cab, hb⟩ := hb
  rw [hb, List.append_assoc]
  have hs15 : slotArr reloadScratch = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hs14 : slotArr reloadScratch2 = none := slotArr_none_of_prefix hslot (by decide +kernel)
  have hmem : ∀ c, slotArr ("mem." ++ c) = none := fun c =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_mem c)
  have hP : ∀ p, slotArr (physRegName p x86Abi) = none := fun p =>
    slotArr_none_of_prefix hslot (hasPrefix_qsave_physRegName p)
  have hcall : ∀ i ∈ body1, ∀ a b, i.li_i ≠ .Lcall a b := by
    intro i hi a b he
    have := List.any_eq_false.mp hcf i hi
    rw [he] at this
    exact this rfl
  have hok : ∀ i ∈ body1, ∀ x ∈ lopnOperands i.li_i, OperandOk slotArr
      ((fun o => remapOperand body1
        (straightCallComposeTable body1 (physTableOut body1 [] [])) o) x) := by
    intro i hi x hx
    cases x with
    | reg n => exact ⟨fun q hq => by cases hq; exact hP _, nofun, nofun⟩
    | arrIdx b y s => exact ⟨nofun, nofun, fun q j sc hq => by cases hq; exact hP _⟩
    | arr q n => exact ⟨nofun, fun q' n' hq => by cases hq; exact harr i hi q n hx, nofun⟩
    | imm _ => exact ⟨nofun, nofun, nofun⟩
  obtain ⟨hFd, hFa⟩ := physBodyWithStores_physImg sh body1 reloadScratch2 reloadScratch2 0 mbr
    cab [] _ (by simp [hcf]) hcall hs15 hs14 hmem hok (fun n => ⟨_, rfl⟩) hshape
  obtain ⟨hpre, -, -⟩ := prologue_moves { virt0 with lfd_body := body1 } (physTableOut body1 [])
    abiArgs
  have hepiAcc : ∀ r ∈ calleeSaveRestoreEpilogue, isAccB r.li_i = false := by
    intro r hr
    simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hepiImm : ∀ r ∈ calleeSaveRestoreEpilogue, isArrImmB r.li_i = false := by
    intro r hr
    simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hA : AccLocal slotArr
      ((buildPrologue { virt0 with lfd_body := body1 } (physTableOut body1 []) (fun _ => none)
          ++ extraSaves abiArgs) ++
        (buildArgPtrMaterialize { virt0 with lfd_body := body1 } (physTableOut body1 []) abiArgs
            (fun _ => none) ++
          insertEpilogue (reloadArrImmBody mbr ((physBodyWithStores sh body1 (fun _ => none)
            reloadScratch2 [] reloadScratch2 0 mbr cab).filter
              fun r => match r.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true))
            calleeSaveRestoreEpilogue)) := by
    refine accLocal_append (accLocal_of_noAcc (fun r hr => ?_) (fun r hr => ?_))
      (accLocal_append (accLocal_of_noAcc (buildArgPtrMaterialize_noAcc _ _ _ _)
        (buildArgPtrMaterialize_noArrImm _ _ _ _)) ?_)
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hpre r hr)
      exact isAccB_of_slotMov hp
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hpre r hr)
      exact isArrImmB_of_slotMov hp
    · unfold insertEpilogue
      exact accLocal_append (accLocal_append (accLocal_dropLast hFa)
        (accLocal_of_noAcc hepiAcc hepiImm)) (accLocal_of_noAcc (by simp [isAccB]) (by simp [isArrImmB]))
  refine physImgB_of_movePrefix hpre (prologue_hsave hslot _ _ abiArgs) ?_
    (fun k i _ hi => hA k i hi)
  intro j hj ds o ss he x hx
  have hD : DstOk slotArr j.li_i := by
    rcases List.mem_append.mp hj with hj | hj
    · exact buildArgPtrMaterialize_dstOk hslot _ _ _ _ j hj
    · unfold insertEpilogue at hj
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with (hj | hj) | rfl
      · exact hFd j (List.dropLast_subset _ hj)
      · exact calleeSaveRestoreEpilogue_dstOk hslot j hj
      · exact fun _ _ _ h => by cases h
  exact hD ds o ss he x hx

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
