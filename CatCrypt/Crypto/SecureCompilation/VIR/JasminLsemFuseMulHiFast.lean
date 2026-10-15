/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
public import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
# A single-pass implementation of the fusion check

`fuseOKL` checks every position `k` of the source body against the symbolic state `blk c k`,
which it recomputes from the start of the block, and it locates the block start by
`bstart`, a recursion over `k` that indexes the list at every step. `fuseOKLFast` walks the
body once, carrying the symbolic state of the current position and the remaining low
destinations, and keeps no guards, which `posOK` does not read.

The carried state `FSt` holds the symbolic registers and arrays in hash maps, so a lookup
costs a hash-map access and not one test per write since the start of the block. A step
runs `symStep` on the state `FSt.toSSt` the maps describe and inserts the at most two
registers and array names the step writes (`FSt.upd`), which the frame lemma `symStep_frame`
justifies. `stepOut` takes both states apart before it inserts, so the closures of the
returned state, which read the maps, are released and the maps are updated in place.
Symbolic words share their subterms in memory, and the comparisons of `siteOK` run through
`decEqTermP`, which tests pointer equality before it compares two subterms and compares a
subterm only when the scalar fields and every earlier subterm agree, so that two different
words are compared along one path to their first difference. Compiled code runs `termEqP`
as `termEqPMemo`, which keeps the address pairs of the subterms found equal during one
comparison in a hash set, so that equal words built along two paths, whose subterms are equal
but distinct objects, are compared once per pair of subterm objects and not once per path.
`mulLoBF` reads the outer constructor and operation of the low destination's word before any
comparison.

The width check of `posOK` over every register of `E` walks the width base `STerm.wbase` of
each word, whose length grows with the block. The pass carries that check as a flag: a step
recomputes it only for the registers of `E` among the at most two registers it writes
(`all_w64_frame`), which is exact while the check held before the step, and a pass whose
check fails stops there.

The equality `fuseOKL_eq_fast` is registered with `@[csimp]`, so compiled code runs
`fuseOKLFast` whenever it calls `fuseOKL`; the definition `fuseOKL` and its theorems are
unchanged.

## Main definitions

* `FSt` — a symbolic state with its registers and arrays in hash maps.
* `decAndL` — a decided conjunction whose second decision runs only when the first holds.
* `decEqTermP` — equality of symbolic words with a pointer-equality test at each subterm.
* `termEqMemo` — the compiled equality of symbolic words, with a table of the address pairs
  found equal.
* `mulLoBF` — the low-product test of a fused site, decided on the outer constructor first.
* `posPass` — the per-position checks from the current position on, in one forward pass.
* `FOut` — a symbolic outcome over the hash-map state with the carried width flag.
* `stepOut` — the hash-map state and the width flag after a step.
* `posPassF` — `posPass` over the hash-map state.
* `fuseOKLFast` — the fusion check in one forward pass over the body.

## Main results

* `symStep_frame` — a symbolic step changes only the first two written registers and array
  names.
* `FSt.toSSt_upd` — the hash-map state after a step describes the state `symStep` returns.
* `posPass_drop` — the forward pass from position `k` equals the per-position checks from `k`.
* `all_w64_frame` — after a step, the width check of `E` is the check of its written
  registers, when the check held before.
* `nextF_EA`, `nextF_toS` — the step over the hash-map state keeps the width flag exact and
  describes `nextS`.
* `posPassF_eq` — `posPassF` equals `posPass` on the described state, when the flag is
  exact.
* `fuseOKL_eq_fast` — `fuseOKL = fuseOKLFast`, registered with `@[csimp]`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## The forward pass over closure states -/

/-- The symbolic outcome with its guards dropped. -/
def forgetG : SOut → SOut
  | .ok ss _ => .ok ss []
  | .fail => .fail
  | .unk => .unk

/-- The check of `posOK` at a position with the low-destination entry `l`, the instruction
    `ci` and the symbolic outcome `o`. -/
def posAt (E : List String) (l : Option (Option String)) (ci : Option LinstrRM) (o : SOut) :
    Bool :=
  match o with
  | .ok ss _ =>
      E.all (fun x => w64 E (ss.regs x)) &&
        (match l with
         | some (some d) => ci.any (fun i => siteOK E d i ss)
         | _ => true)
  | .fail => true
  | .unk => false

/-- The symbolic outcome after the instruction `i`, guards dropped: the start state after a
    control instruction, the symbolic step otherwise. -/
def nextS (o : SOut) (i : LinstrRM) : SOut :=
  if isCtlB i then .ok SSt.start [] else forgetG (symSnoc o i)

/-- The positions of a body from the current one on, checked in one forward pass: `Ls` and
    `cs` are the remaining low destinations and instructions, `o` the symbolic outcome at the
    current position. -/
def posPass (E : List String) : List (Option String) → List LinstrRM → SOut → Bool
  | Ls, [], o => posAt E Ls.head? none o
  | Ls, i :: cs, o => posAt E Ls.head? (some i) o && posPass E Ls.tail cs (nextS o i)

theorem posAt_forgetG (E : List String) (l : Option (Option String)) (ci : Option LinstrRM)
    (o : SOut) : posAt E l ci (forgetG o) = posAt E l ci o := by
  cases o <;> rfl

theorem forgetG_symSnoc_forgetG (o : SOut) (i : LinstrRM) :
    forgetG (symSnoc (forgetG o) i) = forgetG (symSnoc o i) := by
  cases o with
  | ok ss g => simp only [forgetG, symSnoc]; cases symStep i ss <;> rfl
  | fail => rfl
  | unk => rfl

theorem posOK_eq_posAt (E : List String) (L : List (Option String)) (c : List LinstrRM)
    (k : Nat) : posOK E L c k = posAt E L[k]? c[k]? (blk c k) := rfl

theorem nextS_blk {c : List LinstrRM} {k : Nat} {i : LinstrRM} (hk : c[k]? = some i) :
    nextS (forgetG (blk c k)) i = forgetG (blk c (k + 1)) := by
  unfold nextS
  cases hc : isCtlB i
  · rw [blk_succ_lopn hk hc, forgetG_symSnoc_forgetG]; rfl
  · rw [blk_succ_ctl hk hc]; rfl

theorem posPass_drop (E : List String) (L : List (Option String)) (c : List LinstrRM) :
    ∀ (n k : Nat), k + n = c.length →
      posPass E (L.drop k) (c.drop k) (forgetG (blk c k))
        = (List.range' k (n + 1)).all (posOK E L c)
  | 0, k, h => by
      have hc : c.drop k = [] := List.drop_eq_nil_of_le (by omega)
      have hk : c[k]? = none := List.getElem?_eq_none (by omega)
      rw [hc, posPass, List.head?_drop, posAt_forgetG]
      simp [posOK_eq_posAt, hk]
  | n + 1, k, h => by
      have hlt : k < c.length := by omega
      rw [List.drop_eq_getElem_cons hlt, posPass, List.head?_drop, posAt_forgetG,
        List.tail_drop, nextS_blk (List.getElem?_eq_getElem hlt),
        posPass_drop E L c n (k + 1) (by omega), List.range'_succ (s := k), List.all_cons,
        posOK_eq_posAt E L c k, List.getElem?_eq_getElem hlt]

/-! ## The frame of a symbolic step -/

/-- `ss'` agrees with `ss` on every register outside the first two entries of `ss'.wr` and
    on every array name outside the first two entries of `ss'.awr`. -/
def FrameT (ss ss' : SSt) : Prop :=
  (∀ r, r ∉ ss'.wr.take 2 → ss'.regs r = ss.regs r) ∧
    (∀ r, r ∉ ss'.awr.take 2 → ss'.arrs r = ss.arrs r)

theorem frameT_refl (ss : SSt) : FrameT ss ss := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem frameT_setR (ss : SSt) (d : String) (t : STerm) : FrameT ss (ss.setR d t) := by
  refine ⟨fun r hr => ?_, fun _ _ => rfl⟩
  simp only [SSt.setR, List.take_succ_cons, List.mem_cons, not_or] at hr
  rw [SSt.setR_regs, if_neg hr.1]

theorem frameT_setR_setR (ss : SSt) (d e : String) (t u : STerm) :
    FrameT ss ((ss.setR d t).setR e u) := by
  refine ⟨fun r hr => ?_, fun _ _ => rfl⟩
  simp only [SSt.setR, List.take_succ_cons, List.mem_cons, not_or] at hr
  rw [SSt.setR_regs, SSt.setR_regs, if_neg hr.1, if_neg hr.2.1]

theorem frameT_setA (ss : SSt) (d : String) (a : SArr) : FrameT ss (ss.setA d a) := by
  refine ⟨fun _ _ => rfl, fun r hr => ?_⟩
  simp only [SSt.setA, List.take_succ_cons, List.mem_cons, not_or] at hr ⊢
  exact if_neg hr.1

theorem liftR_frame {ss : SSt} {o : ROut} {ss' : SSt} {gs : List SG}
    (h : liftR ss o = .ok ss' gs) : FrameT ss ss' := by
  cases o <;> simp only [liftR, SOut.ok.injEq, reduceCtorEq] at h
  · rw [← h.1]; exact frameT_setR _ _ _
  · rw [← h.1]; exact frameT_refl _

theorem symMem_frame (i : LinstrRM) {ss : SSt} {ss' : SSt} {gs : List SG}
    (h : symMem i ss = .ok ss' gs) : FrameT ss ss' := by
  obtain ⟨x, tag⟩ := i
  unfold symMem at h
  cases tag with
  | load w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_setR _ _ _
      · exact liftR_frame h
  | store w n =>
      dsimp only at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_setA _ _ _
      · exact liftR_frame h
  | loadC => cases h
  | storeC => cases h
  | zero _ _ => cases h
  | storeImm _ _ => cases h
  | reg cd => exact liftR_frame h

theorem symCarry_frame {op : CarryOp} {d : String} {a b : LOperand} {ss : SSt}
    {ss' : SSt} {gs : List SG} (h : symCarry op d a b ss = .ok ss' gs) : FrameT ss ss' := by
  unfold symCarry at h
  split at h
  · cases op <;> simp only [SOut.ok.injEq] at h <;> rw [← h.1] <;> exact frameT_setR _ _ _
  · cases h

theorem symWide_frame {w : WideOp} {ss : SSt} {ss' : SSt} {gs : List SG}
    (h : symWide w ss = .ok ss' gs) : FrameT ss ss' := by
  cases w with
  | mov d b =>
      simp only [symWide] at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_setR _ _ _
      · cases h
  | mulx lo hi b =>
      simp only [symWide] at h
      split at h
      · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_setR_setR _ _ _ _ _
      · cases h

/-- **A symbolic step changes at most the first two written registers and array names.** -/
theorem symStep_frame (i : LinstrRM) {ss : SSt} {ss' : SSt} {gs : List SG}
    (h : symStep i ss = .ok ss' gs) : FrameT ss ss' := by
  unfold symStep at h
  split at h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_refl _
    · cases h
  · split at h
    · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_setR _ _ _
    · split at h
      · cases h
      · split at h
        · simp only [SOut.ok.injEq] at h; rw [← h.1]; exact frameT_refl _
        · cases h
        · cases h
        · split at h
          · exact symCarry_frame h
          · split at h
            · exact symWide_frame h
            · cases hm : symMem i ss with
              | ok s1 g1 =>
                  rw [hm] at h
                  simp only [aluFl, SOut.ok.injEq] at h
                  rw [← h.1]
                  exact (symMem_frame i hm :)
              | fail => rw [hm] at h; cases h
              | unk => rw [hm] at h; cases h

/-! ## The hash-map state -/

/-- A symbolic state whose registers are a register map and whose arrays are a hash map; an
    absent register or array name holds its start value. The remaining fields are those of
    `SSt`. -/
structure FSt where
  /-- The symbolic words of the registers written. -/
  regs : RegMap
  /-- The symbolic arrays of the array names written. -/
  arrs : Std.HashMap String SArr
  /-- The symbolic zero flag. -/
  zf : SFlag
  /-- The registers written. -/
  wr : List String
  /-- The array names written. -/
  awr : List String
  /-- The symbolic carry flag. -/
  cf : STerm
  /-- The symbolic overflow flag. -/
  of : STerm

/-- The symbolic state an `FSt` describes. -/
def FSt.toSSt (F : FSt) : SSt :=
  { rf := Quotient.mk _ F.regs, arrs := fun r => F.arrs.getD r (.cell r), zf := F.zf,
    wr := F.wr, awr := F.awr, cf := F.cf, of := F.of }

/-- The hash-map state at the start of a block. -/
def FSt.start : FSt := ⟨∅, ∅, .init, [], [], .cin false, .cin true⟩

/-- The hash-map state after a step to `ss'`: the first two written registers and array names
    of `ss'` take their values in `ss'`, the other fields are those of `ss'`. -/
def FSt.upd (F : FSt) (ss' : SSt) : FSt :=
  ⟨((ss'.wr.take 2).map fun d => (d, ss'.regs d)).foldl (fun m p => m.insert p.1 p.2) F.regs,
    ((ss'.awr.take 2).map fun d => (d, ss'.arrs d)).foldl (fun m p => m.insert p.1 p.2) F.arrs,
    ss'.zf, ss'.wr, ss'.awr, ss'.cf, ss'.of⟩

theorem FSt.toSSt_start : FSt.start.toSSt = SSt.start := by
  refine SSt.ext (fun r => rfl) (funext fun r => Std.HashMap.getD_empty) rfl rfl rfl rfl rfl

theorem getD_foldl_insert {β : Type} (f : String → β) (r : String) (dflt : β) :
    ∀ (l : List String) (m : Std.HashMap String β),
      (l.foldl (fun m d => m.insert d (f d)) m).getD r dflt
        = if r ∈ l then f r else m.getD r dflt
  | [], m => by simp
  | d :: l, m => by
      rw [List.foldl_cons, getD_foldl_insert f r dflt l, Std.HashMap.getD_insert]
      by_cases hr : r ∈ l
      · simp [hr]
      · by_cases hd : d = r
        · subst hd; simp
        · simp [hr, hd, Ne.symm hd]

theorem rd_foldl_insert (f : String → STerm) (r : String) :
    ∀ (l : List String) (m : RegMap),
      RegMap.rd (l.foldl (fun m d => m.insert d (f d)) m) r
        = if r ∈ l then f r else RegMap.rd m r
  | [], m => by simp
  | d :: l, m => by
      rw [List.foldl_cons, rd_foldl_insert f r l, RegMap.rd_insert]
      by_cases hr : r ∈ l
      · simp [hr]
      · by_cases hd : r = d
        · subst hd; simp
        · simp [hr, hd]

/-- **The hash-map state after a step describes the state the step returns.** -/
theorem FSt.toSSt_upd {F : FSt} {ss' : SSt} (h : FrameT F.toSSt ss') :
    (F.upd ss').toSSt = ss' := by
  obtain ⟨hr, ha⟩ := h
  refine SSt.ext (fun r => ?_) (funext fun r => ?_) rfl rfl rfl rfl rfl
  · show RegMap.rd (((ss'.wr.take 2).map fun d => (d, ss'.regs d)).foldl
      (fun m p => m.insert p.1 p.2) F.regs) r = ss'.regs r
    rw [List.foldl_map, rd_foldl_insert]
    split
    · rfl
    · next hn => exact (hr r hn).symm
  · simp only [FSt.toSSt, FSt.upd, List.foldl_map]
    rw [getD_foldl_insert]
    split
    · rfl
    · next hn => exact (ha r hn).symm

/-! ## Equality of symbolic words with a pointer-equality test -/

/-- The conjunction `p ∧ q` decided by `dp`, with the decision `dq` of `q` called only when
    `p` holds. -/
@[inline] def decAndL {p q : Prop} (dp : Decidable p) (dq : p → Decidable q) :
    Decidable (p ∧ q) :=
  match dp with
  | isTrue hp =>
      match dq hp with
      | isTrue hq => isTrue ⟨hp, hq⟩
      | isFalse hq => isFalse fun h => hq h.2
  | isFalse hp => isFalse fun h => hp h.1

mutual
/-- Equality of symbolic words, decided structurally: the scalar fields are compared first,
    then the subterms from left to right, each with a pointer-equality test
    (`withPtrEqDecEq`) before its comparison, and each comparison runs only when every earlier
    one succeeded (`decAndL`). Subterms shared in memory are compared in constant time, and
    two words that differ are compared along one path to their first difference. -/
def decEqTermP : (a b : STerm) → Decidable (a = b)
  | .immAt n x, .immAt n' x' =>
      @decidable_of_iff _ (n = n' ∧ x = x') (by simp)
        (decAndL (decEq n n') fun _ => withPtrEqDecEq x x' fun _ => decEqTermP x x')
  | .bin m x y, .bin m' x' y' =>
      @decidable_of_iff _ (m = m' ∧ x = x' ∧ y = y') (by simp)
        (decAndL (decEq m m') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            withPtrEqDecEq y y' fun _ => decEqTermP y y')
  | .un m x, .un m' x' =>
      @decidable_of_iff _ (m = m' ∧ x = x') (by simp)
        (decAndL (decEq m m') fun _ => withPtrEqDecEq x x' fun _ => decEqTermP x x')
  | .shImm m k x, .shImm m' k' x' =>
      @decidable_of_iff _ (m = m' ∧ k = k' ∧ x = x') (by simp)
        (decAndL (decEq m m') fun _ => decAndL (decEq k k') fun _ =>
          withPtrEqDecEq x x' fun _ => decEqTermP x x')
  | .aget a w n i, .aget a' w' n' i' =>
      @decidable_of_iff _ (w = w' ∧ n = n' ∧ i = i' ∧ a = a')
        (by simp only [STerm.aget.injEq]; tauto)
        (decAndL (decEq w w') fun _ => decAndL (decEq n n') fun _ =>
          decAndL (withPtrEqDecEq i i' fun _ => decEqTermP i i') fun _ =>
            withPtrEqDecEq a a' fun _ => decEqArrP a a')
  | .aluF op o x y z, .aluF op' o' x' y' z' =>
      @decidable_of_iff _ (op = op' ∧ o = o' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
        (decAndL (decEq op op') fun _ => decAndL (decEq o o') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            decAndL (withPtrEqDecEq y y' fun _ => decEqTermP y y') fun _ =>
              withPtrEqDecEq z z' fun _ => decEqTermP z z')
  | .carryW op x y z, .carryW op' x' y' z' =>
      @decidable_of_iff _ (op = op' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
        (decAndL (decEq op op') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            decAndL (withPtrEqDecEq y y' fun _ => decEqTermP y y') fun _ =>
              withPtrEqDecEq z z' fun _ => decEqTermP z z')
  | .carryF op o x y z, .carryF op' o' x' y' z' =>
      @decidable_of_iff _ (op = op' ∧ o = o' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
        (decAndL (decEq op op') fun _ => decAndL (decEq o o') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            decAndL (withPtrEqDecEq y y' fun _ => decEqTermP y y') fun _ =>
              withPtrEqDecEq z z' fun _ => decEqTermP z z')
  | .mulx h x y, .mulx h' x' y' =>
      @decidable_of_iff _ (h = h' ∧ x = x' ∧ y = y') (by simp)
        (decAndL (decEq h h') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            withPtrEqDecEq y y' fun _ => decEqTermP y y')
  | .cout s x y z, .cout s' x' y' z' =>
      @decidable_of_iff _ (s = s' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
        (decAndL (decEq s s') fun _ =>
          decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
            decAndL (withPtrEqDecEq y y' fun _ => decEqTermP y y') fun _ =>
              withPtrEqDecEq z z' fun _ => decEqTermP z z')
  | .sel x y z, .sel x' y' z' =>
      @decidable_of_iff _ (x = x' ∧ y = y' ∧ z = z') (by simp)
        (decAndL (withPtrEqDecEq x x' fun _ => decEqTermP x x') fun _ =>
          decAndL (withPtrEqDecEq y y' fun _ => decEqTermP y y') fun _ =>
            withPtrEqDecEq z z' fun _ => decEqTermP z z')
  | a, b => decEq a b

/-- Equality of symbolic arrays, decided structurally: the shape first, then the index, the
    value and the array below, each with a pointer-equality test before its comparison and
    each comparison run only when every earlier one succeeded. -/
def decEqArrP : (a b : SArr) → Decidable (a = b)
  | .aset a w n i v, .aset a' w' n' i' v' =>
      @decidable_of_iff _ (w = w' ∧ n = n' ∧ i = i' ∧ v = v' ∧ a = a')
        (by simp only [SArr.aset.injEq]; tauto)
        (decAndL (decEq w w') fun _ => decAndL (decEq n n') fun _ =>
          decAndL (withPtrEqDecEq i i' fun _ => decEqTermP i i') fun _ =>
            decAndL (withPtrEqDecEq v v' fun _ => decEqTermP v v') fun _ =>
              withPtrEqDecEq a a' fun _ => decEqArrP a a')
  | a, b => decEq a b
end

/-- The pairs of addresses of symbolic words found equal during one comparison. -/
abbrev EqMemo := Std.HashSet (USize × USize)

mutual
/-- Structural equality of symbolic words with a table of the address pairs already found
    equal: a pair of words that are one object, or whose addresses are in the table, is
    equal; otherwise the scalar fields are compared, then the subterms from left to right,
    each only when every earlier comparison succeeded, and a pair found equal is added to the
    table. Each pair of subterm objects is compared structurally at most once per call. -/
unsafe def termEqMemo (a b : STerm) : StateM EqMemo Bool := do
  if ptrEq a b then return true
  let key := (ptrAddrUnsafe a, ptrAddrUnsafe b)
  if (← get).contains key then return true
  let r ← match a, b with
    | .immAt n x, .immAt n' x' => if n == n' then termEqMemo x x' else pure false
    | .bin m x y, .bin m' x' y' =>
        if m == m' then do
          if ← termEqMemo x x' then termEqMemo y y' else pure false
        else pure false
    | .un m x, .un m' x' => if m == m' then termEqMemo x x' else pure false
    | .shImm m k x, .shImm m' k' x' =>
        if m == m' && k == k' then termEqMemo x x' else pure false
    | .aget a w n i, .aget a' w' n' i' =>
        if w == w' && n == n' then do
          if ← termEqMemo i i' then arrEqMemo a a' else pure false
        else pure false
    | .aluF op o x y z, .aluF op' o' x' y' z' =>
        if op == op' && o == o' then termEqMemo3 x y z x' y' z' else pure false
    | .carryW op x y z, .carryW op' x' y' z' =>
        if op == op' then termEqMemo3 x y z x' y' z' else pure false
    | .carryF op o x y z, .carryF op' o' x' y' z' =>
        if op == op' && o == o' then termEqMemo3 x y z x' y' z' else pure false
    | .mulx h x y, .mulx h' x' y' =>
        if h == h' then do
          if ← termEqMemo x x' then termEqMemo y y' else pure false
        else pure false
    | .cout s x y z, .cout s' x' y' z' =>
        if s == s' then termEqMemo3 x y z x' y' z' else pure false
    | .sel x y z, .sel x' y' z' => termEqMemo3 x y z x' y' z'
    | a, b => pure (decide (a = b))
  if r then modify (·.insert key)
  return r

/-- The pairs `(x, x')`, `(y, y')`, `(z, z')` compared by `termEqMemo` from left to right,
    each only when every earlier comparison succeeded. -/
unsafe def termEqMemo3 (x y z x' y' z' : STerm) : StateM EqMemo Bool := do
  if ← termEqMemo x x' then
    if ← termEqMemo y y' then termEqMemo z z' else pure false
  else pure false

/-- Structural equality of symbolic arrays: a pair that is one object is equal; otherwise the
    shape, the index, the value and the array below are compared, each only when every
    earlier comparison succeeded, with the words compared by `termEqMemo`. -/
unsafe def arrEqMemo (a b : SArr) : StateM EqMemo Bool := do
  if ptrEq a b then return true
  match a, b with
  | .aset a w n i v, .aset a' w' n' i' v' =>
      if w == w' && n == n' then do
        if ← termEqMemo i i' then
          if ← termEqMemo v v' then arrEqMemo a a' else pure false
        else pure false
      else pure false
  | a, b => pure (decide (a = b))
end

/-- `termEqMemo` from the empty table. -/
unsafe def termEqPMemo (a b : STerm) : Bool := (termEqMemo a b).run' {}

/-- The Boolean equality of symbolic words through `decEqTermP`. Compiled code runs
    `termEqPMemo`, which compares each pair of subterm objects structurally at most once, so
    that two equal words whose shared subterms are distinct objects are compared in time
    polynomial in their numbers of distinct subterm objects. -/
@[implemented_by termEqPMemo]
def termEqP (a b : STerm) : Bool := @decide (a = b) (decEqTermP a b)

theorem termEqP_eq (a b : STerm) : termEqP a b = (a == b) := by
  unfold termEqP
  exact congrArg (@decide (a = b)) (Subsingleton.elim _ _)

/-- `mulLoB` decided on the outer constructor and operation of `dt` first: a low `MUL` compares
    its sources with `a` and `b` in both orders, a low `mulx` in the given order, and any other
    word fails at the root. -/
def mulLoBF (dt a b : STerm) : Bool :=
  match dt with
  | .bin m x y => m == "MUL" && ((termEqP x a && termEqP y b) || (termEqP x b && termEqP y a))
  | .mulx h x y => !h && termEqP x a && termEqP y b
  | _ => false

theorem mulLoBF_eq : mulLoBF = mulLoB := by
  funext dt a b
  cases dt <;> simp only [mulLoBF, mulLoB, termEqP_eq] <;> rw [Bool.eq_iff_iff] <;> simp <;>
    tauto

/-- `siteOK` with the comparisons of `termEqP`. -/
def siteOKF (E : List String) (d : String) (i : LinstrRM) (ss : SSt) : Bool :=
  match i with
  | (.Lopn [.reg _] opn [.reg h1, .reg s2], .reg _) =>
      stripWidthTag opn == "MULXHI" && (nameOK d && d != "RDX") && w64 E (ss.regs h1)
        && w64 E (ss.regs s2)
        && mulLoBF (ss.regs d) (ss.regs h1) (ss.regs s2)
  | _ => false

theorem siteOKF_eq : siteOKF = siteOK := by
  funext E d i ss
  unfold siteOKF siteOK
  rw [mulLoBF_eq]
  split
  · rfl
  · split
    · next h => exact absurd rfl (h _ _ _ _ _)
    · rfl

/-! ## The forward pass over the hash-map state -/

/-- `w64` with the width base `STerm.wbase` computed once. -/
def w64F (E : List String) (t : STerm) : Bool :=
  let b := t.wbase
  b.wknown == some 64 || (match b with | .reg x => E.contains x | _ => false)

theorem w64F_eq : w64F = w64 := rfl

/-- A symbolic outcome over the hash-map state, guards dropped; a described state carries
    the flag `ea`, which the forward pass keeps equal to the width check of every register
    of `E` while that check holds (`FOut.EA`). -/
inductive FOut where
  | ok (F : FSt) (ea : Bool)
  | fail
  | unk

/-- The symbolic outcome an `FOut` describes. -/
def FOut.toS : FOut → SOut
  | .ok F _ => .ok F.toSSt []
  | .fail => .fail
  | .unk => .unk

/-- The flag of a described state is the width check `posAt` makes of every register of
    `E`. -/
def FOut.EA (E : List String) : FOut → Prop
  | .ok F ea => ea = E.all (fun x => w64 E (F.toSSt.regs x))
  | .fail => True
  | .unk => True

/-- `posAt` over the hash-map state, with the width check of the registers of `E` read from
    the carried flag. -/
def posAtF (E : List String) (l : Option (Option String)) (ci : Option LinstrRM) (o : FOut) :
    Bool :=
  match o with
  | .ok F ea =>
      ea &&
        (match l with
         | some (some d) => ci.any (fun i => siteOKF E d i F.toSSt)
         | _ => true)
  | .fail => true
  | .unk => false

/-- The outcome after a step from `F` to `ss'`: the state `F.upd ss'`, and the flag that every
    register of `E` among the first two written registers of `ss'` has a word of width `64`.
    Both states are taken apart before the maps are updated, so that the closures of `ss'`,
    which read the maps of `F`, are released before the inserts. -/
def stepOut (E : List String) (F : FSt) (ss' : SSt) : FOut :=
  match F, ss' with
  | ⟨mr, ma, _, _, _, _, _⟩, ⟨rf, arrs, zf, wr, awr, cf, of, _, _⟩ =>
      let rv := (wr.take 2).map fun d => (d, rf.get d)
      let av := (awr.take 2).map fun d => (d, arrs d)
      .ok ⟨rv.foldl (fun m p => m.insert p.1 p.2) mr, av.foldl (fun m p => m.insert p.1 p.2) ma,
          zf, wr, awr, cf, of⟩
        (rv.all fun p => !E.contains p.1 || w64F E p.2)

theorem stepOut_eq (E : List String) (F : FSt) (ss' : SSt) :
    stepOut E F ss' = .ok (F.upd ss')
      (((ss'.wr.take 2).map fun d => (d, ss'.regs d)).all
        fun p => !E.contains p.1 || w64F E p.2) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := F
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := ss'
  rfl

/-- `nextS` over the hash-map state: the step runs `symStep` on the described state and
    updates the maps and the flag by `stepOut`. -/
def nextF (E : List String) (o : FOut) (i : LinstrRM) : FOut :=
  if isCtlB i then .ok FSt.start true else
    match o with
    | .ok F _ =>
        match symStep i F.toSSt with
        | .ok ss' _ => stepOut E F ss'
        | .fail => .fail
        | .unk => .unk
    | .fail => .fail
    | .unk => .unk

/-- `posPass` over the hash-map state. -/
def posPassF (E : List String) : List (Option String) → List LinstrRM → FOut → Bool
  | Ls, [], o => posAtF E Ls.head? none o
  | Ls, i :: cs, o => posAtF E Ls.head? (some i) o && posPassF E Ls.tail cs (nextF E o i)

theorem posAtF_eq (E : List String) (l : Option (Option String)) (ci : Option LinstrRM)
    {o : FOut} (h : o.EA E) : posAtF E l ci o = posAt E l ci o.toS := by
  cases o with
  | ok F ea =>
      simp only [FOut.EA] at h
      subst h
      simp only [posAtF, posAt, FOut.toS, siteOKF_eq]
  | fail => rfl
  | unk => rfl

/-- Every register of `E` has a word of width `64` in the start state. -/
theorem all_w64_start (E : List String) : E.all (fun x => w64 E (SSt.start.regs x)) = true :=
  List.all_eq_true.mpr fun x hx => by simp [w64, STerm.wbase, STerm.wknown, hx]

/-- After a step that passes the width check before it, the width check of every register of
    `E` is the check of the registers of `E` among the first two written registers. -/
theorem all_w64_frame {E : List String} {ss ss' : SSt} (hf : FrameT ss ss')
    (h : E.all (fun x => w64 E (ss.regs x)) = true) :
    (((ss'.wr.take 2).map fun d => (d, ss'.regs d)).all
        fun p => !E.contains p.1 || w64F E p.2)
      = E.all (fun x => w64 E (ss'.regs x)) := by
  rw [w64F_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.or_eq_true,
    Bool.not_eq_true']
  constructor
  · intro hw x hx
    by_cases hm : x ∈ ss'.wr.take 2
    · exact (hw x hm).resolve_left (by simpa using hx)
    · rw [hf.1 x hm]; exact List.all_eq_true.mp h x hx
  · intro hall d _
    by_cases hd : d ∈ E
    · exact Or.inr (hall d hd)
    · exact Or.inl (by simpa using hd)

theorem nextF_EA (E : List String) {o : FOut} {l : Option (Option String)} {i : LinstrRM}
    (h : o.EA E) (hp : posAt E l (some i) o.toS = true) : (nextF E o i).EA E := by
  unfold nextF
  split
  · simp only [FOut.EA, FSt.toSSt_start, all_w64_start]
  · cases o with
    | ok F ea =>
        have hall : E.all (fun x => w64 E (F.toSSt.regs x)) = true := by
          simp only [posAt, FOut.toS, Bool.and_eq_true] at hp
          exact hp.1
        dsimp only
        cases hs : symStep i F.toSSt with
        | ok ss' g =>
            have hf := symStep_frame i hs
            simp only [stepOut_eq, FOut.EA, FSt.toSSt_upd hf]
            exact all_w64_frame hf hall
        | fail => trivial
        | unk => trivial
    | fail => trivial
    | unk => trivial

theorem nextF_toS (E : List String) (o : FOut) (i : LinstrRM) :
    (nextF E o i).toS = nextS o.toS i := by
  unfold nextF nextS
  split
  · simp only [FOut.toS, FSt.toSSt_start]
  · cases o with
    | ok F ea =>
        simp only [FOut.toS, symSnoc]
        cases h : symStep i F.toSSt with
        | ok ss' g => simp only [stepOut_eq, forgetG, FSt.toSSt_upd (symStep_frame i h)]
        | fail => rfl
        | unk => rfl
    | fail => rfl
    | unk => rfl

theorem posPassF_eq (E : List String) :
    ∀ (Ls : List (Option String)) (cs : List LinstrRM) (o : FOut), o.EA E →
      posPassF E Ls cs o = posPass E Ls cs o.toS
  | Ls, [], o, h => by rw [posPassF, posPass, posAtF_eq E _ _ h]
  | Ls, i :: cs, o, h => by
      rw [posPassF, posPass, posAtF_eq E _ _ h]
      cases hp : posAt E Ls.head? (some i) o.toS
      · rfl
      · rw [Bool.true_and, Bool.true_and, posPassF_eq E Ls.tail cs _ (nextF_EA E h hp),
          nextF_toS]

/-! ## The fast check -/

/-- **The fusion check in one pass**: the instruction-class conjunct of `fuseOKL`, and
    `posPassF` from the start state. -/
def fuseOKLFast (E : List String) (L : List (Option String)) (c : List LinstrRM) : Bool :=
  c.all (fun i => clsB i && wireOK i.1 && JasminLsemExportRewrites.mulxFree i)
    && posPassF E L c (.ok FSt.start true)

/-- **The single-pass fusion check equals `fuseOKL`**; compiled code runs `fuseOKLFast`. -/
@[csimp] theorem fuseOKL_eq_fast : @fuseOKL = @fuseOKLFast := by
  funext E L c
  unfold fuseOKL fuseOKLFast
  congr 1
  have h := posPass_drop E L c c.length 0 (by omega)
  rw [List.drop_zero, List.drop_zero, blk_zero] at h
  have hs : (FOut.ok FSt.start true).EA E := by
    simp only [FOut.EA, FSt.toSSt_start, all_w64_start]
  rw [List.range_eq_range', posPassF_eq E L c _ hs, FOut.toS, FSt.toSSt_start]
  exact h.symm

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
