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
justifies. Symbolic words share their subterms in memory, and the comparisons of `siteOK`
run through `decEqTermP`, which tests pointer equality before it compares two subterms.

The equality `fuseOKL_eq_fast` is registered with `@[csimp]`, so compiled code runs
`fuseOKLFast` whenever it calls `fuseOKL`; the definition `fuseOKL` and its theorems are
unchanged.

## Main definitions

* `FSt` — a symbolic state with its registers and arrays in hash maps.
* `decEqTermP` — equality of symbolic words with a pointer-equality test at each subterm.
* `posPass` — the per-position checks from the current position on, in one forward pass.
* `posPassF` — `posPass` over the hash-map state.
* `fuseOKLFast` — the fusion check in one forward pass over the body.

## Main results

* `symStep_frame` — a symbolic step changes only the first two written registers and array
  names.
* `FSt.toSSt_upd` — the hash-map state after a step describes the state `symStep` returns.
* `posPass_drop` — the forward pass from position `k` equals the per-position checks from `k`.
* `posPassF_eq` — `posPassF` equals `posPass` on the described state.
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
  simp only [SSt.setR, List.take_succ_cons, List.mem_cons, not_or] at hr ⊢
  exact if_neg hr.1

theorem frameT_setR_setR (ss : SSt) (d e : String) (t u : STerm) :
    FrameT ss ((ss.setR d t).setR e u) := by
  refine ⟨fun r hr => ?_, fun _ _ => rfl⟩
  simp only [SSt.setR, List.take_succ_cons, List.mem_cons, not_or] at hr ⊢
  rw [if_neg hr.1, if_neg hr.2.1]

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

/-- A symbolic state whose registers and arrays are hash maps; an absent register or array
    name holds its start value. The remaining fields are those of `SSt`. -/
structure FSt where
  /-- The symbolic words of the registers written. -/
  regs : Std.HashMap String STerm
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
  ⟨fun r => F.regs.getD r (.reg r), fun r => F.arrs.getD r (.cell r), F.zf, F.wr, F.awr,
    F.cf, F.of⟩

/-- The hash-map state at the start of a block. -/
def FSt.start : FSt := ⟨∅, ∅, .init, [], [], .cin false, .cin true⟩

/-- The hash-map state after a step to `ss'`: the first two written registers and array names
    of `ss'` take their values in `ss'`, the other fields are those of `ss'`. -/
def FSt.upd (F : FSt) (ss' : SSt) : FSt :=
  ⟨(ss'.wr.take 2).foldl (fun m d => m.insert d (ss'.regs d)) F.regs,
    (ss'.awr.take 2).foldl (fun m d => m.insert d (ss'.arrs d)) F.arrs,
    ss'.zf, ss'.wr, ss'.awr, ss'.cf, ss'.of⟩

theorem FSt.toSSt_start : FSt.start.toSSt = SSt.start := by
  simp only [FSt.toSSt, FSt.start, SSt.start, Std.HashMap.getD_empty]

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

/-- **The hash-map state after a step describes the state the step returns.** -/
theorem FSt.toSSt_upd {F : FSt} {ss' : SSt} (h : FrameT F.toSSt ss') :
    (F.upd ss').toSSt = ss' := by
  obtain ⟨hr, ha⟩ := h
  obtain ⟨regs, arrs, zf, wr, awr, cf, of⟩ := ss'
  simp only [FSt.toSSt, FSt.upd, SSt.mk.injEq, and_true]
  refine ⟨funext fun r => ?_, funext fun r => ?_⟩
  · rw [getD_foldl_insert]
    split
    · rfl
    · next hn => exact (hr r hn).symm
  · rw [getD_foldl_insert]
    split
    · rfl
    · next hn => exact (ha r hn).symm

/-! ## Equality of symbolic words with a pointer-equality test -/

mutual
/-- Equality of symbolic words, decided structurally with a pointer-equality test
    (`withPtrEqDecEq`) before each comparison of two subterms, so that subterms shared in
    memory are compared in constant time. -/
def decEqTermP : (a b : STerm) → Decidable (a = b)
  | .immAt n x, .immAt n' x' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      decidable_of_iff (n = n' ∧ x = x') (by simp)
  | .bin m x y, .bin m' x' y' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      decidable_of_iff (m = m' ∧ x = x' ∧ y = y') (by simp)
  | .un m x, .un m' x' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      decidable_of_iff (m = m' ∧ x = x') (by simp)
  | .shImm m k x, .shImm m' k' x' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      decidable_of_iff (m = m' ∧ k = k' ∧ x = x') (by simp)
  | .aget a w n i, .aget a' w' n' i' =>
      have : Decidable (a = a') := withPtrEqDecEq a a' (fun _ => decEqArrP a a')
      have : Decidable (i = i') := withPtrEqDecEq i i' (fun _ => decEqTermP i i')
      decidable_of_iff (a = a' ∧ w = w' ∧ n = n' ∧ i = i') (by simp)
  | .aluF op o x y z, .aluF op' o' x' y' z' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      have : Decidable (z = z') := withPtrEqDecEq z z' (fun _ => decEqTermP z z')
      decidable_of_iff (op = op' ∧ o = o' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
  | .carryW op x y z, .carryW op' x' y' z' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      have : Decidable (z = z') := withPtrEqDecEq z z' (fun _ => decEqTermP z z')
      decidable_of_iff (op = op' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
  | .carryF op o x y z, .carryF op' o' x' y' z' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      have : Decidable (z = z') := withPtrEqDecEq z z' (fun _ => decEqTermP z z')
      decidable_of_iff (op = op' ∧ o = o' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
  | .mulx h x y, .mulx h' x' y' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      decidable_of_iff (h = h' ∧ x = x' ∧ y = y') (by simp)
  | .cout s x y z, .cout s' x' y' z' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      have : Decidable (z = z') := withPtrEqDecEq z z' (fun _ => decEqTermP z z')
      decidable_of_iff (s = s' ∧ x = x' ∧ y = y' ∧ z = z') (by simp)
  | .sel x y z, .sel x' y' z' =>
      have : Decidable (x = x') := withPtrEqDecEq x x' (fun _ => decEqTermP x x')
      have : Decidable (y = y') := withPtrEqDecEq y y' (fun _ => decEqTermP y y')
      have : Decidable (z = z') := withPtrEqDecEq z z' (fun _ => decEqTermP z z')
      decidable_of_iff (x = x' ∧ y = y' ∧ z = z') (by simp)
  | a, b => decEq a b

/-- Equality of symbolic arrays, decided structurally with a pointer-equality test before
    each comparison of two subterms. -/
def decEqArrP : (a b : SArr) → Decidable (a = b)
  | .aset a w n i v, .aset a' w' n' i' v' =>
      have : Decidable (a = a') := withPtrEqDecEq a a' (fun _ => decEqArrP a a')
      have : Decidable (i = i') := withPtrEqDecEq i i' (fun _ => decEqTermP i i')
      have : Decidable (v = v') := withPtrEqDecEq v v' (fun _ => decEqTermP v v')
      decidable_of_iff (a = a' ∧ w = w' ∧ n = n' ∧ i = i' ∧ v = v') (by simp)
  | a, b => decEq a b
end

/-- The Boolean equality of symbolic words through `decEqTermP`. -/
def termEqP (a b : STerm) : Bool := @decide (a = b) (decEqTermP a b)

theorem termEqP_eq (a b : STerm) : termEqP a b = (a == b) := by
  unfold termEqP
  exact congrArg (@decide (a = b)) (Subsingleton.elim _ _)

/-- `mulLoB` with the comparisons of `termEqP`. -/
def mulLoBF (dt a b : STerm) : Bool :=
  termEqP dt (.bin "MUL" a b) || termEqP dt (.bin "MUL" b a) || termEqP dt (.mulx false a b)

theorem mulLoBF_eq : mulLoBF = mulLoB := by
  funext dt a b
  simp only [mulLoBF, mulLoB, termEqP_eq]

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

/-- A symbolic outcome over the hash-map state, guards dropped. -/
inductive FOut where
  | ok (F : FSt)
  | fail
  | unk

/-- The symbolic outcome an `FOut` describes. -/
def FOut.toS : FOut → SOut
  | .ok F => .ok F.toSSt []
  | .fail => .fail
  | .unk => .unk

/-- `posAt` over the hash-map state. -/
def posAtF (E : List String) (l : Option (Option String)) (ci : Option LinstrRM) (o : FOut) :
    Bool :=
  match o with
  | .ok F =>
      E.all (fun x => w64 E (F.regs.getD x (.reg x))) &&
        (match l with
         | some (some d) => ci.any (fun i => siteOKF E d i F.toSSt)
         | _ => true)
  | .fail => true
  | .unk => false

/-- `nextS` over the hash-map state: the step runs `symStep` on the described state and
    updates the maps by `FSt.upd`. -/
def nextF (o : FOut) (i : LinstrRM) : FOut :=
  if isCtlB i then .ok FSt.start else
    match o with
    | .ok F =>
        match symStep i F.toSSt with
        | .ok ss' _ => .ok (F.upd ss')
        | .fail => .fail
        | .unk => .unk
    | .fail => .fail
    | .unk => .unk

/-- `posPass` over the hash-map state. -/
def posPassF (E : List String) : List (Option String) → List LinstrRM → FOut → Bool
  | Ls, [], o => posAtF E Ls.head? none o
  | Ls, i :: cs, o => posAtF E Ls.head? (some i) o && posPassF E Ls.tail cs (nextF o i)

theorem posAtF_eq (E : List String) (l : Option (Option String)) (ci : Option LinstrRM)
    (o : FOut) : posAtF E l ci o = posAt E l ci o.toS := by
  cases o with
  | ok F => simp only [posAtF, posAt, FOut.toS, siteOKF_eq]; rfl
  | fail => rfl
  | unk => rfl

theorem nextF_toS (o : FOut) (i : LinstrRM) : (nextF o i).toS = nextS o.toS i := by
  unfold nextF nextS
  split
  · simp only [FOut.toS, FSt.toSSt_start]
  · cases o with
    | ok F =>
        simp only [FOut.toS, symSnoc]
        cases h : symStep i F.toSSt with
        | ok ss' g => simp only [forgetG, FSt.toSSt_upd (symStep_frame i h)]
        | fail => rfl
        | unk => rfl
    | fail => rfl
    | unk => rfl

theorem posPassF_eq (E : List String) :
    ∀ (Ls : List (Option String)) (cs : List LinstrRM) (o : FOut),
      posPassF E Ls cs o = posPass E Ls cs o.toS
  | Ls, [], o => by rw [posPassF, posPass, posAtF_eq]
  | Ls, i :: cs, o => by
      rw [posPassF, posPass, posAtF_eq, posPassF_eq E Ls.tail cs (nextF o i), nextF_toS]

/-! ## The fast check -/

/-- **The fusion check in one pass**: the instruction-class conjunct of `fuseOKL`, and
    `posPassF` from the start state. -/
def fuseOKLFast (E : List String) (L : List (Option String)) (c : List LinstrRM) : Bool :=
  c.all (fun i => clsB i && wireOK i.1 && JasminLsemExportRewrites.mulxFree i)
    && posPassF E L c (.ok FSt.start)

/-- **The single-pass fusion check equals `fuseOKL`**; compiled code runs `fuseOKLFast`. -/
@[csimp] theorem fuseOKL_eq_fast : @fuseOKL = @fuseOKLFast := by
  funext E L c
  unfold fuseOKL fuseOKLFast
  congr 1
  have h := posPass_drop E L c c.length 0 (by omega)
  rw [List.drop_zero, List.drop_zero, blk_zero] at h
  rw [List.range_eq_range', posPassF_eq, FOut.toS, FSt.toSSt_start]
  exact h.symm

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
