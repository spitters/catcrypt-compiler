/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.RustSemantics.ToRustMS
public import HaxLean.HaxBackendPrelude
public import HaxLean.AeneasBackendPrelude

/-!
# The loops of the hax and Aeneas backends against the state-passing reading

The hax Lean backend prints a counted loop `for i in s..e` as `fold_range`, which runs its
body on `k` successive indices (`HaxBackend.foldRangeAux`). The Aeneas backend prints it as
`loop` over a body that steps the iterator `core.ops.range.Range Usize` with
`IteratorRange.next`. The state-passing reading `toRustMS` reads it as `loopS`.

* `ROk R x y` relates two `RustM` computations that return a value together, the two
  values related by `R`. `rOk_ok` and `rOk_bind` are its unit and composition, and
  `rOk_bind_same` composes two continuations of one computation.
* `AEnv.upd_apply`, `AVal.asW_w`, `ctr_asW` and `appExt_of_not_mem` evaluate the reading
  on a literal: a lookup, a word at its own width, the loop index, and a call to a name that
  no function of the extraction defines.
* `foldRangeAux_loopS`: when each step of the backend and each step of the reading are
  related, from accumulators related by `R`, so are the two loops.
* `next_usize` evaluates `IteratorRange.next` on a `usize` range, and `loop_range` states
  the Aeneas `loop` over a body that steps the range as `foldRangeAux`.

## Main results

* `ROk`, `rOk_ok`, `rOk_bind`, `rOk_bind_same`, `appExt_of_not_mem`
* `foldRangeAux_loopS`, `next_usize`, `loop_range`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std

/-- Two computations that return a value together, with values related by `R`. -/
def ROk {α β : Type} (R : α → β → Prop) (x : RustM α) (y : RustM β) : Prop :=
  (∀ a, x = .ok a → ∃ b, y = .ok b ∧ R a b) ∧ (∀ b, y = .ok b → ∃ a, x = .ok a ∧ R a b)

theorem rOk_ok {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    ROk R (.ok a) (.ok b) :=
  ⟨fun a' h' => by cases h'; exact ⟨b, rfl, h⟩, fun b' h' => by cases h'; exact ⟨a, rfl, h⟩⟩

theorem rOk_bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {x : RustM α} {y : RustM β} {f : α → RustM γ} {g : β → RustM δ} (h : ROk R x y)
    (hfg : ∀ a b, R a b → ROk S (f a) (g b)) : ROk S (x >>= f) (y >>= g) := by
  constructor
  · intro c hc
    obtain ⟨a, ha, hc⟩ := rustM_bind_ok hc
    obtain ⟨b, hb, hab⟩ := h.1 a ha
    obtain ⟨d, hd, hcd⟩ := (hfg a b hab).1 c hc
    exact ⟨d, by rw [hb]; exact hd, hcd⟩
  · intro d hd
    obtain ⟨b, hb, hd⟩ := rustM_bind_ok hd
    obtain ⟨a, ha, hab⟩ := h.2 b hb
    obtain ⟨c, hc, hcd⟩ := (hfg a b hab).2 d hd
    exact ⟨c, by rw [ha]; exact hc, hcd⟩

theorem rOk_bind_same {α γ δ : Type} {S : γ → δ → Prop} (x : RustM α)
    {f : α → RustM γ} {g : α → RustM δ} (h : ∀ a, ROk S (f a) (g a)) :
    ROk S (x >>= f) (x >>= g) := by
  cases x with
  | ok a => exact h a
  | fail e => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | div => exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

theorem bind_ok_right {α : Type} (x : RustM α) : x >>= RustM.ok = x := by
  cases x <;> rfl

theorem rOk_bind_right {α δ : Type} {S : α → δ → Prop} (x : RustM α)
    {g : α → RustM δ} (h : ∀ a, ROk S (.ok a) (g a)) : ROk S x (x >>= g) := by
  have := rOk_bind_same x (f := RustM.ok) h
  rwa [bind_ok_right] at this

theorem rOk_bind_left {α γ : Type} {S : γ → α → Prop} (x : RustM α)
    {f : α → RustM γ} (h : ∀ a, ROk S (f a) (.ok a)) : ROk S (x >>= f) x := by
  have := rOk_bind_same x (g := RustM.ok) h
  rwa [bind_ok_right] at this

/-! ## Evaluating the reading on a literal -/

theorem AEnv.upd_apply (ρ : AEnv) (x : String) (v : AVal) (y : String) :
    ρ.upd x v y = if y == x then some v else ρ y := rfl

theorem AVal.asW_w {ty : UScalarTy} (x : UScalar ty) : (AVal.w ty x).asW ty = .ok x := by
  simp [AVal.asW]

theorem ctr_asW (i : Nat) : (ctr i).asW .Usize = .ok ⟨BitVec.ofNat _ i⟩ := rfl

theorem AVal.asW_int {ty : UScalarTy} (n : Int) : (AVal.int n).asW ty = litA ty n := rfl

/-- A literal in range is read as the word `BitVec.ofNat _ n`, the form of a literal of
    both backends. -/
theorem litA_ofNat {ty : UScalarTy} {n : Nat} (h : n < 2 ^ ty.numBits) :
    litA ty (n : Int) = .ok ⟨BitVec.ofNat _ n⟩ := by
  have h' : (0 : Int) ≤ n ∧ (n : Int).toNat < 2 ^ ty.numBits := ⟨by omega, by simpa using h⟩
  rw [litA, dif_pos h']
  simp only [UScalar.ofNatCore, Int.toNat_natCast]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt h).symm

/-- A `usize` literal below `2 ^ 32` is in range at either platform width. -/
theorem usize_lt {n : Nat} (hn : n < 2 ^ 32) : n < 2 ^ UScalarTy.Usize.numBits := by
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    apply Nat.pow_le_pow_right (by decide)
    show 32 ≤ System.Platform.numBits
    rcases System.Platform.numBits_eq with h | h <;> omega
  omega

/-- A right shift by a word literal in range is `shiftRight` by its value. -/
theorem shr_uscalar_ofNat {ty tys : UScalarTy} (x : UScalar ty) {n : Nat}
    (h : n < 2 ^ tys.numBits) : x >>> (⟨BitVec.ofNat _ n⟩ : UScalar tys) = x.shiftRight n := by
  show x.shiftRight (BitVec.ofNat _ n).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A right shift by a nonnegative signed amount is `shiftRight` by its value. -/
theorem shr_iscalar {tys : IScalarTy} {tyx : UScalarTy} (x : UScalar tyx) (s : IScalar tys)
    {n : Nat} (h0 : 0 ≤ s.val) (hn : s.toNat = n) : x >>> s = x.shiftRight n := by
  show UScalar.shiftRight_IScalar x s = _
  rw [UScalar.shiftRight_IScalar, if_pos h0, hn]

theorem extStepS_of_ne {base : String → List AVal → RustM AVal} {fn : Hax.Ascent.ExtFn}
    {f : String} (h : f ≠ fn.name) : extStepS base fn f = base f := by
  funext vs
  simp [extStepS, h]

/-- A name no function of `fns` defines is read by `appRt`. -/
theorem appExt_of_not_mem {f : String} :
    ∀ {fns : List Hax.Ascent.ExtFn} (base : String → List AVal → RustM AVal),
      f ∉ fns.map Hax.Ascent.ExtFn.name → fns.foldl extStepS base f = base f
  | [], _, _ => rfl
  | fn :: fns, base, h => by
    rw [List.foldl_cons, appExt_of_not_mem (fns := fns) _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact extStepS_of_ne (fun e => h (by simp [e]))

/-! ## Loops -/

/-- **The hax backend's loop against the reading's loop.** -/
theorem foldRangeAux_loopS {α : Type} {ty : UScalarTy} (R : α → AEnv → Prop)
    (body : α → UScalar ty → RustM α) (step : Nat → AEnv → RustM AEnv)
    (hstep : ∀ i acc ρ, R acc ρ → ROk R (body acc ⟨BitVec.ofNat _ i⟩) (step i ρ)) :
    ∀ (k i : Nat) (acc : α) (ρ : AEnv), R acc ρ →
      ROk R (HaxBackend.foldRangeAux body k i acc) (loopS step k i ρ)
  | 0, _, _, _, h => rOk_ok h
  | k + 1, i, acc, ρ, h =>
    rOk_bind (hstep i acc ρ h) fun _ _ h' => foldRangeAux_loopS R body step hstep k (i + 1) _ _ h'

theorem uscalar_ofNat_val {ty : UScalarTy} (s : UScalar ty) :
    (⟨BitVec.ofNat _ s.val⟩ : UScalar ty) = s := by
  cases s
  simp [UScalar.val]

/-- `IteratorRange.next` on a `usize` range. -/
theorem next_usize (s n : Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({ start := s, «end» := n } : core.ops.range.Range Usize) =
      if s.val < n.val then
        .ok (some s, { start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n })
      else .ok (none, { start := s, «end» := n }) := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.iter.range.UScalarStep, bind_tc_ok]
  by_cases h : s.val < n.val
  · have hn : n.val < 2 ^ UScalarTy.Usize.numBits := n.bv.isLt
    have h1 : s.val + 1 < 2 ^ UScalarTy.Usize.numBits := by omega
    simp only [decide_eq_true h, if_true, core.iter.range.UScalarStep.forward_checked]
    have e1 : ∀ p, (UScalar.ofNatCore (ty := .Usize) 1 p).val = 1 := fun _ => rfl
    have e2 : UScalar.ofNatCore (ty := .Usize) (s.val + 1) h1 = ⟨BitVec.ofNat _ (s.val + 1)⟩ := by
      simp only [UScalar.ofNatCore]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt h1).symm
    simp only [e1, dif_pos h1, bind_tc_ok, if_pos h, e2]
  · simp [h]

/-- **The Aeneas backend's loop over a `usize` range**, for a body that steps the range and
    runs `f` on the current index, is the hax backend's `foldRangeAux f`. -/
theorem loop_range {α : Type}
    (body : core.ops.range.Range Usize × α →
      RustM (Aeneas.Std.ControlFlow (core.ops.range.Range Usize × α) α))
    (f : α → Usize → RustM α) (n : Usize)
    (hbody : ∀ (s : Usize) (acc : α), body ({ start := s, «end» := n }, acc) =
      if s.val < n.val then
        f acc s >>= fun acc' =>
          .ok (.cont ({ start := ⟨BitVec.ofNat _ (s.val + 1)⟩, «end» := n }, acc'))
      else .ok (.done acc)) :
    ∀ (k : Nat) (s : Usize) (acc : α), k = n.val - s.val →
      loop body ({ start := s, «end» := n }, acc) = HaxBackend.foldRangeAux f k s.val acc
  | 0, s, acc, hk => by
    rw [loop.eq_1, hbody, if_neg (by omega)]
    rfl
  | k + 1, s, acc, hk => by
    have hlt : s.val < n.val := by omega
    rw [loop.eq_1, hbody, if_pos hlt, HaxBackend.foldRangeAux, uscalar_ofNat_val]
    cases hf : f acc s with
    | ok acc' =>
      simp only [bind_tc_ok]
      have hs : (⟨BitVec.ofNat _ (s.val + 1)⟩ : Usize).val = s.val + 1 := by
        have hn := n.bv.isLt
        simp only [UScalar.val, BitVec.toNat_ofNat] at hlt hn ⊢
        exact Nat.mod_eq_of_lt (by omega)
      have := loop_range body f n hbody k ⟨BitVec.ofNat _ (s.val + 1)⟩ acc' (by omega)
      rw [hs] at this
      exact this
    | fail e => rfl
    | div => rfl

end CatCrypt.Hax.RustSemantics
