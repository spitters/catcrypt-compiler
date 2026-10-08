/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallX

@[expose] public section

set_option autoImplicit false

/-!
# The linked call to a vector kernel on the machine of mixed images

A caller runs on the scalar machine `aMachine`, its call to a kernel answered by an oracle
(`Callee.HaltsO`). The kernel is a block of scalar operations and vector instructions
followed by `vzeroupper` and `ret`. This module links the two on `VecImage.mixedMach`: the
program is the caller's instructions followed by the line program of the kernel, and the
state carries the vector registers, which the caller does not touch.

The callee of the link is vector-local: from an entry state, its return state does not
depend on the entry vector state (`VecLocalRun`). `kernelRunL` is the callee whose runs are
runs of the line program from every entry vector state, with one trace and one return
state; it is vector-local. On the entry states of a signature on which the scalar result
and the leakage of the block do not depend on the entry vector state (`VecLocalOn`), the
specification of `VecKernelSpec.kernelRun` is a specification of `kernelRunL`
(`calleeSpec_kernelRunL`).

## Main definitions

* `VecLocalRun`: every return state of a callee is the scalar state after the block, from
  every entry vector state.
* `kernelRunL`: the vector-local callee of a kernel block.
* `VecLocalOn`: the scalar state and the leakage after a block do not depend on the entry
  vector state, on the states of a precondition.

## Main results

* `calleeSpec_kernelRunL`: the specification of `kernelRun` is one of `kernelRunL` under
  `VecLocalOn`.
* `mixedMach_haltsC_link`: a run of the caller under the oracle of a vector-local callee
  at the end of the caller is, from every entry vector state, a run through calls on
  `mixedMach` of the caller followed by the line program of the kernel.
* `mixedDecode_items_lineBytes`: the bytes of well-formed caller positions followed by the
  bytes of the kernel decode on `mixedMach` to the caller's program followed by the line
  program of the kernel.
* `cpu_link`: a processor faithful to a lawful table runs the caller bytes followed by the
  kernel bytes, from every entry vector state, to the return state of the caller's run.
* `VecKernelCallee.cpu_link`: the same for a spec-carrying kernel whose callee is
  `kernelRun`, through `kernelRunL`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelMixedLink

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Mach x86Mach_mstep x86Mach_runBlock
  x86Act_ret x86Act_call)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO oracleAt)
open CatCrypt.Crypto.SecureCompilation.CT

variable {r : DoitRegime} {m : Mode}

/-! ## 1. Vector-local callees -/

/-- **A vector-local callee of a kernel block.** Every return state of `X` from an entry
    state `s` is the scalar state after the block followed by `vzeroupper`, from `s` and
    every entry vector state. -/
def VecLocalRun (r : DoitRegime) (m : Mode) (ops : List (JInstr 64 ⊕ VInstr))
    (X : CalleeRun) : Prop :=
  ∀ s t s', X s t s' → ∀ v : VState,
    ((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).1 = s'

/-- **The vector-local callee of a kernel block**: from every entry vector state, a run with
    leakage of the block followed by `vzeroupper` and `ret`, with the trace `t` and the
    scalar return state `s'`. -/
def kernelRunL (r : DoitRegime) (m : Mode) (ops : List (JInstr 64 ⊕ VInstr)) : CalleeRun :=
  fun s t s' => ∀ v : VState, ∃ v' : VState,
    (x86VecMach r m).RunL (fun _ _ => True) (lineProg (ops ++ [.inr .zeroUpper])) 0 (s, v) t
      (s', v')

/-- `kernelRunL` is vector-local. -/
theorem kernelRunL_vecLocal (ops : List (JInstr 64 ⊕ VInstr)) :
    VecLocalRun r m ops (kernelRunL r m ops) := by
  intro s t s' hX v
  obtain ⟨v', h⟩ := hX v
  obtain ⟨-, -, he⟩ := (runL_lineProg r m _ _ _ _ _).mp h
  exact (congrArg Prod.fst he).symm

/-- A run of `kernelRunL` is a run of `kernelRun`. -/
theorem kernelRun_of_kernelRunL {ops : List (JInstr 64 ⊕ VInstr)} {s : AState}
    {t : List CTLeak} {s' : AState} (h : kernelRunL r m ops s t s') :
    kernelRun r m ops s t s' := by
  obtain ⟨v', hv⟩ := h ⟨fun _ => 0, fun _ => 0⟩
  exact ⟨_, v', hv⟩

/-- **The scalar state and the leakage after the block `ops` do not depend on the entry
    vector state**, on the entry states that satisfy `pre`. -/
def VecLocalOn (r : DoitRegime) (m : Mode) (pre : AState → Prop)
    (ops : List (JInstr 64 ⊕ VInstr)) : Prop :=
  ∀ s, pre s → ∀ v w : VState,
    ((x86VecMach r m).runBlock (s, v) ops).1 = ((x86VecMach r m).runBlock (s, w) ops).1 ∧
      (x86VecMach r m).blockLeak (s, v) ops = (x86VecMach r m).blockLeak (s, w) ops

/-- **The specification of `kernelRun` is one of `kernelRunL`** when the scalar state and
    the leakage after the block do not depend on the entry vector state on the entry states
    of the signature. -/
theorem calleeSpec_kernelRunL {ops : List (JInstr 64 ⊕ VInstr)} {c : CalleeSig}
    (hX : CalleeSpec (kernelRun r m ops) c) (hloc : VecLocalOn r m c.pre ops) :
    CalleeSpec (kernelRunL r m ops) c := by
  refine ⟨?_, fun s t s' hp h => hX.rsp s t s' hp (kernelRun_of_kernelRunL h),
    fun s t s' hp h => hX.keep s t s' hp (kernelRun_of_kernelRunL h),
    fun s t s' hp h => hX.frame s t s' hp (kernelRun_of_kernelRunL h),
    fun s t s' hp h => hX.post s t s' hp (kernelRun_of_kernelRunL h),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h1 h2 hp hX₁ hX₂ =>
      hX.ct s₁ s₂ t₁ t₂ s₁' s₂' h1 h2 hp (kernelRun_of_kernelRunL hX₁)
        (kernelRun_of_kernelRunL hX₂)⟩
  intro s hpre
  obtain ⟨t, s', hk⟩ := hX.halts s hpre
  obtain ⟨v₀, hs', ht⟩ := (kernelRun_iff r m ops s t s').mp hk
  refine ⟨t, s', fun v => ⟨((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).2,
    ?_⟩⟩
  have hrun := (runL_lineProg r m (fun _ _ => True) (ops ++ [.inr .zeroUpper]) (s, v) _ _).mpr
    ⟨IsaMachine.blockOk_true _ _ _, rfl, rfl⟩
  have e1 : t = (x86VecMach r m).blockLeak (s, v) (ops ++ [.inr .zeroUpper]) := by
    rw [blockLeak_zeroUpper, ht, (hloc s hpre v₀ v).2]
  have e2 : (s', ((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).2)
      = (x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper]) := by
    refine Prod.ext ?_ rfl
    rw [runBlock_zeroUpper_fst, hs', (hloc s hpre v₀ v).1]
  rw [e1, e2]
  exact hrun

/-! ## 2. The link on the machine of mixed images -/

/-- The action of `x86VecMach` at an index of a program is its action there in the program
    with instructions appended. -/
theorem act_append_of_some {q ext : List (RInstr ⊕ VInstr)} {pc : Nat} {a : AState × VState}
    {x : MAct (JInstr 64 ⊕ VInstr)} (h : (x86VecMach r m).act q pc a = some x) :
    (x86VecMach r m).act (q ++ ext) pc a = some x := by
  have hlt : pc < q.length := by
    by_contra hn
    have hnone : q[pc]? = none := List.getElem?_eq_none (Nat.le_of_not_gt hn)
    simp [hnone] at h
  simpa [IsaMachine.withOps, List.getElem?_append_left hlt] using h

/-- A step of `x86VecMach` is a step of the program with instructions appended. -/
theorem mstep_append_of_some {q ext : List (RInstr ⊕ VInstr)} {pc : Nat} {a : AState × VState}
    {n : RInstrSemantics.Next (AState × VState)} (h : (x86VecMach r m).mstep q pc a = some n) :
    (x86VecMach r m).mstep (q ++ ext) pc a = some n := by
  unfold IsaMachine.mstep at h ⊢
  cases hact : (x86VecMach r m).act q pc a with
  | none => rw [hact] at h; cases h
  | some x => rw [act_append_of_some hact]; rw [hact] at h; exact h

/-- **The line program after a prefix runs its remaining block.** In `pre` followed by the
    line program of `done ++ post`, the run from the index of the first operation of `post`
    halts in the state after `post`. -/
theorem haltsC_lineProg_after (pre : List (RInstr ⊕ VInstr)) :
    ∀ (post done : List (JInstr 64 ⊕ VInstr)) (a : AState × VState),
      (x86VecMach r m).HaltsC (pre ++ lineProg (done ++ post)) (pre.length + done.length) a
        ((x86VecMach r m).runBlock a post)
  | [], done, a => by
    refine .ret ?_
    have hget : (pre ++ lineProg (done ++ []))[pre.length + done.length]? = some (.inl .ret) := by
      simp [lineProg]
    simp only [hget]
    rfl
  | o :: post, done, a => by
    have ih := haltsC_lineProg_after pre post (done ++ [o]) ((x86VecMach r m).exec a o)
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] at ih
    refine .go ?_ ih
    have hget : (pre ++ lineProg (done ++ o :: post))[pre.length + done.length]?
        = some (Sum.map RInstr.op id o) := by
      simp [lineProg]
    unfold IsaMachine.mstep
    simp only [hget]
    cases o <;> rfl

/-- The block fold of `x86Mach` is the fold of `aMachine.exec`. -/
theorem x86Mach_runBlock_foldl (ops : List (JInstr 64)) (s : AState) :
    (x86Mach r).runBlock s ops = ops.foldl aMachine.exec s := by
  rw [x86Mach_runBlock, DecodedCT.foldl_aMachine_exec]

/-- **The linked call to a vector kernel on `mixedMach`.** Let the caller `p` run from `pc`
    in `s` to `s'` under the oracle that answers a call to the index `p.length` by a
    vector-local callee `X` of the block `ops`. Then, from every entry vector state `v`,
    the caller followed by the line program of the block followed by `vzeroupper` runs
    through calls on `mixedMach` from `pc` in `(s, v)` to `(s', v')` for some `v'`. The
    vector state is changed by the kernel only. -/
theorem mixedMach_haltsC_link (A : VecAsm) {ops : List (JInstr 64 ⊕ VInstr)} {X : CalleeRun}
    (hX : VecLocalRun r m ops X) {p : List RInstr} {pc : Nat} {s s' : AState}
    (h : HaltsO aMachine (oracleAt p.length X) p pc s s') (v : VState) :
    ∃ v' : VState, (mixedMach A r m).HaltsC
      (p.map Sum.inl ++ lineProg (ops ++ [.inr .zeroUpper])) pc (s, v) (s', v') := by
  have hloc := x86Mach_actLocal r
  suffices H : ∀ v : VState, ∃ v' : VState, (x86VecMach r m).HaltsC
      (p.map Sum.inl ++ lineProg (ops ++ [.inr .zeroUpper])) pc (s, v) (s', v') by
    obtain ⟨v', hv⟩ := H v
    exact ⟨v', mixedMach_haltsC.mpr hv⟩
  induction h with
  | ret h =>
    intro v
    exact ⟨v, .ret (act_append_of_some
      ((IsaMachine.withOps_act_inl_eq_some hloc).mpr ⟨.ret, x86Act_ret.mpr h, rfl⟩))⟩
  | @go pc s₀ pc' s₁ s₂ h _ ih =>
    intro v
    obtain ⟨v', hv⟩ := ih v
    refine ⟨v', .go (mstep_append_of_some
      ((IsaMachine.withOps_mstep_inl_go hloc (a := (s₀, v)) (b := (s₁, v))).mpr ⟨?_, rfl⟩))
      hv⟩
    rw [x86Mach_mstep]
    exact h
  | @call pc t s₀ sc s'' h hc _ ih =>
    intro v
    obtain ⟨rfl, tr, hXr⟩ := hc
    have hs := hX _ _ _ hXr v
    obtain ⟨v', hv⟩ := ih ((x86VecMach r m).runBlock
      ((callOps (pc + 1)).foldl aMachine.exec s₀, v) (ops ++ [.inr .zeroUpper])).2
    refine ⟨v', .call (sc := (sc, ((x86VecMach r m).runBlock
        ((callOps (pc + 1)).foldl aMachine.exec s₀, v) (ops ++ [.inr .zeroUpper])).2))
      (act_append_of_some
      ((IsaMachine.withOps_act_inl_eq_some hloc).mpr ⟨.call _, x86Act_call.mpr h, rfl⟩))
      ?_ ?_⟩
    · rw [IsaMachine.withOps_callOps, IsaMachine.withOps_runBlock_inl, x86Mach_runBlock_foldl]
      have hl := haltsC_lineProg_after (r := r) (m := m) (p.map Sum.inl)
        (ops ++ [.inr .zeroUpper]) [] ((callOps (pc + 1)).foldl aMachine.exec s₀, v)
      simp only [List.nil_append, List.length_map, List.length_nil, Nat.add_zero] at hl
      rw [← hs]
      exact hl
    · rw [IsaMachine.withOps_retOps, IsaMachine.withOps_runBlock_inl, x86Mach_runBlock_foldl]
      exact hv

/-! ## 3. The bytes of a caller followed by the bytes of a kernel -/

theorem mixedBytes_append (a b : List MixedItem) :
    mixedBytes (a ++ b) = mixedBytes a ++ mixedBytes b := by
  simp [mixedBytes]

theorem mixedBytes_ofScalar (items : List Item) :
    mixedBytes (items.map MixedItem.ofScalar) = itemBytes items := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    simp only [mixedBytes, itemBytes, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem mixedLayout_append (a b : List MixedItem) :
    ∀ off, mixedLayout off (a ++ b)
      = mixedLayout off a ++ mixedLayout (off + (mixedBytes a).length) b := by
  induction a with
  | nil => intro off; simp [mixedBytes, mixedLayout]
  | cons it rest ih =>
    intro off
    have hbs : (mixedBytes (it :: rest)).length = it.bytes.length + (mixedBytes rest).length := by
      simp [mixedBytes]
    cases hdec : it.dec with
    | none => simp [mixedLayout, hdec, ih, hbs, Nat.add_assoc]
    | some x => simp [mixedLayout, hdec, ih, hbs, Nat.add_assoc]

theorem mixedLayout_ofScalar (items : List Item) :
    ∀ off, mixedLayout off (items.map MixedItem.ofScalar) = (layoutAt off items).map liftLayout := by
  induction items with
  | nil => intro off; rfl
  | cons it rest ih =>
    intro off
    cases hdec : it.dec with
    | none => simp [mixedLayout, layoutAt, MixedItem.ofScalar, hdec, ih]
    | some x => simp [mixedLayout, layoutAt, MixedItem.ofScalar, hdec, ih, liftLayout]

/-- Resolution of the layout `ys ++ zs` is the resolution of `ys` followed by that of
    `zs`. -/
theorem mixedResolve_append (xs : List (Nat × Nat × (DInstr ⊕ VInstr))) :
    ∀ (ys zs : List (Nat × Nat × (DInstr ⊕ VInstr))) (a b : List (RInstr ⊕ VInstr)),
      mixedResolve xs ys = some a → mixedResolve xs zs = some b →
        mixedResolve xs (ys ++ zs) = some (a ++ b) := by
  intro ys
  induction ys with
  | nil => intro zs a b ha hb; simp only [mixedResolve, Option.some.injEq] at ha; subst ha; exact hb
  | cons y rest ih =>
    intro zs a b ha hb
    obtain ⟨st, e, x⟩ := y
    rcases x with x | v
    · cases x with
      | jcc cc d =>
        simp only [List.cons_append, mixedResolve] at ha ⊢
        split at ha
        · obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
          rw [ih zs a' b ha' hb]
          rfl
        · cases ha
      | call d =>
        simp only [List.cons_append, mixedResolve] at ha ⊢
        split at ha
        · obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
          rw [ih zs a' b ha' hb]
          rfl
        · cases ha
      | _ =>
        simp only [List.cons_append, mixedResolve] at ha ⊢
        obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
        rw [ih zs a' b ha' hb]
        rfl
    · simp only [List.cons_append, mixedResolve] at ha ⊢
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [ih zs a' b ha' hb]
      rfl

/-- Resolution of a lifted scalar layout against a mixed layout is scalar resolution against
    any scalar layout with the same start offsets. -/
theorem mixedResolve_liftLayout_of_starts (xs : List (Nat × Nat × (DInstr ⊕ VInstr)))
    (xs' : List (Nat × Nat × DInstr)) (hst : xs.map (·.1) = xs'.map (·.1)) :
    ∀ ys : List (Nat × Nat × DInstr),
      mixedResolve xs (ys.map liftLayout) = (resolveAll xs' ys).map (List.map Sum.inl) := by
  have hf : ∀ k : Int, xs.findIdx? (fun y => decide ((y.1 : Int) = k))
      = xs'.findIdx? (fun y => decide ((y.1 : Int) = k)) := by
    intro k
    have h1 : xs.findIdx? (fun y => decide ((y.1 : Int) = k))
        = (xs.map (·.1)).findIdx? (fun a : Nat => decide ((a : Int) = k)) := by
      rw [List.findIdx?_map]; rfl
    have h2 : xs'.findIdx? (fun y => decide ((y.1 : Int) = k))
        = (xs'.map (·.1)).findIdx? (fun a : Nat => decide ((a : Int) = k)) := by
      rw [List.findIdx?_map]; rfl
    rw [h1, h2, hst]
  intro ys
  induction ys with
  | nil => rfl
  | cons y rest ih =>
    obtain ⟨s, e, x⟩ := y
    cases x with
    | op i =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs' rest <;> rfl
    | ret =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs' rest <;> rfl
    | push r =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs' rest <;> rfl
    | pop r =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih]
      cases resolveAll xs' rest <;> rfl
    | jcc cc d =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih, hf]
      cases xs'.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
      | none => rfl
      | some j => cases resolveAll xs' rest <;> rfl
    | call d =>
      simp only [List.map_cons, liftLayout, mixedResolve, resolveAll, ih, hf]
      cases xs'.findIdx? (fun y => decide ((y.1 : Int) = (e : Int) + d)) with
      | none => rfl
      | some j => cases resolveAll xs' rest <;> rfl

/-- The layout of the positions of a block followed by `ret` starts at its offset. -/
theorem mixedLayout_lineItems_head (A : VecAsm) (enc : JInstr 64 → List (BitVec 8))
    (ops : List (JInstr 64 ⊕ VInstr)) (off : Nat) :
    ∃ e x tl, mixedLayout off (mixedItems A (lineItems enc ops)) = (off, e, x) :: tl := by
  cases ops with
  | nil => simp [mixedItems, lineItems, mixedLayout, MixedItem.ofScalar, mkRet]
  | cons o ops =>
    cases o <;> simp [mixedItems, lineItems, mixedLayout, MixedItem.ofScalar, scalarItem,
      VecAsm.item]

/-- The layout of the positions of a block followed by `ret` resolves to its line program,
    against every layout. -/
theorem mixedResolve_lineItems (A : VecAsm) (enc : JInstr 64 → List (BitVec 8))
    (xs : List (Nat × Nat × (DInstr ⊕ VInstr))) :
    ∀ (ops : List (JInstr 64 ⊕ VInstr)) (off : Nat),
      mixedResolve xs (mixedLayout off (mixedItems A (lineItems enc ops))) = some (lineProg ops)
  | [], off => by
    simp [mixedItems, lineItems, mixedLayout, MixedItem.ofScalar, mkRet, mixedResolve, lineProg]
  | o :: ops, off => by
    have ih := mixedResolve_lineItems A enc xs ops
    cases o with
    | inl i =>
      simp only [mixedItems, lineItems, List.map_cons, List.cons_append] at ih ⊢
      show (mixedResolve xs (mixedLayout _ _)).map (Sum.inl (.op i) :: ·) = _
      rw [ih]
      rfl
    | inr v =>
      simp only [mixedItems, lineItems, List.map_cons, List.cons_append] at ih ⊢
      show (mixedResolve xs (mixedLayout _ _)).map (Sum.inr v :: ·) = _
      rw [ih]
      rfl

/-- **The bytes of a caller followed by the bytes of a kernel decode to the caller's program
    followed by the line program of the kernel.** Let the caller positions `items` be well
    formed and resolve to `prog` in front of every layout that starts at the end of their
    bytes, let the table be lawful and encode the vector instructions of the block, and let
    the position of each scalar operation of the block be well formed. Then `mixedMach`
    decodes the caller bytes followed by `lineBytes A enc ops` to `prog` followed by the
    line program of the block followed by `vzeroupper`. -/
theorem mixedDecode_items_lineBytes {A : VecAsm} (hA : A.Lawful) {items : List Item}
    (hok : ∀ it ∈ items, ItemOK it) {prog : List RInstr}
    (hres : ∀ e x tl, resolveAll (layoutAt 0 items ++ ((itemBytes items).length, e, x) :: tl)
      (layoutAt 0 items) = some prog)
    (enc : JInstr 64 → List (BitVec 8)) {ops : List (JInstr 64 ⊕ VInstr)}
    (henc : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) (hbe : BlockEncodable A ops) :
    mixedDecode A (itemBytes items ++ lineBytes A enc ops)
      = some (prog.map Sum.inl ++ lineProg (ops ++ [.inr .zeroUpper])) := by
  set K := ops ++ [Sum.inr VInstr.zeroUpper] with hK
  set CI := mixedItems A (lineItems enc K) with hCI
  have hbytes : itemBytes items ++ lineBytes A enc ops
      = mixedBytes (items.map MixedItem.ofScalar ++ CI) := by
    rw [mixedBytes_append, mixedBytes_ofScalar, hCI, mixedBytes_mixedItems]
    rfl
  have hokAll : ∀ it ∈ items.map MixedItem.ofScalar ++ CI, MixedItemOK A it := by
    intro it hit
    rcases List.mem_append.mp hit with h | h
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      exact MixedItemOK.ofScalar A (hok i hi)
    · simp only [hCI, mixedItems, List.mem_map] at h
      obtain ⟨src, hsrc, rfl⟩ := h
      cases src with
      | inl i =>
        exact MixedItemOK.ofScalar A
          (lineItems_ok (fun i hi => henc i (by simpa [hK] using hi)) i hsrc)
      | inr v => exact hA.item_ok (lineItems_encodable hbe v hsrc)
  have hfuel : (mixedLayout 0 (items.map MixedItem.ofScalar ++ CI)).length
      ≤ (mixedBytes (items.map MixedItem.ofScalar ++ CI)).length := by
    rw [mixedLayout_length]; exact mixedCount_le_bytes A _ hokAll
  rw [hbytes, mixedDecode, mixedStream_items A _ hokAll _ 0 hfuel, Option.bind_some,
    mixedLayout_append, mixedLayout_ofScalar, mixedBytes_ofScalar, Nat.zero_add]
  obtain ⟨e, x, tl, htl⟩ := mixedLayout_lineItems_head A enc K (itemBytes items).length
  rw [← hCI] at htl
  rw [htl]
  refine mixedResolve_append _ _ _ _ _ ?_ ?_
  · rw [mixedResolve_liftLayout_of_starts _
      (layoutAt 0 items ++ ((itemBytes items).length, e, DInstr.ret) ::
        tl.map (fun y => (y.1, y.2.1, DInstr.ret))) ?_, hres]
    · rfl
    · simp [liftLayout, Function.comp_def]
  · rw [← htl, hCI]
    exact mixedResolve_lineItems A enc _ K _

/-! ## 4. The processor on the bytes of a caller and a kernel -/

/-- **A faithful processor runs the linked caller and kernel.** Let the caller positions be
    well formed and resolve to `prog` in front of every layout starting at the end of their
    bytes, and let `prog` run from index `0` in `s` to `s'` under the oracle that answers a
    call to `prog.length` by a vector-local callee of the block `ops`. For a lawful table
    that encodes the vector instructions of the block, well-formed positions of its scalar
    operations, and a processor faithful to that table, the processor runs the caller bytes
    followed by `lineBytes A enc ops` from `(s, v)` to `(s', v')`, for every entry vector
    state `v` and some `v'`. -/
theorem cpu_link {A : VecAsm} {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}
    (hA : A.Lawful) (hF : A.Faithful r m cpu) {items : List Item}
    (hok : ∀ it ∈ items, ItemOK it) {prog : List RInstr}
    (hres : ∀ e x tl, resolveAll (layoutAt 0 items ++ ((itemBytes items).length, e, x) :: tl)
      (layoutAt 0 items) = some prog)
    (enc : JInstr 64 → List (BitVec 8)) {ops : List (JInstr 64 ⊕ VInstr)}
    (henc : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) (hbe : BlockEncodable A ops)
    {X : CalleeRun} (hX : VecLocalRun r m ops X) {s s' : AState}
    (h : HaltsO aMachine (oracleAt prog.length X) prog 0 s s') (v : VState) :
    ∃ v' : VState, cpu (itemBytes items ++ lineBytes A enc ops) (s, v) (s', v') := by
  obtain ⟨v', hv⟩ := mixedMach_haltsC_link A hX h v
  exact ⟨v', (VecAsm.faithful_iff_mixedMach.mp hF) _ _ _ _
    (mixedDecode_items_lineBytes hA hok hres enc henc hbe) hv⟩

/-- **The vector-local callee of a spec-carrying kernel meets its signature**, when the
    callee of the record is `kernelRun` of its block and the block has a scalar result and a
    leakage independent of the entry vector state on the entry states of the signature. -/
theorem VecKernelCallee.spec_local {sig : CalleeSig} (k : VecKernelCallee r m sig)
    (hrun : k.run = kernelRun r m k.ops) (hloc : VecLocalOn r m sig.pre k.ops) :
    CalleeSpec (kernelRunL r m k.ops) sig :=
  calleeSpec_kernelRunL (hrun ▸ k.spec) hloc

/-- **A faithful processor runs a caller linked with a spec-carrying kernel**: the statement
    of `cpu_link` for the block of the record, the scalar encoder `frameEnc` and the callee
    `kernelRunL`. -/
theorem VecKernelCallee.cpu_link {sig : CalleeSig} (k : VecKernelCallee r m sig) {A : VecAsm}
    {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}
    (hA : A.Lawful) (hF : A.Faithful r m cpu) (hbe : BlockEncodable A k.ops)
    (henc : ∀ i, Sum.inl i ∈ k.ops → ItemOK (scalarItem frameEnc i)) {items : List Item}
    (hok : ∀ it ∈ items, ItemOK it) {prog : List RInstr}
    (hres : ∀ e x tl, resolveAll (layoutAt 0 items ++ ((itemBytes items).length, e, x) :: tl)
      (layoutAt 0 items) = some prog) {s s' : AState}
    (h : HaltsO aMachine (oracleAt prog.length (kernelRunL r m k.ops)) prog 0 s s')
    (v : VState) :
    ∃ v' : VState, cpu (itemBytes items ++ lineBytes A frameEnc k.ops) (s, v) (s', v') :=
  VecKernelMixedLink.cpu_link hA hF hok hres frameEnc henc hbe (kernelRunL_vecLocal k.ops) h v

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelMixedLink
