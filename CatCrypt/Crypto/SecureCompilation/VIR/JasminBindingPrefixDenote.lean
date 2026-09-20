/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

@[expose] public section

set_option autoImplicit false

/-!
# Binding registers and truncated denotations

The straight-line `lsem` faithfulness statements (`ComLsemExportFaithful` and the
tower below it) constrain one register: `comRetReg`, the destination of the last
binding. A multi-output kernel reads its other outputs off the destination
registers of earlier bindings, which those statements say nothing about.

This module states and proves what an earlier binding's register holds: the
denotation of the source program truncated at that binding. `comPrefix com k` is
that truncation — the first `k + 1` bindings of `com`, returning the value bound
by binding `k` — and `straightOps_binding_denote` is the register-level reading
of it, for the uniform-`regArith` fragment the existing faithfulness tower covers.

The supporting frame results are about the linear machine's register map:
`lsemStep_lvm_of_ne` for a single instruction, `lsemStraight_lvm_of_dsts` for a
run, and `straightOps_lvm_frame` for an emitted chain. The last says an emitted
chain rooted at depth `d` writes only `regName` slots at depth `d` and above, so
a binding register survives the rest of the chain.

## Main definitions

* `comBindingTy` — the type of a `Com`'s `k`-th binding.
* `comPrefix` — the `Com` truncated at binding `k`.
* `LvmFrame` — the register map outside a `regName` block is unchanged.
* `epilogueOps` — the ABI epilogue's instruction list at `LinstrR`.

## Main results

* `comPrefix_denote_zero`, `comPrefix_denote_succ` — the truncation's denotation.
* `uniformRegArith_bindingTy` — every binding of the fragment is `.reg w`.
* `lsemStep_lvm_of_ne`, `lsemStraight_lvm_of_dsts` — register-map frames.
* `straightOps_lvm_frame` — an emitted chain writes only its own depth block.
* `straightOps_binding_denote` — binding `k`'s register holds
  `(comPrefix com k).denote V`.
* `comToLprog_lsem_binding` — the same, from the encoded argument valuation.
* `buildEpilogue_single_store_value` — the one-target epilogue stores the
  designated binding's register value into `[R14 + off]`.
* `buildEpilogue_dsts` — the epilogue writes only `R14`, `R15` and the map's
  `[R14 + off]` cells.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-! ## 1. The truncation of a `Com` at a binding -/

/-- The type of the `k`-th `.var` binding of a `Com`, and the `Com`'s own result
    type when `k` is at or past the number of bindings. -/
def comBindingTy : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat → JasminTy
  | _, t, .ret _, _ => t
  | _, _, .var (t := u) _ _, 0 => u
  | _, _, .var _ body, k + 1 => comBindingTy body k

/-- The `Com` truncated at binding `k`: the first `k + 1` bindings of `com`,
    returning the value bound by binding `k`. A `.ret` is returned unchanged. -/
def comPrefix : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (com : Com jasminDialect Γ t) → (k : Nat) → Com jasminDialect Γ (comBindingTy com k)
  | _, _, .ret v, _ => .ret v
  | _, _, .var e _, 0 => .var e (.ret (Ctxt.Var.here))
  | _, _, .var e body, k + 1 => .var e (comPrefix body k)

/-- The truncation at binding `0` denotes the head expression. -/
theorem comPrefix_denote_zero {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (comPrefix (Com.var e body) 0).denote V = e.denote V := rfl

/-- The truncation at binding `k + 1` peels the head binding. -/
theorem comPrefix_denote_succ {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) (k : Nat)
    (V : Ctxt.Valuation Γ) :
    (comPrefix (Com.var e body) (k + 1)).denote V
      = (comPrefix body k).denote (V.extend (e.denote V)) := rfl

/-- Every binding of a uniform-`regArith` program has type `.reg w`. -/
theorem uniformRegArith_bindingTy {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) :
    ∀ {k : Nat}, k < comLen com → comBindingTy com k = .reg w := by
  induction hcom with
  | ret v => intro k hk; simp [comLen] at hk
  | var bop heq args hbody ih =>
      intro k hk
      cases k with
      | zero => rfl
      | succ k => exact ih (by simpa [comLen] using hk)

/-! ## 2. Register-map frames for the linear machine -/

/-- The register map outside a `regName` block: `s'` reads as `s` at every name
    that is not `regName k` for some `k ≥ d`. -/
def LvmFrame {w : Nat} (d : Nat) (s s' : Lstate w) : Prop :=
  ∀ r : String, (∀ k, d ≤ k → r ≠ regName k) → s'.lvm r = s.lvm r

/-- A successful step of a single-destination `Lopn` leaves every other register
    unchanged. `STOREIDX` writes memory only, so it too leaves the register map
    fixed away from its nominal destination. -/
theorem lsemStep_lvm_of_ne {w : Nat} (dst opn : String) (srcs : List LOperand)
    (s s' : Lstate w) (h : lsemStep (.Lopn [.reg dst] opn srcs) s = some s')
    (r : String) (hr : r ≠ dst) : s'.lvm r = s.lvm r := by
  have key : ∀ v : BitVec w, ((s.setReg dst v).nextPc).lvm r = s.lvm r := by
    intro v; simp [Lstate.setReg, hr]
  have gen : ∀ srcs' : List LOperand,
      lsemStep (.Lopn [.reg dst] opn srcs') s = some s' → s'.lvm r = s.lvm r := by
    intro srcs' h'
    match srcs' with
    | [] =>
        simp only [lsemStep] at h'
        split at h'
        · cases h'; exact key _
        · exact absurd h' (by simp)
    | .reg n :: rest =>
        simp only [lsemStep] at h'
        split at h'
        · cases h'; exact key _
        · exact absurd h' (by simp)
    | .imm n :: rest =>
        simp only [lsemStep] at h'
        split at h'
        · cases h'; exact key _
        · exact absurd h' (by simp)
    | .arr b o :: rest =>
        simp only [lsemStep] at h'
        split at h'
        · cases h'; exact key _
        · exact absurd h' (by simp)
    | .arrIdx base idx scale :: rest =>
        simp only [lsemStep] at h'
        split at h'
        · cases h'; exact key _
        · split at h'
          · split at h'
            · cases h'; rfl
            · exact absurd h' (by simp)
          · split at h'
            · cases h'; exact key _
            · exact absurd h' (by simp)
  exact gen srcs h

/-- A successful run of single-destination `Lopn`s whose destinations all satisfy
    `P` leaves every register outside `P` unchanged. -/
theorem lsemStraight_lvm_of_dsts {w : Nat} (P : String → Prop) :
    ∀ (is : List LinstrR) (s s' : Lstate w),
      (∀ i ∈ is, ∃ dst opn srcs, i = .Lopn [.reg dst] opn srcs ∧ P dst) →
      lsemStraight is s = some s' →
      ∀ r : String, ¬ P r → s'.lvm r = s.lvm r := by
  intro is
  induction is with
  | nil => intro s s' _ h r _; cases h; rfl
  | cons i rest ih =>
      intro s s' hshape h r hr
      obtain ⟨dst, opn, srcs, hi, hmem⟩ := hshape i (by simp)
      subst hi
      rw [lsemStraight_cons] at h
      rcases hstep : lsemStep (LinstrR.Lopn [.reg dst] opn srcs) s with _ | s1
      · rw [hstep] at h; simp at h
      · rw [hstep] at h
        simp only at h
        rw [ih s1 s' (fun i' hi' => hshape i' (by simp [hi'])) h r hr]
        exact lsemStep_lvm_of_ne dst opn srcs s s1 hstep r
          (fun he => hr (he ▸ hmem))

/-! ## 3. The frame of an emitted chain -/

/-- Every instruction of an emitted uniform-`regArith` chain rooted at depth
    `curDepth` is a single-destination `Lopn` writing `regName d` for some
    `d ≥ curDepth`. -/
theorem straightOps_dsts {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) :
    ∀ {nArgs curDepth : Nat},
      ∀ i ∈ straightOps nArgs com curDepth,
        ∃ d opn srcs, curDepth ≤ d ∧ i = .Lopn [.reg (regName d)] opn srcs := by
  induction hcom with
  | ret v => intro nArgs curDepth i hi; simp [straightOps] at hi
  | var bop heq args hbody ih =>
      intro nArgs curDepth i hi
      rw [straightOps, List.mem_cons] at hi
      rcases hi with h | h
      · subst h
        exact ⟨curDepth, _, _, le_rfl, rfl⟩
      · obtain ⟨d, opn, srcs, hd, hieq⟩ := ih (nArgs := nArgs) (curDepth := curDepth + 1) i h
        exact ⟨d, opn, srcs, by omega, hieq⟩

/-- **An emitted chain writes only its own depth block.** A successful run of the
    chain a uniform-`regArith` `Com` emits at depth `curDepth` leaves every
    register outside `{regName d | d ≥ curDepth}` unchanged. -/
theorem straightOps_lvm_frame {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    {nArgs curDepth : Nat} {st st' : Lstate w}
    (h : lsemStraight (straightOps nArgs com curDepth) st = some st') :
    LvmFrame curDepth st st' := by
  intro r hr
  refine lsemStraight_lvm_of_dsts (fun n => ∃ d, curDepth ≤ d ∧ n = regName d)
    _ st st' ?_ h r ?_
  · intro i hi
    obtain ⟨d, opn, srcs, hd, hieq⟩ := straightOps_dsts hcom i hi
    exact ⟨regName d, opn, srcs, hieq, ⟨d, hd, rfl⟩⟩
  · rintro ⟨d, hd, rfl⟩
    exact hr d hd rfl

/-! ## 4. The binding register holds the truncated denotation -/

/-- **Binding `k`'s register holds the truncation's denotation.** Running the
    chain a uniform-`regArith` `Com` emits at depth `curDepth`, from a store
    agreeing with `V`, reaches a state whose register `regName (curDepth + k)`
    holds the denotation of `com` truncated at binding `k`. At the last binding
    this is `Com.denote com V`; the earlier bindings are the outputs the export's
    per-output stores read. -/
theorem straightOps_binding_denote {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com) :
    ∀ {nArgs curDepth k : Nat} {st st' : Lstate w} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgrees w nArgs curDepth st V →
      lsemStraight (straightOps nArgs com curDepth) st = some st' →
      k < comLen com →
      ∀ hty : comBindingTy com k = .reg w,
        st'.lvm (regName (curDepth + k))
          = (hty ▸ (comPrefix com k).denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth k st st' V _ _ _ _ hk _
      simp [comLen] at hk
  | var bop heq args hbody ih =>
      intro nArgs curDepth k st st' V hlen harg hagree hrun hk hty
      rename_i Γ' _ body
      set e : Expr jasminDialect Γ' (.reg w) :=
        ⟨JasminOp.regArith bop w, heq, args⟩ with he
      set val : BitVec w := e.denote V with hval
      have hstep := lsemStep_var (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) bop heq args hagree
      set st1 : Lstate w := (st.setReg (regName curDepth) val).nextPc with hst1
      have hrun' : lsemStraight (straightOps nArgs body (curDepth + 1)) st1 = some st' := by
        rw [straightOps, lsemStraight_cons, hstep] at hrun
        simpa using hrun
      have hagree' : StoreAgrees w nArgs (curDepth + 1) st1
          (V.extend (t := JasminTy.reg w) val) :=
        StoreAgrees.step val hlen harg hagree
      cases k with
      | zero =>
          have hframe : LvmFrame (curDepth + 1) st1 st' :=
            straightOps_lvm_frame hbody hrun'
          have hne : ∀ j, curDepth + 1 ≤ j → regName curDepth ≠ regName j := by
            intro j hj hcontra
            exact absurd (regName_injective hcontra) (by omega)
          have hval' : st'.lvm (regName (curDepth + 0)) = val := by
            simpa [hst1, Lstate.setReg] using hframe (regName curDepth) hne
          simpa [hval, comPrefix_denote_zero] using hval'
      | succ k =>
          have hlen' : (JasminTy.reg w :: Γ').length = curDepth + 1 := by
            simp [List.length_cons, hlen]
          have harg' : nArgs ≤ curDepth + 1 := by omega
          have hk' : k < comLen body := by simpa [comLen] using hk
          have := ih (nArgs := nArgs) (curDepth := curDepth + 1) (k := k)
            (st := st1) (st' := st') (V := V.extend (t := JasminTy.reg w) val)
            hlen' harg' hagree' hrun' hk' hty
          rw [show curDepth + (k + 1) = curDepth + 1 + k from by omega]
          exact this

/-- **The export reading of `straightOps_binding_denote`.** From the encoded
    argument valuation, the emitted chain reaches a state where the register of
    binding `k` decodes to the denotation of `com` truncated at binding `k`. The
    `k`-indexed companion of `comToLprog_lsem_straightline`, which reads one
    register (`comRetReg`). -/
theorem comToLprog_lsem_binding {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : UniformRegArith w com)
    (hu : UniformCtxt w Γ) (V : Ctxt.Valuation Γ) {k : Nat} (hk : k < comLen com) :
    ∃ st', lsemStraight (straightOps Γ.length com Γ.length) (encode V) = some st' ∧
      decode st' (regName (Γ.length + k))
        = (uniformRegArith_bindingTy hcom hk ▸ (comPrefix com k).denote V :
            ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, _⟩ :=
    lsemStraight_straightOps hcom (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encode V) (V := V) rfl le_rfl (encode_StoreAgrees hu V)
  exact ⟨st', hrun,
    straightOps_binding_denote hcom rfl le_rfl (encode_StoreAgrees hu V) hrun hk _⟩

/-! ## 5. The ABI epilogue's store -/

/-- The epilogue's instruction list, lifted from `Linstr` to the `LinstrR` the
    linear semantics steps. -/
def epilogueOps (virt : Lfundef) (tbl : Array Nat) (outStoreMap : OutStoreMap) :
    List LinstrR :=
  (buildEpilogue virt tbl outStoreMap).map Linstr.li_i

/-- `stripWidthTag` leaves the untagged `MOV` mnemonic alone. -/
@[simp] theorem stripWidthTag_MOV : stripWidthTag "MOV" = "MOV" := by decide +kernel

/-- **The single-output epilogue stores the binding's value.** For a one-target
    `outStoreMap` whose designated binding has a register destination allocated
    to a physical register other than the out-pointer scratch, the epilogue runs
    to a state whose `[R14 + off]` cell holds the value that register held on
    entry to the epilogue. -/
theorem buildEpilogue_single_store_value {w : Nat} (virt : Lfundef) (tbl : Array Nat)
    (base : String) (off : Nat) (srcName : String)
    (hdst : bindingDstOp virt.lfd_body (numBindings virt.lfd_body - 1)
      = some (.reg srcName))
    (hns : ¬ (LOperand.reg (physNameForBody virt.lfd_body tbl srcName)).isSpill)
    (hne : physNameForBody virt.lfd_body tbl srcName ≠ reloadScratch2)
    (s : Lstate w) :
    ∃ s', lsemStraight (epilogueOps virt tbl [(base, off)]) s = some s' ∧
      s'.lvm (memName reloadScratch2 off)
        = s.lvm (physNameForBody virt.lfd_body tbl srcName) := by
  have hops : epilogueOps virt tbl [(base, off)] =
      [.Lopn [.reg reloadScratch2] "MOV" [.reg abiSaveRdiName],
       .Lopn [.reg (memName reloadScratch2 off)] "MOV"
         [.reg (physNameForBody virt.lfd_body tbl srcName)]] := by
    simp [epilogueOps, buildEpilogue, hdst, hns]
  rw [hops]
  refine ⟨_, rfl, ?_⟩
  have hne' : physNameForBody virt.lfd_body tbl srcName ≠ "R14" := by
    simpa [reloadScratch2] using hne
  simp [Lstate.setReg, memName, evalOperand, reloadScratch2, abiSaveRdiName, hne']

/-- **What the epilogue writes.** Every epilogue instruction is a single-`MOV`
    `Lopn` whose destination is the out-pointer scratch `R14`, the reload scratch
    `R15`, or an `[R14 + off]` cell at an offset the `outStoreMap` carries. With
    `lsemStraight_lvm_of_dsts` this bounds what a store can disturb. -/
theorem buildEpilogue_dsts (virt : Lfundef) (tbl : Array Nat)
    (outStoreMap : OutStoreMap) :
    ∀ i ∈ buildEpilogue virt tbl outStoreMap,
      ∃ dst srcs, i.li_i = LinstrR.Lopn [.reg dst] "MOV" srcs ∧
        (dst = reloadScratch2 ∨ dst = reloadScratch ∨
          ∃ (j : Nat) (base : String) (off : Nat),
            outStoreMap[j]? = some (base, off) ∧
            dst = memName reloadScratch2 off) := by
  intro i hi
  unfold buildEpilogue at hi
  rw [List.mem_append] at hi
  rcases hi with hres | hi
  · simp at hres
    subst hres
    exact ⟨_, _, rfl, Or.inl rfl⟩
  · rw [List.mem_flatMap] at hi
    obtain ⟨j, _hj, h⟩ := hi
    cases ho : outStoreMap[j]? with
    | none => simp [ho] at h
    | some bo =>
        simp [ho] at h
        cases hbd : bindingDstOp virt.lfd_body
                      (numBindings virt.lfd_body - outStoreMap.length + j) with
        | none => simp [hbd] at h
        | some d =>
            cases d with
            | reg srcName =>
                simp [hbd] at h
                by_cases hs : (LOperand.reg
                                (physNameForBody virt.lfd_body tbl srcName)).isSpill
                · simp [hs] at h
                  rcases h with h | h <;> subst h
                  · exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
                  · exact ⟨_, _, rfl, Or.inr (Or.inr ⟨j, bo.1, bo.2, by simpa using ho, rfl⟩)⟩
                · simp [hs] at h
                  subst h
                  exact ⟨_, _, rfl, Or.inr (Or.inr ⟨j, bo.1, bo.2, by simpa using ho, rfl⟩)⟩
            | imm _ => simp [hbd] at h
            | arr _ _ => simp [hbd] at h
            | arrIdx _ _ _ => simp [hbd] at h

end CatCrypt.Crypto.SecureCompilation.VIR.JasminBindingPrefixDenote
