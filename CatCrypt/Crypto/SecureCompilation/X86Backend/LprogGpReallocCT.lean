/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# The register re-allocation introduces no register-indexed access

The only instruction whose memory address depends on a register value is one with
a register-indexed operand `LOperand.arrIdx` (`AllocCTPreservation.isIndexed`).
The re-allocation `LprogGpRealloc.reallocBody` rewrites only the runs of fragment
instructions, whose sources are registers and immediates; a register rename maps a
register to a register (`renOp`). Every instruction of its output is therefore an
instruction of its input or has no register-indexed operand. A spill cell `k.N`
and a memory cell `mem.<B>.<off>` are register-shaped names at a fixed frame or
base offset, so a promoted or renamed cell issues no value-dependent address.

* `fiDirect`, `goAcc_direct`, `reallocRun_direct`: every instruction the check
  materializes, and every instruction of a re-allocated run, has no
  register-indexed source.
* `reallocBody_mem`: every instruction of `reallocBody res body` is an instruction
  of `body` or is `linstrRDirect`.
* `reallocBody_lcmdDirect`, `reallocLprog_lcmdDirect`: the pass preserves the
  direct-addressing class `lcmdDirect`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (isIndexed linstrRDirect lcmdDirect lcmdDirect_iff)

/-- No source of the fragment instruction is register-indexed. -/
def fiDirect (i : FI) : Bool := i.srcs.all (fun o => !isIndexed o)

theorem renOp_not_indexed (m : Cur) {o : LOperand} (h : isIndexed o = false) :
    isIndexed (renOp m o) = false := by
  cases o with
  | reg n => simp only [renOp]; split <;> rfl
  | _ => simp_all [renOp]

theorem fiDirect_rename (m : Cur) (i : FI) (c : String) (h : fiDirect i = true) :
    fiDirect ⟨i.ii, c, i.opn, i.srcs.map (renOp m)⟩ = true := by
  simp only [fiDirect, List.all_map, List.all_eq_true, Function.comp_apply,
    Bool.not_eq_true'] at h ⊢
  exact fun o ho => renOp_not_indexed m (h o ho)

theorem fiDirect_of_wf {i : FI} (h : i.wf = true) : fiDirect i = true := by
  have hs := wf_of_srcs h
  simp only [fiDirect, List.all_eq_true] at hs ⊢
  intro o ho
  have := hs o ho
  cases o <;> simp_all [regOrImm, isIndexed]

theorem linstrRDirect_toR {i : FI} (h : fiDirect i = true) :
    linstrRDirect i.toR = true := by
  simp only [fiDirect, List.all_eq_true, Bool.not_eq_true'] at h
  simpa [FI.toR, linstrRDirect] using h

/-- Every instruction the check materializes has no register-indexed source. -/
theorem goAcc_direct (lend : List String) :
    ∀ (ann : List (FI × List String)) (m : Cur) (cs : List String) (acc out : List FI),
      (∀ p ∈ ann, fiDirect p.1 = true) → (∀ j ∈ acc, fiDirect j = true) →
      goAcc lend m ann cs acc = some out → ∀ j ∈ out, fiDirect j = true := by
  intro ann
  induction ann with
  | nil =>
      intro m cs acc out _ hacc h
      cases cs with
      | nil =>
          simp only [goAcc] at h
          split at h
          · cases h
            intro j hj
            exact hacc j (List.mem_reverse.1 hj)
          · cases h
      | cons c cs => simp [goAcc] at h
  | cons p rest ih =>
      intro m cs acc out hann hacc h
      obtain ⟨i, la⟩ := p
      have hi : fiDirect i = true := hann (i, la) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, fiDirect q.1 = true :=
        fun q hq => hann q (List.mem_cons_of_mem _ hq)
      cases cs with
      | nil => simp [goAcc] at h
      | cons c cs =>
          simp only [goAcc] at h
          have push : ∀ (d : String), ∀ j ∈
              ({ ii := i.ii, d := d, opn := i.opn, srcs := i.srcs.map (renOp m) } : FI) :: acc,
              fiDirect j = true := by
            intro d j hj
            rcases List.mem_cons.1 hj with rfl | hj
            · exact fiDirect_rename m i d hi
            · exact hacc j hj
          split_ifs at h
          all_goals first
            | exact ih _ _ _ _ hrest hacc h
            | exact ih _ _ _ _ hrest (push _) h

/-- Every instruction of a re-allocated run with direct sources has direct sources. -/
theorem reallocRun_direct (lend : List String) (is : List FI)
    (h : ∀ i ∈ is, fiDirect i = true) : ∀ j ∈ reallocRun lend is, fiDirect j = true := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    have hann : ∀ p ∈ (annotate lend is).1, fiDirect p.1 = true := by
      suffices hs : ∀ (l : List FI), (∀ i ∈ l, fiDirect i = true) →
          ∀ p ∈ (annotate lend l).1, fiDirect p.1 = true from hs is h
      intro l
      induction l with
      | nil => intro _ p hp; simp [annotate] at hp
      | cons i l ih =>
          intro hl p hp
          rw [annotate_cons] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hl i (List.mem_cons_self ..)
          · exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) p hp
    exact goAcc_direct lend _ {} cs [] out hann (by simp) hcs
  · exact h

theorem fragOf?_wf {li : Linstr} {i : FI} (h : fragOf? li = some i) : i.wf = true := by
  unfold fragOf? at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact hc.2
    · cases h
  · cases h

/-- A piece of `pieces body` is an instruction of `body` or a run of fragment
    instructions. -/
theorem pieces_spec (body : Lcmd) :
    ∀ p ∈ pieces body, (∃ li ∈ body, p = .bar li) ∨
      (∃ is, p = .run is ∧ ∀ i ∈ is, i.wf = true) := by
  induction body with
  | nil => intro p hp; simp [pieces] at hp
  | cons li rest ih =>
      intro p hp
      have ih' : ∀ p ∈ pieces rest, (∃ li' ∈ li :: rest, p = .bar li') ∨
          (∃ is, p = .run is ∧ ∀ i ∈ is, i.wf = true) := by
        intro q hq
        rcases ih q hq with ⟨li', hli', rfl⟩ | hr
        · exact Or.inl ⟨li', List.mem_cons_of_mem _ hli', rfl⟩
        · exact Or.inr hr
      have hfr : pieces (li :: rest) =
          (match fragOf? li with
            | some i =>
                match pieces rest with
                | Piece.run is :: tl => Piece.run (i :: is) :: tl
                | _ => Piece.run [i] :: pieces rest
            | none => Piece.bar li :: pieces rest) := rfl
      rw [hfr] at hp
      cases hf : fragOf? li with
      | none =>
          rw [hf] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact Or.inl ⟨li, List.mem_cons_self .., rfl⟩
          · exact ih' p hp
      | some i =>
          rw [hf] at hp
          have hwf := fragOf?_wf hf
          have hone : ∀ j ∈ [i], j.wf = true := by
            intro j hj
            rw [List.mem_singleton] at hj
            subst hj
            exact hwf
          revert hp ih'
          cases pieces rest with
          | nil =>
              intro _ hp
              rw [List.mem_singleton] at hp
              subst hp
              exact Or.inr ⟨[i], rfl, hone⟩
          | cons q tl =>
              cases q with
              | run is =>
                  intro ih' hp
                  rcases List.mem_cons.1 hp with rfl | hp
                  · rcases ih' (.run is) (List.mem_cons_self ..) with
                      ⟨_, _, hc⟩ | ⟨is', hc, hwfs⟩
                    · cases hc
                    · cases hc
                      refine Or.inr ⟨i :: is, rfl, fun j hj => ?_⟩
                      rcases List.mem_cons.1 hj with rfl | hj
                      · exact hwf
                      · exact hwfs j hj
                  · exact ih' p (List.mem_cons_of_mem _ hp)
              | bar l =>
                  intro ih' hp
                  rcases List.mem_cons.1 hp with rfl | hp
                  · exact Or.inr ⟨[i], rfl, hone⟩
                  · exact ih' p hp

/-- **Every instruction of the re-allocated body is an instruction of the body or
    has no register-indexed operand.** -/
theorem reallocBody_mem (res : List String) (body : Lcmd) :
    ∀ li ∈ reallocBody res body, li ∈ body ∨ linstrRDirect li.li_i = true := by
  unfold reallocBody
  dsimp only
  generalize hps : pieces body = ps
  have hspec : ∀ p ∈ ps, (∃ li ∈ body, p = .bar li) ∨
      (∃ is, p = .run is ∧ ∀ i ∈ is, i.wf = true) := hps ▸ pieces_spec body
  clear hps
  induction ps with
  | nil => intro li hli; simp at hli
  | cons p ps ih =>
      intro li hli
      have ih' := ih (fun q hq => hspec q (List.mem_cons_of_mem _ hq))
      rw [List.foldr_cons] at hli
      split at hli
      · rename_i is
        rcases List.mem_append.1 hli with hli | hli
        · right
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hli
          have hwf : ∀ i ∈ is, i.wf = true := by
            rcases hspec (.run is) (List.mem_cons_self ..) with ⟨_, _, hc⟩ | ⟨is', hc, hw⟩
            · cases hc
            · cases hc; exact hw
          exact linstrRDirect_toR (reallocRun_direct _ is
            (fun i hi => fiDirect_of_wf (hwf i hi)) j hj)
        · exact ih' li hli
      · rename_i li'
        rcases List.mem_cons.1 hli with rfl | hli
        · rcases hspec (.bar li) (List.mem_cons_self ..) with ⟨li', hli', hc⟩ | ⟨_, hc, _⟩
          · cases hc; exact Or.inl hli'
          · cases hc
        · exact ih' li hli

/-- **The re-allocation preserves direct addressing.** -/
theorem reallocBody_lcmdDirect (res : List String) {body : Lcmd}
    (h : lcmdDirect body = true) : lcmdDirect (reallocBody res body) = true := by
  rw [lcmdDirect_iff] at h ⊢
  intro li hli
  rcases reallocBody_mem res body li hli with hli | hd
  · exact h li hli
  · exact hd

/-- **The pass on a program preserves direct addressing** in every function body. -/
theorem reallocLprog_lcmdDirect {p : Lprog}
    (h : ∀ f ∈ p.lp_funcs, lcmdDirect f.2.lfd_body = true) :
    ∀ f ∈ (reallocLprog p).lp_funcs, lcmdDirect f.2.lfd_body = true := by
  intro f hf
  simp only [reallocLprog, List.mem_map] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  exact reallocBody_lcmdDirect _ (h g hg)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCT
