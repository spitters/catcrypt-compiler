/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof

/-!
# The RV64 Curve25519 ladder step as a function

`RiscvX25519LadderStepProof` states the ladder step as eighteen field operations over named
field elements. Here the field elements live in a 576-byte state block in memory, at the
offsets `off p`, and each operation is a call `jal ra` to the buffer function of its kernel
(`RiscvFeFnProof.fnSpec_buf`). `stepCode` is the step as a function of the
program-counter machine `RiscvPc64`: it opens a 16-byte frame, saves `ra` and `s0`, makes
the eighteen calls and returns.

## Main results

* `run_calls`: a list of calls leaves the field elements its steps compute, for any
  functions meeting the buffer specifications.
* `fnSpec_step`: `stepCode` placed in any program meets `FnSpec` with `StepPre` and
  `StepPost`.
* `step_value`: `StepPost` leaves `x25519DoubleAndAdd` of the coordinates in the block,
  canonical.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof
  (FeOp Step ladderSteps ladderPfx Pre)
open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64)

/-! ## Buffers in a state block -/

theorem sep_sub {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) (o w : Nat) (hw0 : 0 < w)
    (hw : o + w ≤ m) (hm : m < 2 ^ 64) : Sep a n (b + BitVec.ofNat 64 o) w := by
  obtain ⟨h1, h2⟩ := h
  have := a.isLt; have := b.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
  omega

theorem sep_bufs (P : BitVec 64) (o1 o2 j : Nat) (h : o1 + 32 ≤ o2 ∨ o2 + 32 ≤ o1) (hj : j < 32)
    (h1 : o1 < 2 ^ 32) (h2 : o2 < 2 ^ 32) :
    Sep (P + BitVec.ofNat 64 o1) 32 (P + BitVec.ofNat 64 o2 + BitVec.ofNat 64 j) 1 := by
  have := P.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_ofNat_add (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **A buffer whose bytes are unchanged reads the same.** -/
theorem memLimbs4_congr (m m' : AMem) (p : BitVec 64)
    (h : ∀ j < 32, m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    memLimbs4 m' p = memLimbs4 m p := by
  have hw : ∀ o, o + 8 ≤ 32 → read64 m' (p + BitVec.ofNat 64 o) = read64 m (p + BitVec.ofNat 64 o) :=
    fun o ho => read64_congr _ _ _ fun j hj => by
      rw [add_ofNat_add]
      exact h (o + j) (by omega)
  unfold memLimbs4
  rw [hw 0 (by decide), hw 8 (by decide), hw 16 (by decide), hw 24 (by decide)]

/-! ## The field operations at their kernels -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof
  (feAddPhys feSubPhys feMul121666Phys feAddPhys_correct feSubPhys_correct
    feMul121666Phys_correct)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof
  (feMulPhys feSqrPhys feMulPhys_correct feSqrPhys_correct)

/-- The physical kernel of a field operation. -/
def phys : FeOp → List MInst64
  | .add => feAddPhys
  | .sub => feSubPhys
  | .mul => feMulPhys
  | .sqr => feSqrPhys
  | .a24 => feMul121666Phys

theorem phys_correct (op : FeOp) (r : RState64)
    (h : op.pre (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7")) :
    limbs4 (runM64 r (phys op)).get "a0" "a1" "a2" "a3"
      = op.eval (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7") := by
  cases op
  · exact feAddPhys_correct r
  · exact feSubPhys_correct r h
  · exact feMulPhys_correct r
  · exact feSqrPhys_correct r
  · exact feMul121666Phys_correct r

theorem phys_sp_ra (op : FeOp) : "sp" ∉ mWrites (phys op) ∧ "ra" ∉ mWrites (phys op) := by
  cases op <;> decide +kernel

/-! ## The state block and the call sequence -/

/-- The offset of a field element in the state block. The first 32 bytes hold the scalar;
    field element `i` of `ladderPfx` is at `32·(i + 1)`. -/
def off (p : String) : Nat := 32 * (ladderPfx.idxOf p + 1)

theorem off_lt : ∀ p ∈ ladderPfx, 32 ≤ off p ∧ off p + 32 ≤ 576 := by decide

theorem off_sep : ∀ p ∈ ladderPfx, ∀ q ∈ ladderPfx, p ≠ q → off p + 32 ≤ off q ∨ off q + 32 ≤ off p := by
  decide

theorem off_se : ∀ p ∈ ladderPfx,
    (BitVec.ofNat 12 (off p)).signExtend 64 = BitVec.ofNat 64 (off p) := by decide

/-- The four instructions of one step at instruction `k`: point `a0`, `a1`, `a2` at the
    destination and the two sources, and call the operation's function. -/
def callCode (fnIdx : FeOp → Nat) (k : Nat) (s : Step) : List PInst64 :=
  [.x (.m (.addi "a0" "s0" (BitVec.ofNat 12 (off s.d)))),
    .x (.m (.addi "a1" "s0" (BitVec.ofNat 12 (off s.a)))),
    .x (.m (.addi "a2" "s0" (BitVec.ofNat 12 (off s.b)))),
    .jal "ra" (BitVec.ofInt 21 (4 * (fnIdx s.op : Int) - 4 * (k + 3 : Nat)))]

/-- The calls of a list of steps, from instruction `k`. -/
def callsCode (fnIdx : FeOp → Nat) : Nat → List Step → List PInst64
  | _, [] => []
  | k, s :: sts => callCode fnIdx k s ++ callsCode fnIdx (k + 4) sts

theorem callsCode_length (fnIdx : FeOp → Nat) (k : Nat) (sts : List Step) :
    (callsCode fnIdx k sts).length = 4 * sts.length := by
  induction sts generalizing k with
  | nil => rfl
  | cons s sts ih => simp [callsCode, callCode, ih]; omega

/-- The field elements `e` are in the state block at `P`. -/
def InvM (P : BitVec 64) (m : AMem) (e : String → Nat) : Prop :=
  ∀ p ∈ ladderPfx, memLimbs4 m (P + BitVec.ofNat 64 (off p)) = e p

theorem sep_symm' {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) : Sep b m a n := ⟨h.2, h.1⟩

theorem sep_into {b x : BitVec 64} {m : Nat} (h : Sep b m x 1) (o w : Nat) (hw0 : 0 < w)
    (hw : o + w ≤ m) (hm : m < 2 ^ 64) : Sep (b + BitVec.ofNat 64 o) w x 1 :=
  sep_symm' (sep_sub (sep_symm' h) o w hw0 hw hm)

theorem frame_ne : ∀ q ∈ frameSlots, q.1 ≠ "a0" ∧ q.1 ≠ "a1" ∧ q.1 ≠ "a2" ∧ q.1 ≠ "ra" := by
  decide

theorem s0_mem : ("s0", 0) ∈ frameSlots := by decide

/-- **A sequence of calls.** From a state with the state block at `s0 = P`, whose 576 bytes
    are disjoint from the callee frames below `sp`, the calls of `sts` leave the field
    elements the steps compute, restore `s0..s11` and `sp`, and change no byte outside the
    callee frames and the field region of the block. -/
theorem run_calls (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (fnIdx : FeOp → Nat) (hfn : ∀ op, 4 * fnIdx op < 2 ^ 20)
    (hspec : ∀ op, FnSpec prog base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval))
    (P SP : BitVec 64) (hsep : Sep (SP + BitVec.ofInt 64 (-112)) 112 P 576) :
    ∀ (sts : List Step) (pre post : List PInst64) (e : String → Nat) (st0 : MState64),
      prog = pre ++ callsCode fnIdx pre.length sts ++ post →
      4 * (pre.length + 4 * sts.length) < 2 ^ 20 →
      (∀ s ∈ sts, s.a ∈ ladderPfx ∧ s.b ∈ ladderPfx ∧ s.d ∈ ladderPfx) →
      st0.regs.get "s0" = P → st0.regs.get "sp" = SP → InvM P st0.mem e → Pre sts e →
      ∃ n st', steps prog base n ⟨addrOf base pre.length, st0⟩
          = some ⟨addrOf base (pre.length + 4 * sts.length), st'⟩ ∧
        InvM P st'.mem (sts.foldl (fun e s => s.env e) e) ∧
        (∀ q ∈ frameSlots, st'.regs.get q.1 = st0.regs.get q.1) ∧ st'.regs.get "sp" = SP ∧
        ∀ x, Sep (SP + BitVec.ofInt 64 (-112)) 112 x 1 →
          Sep (P + BitVec.ofNat 64 32) 544 x 1 → st'.mem x = st0.mem x := by
  intro sts
  induction sts with
  | nil =>
    intro pre post e st0 _ _ _ _ hsp hinv _
    exact ⟨0, st0, by simp [steps], hinv, fun _ _ => rfl, hsp, fun _ _ _ => rfl⟩
  | cons s sts ih =>
    intro pre post e st0 hprog hlen hwf hs0 hsp hinv hpre
    obtain ⟨ha, hbb, hd⟩ := hwf s List.mem_cons_self
    have hprog' : prog = pre ++ callCode fnIdx pre.length s
        ++ (callsCode fnIdx (pre.length + 4) sts ++ post) := by
      rw [hprog]; simp [callsCode, List.append_assoc]
    have hat : ∀ j < 4, prog[pre.length + j]? = (callCode fnIdx pre.length s)[j]? := by
      intro j hj
      rw [hprog']
      exact getElem?_mid _ _ _ j (by simp [callCode]; omega)
    simp only [List.length_cons] at hlen
    -- the three pointer set-ups
    have f0 : prog[pre.length]? = some (.x (.m (.addi "a0" "s0" (BitVec.ofNat 12 (off s.d))))) := by
      have := hat 0 (by decide)
      simp only [Nat.add_zero] at this
      rw [this]; rfl
    have f1 : prog[pre.length + 1]? =
        some (.x (.m (.addi "a1" "s0" (BitVec.ofNat 12 (off s.a))))) := by
      rw [hat 1 (by decide)]; rfl
    have f2 : prog[pre.length + 1 + 1]? =
        some (.x (.m (.addi "a2" "s0" (BitVec.ofNat 12 (off s.b))))) := by
      rw [show pre.length + 1 + 1 = pre.length + 2 by omega, hat 2 (by decide)]; rfl
    have h1 := steps_x prog base pre.length (by omega) _ f0 st0
    have h2 := steps_x prog base (pre.length + 1) (by omega) _ f1
      (evalX st0 (.m (.addi "a0" "s0" (BitVec.ofNat 12 (off s.d)))))
    have h3 := steps_x prog base (pre.length + 1 + 1) (by omega) _ f2
      (evalX (evalX st0 (.m (.addi "a0" "s0" (BitVec.ofNat 12 (off s.d)))))
        (.m (.addi "a1" "s0" (BitVec.ofNat 12 (off s.a)))))
    generalize hst3 : evalX (evalX (evalX st0 (.m (.addi "a0" "s0" (BitVec.ofNat 12 (off s.d)))))
        (.m (.addi "a1" "s0" (BitVec.ofNat 12 (off s.a)))))
        (.m (.addi "a2" "s0" (BitVec.ofNat 12 (off s.b)))) = st3 at h3
    have hm3 : st3.mem = st0.mem := by rw [← hst3]; rfl
    have hr3 : ∀ r, r ≠ "a0" → r ≠ "a1" → r ≠ "a2" → st3.regs.get r = st0.regs.get r := by
      intro r h0 h1' h2'
      rw [← hst3]
      simp only [evalX, evalMInst64]
      rw [RState64.get_set_other _ _ _ _ h2', RState64.get_set_other _ _ _ _ h1',
        RState64.get_set_other _ _ _ _ h0]
    have hp : ∀ p ∈ ladderPfx, ∀ r, r = "a0" ∨ r = "a1" ∨ r = "a2" → True := fun _ _ _ _ => trivial
    clear hp
    have hv0 : st3.regs.get "a0" = P + BitVec.ofNat 64 (off s.d) := by
      rw [← hst3]
      simp only [evalX, evalMInst64, RState64.get_set_same, RState64.get_set_other, ne_eq,
        String.reduceEq, not_false_eq_true, or_self]
      rw [hs0, off_se _ hd]
    have hv1 : st3.regs.get "a1" = P + BitVec.ofNat 64 (off s.a) := by
      rw [← hst3]
      simp only [evalX, evalMInst64, RState64.get_set_same, RState64.get_set_other, ne_eq,
        String.reduceEq, not_false_eq_true, or_self]
      rw [hs0, off_se _ ha]
    have hv2 : st3.regs.get "a2" = P + BitVec.ofNat 64 (off s.b) := by
      rw [← hst3]
      simp only [evalX, evalMInst64, RState64.get_set_same, RState64.get_set_other, ne_eq,
        String.reduceEq, not_false_eq_true, or_self]
      rw [hs0, off_se _ hbb]
    -- the call
    have hjal : prog[pre.length + 3]? =
        some (.jal "ra" (BitVec.ofInt 21 (4 * (fnIdx s.op : Int) - 4 * ((pre.length + 3 : Nat) : Int)))) := by
      rw [hat 3 (by decide)]; rfl
    have hsep' := fun o (ho : o + 32 ≤ 576) => sep_sub hsep o 32 (by decide) ho (by decide)
    have hpre1 := hpre.1
    rw [← hinv _ ha, ← hinv _ hbb] at hpre1
    obtain ⟨n, st4, hrun, hpost⟩ := steps_call_at prog base hb (pre.length + 3) (fnIdx s.op)
      (by omega) (hfn _) hjal (hspec s.op) st3 (by
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp only [RState64.get_set_other _ _ _ _ (show ("sp" : String) ≠ "ra" by decide),
            RState64.get_set_other _ _ _ _ (show ("a0" : String) ≠ "ra" by decide),
            RState64.get_set_other _ _ _ _ (show ("a1" : String) ≠ "ra" by decide),
            RState64.get_set_other _ _ _ _ (show ("a2" : String) ≠ "ra" by decide)]
        · rw [hr3 "sp" (by decide) (by decide) (by decide), hsp, hv1]
          exact hsep' _ (off_lt _ ha).2
        · rw [hr3 "sp" (by decide) (by decide) (by decide), hsp, hv2]
          exact hsep' _ (off_lt _ hbb).2
        · rw [hr3 "sp" (by decide) (by decide) (by decide), hsp, hv0]
          exact hsep' _ (off_lt _ hd).2
        · rw [hv1, hv2, hm3]; exact hpre1)
    obtain ⟨p1, p2, p3, p4, p5⟩ := hpost
    simp only [RState64.get_set_other _ _ _ _ (show ("sp" : String) ≠ "ra" by decide),
      RState64.get_set_other _ _ _ _ (show ("a0" : String) ≠ "ra" by decide),
      RState64.get_set_other _ _ _ _ (show ("a1" : String) ≠ "ra" by decide),
      RState64.get_set_other _ _ _ _ (show ("a2" : String) ≠ "ra" by decide),
      hv0, hv1, hv2, hm3, hr3 "sp" (by decide) (by decide) (by decide), hsp] at p1 p3 p5
    rw [hinv _ ha, hinv _ hbb] at p1
    have hfs : ∀ q ∈ frameSlots, st4.regs.get q.1 = st0.regs.get q.1 := by
      intro q hq
      obtain ⟨n0, n1, n2, nra⟩ := frame_ne q hq
      rw [p2 q hq, RState64.get_set_other _ _ _ _ nra, hr3 _ n0 n1 n2]
    have hx4 : ∀ x, Sep (SP + BitVec.ofInt 64 (-112)) 112 x 1 →
        Sep (P + BitVec.ofNat 64 32) 544 x 1 → st4.mem x = st0.mem x := by
      intro x hx hx'
      refine p5 x hx ?_
      have := sep_into hx' (off s.d - 32) 32 (by decide) (by have := off_lt _ hd; omega)
        (by decide)
      rwa [add_ofNat_add, show 32 + (off s.d - 32) = off s.d by have := off_lt _ hd; omega]
        at this
    have hinv4 : InvM P st4.mem (s.env e) := by
      intro q hq
      simp only [RiscvX25519LadderStepProof.Step.env]
      by_cases hqd : q = s.d
      · subst hqd
        rw [Function.update_self, p1]
      · rw [Function.update_of_ne hqd, ← hinv _ hq]
        refine memLimbs4_congr _ _ _ fun j hj => ?_
        refine (p5 _ ?_ ?_).trans rfl
        · rw [add_ofNat_add]
          exact sep_sub hsep _ 1 (by decide) (by have := off_lt _ hq; omega) (by decide)
        · exact sep_bufs P (off s.d) (off q) j (off_sep _ hd _ hq (Ne.symm hqd)) hj
            (by have := off_lt _ hd; omega) (by have := off_lt _ hq; omega)
    obtain ⟨n', st', hrun', hinv', hfs', hsp', hx'⟩ := ih (pre ++ callCode fnIdx pre.length s)
      post (s.env e) st4 (by rw [hprog]; simp [callsCode, callCode, List.append_assoc])
      (by simp [callCode]; omega) (fun s' hs' => hwf s' (List.mem_cons_of_mem _ hs'))
      (by rw [hfs _ s0_mem, hs0]) p3 hinv4 hpre.2
    refine ⟨1 + 1 + 1 + (1 + n) + n', st', ?_, hinv', ?_, hsp', ?_⟩
    · simp only [List.length_append, show (callCode fnIdx pre.length s).length = 4 from rfl]
        at hrun'
      rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega] at h3
      rw [show pre.length + 3 + 1 = pre.length + 4 by omega] at hrun
      rw [steps_trans (steps_trans (steps_trans (steps_trans h1 h2) h3) hrun) hrun']
      simp only [List.length_cons]
      congr 3
      omega
    · intro q hq; rw [hfs' q hq, hfs q hq]
    · intro x hx hx''; rw [hx' x hx hx'', hx4 x hx hx'']

/-! ## The ladder step as a function -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof
  (ladderEnvP ladderNat ladderEnvP_eq ladderNat_correct)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof (p25519_pos)

theorem pre_ladder (e : String → Nat) (hz2 : e "z2" ≤ 2 * p25519) (hz3 : e "z3" ≤ 2 * p25519) :
    Pre ladderSteps e := by
  simp only [ladderSteps, Pre, RiscvX25519LadderStepProof.Step.env, FeOp.pre, FeOp.eval,
    FeOp.evalP, Function.update_apply, String.reduceEq, ↓reduceIte, and_true, true_and]
  exact ⟨by omega, (Nat.mod_lt _ p25519_pos).le.trans (by omega), by omega,
    (Nat.mod_lt _ p25519_pos).le.trans (by omega)⟩

theorem ladder_wf : ∀ s ∈ ladderSteps, s.a ∈ ladderPfx ∧ s.b ∈ ladderPfx ∧ s.d ∈ ladderPfx := by
  decide

/-- Open a 16-byte frame, save `ra` and `s0`, and keep the block pointer in `s0`. -/
def stepPro : List PInst64 :=
  [.x (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16)))), .x (.sd "ra" "sp" 0), .x (.sd "s0" "sp" 8),
    .x (.m (.base (.mv "s0" "a0")))]

/-- Restore `ra` and `s0`, close the frame and return. -/
def stepEpi : List PInst64 :=
  [.x (.ld "ra" "sp" 0), .x (.ld "s0" "sp" 8), .x (.m (.addi "sp" "sp" 16)), .jalr "zero" "ra" 0]

/-- The ladder step function at instruction `k`: open a 16-byte frame, save `ra` and `s0`,
    keep the state block pointer `a0` in `s0`, make the eighteen calls, restore and return. -/
def stepCode (fnIdx : FeOp → Nat) (k : Nat) : List PInst64 :=
  stepPro ++ callsCode fnIdx (k + 4) ladderSteps ++ stepEpi

theorem stepCode_length (fnIdx : FeOp → Nat) (k : Nat) : (stepCode fnIdx k).length = 80 := by
  simp [stepCode, stepPro, stepEpi, callsCode_length, ladderSteps]

/-- The entry condition of the step function: the 128 bytes below `sp` are disjoint from the
    576-byte state block at `a0`, and `z2`, `z3` are at most `2·p25519`. -/
def StepPre (st : MState64) : Prop :=
  Sep (st.regs.get "sp" + BitVec.ofInt 64 (-128)) 128 (st.regs.get "a0") 576 ∧
    memLimbs4 st.mem (st.regs.get "a0" + BitVec.ofNat 64 (off "z2")) ≤ 2 * p25519 ∧
    memLimbs4 st.mem (st.regs.get "a0" + BitVec.ofNat 64 (off "z3")) ≤ 2 * p25519

/-- The effect of the step function. -/
def StepPost (st st' : MState64) : Prop :=
  InvM (st.regs.get "a0") st'.mem (ladderSteps.foldl (fun e s => s.env e)
      fun p => memLimbs4 st.mem (st.regs.get "a0" + BitVec.ofNat 64 (off p))) ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra" ∧
    ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-128)) 128 x 1 →
      Sep (st.regs.get "a0" + BitVec.ofNat 64 32) 544 x 1 → st'.mem x = st.mem x

theorem sep_shift {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) (o n' : Nat) (hn0 : 0 < n')
    (hn : o + n' ≤ n) (hn64 : n < 2 ^ 64) : Sep (a + BitVec.ofNat 64 o) n' b m :=
  sep_symm' (sep_sub (sep_symm' h) o n' hn0 hn hn64)

theorem sep_shrink {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) (n' : Nat) (hn : n' ≤ n) :
    Sep a n' b m := ⟨le_trans hn h.1, h.2⟩

theorem memLimbs4_writeSlots_sepN (m : AMem) (base p : BitVec 64) (l : List (Nat × BitVec 64))
    (n : Nat) (hn : n < 2 ^ 64) (hl : ∀ q ∈ l, q.1 + 8 ≤ n) (h : Sep base n p 32) :
    memLimbs4 (writeSlots m base l) p = memLimbs4 m p := by
  unfold memLimbs4
  rw [read64_writeSlots_sep _ _ _ n hn _ hl (sep_word h 0 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ n hn _ hl (sep_word h 8 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ n hn _ hl (sep_word h 16 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ n hn _ hl (sep_word h 24 (by decide) (by decide))]

theorem seNeg16 : (BitVec.ofInt 12 (-16)).signExtend 64 = BitVec.ofInt 64 (-16) := by decide

theorem addr_m128 (S : BitVec 64) (o : Nat) :
    S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o = S + BitVec.ofInt 64 (-128) + BitVec.ofNat 64 (112 + o) := by
  rw [show BitVec.ofInt 64 (-16) = BitVec.ofInt 64 (-128) + BitVec.ofNat 64 112 by decide,
    ← BitVec.add_assoc, add_ofNat_add]

theorem addr_m112 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112) = S + BitVec.ofInt 64 (-128) := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112) = BitVec.ofInt 64 (-128) by decide]

theorem addr_p16 (S : BitVec 64) : S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 16 = S := by
  rw [BitVec.add_assoc, show BitVec.ofInt 64 (-16) + BitVec.ofNat 64 16 = 0 by decide]
  simp

theorem sep_after (Q : BitVec 64) (n k : Nat) (hk0 : 0 < k) (hk : n ≤ k) (hk' : k < 2 ^ 32) :
    Sep Q n (Q + BitVec.ofNat 64 k) 1 := by
  have := Q.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A byte of the 16-byte frame below `sp` lies outside the callee frames and the state
    block. -/
theorem slot_byte (S P : BitVec 64) (hsep : Sep (S + BitVec.ofInt 64 (-128)) 128 P 576)
    (o : Nat) (ho : o < 16) :
    Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)) 112
        (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) 1 ∧
      Sep (P + BitVec.ofNat 64 32) 544 (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) 1 := by
  rw [addr_m112, addr_m128]
  refine ⟨sep_after _ 112 (112 + o) (by omega) (by omega) (by omega), ?_⟩
  exact sep_symm' (sep_sub (sep_shift hsep (112 + o) 1 (by decide) (by omega) (by decide))
    32 544 (by decide) (by decide) (by decide))

theorem sp_base (S : BitVec 64) :
    S + BitVec.ofInt 64 (-16) = S + BitVec.ofInt 64 (-128) + BitVec.ofNat 64 112 := by
  rw [show BitVec.ofInt 64 (-16) = BitVec.ofInt 64 (-128) + BitVec.ofNat 64 112 by decide,
    ← BitVec.add_assoc]

theorem steps_mid (prog pre post : List PInst64) (mid : List PInst64) (h : prog = pre ++ mid ++ post)
    (j : Nat) (hj : j < mid.length) : prog[pre.length + j]? = mid[j]? := by
  rw [h]; exact getElem?_mid _ _ _ j hj

/-- **The ladder step is a function.** -/
theorem fnSpec_step (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (fnIdx : FeOp → Nat) (hfn : ∀ op, 4 * fnIdx op < 2 ^ 20)
    (hspec : ∀ op, FnSpec prog base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval))
    (pre post : List PInst64) (hprog : prog = pre ++ stepCode fnIdx pre.length ++ post)
    (hlen : 4 * (pre.length + 80) < 2 ^ 20) :
    FnSpec prog base (addrOf base pre.length) StepPre StepPost := by
  intro st ⟨hsep, hz2, hz3⟩
  generalize hS : st.regs.get "sp" = S at hsep
  generalize hP : st.regs.get "a0" = P at hsep hz2 hz3
  have hat := steps_mid prog pre post _ hprog
  have hL := stepCode_length fnIdx pre.length
  -- the prologue
  have g0 : prog[pre.length]? = some (.x (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) := by
    have := hat 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; rfl
  have g1 : prog[pre.length + 1]? = some (.x (.sd "ra" "sp" 0)) := by
    rw [hat 1 (by omega)]; rfl
  have g2 : prog[pre.length + 1 + 1]? = some (.x (.sd "s0" "sp" 8)) := by
    rw [show pre.length + 1 + 1 = pre.length + 2 by omega, hat 2 (by omega)]; rfl
  have g3 : prog[pre.length + 1 + 1 + 1]? = some (.x (.m (.base (.mv "s0" "a0")))) := by
    rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega, hat 3 (by omega)]; rfl
  have k0 := steps_x prog base pre.length (by omega) _ g0 st
  have k1 := steps_x prog base (pre.length + 1) (by omega) _ g1
    (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16)))))
  have k2 := steps_x prog base (pre.length + 1 + 1) (by omega) _ g2
    (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) (.sd "ra" "sp" 0))
  have k3 := steps_x prog base (pre.length + 1 + 1 + 1) (by omega) _ g3
    (evalX (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) (.sd "ra" "sp" 0))
      (.sd "s0" "sp" 8))
  generalize hst1 : evalX (evalX (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16)))))
      (.sd "ra" "sp" 0)) (.sd "s0" "sp" 8)) (.m (.base (.mv "s0" "a0"))) = st1 at k3
  have hm1 : st1.mem = writeSlots st.mem (S + BitVec.ofInt 64 (-16))
      [(0, st.regs.get "ra"), (8, st.regs.get "s0")] := by
    rw [← hst1, ← hS]
    simp only [evalX, evalMInst64, evalRInst64, addr, writeSlots, seNeg16,
      RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true,
      or_self]
    rfl
  have hsp1 : st1.regs.get "sp" = S + BitVec.ofInt 64 (-16) := by
    rw [← hst1, ← hS]
    simp only [evalX, evalMInst64, evalRInst64, seNeg16, RState64.get_set_same,
      RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  have hs01 : st1.regs.get "s0" = P := by
    rw [← hst1, ← hP]
    simp only [evalX, evalMInst64, evalRInst64, RState64.get_set_same, RState64.get_set_other,
      ne_eq, String.reduceEq, not_false_eq_true, or_self]
  have hr1 : ∀ r, r ≠ "sp" → r ≠ "s0" → st1.regs.get r = st.regs.get r := by
    intro r h1 h2
    rw [← hst1]
    simp only [evalX, evalMInst64, evalRInst64]
    rw [RState64.get_set_other _ _ _ _ h2, RState64.get_set_other _ _ _ _ h1]
  -- the calls
  have hsepc : Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)) 112 P 576 := by
    rw [addr_m112]; exact sep_shrink hsep 112 (by decide)
  have hinv1 : InvM P st1.mem (fun p => memLimbs4 st.mem (P + BitVec.ofNat 64 (off p))) := by
    intro p hp
    rw [hm1, memLimbs4_writeSlots_sepN _ _ _ _ 16 (by decide) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp)]
    rw [sp_base]
    exact sep_sub (sep_shift hsep 112 16 (by decide) (by decide) (by decide)) (off p) 32
      (by decide) (off_lt p hp).2 (by decide)
  have hprog' : prog = (pre ++ stepPro) ++ callsCode fnIdx (pre ++ stepPro).length ladderSteps
      ++ (stepEpi ++ post) := by
    rw [hprog]; simp [stepCode, List.append_assoc, stepPro]
  obtain ⟨n, st2, hrun, hinv2, hfs2, hsp2, hfr2⟩ := run_calls prog base hb fnIdx hfn hspec P
    (S + BitVec.ofInt 64 (-16)) hsepc ladderSteps _ _ _ st1 hprog'
    (by simp [ladderSteps, stepPro]; omega) ladder_wf hs01 hsp1 hinv1
    (pre_ladder _ (by rw [← hP] at hz2 ⊢; exact hz2) (by rw [← hP] at hz3 ⊢; exact hz3))
  rw [show (pre ++ stepPro).length = pre.length + 4 by simp [stepPro],
    show ladderSteps.length = 18 from rfl] at hrun
  -- the epilogue
  have e0 : prog[pre.length + 76]? = some (.x (.ld "ra" "sp" 0)) := by
    rw [hat 76 (by omega)]; rfl
  have e1 : prog[pre.length + 76 + 1]? = some (.x (.ld "s0" "sp" 8)) := by
    rw [show pre.length + 76 + 1 = pre.length + 77 by omega, hat 77 (by omega)]; rfl
  have e2 : prog[pre.length + 76 + 1 + 1]? = some (.x (.m (.addi "sp" "sp" 16))) := by
    rw [show pre.length + 76 + 1 + 1 = pre.length + 78 by omega, hat 78 (by omega)]; rfl
  have e3 : prog[pre.length + 76 + 1 + 1 + 1]? = some (.jalr "zero" "ra" 0) := by
    rw [show pre.length + 76 + 1 + 1 + 1 = pre.length + 79 by omega, hat 79 (by omega)]; rfl
  have q0 := steps_x prog base (pre.length + 76) (by omega) _ e0 st2
  have q1 := steps_x prog base (pre.length + 76 + 1) (by omega) _ e1
    (evalX st2 (.ld "ra" "sp" 0))
  have q2 := steps_x prog base (pre.length + 76 + 1 + 1) (by omega) _ e2
    (evalX (evalX st2 (.ld "ra" "sp" 0)) (.ld "s0" "sp" 8))
  generalize hst3 : evalX (evalX (evalX st2 (.ld "ra" "sp" 0)) (.ld "s0" "sp" 8))
      (.m (.addi "sp" "sp" 16)) = st3 at q2
  have hm3 : st3.mem = st2.mem := by rw [← hst3]; rfl
  -- the two saved words
  have hslot : ∀ o, o < 16 → o % 8 = 0 →
      read64 st2.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o)
        = read64 st1.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) := by
    intro o ho _
    refine read64_congr _ _ _ fun j hj => ?_
    rw [add_ofNat_add]
    obtain ⟨hx1, hx2⟩ := slot_byte S P hsep (o + j) (by omega)
    exact hfr2 _ hx1 hx2
  have hsaved : ∀ o v, (o, v) ∈ [(0, st.regs.get "ra"), (8, st.regs.get "s0")] →
      read64 st1.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) = v := by
    intro o v hmem
    rw [hm1]
    exact read64_writeSlots_mem _ _ _ o v hmem (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
  have hra3 : st3.regs.get "ra" = st.regs.get "ra" := by
    rw [← hst3]
    simp only [evalX, evalMInst64, addr, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp2]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (0 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 0 from rfl,
      hslot 0 (by decide) (by decide), hsaved 0 (st.regs.get "ra") (by simp)]
  have hs03 : st3.regs.get "s0" = st.regs.get "s0" := by
    rw [← hst3]
    simp only [evalX, evalMInst64, addr, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp2]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (8 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 8 from rfl,
      hslot 8 (by decide) (by decide), hsaved 8 (st.regs.get "s0") (by simp)]
  have hsp3 : st3.regs.get "sp" = S := by
    rw [← hst3]
    simp only [evalX, evalMInst64, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp2]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (16 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 16 from rfl, addr_p16]
  have hr3 : ∀ r, r ≠ "ra" → r ≠ "s0" → r ≠ "sp" → st3.regs.get r = st2.regs.get r := by
    intro r h1 h2 h3
    rw [← hst3]
    simp only [evalX, evalMInst64]
    rw [RState64.get_set_other _ _ _ _ h3, RState64.get_set_other _ _ _ _ h2,
      RState64.get_set_other _ _ _ _ h1]
  have q3 : steps prog base 1 ⟨addrOf base (pre.length + 76 + 1 + 1 + 1), st3⟩
      = some ⟨st.regs.get "ra" &&& ~~~1, st3⟩ := by
    simp only [steps, step, fetch_addrOf prog base (pre.length + 76 + 1 + 1 + 1) (by omega), e3,
      Option.bind_some, hra3]
    rw [set_zero _ _ (Or.inl rfl)]
    simp
  refine ⟨1 + 1 + 1 + 1 + n + 1 + 1 + 1 + 1, st3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show pre.length + 1 + 1 + 1 + 1 = pre.length + 4 by omega] at k3
    rw [show pre.length + 76 + 1 = pre.length + 76 + 1 from rfl] at q0
    exact steps_trans (steps_trans (steps_trans (steps_trans (steps_trans (steps_trans
      (steps_trans (steps_trans k0 k1) k2) k3) hrun) q0) q1) q2) q3
  · rw [hm3, hP]; exact hinv2
  · intro q hq
    by_cases hq0 : q.1 = "s0"
    · rw [hq0, hs03]
    · have hne : q.1 ≠ "ra" ∧ q.1 ≠ "sp" := by
        simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      rw [hr3 _ hne.1 hq0 hne.2, hfs2 q hq, hr1 _ hne.2 hq0]
  · rw [hsp3, hS]
  · exact hra3
  · intro x hx hx'
    rw [hS] at hx
    rw [hP] at hx'
    rw [hm3, hfr2 x (by rw [addr_m112]; exact sep_shrink hx 112 (by decide)) hx', hm1,
      writeSlots_out _ _ _ _ fun q hq => not_inRange_of_out
        (out_of_sep (by rw [sp_base]; exact sep_shift hx 112 16 (by decide) (by decide) (by decide))
          (by simp)) ?_ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp

/-! ## The value of a step -/

open CatCrypt.Util (P25519 X25519State x25519DoubleAndAdd x25519CSwap x25519LadderStepVerified
  x25519ScalarBit)
open CatCrypt.Util.Fp25519 (fromNat)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof (Step.envP)

theorem ladderEnvP_x1 (Q : Nat) (e0 : String → Nat) : ladderEnvP Q e0 "x1" = e0 "x1" := by
  simp only [ladderEnvP, ladderSteps, List.foldl_cons, List.foldl_nil, Step.envP,
    Function.update_apply, String.reduceEq, ↓reduceIte]

/-- The field element at `p` in the block at `P`. -/
def fe (m : AMem) (P : BitVec 64) (p : String) : Nat := memLimbs4 m (P + BitVec.ofNat 64 (off p))

/-- The block at `P` holds the ladder coordinates of `sx`. -/
def Holds (m : AMem) (P : BitVec 64) (sx : X25519State) : Prop :=
  fromNat (fe m P "x1") = sx.baseX ∧ fromNat (fe m P "x2") = sx.x2 ∧
    fromNat (fe m P "z2") = sx.z2 ∧ fromNat (fe m P "x3") = sx.x3 ∧ fromNat (fe m P "z3") = sx.z3

/-- **A step leaves double-and-add.** -/
theorem step_value (st st' : MState64) (hpost : StepPost st st') (sx : X25519State)
    (hh : Holds st.mem (st.regs.get "a0") sx)
    (hz2 : fe st.mem (st.regs.get "a0") "z2" ≤ 2 * p25519)
    (hz3 : fe st.mem (st.regs.get "a0") "z3" ≤ 2 * p25519) :
    Holds st'.mem (st.regs.get "a0") (x25519DoubleAndAdd sx) ∧
      fe st'.mem (st.regs.get "a0") "x2" < p25519 ∧ fe st'.mem (st.regs.get "a0") "z2" < p25519 ∧
      fe st'.mem (st.regs.get "a0") "x3" < p25519 ∧ fe st'.mem (st.regs.get "a0") "z3" < p25519 ∧
      fe st'.mem (st.regs.get "a0") "x1" = fe st.mem (st.regs.get "a0") "x1" := by
  obtain ⟨hinv, -⟩ := hpost
  have h : InvM (st.regs.get "a0") st'.mem
      (ladderEnvP p25519 fun p => fe st.mem (st.regs.get "a0") p) := hinv
  obtain ⟨v1, v2, v3, v4⟩ := ladderEnvP_eq p25519 fun p => fe st.mem (st.regs.get "a0") p
  obtain ⟨hx1, hx2, hzz2, hx3, hzz3⟩ := hh
  obtain ⟨c1, c2, c3, c4, l1, l2, l3, l4⟩ :=
    ladderNat_correct _ _ _ _ _ sx hx1 hx2 hzz2 hx3 hzz3 hz2 hz3
  have hx1' : fe st'.mem (st.regs.get "a0") "x1" = fe st.mem (st.regs.get "a0") "x1" :=
    (h "x1" (by decide)).trans (ladderEnvP_x1 _ _)
  refine ⟨⟨?_, (congrArg fromNat ((h "x2" (by decide)).trans v1)).trans c1,
    (congrArg fromNat ((h "z2" (by decide)).trans v2)).trans c2,
    (congrArg fromNat ((h "x3" (by decide)).trans v3)).trans c3,
    (congrArg fromNat ((h "z3" (by decide)).trans v4)).trans c4⟩,
    ((h "x2" (by decide)).trans v1).trans_lt l1, ((h "z2" (by decide)).trans v2).trans_lt l2,
    ((h "x3" (by decide)).trans v3).trans_lt l3, ((h "z3" (by decide)).trans v4).trans_lt l4,
    hx1'⟩
  rw [hx1']
  exact hx1

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof
