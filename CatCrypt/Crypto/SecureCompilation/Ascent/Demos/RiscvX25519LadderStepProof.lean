/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof
public import CatCrypt.Crypto.Util.X25519Verified

/-!
# The RV64 Montgomery ladder step computes RFC 7748 double-and-add

`RiscvX25519FieldKernel.ladderStepBlock` is the Montgomery differential add-and-double as
eighteen marshalled field-operation blocks (`runFe`) over field elements stored at register
prefixes (`x20..x23` for `x2`, and so on). That module states its composition (`rfl`) and
no value. This module proves the value for all inputs, over `runRBlock64`.

## Main results

* `ladderStep_correct`: for every machine state with `z2, z3 ≤ 2·p25519`, running
  `ladderStepBlock` leaves at `x2, z2, x3, z3` the coordinates of
  `CatCrypt.Util.x25519DoubleAndAdd` (RFC 7748 §5, without the swap), canonical;
* `runFe_step`: one marshalled field operation leaves its value at the destination prefix
  and every register outside its writes unchanged;
* `run_steps`: a list of marshalled field operations over disjoint prefixes computes the
  field elements of the list, prefix by prefix.

## Structure

* `FeOp.correct` collects `feAdd_correct`, `feSub_correct`, `feMul_correct`, `feSqr_correct`
  and `feMul121666_correct`; `FeOp.writes` bounds their write sets by `fieldWrites`;
* `ladder_wf` checks by `decide` that the seventeen prefixes are disjoint from each other,
  from `fieldWrites` and from the input registers;
* `ladderEnvP_eq` unfolds the eighteen steps with the modulus abstract, and
  `ladderNat_correct` maps the result into `ZMod p25519`. The kernel's `z2'` is
  `E·(BB + 121666·E)`, RFC 7748's is `E·(AA + 121665·E)`; they agree as `AA = BB + E`.

The subtraction blocks need `y ≤ x + 2·p25519`: the hypotheses on `z2` and `z3` cover the
two subtractions of inputs, and the other two subtract a canonical value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519MulProof
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Util (P25519 X25519State x25519DoubleAndAdd x25519A24)
open CatCrypt.Util.Fp25519 (fromNat)

/-! ## Field elements at a prefix -/

/-- The four limb registers of the field element at prefix `pfx`. -/
def feNames (pfx : String) : List String := [pfx ++ "0", pfx ++ "1", pfx ++ "2", pfx ++ "3"]

/-- The value of the field element at prefix `pfx`. -/
def feV (R : AStateR) (pfx : String) : Nat :=
  limbs4 R (pfx ++ "0") (pfx ++ "1") (pfx ++ "2") (pfx ++ "3")

theorem feAt_eq (s : RState64) (pfx : String) : feAt s pfx = feV s.get pfx := by
  unfold feAt feV limbs4; omega

theorem feV_frame {s t : RState64} {pfx : String} (h : ∀ r ∈ feNames pfx, t.get r = s.get r) :
    feV t.get pfx = feV s.get pfx := by
  simp only [feNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  unfold feV limbs4; rw [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-! ## Moving a field element -/

/-- A move from `src` to `dst` is sound: the destinations are writable, distinct and
    disjoint from the sources. -/
def MoveOK (src dst : String) : Prop :=
  (∀ d ∈ feNames dst, ¬ (d = "zero" ∨ d = "x0")) ∧ (feNames dst).Nodup ∧
    ∀ r ∈ feNames src, r ∉ feNames dst

instance (src dst : String) : Decidable (MoveOK src dst) := by
  unfold MoveOK; infer_instance

theorem blockWrites_moveFe (src dst : String) : blockWrites (moveFe src dst) = feNames dst := rfl

theorem moveFe_frame (s : RState64) (src dst r : String) (h : r ∉ feNames dst) :
    (runRBlock64 s (moveFe src dst)).get r = s.get r :=
  runRBlock64_frame _ _ _ (by rwa [blockWrites_moveFe])

theorem moveFe_val (s : RState64) (src dst : String) (h : MoveOK src dst) :
    feV (runRBlock64 s (moveFe src dst)).get dst = feV s.get src := by
  obtain ⟨hz, hn, hd⟩ := h
  simp only [feNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.nodup_cons, not_or] at hz hn hd
  simp only [moveFe, runRBlock64_cons, runRBlock64_nil, RiscvRename64.evalRInst64_eq_set,
    rinst64DstSrcs, RiscvRename64.instVal64]
  unfold feV limbs4
  generalize dst ++ "0" = d0 at *
  generalize dst ++ "1" = d1 at *
  generalize dst ++ "2" = d2 at *
  generalize dst ++ "3" = d3 at *
  generalize src ++ "0" = a0 at *
  generalize src ++ "1" = a1 at *
  generalize src ++ "2" = a2 at *
  generalize src ++ "3" = a3 at *
  obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, -⟩ := hn
  obtain ⟨-, ⟨e10, -⟩, ⟨e20, e21, -⟩, ⟨e30, e31, e32, -⟩⟩ := hd
  simp only [RState64.get_set_same _ _ _ (not_or.mpr hz0),
    RState64.get_set_same _ _ _ (not_or.mpr hz1),
    RState64.get_set_same _ _ _ (not_or.mpr hz2), RState64.get_set_same _ _ _ (not_or.mpr hz3),
    RState64.get_set_other _ _ _ _ e10, RState64.get_set_other _ _ _ _ e20,
    RState64.get_set_other _ _ _ _ e21, RState64.get_set_other _ _ _ _ e30,
    RState64.get_set_other _ _ _ _ e31, RState64.get_set_other _ _ _ _ e32,
    RState64.get_set_other _ _ _ _ h01, RState64.get_set_other _ _ _ _ h02,
    RState64.get_set_other _ _ _ _ h03, RState64.get_set_other _ _ _ _ h12,
    RState64.get_set_other _ _ _ _ h13, RState64.get_set_other _ _ _ _ h23]

/-! ## The field operations -/

/-- The five field operations the ladder step runs. -/
inductive FeOp
  | add | sub | mul | sqr | a24

/-- The block of a field operation. -/
def FeOp.block : FeOp → List ROp64
  | .add => feAddBlock
  | .sub => feSubBlock
  | .mul => feMulBlock
  | .sqr => feSqrBlock
  | .a24 => feMul121666Block

/-- The value of a field operation modulo `P`. The modulus is a parameter so that the
    unfolding of the ladder (`ladderEnvP_eq`) is checked with `P` abstract. -/
def FeOp.evalP (P : Nat) : FeOp → Nat → Nat → Nat
  | .add, x, y => (x + y) % P
  | .sub, x, y => (x + 2 * P - y) % P
  | .mul, x, y => x * y % P
  | .sqr, x, _ => x * x % P
  | .a24, x, _ => 121666 * x % P

/-- The value a field operation leaves in `z0..z3`, from `x` in `q0..q3` and `y` in
    `y0..y3`. -/
def FeOp.eval : FeOp → Nat → Nat → Nat := FeOp.evalP p25519

/-- The precondition of a field operation: only the subtraction has one. -/
def FeOp.pre : FeOp → Nat → Nat → Prop
  | .sub, x, y => y ≤ x + 2 * p25519
  | _, _, _ => True

theorem feV_q (R : AStateR) : feV R "q" = limbs4 R "q0" "q1" "q2" "q3" := rfl
theorem feV_y (R : AStateR) : feV R "y" = limbs4 R "y0" "y1" "y2" "y3" := rfl
theorem feV_z (R : AStateR) : feV R "z" = limbs4 R "z0" "z1" "z2" "z3" := rfl

theorem FeOp.correct (op : FeOp) (s : RState64) (h : op.pre (feV s.get "q") (feV s.get "y")) :
    feV (runRBlock64 s (lowerRBlock64 op.block)).get "z"
      = op.eval (feV s.get "q") (feV s.get "y") := by
  rw [feV_q, feV_y, feV_z]
  rw [feV_q, feV_y] at h
  cases op
  · exact feAdd_correct s
  · exact feSub_correct s h
  · exact feMul_correct s
  · exact feSqr_correct s
  · exact feMul121666_correct s

/-- Every register a field-operation block writes. -/
def fieldWrites : List String :=
  ["sum__", "e1", "d0", "tt__", "c1__", "c2__", "e2", "d1", "e3", "d2", "d4", "d3", "c38",
    "fl", "cy1", "z0", "cy2", "z1", "cy3", "z2", "cy", "z3", "cz1", "cz2", "cz3", "cz4", "pp0",
    "pp1", "pp2", "pp3", "bo1", "m0", "b1__", "b2__", "dif__", "bo2", "m1", "bo3", "m2", "bo",
    "m3", "one", "cond", "mask", "csm__", "tp0", "tp1", "tp2", "tp3", "f1", "a0", "f2", "a1",
    "f3", "a2", "a4", "a3", "g1", "g2", "g3", "g4", "gF", "u0", "u1", "u2", "u3", "v0", "v1",
    "v2", "v3", "acc0", "acc1", "acc2", "acc3", "acc4", "acc5", "acc6", "acc7", "lo__", "hi__",
    "cra", "crb", "rl4", "rh4", "rl5", "rh5", "rl6", "rh6", "rl7", "rh7", "j0", "q1", "j1",
    "q2", "j2", "q3", "j3", "q4", "j4", "r1", "t0", "r2", "t1", "r3", "t2", "r4", "t3", "r5",
    "t4", "y0", "y1", "y2", "y3", "cc", "l0", "h0", "l1", "h1", "l2", "h2", "l3", "h3", "p1",
    "p2", "p3", "p4"]

theorem FeOp.writes (op : FeOp) (r : String) (h : r ∉ fieldWrites) :
    r ∉ blockWrites (lowerRBlock64 op.block) := by
  have hsub : ∀ w ∈ blockWrites (lowerRBlock64 op.block), w ∈ fieldWrites := by
    cases op <;> decide +kernel
  exact fun hr => h (hsub r hr)

/-! ## One marshalled field operation -/

/-- The names of one `runFe` are sound: the three moves are, and the second source is not
    overwritten by the first move. -/
def StepOK (a b d : String) : Prop :=
  MoveOK a "q" ∧ MoveOK b "y" ∧ MoveOK "z" d ∧ ∀ r ∈ feNames b, r ∉ feNames "q"

instance (a b d : String) : Decidable (StepOK a b d) := by
  unfold StepOK; infer_instance

/-- **One marshalled field operation.** `runFe op.block a b d` leaves the operation's value
    on the elements at `a` and `b` at prefix `d`, and every register outside the block's
    writes, the input registers and `d` unchanged. -/
theorem runFe_step (op : FeOp) (a b d : String) (s : RState64) (hok : StepOK a b d)
    (hpre : op.pre (feV s.get a) (feV s.get b)) :
    feV (runRBlock64 s (runFe op.block a b d)).get d = op.eval (feV s.get a) (feV s.get b) ∧
      ∀ r, r ∉ fieldWrites → r ∉ feNames "q" → r ∉ feNames "y" → r ∉ feNames d →
        (runRBlock64 s (runFe op.block a b d)).get r = s.get r := by
  obtain ⟨h1, h2, h3, h4⟩ := hok
  simp only [runFe, runRBlock64_append]
  have hqy : ∀ r ∈ feNames "q", r ∉ feNames "y" := by decide
  have hq : feV (runRBlock64 (runRBlock64 s (moveFe a "q")) (moveFe b "y")).get "q"
      = feV s.get a := by
    rw [feV_frame (fun r hr => moveFe_frame _ b "y" r (hqy r hr)), moveFe_val s a "q" h1]
  have hy : feV (runRBlock64 (runRBlock64 s (moveFe a "q")) (moveFe b "y")).get "y"
      = feV s.get b := by
    rw [moveFe_val _ b "y" h2, feV_frame (fun r hr => moveFe_frame s a "q" r (h4 r hr))]
  refine ⟨?_, fun r hw hq' hy' hd => ?_⟩
  · rw [moveFe_val _ "z" d h3, op.correct _ (by rw [hq, hy]; exact hpre), hq, hy]
  · rw [moveFe_frame _ "z" d r hd, runRBlock64_frame _ _ r (op.writes r hw),
      moveFe_frame _ b "y" r hy', moveFe_frame _ a "q" r hq']

/-! ## A sequence of marshalled field operations -/

/-- One step: the operation, its two source prefixes and its destination prefix. -/
structure Step where
  op : FeOp
  a : String
  b : String
  d : String

/-- The code of a step. -/
def Step.code (st : Step) : List RInst64 := runFe st.op.block st.a st.b st.d

/-- The effect of a step on the field elements, prefix by prefix. -/
def Step.env (st : Step) (e : String → Nat) : String → Nat :=
  Function.update e st.d (st.op.eval (e st.a) (e st.b))

/-- The machine holds the field elements `e` at the prefixes `ps`. -/
def Inv (ps : List String) (s : RState64) (e : String → Nat) : Prop :=
  ∀ p ∈ ps, feV s.get p = e p

/-- The prefixes are disjoint from the field blocks' registers, from the inputs and from each
    other. -/
def PfxOK (ps : List String) : Prop :=
  (∀ p ∈ ps, ∀ r ∈ feNames p, r ∉ fieldWrites ∧ r ∉ feNames "q" ∧ r ∉ feNames "y") ∧
    ∀ p ∈ ps, ∀ p' ∈ ps, p ≠ p' → ∀ r ∈ feNames p, r ∉ feNames p'

instance (ps : List String) : Decidable (PfxOK ps) := by
  unfold PfxOK; infer_instance

/-- A step over the prefixes `ps` is sound. -/
def StepWF (ps : List String) (st : Step) : Prop :=
  StepOK st.a st.b st.d ∧ st.a ∈ ps ∧ st.b ∈ ps ∧ st.d ∈ ps

instance (ps : List String) (st : Step) : Decidable (StepWF ps st) := by
  unfold StepWF; infer_instance

/-- The preconditions of the steps along the run. -/
def Pre : List Step → (String → Nat) → Prop
  | [], _ => True
  | st :: sts, e => st.op.pre (e st.a) (e st.b) ∧ Pre sts (st.env e)

theorem run_step (ps : List String) (hP : PfxOK ps) (st : Step) (hwf : StepWF ps st)
    (s : RState64) (e : String → Nat) (hinv : Inv ps s e) (hpre : st.op.pre (e st.a) (e st.b)) :
    Inv ps (runRBlock64 s st.code) (st.env e) := by
  obtain ⟨hok, ha, hb, hd⟩ := hwf
  rw [← hinv _ ha, ← hinv _ hb] at hpre
  have hstep := runFe_step st.op st.a st.b st.d s hok hpre
  intro p hp
  unfold Step.env Step.code
  by_cases hpd : p = st.d
  · subst hpd
    rw [Function.update_self, hstep.1, hinv _ ha, hinv _ hb]
  · rw [Function.update_of_ne hpd, ← hinv _ hp]
    refine feV_frame fun r hr => hstep.2 r (hP.1 p hp r hr).1 (hP.1 p hp r hr).2.1
      (hP.1 p hp r hr).2.2 (hP.2 p hp st.d hd hpd r hr)

/-- **A sequence of marshalled field operations** leaves the field elements the steps
    compute, prefix by prefix. -/
theorem run_steps (ps : List String) (hP : PfxOK ps) (sts : List Step)
    (hwf : ∀ st ∈ sts, StepWF ps st) (s : RState64) (e : String → Nat) (hinv : Inv ps s e)
    (hpre : Pre sts e) :
    Inv ps (runRBlock64 s (sts.flatMap Step.code)) (sts.foldl (fun e st => st.env e) e) := by
  induction sts generalizing s e with
  | nil => exact hinv
  | cons st sts ih =>
    rw [List.flatMap_cons, runRBlock64_append, List.foldl_cons]
    exact ih (fun st' h => hwf st' (List.mem_cons_of_mem _ h)) _ _
      (run_step ps hP st (hwf st List.mem_cons_self) s e hinv hpre.1) hpre.2

/-! ## The ladder step -/

/-- The field elements of the ladder step: the base, the two points and the scratch. -/
def ladderPfx : List String :=
  ["x1", "x2", "z2", "x3", "z3", "A", "AA", "B", "BB", "E", "C", "D", "DA", "CB", "t0", "t1",
    "t2"]

/-- The eighteen steps of `ladderStepBlock`. -/
def ladderSteps : List Step :=
  [⟨.add, "x2", "z2", "A"⟩, ⟨.sqr, "A", "A", "AA"⟩, ⟨.sub, "x2", "z2", "B"⟩,
    ⟨.sqr, "B", "B", "BB"⟩, ⟨.sub, "AA", "BB", "E"⟩, ⟨.add, "x3", "z3", "C"⟩,
    ⟨.sub, "x3", "z3", "D"⟩, ⟨.mul, "D", "A", "DA"⟩, ⟨.mul, "C", "B", "CB"⟩,
    ⟨.add, "DA", "CB", "t0"⟩, ⟨.sqr, "t0", "t0", "x3"⟩, ⟨.sub, "DA", "CB", "t1"⟩,
    ⟨.sqr, "t1", "t1", "t1"⟩, ⟨.mul, "t1", "x1", "z3"⟩, ⟨.mul, "AA", "BB", "x2"⟩,
    ⟨.a24, "E", "E", "t2"⟩, ⟨.add, "BB", "t2", "t2"⟩, ⟨.mul, "E", "t2", "z2"⟩]

theorem ladderStepBlock_eq : ladderStepBlock = ladderSteps.flatMap Step.code := by
  simp only [ladderStepBlock, ladderSteps, List.flatMap_cons, List.flatMap_nil, Step.code,
    FeOp.block, List.append_nil, List.append_assoc]

theorem ladder_wf : PfxOK ladderPfx ∧ ∀ st ∈ ladderSteps, StepWF ladderPfx st := by
  decide +kernel

theorem ladder_run (s : RState64) (hz2 : feV s.get "z2" ≤ 2 * p25519)
    (hz3 : feV s.get "z3" ≤ 2 * p25519) :
    Inv ladderPfx (runRBlock64 s ladderStepBlock)
      (ladderSteps.foldl (fun e st => st.env e) fun p => feV s.get p) := by
  rw [ladderStepBlock_eq]
  refine run_steps _ ladder_wf.1 _ ladder_wf.2 s _ (fun _ _ => rfl) ?_
  simp only [ladderSteps, Pre, Step.env, FeOp.pre, FeOp.eval, FeOp.evalP, Function.update_apply,
    String.reduceEq, ↓reduceIte, and_true, true_and]
  exact ⟨by omega, (Nat.mod_lt _ p25519_pos).le.trans (by omega), by omega,
    (Nat.mod_lt _ p25519_pos).le.trans (by omega)⟩

/-! ## In the field -/

theorem p25519_P : p25519 = P25519 := rfl

theorem cast_mod (n : Nat) : ((n % p25519 : Nat) : ZMod P25519) = n := by
  rw [p25519_P, ZMod.natCast_mod]

theorem cast_subP (a b : Nat) (h : b ≤ a + 2 * p25519) :
    ((a + 2 * p25519 - b : Nat) : ZMod P25519) = a - b := by
  rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_mul, p25519_P, ZMod.natCast_self]; ring

theorem cast_subP_mod (a b : Nat) :
    ((a + 2 * p25519 - b % p25519 : Nat) : ZMod P25519) = a - b := by
  rw [cast_subP _ _ (by have := Nat.mod_lt b p25519_pos; omega), cast_mod]

/-- The ladder steps over field elements modulo `P`. -/
def Step.envP (P : Nat) (st : Step) (e : String → Nat) : String → Nat :=
  Function.update e st.d (st.op.evalP P (e st.a) (e st.b))

/-- The field elements the ladder steps compute, modulo `P`. -/
def ladderEnvP (P : Nat) (e0 : String → Nat) : String → Nat :=
  ladderSteps.foldl (fun e st => st.envP P e) e0

/-- The ladder step on naturals modulo `P`, in the order of `ladderSteps`. -/
def ladderNat (P x1 x2 z2 x3 z3 : Nat) : Nat × Nat × Nat × Nat :=
  let A := (x2 + z2) % P
  let AA := A * A % P
  let B := (x2 + 2 * P - z2) % P
  let BB := B * B % P
  let E := (AA + 2 * P - BB) % P
  let C := (x3 + z3) % P
  let D := (x3 + 2 * P - z3) % P
  let DA := D * A % P
  let CB := C * B % P
  let t0 := (DA + CB) % P
  let t1 := (DA + 2 * P - CB) % P
  let t1' := t1 * t1 % P
  let t2 := 121666 * E % P
  (AA * BB % P, E * ((BB + t2) % P) % P, t0 * t0 % P, t1' * x1 % P)

theorem ladderEnvP_eq (P : Nat) (e0 : String → Nat) :
    ladderEnvP P e0 "x2" = (ladderNat P (e0 "x1") (e0 "x2") (e0 "z2") (e0 "x3") (e0 "z3")).1 ∧
      ladderEnvP P e0 "z2" = (ladderNat P (e0 "x1") (e0 "x2") (e0 "z2") (e0 "x3") (e0 "z3")).2.1 ∧
      ladderEnvP P e0 "x3" = (ladderNat P (e0 "x1") (e0 "x2") (e0 "z2") (e0 "x3") (e0 "z3")).2.2.1 ∧
      ladderEnvP P e0 "z3" = (ladderNat P (e0 "x1") (e0 "x2") (e0 "z2") (e0 "x3") (e0 "z3")).2.2.2 := by
  simp only [ladderEnvP, ladderSteps, List.foldl_cons, List.foldl_nil, Step.envP, FeOp.evalP,
    Function.update_apply, String.reduceEq, ↓reduceIte, ladderNat, and_self]

/-- **The ladder step on naturals computes double-and-add** in `ZMod p25519`, canonically. -/
theorem ladderNat_correct (x1 x2 z2 x3 z3 : Nat) (st : X25519State)
    (hx1 : fromNat x1 = st.baseX) (hx2 : fromNat x2 = st.x2) (hz2 : fromNat z2 = st.z2)
    (hx3 : fromNat x3 = st.x3) (hz3 : fromNat z3 = st.z3)
    (hz2b : z2 ≤ 2 * p25519) (hz3b : z3 ≤ 2 * p25519) :
    fromNat (ladderNat p25519 x1 x2 z2 x3 z3).1 = (x25519DoubleAndAdd st).x2 ∧
      fromNat (ladderNat p25519 x1 x2 z2 x3 z3).2.1 = (x25519DoubleAndAdd st).z2 ∧
      fromNat (ladderNat p25519 x1 x2 z2 x3 z3).2.2.1 = (x25519DoubleAndAdd st).x3 ∧
      fromNat (ladderNat p25519 x1 x2 z2 x3 z3).2.2.2 = (x25519DoubleAndAdd st).z3 ∧
      (ladderNat p25519 x1 x2 z2 x3 z3).1 < p25519 ∧
      (ladderNat p25519 x1 x2 z2 x3 z3).2.1 < p25519 ∧
      (ladderNat p25519 x1 x2 z2 x3 z3).2.2.1 < p25519 ∧
      (ladderNat p25519 x1 x2 z2 x3 z3).2.2.2 < p25519 := by
  have b2 : z2 ≤ x2 + 2 * p25519 := by omega
  have b3 : z3 ≤ x3 + 2 * p25519 := by omega
  simp only [ladderNat]
  refine ⟨?_, ?_, ?_, ?_, Nat.mod_lt _ p25519_pos, Nat.mod_lt _ p25519_pos,
    Nat.mod_lt _ p25519_pos, Nat.mod_lt _ p25519_pos⟩
  all_goals simp only [x25519DoubleAndAdd, x25519A24, ← hx1, ← hx2, ← hz2, ← hx3, ← hz3, fromNat,
    cast_mod, cast_subP_mod, cast_subP _ _ b2, cast_subP _ _ b3, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]
  all_goals ring

/-- **The ladder step computes RFC 7748 double-and-add.** For every machine state holding
    the base `x1` and the points `(x2 : z2)`, `(x3 : z3)` at their prefixes, with `z2` and
    `z3` at most `2·p25519`, running `ladderStepBlock` leaves the four coordinates of
    `x25519DoubleAndAdd`, canonical. -/
theorem ladderStep_correct (s : RState64) (st : X25519State)
    (hx1 : fromNat (feAt s "x1") = st.baseX) (hx2 : fromNat (feAt s "x2") = st.x2)
    (hz2 : fromNat (feAt s "z2") = st.z2) (hx3 : fromNat (feAt s "x3") = st.x3)
    (hz3 : fromNat (feAt s "z3") = st.z3)
    (hz2b : feAt s "z2" ≤ 2 * p25519) (hz3b : feAt s "z3" ≤ 2 * p25519) :
    fromNat (feAt (runRBlock64 s ladderStepBlock) "x2") = (x25519DoubleAndAdd st).x2 ∧
      fromNat (feAt (runRBlock64 s ladderStepBlock) "z2") = (x25519DoubleAndAdd st).z2 ∧
      fromNat (feAt (runRBlock64 s ladderStepBlock) "x3") = (x25519DoubleAndAdd st).x3 ∧
      fromNat (feAt (runRBlock64 s ladderStepBlock) "z3") = (x25519DoubleAndAdd st).z3 ∧
      feAt (runRBlock64 s ladderStepBlock) "x2" < p25519 ∧
      feAt (runRBlock64 s ladderStepBlock) "z2" < p25519 ∧
      feAt (runRBlock64 s ladderStepBlock) "x3" < p25519 ∧
      feAt (runRBlock64 s ladderStepBlock) "z3" < p25519 := by
  simp only [feAt_eq] at *
  have h : Inv ladderPfx (runRBlock64 s ladderStepBlock) (ladderEnvP p25519 fun p => feV s.get p) :=
    ladder_run s hz2b hz3b
  obtain ⟨v1, v2, v3, v4⟩ := ladderEnvP_eq p25519 fun p => feV s.get p
  obtain ⟨c1, c2, c3, c4, l1, l2, l3, l4⟩ :=
    ladderNat_correct _ _ _ _ _ st hx1 hx2 hz2 hx3 hz3 hz2b hz3b
  exact ⟨(congrArg fromNat ((h "x2" (by decide)).trans v1)).trans c1,
    (congrArg fromNat ((h "z2" (by decide)).trans v2)).trans c2,
    (congrArg fromNat ((h "x3" (by decide)).trans v3)).trans c3,
    (congrArg fromNat ((h "z3" (by decide)).trans v4)).trans c4,
    ((h "x2" (by decide)).trans v1).trans_lt l1, ((h "z2" (by decide)).trans v2).trans_lt l2,
    ((h "x3" (by decide)).trans v3).trans_lt l3, ((h "z3" (by decide)).trans v4).trans_lt l4⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof.ladderStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ladderStep_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof
