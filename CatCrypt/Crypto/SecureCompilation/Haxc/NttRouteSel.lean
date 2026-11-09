/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain
public import CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
public import CatCrypt.Crypto.SecureCompilation.VIR.BoundSched

@[expose] public section

set_option autoImplicit false

/-!
# The NTT route selected by the bounds certificate at the modulus

The NTT templates on words are the signed Montgomery transform `nttProgSW` and the
unsigned lazy transform `nttProgUW` on lanes of a schedule's width (`WordSched`,
`nttProgG`), and the lazy transform `nttProgW` on 64-bit lanes. An arm `NttArm` is one
of them; `NttArm.prog P A` is its program on `2 ^ P.logN` lanes of 64-bit words, the
narrow arms between the casts `castLanes 64 w` and `castLanes w 64`. The route program
of an arm is the run of the lane chain `FieldChain.lanesChain` on that program.

The selection `nttArmOf P S logR` is generic in the modulus. It takes the signed
schedule on 16-bit words `signedOf P.q 16` when its certificate `WordSched.Ok` holds at
`P` (as at ML-KEM, `q = 3329`), else the unsigned lazy schedule on 32-bit words
`lazyOf P.q 32` when its certificate holds (as at ML-DSA and Falcon), and the 64-bit
lazy schedule `S` of radix `2 ^ logR` otherwise. The Montgomery constants of the two
schedules are computed from `q` by `invPow2`; the certificates check them.

An output word of an arm is read as an integer by `NttArm.read`: the signed value of its
low `w` bits at the signed arm, its unsigned value otherwise.

## Main results

* `castLanes_denote`, `hvGetG_castLanes`: the casts on lanes.
* `NttArm.prog_denote`: the output lanes of the program of an arm satisfying its
  certificate, below the arm's bound and congruent to `nttSpec` of the input.
* `nttRouteOf`, `lanesChain_run_arm`, `nttRouteOf_denote`: the route program of an arm,
  the lane chain running to it, and its output words.
* `nttArmOf`, `nttArmOf_ok`, `nttRouteSel`, `nttRouteSel_denote`: the selection, its
  certificate from the certificate of the 64-bit fallback, and the selected route with
  its output words.
* `nttArmOf_mlkem`, `nttArmOf_mldsa`: the selection takes the signed 16-bit arm at
  ML-KEM and the unsigned 32-bit arm at ML-DSA.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord (laneMapW laneMapW_denote)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact (mrSeq mrSeq_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx lanesCom arrLimbs_eq_lanesVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain (lanesChain lanesChain_run
  lanesChain_denote)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (gvnMR)

/-! ## 1. Casts on lanes -/

section Cast

/-- Lane `i` of `n` lanes of `w`-bit words cast to `w'` bits. -/
def castLane (w w' : ℕ) : (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (Rw w')
  | 0, _ => .var (constE w' 0) (.ret .here)
  | n + 1, i => .var (castE w w' (laneVarG (Rw w) n i)) (.ret .here)

/-- The casts of `N` lanes of `w`-bit words to `w'` bits. -/
def castLanes (w w' N : ℕ) : MultiReturnCom jasminDialect (Ctxs w N) (Ctxs w' N) :=
  laneMapW N (castLane w w' N)

theorem castLane_denote (w w' N : ℕ) (g : ℕ → BitVec w) (i : ℕ) (hi : i < N) :
    (castLane w w' N i).denote (lanesVal (Rw w) g N 0) = (g i).setWidth w' := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  show ((laneVarG (Rw w) n i).lookup (lanesVal (Rw w) g (n + 1) 0)).zeroExtend w' = _
  rw [laneVarG_lookup (Rw w) g n i 0 (by omega), Nat.zero_add]

/-- **The casts on lanes**: lane `j` of the output is lane `j` of the input cast. -/
theorem castLanes_denote (w w' N : ℕ) (g : ℕ → BitVec w) :
    (castLanes w w' N).denote (lanesVal (Rw w) g N 0)
      = lanesVal (Rw w') (fun j => (g j).setWidth w') N 0 := by
  rw [castLanes, laneMapW_denote]
  refine eq_lanesVal (Rw w') (0 : BitVec w') _ N 0 _ fun i hi => ?_
  rw [hvGetG_denoteN _ _ _ _ _ _ hi, castLane_denote w w' N g i hi, Nat.zero_add]

/-- Lane `i` of the casts of a valuation is lane `i` of the valuation cast. -/
theorem hvGetG_castLanes (w w' N : ℕ) (X : Valuation (Ctxs w N)) (i : ℕ) (hi : i < N) :
    hvGetG (Rw w') (0 : BitVec w') ((castLanes w w' N).denote X) i
      = (hvGetG (Rw w) (0 : BitVec w) X i).setWidth w' := by
  have hX : X = lanesVal (Rw w) (fun j => hvGetG (Rw w) (0 : BitVec w) X j) N 0 :=
    eq_lanesVal (Rw w) (0 : BitVec w) _ N 0 X fun j _ => by rw [Nat.zero_add]
  rw [hX, castLanes_denote, hvGetG_lanesVal _ _ _ _ _ _ hi, hvGetG_lanesVal _ _ _ _ _ _ hi]

/-- A program on `N` lanes of `w`-bit words, run on `N` lanes of 64-bit words: the
    inputs cast to `w` bits, the program, and its outputs cast to `64` bits. -/
def widenProg (w N : ℕ) (m : MultiReturnCom jasminDialect (Ctxs w N) (Ctxs w N)) :
    MultiReturnCom jasminDialect (Rn N) (Rn N) :=
  mrSeq (castLanes 64 w N) (mrSeq m (castLanes w 64 N))

theorem hvGetG_widenProg (w N : ℕ) (m : MultiReturnCom jasminDialect (Ctxs w N) (Ctxs w N))
    (g : ℕ → BitVec 64) (i : ℕ) (hi : i < N) :
    hvGetG R64 (0 : BitVec 64) ((widenProg w N m).denote (lanesVal R64 g N 0)) i
      = (hvGetG (Rw w) (0 : BitVec w) (m.denote
          (lanesVal (Rw w) (fun j => (g j).setWidth w) N 0)) i).setWidth 64 := by
  rw [widenProg, mrSeq_denote, mrSeq_denote]
  erw [castLanes_denote 64 w N g]
  exact hvGetG_castLanes w 64 N _ i hi

end Cast

/-! ## 2. The arms -/

/-- **An arm of the NTT route**: a word schedule on lanes of its width, or a lazy schedule
    of radix `2 ^ logR` on 64-bit lanes. -/
inductive NttArm where
  /-- The word schedule `s` on `s.width`-bit lanes (`nttProgG`). -/
  | word (s : WordSched)
  /-- The lazy schedule `S` of radix `2 ^ logR` on 64-bit lanes (`nttProgW`). -/
  | wide (S : LazySched) (logR : ℕ)

namespace NttArm

variable (P : NttParams)

/-- The program of an arm on `2 ^ P.logN` lanes of 64-bit words. -/
def prog : NttArm → MultiReturnCom jasminDialect (Rn (2 ^ P.logN)) (Rn (2 ^ P.logN))
  | .word s => widenProg s.width (2 ^ P.logN) (nttProgG P s)
  | .wide S logR => nttProgW P S logR

/-- The certificate of an arm, decidable on `ℕ` at a word schedule. -/
def Ok : NttArm → Prop
  | .word s => s.Ok P ∧ s.width ≤ 64
  | .wide S logR => SchedOk P S ∧ WordOk P S logR

/-- The integer an output word of an arm stands for: the value of its low `w` bits as the
    word schedule reads them, or its unsigned value. -/
def read : NttArm → BitVec 64 → ℤ
  | .word s, x => s.val (x.setWidth s.width)
  | .wide _ _, x => (x.toNat : ℤ)

/-- The bound on the absolute value of every output word of an arm. -/
def bound : NttArm → ℕ
  | .word s => s.bound P
  | .wide S _ => bnd P S P.layers

/-- **The output lanes of the program of an arm.** For a parameter record satisfying
    `NttParams.Ok`, an arm satisfying its certificate, and input words below `q`, every
    output word read by the arm is below the arm's bound in absolute value and congruent
    modulo `q` to `nttSpec` of the input. -/
theorem prog_denote (hP : P.Ok) (A : NttArm) (hA : A.Ok P) (g : ℕ → BitVec 64)
    (hg : ∀ j, (g j).toNat < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    |A.read (hvGetG R64 (0 : BitVec 64) ((A.prog P).denote (lanesVal R64 g (2 ^ P.logN) 0)) i)|
        < A.bound P ∧
    ((A.read (hvGetG R64 (0 : BitVec 64)
        ((A.prog P).denote (lanesVal R64 g (2 ^ P.logN) 0)) i) : ℤ) : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => ((g j).toNat : ZMod P.q)) i := by
  cases A with
  | word s =>
    obtain ⟨hs, hw⟩ := hA
    have hin : (fun j => (g j).setWidth s.width) = fun j => BitVec.ofNat s.width (g j).toNat :=
      funext fun j => (BitVec.ofNat_toNat _ _).symm
    simp only [read, prog, bound]
    rw [hvGetG_widenProg _ _ _ g i hi, BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq,
      hin]
    exact nttProgG_denote P hP s hs (fun j => (g j).toNat) hg i hi
  | wide S logR =>
    obtain ⟨hS, hW⟩ := hA
    have hin : g = fun j => BitVec.ofNat 64 (g j).toNat := funext fun j => by simp
    simp only [read, prog, bound]
    rw [congrArg (fun g => lanesVal R64 g (2 ^ P.logN) 0) hin]
    obtain ⟨h1, h2⟩ := nttProgW_denote P S logR hP hS hW (fun j => (g j).toNat) hg i hi
    refine ⟨?_, ?_⟩
    · rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast h1
    · rw [Int.cast_natCast]
      exact h2

end NttArm

/-! ## 3. The route program of an arm -/

section Route

variable (P : NttParams) (pure : jasminDialect.Op → Bool)

/-- **The route program of an arm**: the run of the lane chain `lanesChain` (the value
    numbering `gvnMR pure`, the lane lowering and the route wrapper) on the arm's
    program. -/
def nttRouteOf (A : NttArm) : RouteProg (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN)) :=
  ((lanesChain (2 ^ P.logN) pure).run (A.prog P)).get rfl

/-- The lane chain runs on the program of an arm to its route program. -/
theorem lanesChain_run_arm (A : NttArm) :
    (lanesChain (2 ^ P.logN) pure).run (A.prog P) = some (nttRouteOf P pure A) :=
  (Option.some_get _).symm

/-- **The output words of the route program of an arm**, from the certificate of the lane
    chain: for input words below `q`, every output word read by the arm is below the arm's
    bound in absolute value and congruent modulo `q` to `nttSpec` of the input words. -/
theorem nttRouteOf_denote (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (A : NttArm) (hA : A.Ok P)
    (a o : Fin (2 ^ P.logN) → BitVec 64) (ha : ∀ j, (stackGet a j).toNat < P.q) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    |A.read (stackGet ((nttRouteOf P pure A).denote (.cons a (.cons o .nil))) i)| < A.bound P ∧
    ((A.read (stackGet ((nttRouteOf P pure A).denote (.cons a (.cons o .nil))) i) : ℤ)
        : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN
          (fun j => ((stackGet a j).toNat : ZMod P.q)) i := by
  have h := lanesChain_denote hN pure (lanesChain_run_arm P pure A) a o
  have e : stackGet ((nttRouteOf P pure A).denote (.cons a (.cons o .nil))) i
      = hvGetG R64 (0 : BitVec 64) ((A.prog P).denote
          (lanesVal R64 (fun j => stackGet a j) (2 ^ P.logN) 0)) i := by
    rw [← arrLimbs_eq_lanesVal, ← h, arrLimbs_eq_lanesVal, hvGetG_lanesVal _ _ _ _ _ _ hi,
      Nat.zero_add]
  rw [e]
  exact NttArm.prog_denote P hP A hA _ ha i hi

end Route

/-! ## 4. The selection -/

/-- The inverse of `q` modulo `2 ^ w` by six Newton steps from `q`; correct for odd `q`
    and `w ≤ 192`. -/
def invPow2 (q w : ℕ) : ℕ :=
  Nat.repeat (fun x => x * (2 ^ w + 2 - q * x % 2 ^ w) % 2 ^ w) 6 (q % 2 ^ w)

/-- The signed schedule on `w`-bit lanes at the modulus `q`: Montgomery constant
    `q⁻¹ mod 2 ^ w` and bound `(ℓ + 1) · q` after `ℓ` layers. -/
def signedOf (q w : ℕ) : SignedSched := ⟨w, invPow2 q w, fun ℓ => (ℓ + 1) * q⟩

/-- The lazy schedule on `w`-bit lanes at the modulus `q`: radix `2 ^ w`, Montgomery
    constant `−q⁻¹ mod 2 ^ w`, offset `2 q`, no reduced layer. -/
def lazyOf (q w : ℕ) : LazySched := ⟨2 ^ w, 2 ^ w - invPow2 q w, 2, fun _ => false, w⟩

variable (P : NttParams)

/-- **The arm selected by the certificates at the modulus**: the signed 16-bit arm when
    its certificate holds, else the unsigned 32-bit arm when its certificate holds, else
    the 64-bit arm of the lazy schedule `S` of radix `2 ^ logR`. -/
def nttArmOf (S : LazySched) (logR : ℕ) : NttArm :=
  if (WordSched.signedMont (signedOf P.q 16)).Ok P then .word (.signedMont (signedOf P.q 16))
  else if (WordSched.unsignedMont (lazyOf P.q 32) 32).Ok P then
    .word (.unsignedMont (lazyOf P.q 32) 32)
  else .wide S logR

/-- The selected arm satisfies its certificate when the 64-bit fallback does. -/
theorem nttArmOf_ok (S : LazySched) (logR : ℕ) (hS : SchedOk P S) (hW : WordOk P S logR) :
    (nttArmOf P S logR).Ok P := by
  unfold nttArmOf
  split
  · next h => exact ⟨h, show 16 ≤ 64 by omega⟩
  · split
    · next h => exact ⟨h, show 32 ≤ 64 by omega⟩
    · exact ⟨hS, hW⟩

/-- **The NTT route**: the route program of the selected arm. -/
def nttRouteSel (pure : jasminDialect.Op → Bool) (S : LazySched) (logR : ℕ) :
    RouteProg (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN)) :=
  nttRouteOf P pure (nttArmOf P S logR)

/-- **The output words of the NTT route.** For a parameter record satisfying
    `NttParams.Ok`, a 64-bit fallback schedule satisfying `SchedOk` and `WordOk`, and
    input words below `q`, every output word, read by the selected arm, is below that
    arm's bound in absolute value and congruent modulo `q` to `nttSpec` of the input
    words. -/
theorem nttRouteSel_denote (pure : jasminDialect.Op → Bool) (S : LazySched) (logR : ℕ)
    (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (hS : SchedOk P S) (hW : WordOk P S logR)
    (a o : Fin (2 ^ P.logN) → BitVec 64) (ha : ∀ j, (stackGet a j).toNat < P.q) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    |(nttArmOf P S logR).read
        (stackGet ((nttRouteSel P pure S logR).denote (.cons a (.cons o .nil))) i)|
        < (nttArmOf P S logR).bound P ∧
    (((nttArmOf P S logR).read
        (stackGet ((nttRouteSel P pure S logR).denote (.cons a (.cons o .nil))) i) : ℤ)
        : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN
          (fun j => ((stackGet a j).toNat : ZMod P.q)) i :=
  nttRouteOf_denote P pure hN hP _ (nttArmOf_ok P S logR hS hW) a o ha i hi

/-- At ML-KEM the selection takes the signed 16-bit arm, whose schedule is the reference
    schedule `mlkemSigned`. -/
theorem nttArmOf_mlkem (S : LazySched) (logR : ℕ) :
    nttArmOf mlkemNtt S logR = .word (.signedMont mlkemSigned) := by
  rw [nttArmOf, ite_eq_left (by decide)]
  rfl

/-- At ML-DSA the selection takes the unsigned 32-bit arm, whose schedule is `mldsaLazy`. -/
theorem nttArmOf_mldsa (S : LazySched) (logR : ℕ) :
    nttArmOf mldsaNtt S logR = .word (.unsignedMont mldsaLazy 32) := by
  rw [nttArmOf, ite_eq_right (by decide), ite_eq_left (by decide)]
  rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NttRouteSel
