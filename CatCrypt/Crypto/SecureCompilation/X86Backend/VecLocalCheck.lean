/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelMixedLink

@[expose] public section

set_option autoImplicit false

/-!
# A check that a vector-kernel block is vector-local

A block of scalar operations and vector instructions is vector-local when every vector
register and every mask register that a vector instruction of the block reads is written by
an earlier instruction of the block. `vecLocalCheck` decides this by a fold over the block
that keeps the registers written so far. From two entry states with the same scalar part,
the runs of an accepted block keep the same scalar part and agree on the registers written
so far; the scalar state and the leakage after the block therefore do not depend on the
entry vector state (`VecKernelMixedLink.VecLocalOn`, for every precondition).

## Main definitions

* `vReadsZ`, `vReadsK`, `vWritesZ`, `vWritesK`: the vector and mask registers a vector
  instruction reads and writes.
* `vecLocalCheckFrom`, `vecLocalCheck`: the check over a block, from given sets of written
  registers and from the empty sets.
* `VAgree`: two vector states agree on given sets of vector and mask registers.

## Main results

* `vexec_agree`: a vector instruction whose reads are in the agreed sets keeps the scalar
  state equal and extends the agreement by its writes.
* `runBlock_agree`: the simulation over an accepted block.
* `vecLocalCheck_sound`: an accepted block satisfies `VecLocalOn` for every precondition.
* `kernelRun_vecLocal_of_check`: the callee `kernelRun` of an accepted block is vector-local.
* `VecKernelCallee.cpu_link_of_check`: `VecKernelMixedLink.cpu_link` for a spec-carrying
  kernel whose callee is `kernelRun` of an accepted block.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecLocalCheck

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelMixedLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
  (CalleeRun CalleeSig CalleeSpec HaltsO oracleAt)
open CatCrypt.Crypto.SecureCompilation.CT

variable {r : DoitRegime} {m : Mode}

/-! ## 1. The registers of a vector instruction -/

/-- The vector registers a vector instruction reads. `vzeroupper` maps each register to a
    function of itself and is given no reads. -/
def vReadsZ : VInstr → List (Fin 32)
  | .ld _ _ => []
  | .st src _ => [src]
  | .op _ _ s2 s1 _ => [s2, s1]
  | .shi _ _ _ src _ => [src]
  | .dup _ src _ none => [src]
  | .dup _ src d (some _) => [src, d]
  | .mova src _ => [src]
  | .perm x i _ => [x, i]
  | .blend _ a b _ => [a, b]
  | .rol _ _ src _ => [src]
  | .tern _ _ s3 s2 d => [d, s2, s3]
  | .ldK _ _ => []
  | .opK _ _ _ s1 _ => [s1]
  | .kmov _ => []
  | .zeroUpper => []

/-- The mask registers a vector instruction reads. -/
def vReadsK : VInstr → List (Fin 8)
  | .dup _ _ _ (some k) => [k]
  | .blend k _ _ _ => [k]
  | _ => []

/-- The vector register a vector instruction writes. -/
def vWritesZ : VInstr → List (Fin 32)
  | .ld _ d => [d]
  | .op _ _ _ _ d => [d]
  | .shi _ _ _ _ d => [d]
  | .dup _ _ d _ => [d]
  | .mova _ d => [d]
  | .perm _ _ d => [d]
  | .blend _ _ _ d => [d]
  | .rol _ _ _ d => [d]
  | .tern _ _ _ _ d => [d]
  | .ldK _ d => [d]
  | .opK _ _ _ _ d => [d]
  | _ => []

/-- The mask register a vector instruction writes. -/
def vWritesK : VInstr → List (Fin 8)
  | .kmov k => [k]
  | _ => []

/-! ## 2. The check -/

/-- **Every register a vector instruction of the block reads is written before**, from the
    vector registers `Z` and the mask registers `K` written so far. Scalar operations are
    not inspected. -/
def vecLocalCheckFrom (Z : List (Fin 32)) (K : List (Fin 8)) :
    List (JInstr 64 ⊕ VInstr) → Bool
  | [] => true
  | .inl _ :: ops => vecLocalCheckFrom Z K ops
  | .inr v :: ops =>
      (vReadsZ v).all (fun x => decide (x ∈ Z)) && (vReadsK v).all (fun k => decide (k ∈ K)) &&
        vecLocalCheckFrom (vWritesZ v ++ Z) (vWritesK v ++ K) ops

/-- **Every vector and mask register a vector instruction of the block reads is written
    earlier in the block.** -/
def vecLocalCheck (ops : List (JInstr 64 ⊕ VInstr)) : Bool :=
  vecLocalCheckFrom [] [] ops

/-! ## 3. The simulation -/

/-- Two vector states agree on the vector registers `Z` and the mask registers `K`. -/
def VAgree (Z : List (Fin 32)) (K : List (Fin 8)) (v w : VState) : Prop :=
  (∀ z ∈ Z, v.zmm z = w.zmm z) ∧ ∀ k ∈ K, v.kr k = w.kr k

theorem VAgree.setZ {Z : List (Fin 32)} {K : List (Fin 8)} {v w : VState}
    (h : VAgree Z K v w) (d : Fin 32) {x y : BitVec 512} (hxy : x = y) :
    VAgree (d :: Z) K (v.setZ d x) (w.setZ d y) := by
  refine ⟨fun z hz => ?_, h.2⟩
  simp only [VState.setZ]
  split
  · exact hxy
  · exact h.1 z ((List.mem_cons.mp hz).resolve_left ‹_›)

/-- **A vector instruction whose reads are agreed keeps the scalar state equal and extends
    the agreement by its writes.** -/
theorem vexec_agree {Z : List (Fin 32)} {K : List (Fin 8)} (i : VInstr)
    (hZ : ∀ z ∈ vReadsZ i, z ∈ Z) (hK : ∀ k ∈ vReadsK i, k ∈ K)
    (s : AState) {v w : VState} (h : VAgree Z K v w) :
    (vexec m (s, v) i).1 = (vexec m (s, w) i).1 ∧
      VAgree (vWritesZ i ++ Z) (vWritesK i ++ K) (vexec m (s, v) i).2 (vexec m (s, w) i).2 := by
  cases i with
  | ld a d => exact ⟨rfl, h.setZ d rfl⟩
  | st src a =>
    refine ⟨?_, h⟩
    simp only [vexec, h.1 src (hZ src (by simp [vReadsZ]))]
  | op L o s2 s1 d =>
    refine ⟨rfl, h.setZ d ?_⟩
    rw [h.1 s1 (hZ s1 (by simp [vReadsZ])), h.1 s2 (hZ s2 (by simp [vReadsZ]))]
  | shi L l imm src d => exact ⟨rfl, h.setZ d (by rw [h.1 src (hZ src (by simp [vReadsZ]))])⟩
  | dup odd src d mask =>
    cases mask with
    | none => exact ⟨rfl, h.setZ d (by rw [h.1 src (hZ src (by simp [vReadsZ]))])⟩
    | some k =>
      refine ⟨rfl, h.setZ d ?_⟩
      rw [h.1 src (hZ src (by simp [vReadsZ])), h.1 d (hZ d (by simp [vReadsZ])),
        h.2 k (hK k (by simp [vReadsK]))]
  | mova src d => exact ⟨rfl, h.setZ d (by rw [h.1 src (hZ src (by simp [vReadsZ]))])⟩
  | perm x idx d =>
    refine ⟨rfl, h.setZ d ?_⟩
    rw [h.1 x (hZ x (by simp [vReadsZ])), h.1 idx (hZ idx (by simp [vReadsZ]))]
  | blend k a b d =>
    refine ⟨rfl, h.setZ d ?_⟩
    rw [h.1 a (hZ a (by simp [vReadsZ])), h.1 b (hZ b (by simp [vReadsZ])),
      h.2 k (hK k (by simp [vReadsK]))]
  | rol L imm src d => exact ⟨rfl, h.setZ d (by rw [h.1 src (hZ src (by simp [vReadsZ]))])⟩
  | tern L imm s3 s2 d =>
    refine ⟨rfl, h.setZ d ?_⟩
    rw [h.1 d (hZ d (by simp [vReadsZ])), h.1 s2 (hZ s2 (by simp [vReadsZ])),
      h.1 s3 (hZ s3 (by simp [vReadsZ]))]
  | ldK x d => exact ⟨rfl, h.setZ d rfl⟩
  | opK L o x s1 d => exact ⟨rfl, h.setZ d (by rw [h.1 s1 (hZ s1 (by simp [vReadsZ]))])⟩
  | kmov k =>
    refine ⟨rfl, h.1, fun k' hk' => ?_⟩
    simp only [vexec]
    split
    · rfl
    · exact h.2 k' (by simpa [vWritesK, *] using hk')
  | zeroUpper =>
    refine ⟨rfl, fun z hz => ?_, h.2⟩
    simp only [vexec]
    rw [h.1 z (by simpa [vWritesZ] using hz)]

/-- **The simulation over an accepted block.** From two states with the same scalar part
    and vector states agreeing on the registers written so far, an accepted block ends in
    the same scalar state with the same leakage. -/
theorem runBlock_agree :
    ∀ (ops : List (JInstr 64 ⊕ VInstr)) (Z : List (Fin 32)) (K : List (Fin 8))
      (s : AState) (v w : VState), vecLocalCheckFrom Z K ops = true → VAgree Z K v w →
      ((x86VecMach r m).runBlock (s, v) ops).1 = ((x86VecMach r m).runBlock (s, w) ops).1 ∧
        (x86VecMach r m).blockLeak (s, v) ops = (x86VecMach r m).blockLeak (s, w) ops
  | [], _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | .inl i :: ops, Z, K, s, v, w, hc, h => by
    have ih := runBlock_agree ops Z K (aMachine.exec s i) v w hc h
    exact ⟨ih.1, congrArg (DecodedCT.opLeak r s i ++ ·) ih.2⟩
  | .inr i :: ops, Z, K, s, v, w, hc, h => by
    simp only [vecLocalCheckFrom, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hZ, hK⟩, hc⟩ := hc
    obtain ⟨hs, hv⟩ := vexec_agree (m := m) i hZ hK s h
    have ih := runBlock_agree ops _ _ (vexec m (s, v) i).1
      (vexec m (s, v) i).2 (vexec m (s, w) i).2 hc hv
    have e1 : vexec m (s, v) i = ((vexec m (s, v) i).1, (vexec m (s, v) i).2) := rfl
    have e2 : vexec m (s, w) i = ((vexec m (s, v) i).1, (vexec m (s, w) i).2) :=
      Prod.ext hs.symm rfl
    show ((x86VecMach r m).runBlock (vexec m (s, v) i) ops).1
        = ((x86VecMach r m).runBlock (vexec m (s, w) i) ops).1 ∧
      vLeak s.regs i ++ (x86VecMach r m).blockLeak (vexec m (s, v) i) ops
        = vLeak s.regs i ++ (x86VecMach r m).blockLeak (vexec m (s, w) i) ops
    rw [e2, e1]
    exact ⟨ih.1, congrArg (vLeak s.regs i ++ ·) ih.2⟩

/-- **An accepted block is vector-local**: the scalar state and the leakage after it do not
    depend on the entry vector state, for every precondition. -/
theorem vecLocalCheck_sound {pre : AState → Prop} {ops : List (JInstr 64 ⊕ VInstr)}
    (hc : vecLocalCheck ops = true) : VecLocalOn r m pre ops :=
  fun s _ v w => runBlock_agree ops [] [] s v w hc ⟨by simp, by simp⟩

/-- **The callee `kernelRun` of an accepted block is vector-local.** -/
theorem kernelRun_vecLocal_of_check {ops : List (JInstr 64 ⊕ VInstr)}
    (hc : vecLocalCheck ops = true) : VecLocalRun r m ops (kernelRun r m ops) := by
  intro s t s' hX v
  obtain ⟨v₀, hs', -⟩ := (kernelRun_iff r m ops s t s').mp hX
  rw [runBlock_zeroUpper_fst, hs',
    ((vecLocalCheck_sound (pre := fun _ => True) hc) s trivial v v₀).1]

/-! ## 4. The link of an accepted kernel -/

/-- **The vector-local callee of a spec-carrying kernel with an accepted block meets its
    signature**, when the callee of the record is `kernelRun` of its block. -/
theorem VecKernelCallee.spec_local_of_check {sig : CalleeSig} (k : VecKernelCallee r m sig)
    (hrun : k.run = kernelRun r m k.ops) (hc : vecLocalCheck k.ops = true) :
    CalleeSpec (kernelRunL r m k.ops) sig :=
  VecKernelMixedLink.VecKernelCallee.spec_local k hrun (vecLocalCheck_sound hc)

/-- **A faithful processor runs a caller linked with a spec-carrying kernel whose block is
    accepted.** Let the callee of the record be `kernelRun` of its block, and let the caller
    `prog` run from index `0` in `s` to `s'` under the oracle that answers a call to
    `prog.length` by the callee of the record. Then the processor runs the caller bytes
    followed by the kernel bytes from `(s, v)` to `(s', v')`, for every entry vector state
    `v` and some `v'`. -/
theorem VecKernelCallee.cpu_link_of_check {sig : CalleeSig} (k : VecKernelCallee r m sig)
    (hrun : k.run = kernelRun r m k.ops) (hc : vecLocalCheck k.ops = true) {A : VecAsm}
    {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}
    (hA : A.Lawful) (hF : A.Faithful r m cpu) (hbe : BlockEncodable A k.ops)
    (henc : ∀ i, Sum.inl i ∈ k.ops → ItemOK (scalarItem frameEnc i)) {items : List Item}
    (hok : ∀ it ∈ items, ItemOK it) {prog : List RInstr}
    (hres : ∀ e x tl, resolveAll (layoutAt 0 items ++ ((itemBytes items).length, e, x) :: tl)
      (layoutAt 0 items) = some prog) {s s' : AState}
    (h : HaltsO aMachine (oracleAt prog.length k.run) prog 0 s s') (v : VState) :
    ∃ v' : VState, cpu (itemBytes items ++ lineBytes A frameEnc k.ops) (s, v) (s', v') := by
  rw [hrun] at h
  exact VecKernelMixedLink.cpu_link hA hF hok hres frameEnc henc hbe
    (kernelRun_vecLocal_of_check hc) h v

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecLocalCheck
