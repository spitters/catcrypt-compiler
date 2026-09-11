/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

@[expose] public section

set_option autoImplicit false

/-!
# The array-carrier counted loop at an arbitrary update body

`JasminLsemMemSourceTieUncond` discharges the per-trip simulation of a counted
loop unconditionally at a **scalar** accumulator, for the linearizer chain of an
arbitrary `ScalarMemN` update (`loopBodyFullMN_trip`), and at an **array**
accumulator only for the fixed fill shape `out[i] := a[i]` (`fillBodyM_trip`).
This module supplies the array-carrier analogue of the scalar result: the update
body is an arbitrary member of the array-returning stack-memory fragment, and
the emitted `chain ++ writeback` loop body's per-trip simulation is proved.

The fragment `ArrMemN` is a chain of register-producing `ScalarMemN` heads and
`stackStore` bindings terminated by a `.ret` at an array variable. Its emitted
chain is `straightOpsMem`, exactly as in the scalar case, so each `stackStore`
binding writes a **fresh** array slot `regName curDepth`. The writeback then
copies the chain's return array into the accumulator argument's slot: a
`LOADIDX` of one cell of the return array followed by a `STOREIDX` of that cell
back into the accumulator slot with the return array as source, which by
`stackSet_stackGet_self` transfers the whole array.

## Main results

* `ArrMemN` — the array-returning stack-memory source fragment, over the
  register heads admitted by `ScalarMemN` (`RegHeadMemN`) and `stackStore`.
* `ArrMemN.straightOps_full` — the emitted chain of an `ArrMemN` update runs,
  touches only the fresh `regName` block, and leaves `Com.denote` at the
  return array slot.
* `loopBodyArrFullMN` — the emitted array-carrier loop body: the `straightOpsMem`
  chain, the array writeback into the accumulator argument, the loop-index
  increment, the counter decrement.
* `loopBodyArrFullMN_trip` — one pass of that body from any state agreeing with
  the trip valuation computes one `JLoopBodyN.stepC`.
* `loopBodyArrFullMN_inv` — the trip invariant: every trip state agrees with the
  source fold at its trip valuation.
* `loopMemArr_export_faithful_denote_uncond` — export faithfulness at the array
  cells with no per-trip simulation hypothesis: only the counter schedule, the
  seed, and the counter-name hygiene.
* `loopMemArr_export_faithful_comL_uncond` — the same, concluded at the front
  node `ComL.forLoopNRt`'s denotation.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

variable {invTys : Ctxt jasminDialect}

/-! ## 1. Bricks: the self-store identity and frame composition -/

/-- Storing into a cell the value that cell already holds is the identity on the
    array. -/
theorem stackSet_stackGet_self {w n : Nat} (arr : Fin n → BitVec w) (k : Nat) :
    stackSet arr k (stackGet arr k) = arr := by
  cases n with
  | zero => funext j; exact Fin.elim0 j
  | succ m =>
      funext j
      show (if j = _ then _ else arr j) = arr j
      split
      · next h => subst h; rfl
      · rfl

/-- Two chains, the second rooted one binder deeper than the first, compose into
    one write frame at the outer depth. -/
theorem WriteFrame.comp {d : Nat} {s s1 s2 : LstateM}
    (h1 : WriteFrame d s s1) (h2 : WriteFrame (d + 1) s1 s2) : WriteFrame d s s2 :=
  ⟨fun r w hr => (h2.1 r w (fun k hk => hr k (by omega))).trans (h1.1 r w hr),
   fun r w n hr => (h2.2 r w n (fun k hk => hr k (by omega))).trans (h1.2 r w n hr)⟩

/-! ## 2. The array-returning stack-memory fragment -/

/-- A single register-producing binding admitted by the stack-memory fragment:
    the one-binding program returning that binding is `ScalarMemN`. -/
def RegHeadMemN {Γ : Ctxt jasminDialect} {w : Nat}
    (e : Expr jasminDialect Γ (JasminTy.reg w)) : Prop :=
  ScalarMemN (Com.var e (Com.ret (.here : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w))))

/-- The emitted chain of a `.var` splits into the head's one-binding chain and
    the tail's chain one binder deeper. -/
theorem straightOpsMem_var_split {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {w : Nat} (e : Expr jasminDialect Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) t) :
    straightOpsMem nArgs (Com.var e body) curDepth
      = straightOpsMem nArgs
          (Com.var e (Com.ret (.here : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w))))
          curDepth
        ++ straightOpsMem nArgs body (curDepth + 1) := rfl

/-- The **array-returning stack-memory fragment**: a chain of register-producing
    `ScalarMemN` heads and `stackStore` bindings, terminated by a `.ret` at an
    array variable. The scalar fragment `ScalarMemN` is the same chain terminated
    at a register variable. -/
inductive ArrMemN {w n : Nat} :
    {Γ : Ctxt jasminDialect} → Com jasminDialect Γ (JasminTy.stackArr w n) → Prop where
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (JasminTy.stackArr w n)) :
      ArrMemN (Com.ret v)
  | reg {Γ : Ctxt jasminDialect} {w' : Nat} (e : Expr jasminDialect Γ (JasminTy.reg w'))
      (he : RegHeadMemN e)
      {body : Com jasminDialect (JasminTy.reg w' :: Γ) (JasminTy.stackArr w n)}
      (hbody : ArrMemN body) :
      ArrMemN (Com.var e body)
  | store {Γ : Ctxt jasminDialect} {w' n' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackStore w' n')
        = .stackArr w' n')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.stackStore w' n')))
      {body : Com jasminDialect (JasminTy.stackArr w' n' :: Γ) (JasminTy.stackArr w n)}
      (hbody : ArrMemN body) :
      ArrMemN (Com.var ⟨JasminOp.stackStore w' n', heq, args⟩ body)

/-! ## 3. The emitted chain of an `ArrMemN` update -/

/-- **The chain simulation at an array return.** From any state agreeing with
    `V`, the emitted chain of an `ArrMemN` program runs to completion, writes
    only the fresh `regName` block at depth `≥ curDepth`, and leaves
    `Com.denote com V` in the array slot the chain returns. -/
theorem ArrMemN.straightOps_full {w n : Nat} {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (JasminTy.stackArr w n)} (hcom : ArrMemN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateM} {V : Ctxt.Valuation Γ},
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesM nArgs curDepth st V →
      ∃ st', lsemStraightMem (straightOpsMem nArgs com curDepth) st = some st' ∧
        WriteFrame curDepth st st' ∧
        st'.getArr (comRetReg nArgs argName com curDepth) w n = some (com.denote V) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V _hlen _harg hagree
      refine ⟨st, rfl, WriteFrame.refl curDepth st, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      have harr := hagree.arr v
      rw [key] at harr
      exact harr
  | reg e he hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      obtain ⟨st1, hrun1, hAg1, hFr1⟩ :=
        lsemStraightMem_straightOps_store he (nArgs := nArgs) (curDepth := curDepth)
          hlen harg hagree
      simp only [comLen, comDenoteLets] at hAg1
      obtain ⟨st2, hrun2, hFr2, hret2⟩ :=
        ih (nArgs := nArgs) (curDepth := curDepth + 1) (st := st1)
          (V := V.extend (e.denote V)) (by simp [List.length_cons, hlen]) (by omega) hAg1
      refine ⟨st2, ?_, WriteFrame.comp hFr1 hFr2, ?_⟩
      · rw [straightOpsMem_var_split, lsemStraightMem_append, hrun1, Option.bind_some]
        exact hrun2
      · simp only [comRetReg, Com.denote]
        exact hret2
  | store heq args hbody ih =>
      intro nArgs curDepth st V hlen harg hagree
      have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs)
        (curDepth := curDepth) heq args hagree
      have hagree' := StoreAgreesM.stepArr
        ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st2, hrun2, hFr2, hret2⟩ :=
        ih (nArgs := nArgs) (curDepth := curDepth + 1) (by simp [List.length_cons, hlen])
          (by omega) hagree'
      refine ⟨st2, ?_, WriteFrame.stepArr _ hFr2, ?_⟩
      · rw [straightOpsMem_store, lsemStraightMem_cons, hstep]
        exact hrun2
      · simp only [comRetReg, Com.denote]
        exact hret2

/-! ## 4. The emitted array-carrier loop body -/

/-- The array slot the emitted chain of an array-returning update returns in. -/
def loopBodyRetArrMN {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)) :
    String :=
  comRetReg (invTys.length + 2) argName update (invTys.length + 2)

/-- The scratch register the array writeback stages one cell through: the first
    slot above the chain's fresh block. -/
def loopArrCopyRegMN {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)) :
    String :=
  regName (invTys.length + 2 + comLen update)

/-- The writeback of an array-carrier loop pass: copy the chain's return array
    into the accumulator argument's slot (a `LOADIDX` of the cell at the loop
    index, then a `STOREIDX` of that cell back into the accumulator slot with
    the return array as source), advance the loop index, decrement the
    counter. -/
def loopArrWritebackMN {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) : List LinstrRM :=
  [ (LinstrR.Lopn [.reg (loopArrCopyRegMN update)] "LOADIDX"
      [.arrIdx (loopBodyRetArrMN update) (idxRegMN invTys) (w / 8)], MemTag.load w n)
  , (LinstrR.Lopn [.reg (accRegMN invTys)] "STOREIDX"
      [.arrIdx (loopBodyRetArrMN update) (idxRegMN invTys) (w / 8),
        .reg (loopArrCopyRegMN update)], MemTag.store w n)
  , (LinstrR.Lopn [.reg (idxRegMN invTys)] "ADD:64"
      [.reg (idxRegMN invTys), .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg nReg] "SUB:64" [.reg nReg, .imm 1], MemTag.reg none) ]

/-- **The emitted array-carrier loop body**: the linearizer chain of the
    `ArrMemN` update followed by the array writeback — the `chain ++ writeback`
    shape the back-edge iterates, at an array accumulator. -/
def loopBodyArrFullMN {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) : List LinstrRM :=
  straightOpsMem (invTys.length + 2) update (invTys.length + 2)
    ++ loopArrWritebackMN update nReg

/-- Every element of the array-carrier body is an `Lopn`. -/
theorem loopBodyArrFullMN_isLopn {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) :
    ∀ i ∈ loopBodyArrFullMN update nReg, IsLopn i := by
  intro i hi
  rw [loopBodyArrFullMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact straightOpsMem_isLopn update (invTys.length + 2) (invTys.length + 2) i hi
  · simp only [loopArrWritebackMN, List.mem_cons] at hi
    rcases hi with rfl | rfl | rfl | rfl | h
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact absurd h (List.not_mem_nil)

/-! ## 5. The per-trip pass and the trip invariant -/

/-- **The per-trip array pass.** One pass of the emitted array-carrier body,
    from ANY machine state agreeing with the trip-`t` valuation and holding a
    readable counter: it succeeds, lands in a state agreeing with the
    trip-`(t+1)` valuation at the stepped accumulator array
    `JLoopBodyN.stepC`, and decrements the counter. -/
theorem loopBodyArrFullMN_trip {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) (t : Nat) (arrt : Fin n → BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
      (tripValArrMN invs t arrt))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) :
    ∃ bt', lsemStraightMem (loopBodyArrFullMN update nReg) bt = some bt'
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt'
          (tripValArrMN invs (t + 1) (JLoopBodyN.stepC update invs t arrt))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  -- the chain: run, write frame, and the return array slot
  obtain ⟨stc, hrunC, hFrC, hretC⟩ :=
    ArrMemN.straightOps_full hupd (nArgs := invTys.length + 2)
      (curDepth := invTys.length + 2) rfl le_rfl hagree
  have hAgC : StoreAgreesM (invTys.length + 2) (invTys.length + 2) stc
      (tripValArrMN invs t arrt) := StoreAgreesM.of_frame rfl hagree hFrC
  set stepv : Fin n → BitVec w := JLoopBodyN.stepC update invs t arrt with hstepv
  have hret : stc.getArr (loopBodyRetArrMN update) w n = some stepv := hretC
  have hnc : stc.reg.getW nReg 64 = some vn :=
    (hFrC.1 nReg 64 (fun k _ => hnr k)).trans hn
  -- split the fold at the writeback
  rw [loopBodyArrFullMN, lsemStraightMem_append, hrunC, Option.bind_some]
  -- step 1: stage one cell of the return array in the copy register
  have hidxC : stc.reg.getW (idxRegMN invTys) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx hAgC
  have h1 := lsemStepMem_loadIdx (loopArrCopyRegMN update) (loopBodyRetArrMN update)
    (idxRegMN invTys) (w / 8) stepv (BitVec.ofNat 64 t) stc hret hidxC
  set lv : BitVec w := stackGet stepv (BitVec.ofNat 64 t).toNat with hlv
  set s1 := (stc.setReg (loopArrCopyRegMN update) lv).nextPc with hs1
  have hAg1 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s1
      (tripValArrMN invs t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch rfl
      (invTys.length + 2 + comLen update) (by simp only [List.length_cons]; omega) lv hAgC)
  -- step 2: store that cell back into the accumulator slot from the return array
  have hret1 : s1.getArr (loopBodyRetArrMN update) w n = some stepv := by
    rw [hs1, LstateM.getArr_nextPc, LstateM.getArr_setReg]
    exact hret
  have hidx1 : s1.reg.getW (idxRegMN invTys) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx hAg1
  have hval1 : s1.reg.getW (loopArrCopyRegMN update) w = some lv := by
    rw [hs1]
    exact LstateM.getW_setReg_nextPc_same stc (loopArrCopyRegMN update) lv
  have h2 := lsemStepMem_storeIdx (accRegMN invTys) (loopBodyRetArrMN update)
    (idxRegMN invTys) (loopArrCopyRegMN update) (w / 8) stepv (BitVec.ofNat 64 t) lv s1
    hret1 hidx1 hval1
  rw [hlv, stackSet_stackGet_self] at h2
  set s2 := (s1.setArr (accRegMN invTys) stepv).nextPc with hs2
  have hAg2 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s2
      (tripValArrMN invs t stepv) :=
    StoreAgreesM.nextPc (tripAgree_setArr_acc hAg1 stepv)
  -- step 3: loop-index increment
  have hidx2 : s2.reg.getW (idxRegMN invTys) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx hAg2
  have h3 := lsemStepMem_add64Imm (idxRegMN invTys) (idxRegMN invTys) 1
    (BitVec.ofNat 64 t) s2 hidx2
  rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from by
    rw [BitVec.ofNat_add]] at h3
  set s3 := (s2.setReg (idxRegMN invTys) (BitVec.ofNat 64 (t + 1))).nextPc with hs3
  have hAg3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s3
      (tripValArrMN invs (t + 1) stepv) :=
    StoreAgreesM.nextPc (tripAgree_setReg_idx hAg2 (BitVec.ofNat 64 (t + 1)))
  -- step 4: counter decrement
  have hn3 : s3.reg.getW nReg 64 = some vn := by
    rw [hs3, LstateM.getW_setReg_nextPc_other _ _ _ _ _
        (show nReg ≠ idxRegMN invTys from hna invTys.length),
      hs2, LstateM.getW_setArr_nextPc,
      hs1, LstateM.getW_setReg_nextPc_other _ _ _ _ _
        (show nReg ≠ loopArrCopyRegMN update from
          hnr (invTys.length + 2 + comLen update))]
    exact hnc
  have h4 := lsemStepMem_sub64Imm nReg nReg 1 vn s3 hn3
  set s4 := (s3.setReg nReg (vn - BitVec.ofNat 64 1)).nextPc with hs4
  refine ⟨s4, ?_, ?_, ?_⟩
  · show lsemStraightMem (loopArrWritebackMN update nReg) stc = some s4
    rw [loopArrWritebackMN, lsemStraightMem_cons_some h1, lsemStraightMem_cons_some h2,
      lsemStraightMem_cons_some h3, lsemStraightMem_cons_some h4, lsemStraightMem_nil]
  · exact StoreAgreesM.nextPc
      (StoreAgreesM.setReg_untracked nReg (vn - BitVec.ofNat 64 1) hna hnr hAg3)
  · rw [hs4]
    exact LstateM.getW_setReg_nextPc_same s3 nReg (vn - BitVec.ofNat 64 1)

/-- **The array trip invariant.** Every `runBoundedLoopMem` trip state of the
    emitted array-carrier loop agrees with its trip valuation at the source fold
    `JLoopBodyN.denote ⟨t, update⟩`, with a readable counter. -/
theorem loopBodyArrFullMN_inv {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValArrMN invs 0 arr0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedLoopMem (loopBodyArrFullMN update nReg) t s0 = some bt →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValArrMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs arr0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedLoopMem_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedLoopMem_succ_right] at hbt
      cases hbk : runBoundedLoopMem (loopBodyArrFullMN update nReg) k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', hbt', hAg', hn'⟩ := loopBodyArrFullMN_trip update hupd nReg hna hnr
            invs k (JLoopBodyN.denote ⟨k, update⟩ invs arr0) bk hAgk vn hvn
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' 1
          · rw [show ((bt'.setLpc 1).reg).getW nReg 64 = bt'.reg.getW nReg 64 from
              LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) nReg 64, hn']
            rfl

/-! ## 6. The array-carrier export theorems, per-trip discharged -/

/-- **Export faithfulness at the array cells, UNCONDITIONAL per-trip.** As
    `loopMemArr_export_faithful_denote`, for the emitted `chain ++ writeback`
    body of an arbitrary `ArrMemN` update: the remaining hypotheses are the
    counter schedule (`hprev`/`hlast`/`hbfin`/`htaken`/`hhalt`), the seed
    (`hseed`/`hn0`) and the counter-name hygiene (`hna`/`hnr`). The per-trip
    simulation is discharged through the trip invariant, and the all-`Lopn` side
    condition holds by construction. -/
theorem loopMemArr_export_faithful_denote_uncond {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValArrMN invs 0 arr0))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN update nReg) (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN update nReg) m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN update nReg)))
          (m * ((loopBodyArrFullMN update nReg).length + 1)) s = some t
        ∧ decodeArrM t.base (accRegMN invTys) w n
            = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0) := by
  have hinv := loopBodyArrFullMN_inv update hupd nReg hna hnr invs s.base arr0 hseed hn0
  refine loopMemArr_export_faithful_denote update invs fn top nReg
    (loopBodyArrFullMN update nReg) (loopBodyArrFullMN_isLopn update nReg) s hfn hpc
    m hm bprev blast bfin hprev hlast hbfin htaken hhalt (accRegMN invTys) arr0 ?_ ?_
  · exact tripAgree_getArr_acc hseed
  · intro t ht bt arrt hbt hdec
    obtain ⟨hAgt, hnt⟩ := hinv t bt hbt
    obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
    have harrt : decodeArrM bt (accRegMN invTys) w n
        = some (JLoopBodyN.denote ⟨t, update⟩ invs arr0) := tripAgree_getArr_acc hAgt
    rw [hdec] at harrt
    obtain rfl := Option.some.inj harrt
    obtain ⟨bt', hbt', hAg', _⟩ := loopBodyArrFullMN_trip update hupd nReg hna hnr
      invs t _ bt hAgt vn hvn
    exact ⟨bt', hbt', tripAgree_getArr_acc hAg'⟩

/-- **Export faithfulness at the array cells, concluded at `ComL.denote`,
    UNCONDITIONAL per-trip.** The machine run of the emitted array-carrier
    counter loop decodes at the accumulator's array slot to the front node
    `ComL.forLoopNRt`'s denotation, with only schedule, seed and name-hygiene
    hypotheses. -/
theorem loopMemArr_export_faithful_comL_uncond {Γ : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update)
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValArrMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyArrFullMN update nReg)
      ((count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyArrFullMN update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyArrFullMN update nReg) (count.lookup V).toNat
      s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyArrFullMN update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL
          (singletonProgM fn (loopLinstrRM top nReg (loopBodyArrFullMN update nReg)))
          ((count.lookup V).toNat * ((loopBodyArrFullMN update nReg).length + 1)) s
            = some t
        ∧ decodeArrM t.base (accRegMN invTys) w n
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote_acc]
  exact loopMemArr_export_faithful_denote_uncond update hupd (Expr.lookupArgs invsV V)
    fn top nReg hna hnr s hfn hpc (initV.lookup V) hseed hn0 _ hm
    bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 6. A front-generated inhabitant -/

/-- `fillUpdate` — the counted-fill loop body of `JasminLsemMemSourceTieUncond` —
    is an `ArrMemN` update: a `stackLoad` register head followed by a `stackStore`
    binding returning the fresh array. Every result above is conditioned on
    `ArrMemN`, so this is what carries them to a body the front emits. -/
theorem fillUpdate_arrMemN (w n : Nat) : ArrMemN (fillUpdate w n) :=
  .reg _ (ScalarMemN.load rfl _ (.ret .here)) (.store rfl _ (.ret .here))

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
