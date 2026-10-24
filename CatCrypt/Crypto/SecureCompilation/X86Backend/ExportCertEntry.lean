/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFaithful
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

@[expose] public section

set_option autoImplicit false

/-!
# The System V entry of a certified export

`ExportCertFaithful.singleLoop_export_faithful_cert` takes three entry hypotheses on the
flag-machine state `b0`: the seed agreement along `certTau` with the trip-`0` valuation, a
readable width-`64` register at each invariant base, and the runtime count at the count
register. This module derives all three from one condition relating `b0` and the source
valuation to a System V entry state `sa` of an `AbiLayout`.

At the virtual node the array and register names of the program's parameters are the
argument names `argName j`, `j` the ABI parameter index. `AbiEntryM σ sa b0` states that
`b0` starts at program counter `0`, holds at `argName j` the entry value of parameter `j`'s
register at width `64`, and holds at the array name `argName j` of an array parameter the
words at that register's address. `AbiValOf σ sa V` states that the valuation `V` of the
program's context reads each variable off its parameter: a register variable is the `u64`
value of a scalar parameter, an array variable the words of an array parameter.

## Main results

* `AbiValOf`, `AbiEntryM` — the ABI reading of a valuation and of a flag-machine entry.
* `abiEntryM`, `abiEntryM_spec` — the canonical entry state of `sa`, which satisfies
  `AbiEntryM`.
* `storeAgreesM_of_abi` — an ABI entry agrees with an ABI valuation at the argument depth.
* `certSeed_of_storeAgreesM` — the seed agreement along `certTau` from the entry agreement
  and `exportCertB`.
* `singleLoop_export_faithful_abi` — the single-loop export theorem whose only entry
  hypotheses are `AbiValOf` and `AbiEntryM`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (pullM pullM_getW pullM_getArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
  (tripValArrMN decodeArrM resolveVar_trip_acc resolveVar_trip_idx accRegMN idxRegMN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (argName_injective varIndex_lt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFaithful
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd (ComExpOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout AbiArg ArgKind)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)

/-! ## 1. The ABI reading -/

/-- The `n` words at the address `base` of the memory of `sa`, as a width-`64` array. -/
def wordsFn (sa : AState) (base : BitVec 64) (n : Nat) : Fin n → BitVec 64 :=
  fun i => read64 sa.mem (base + BitVec.ofNat 64 (8 * i.val))

/-- The parameter index of a variable of `Γ`: its slot counted from the program root. -/
abbrev argIdx {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) : Nat :=
  Γ.length - 1 - varIndex v

/-- **The ABI reading of a valuation.** Every variable of `Γ` has a parameter at its slot;
    a register variable is a `u64` scalar parameter's register value; an array variable
    of shape `(w, n)` is a `64`-bit array parameter of length `n`, whose words are read at
    the address its register holds. -/
structure AbiValOf (σ : AbiLayout) (sa : AState) {Γ : Ctxt jasminDialect}
    (V : Ctxt.Valuation Γ) : Prop where
  /-- Every variable's slot is a parameter. -/
  arg : ∀ {t : JasminTy} (v : Ctxt.Var Γ t), (σ.args[argIdx v]?).isSome
  /-- A register variable reads a scalar parameter. -/
  reg : ∀ {w : Nat} (v : Ctxt.Var Γ (.reg w)), ∃ a, σ.args[argIdx v]? = some a
    ∧ a.kind = .scalar ∧ ∃ h : w = 64, v.lookup V = h ▸ sa.regs a.reg
  /-- An array variable reads the words of an array parameter. -/
  arr : ∀ {w n : Nat} (v : Ctxt.Var Γ (.stackArr w n)), ∃ a, σ.args[argIdx v]? = some a
    ∧ a.kind = .words n ∧ ∃ h : w = 64, v.lookup V = h ▸ wordsFn sa (sa.regs a.reg) n

/-- **The ABI entry of the flag machine.** The program counter is `0`; the register
    `argName j` holds the entry value of parameter `j`'s register at width `64`; the array
    `argName j` of an array parameter of length `n` holds the words at that register's
    address. -/
structure AbiEntryM (σ : AbiLayout) (sa : AState) (b0 : LstateM) : Prop where
  /-- The program counter. -/
  pc : b0.lpc = 0
  /-- The register of each parameter. -/
  reg : ∀ j a, σ.args[j]? = some a → b0.reg.getW (argName j) 64 = some (sa.regs a.reg)
  /-- The words of each array parameter. -/
  arr : ∀ j a n, σ.args[j]? = some a → a.kind = .words n →
    b0.getArr (argName j) 64 n = some (wordsFn sa (sa.regs a.reg) n)

/-- The parameter index an argument name denotes, below `m`. -/
def argIdxOf (m : Nat) (r : String) : Option Nat := (List.range m).find? (argName · == r)

theorem argIdxOf_argName {m j : Nat} (hj : j < m) : argIdxOf m (argName j) = some j := by
  unfold argIdxOf
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, j, by simpa using hj, by simp, fun i hi => ?_⟩
  simp only [List.getElem_range, Bool.not_eq_true']
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro he
  have := argName_injective he
  omega

theorem argIdxOf_argName_ge {m j : Nat} (hj : m ≤ j) : argIdxOf m (argName j) = none := by
  unfold argIdxOf
  rw [List.find?_eq_none]
  intro i hi he
  simp only [List.mem_range] at hi
  have := argName_injective (by simpa using he)
  omega

/-- The canonical flag-machine entry of `sa`: each argument name holds its parameter's
    register at width `64`, and the array of each array parameter the words at that
    register's address; every other cell is empty. -/
def abiEntryM (σ : AbiLayout) (sa : AState) : LstateM where
  reg :=
    { lvm := fun r => match (argIdxOf σ.args.length r).bind (σ.args[·]?) with
        | some a => ⟨64, sa.regs a.reg⟩
        | none => ⟨0, 0#0⟩
      lpc := 0 }
  larr := fun r => match (argIdxOf σ.args.length r).bind (σ.args[·]?) with
    | some a => match a.kind with
      | .words n => ⟨64, n, wordsFn sa (sa.regs a.reg) n⟩
      | .scalar => ArrCell.default
    | none => ArrCell.default

theorem abiEntryM_lookup {σ : AbiLayout} {j : Nat} {a : AbiArg} (h : σ.args[j]? = some a) :
    (argIdxOf σ.args.length (argName j)).bind (σ.args[·]?) = some a := by
  have hj : j < σ.args.length := by
    rcases Nat.lt_or_ge j σ.args.length with hj | hj
    · exact hj
    · rw [List.getElem?_eq_none hj] at h; cases h
  rw [argIdxOf_argName hj, Option.bind_some, h]

/-- The canonical entry satisfies `AbiEntryM`. -/
theorem abiEntryM_spec (σ : AbiLayout) (sa : AState) : AbiEntryM σ sa (abiEntryM σ sa) where
  pc := rfl
  reg := fun j a h => by
    have hl : (abiEntryM σ sa).reg.lvm (argName j) = ⟨64, sa.regs a.reg⟩ := by
      simp only [abiEntryM, abiEntryM_lookup h]
    unfold LstateN.getW
    rw [hl]
    simp
  arr := fun j a n h hk => by
    have hl : (abiEntryM σ sa).larr (argName j) = ⟨64, n, wordsFn sa (sa.regs a.reg) n⟩ := by
      simp only [abiEntryM, abiEntryM_lookup h, hk]
    unfold LstateM.getArr
    rw [hl]
    simp

/-! ## 2. The entry agreement -/

/-- At the argument depth a variable resolves to its parameter's argument name. -/
theorem resolveVar_top {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Ctxt.Var Γ t) :
    resolveVar Γ.length Γ.length argName (fun _ => none) v = .reg (argName (argIdx v)) := by
  have := varIndex_lt v
  simp only [resolveVar]
  rw [ite_eq_left (by omega)]

/-- **An ABI entry agrees with an ABI valuation** at the argument depth. -/
theorem storeAgreesM_of_abi {σ : AbiLayout} {sa : AState} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {b0 : LstateM} (hV : AbiValOf σ sa V) (hb : AbiEntryM σ sa b0) :
    StoreAgreesM Γ.length Γ.length b0 V := by
  refine ⟨fun {w} v => ?_, fun {w n} v => ?_⟩
  · obtain ⟨a, ha, _, rfl, hv⟩ := hV.reg v
    rw [resolveVar_top, evalOperandN, hb.reg _ _ ha, hv]
  · obtain ⟨a, ha, hk, rfl, hv⟩ := hV.arr v
    rw [resolveVar_top]
    simp only [operandName]
    rw [hb.arr _ _ _ ha hk, hv]

/-! ## 3. The seed agreement along `certTau` -/

section Seed

variable {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}

/-- The invariant base registers of a nonempty invariant list: the argument name of the
    first seed, then those of the rest. -/
theorem invRegsOf_cons {τ : JasminTy} {tys : Ctxt jasminDialect} (v : Ctxt.Var Γ τ)
    (rest : HVector (fun ty => Ctxt.Var Γ ty) tys) :
    invRegsOf (loopInvOps (.cons v rest)) = argName (argIdx v) :: invRegsOf (loopInvOps rest) := by
  show List.filterMap _ (resolveVar Γ.length Γ.length argName (fun _ => none) v
    :: exprArgsHV Γ.length Γ.length argName (fun _ => none) rest) = _
  rw [resolveVar_top, List.filterMap_cons]
  rfl

/-- The invariant operands of the export resolve to the argument names of the invariant
    seeds, and each invariant lookup is the lookup of its seed. -/
theorem loopInv_name : ∀ {invTys : Ctxt jasminDialect}
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    {τ : JasminTy} (u : Ctxt.Var invTys τ),
    ∃ v : Ctxt.Var Γ τ, (invRegsOf (loopInvOps invs))[varIndex u]? = some (argName (argIdx v))
      ∧ u.lookup (Expr.lookupArgs invs V) = v.lookup V
  | _ :: _, .cons v rest, V, _, .here => ⟨v, by rw [invRegsOf_cons]; rfl, rfl⟩
  | _ :: _, .cons v rest, V, _, .there u => by
      obtain ⟨v', h1, h2⟩ := loopInv_name rest V u
      refine ⟨v', ?_, h2⟩
      rw [invRegsOf_cons]
      exact h1

theorem invRegsOf_length : ∀ {invTys : Ctxt jasminDialect}
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys),
    (invRegsOf (loopInvOps invs)).length = invTys.length
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      rw [invRegsOf_cons, List.length_cons, invRegsOf_length rest, List.length_cons]

/-- Every invariant base register of the export is the argument name of a variable. -/
theorem invRegsOf_mem : ∀ {invTys : Ctxt jasminDialect}
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (r : String),
    r ∈ invRegsOf (loopInvOps invs) → ∃ (t : JasminTy) (v : Ctxt.Var Γ t), r = argName (argIdx v)
  | [], .nil, _, h => by simp [loopInvOps, exprArgsHV, invRegsOf] at h
  | _ :: _, .cons v rest, r, h => by
      rw [invRegsOf_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, v, rfl⟩
      · exact invRegsOf_mem rest r h

/-- **The seed agreement from the entry agreement.** Let the single-loop node over
    `update` with seed `init`, count and invariant seeds `invs` resolve its seed to the
    register `out` and pass `exportCertB` at loop depth `Γ.length` and accumulator
    `regName Γ.length`. An entry state agreeing with `V` at the argument depth, with the
    loop index set to `0`, pulls back along `certTau` to a state agreeing with the trip-`0`
    valuation. -/
theorem certSeed_of_storeAgreesM {out c : String}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (init : Ctxt.Var Γ (JasminTy.stackArr w n)) (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (hout : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcert : exportCertB Γ.length (regName Γ.length) out c update (loopInvOps invs) = true)
    (V : Ctxt.Valuation Γ) (b0 : LstateM) (hag : StoreAgreesM Γ.length Γ.length b0 V) :
    StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (pullM (certTau Γ.length (regName Γ.length) out update (loopInvOps invs))
        (b0.setReg (loopIdx Γ.length) (0#64)))
      (tripValArrMN (Expr.lookupArgs invs V) 0 (init.lookup V)) := by
  have hc := exportCertB_sound hcert
  set d := Γ.length
  set invRegs := invRegsOf (loopInvOps invs)
  set ρ := certRho d (regName d) out (certSlots update)
  set σ := certSigma d invTys.length (regName d) invRegs
  have hlen : invRegs.length = invTys.length := invRegsOf_length invs
  -- the invariant slot `argName (k - 1 - i)` goes to the `i`-th invariant register
  have hinvτ : ∀ {τ : JasminTy} (u : Ctxt.Var invTys τ),
      ∃ v : Ctxt.Var Γ τ, ρ (σ (argName (invTys.length - 1 - varIndex u)))
          = argName (argIdx v) ∧ u.lookup (Expr.lookupArgs invs V) = v.lookup V
        ∧ argName (argIdx v) ≠ loopIdx d := by
    intro τ u
    have hu := varIndex_lt u
    obtain ⟨v, hv1, hv2⟩ := loopInv_name invs V u
    have hσ : σ (argName (invTys.length - 1 - varIndex u)) = argName (argIdx v) := by
      show certSigma _ _ _ _ _ = _
      rw [certSigma_inv (by omega), show invTys.length - 1 - (invTys.length - 1 - varIndex u)
        = varIndex u by omega, List.getD_eq_getElem?_getD, hv1, Option.getD_some]
    have hmem : argName (argIdx v) ∈ invRegs := List.mem_of_getElem? hv1
    have hne := hc.canon.invIdx (invTys.length - 1 - varIndex u) (by omega)
    refine ⟨v, ?_, hv2, ?_⟩
    · rw [hσ, hc.nodeRen.invFix _ hmem]
    · have : (ρ ∘ σ) (argName (invTys.length - 1 - varIndex u)) = argName (argIdx v) := by
        show ρ (σ _) = _
        rw [hσ, hc.nodeRen.invFix _ hmem]
      rw [← this]
      exact hne
  have hinvRes : ∀ {τ : JasminTy} (u : Ctxt.Var invTys τ),
      resolveVar (invTys.length + 2) (invTys.length + 2) argName (fun _ => none)
        (.there (.there u) : Ctxt.Var (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) τ)
        = .reg (argName (invTys.length - 1 - varIndex u)) := by
    intro τ u
    have hlt : varIndex u < invTys.length := varIndex_lt u
    have h : invTys.length + 2 - 1 - (varIndex u + 1 + 1) = invTys.length - 1 - varIndex u := by
      omega
    simp only [resolveVar, varIndex, h]
    rw [ite_eq_left (by omega)]
  refine ⟨fun {w'} v => ?_, fun {w' n'} v => ?_⟩
  · cases v with
    | there v' =>
      cases v' with
      | here =>
          rw [resolveVar_trip_idx, evalOperandN, pullM_getW]
          show (b0.setReg (loopIdx d) (0#64)).reg.getW (ρ (σ (argName invTys.length))) 64 = _
          rw [show σ (argName invTys.length) = loopIdx d from certSigma_idx,
            hc.nodeRen.idxFix]
          rw [LstateM.reg_setReg, LstateN.getW_setReg_same]
          rfl
      | there u =>
          obtain ⟨v0, h1, h2, h3⟩ := hinvτ u
          rw [hinvRes, evalOperandN, pullM_getW]
          show (b0.setReg (loopIdx d) (0#64)).reg.getW (ρ (σ _)) w' = _
          rw [h1]
          have hg := hag.reg v0
          rw [resolveVar_top, evalOperandN] at hg
          rw [LstateM.reg_setReg, LstateN.getW_setReg_other _ _ _ _ _ h3]
          rw [show (Ctxt.Var.lookup (.there (.there u)) (tripValArrMN (Expr.lookupArgs invs V) 0
            (init.lookup V))) = u.lookup (Expr.lookupArgs invs V) from rfl, h2, ← hg]
  · cases v with
    | here =>
        rw [resolveVar_trip_acc]
        simp only [operandName, pullM_getArr]
        show (b0.setReg (loopIdx d) (0#64)).getArr (ρ (σ (argName (invTys.length + 1)))) w n = _
        rw [show σ (argName (invTys.length + 1)) = regName d from certSigma_acc,
          show ρ (regName d) = out from certRho_acc _ _ _ _]
        have hg := hag.arr init
        rw [hout] at hg
        exact hg
    | there v' =>
      cases v' with
      | there u =>
          obtain ⟨v0, h1, h2, _⟩ := hinvτ u
          rw [hinvRes]
          simp only [operandName, pullM_getArr]
          show (b0.setReg (loopIdx d) (0#64)).getArr (ρ (σ _)) w' n' = _
          rw [h1]
          have hg := hag.arr v0
          rw [resolveVar_top] at hg
          rw [show (Ctxt.Var.lookup (.there (.there u)) (tripValArrMN (Expr.lookupArgs invs V) 0
            (init.lookup V))) = u.lookup (Expr.lookupArgs invs V) from rfl, h2, ← hg]
          rfl

end Seed

/-! ## 4. The single-loop export from the ABI entry -/

/-- **The certified single-loop export from the System V entry.** For the program with one
    runtime-count loop node and nothing after it, whose update is in `ArrMemN` with
    `ComExpOK` and which passes `loopCertB`: the seed and count resolve to registers `out`
    and `c`; the body `ComL.toLfundefPhysAbi` allocates is the liveness pin, `certNode` and
    the return, instruction for instruction; and for every valuation `V` that a layout `σ`
    reads off an entry state `sa` (`AbiValOf`) and every flag-machine state `b0` that is
    the ABI entry of `sa` (`AbiEntryM`), `certNode` run by `lsemFuelMemF` from `b0` halts
    with the array at `out` decoding to the program's denotation at `V`. -/
theorem singleLoop_export_faithful_abi {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (outArg : String) (inArgs abiArgs : List String)
    (hupd : ArrMemN update) (hexp : ComExpOK update)
    (hcert : loopCertB update count init invs outArg inArgs abiArgs = true) :
    ∃ out c, resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out
      ∧ resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c
      ∧ (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
            abiArgs).map (·.li_i)
          = (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
            ++ [.Lret]
      ∧ ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
          (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
          ∃ (k : Nat) (t : LstateMF),
            lsemFuelMemF (singletonProgM fn (certNode update invs out c)) k
                { prog := { base := b0, lfn := fn }, zf := zf } = some t
              ∧ decodeArrM t.prog.base out w n
                  = some ((singleLoop update count init invs).denote V) := by
  obtain ⟨out, c, hi, hcn, hbody, hrun⟩ := singleLoop_export_faithful_cert update count init
    invs outArg inArgs abiArgs hupd hexp hcert
  obtain ⟨_, _, _, _, hx, _⟩ := loopCertB_spec hcert
  refine ⟨out, c, hi, hcn, hbody, fun σ sa V fn b0 zf hV hb => ?_⟩
  have hag := storeAgreesM_of_abi hV hb
  obtain ⟨out', c', hi', hc', hx', _⟩ := loopCertB_spec hcert
  rw [hi] at hi'
  cases hi'
  rw [hcn] at hc'
  cases hc'
  refine hrun V fn b0 zf hb.pc (certSeed_of_storeAgreesM update init invs hi hx' V b0 hag) ?_ ?_
  · intro r hr
    obtain ⟨t, v, rfl⟩ := invRegsOf_mem invs r hr
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hV.arg v)
    rw [hb.reg _ _ ha]
    rfl
  · have hg := hag.reg count
    rw [hcn, evalOperandN] at hg
    exact hg

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
