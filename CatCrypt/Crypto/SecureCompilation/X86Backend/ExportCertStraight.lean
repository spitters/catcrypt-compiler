/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

@[expose] public section

set_option autoImplicit false

/-!
# The certified export of a straight-line body

`Com.toLprogPhysAbi` with the argument-liveness pin forced (`forceLivePin := true`, as the
straight route of the general compiler exports) allocates the virtual body
`straightAbiBody`: the pin over the argument names, then the store-thread canonicalisation
of the call-shadow expansion of `comToBody`. `straightCertB` is the check a compiler runs on
such a body: the program is in the register-returning stack-memory fragment (`scalarMemNB`)
and the instructions of the allocated body are the pin, the typed chain `straightOpsMem`
and the return.

The chain is plain, so the flag machine `lsemFuelMemF` runs it as the straight-line fold
`lsemStraightMem`, and `JasminLsemMem.lsemStraightMem_straightOps` gives its value from any
state agreeing with the valuation. With `ExportCertEntry.storeAgreesM_of_abi` the entry
hypothesis is the System V one: arrays and registers are named by ABI parameter.

## Main results

* `straightPin`, `straightAbiBody` — the pin and the allocated virtual body.
* `straightCertB`, `straightCertB_spec` — the check and what an accepted body satisfies.
* `lsemFuelMemF_plain_halts` — a plain chain from program counter `0` halts under
  `lsemFuelMemF` in the state the straight-line fold reaches, up to the carry and
  overflow flags.
* `straight_chain_abi` — for a straight-line program in the stack-memory fragment
  (`scalarMemNB`), the chain run from an ABI entry halts with the program's denotation at
  the return register.
* `straight_export_faithful_abi` — for a straight-line program that passes
  `straightCertB`, the allocated body is the pin, the chain and the return, and the chain,
  run from an ABI entry, halts with the program's denotation at the return register.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
  (runStraightF runStraightF_of_lsemStraightMem runStraightF_lpc lsemFuelMemF_segF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
  (straightOpsMem_plain scalarMemN_comOpsPlain)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. The allocated virtual body and its check -/

/-- The argument-liveness pin over the first `nArgs` argument names. -/
def straightPin (nArgs : Nat) : Lcmd :=
  [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range nArgs).map (fun j => (.reg (argName j) : LOperand)))⟩]

/-- The virtual body `Com.toLprogPhysAbi` allocates for `com` with the liveness pin forced
    and no residence map: the pin, then the store-thread canonicalisation of the
    call-shadow expansion of the exported walk. -/
def straightAbiBody {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) :
    Lcmd :=
  straightPin Γ.length
    ++ canonicalizeMemrefThread
      (expandCallShadows (comToBody Γ.length argName (fun _ => none) com Γ.length))

/-- **The check of a straight-line export.** The program is in the register-returning
    stack-memory fragment, and the allocated virtual body is the pin, the typed chain
    `straightOpsMem` and the return, instruction for instruction. -/
def straightCertB {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) : Bool :=
  scalarMemNB com
    && (straightAbiBody com).map (·.li_i)
      == (straightPin Γ.length).map (·.li_i)
        ++ (straightOpsMem Γ.length com Γ.length).map Prod.fst ++ [.Lret]

/-- An accepted body is in `ScalarMemN`, and its allocated virtual body is the pin, the
    chain and the return. -/
theorem straightCertB_spec {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : straightCertB com = true) :
    ScalarMemN com ∧ (straightAbiBody com).map (·.li_i)
      = (straightPin Γ.length).map (·.li_i)
        ++ (straightOpsMem Γ.length com Γ.length).map Prod.fst ++ [.Lret] := by
  simp only [straightCertB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨scalarMemNB_sound com h.1, h.2⟩

/-! ## 2. A plain chain on the flag machine -/

/-- **A plain chain halts on the flag machine.** A chain of plain `Lopn`s whose
    straight-line fold runs from `b0` to `b` halts under `lsemFuelMemF`, from program counter
    `0`, in the state with base `b` up to the carry and overflow flags and `zf`
    unchanged. -/
theorem lsemFuelMemF_plain_halts (fn : String) (seg : List LinstrRM) (hplain : PlainLopnBody seg)
    (b0 b : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (hrun : lsemStraightMem seg b0 = some b) :
    ∃ c o, lsemFuelMemF (singletonProgM fn seg) seg.length
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := { b with cf := c, of := o }, lfn := fn }, zf := zf } := by
  obtain ⟨c, o, hF⟩ := runStraightF_of_lsemStraightMem seg hplain b0 b zf hrun
  refine ⟨c, o, ?_⟩
  have hseg := lsemFuelMemF_segF (singletonProgM fn seg) fn rfl seg b0 zf 0
    (fun i hi => (hplain i hi).1) (fun k _ => by rw [hpc, Nat.zero_add]; rfl)
  rw [Nat.add_zero] at hseg
  rw [hseg, hF, Option.bind_some]
  have hlpc : ({ b with cf := c, of := o } : LstateM).lpc = seg.length := by
    rw [runStraightF_lpc seg b0 zf _ zf hF, hpc, Nat.zero_add]
  unfold lsemFuelMemF
  simp only [findInstrMem, singletonProgM, ite_true]
  rw [show ({ b with cf := c, of := o } : LstateM).lpc = seg.length from hlpc,
    List.getElem?_eq_none (le_refl _)]

/-! ## 3. The export theorem -/

/-- **The chain of a straight-line program in the stack-memory fragment realises it.** For a
    program returning a width-`w` register that passes `scalarMemNB`, every valuation `V` a
    layout `σ` reads off an entry state `sa` (`AbiValOf`) and every flag-machine state `b0`
    that is the ABI entry of `sa` (`AbiEntryM`), the chain `straightOpsMem` run by
    `lsemFuelMemF` from `b0` halts with the return register `comRetReg` holding the program's
    denotation at `V`. -/
theorem straight_chain_abi {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hmem : scalarMemNB com = true) :
    ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
      (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
      ∃ (k : Nat) (t : LstateMF),
        lsemFuelMemF (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) k
            { prog := { base := b0, lfn := fn }, zf := zf } = some t
          ∧ t.prog.base.reg.getW (comRetReg Γ.length argName com Γ.length) w
              = some (com.denote V) := by
  intro σ sa V fn b0 zf hV hb
  have hm := scalarMemNB_sound com hmem
  obtain ⟨b, hrun, hval⟩ := lsemStraightMem_straightOps hm (w := w) rfl rfl le_rfl
    (storeAgreesM_of_abi hV hb)
  obtain ⟨c, o, hh⟩ := lsemFuelMemF_plain_halts fn _
    (straightOpsMem_plain _ com (scalarMemN_comOpsPlain hm) _) b0 b zf hb.pc hrun
  refine ⟨_, _, hh, ?_⟩
  simpa only [evalOperandN] using hval

/-- **The certified straight-line export realises its program.** For a straight-line
    program returning a width-`w` register that passes `straightCertB`: the body
    `Com.toLprogPhysAbi` allocates (liveness pin forced) is the pin, the typed chain
    `straightOpsMem` and the return, instruction for instruction; and for every valuation
    `V` that a layout `σ` reads off an entry state `sa` (`AbiValOf`) and every flag-machine
    state `b0` that is the ABI entry of `sa` (`AbiEntryM`), the chain run by `lsemFuelMemF`
    from `b0` halts with the return register `comRetReg` holding the program's denotation
    at `V`. -/
theorem straight_export_faithful_abi {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hcert : straightCertB com = true) :
    (straightAbiBody com).map (·.li_i)
        = (straightPin Γ.length).map (·.li_i)
          ++ (straightOpsMem Γ.length com Γ.length).map Prod.fst ++ [.Lret]
      ∧ ∀ (σ : AbiLayout) (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM)
          (zf : Bool), AbiValOf σ sa V → AbiEntryM σ sa b0 →
          ∃ (k : Nat) (t : LstateMF),
            lsemFuelMemF (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) k
                { prog := { base := b0, lfn := fn }, zf := zf } = some t
              ∧ t.prog.base.reg.getW (comRetReg Γ.length argName com Γ.length) w
                  = some (com.denote V) := by
  have h := hcert
  simp only [straightCertB, Bool.and_eq_true] at h
  exact ⟨(straightCertB_spec hcert).2, straight_chain_abi com h.1⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight
