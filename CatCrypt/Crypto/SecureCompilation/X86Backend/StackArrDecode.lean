/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame

@[expose] public section

set_option autoImplicit false

/-!
# The machine steps of the stack-array instructions on the correspondence with narrow names

`LprogBytes.encodeLopn` encodes the constant-index store `STOREIMM [d] <- [B; V; imm k]` as
`movq %V, 8k(%B)` (`DecodePrintedAddr.stPieces`) and the zeroing in the source form
`ZEROARR [] <- [B; imm n; imm 64]` as the `n` stores `movq $0, 8i(%B)`, `i < n`
(`DecodePrintedAddr.zeroPieces`). `DecodePrintedAddr` gives their bytes, their runs on the
address machine and their simulation from `ACorr`. The results below are the simulation from
the correspondence with narrow names `ACorrW`.

## Main results

* `sim_storeImm`: from `ACorrW`, the step of the address semantics `fstepA` at the tag
  `.storeImm 64 n` with `k < n` is matched by the run of the decoded store.
* `sim_zeroArr`: from `ACorrW`, the step of `fstepA` on the source-form zeroing at the tag
  `.zero 64 n` is matched by the run of the decoded stores.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.StackArrDecode

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-- **The simulation of the constant-index store.** From `ACorrW`, with the base `B` and the
    value `V` general-purpose names at width `64` and `k < n`, the step of the address
    semantics of `STOREIMM d, [B, V, #k]` at the tag `.storeImm 64 n` is matched by the run of
    the decoded store `movq %V, 8k(%B)`. -/
theorem sim_storeImm (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (d B V : String)
    {k n : Nat} (hk : k < n) (hB : gpOk B = true) (hV : gpOk V = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64)
    (hwV : (s.reg.lvm V).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA frame (.Lopn [.reg d] "STOREIMM" [.reg B, .reg V, .imm k], .storeImm 64 n)
      s zf = some (s', zf')) :
    ACorrW rsp (runBlockA sa ((stPieces B V k).map Prod.snd)) s' ∧ zf' = zf := by
  rw [fstepA_storeImm _ hk (hc.wide hB hwB) (hc.wide hV hwV)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  rw [run_stPieces]
  refine ⟨⟨fun r hr => ?_, hc.sp, fun x hx => ?_⟩, rfl⟩
  · have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · exact agree_write64 hc.mem _ _ x hx

/-- **The simulation of the zeroing.** From `ACorrW`, with the base `B` a general-purpose name
    at width `64`, the step of the address semantics of `ZEROARR [], [B, #n, #64]` at the tag
    `.zero 64 n` is matched by the run of the decoded stores `movq $0, 8i(%B)`, `i < n`. -/
theorem sim_zeroArr (frame : String → Option (BitVec 64)) (rsp : BitVec 64) (B : String)
    {n : Nat} (hB : gpOk B = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 = 64) (s' : LstateA) (zf' : Bool)
    (hst : fstepA frame (.Lopn [] "ZEROARR" [.reg B, .imm n, .imm 64], .zero 64 n) s zf
      = some (s', zf')) :
    ACorrW rsp (runBlockA sa ((zeroPieces B n).map Prod.snd)) s' ∧ zf' = zf := by
  rw [fstepA_zeroArr _ (hc.wide hB hwB)] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  rw [run_zeroPieces]
  refine ⟨⟨fun r hr => ?_, hc.sp, fun x hx => ?_⟩, rfl⟩
  · have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ (∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _) ∨ _
    rw [hg]
    exact hc.regs r hr
  · exact agree_zeroWords hc.mem _ _ x hx

end CatCrypt.Crypto.SecureCompilation.X86Backend.StackArrDecode
