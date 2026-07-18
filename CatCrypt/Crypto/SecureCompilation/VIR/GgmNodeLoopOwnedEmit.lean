/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Owned GGM node loop with a genuine in-loop `Lcall` (caller-save barrier)

The GGM PRF-tree node expansion as a ROLLED `ComL.forLoopN` whose loop body issues
a genuine `LinstrR.Lcall` to the per-node PRG leaf `ggm_prg_node` — a real consumer
of the in-loop-`Lcall` caller-save barrier (`forLoopLcmdNCall` / `loopBodyCallLcmd`
/ `physNameForBody`). At each node the loop-carried seed/buffer is preserved across
the call because the barrier routes it into a callee-saved register; the call is a
real `call ggm_prg_node`.

`ggm_prg_node` is the GP-ABI per-node PRG leaf (a `u64 → u64` over the node-buffer
pointer) that wraps the owned AES-128 leaf `aes_enc` (`FAEST.AesNiLeafVsimdEmit`);
the barrier marshals the integer/pointer argument in `RDI` and captures the result
in `RAX`. The rolled single-accumulator loop validates the per-node call barrier;
the full `2L-1`-node array plumbing (register-indexed `u128[]`) is outside the
single-accumulator loop-body shape.

## Evidence

* `ggmNodeLoopProg_hasLoopCall` / `_virt_hasCall` / `_phys_hasCall` — the program is
  an in-loop-call `ComL`, the lowered body issues a real `Lcall`, and `bodyHasCall`
  survives register allocation (the barrier stays engaged end-to-end).
* `ggmNodeLoopProg_one_real_Lcall` / `_calls_prg_node` — exactly one genuine
  `LinstrR.Lcall` survives, and it targets `ggm_prg_node`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.GgmNodeLoopOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. The kernel: a GGM node-expansion loop with a real per-node call -/

/-- One GGM node: `child := ggm_prg_node(parent)` — a genuine `extCall` (lowered to
    a real `Lcall`) over the single `reg 64` node accumulator, with the trip index
    in scope. -/
def ggmNodeCallBody : JLoopBodyN (.reg 64) [] :=
  ⟨3, .var (.mk (.extCall "ggm_prg_node" [.reg 64] (.reg 64)) rfl
              (.cons .here .nil))
        (.ret .here)⟩

/-- The rolled GGM node-expansion loop: `n = 3` nodes, each
    `acc := ggm_prg_node(acc)`, via `.forLoopN` — one body copy, a real `jne`
    back-edge, and a real `call ggm_prg_node`. -/
def ggmNodeLoopProg : ComL [JasminTy.reg 64] (JasminTy.reg 64) :=
  .forLoopN ggmNodeCallBody .here .nil (.ret .here)

/-! ## 2. The barrier is engaged end-to-end (real in-loop call) -/

/-- The program is recognised as an in-loop-call `ComL`, so the call-walk engages. -/
theorem ggmNodeLoopProg_hasLoopCall : comLHasLoopCall ggmNodeLoopProg = true := by decide

/-- The virtual lowered body uses a **real `Lcall`** (not a `CALL:` shadow), so
    `bodyHasCall` fires (the barrier-gating predicate). -/
theorem ggmNodeLoopProg_virt_hasCall :
    bodyHasCall (ComL.toLfundef ggmNodeLoopProg).lfd_body = true := by decide

/-- The full physical export keeps `bodyHasCall` true (the body still issues the
    real `Lcall` after register allocation), so the barrier stays engaged. -/
theorem ggmNodeLoopProg_phys_hasCall :
    bodyHasCall (ComL.toLfundefPhys ggmNodeLoopProg).lfd_body = true := by native_decide

/-- **Exactly one genuine `LinstrR.Lcall` survives** register allocation — the real
    `call ggm_prg_node`, not a `CALL:` shadow `Lopn`. -/
theorem ggmNodeLoopProg_one_real_Lcall :
    ((ComL.toLfundefPhys ggmNodeLoopProg).lfd_body.filter (fun i =>
      match i.li_i with | .Lcall _ _ => true | _ => false)).length = 1 := by native_decide

/-- The surviving call targets the GGM PRG node leaf `ggm_prg_node`. -/
theorem ggmNodeLoopProg_calls_prg_node :
    (ComL.toLfundefPhys ggmNodeLoopProg).lfd_body.any (fun i =>
      match i.li_i with | .Lcall _ (f, _) => f == "ggm_prg_node" | _ => false) = true := by
  native_decide

/-- **No loop-carried value lands in a SysV caller-saved register.** Every
    register operand of the exported body is either a literal SysV ABI register
    (`RDI` marshal / `RAX` return) or callee-saved — so the in-body `call` cannot
    clobber the accumulator, loop index, or trip counter. -/
theorem ggmNodeLoopProg_no_loopcarried_caller_saved :
    (ComL.toLfundefPhys ggmNodeLoopProg).lfd_body.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs => (dsts ++ srcs).all (fun o =>
          match o with
          | .reg n => !sysvCallerSaved.contains n || n == "RDI" || n == "RAX"
          | _ => true)
      | _ => true) = true := by native_decide

/-! ## 3. The owned ROLLED emission (physical register allocation) -/

/-- The exported physical `lprog` for the GGM node loop. -/
def ggmNodeLoopLprog (fname : String := "ggm_node_loop") : Lprog :=
  ComL.toLprogPhys ggmNodeLoopProg fname

/-- The rendered, assemblable AT&T `.s`: real registers, one `call ggm_prg_node`,
    a real `jne .L` back-edge — the loop-carried accumulator preserved callee-saved
    across the call. -/
def ggmNodeLoopAsm (fname : String := "ggm_node_loop") : String :=
  renderLprogAtt (ggmNodeLoopLprog fname)

/-- Write the assemblable physical `.s` of the GGM node loop to the bench gen
    directory, so the orchestrator can re-emit + `gcc -c` + byte-KAT it against the
    faest-ref per-node PRG (`prg_2_lambda`). -/
def writeGgmNodeLoopAsm
    (path : System.FilePath :=
      "bench/faest_ggm_owned/gen/ggm_node_loop_owned.s")
    (fname : String := "ggm_node_loop") : IO Unit :=
  IO.FS.writeFile path (ggmNodeLoopAsm fname)

end CatCrypt.Crypto.SecureCompilation.VIR.GgmNodeLoopOwnedEmit
