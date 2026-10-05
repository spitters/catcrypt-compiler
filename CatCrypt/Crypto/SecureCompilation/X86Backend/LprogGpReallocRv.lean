/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa

/-!
# The general-purpose register re-allocation at the RV64 register file

`LprogGpRealloc.reallocRun` takes its register file as a parameter. This module
instantiates it at the RV64 data `RvIsa.rvData`: the pool is the RV64 allocation pool, an
x86 register is not a pool register, and a three-instruction run with a frame cell is
re-allocated into RV64 pool registers.

## Main results

* `poolOrder_rv`: the pool at `rvData` is `a0`–`a7`, `t0`–`t4`.
* `isPool_rv_RAX`, `isLoc_rv_t6`: `RAX` is not an RV64 pool register; the scratch `t6` is
  a location.
* `isaRecognized_rv`: the alphabet of `rvData` is `isRecognizedOpn`, since `rvData` has no
  implicit register read.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocRv

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvIsa (rvData)

/-- The pool the allocator colours with at `rvData` is the RV64 allocation pool. -/
theorem poolOrder_rv :
    poolOrder rvData.toIsaAbi =
      ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4"] := rfl

/-- The x86 register `RAX` is not a pool register at `rvData`. -/
theorem isPool_rv_RAX : isPool "RAX" rvData.toIsaAbi = false := by decide

/-- The RV64 scratch register `t6` is a location at `rvData`. -/
theorem isLoc_rv_t6 : isLoc "t6" rvData.toIsaAbi = true := by decide

/-- The fragment alphabet of `rvData` is the recognised alphabet: `rvData` gives no
    mnemonic an implicit register read. -/
theorem isaRecognized_rv (opn : String) : isaRecognized rvData opn = isRecognizedOpn opn :=
  rfl

/-- A three-instruction run over RV64 register names: a frame cell `k.0` receives `a1`, is
    added to `a2` and is copied to the live-out register `a0`. -/
def rvRun : List FI :=
  [⟨0, "k.0", "MOV:64", [.reg "a1"]⟩, ⟨1, "k.0", "ADD:64", [.reg "k.0", .reg "a2"]⟩,
   ⟨2, "a0", "MOV:64", [.reg "k.0"]⟩]

-- At `rvData` the frame cell is promoted to the RV64 pool register `a1`.
#kat (reallocRun ["a0"] rvRun rvData.toIsaAbi).map (fun i => (i.d, i.opn, i.srcs)) ==
  [("a1", "ADD:64", [.reg "a1", .reg "a2"]), ("a0", "MOV:64", [.reg "a1"])]

-- At the default `x86Abi` the same run is promoted to the x86 pool register `RAX`.
#kat (reallocRun ["a0"] rvRun).map (fun i => (i.d, i.opn, i.srcs)) ==
  [("RAX", "MOV:64", [.reg "a1"]), ("RAX", "ADD:64", [.reg "RAX", .reg "a2"]),
   ("a0", "MOV:64", [.reg "RAX"])]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocRv
