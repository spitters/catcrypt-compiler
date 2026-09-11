/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
public import CatCrypt.Crypto.SecureCompilation.ScalarLinNeutral
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
public import Mathlib.Data.ZMod.Basic

/-!
# A real field kernel: modular addition `(a + b) mod p`, compiled both ways

A worked end-to-end field kernel over the scalar `RegProg` waist: 64-bit prime-field
addition `(a + b) mod p`, straight-line over the existing alphabet (an `add`, a
materialised `p`, and the branchless conditional subtract from `FieldReduceIdioms`).
Two results:

* `addmodProg_toNat` — **field-arithmetic correctness**: for `a, b < p` the program's
  result register holds `(a + b) mod p`. (No new primitive — the modular reduction is
  the verified branchless conditional subtract.)
* `addmodProg_arm` / `addmodProg_riscv` — the kernel **compiles to both backends** via
  the generic main theorems, with the machine run realising the `RegProg` denotation.

This is the template for migrating real field kernels: author the operation as a
straight-line `RegProg` (or, above it, a `Com`) over the alphabet, prove the value
correctness against the `ZMod`-style spec, and inherit both backends for free.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.AddModKernel

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-- Modular addition `(a + b) mod p` for a 64-bit prime `p`: an `add`, then the
    branchless conditional subtract of the sum against `p`. -/
def addmodProg (p : Nat) : RegProg :=
  [ .add "s" "a" "b",
    .loadImm "pc" p,
    .sub "d" "s" "pc",
    .loadImm "ones" 0xFFFFFFFFFFFFFFFF,
    .eor "sxp" "s" "pc",
    .eor "nsxp" "sxp" "ones",
    .and "t1" "nsxp" "d",
    .eor "ns" "s" "ones",
    .and "t2" "ns" "pc",
    .orr "bor0" "t2" "t1",
    .shrI "bor" "bor0" 63,
    .loadImm "zero" 0,
    .sub "mask" "zero" "bor",
    .and "r1" "s" "mask",
    .eor "nmask" "mask" "ones",
    .and "r2" "d" "nmask",
    .orr "res" "r1" "r2" ]

/-- The kernel's result register holds the branchless conditional subtract of `a + b`
    against `p` (the `^^^ (all ones)` complement matches `~~~`, closed by `bv_decide`). -/
theorem addmodProg_denote (p : Nat) (env : Env) :
    (RegProg.denotePure (addmodProg p) env) "res"
      = bCondSub (env "a" + env "b") (BitVec.ofNat 64 p) := by
  simp only [addmodProg, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.set, Env.get, bCondSub, bSltu, String.reduceEq, reduceIte]
  bv_decide

/-- **Field-arithmetic correctness.** For `a, b < p` (and `p < 2^63`, so `a + b` does
    not wrap), the kernel returns `(a + b) mod p`. -/
theorem addmodProg_toNat (p : Nat) (env : Env) (hp : 0 < p) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (addmodProg p) env) "res").toNat
      = ((env "a").toNat + (env "b").toNat) % p := by
  rw [addmodProg_denote]
  have hpc : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsum : ((env "a") + (env "b")).toNat = (env "a").toNat + (env "b").toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  rw [bCondSub_toNat _ _ (by rw [hpc]; omega) (by rw [hpc, hsum]; omega), hpc, hsum]

/-- The kernel compiles to AArch64: the machine run of the lowered block realises the
    `RegProg` denotation (generic main theorem). -/
theorem addmodProg_arm (p : Nat) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (addmodProg p))) = armTarget.denote (addmodProg p) s :=
  regToBOp_denote (addmodProg p) s

/-- …and to RISC-V. -/
theorem addmodProg_riscv (p : Nat) (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp (addmodProg p))) = rvTarget.denote (addmodProg p) s :=
  regToROp_denote (addmodProg p) s

/-! ## Modular subtraction `(a - b) mod p` — the same template -/

/-- Modular subtraction: `a - b`, then add `p` back via the branchless borrow mask. -/
def submodProg (p : Nat) : RegProg :=
  [ .sub "d" "a" "b",
    .loadImm "pc" p,
    .loadImm "ones" 0xFFFFFFFFFFFFFFFF,
    .eor "axb" "a" "b",
    .eor "naxb" "axb" "ones",
    .and "t1" "naxb" "d",
    .eor "na" "a" "ones",
    .and "t2" "na" "b",
    .orr "bor0" "t2" "t1",
    .shrI "bor" "bor0" 63,
    .loadImm "zero" 0,
    .sub "mask" "zero" "bor",
    .and "mp" "mask" "pc",
    .add "res" "d" "mp" ]

theorem submodProg_denote (p : Nat) (env : Env) :
    (RegProg.denotePure (submodProg p) env) "res"
      = bSubMod (env "a") (env "b") (BitVec.ofNat 64 p) := by
  simp only [submodProg, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure,
    Env.set, Env.get, bSubMod, bSltu, String.reduceEq, reduceIte]
  bv_decide

/-- **Field-arithmetic correctness.** For `a, b < p` the kernel returns `(a - b) mod p`
    (as `(a + p - b) mod p`). -/
theorem submodProg_toNat (p : Nat) (env : Env) (hp : 0 < p) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (submodProg p) env) "res").toNat
      = ((env "a").toNat + p - (env "b").toNat) % p := by
  rw [submodProg_denote]
  have hpc : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [bSubMod_toNat _ _ _ (by rw [hpc]; omega) (by rw [hpc]; omega) (by rw [hpc]; omega)
        (by rw [hpc]; omega), hpc]

theorem submodProg_arm (p : Nat) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp (submodProg p))) = armTarget.denote (submodProg p) s :=
  regToBOp_denote (submodProg p) s

theorem submodProg_riscv (p : Nat) (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp (submodProg p))) = rvTarget.denote (submodProg p) s :=
  regToROp_denote (submodProg p) s

/-! ## High-level spec link: the kernel computes `ZMod p` field addition

Tying the compiled kernel to Mathlib's prime field `ZMod p` — the result register
holds the `val` of the genuine field sum, not merely a `Nat` modulus. This is the
high-level mathlib-linked specification the kernel realises. -/

theorem addmodProg_zmod (p : Nat) [NeZero p] (env : Env) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (addmodProg p) env) "res").toNat
      = (((env "a").toNat : ZMod p) + ((env "b").toNat : ZMod p)).val := by
  rw [addmodProg_toNat p env (Nat.pos_of_ne_zero (NeZero.ne p)) hp64 ha hb,
      ← Nat.cast_add, ZMod.val_natCast]

/-- And the subtraction kernel computes `ZMod p` field subtraction. -/
theorem submodProg_zmod (p : Nat) [NeZero p] (env : Env) (hp64 : p < 2 ^ 63)
    (ha : (env "a").toNat < p) (hb : (env "b").toNat < p) :
    ((RegProg.denotePure (submodProg p) env) "res").toNat
      = (((env "a").toNat : ZMod p) - ((env "b").toNat : ZMod p)).val := by
  rw [submodProg_toNat p env (Nat.pos_of_ne_zero (NeZero.ne p)) hp64 ha hb]
  have hcast : (((env "a").toNat : ZMod p) - ((env "b").toNat : ZMod p))
      = (((env "a").toNat + p - (env "b").toNat : Nat) : ZMod p) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [hcast, ZMod.val_natCast]

end CatCrypt.Crypto.SecureCompilation.AddModKernel
