/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.PlonkyBabyBearKernel
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-!
# A whole plonky3 operation routed through the compiler

The BabyBear field kernels (`bbMulProg`, `bbAddProg`) are each a compiled, value-correct
`RegProg`. plonky3's higher operations are built from them; here we assemble one — the
**FRI fold** `f' = fEven + β·fOdd`, the inner step of plonky3's low-degree test — as a
single `RegProg` by sequencing the compiled multiply and add kernels (`++` is the
sequencing law `denotePure_append`), routing registers with `mov`.

The result `bbFriFoldProg`:
* `bbFriFold_zmod` — computes the `ZMod babyBear` fold value;
* `bbFriFold_arm` / `bbFriFold_riscv` — compiles to both backends.

Composition needs one ingredient — that a kernel leaves the registers it never writes
untouched (`denotePure_app_ne`), so an input held across a kernel call survives.
-/

namespace CatCrypt.Crypto.SecureCompilation.PlonkyRouting

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.MulModKernel
open CatCrypt.Crypto.SecureCompilation.AddModKernel
open CatCrypt.Crypto.SecureCompilation.PlonkyBabyBearKernel
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## Register preservation (the sequencing enabler) -/

/-- The register a statement writes. -/
def RegStmt.dst : RegStmt → String
  | .add d _ _ => d | .sub d _ _ => d | .mul d _ _ => d | .and d _ _ => d
  | .orr d _ _ => d | .eor d _ _ => d | .umulh d _ _ => d | .shrI d _ _ => d
  | .shlI d _ _ => d | .mov d _ => d | .movz d _ => d | .movk d _ _ => d
  | .loadImm d _ => d

/-- Writing one register leaves a different one untouched (read by application). -/
theorem set_app_ne (e : Env) (d : String) (v : BitVec 64) (r : String) (h : r ≠ d) :
    (Env.set e d v) r = e r := by
  unfold Env.set; split
  · rfl
  · simp [h]

/-- One statement leaves any register it does not write untouched. -/
theorem evalRegStmtPure_app_ne (e : Env) (s : RegStmt) (r : String) (h : r ≠ RegStmt.dst s) :
    (evalRegStmtPure e s) r = e r := by
  cases s <;> exact set_app_ne e _ _ r h

/-- A program leaves untouched any register none of its statements write. -/
theorem denotePure_app_ne (r : String) : ∀ (p : RegProg) (e : Env),
    (∀ s ∈ p, r ≠ RegStmt.dst s) → (RegProg.denotePure p e) r = e r
  | [], _, _ => rfl
  | s :: p, e, h => by
      rw [RegProg.denotePure_cons,
        denotePure_app_ne r p (evalRegStmtPure e s)
          (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')),
        evalRegStmtPure_app_ne e s r (h s List.mem_cons_self)]

/-- A register outside a program's list of destinations is written by none of its
    statements. -/
theorem ne_dst_of_not_mem_dsts (r : String) (p : RegProg) (h : r ∉ p.map RegStmt.dst) :
    ∀ s ∈ p, r ≠ RegStmt.dst s :=
  fun s hs hr => h (List.mem_map.mpr ⟨s, hs, hr.symm⟩)

/-- The destination registers of the BabyBear multiply kernel, in order. -/
theorem bbMulProg_dsts :
    bbMulProg.map RegStmt.dst =
      ["x", "muc", "q", "pc", "qp", "r", "ones", "zero", "d", "rxp", "nrxp", "t1", "nr", "t2",
       "bor0", "bor", "mask", "r1", "nmask", "r2", "res"] := rfl

/-- The destination registers of the BabyBear add kernel, in order. -/
theorem bbAddProg_dsts :
    bbAddProg.map RegStmt.dst =
      ["s", "pc", "d", "ones", "sxp", "nsxp", "t1", "ns", "t2", "bor0", "bor", "zero", "mask",
       "r1", "nmask", "r2", "res"] := rfl

/-- The destination registers of the modular-subtract kernel, in order. -/
theorem submodProg_dsts (p : Nat) :
    (submodProg p).map RegStmt.dst =
      ["d", "pc", "ones", "axb", "naxb", "t1", "na", "t2", "bor0", "bor", "zero", "mask", "mp",
       "res"] := rfl

/-! ## The FRI fold, routed through the compiler -/

/-- plonky3's FRI fold `fEven + β·fOdd` over BabyBear: copy `(β, fOdd)` into the
    multiply kernel's inputs, run `bbMulProg`, copy `(fEven, β·fOdd)` into the add
    kernel's inputs, run `bbAddProg`. Inputs in `fe`, `be`, `fo`; result in `res`. -/
def bbFriFoldProg : RegProg :=
  [RegStmt.mov "a" "be", RegStmt.mov "b" "fo"] ++ bbMulProg
    ++ [RegStmt.mov "a" "fe", RegStmt.mov "b" "res"] ++ bbAddProg

/-- `fe` is not written by the multiply kernel, so it survives the call. -/
theorem fe_fresh_mul : ∀ s ∈ bbMulProg, "fe" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [bbMulProg_dsts])

/-- The composed program computes the `ZMod babyBear` FRI fold. -/
theorem bbFriFold_zmod (env : Env)
    (hfe : (env "fe").toNat < babyBear) (hbe : (env "be").toNat < babyBear)
    (hfo : (env "fo").toNat < babyBear) :
    ((RegProg.denotePure bbFriFoldProg env) "res").toNat
      = (((env "fe").toNat : ZMod babyBear)
          + ((env "be").toNat : ZMod babyBear) * ((env "fo").toNat : ZMod babyBear)).val := by
  -- e1: after the input movs for the multiply
  set e1 := RegProg.denotePure [RegStmt.mov "a" "be", RegStmt.mov "b" "fo"] env with he1
  have he1a : e1 "a" = env "be" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1b : e1 "b" = env "fo" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1fe : e1 "fe" = env "fe" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  -- e2: after the multiply kernel
  set e2 := RegProg.denotePure bbMulProg e1 with he2
  have he2res : (e2 "res").toNat = ((env "be").toNat * (env "fo").toNat) % babyBear := by
    have := mulmodProg_toNat babyBear e1 babyBear_pos babyBear_lt (by rw [he1a]; exact hbe)
      (by rw [he1b]; exact hfo)
    rw [he1a, he1b] at this; exact this
  have he2fe : e2 "fe" = env "fe" := by
    rw [he2, denotePure_app_ne "fe" bbMulProg e1 fe_fresh_mul, he1fe]
  -- e3: after the input movs for the add
  set e3 := RegProg.denotePure [RegStmt.mov "a" "fe", RegStmt.mov "b" "res"] e2 with he3
  have he3a : e3 "a" = env "fe" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
    rw [he2fe]
  have he3b : e3 "b" = e2 "res" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  -- final add kernel
  have hba : (e3 "a").toNat < babyBear := by rw [he3a]; exact hfe
  have hbb : (e3 "b").toNat < babyBear := by
    rw [he3b, he2res]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (le_refl _)
  have hfinal : ((RegProg.denotePure bbFriFoldProg env) "res").toNat
      = ((e3 "a").toNat + (e3 "b").toNat) % babyBear := by
    rw [bbFriFoldProg, RegProg.denotePure_append, RegProg.denotePure_append,
      RegProg.denotePure_append, ← he1, ← he2, ← he3]
    exact addmodProg_toNat babyBear e3 (by decide) (by decide) hba hbb
  -- cast to ZMod: the inner `% babyBear` is absorbed by the field cast
  have hrhs : (((env "fe").toNat : ZMod babyBear)
      + ((env "be").toNat : ZMod babyBear) * ((env "fo").toNat : ZMod babyBear)).val
      = ((env "fe").toNat + (env "be").toNat * (env "fo").toNat) % babyBear := by
    rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.val_natCast]
  rw [hfinal, he3a, he3b, he2res, hrhs, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- The composed fold compiles to AArch64: the machine run of the lowered block
    realises the whole program's `RegProg` denotation. -/
theorem bbFriFold_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp bbFriFoldProg)) = armTarget.denote bbFriFoldProg s :=
  regToBOp_denote bbFriFoldProg s

/-- …and to RISC-V. -/
theorem bbFriFold_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp bbFriFoldProg)) = rvTarget.denote bbFriFoldProg s :=
  regToROp_denote bbFriFoldProg s

/-! ## Poseidon S-box, routed through the compiler

The chaining helpers: a multiply kernel's result, cast to `ZMod`, is the product of
its inputs' field values, and stays below the modulus — so its `.toNat` feeds the next
kernel directly (the `% babyBear` absorbed by the field cast). -/

/-- The multiply kernel's result cast to `ZMod` is the field product of its inputs. -/
theorem bbMul_resZMod (e : Env) (ha : (e "a").toNat < babyBear) (hb : (e "b").toNat < babyBear) :
    (((RegProg.denotePure bbMulProg e) "res").toNat : ZMod babyBear)
      = ((e "a").toNat : ZMod babyBear) * ((e "b").toNat : ZMod babyBear) := by
  rw [bbMul_zmod e ha hb, ZMod.natCast_zmod_val]

/-- …and stays below the modulus. -/
theorem bbMul_resLt (e : Env) (ha : (e "a").toNat < babyBear) (hb : (e "b").toNat < babyBear) :
    ((RegProg.denotePure bbMulProg e) "res").toNat < babyBear := by
  rw [bbMul_zmod e ha hb]; exact ZMod.val_lt _

/-- `fx` is not written by the multiply kernel, so it survives each call. -/
theorem fx_fresh_mul : ∀ s ∈ bbMulProg, "fx" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [bbMulProg_dsts])

/-- plonky3's Poseidon S-box `x^5 = ((x·x)·(x·x))·x` over BabyBear: three multiply
    kernels chained, squaring then squaring then one more multiply. Input `fx`, result
    `res`. -/
def bbSboxProg : RegProg :=
  [RegStmt.mov "a" "fx", RegStmt.mov "b" "fx"] ++ bbMulProg
    ++ [RegStmt.mov "s2" "res", RegStmt.mov "a" "s2", RegStmt.mov "b" "s2"] ++ bbMulProg
    ++ [RegStmt.mov "s4" "res", RegStmt.mov "a" "s4", RegStmt.mov "b" "fx"] ++ bbMulProg

/-- The composed program computes the `ZMod babyBear` S-box `x^5`. -/
theorem bbSbox_zmod (env : Env) (hx : (env "fx").toNat < babyBear) :
    ((RegProg.denotePure bbSboxProg env) "res").toNat
      = (((env "fx").toNat : ZMod babyBear) ^ 5).val := by
  -- e1: inputs (x, x) for the first square
  set e1 := RegProg.denotePure [RegStmt.mov "a" "fx", RegStmt.mov "b" "fx"] env with he1
  have he1a : e1 "a" = env "fx" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1b : e1 "b" = env "fx" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1fx : e1 "fx" = env "fx" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have ha1 : (e1 "a").toNat < babyBear := by rw [he1a]; exact hx
  have hb1 : (e1 "b").toNat < babyBear := by rw [he1b]; exact hx
  -- m1 = x²
  set m1 := RegProg.denotePure bbMulProg e1 with hm1
  have hm1z : ((m1 "res").toNat : ZMod babyBear) = ((env "fx").toNat : ZMod babyBear) ^ 2 := by
    rw [hm1, bbMul_resZMod e1 ha1 hb1, he1a, he1b, sq]
  have hm1lt : (m1 "res").toNat < babyBear := by rw [hm1]; exact bbMul_resLt e1 ha1 hb1
  have hm1fx : m1 "fx" = env "fx" := by
    rw [hm1, denotePure_app_ne "fx" bbMulProg e1 fx_fresh_mul, he1fx]
  -- e2: inputs (x², x²) for the second square
  set e2 := RegProg.denotePure [RegStmt.mov "s2" "res", RegStmt.mov "a" "s2", RegStmt.mov "b" "s2"] m1
    with he2
  have he2a : e2 "a" = m1 "res" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he2b : e2 "b" = m1 "res" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he2fx : e2 "fx" = env "fx" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]; rw [hm1fx]
  have ha2 : (e2 "a").toNat < babyBear := by rw [he2a]; exact hm1lt
  have hb2 : (e2 "b").toNat < babyBear := by rw [he2b]; exact hm1lt
  -- m2 = x⁴
  set m2 := RegProg.denotePure bbMulProg e2 with hm2
  have hm2z : ((m2 "res").toNat : ZMod babyBear) = ((env "fx").toNat : ZMod babyBear) ^ 4 := by
    rw [hm2, bbMul_resZMod e2 ha2 hb2, he2a, he2b, hm1z]; ring
  have hm2lt : (m2 "res").toNat < babyBear := by rw [hm2]; exact bbMul_resLt e2 ha2 hb2
  have hm2fx : m2 "fx" = env "fx" := by
    rw [hm2, denotePure_app_ne "fx" bbMulProg e2 fx_fresh_mul, he2fx]
  -- e3: inputs (x⁴, x) for the final multiply
  set e3 := RegProg.denotePure [RegStmt.mov "s4" "res", RegStmt.mov "a" "s4", RegStmt.mov "b" "fx"] m2
    with he3
  have he3a : e3 "a" = m2 "res" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he3b : e3 "b" = env "fx" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]; rw [hm2fx]
  have ha3 : (e3 "a").toNat < babyBear := by rw [he3a]; exact hm2lt
  have hb3 : (e3 "b").toNat < babyBear := by rw [he3b]; exact hx
  -- m3 = x⁵
  have hm3z : (((RegProg.denotePure bbMulProg e3) "res").toNat : ZMod babyBear)
      = ((env "fx").toNat : ZMod babyBear) ^ 5 := by
    rw [bbMul_resZMod e3 ha3 hb3, he3a, he3b, hm2z]; ring
  have hm3lt : ((RegProg.denotePure bbMulProg e3) "res").toNat < babyBear := bbMul_resLt e3 ha3 hb3
  -- assemble
  have hfinal : (RegProg.denotePure bbSboxProg env) "res" = (RegProg.denotePure bbMulProg e3) "res" := by
    rw [bbSboxProg, RegProg.denotePure_append, RegProg.denotePure_append,
      RegProg.denotePure_append, RegProg.denotePure_append, RegProg.denotePure_append,
      ← he1, ← hm1, ← he2, ← hm2, ← he3]
  rw [hfinal]
  have hv := congrArg ZMod.val hm3z
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm3lt] at hv
  exact hv

/-- The S-box compiles to AArch64. -/
theorem bbSbox_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp bbSboxProg)) = armTarget.denote bbSboxProg s :=
  regToBOp_denote bbSboxProg s

/-- …and to RISC-V. -/
theorem bbSbox_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp bbSboxProg)) = rvTarget.denote bbSboxProg s :=
  regToROp_denote bbSboxProg s

/-! ## NTT butterfly, routed through the compiler

The radix-2 butterfly `(a, b) ↦ (a + ω·b, a − ω·b)` — one multiply (`ω·b`), one add
(`a + ω·b` → `o0`), one modular subtract (`a − ω·b` → `res`) — chaining the compiled
BabyBear kernels and holding `a` and `ω·b` across the calls via register preservation. -/

theorem fa_fresh_mul : ∀ s ∈ bbMulProg, "fa" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [bbMulProg_dsts])

theorem fa_fresh_add : ∀ s ∈ bbAddProg, "fa" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [bbAddProg_dsts])

theorem wb_fresh_add : ∀ s ∈ bbAddProg, "wb" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [bbAddProg_dsts])

theorem o0_fresh_sub : ∀ s ∈ submodProg babyBear, "o0" ≠ RegStmt.dst s :=
  ne_dst_of_not_mem_dsts _ _ (by simp [submodProg_dsts])

/-- plonky3's radix-2 NTT butterfly over BabyBear. Inputs `fa = a`, `fw = ω`,
    `fb = b`; outputs `o0 = a + ω·b` and `res = a − ω·b`. -/
def bbButterflyProg : RegProg :=
  [RegStmt.mov "a" "fw", RegStmt.mov "b" "fb"] ++ bbMulProg
    ++ [RegStmt.mov "wb" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] ++ bbAddProg
    ++ [RegStmt.mov "o0" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] ++ submodProg babyBear

/-- Shared setup: the value-and-preservation facts up to (and including) the add kernel. -/
private theorem bb_butterfly_pre (env : Env)
    (hfa : (env "fa").toNat < babyBear) (hfw : (env "fw").toNat < babyBear)
    (hfb : (env "fb").toNat < babyBear) :
    ∃ ma : Env,
      RegProg.denotePure ([RegStmt.mov "a" "fw", RegStmt.mov "b" "fb"] ++ bbMulProg
        ++ [RegStmt.mov "wb" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] ++ bbAddProg) env
        = ma
      ∧ ma "fa" = env "fa"
      ∧ (((ma "wb").toNat : ZMod babyBear)
          = ((env "fw").toNat : ZMod babyBear) * ((env "fb").toNat : ZMod babyBear))
      ∧ (ma "wb").toNat < babyBear
      ∧ (env "fa").toNat < babyBear
      ∧ ((ma "res").toNat
          = (((env "fa").toNat : ZMod babyBear)
              + ((env "fw").toNat : ZMod babyBear) * ((env "fb").toNat : ZMod babyBear)).val) := by
  -- e1, m1 (the multiply), e2, ma (the add)
  set e1 := RegProg.denotePure [RegStmt.mov "a" "fw", RegStmt.mov "b" "fb"] env with he1
  have he1a : e1 "a" = env "fw" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1b : e1 "b" = env "fb" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he1fa : e1 "fa" = env "fa" := by
    simp only [he1, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have ha1 : (e1 "a").toNat < babyBear := by rw [he1a]; exact hfw
  have hb1 : (e1 "b").toNat < babyBear := by rw [he1b]; exact hfb
  set m1 := RegProg.denotePure bbMulProg e1 with hm1
  have hm1z : ((m1 "res").toNat : ZMod babyBear)
      = ((env "fw").toNat : ZMod babyBear) * ((env "fb").toNat : ZMod babyBear) := by
    rw [hm1, bbMul_resZMod e1 ha1 hb1, he1a, he1b]
  have hm1lt : (m1 "res").toNat < babyBear := by rw [hm1]; exact bbMul_resLt e1 ha1 hb1
  have hm1fa : m1 "fa" = env "fa" := by
    rw [hm1, denotePure_app_ne "fa" bbMulProg e1 fa_fresh_mul, he1fa]
  set e2 := RegProg.denotePure [RegStmt.mov "wb" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] m1
    with he2
  have he2a : e2 "a" = env "fa" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]; rw [hm1fa]
  have he2b : e2 "b" = m1 "res" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he2wb : e2 "wb" = m1 "res" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he2fa : e2 "fa" = env "fa" := by
    simp only [he2, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]; rw [hm1fa]
  have ha2 : (e2 "a").toNat < babyBear := by rw [he2a]; exact hfa
  have hb2 : (e2 "b").toNat < babyBear := by rw [he2b]; exact hm1lt
  refine ⟨RegProg.denotePure bbAddProg e2, ?_, ?_, ?_, ?_, hfa, ?_⟩
  · rw [RegProg.denotePure_append, RegProg.denotePure_append, RegProg.denotePure_append,
      ← he1, ← hm1, ← he2]
  · rw [denotePure_app_ne "fa" bbAddProg e2 fa_fresh_add, he2fa]
  · rw [denotePure_app_ne "wb" bbAddProg e2 wb_fresh_add, he2wb, hm1z]
  · rw [denotePure_app_ne "wb" bbAddProg e2 wb_fresh_add, he2wb]; exact hm1lt
  · rw [bbAddProg, addmodProg_zmod babyBear e2 (by decide) ha2 hb2, he2a, he2b, hm1z]

/-- The butterfly's first output `o0` is the field value `a + ω·b`. -/
theorem bbButterfly_o0_zmod (env : Env)
    (hfa : (env "fa").toNat < babyBear) (hfw : (env "fw").toNat < babyBear)
    (hfb : (env "fb").toNat < babyBear) :
    ((RegProg.denotePure bbButterflyProg env) "o0").toNat
      = (((env "fa").toNat : ZMod babyBear)
          + ((env "fw").toNat : ZMod babyBear) * ((env "fb").toNat : ZMod babyBear)).val := by
  obtain ⟨ma, hma, hmafa, hmawb, hmawblt, hfa', hmares⟩ := bb_butterfly_pre env hfa hfw hfb
  -- e3, then the subtract kernel; o0 survives the subtract
  set e3 := RegProg.denotePure [RegStmt.mov "o0" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] ma
    with he3
  have he3o0 : e3 "o0" = ma "res" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have hfinal : (RegProg.denotePure bbButterflyProg env) "o0"
      = (RegProg.denotePure (submodProg babyBear) e3) "o0" := by
    rw [bbButterflyProg, RegProg.denotePure_append, RegProg.denotePure_append, hma, ← he3]
  rw [hfinal, denotePure_app_ne "o0" (submodProg babyBear) e3 o0_fresh_sub, he3o0, hmares]

/-- The butterfly's second output `res` is the field value `a − ω·b`. -/
theorem bbButterfly_res_zmod (env : Env)
    (hfa : (env "fa").toNat < babyBear) (hfw : (env "fw").toNat < babyBear)
    (hfb : (env "fb").toNat < babyBear) :
    ((RegProg.denotePure bbButterflyProg env) "res").toNat
      = (((env "fa").toNat : ZMod babyBear)
          - ((env "fw").toNat : ZMod babyBear) * ((env "fb").toNat : ZMod babyBear)).val := by
  obtain ⟨ma, hma, hmafa, hmawb, hmawblt, hfa', hmares⟩ := bb_butterfly_pre env hfa hfw hfb
  set e3 := RegProg.denotePure [RegStmt.mov "o0" "res", RegStmt.mov "a" "fa", RegStmt.mov "b" "wb"] ma
    with he3
  have he3a : e3 "a" = ma "fa" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have he3b : e3 "b" = ma "wb" := by
    simp only [he3, RegProg.denotePure, List.foldl_cons, List.foldl_nil, evalRegStmtPure, Env.set,
      Env.get, String.reduceEq, reduceIte]
  have ha3 : (e3 "a").toNat < babyBear := by rw [he3a, hmafa]; exact hfa
  have hb3 : (e3 "b").toNat < babyBear := by rw [he3b]; exact hmawblt
  have hfinal : (RegProg.denotePure bbButterflyProg env) "res"
      = (RegProg.denotePure (submodProg babyBear) e3) "res" := by
    rw [bbButterflyProg, RegProg.denotePure_append, RegProg.denotePure_append, hma, ← he3]
  rw [hfinal, submodProg_zmod babyBear e3 (by decide) ha3 hb3, he3a, he3b, hmafa, hmawb]

/-- The butterfly compiles to AArch64. -/
theorem bbButterfly_arm (s : BState) :
    runBBlock s (lowerBBlock (regToBOp bbButterflyProg)) = armTarget.denote bbButterflyProg s :=
  regToBOp_denote bbButterflyProg s

/-- …and to RISC-V. -/
theorem bbButterfly_riscv (s : RState64) :
    runRBlock64 s (lowerRBlock64 (regToROp bbButterflyProg)) = rvTarget.denote bbButterflyProg s :=
  regToROp_denote bbButterflyProg s

end CatCrypt.Crypto.SecureCompilation.PlonkyRouting
