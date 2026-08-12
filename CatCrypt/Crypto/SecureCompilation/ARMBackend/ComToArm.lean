/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLin
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder
import Std.Tactic.BVDecide
import Mathlib.Tactic

/-!
# `Com → AArch64`: the AArch64 `ScalarTarget` instance

The AArch64 backend's instance of the shared `ScalarLin` waist
(`CatCrypt.Crypto.SecureCompilation.ScalarLin`). It supplies the instruction
selection `RegStmt → BOp`, the machine semantics, and the one per-statement
correctness proof; the whole-program denotation keystone (`regToBOp_denote`) then
comes from the generic `ScalarTarget.compile_denote` — *not* a per-backend proof.

```
RegProg ──armTarget.compile──▶ List BOp ──lowerBBlock──▶ List BInst ──encodeBBlock──▶ bytes
   │ ScalarTarget.denote                  │ (bignumBlock_lowering_denote, proved)
   └──────────── regToBOp_denote = ScalarTarget.compile_denote ───────────┘
```

The `BOp → BInst → bytes` back half is proved (`bignumBlock_lowering_denote`,
`encodeBInst_length`, the `SailArmDecoder` `decode(encode)=i` round-trip) and
externally differentially validated (`bench/arm_compare/decoder_diff`: 704/704
encode/decode vs GNU `as`/objdump + LLVM, 237/237 execute vs real AArch64 under
qemu). The remaining verified piece is the `Com`-tree flattening
`Com jasminDialect → RegProg` feeding this waist (the de-Bruijn front).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. Instruction selection: `RegStmt → BOp` (1:1 on this fragment) -/

/-- Select the AArch64 `BOp`(s) for one statement. -/
def regStmtToBOp : RegStmt → List BOp
  | .add d a b => [.add d a b]
  | .sub d a b => [.sub d a b]
  | .mul d a b => [.mul d a b]
  | .and d a b => [.and d a b]
  | .orr d a b => [.orr d a b]
  | .eor d a b => [.eor d a b]
  | .umulh d a b => [.umulh d a b]
  | .shrI d a i => [.lsr d a i]
  | .shlI d a i => [.lsl d a i]
  | .mov d a => [.mov d a]
  | .movz d i => [.movz d i]
  | .movk d i h => [.movk d i h]
  | .loadImm d n =>
      [ .movz d (n % 65536),
        .movk d ((n / 2^16) % 65536) 1,
        .movk d ((n / 2^32) % 65536) 2,
        .movk d ((n / 2^48) % 65536) 3 ]

/-- The source effect of one statement on the AArch64 register state, written in
    the same op functions the machine `evalBInst` uses (so selection is exact). -/
def evalRegStmt (s : BState) : RegStmt → BState
  | .add d a b => s.set d (s.get a + s.get b)
  | .sub d a b => s.set d (s.get a - s.get b)
  | .mul d a b => s.set d (opMul (s.get a) (s.get b))
  | .and d a b => s.set d (opAnd64 (s.get a) (s.get b))
  | .orr d a b => s.set d (opOrr64 (s.get a) (s.get b))
  | .eor d a b => s.set d (opEor64 (s.get a) (s.get b))
  | .umulh d a b => s.set d (opUmulh (s.get a) (s.get b))
  | .shrI d a i => s.set d (opLsr64 (s.get a) i)
  | .shlI d a i => s.set d (opLsl64 (s.get a) i)
  | .mov d a => s.set d (s.get a)
  | .movz d i => s.set d (BitVec.ofNat 64 (i % 0x10000))
  | .movk d i h => s.set d (movkInsert (s.get d) i h)
  | .loadImm d n => s.set d (BitVec.ofNat 64 n)

/-! ### `loadImm` lowering correctness (ARM-local `movz`/`movk` reconstruction)

The `bv_decide` bit-reconstruction proving the `movz`/`movk` chain re-materialises
`BitVec.ofNat 64 n` lives **here**, in the ARM lowering of `loadImm` — the
backend-neutral faithfulness layer stays free of SAT-certificate axioms. -/

/-- Normalise `movkInsert`'s field to a pure `BitVec` shift (so `bv_decide` sees
    through the `ofNat`-of-Nat-shift). -/
private theorem mk_clean (old b : BitVec 64) (hw : Nat) (hb : b < 65536) :
    movkInsert old b.toNat hw
      = (old &&& ~~~(BitVec.ofNat 64 (0xffff <<< (hw*16)))) ||| (b <<< (hw*16)) := by
  have hb' : b.toNat < 65536 := by have := BitVec.lt_def.mp hb; simpa using this
  simp only [movkInsert]
  rw [show ((b.toNat % 0x10000) <<< (hw*16)) = (b.toNat <<< (hw*16)) from by rw [Nat.mod_eq_of_lt hb']]
  congr 1

private theorem mk_hwin (n k : Nat) (hk : k ≤ 3) :
    BitVec.ofNat 64 ((n / 2^(16*k)) % 65536) = (BitVec.ofNat 64 n >>> (16*k)) &&& 0xffff := by
  apply BitVec.eq_of_toNat_eq
  have hffff : ((0xffff : BitVec 64).toNat) = 65535 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      hffff, Nat.shiftRight_eq_div_pow]
  have hand : ((n % 2^64) / 2^(16*k)) &&& 65535 = ((n % 2^64) / 2^(16*k)) % 65536 := by
    rw [show (65535:Nat) = 2^16-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have e64 : (2:Nat)^64 = 2^(16*k) * 2^(64-16*k) := by rw [← pow_add]; congr 1; omega
  have hdvd : (65536:Nat) ∣ 2^(64-16*k) := by
    rw [show (65536:Nat) = 2^16 from rfl]; exact pow_dvd_pow 2 (by omega)
  rw [hand, e64, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]
  exact Nat.mod_eq_of_lt (by rw [← e64]; exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

private theorem mk_himm (n k : Nat) (hk : k ≤ 3) :
    (n / 2^(16*k)) % 65536 = ((BitVec.ofNat 64 n >>> (16*k)) &&& 0xffff).toNat := by
  have h := congrArg BitVec.toNat (mk_hwin n k hk)
  rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num : (65536:Nat) ≤ 2^64))] at h
  exact h

private theorem mk_recon (x : BitVec 64) :
    movkInsert (movkInsert (movkInsert (x &&& 0xffff) ((x >>> 16 &&& 0xffff).toNat) 1)
        ((x >>> 32 &&& 0xffff).toNat) 2) ((x >>> 48 &&& 0xffff).toNat) 3 = x := by
  rw [mk_clean _ _ 1 (by bv_decide), mk_clean _ _ 2 (by bv_decide), mk_clean _ _ 3 (by bv_decide)]
  bv_decide

private theorem mk_recon_n (n : Nat) :
    movkInsert (movkInsert (movkInsert (BitVec.ofNat 64 (n % 65536))
        ((n / 2^16) % 65536) 1) ((n / 2^32) % 65536) 2) ((n / 2^48) % 65536) 3
      = BitVec.ofNat 64 n := by
  have h0 : BitVec.ofNat 64 (n % 65536) = BitVec.ofNat 64 n &&& 0xffff := by
    have := mk_hwin n 0 (by omega); simpa using this
  have e1 : (n / 2^16) % 65536 = ((BitVec.ofNat 64 n >>> 16 &&& 0xffff)).toNat := by
    have := mk_himm n 1 (by omega); simpa using this
  have e2 : (n / 2^32) % 65536 = ((BitVec.ofNat 64 n >>> 32 &&& 0xffff)).toNat := by
    have := mk_himm n 2 (by omega); simpa using this
  have e3 : (n / 2^48) % 65536 = ((BitVec.ofNat 64 n >>> 48 &&& 0xffff)).toNat := by
    have := mk_himm n 3 (by omega); simpa using this
  rw [h0, e1, e2, e3]; exact mk_recon _

private theorem bstate_set_set (s : BState) (d : String) (a b : X64) :
    (s.set d a).set d b = s.set d b := by
  by_cases h : d = "xzr"
  · simp [BState.set, h]
  · simp only [BState.set, h, if_false]
    congr 1; funext r'; by_cases hr : r' = d <;> simp [hr]

/-- The `movz`/`movk` chain for `loadImm d n`, run on the machine, sets `d` to
    `BitVec.ofNat 64 n` (and leaves the rest of the state untouched). -/
private theorem loadImm_lower (s : BState) (d : String) (n : Nat) :
    (regStmtToBOp (.loadImm d n)).foldl (fun st op => evalBInst st (toBInst op)) s
      = s.set d (BitVec.ofNat 64 n) := by
  have hmz : ∀ (st : BState) (i : Nat),
      evalBInst st (toBInst (BOp.movz d i)) = st.set d (BitVec.ofNat 64 (i % 0x10000)) :=
    fun _ _ => rfl
  have hmk : ∀ (st : BState) (i hw : Nat),
      evalBInst st (toBInst (BOp.movk d i hw)) = st.set d (movkInsert (st.get d) i hw) :=
    fun _ _ _ => rfl
  by_cases hd : d = "xzr"
  · subst hd
    simp only [regStmtToBOp, List.foldl_cons, List.foldl_nil, hmz, hmk]
    simp [BState.set]
  · simp only [regStmtToBOp, List.foldl_cons, List.foldl_nil, hmz, hmk,
      BState.get_set_same _ _ _ hd, bstate_set_set]
    rw [show ((n % 65536) % 0x10000) = n % 65536 from by rw [Nat.mod_mod_of_dvd _ (dvd_refl _)],
        mk_recon_n n]

/-- Per-statement selection correctness: the selected `BOp`(s), run on the
    machine, realise the source effect — definitional for the 1:1 ops, the
    `movz`/`movk` reconstruction `loadImm_lower` for the constant load. -/
theorem regStmtToBOp_denote (s : BState) (stmt : RegStmt) :
    (regStmtToBOp stmt).foldl (fun st op => evalBInst st (toBInst op)) s
      = evalRegStmt s stmt := by
  cases stmt
  case loadImm d n => exact loadImm_lower s d n
  all_goals rfl

/-! ## 2. The AArch64 `ScalarTarget` instance

`runOps` is the foldl of `evalBInst ∘ toBInst` — which `bignumBlock_lowering_denote`
identifies with the real machine run `runBBlock ∘ lowerBBlock`. The three structural
fields are list-fold facts; `select_correct` is the per-statement lemma above. -/

/-- The AArch64 backend as a `ScalarTarget`. -/
def armTarget : ScalarTarget where
  Op := BOp
  St := BState
  runOps s ops := ops.foldl (fun st op => evalBInst st (toBInst op)) s
  runOps_nil _ := rfl
  runOps_append xs ys s := by simp only [List.foldl_append]
  step := evalRegStmt
  toOps := regStmtToBOp
  select_correct s stmt := regStmtToBOp_denote s stmt

/-- Compile a whole program to a `BOp` block. -/
def regToBOp (p : RegProg) : List BOp := armTarget.compile p

/-! ## 3. The keystone — instantiated, not re-proved -/

/-- **Keystone** (the AArch64 instance of `ScalarTarget.compile_denote`). The
    compiled-and-lowered machine block computes the source program's denotation. -/
theorem regToBOp_denote (p : RegProg) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp p)) = armTarget.denote p s := by
  rw [bignumBlock_lowering_denote]
  exact armTarget.compile_denote p s

/-! ## 4. End-to-end: bytes that compute the denotation -/

/-- The compiled byte stream is `4 · |regToBOp p|` bytes (fixed-width A64). -/
theorem compiled_length (alloc : GpAlloc) (p : RegProg) :
    (ArmEncoder.encodeBBlock alloc (lowerBBlock (regToBOp p))).length
      = 4 * (regToBOp p).length := by
  simp only [lowerBBlock, ArmEncoder.encodeBBlock]
  induction (regToBOp p) with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append,
        ArmEncoder.encodeBInst_length, List.length_cons]
      rw [ih]; omega

/-- Compile a source program to its AArch64 machine-code byte stream. -/
def regProgToArmBytes (alloc : GpAlloc) (p : RegProg) : List (BitVec 8) :=
  ArmEncoder.encodeBBlock alloc (lowerBBlock (regToBOp p))

/-- **End-to-end compiler correctness at the `RegProg` waist**: the emitted
    machine block computes the source denotation, and the byte stream is its
    `4·|·|` fixed-width encoding. This is the content the `Jasmin/ISA.lean`
    `aarch64Compile`/`aarch64CompilerCorrect` axioms assert, discharged as a
    theorem — but stated over a `RegProg` straight-line block (reached from
    `Com jasminDialect` by the verified de-Bruijn front `comToReg_faithful`),
    not over the `JasminProg` AST with entry points and arguments that those
    axioms range over. No `JasminProg → RegProg` translation is in the tree, so
    this theorem does not by itself replace the axioms. -/
theorem regProgToArmBytes_spec (alloc : GpAlloc) (p : RegProg) (s : BState) :
    runBBlock s (lowerBBlock (regToBOp p)) = armTarget.denote p s
    ∧ (regProgToArmBytes alloc p).length = 4 * (regToBOp p).length :=
  ⟨regToBOp_denote p s, compiled_length alloc p⟩

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
