/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnLogical32Emit
import CatCrypt.Crypto.Jasmin.Examples.MpnLogicalPrototype
import CatCrypt.Crypto.Jasmin.Examples.MpnAdd32Refines

set_option autoImplicit false

/-!
# `mpn_{and,ior,xor}_n` Jasmin refinements at **U32 limb width**

This file is the U32 analogue of `MpnLogicalPrototype`'s three bridges
`MpnAndJasminRefines` / `MpnIorJasminRefines` / `MpnXorJasminRefines`:
the emitted `mpn_and_n_32` / `mpn_ior_n_32` / `mpn_xor_n_32` kernels
(`MpnLogical32Emit.mpnAndN32Fd` etc.) each refine the corresponding
limb-wise `BitVec 32` reference (`mpnAnd32` / `mpnIor32` / `mpnXor32`)
over byte memory with **4-byte limb stride**.

These are the *simplest* bounded-mpn kernels — no carry, no scalar
multiplication, just a single `Papp2` per limb.  Per-iteration body:

```
t = [:u32 ap + 0];
s = [:u32 bp + 0];
r = t OP s;          // single Papp2, no carry
[:u32 op + 0] = r;
ap += 4; bp += 4; op += 4; n -= 1;
```

Because there is no carry register, the bridge is structurally smaller
than the U32 add bridge: no `addCarryIn32` plumbing, no carry
correspondence lemma.

## Reuses

* `MpnAdd32Refines.memHoldsLimbs32` — 4-byte-stride memory predicate.
* `MpnAdd32Refines.memHoldsLimbs32_store32_range_frame` — frame lemma.
* `MpnAdd32Refines.u32_load_roundtrip` — `BitVec.ofNat 64 (UInt64.ofNat
  w.toNat).toNat = w64 w` round-trip.
* `MpnAdd32Refines.resolveAddr_vr64` — U64 pointer-register address
  resolution.
* `MpnAddPrototype`'s `regAddr_advance_at`, `range_op_head_tail_disjoint_4`,
  `bignumExecFuel_loop_step_generic` / `_exit_generic`,
  `evalPExpr_neq_zero_true` / `_false`, `disjoint_mono`,
  `disjoint_range_lt`, `ofNat64_succ_ne_zero`, `ofNat64_succ_sub_one`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnLogical32Refines

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnLogical32Emit
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnAdd32Refines

/-! ## §1  Pure U32 references — limb-wise BitVec.and/.or/.xor -/

/-- Pure reference for `mpn_and_n_32`. -/
def mpnAnd32 : List (BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | a :: as, b :: bs => (a &&& b) :: mpnAnd32 as bs
  | _, _ => []

/-- Pure reference for `mpn_ior_n_32`. -/
def mpnIor32 : List (BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | a :: as, b :: bs => (a ||| b) :: mpnIor32 as bs
  | _, _ => []

/-- Pure reference for `mpn_xor_n_32`. -/
def mpnXor32 : List (BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | a :: as, b :: bs => (a ^^^ b) :: mpnXor32 as bs
  | _, _ => []

theorem mpnAnd32_nil (a b : List (BitVec 32)) (h : a = [] ∨ b = []) : mpnAnd32 a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

theorem mpnIor32_nil (a b : List (BitVec 32)) (h : a = [] ∨ b = []) : mpnIor32 a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

theorem mpnXor32_nil (a b : List (BitVec 32)) (h : a = [] ∨ b = []) : mpnXor32 a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

/-! ## §2  Local `w64` shim and bit-parallelism on the loaded form

`MpnAdd32Refines.w64` is `private`, so we redefine the same `BitVec 32 →
BitVec 64` zero-extension locally.  The single key fact for the bitwise
kernels: AND/OR/XOR are bit-parallel, so they commute with the `w64`
zero-extension on `BitVec 32` operands. -/

/-- Local copy of `MpnAdd32Refines.w64` (which is `private`). -/
def w64 (w : BitVec 32) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- `u32_load_roundtrip` restated against the local `w64`. -/
theorem load_roundtrip (w : BitVec 32) :
    BitVec.ofNat 64 (UInt64.ofNat w.toNat).toNat = w64 w := by
  have hw : w.toNat < 2 ^ 32 := w.isLt
  apply BitVec.eq_of_toNat_eq
  unfold w64
  simp only [BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

/-- AND distributes over `w64` zero-extension: `w64 a &&& w64 b = w64 (a &&& b)`. -/
theorem w64_and (a b : BitVec 32) : w64 a &&& w64 b = w64 (a &&& b) := by
  unfold w64
  apply BitVec.eq_of_toNat_eq
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have habu : a.toNat &&& b.toNat < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_left ha
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show a.toNat &&& b.toNat < 2 ^ 64 from by omega)]

/-- OR distributes over `w64`. -/
theorem w64_or (a b : BitVec 32) : w64 a ||| w64 b = w64 (a ||| b) := by
  unfold w64
  apply BitVec.eq_of_toNat_eq
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have habu : a.toNat ||| b.toNat < 2 ^ 32 := Nat.or_lt_two_pow ha hb
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_or]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show a.toNat ||| b.toNat < 2 ^ 64 from by omega)]

/-- XOR distributes over `w64`. -/
theorem w64_xor (a b : BitVec 32) : w64 a ^^^ w64 b = w64 (a ^^^ b) := by
  unfold w64
  apply BitVec.eq_of_toNat_eq
  have ha : a.toNat < 2 ^ 32 := a.isLt
  have hb : b.toNat < 2 ^ 32 := b.isLt
  have habu : a.toNat ^^^ b.toNat < 2 ^ 32 := Nat.xor_lt_two_pow ha hb
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_xor]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 from by omega),
      Nat.mod_eq_of_lt (show a.toNat ^^^ b.toNat < 2 ^ 64 from by omega)]

/-! ## §3  The per-iteration limb op as a `BitVec 32` function

Parameter `op : SOp2` (`.Oland .U32` / `.Olor .U32` / `.Olxor .U32`); the
limb-level result is `evalLimbOp32 op a b`. -/

/-- The `BitVec 32` limb value `r := t OP s` produces. -/
def evalLimbOp32 (op : SOp2) (a b : BitVec 32) : BitVec 32 :=
  match op with
  | .Oland _ => a &&& b
  | .Olor _ => a ||| b
  | .Olxor _ => a ^^^ b
  | _ => 0

/-- For the three bitwise ops, the `Papp2` evaluator on the loaded form
    `w64 a` / `w64 b` returns `w64 (evalLimbOp32 op a b)` — using
    bit-parallelism (`w64_and`/`w64_or`/`w64_xor`). -/
theorem evalPExpr_binOp32 (s : BignumState) (op : SOp2) (a b : BitVec 32)
    (ht : s.regs "t" = w64 a) (hs : s.regs "s" = w64 b)
    (hop : op = .Oland .U32 ∨ op = .Olor .U32 ∨ op = .Olxor .U32) :
    evalPExpr s (.Papp2 op (pv32 "t") (pv32 "s")) = some (w64 (evalLimbOp32 op a b)) := by
  rcases hop with h | h | h <;> subst h
  · simp only [pv32, evalPExpr, vr32, evalLimbOp32, bind, Option.bind, ht, hs]
    rw [w64_and]
  · simp only [pv32, evalPExpr, vr32, evalLimbOp32, bind, Option.bind, ht, hs]
    rw [w64_or]
  · simp only [pv32, evalPExpr, vr32, evalLimbOp32, bind, Option.bind, ht, hs]
    rw [w64_xor]

/-! ## §4  Body straight-line / non-control / CT shape -/

/-- `logBody32 op` is straight-line (`Cassgn` only). -/
theorem logBody32_straightLine (op : SOp2) :
    InstrR.bodyIsStraightLine (logBody32 op) := by
  simp only [logBody32, load32At0, binOp32, store32At0, ptrImm,
             InstrR.bodyIsStraightLine, InstrR.isStraightLine, and_self]

/-- Every instruction of `logBody32 op` is non-control. -/
theorem logBody32_nonControl (op : SOp2) :
    ∀ i ∈ logBody32 op, i.isNonControl := by
  intro i hi
  simp only [logBody32, load32At0, binOp32, store32At0, ptrImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-! ## §5  One iteration of `logBody32 op` as an explicit state update

Bitwise analogue of `MpnAdd32Refines.bignumExec_loopBody32_step` and the
U32 mirror of `MpnLogicalPrototype.bignumExec_logBody_step`.  No carry
register: just two loads, one `Papp2`, one store, and four advances. -/

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem bignumExec_logBody32_step (s : BignumState) (op : SOp2)
    (a b : BitVec 32)
    (hop : op = .Oland .U32 ∨ op = .Olor .U32 ∨ op = .Olxor .U32)
    (ha : load32Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load32Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec (logBody32 op) s = some s' ∧
      s'.mem = Mem.store32 s.mem (regAddr s "op")
        (UInt64.ofNat (w64 (evalLimbOp32 op a b)).toNat) ∧
      s'.regs "ap" = s.regs "ap" + 4 ∧
      s'.regs "bp" = s.regs "bp" + 4 ∧
      s'.regs "op" = s.regs "op" + 4 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- The three op-arms are structurally identical (same load/load/store/advances),
  -- so case-split on op and run each branch through the same simp script.
  rcases hop with h | h | h <;> subst h <;>
  · simp only [logBody32, load32At0, binOp32, store32At0, ptrImm,
               bignumExec, execInstr, evalPExpr, pv32, pv64,
               resolveAddr_vr64, vr32, vr64,
               setReg_mem, setReg_regs, storeMem32_mem_proj, storeMem32_regs_proj,
               Option.bind_some, bind, Option.bind,
               List.replicate, List.cons_append, List.nil_append]
    simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
               ↓reduceIte, setReg_regs, storeMem32_regs_proj, storeMem32_mem_proj,
               show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
               ha, hb, Option.bind_some, bind, Option.bind] at *
    -- Fire the two loads.
    rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
    rw [ha]
    simp only [Option.bind_some, bind, Option.bind]
    rw [show (setReg s "t" (BitVec.ofNat 64 (UInt64.ofNat a.toNat).toNat)).regs "bp" + 0
          = s.regs "bp" from by simp only [setReg_regs]; bv_decide, setReg_mem, hb]
    simp only [Option.bind_some, bind, Option.bind]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [setReg_regs, setReg_mem, storeMem32_mem_proj, storeMem32_regs_proj,
                 regAddr, String.reduceEq, ↓reduceIte, reduceIte,
                 show s.regs "op" + 0 = s.regs "op" from by bv_decide,
                 show BitVec.ofInt 64 4 = (4 : BitVec 64) from rfl,
                 show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]
    -- The remaining memory goal: the stored value equals
    -- `UInt64.ofNat (w64 (a OP b)).toNat`, using bit-parallelism.
    rw [load_roundtrip a, load_roundtrip b]
    first
      | (rw [w64_and]; rfl)
      | (rw [w64_or]; rfl)
      | (rw [w64_xor]; rfl)

/-! ## §6  Forward one-iteration rule for `logBody32 op`

The U32 analogue of `MpnLogicalPrototype.bignumExecFuel_logBody_step`,
re-proved here at u32 width.  Uses only the public
`bignumExecFuel_eq_bignumExec_of_straightLine` and
`bignumExecFuel_append_join` primitives from `BignumExec`. -/

theorem bignumExecFuel_logBody32_step (op : SOp2) (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec (logBody32 op) s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond (logBody32 op)] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond (logBody32 op)] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) (logBody32 op) s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f (logBody32 op) s
          (logBody32_straightLine op)]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
             show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) (logBody32 op) [.Cwhile [] cond (logBody32 op)]
        (logBody32_nonControl op) s s_mid s' hsl hrec]

/-! ## §7  The loop, by induction on the limb list

Generic loop lemma parametric over the op and its pure reference.
Bitwise analogue of `MpnAdd32Refines.mpnAddN32_openLoop`, structurally
simpler (no carry threaded). -/

theorem log32_openLoop (op : SOp2)
    (ref : List (BitVec 32) → List (BitVec 32) → List (BitVec 32))
    (hop : op = .Oland .U32 ∨ op = .Olor .U32 ∨ op = .Olxor .U32)
    (href_nil : ∀ a b, a = [] ∨ b = [] → ref a b = [])
    (href_cons : ∀ a as b bs,
        ref (a :: as) (b :: bs) = evalLimbOp32 op a b :: ref as bs) :
    ∀ (as bs : List (BitVec 32)) (s : BignumState) (extra : Nat),
      as.length = bs.length →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs32 s.mem (regAddr s "ap") as →
      memHoldsLimbs32 s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "ap") (4 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (4 * as.length))
        (range (regAddr s "bp") (4 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) (logBody32 op)] s
              = some s' ∧
        memHoldsLimbs32 s'.mem (regAddr s "op") (ref as bs) ∧
        (∀ b, MemoryModel.Disjoint (range b 4)
              (range (regAddr s "op") (4 * as.length)) →
            load32Mem s'.mem b = load32Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s extra _ hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 32)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 0 :=
        evalPExpr_neq_zero_false s (pv64 "n")
          (by simp only [pv64, vr64, evalPExpr]; rw [hn0])
      exact bignumExecFuel_loop_exit_generic emptyRegistry extra _ (logBody32 op) s hcond
    · rw [href_nil [] bs (Or.inl rfl)]; exact True.intro
    · intro b _; rfl
  | cons a as ih =>
    intro bs s extra hlen hn hap hbp hdoa hdob
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hsize : 4 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (4 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- Run one iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_logBody32_step s op a b hop hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hadv : ∀ (bv : BitVec 64),
          UInt64.ofNat (bv + 4).toNat = UInt64.ofNat bv.toNat + 4 := by
        intro bv
        have h := regAddr_advance_at bv 4
        rw [show (BitVec.ofNat 64 4 : BitVec 64) = 4 from rfl,
            show (UInt64.ofNat 4 : UInt64) = 4 from rfl] at h
        exact h
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 4 := by
        simp only [regAddr, hs1_ap]; exact hadv _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 4 := by
        simp only [regAddr, hs1_bp]; exact hadv _
      have hra_op : regAddr s1 "op" = op0 + 4 := by
        simp only [regAddr, hs1_op, hop0]; exact hadv _
      have hmem1 : s1.mem = Mem.store32 s.mem op0
          (UInt64.ofNat (w64 (evalLimbOp32 op a b)).toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- Frame `ap`/`bp` tails across the head store at `op0`.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "ap" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 4) (range (regAddr s "bp" + 4) (4 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hap1 : memHoldsLimbs32 s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "ap" + 4) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs32 s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs32_store32_range_frame s.mem (regAddr s "bp" + 4) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (4 * as.length))
          (range (regAddr s1 "ap") (4 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (4 * as.length))
          (range (regAddr s1 "bp") (4 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        · obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      obtain ⟨s', hs', hs'_mem, hs'_frame⟩ :=
        ih bs s1 extra hlen' hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_⟩
      · -- Fuel: 2·(L+1)+3+extra = (2·L+2+extra)+3.
        have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        have hcond : evalPExpr s (.Papp2 (.Oneq .U64) (pv64 "n") (.Pconst 0)) = some 1 :=
          evalPExpr_neq_zero_true s (pv64 "n") (s.regs "n")
            (by simp only [pv64, vr64, evalPExpr]) hn_ne
        refine bignumExecFuel_logBody32_step op emptyRegistry
          (2 * as.length + 2 + extra) _ s s1 s' hcond hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · -- Memory at op: head limb at op0, tail via IH.
        rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 4) (range (op0 + 4) (4 * as.length)) :=
          range_op_head_tail_disjoint_4 op0 as.length (by omega)
        rw [href_cons a as b bs]
        refine ⟨?_, ?_⟩
        · -- Head: read at op0 via IH frame + read-back.
          rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load32Mem_store32_same s.mem op0
            (UInt64.ofNat (w64 (evalLimbOp32 op a b)).toNat)
          rw [hread]
          -- Mask is identity on `w64`-shaped values (high 32 bits zero).
          have hval_lt : (w64 (evalLimbOp32 op a b)).toNat < 2 ^ 32 := by
            unfold w64
            have h := (evalLimbOp32 op a b).isLt
            simp only [BitVec.toNat_ofNat]
            omega
          have hmask : (UInt64.ofNat (w64 (evalLimbOp32 op a b)).toNat
              &&& 0xFFFFFFFF : UInt64)
              = UInt64.ofNat (w64 (evalLimbOp32 op a b)).toNat := by
            apply UInt64.toNat.inj
            simp only [UInt64.toNat_and, UInt64.toNat_ofNat',
                       show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from by decide]
            rw [Nat.mod_eq_of_lt (by omega : (w64 (evalLimbOp32 op a b)).toNat < 2 ^ 64),
                Nat.and_two_pow_sub_one_eq_mod _ 32, Nat.mod_eq_of_lt hval_lt]
          rw [hmask]
          -- Goal: `some (UInt64.ofNat (w64 (op a b)).toNat) =
          --        some (UInt64.ofNat (op a b).toNat)`.
          -- Both shapes are equal: `(w64 w).toNat = w.toNat` since `w.toNat < 2^32`.
          have hw : (w64 (evalLimbOp32 op a b)).toNat = (evalLimbOp32 op a b).toNat := by
            unfold w64
            have hbnd := (evalLimbOp32 op a b).isLt
            simp only [BitVec.toNat_ofNat]
            omega
          rw [hw]
        · -- Tail: IH gives `memHoldsLimbs32 s'.mem (regAddr s1 "op") (ref as bs)`.
          have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · -- Frame: blocks disjoint from op-region unchanged.
        intro bb hbb
        rw [hmem1] at hs'_frame
        have hbb_tail : MemoryModel.Disjoint (range bb 4)
            (range (regAddr s1 "op") (4 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          obtain ⟨j, hj, hxj⟩ := h
          refine ⟨4 + j, by simp [List.length_cons]; omega, ?_⟩
          rw [UInt64.ofNat_add, show (UInt64.ofNat 4 : UInt64) = 4 from rfl]
          rw [hxj]; ac_rfl
        rw [hs'_frame bb hbb_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 4) (range (regAddr s "op") 4) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          obtain ⟨j, hj, hxj⟩ := h
          exact ⟨j, by simp [List.length_cons]; omega, hxj⟩
        rw [load32Mem_store32_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §8  Bridge statements + assembly

The body is the loop itself (`logFullBody32 op`), no carry prelude.  We
state the bridge in the same shape as `MpnLogicalPrototype.LogRefinesStmt`
at u32. -/

/-- Shared bridge-statement shape for a U32 bitwise kernel body `bdy`
    against reference `ref`. -/
def LogRefines32Stmt (bdy : List InstrR)
    (ref : List (BitVec 32) → List (BitVec 32) → List (BitVec 32)) : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 32)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs32 s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (4 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (4 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (4 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bdy s = some s' ∧
      memHoldsLimbs32 s'.mem (UInt64.ofNat (s.regs "op").toNat) (ref as bs)

/-- Generic bridge assembly: `log32_openLoop` packaged into `LogRefines32Stmt`. -/
theorem log32_refines (op : SOp2)
    (ref : List (BitVec 32) → List (BitVec 32) → List (BitVec 32))
    (hop : op = .Oland .U32 ∨ op = .Olor .U32 ∨ op = .Olxor .U32)
    (href_nil : ∀ a b, a = [] ∨ b = [] → ref a b = [])
    (href_cons : ∀ a as b bs,
        ref (a :: as) (b :: bs) = evalLimbOp32 op a b :: ref as bs) :
    LogRefines32Stmt (logFullBody32 op) ref := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, _⟩ :=
    log32_openLoop op ref hop href_nil href_cons as bs s extra hlen hn hap hbp hdoa hdob
  refine ⟨s', ?_, ?_⟩
  · rw [hextra]; simpa [logFullBody32, regAddr] using hs'
  · simpa [regAddr] using hs'_mem

/-! ### Per-op reference cons equations -/

theorem mpnAnd32_cons (a : BitVec 32) (as : List (BitVec 32)) (b : BitVec 32)
    (bs : List (BitVec 32)) :
    mpnAnd32 (a :: as) (b :: bs) = evalLimbOp32 (.Oland .U32) a b :: mpnAnd32 as bs := rfl

theorem mpnIor32_cons (a : BitVec 32) (as : List (BitVec 32)) (b : BitVec 32)
    (bs : List (BitVec 32)) :
    mpnIor32 (a :: as) (b :: bs) = evalLimbOp32 (.Olor .U32) a b :: mpnIor32 as bs := rfl

theorem mpnXor32_cons (a : BitVec 32) (as : List (BitVec 32)) (b : BitVec 32)
    (bs : List (BitVec 32)) :
    mpnXor32 (a :: as) (b :: bs) = evalLimbOp32 (.Olxor .U32) a b :: mpnXor32 as bs := rfl

/-! ## §9  The three concrete bridges -/

/-- **`mpn_and_n_32` Jasmin bridge, fully proved.**  The emitted
    `while (n != 0) { t = [:u32 ap]; s = [:u32 bp]; r = t & s; [:u32 op] = r;
    ap += 4; bp += 4; op += 4; n -= 1 }` kernel refines the limb-wise
    `BitVec.and` reference `mpnAnd32` over byte memory at 4-byte stride. -/
theorem MpnAnd32JasminRefines :
    LogRefines32Stmt (logFullBody32 (.Oland .U32)) mpnAnd32 :=
  log32_refines (.Oland .U32) mpnAnd32 (Or.inl rfl) mpnAnd32_nil mpnAnd32_cons

/-- **`mpn_ior_n_32` Jasmin bridge, fully proved.** -/
theorem MpnIor32JasminRefines :
    LogRefines32Stmt (logFullBody32 (.Olor .U32)) mpnIor32 :=
  log32_refines (.Olor .U32) mpnIor32 (Or.inr (Or.inl rfl)) mpnIor32_nil mpnIor32_cons

/-- **`mpn_xor_n_32` Jasmin bridge, fully proved.** -/
theorem MpnXor32JasminRefines :
    LogRefines32Stmt (logFullBody32 (.Olxor .U32)) mpnXor32 :=
  log32_refines (.Olxor .U32) mpnXor32 (Or.inr (Or.inr rfl)) mpnXor32_nil mpnXor32_cons

/-! ## §10  Axiom audit -/

#print axioms MpnAnd32JasminRefines
#print axioms MpnIor32JasminRefines
#print axioms MpnXor32JasminRefines

end CatCrypt.Crypto.Jasmin.Examples.MpnLogical32Refines
