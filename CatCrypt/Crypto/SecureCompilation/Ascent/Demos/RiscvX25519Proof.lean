/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof

/-!
# RV64 X25519 at bytes

`RiscvX25519LadderBytesProof` states the 255-iteration Montgomery ladder over its encoded
bytes. This module completes RFC 7748 §5 `X25519(k, u)` around it: a block function at
instruction 3098 clamps the scalar, masks bit 255 of `u`, sets up the ladder state, calls the
ladder, then computes `x2 · z2^(p - 2)` with the field-operation functions of the ladder
program, as calls in the style of `RiscvX25519LadderFnProof.run_calls`. A C function
`catcrypt_x25519(out, scalar, u)` at instruction 4213 copies the scalar and `u` into a state
block in its own frame, calls the block function and copies the result to `out`.

The inversion is the addition chain of the ref10 implementation: 254 squarings and 11
multiplications. `invSteps_exp` states its exponent is `P25519 - 2` by `decide +kernel` over
the exponents each step tracks, and `pow_track` turns tracked exponents into powers.

The specification is `CatCrypt.Util.x25519` (RFC 7748 `X25519` over `Fp25519` on the scalar
and `u` as integers) and `CatCrypt.Util.x25519Bytes` (the same on 32-byte strings).
`ladderN_eq` identifies the ladder iteration used here with the one there.

## Main results

* `xSteps_value`: the 266 field-operation steps after the ladder compute `x2 · z2^(p - 2)`,
  reduced below `p25519`.
* `setup_vals`: the 41-instruction set-up leaves the clamped scalar, the masked `u` and the
  RFC 7748 initial ladder state in the block.
* `fnSpec_x25519`: the block function placed after the ladder program meets `FnSpec` with
  `X25519Pre` and `X25519Post`.
* `fnSpec_wrap`: the C function meets `FnSpec` with `X25519CPre` and `X25519CPost`.
* `x25519Bytes_correct`: the encoded 4246-instruction program decodes to a program whose
  function at instruction 3098 meets the block specification at every word-aligned base.
* `x25519CBytes_correct`: the same program's function at instruction 4213 maps the 32 bytes
  at `scalar` and at `u` to `x25519Bytes` of them at `out`.

## Scope

In the block function the scalar is the little-endian 256-bit integer at offset 0 of the
block and `u` the one at offset 32, as RFC 7748 `decodeScalar25519` and `decodeUCoordinate`
read their 32 bytes; the result at offset 64 is below `p25519`, so its four little-endian
words are `encodeUCoordinate` of it. The C function needs no disjointness of its buffers: it
reads the scalar and `u` before any store and writes `out` after its last load.

The entry conditions require `sp` 16-byte aligned and the pointers 8-byte aligned, the
RISC-V calling convention and the alignment of `ld`/`sd`; the machine model has no alignment
check, so the proofs use the alignment of `sp` only to pass it to the callees. The results are
about the decoded instruction list run by `RiscvPc64` over a flat byte memory; nothing here
parses an ELF file or models a linker (see `RiscvX25519LadderObject`). These are
functional-correctness theorems: no constant-time or leakage property is proved.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel (p25519)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof
  (FeOp Step ladderPfx Pre)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderBytesProof
open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64)
open CatCrypt.Util (P25519 X25519State x25519 x25519Clamp x25519LadderN x25519Bytes decodeLE
  encodeLE encodeLE_decodeLE)
open CatCrypt.Util.Fp25519 (fromNat)

/-! ## The specification

RFC 7748 `X25519(k, u)` is `CatCrypt.Util.x25519` (`Util/X25519Verified.lean`), with the
byte-string form `x25519Bytes`. Its ladder `x25519LadderN` is `ladderN` of
`RiscvX25519LadderLoopProof`. -/

theorem ladderN_eq : ∀ (n : Nat) (s : X25519State), ladderN n s = x25519LadderN n s
  | 0, _ => rfl
  | n + 1, s => by simp only [ladderN, x25519LadderN]; exact ladderN_eq n _

/-! ## The inversion -/

/-- `n` squarings of `d` in place. -/
def sqrs (d : String) : Nat → List Step
  | 0 => []
  | n + 1 => ⟨.sqr, d, d, d⟩ :: sqrs d n

/-- `z2^(p - 2)` into `CB`, by the addition chain of 254 squarings and 11 multiplications. -/
def invSteps : List Step :=
  [⟨.sqr, "z2", "z2", "A"⟩, ⟨.sqr, "A", "A", "t0"⟩, ⟨.sqr, "t0", "t0", "t0"⟩,
    ⟨.mul, "t0", "z2", "AA"⟩, ⟨.mul, "AA", "A", "B"⟩, ⟨.sqr, "B", "B", "t0"⟩,
    ⟨.mul, "t0", "AA", "BB"⟩, ⟨.sqr, "BB", "BB", "t0"⟩] ++ sqrs "t0" 4 ++
  [⟨.mul, "t0", "BB", "E"⟩, ⟨.sqr, "E", "E", "t0"⟩] ++ sqrs "t0" 9 ++
  [⟨.mul, "t0", "E", "C"⟩, ⟨.sqr, "C", "C", "t0"⟩] ++ sqrs "t0" 19 ++
  [⟨.mul, "t0", "C", "t0"⟩] ++ sqrs "t0" 10 ++
  [⟨.mul, "t0", "E", "D"⟩, ⟨.sqr, "D", "D", "t0"⟩] ++ sqrs "t0" 49 ++
  [⟨.mul, "t0", "D", "DA"⟩, ⟨.sqr, "DA", "DA", "t0"⟩] ++ sqrs "t0" 99 ++
  [⟨.mul, "t0", "DA", "t0"⟩] ++ sqrs "t0" 50 ++
  [⟨.mul, "t0", "D", "t0"⟩] ++ sqrs "t0" 5 ++
  [⟨.mul, "t0", "B", "CB"⟩]

/-- The exponent of `z2` each name holds after a step. -/
def expStep (s : Step) (x : String → Nat) : String → Nat :=
  Function.update x s.d (match s.op with
    | .mul => x s.a + x s.b
    | .sqr => 2 * x s.a
    | _ => 0)

/-- Every step multiplies or squares names already known as powers. -/
def Tracked : List Step → List String → Bool
  | [], _ => true
  | s :: sts, ns => (match s.op with
      | .mul => decide (s.a ∈ ns) && decide (s.b ∈ ns)
      | .sqr => decide (s.a ∈ ns)
      | _ => false) && Tracked sts (s.d :: ns)

theorem invSteps_length : invSteps.length = 265 := by decide +kernel

theorem invSteps_tracked : Tracked invSteps ["z2"] = true := by decide +kernel

theorem invSteps_exp :
    (invSteps.foldl (fun x s => expStep s x) (fun n => if n = "z2" then 1 else 0)) "CB"
      = P25519 - 2 := by decide +kernel

theorem fromNat_mod (n : Nat) : fromNat (n % p25519) = fromNat n := by
  simp only [fromNat, p25519, P25519, ZMod.natCast_mod]

theorem pow_track (Z : CatCrypt.Util.Fp25519) :
    ∀ (sts : List Step) (ns : List String) (e : String → Nat) (x : String → Nat),
      Tracked sts ns = true → (∀ n ∈ ns, fromNat (e n) = Z ^ x n) →
      ∀ n ∈ sts.foldl (fun ns s => s.d :: ns) ns,
        fromNat ((sts.foldl (fun e s => s.env e) e) n)
          = Z ^ ((sts.foldl (fun x s => expStep s x) x) n) := by
  intro sts
  induction sts with
  | nil => intro ns e x _ h n hn; exact h n hn
  | cons s sts ih =>
    intro ns e x ht h n hn
    simp only [Tracked, Bool.and_eq_true] at ht
    obtain ⟨hs, ht⟩ := ht
    simp only [List.foldl_cons] at hn ⊢
    refine ih (s.d :: ns) (s.env e) (expStep s x) ht ?_ n hn
    intro m hm
    by_cases hmd : m = s.d
    · subst hmd
      simp only [RiscvX25519LadderStepProof.Step.env, expStep, Function.update_self]
      obtain ⟨op, a, b, d⟩ := s
      cases op with
      | mul =>
        simp only [decide_eq_true_eq, Bool.and_eq_true] at hs
        simp only [FeOp.eval, FeOp.evalP, fromNat_mod]
        rw [show fromNat (e a * e b) = fromNat (e a) * fromNat (e b) by simp [fromNat],
          h a hs.1, h b hs.2, pow_add]
      | sqr =>
        simp only [decide_eq_true_eq] at hs
        simp only [FeOp.eval, FeOp.evalP, fromNat_mod]
        rw [show fromNat (e a * e a) = fromNat (e a) * fromNat (e a) by simp [fromNat],
          h a hs, two_mul, pow_add]
      | add => simp at hs
      | sub => simp at hs
      | a24 => simp at hs
    · have hm' : m ∈ ns := by
        rcases List.mem_cons.1 hm with h' | h'
        · exact absurd h' hmd
        · exact h'
      simp only [RiscvX25519LadderStepProof.Step.env, expStep, Function.update_of_ne hmd]
      exact h m hm'

/-! ## The functions of `ladderProg`, before any code -/

theorem fn_at' (rest : List PInst64) (base : BitVec 64) (op : FeOp) (pre post : List PInst64)
    (h : ladderProg = pre ++ fnCode (phys op) ++ post) (hl : pre.length = fnIdx op) :
    FnSpec (ladderProg ++ rest) base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval) := by
  have hL := congrArg List.length h
  rw [ladderProg_length, List.length_append, List.length_append, fnCode_length] at hL
  rw [← hl, h, List.append_assoc]
  exact fnSpec_buf pre (post ++ rest) base (phys op) op.eval op.pre (phys_correct op)
    (phys_sp_ra op).1 (phys_sp_ra op).2 (by omega)

theorem fnSpecs' (rest : List PInst64) (base : BitVec 64) :
    ∀ op, FnSpec (ladderProg ++ rest) base (addrOf base (fnIdx op)) (BufPre op.pre)
      (BufPost op.eval) := by
  intro op
  cases op
  · exact fn_at' rest base .add (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146)
      (fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at' rest base .sub (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add))
      (fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at' rest base .mul (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub))
      (fnCode (phys .sqr) ++ fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at' rest base .sqr (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub) ++ fnCode (phys .mul))
      (fnCode (phys .a24))
      (by simp [ladderProg]) (by decide +kernel)
  · exact fn_at' rest base .a24 (ladderCode 74 146 0 ++ cswapCode ++ stepCode fnIdx 146
        ++ fnCode (phys .add) ++ fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr))
      [] (by simp [ladderProg]) (by decide +kernel)

theorem ladderSpec' (rest : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0) :
    FnSpec (ladderProg ++ rest) base (addrOf base 0) LadderPre LadderPost := by
  have hC : FnSpec (ladderProg ++ rest) base (addrOf base 74) CswapPre CswapPost := by
    have := fnSpec_cswap (ladderCode 74 146 0) (stepCode fnIdx 146 ++ fnCode (phys .add) ++
      fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24)
      ++ rest) base (by rw [ladderCode_length]; decide)
    rw [ladderCode_length] at this
    convert this using 1
    simp [ladderProg]
  have hS : FnSpec (ladderProg ++ rest) base (addrOf base 146) StepPre StepPost := by
    have hl : (ladderCode 74 146 0 ++ cswapCode).length = 146 := by
      rw [List.length_append, ladderCode_length]; rfl
    have := fnSpec_step (ladderProg ++ rest) base hb fnIdx (fun op => by cases op <;> decide)
      (fnSpecs' rest base) (ladderCode 74 146 0 ++ cswapCode) (fnCode (phys .add) ++
      fnCode (phys .sub) ++ fnCode (phys .mul) ++ fnCode (phys .sqr) ++ fnCode (phys .a24)
      ++ rest) (by rw [hl]; simp [ladderProg]) (by rw [hl]; decide)
    rwa [hl] at this
  exact fnSpec_ladder (ladderProg ++ rest) base hb 74 146 (by decide) (by decide) hC hS [] _
    (by simp [ladderProg]; rfl) (by decide)

/-! ## The set-up of the state block -/

/-- Load the scalar `k` (offset 0) and `u` (offset 32, `x1`), clear bits 0..2 and 254..255 of
    `k` and set bit 254, clear bit 255 of `u`, and store `k`, `x1 = u`, `x2 = 1`, `z2 = 0`,
    `x3 = u`, `z3 = 1`. Every load precedes every store. -/
def setup : List XInst64 :=
  [.ld "t0" "s0" 0, .ld "a3" "s0" 8, .ld "a4" "s0" 16, .ld "t1" "s0" 24,
    .ld "t2" "s0" 32, .ld "t3" "s0" 40, .ld "t4" "s0" 48, .ld "t5" "s0" 56,
    .m (.base (.srli "t0" "t0" 3)), .m (.base (.slli "t0" "t0" 3)),
    .m (.base (.slli "t1" "t1" 2)), .m (.base (.srli "t1" "t1" 2)),
    .m (.addi "a1" "zero" 1), .m (.base (.slli "a2" "a1" 62)), .m (.base (.add "t1" "t1" "a2")),
    .m (.base (.slli "t5" "t5" 1)), .m (.base (.srli "t5" "t5" 1)),
    .sd "t0" "s0" 0, .sd "a3" "s0" 8, .sd "a4" "s0" 16, .sd "t1" "s0" 24,
    .sd "t2" "s0" 32, .sd "t3" "s0" 40, .sd "t4" "s0" 48, .sd "t5" "s0" 56,
    .sd "a1" "s0" 64, .sd "zero" "s0" 72, .sd "zero" "s0" 80, .sd "zero" "s0" 88,
    .sd "zero" "s0" 96, .sd "zero" "s0" 104, .sd "zero" "s0" 112, .sd "zero" "s0" 120,
    .sd "t2" "s0" 128, .sd "t3" "s0" 136, .sd "t4" "s0" 144, .sd "t5" "s0" 152,
    .sd "a1" "s0" 160, .sd "zero" "s0" 168, .sd "zero" "s0" 176, .sd "zero" "s0" 184]

theorem setup_length : setup.length = 41 := rfl

/-- The words the set-up stores, from the block `m` at `P`. -/
def setupSlots (m : AMem) (P : BitVec 64) : List (Nat × BitVec 64) :=
  let r := fun o => read64 m (P + BitVec.ofNat 64 o)
  let k0 := r 0 >>> 3 <<< 3
  let k3 := r 24 <<< 2 >>> 2 + (1 : BitVec 64) <<< 62
  let u3 := r 56 <<< 1 >>> 1
  [(0, k0), (8, r 8), (16, r 16), (24, k3), (32, r 32), (40, r 40), (48, r 48), (56, u3),
    (64, 1), (72, 0), (80, 0), (88, 0), (96, 0), (104, 0), (112, 0), (120, 0),
    (128, r 32), (136, r 40), (144, r 48), (152, u3), (160, 1), (168, 0), (176, 0), (184, 0)]

theorem setup_mem (st : MState64) :
    (runX st setup).mem = writeSlots st.mem (st.regs.get "s0") (setupSlots st.mem (st.regs.get "s0")) := by
  simp only [setup, runX_cons, runX_nil, evalX, evalMInst64, evalRInst64, addr, opAdd64]
  simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
    not_false_eq_true, or_self]
  simp only [setupSlots, writeSlots, get_zero]
  rfl

theorem setup_writes : ∀ r ∈ "sp" :: "ra" :: "s0" :: frameSlots.map Prod.fst,
    r ∉ xWrites setup := by decide

theorem setup_read (m : AMem) (P : BitVec 64) (o : Nat) (v : BitVec 64)
    (h : (o, v) ∈ setupSlots m P) :
    read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 o) = v :=
  read64_writeSlots_mem _ _ _ o v h (by simp only [setupSlots, List.map_cons, List.map_nil]; decide)
    (by simp only [setupSlots, List.map_cons, List.map_nil]; decide)
    (by simp only [setupSlots, List.map_cons, List.map_nil]; decide)

theorem toNat_clr3 (x : BitVec 64) : (x >>> 3 <<< 3).toNat = x.toNat / 8 * 8 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem toNat_k3 (x : BitVec 64) :
    (x <<< 2 >>> 2 + (1 : BitVec 64) <<< 62).toNat = x.toNat % 2 ^ 62 + 2 ^ 62 := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  omega

theorem toNat_u3 (x : BitVec 64) : (x <<< 1 >>> 1).toNat = x.toNat % 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- **The set-up.** The block holds the clamped scalar, `x1 = x3 = u mod 2^255`, `x2 = 1`,
    `z2 = 0` and `z3 = 1`. -/
theorem setup_vals (m : AMem) (P : BitVec 64) :
    memLimbs4 (writeSlots m P (setupSlots m P)) P = x25519Clamp (memLimbs4 m P) ∧
      fe (writeSlots m P (setupSlots m P)) P "x1" = memLimbs4 m (P + BitVec.ofNat 64 32) % 2 ^ 255 ∧
      fe (writeSlots m P (setupSlots m P)) P "x2" = 1 ∧
      fe (writeSlots m P (setupSlots m P)) P "z2" = 0 ∧
      fe (writeSlots m P (setupSlots m P)) P "x3" = memLimbs4 m (P + BitVec.ofNat 64 32) % 2 ^ 255 ∧
      fe (writeSlots m P (setupSlots m P)) P "z3" = 1 := by
  have r := setup_read m P
  have e0 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 0) = read64 m (P + BitVec.ofNat 64 0) >>> 3 <<< 3 :=
    r 0 _ (by simp only [setupSlots]; simp)
  have e8 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 8) = read64 m (P + BitVec.ofNat 64 8) :=
    r 8 _ (by simp only [setupSlots]; simp)
  have e16 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 16) = read64 m (P + BitVec.ofNat 64 16) :=
    r 16 _ (by simp only [setupSlots]; simp)
  have e24 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 24) = read64 m (P + BitVec.ofNat 64 24) <<< 2 >>> 2 + (1 : BitVec 64) <<< 62 :=
    r 24 _ (by simp only [setupSlots]; simp)
  have e32 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 32) = read64 m (P + BitVec.ofNat 64 32) :=
    r 32 _ (by simp only [setupSlots]; simp)
  have e40 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 40) = read64 m (P + BitVec.ofNat 64 40) :=
    r 40 _ (by simp only [setupSlots]; simp)
  have e48 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 48) = read64 m (P + BitVec.ofNat 64 48) :=
    r 48 _ (by simp only [setupSlots]; simp)
  have e56 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 56) = read64 m (P + BitVec.ofNat 64 56) <<< 1 >>> 1 :=
    r 56 _ (by simp only [setupSlots]; simp)
  have e64 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 64) = 1 :=
    r 64 _ (by simp only [setupSlots]; simp)
  have e72 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 72) = 0 :=
    r 72 _ (by simp only [setupSlots]; simp)
  have e80 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 80) = 0 :=
    r 80 _ (by simp only [setupSlots]; simp)
  have e88 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 88) = 0 :=
    r 88 _ (by simp only [setupSlots]; simp)
  have e96 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 96) = 0 :=
    r 96 _ (by simp only [setupSlots]; simp)
  have e104 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 104) = 0 :=
    r 104 _ (by simp only [setupSlots]; simp)
  have e112 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 112) = 0 :=
    r 112 _ (by simp only [setupSlots]; simp)
  have e120 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 120) = 0 :=
    r 120 _ (by simp only [setupSlots]; simp)
  have e128 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 128) = read64 m (P + BitVec.ofNat 64 32) :=
    r 128 _ (by simp only [setupSlots]; simp)
  have e136 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 136) = read64 m (P + BitVec.ofNat 64 40) :=
    r 136 _ (by simp only [setupSlots]; simp)
  have e144 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 144) = read64 m (P + BitVec.ofNat 64 48) :=
    r 144 _ (by simp only [setupSlots]; simp)
  have e152 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 152) = read64 m (P + BitVec.ofNat 64 56) <<< 1 >>> 1 :=
    r 152 _ (by simp only [setupSlots]; simp)
  have e160 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 160) = 1 :=
    r 160 _ (by simp only [setupSlots]; simp)
  have e168 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 168) = 0 :=
    r 168 _ (by simp only [setupSlots]; simp)
  have e176 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 176) = 0 :=
    r 176 _ (by simp only [setupSlots]; simp)
  have e184 : read64 (writeSlots m P (setupSlots m P)) (P + BitVec.ofNat 64 184) = 0 :=
    r 184 _ (by simp only [setupSlots]; simp)
  have hx1 : off "x1" = 32 := by decide
  have hx2 : off "x2" = 64 := by decide
  have hz2 : off "z2" = 96 := by decide
  have hx3 : off "x3" = 128 := by decide
  have hz3 : off "z3" = 160 := by decide
  simp only [fe, hx1, hx2, hz2, hx3, hz3]
  unfold memLimbs4
  simp only [add_ofNat_add, Nat.reduceAdd]
  rw [e0, e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104, e112, e120, e128,
    e136, e144, e152, e160, e168, e176, e184]
  have := (read64 m (P + BitVec.ofNat 64 0)).isLt
  have := (read64 m (P + BitVec.ofNat 64 8)).isLt
  have := (read64 m (P + BitVec.ofNat 64 16)).isLt
  have := (read64 m (P + BitVec.ofNat 64 24)).isLt
  have := (read64 m (P + BitVec.ofNat 64 32)).isLt
  have := (read64 m (P + BitVec.ofNat 64 40)).isLt
  have := (read64 m (P + BitVec.ofNat 64 48)).isLt
  have := (read64 m (P + BitVec.ofNat 64 56)).isLt
  simp only [toNat_clr3, toNat_k3, toNat_u3, x25519Clamp]
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## The X25519 function -/

/-- The inversion, then `x2 := x2 · z2^(p - 2)`. -/
def xSteps : List Step := invSteps ++ [⟨.mul, "x2", "CB", "x2"⟩]

theorem xSteps_length : xSteps.length = 266 := by decide +kernel

theorem xSteps_wf : ∀ s ∈ xSteps, s.a ∈ ladderPfx ∧ s.b ∈ ladderPfx ∧ s.d ∈ ladderPfx := by
  decide +kernel

/-- Every step is a multiplication or a squaring. -/
def AllMS : List Step → Bool
  | [] => true
  | s :: sts => (match s.op with | .mul => true | .sqr => true | _ => false) && AllMS sts

theorem xSteps_ms : AllMS xSteps = true := by decide +kernel

theorem pre_of_ms : ∀ (sts : List Step) (e : String → Nat), AllMS sts = true → Pre sts e := by
  intro sts
  induction sts with
  | nil => intro _ _; trivial
  | cons s sts ih =>
    intro e h
    simp only [AllMS, Bool.and_eq_true] at h
    refine ⟨?_, ih _ h.2⟩
    obtain ⟨op, a, b, d⟩ := s
    cases op <;> simp_all [FeOp.pre]

theorem foldl_env_other : ∀ (sts : List Step) (e : String → Nat) (n : String),
    (∀ s ∈ sts, s.d ≠ n) → (sts.foldl (fun e s => s.env e) e) n = e n := by
  intro sts
  induction sts with
  | nil => intro _ _ _; rfl
  | cons s sts ih =>
    intro e n h
    simp only [List.foldl_cons]
    rw [ih _ _ fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]
    simp only [RiscvX25519LadderStepProof.Step.env]
    exact Function.update_of_ne (Ne.symm (h s List.mem_cons_self)) _ _

theorem invSteps_no_x2 : ∀ s ∈ invSteps, s.d ≠ "x2" := by decide +kernel

theorem cb_tracked : "CB" ∈ invSteps.foldl (fun ns s => s.d :: ns) ["z2"] := by decide +kernel

/-- **The value of the steps.** From `e`, the steps leave `x2 · z2^(p - 2)` at `x2`, below `p`. -/
theorem xSteps_value (e : String → Nat) :
    fromNat ((xSteps.foldl (fun e s => s.env e) e) "x2")
        = fromNat (e "x2") * fromNat (e "z2") ^ (P25519 - 2) ∧
      (xSteps.foldl (fun e s => s.env e) e) "x2" < p25519 := by
  have hcb := pow_track (fromNat (e "z2")) invSteps ["z2"] e (fun n => if n = "z2" then 1 else 0)
    invSteps_tracked (fun n hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      subst hn; simp) "CB" cb_tracked
  rw [invSteps_exp] at hcb
  have hx2 := foldl_env_other invSteps e "x2" invSteps_no_x2
  rw [xSteps, List.foldl_append]
  generalize invSteps.foldl (fun e s => s.env e) e = e1 at hcb hx2 ⊢
  simp only [List.foldl_cons, List.foldl_nil, RiscvX25519LadderStepProof.Step.env,
    Function.update_self, FeOp.eval, FeOp.evalP]
  refine ⟨?_, Nat.mod_lt _ (by decide)⟩
  rw [fromNat_mod, show ∀ a b : Nat, fromNat (a * b) = fromNat a * fromNat b from
    fun a b => by simp [fromNat], hx2, hcb]

/-- The X25519 function at instruction `k`: open a 16-byte frame, save `ra` and `s0`, set up
    the state block at `a0`, call the ladder function at instruction 0, make the 266 calls of
    the inversion and the final multiplication, restore and return. The result is at `x2`. -/
def x25519Code (k : Nat) : List PInst64 :=
  stepPro ++ (setup.map .x ++ ([.x (.m (.base (.mv "a0" "s0"))),
    .jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((k + 46 : Nat) : Int)))] ++
    (callsCode fnIdx (k + 47) xSteps ++ stepEpi)))

theorem x25519Code_length (k : Nat) : (x25519Code k).length = 1115 := by
  simp [x25519Code, stepPro, stepEpi, setup_length, callsCode_length, xSteps_length]

/-- The wrapper prologue: load the scalar at `a1` and `u` at `a2`, open a 592-byte frame,
    save `ra` and the output pointer `a0` at its bottom, copy the scalar and `u` to the state
    block at `sp + 16`, and point `a0` at the block. The loads come before any store, so the
    scalar and `u` may lie anywhere, the output included. -/
def wpro : List XInst64 :=
  [.ld "t0" "a1" 0, .ld "t1" "a1" 8, .ld "t2" "a1" 16, .ld "t3" "a1" 24,
    .ld "a3" "a2" 0, .ld "a4" "a2" 8, .ld "a5" "a2" 16, .ld "a6" "a2" 24,
    .m (.addi "sp" "sp" (BitVec.ofInt 12 (-592))),
    .sd "ra" "sp" 0, .sd "a0" "sp" 8,
    .sd "t0" "sp" 16, .sd "t1" "sp" 24, .sd "t2" "sp" 32, .sd "t3" "sp" 40,
    .sd "a3" "sp" 48, .sd "a4" "sp" 56, .sd "a5" "sp" 64, .sd "a6" "sp" 72,
    .m (.addi "a0" "sp" 16)]

/-- The wrapper epilogue: reload the output pointer and `ra`, copy the result at block
    offset 64 to the output, close the frame. -/
def wepi : List XInst64 :=
  [.ld "a0" "sp" 8, .ld "ra" "sp" 0,
    .ld "t0" "sp" 80, .ld "t1" "sp" 88, .ld "t2" "sp" 96, .ld "t3" "sp" 104,
    .sd "t0" "a0" 0, .sd "t1" "a0" 8, .sd "t2" "a0" 16, .sd "t3" "a0" 24,
    .m (.addi "sp" "sp" 592)]

/-- The C function `catcrypt_x25519(out, scalar, u)` at instruction `k`, calling the block
    function at instruction `j`. -/
def wrapCode (j k : Nat) : List PInst64 :=
  wpro.map .x ++ ([.jal "ra" (BitVec.ofInt 21 (4 * (j : Int) - 4 * ((k + 20 : Nat) : Int)))] ++
    (wepi.map .x ++ [.jalr "zero" "ra" 0]))

theorem wpro_length : wpro.length = 20 := rfl

theorem wepi_length : wepi.length = 11 := rfl

theorem wrapCode_length (j k : Nat) : (wrapCode j k).length = 33 := rfl

/-- The X25519 program: the ladder program, the X25519 block function at instruction 3098, and
    the C interface `catcrypt_x25519(out, scalar, u)` at instruction 4213 (`wrapCode`, defined
    below). -/
def x25519Prog : List PInst64 := ladderProg ++ (x25519Code 3098 ++ wrapCode 3098 4213)

/-- The entry condition of the X25519 function: the 256 bytes below `sp` are disjoint from the
    576-byte state block at `a0`, `sp` is 16-byte and `a0` 8-byte aligned. The proof uses the
    alignment only to give the ladder its own (`LadderPre`). -/
def X25519Pre (st : MState64) : Prop :=
  Sep (st.regs.get "sp" + BitVec.ofInt 64 (-256)) 256 (st.regs.get "a0") 576 ∧
    Aligned 16 (st.regs.get "sp") ∧ Aligned 8 (st.regs.get "a0")

/-- The effect of the X25519 function: `x2` holds `X25519(k, u)` for the scalar `k` at offset 0
    and `u` at `x1`, as its canonical integer; `s0..s11`, `sp` and `ra` are restored; no byte
    outside the frames below `sp` and the state block changed. -/
def X25519Post (st st' : MState64) : Prop :=
  fe st'.mem (st.regs.get "a0") "x2"
      = (x25519 (memLimbs4 st.mem (st.regs.get "a0")) (fe st.mem (st.regs.get "a0") "x1")).val ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra" ∧
    ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-256)) 256 x 1 →
      Sep (st.regs.get "a0") 576 x 1 → st'.mem x = st.mem x

theorem fromNat_val (n : Nat) (h : n < p25519) : (fromNat n).val = n := by
  simp only [fromNat, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

theorem a256 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-240) = S + BitVec.ofInt 64 (-256) := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-240) = BitVec.ofInt 64 (-256) by decide]

theorem a16o (S : BitVec 64) (o : Nat) :
    S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o
      = S + BitVec.ofInt 64 (-256) + BitVec.ofNat 64 (240 + o) := by
  rw [show BitVec.ofInt 64 (-16) = BitVec.ofInt 64 (-256) + BitVec.ofNat 64 240 by decide,
    ← BitVec.add_assoc, add_ofNat_add]

theorem a128 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)
      = S + BitVec.ofInt 64 (-256) + BitVec.ofNat 64 128 := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112) = BitVec.ofInt 64 (-256) + BitVec.ofNat 64 128 by decide,
    ← BitVec.add_assoc]

theorem a16 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-16) = S + BitVec.ofInt 64 (-256) + BitVec.ofNat 64 240 := by
  have := a16o S 0; simpa using this

theorem sep_P (P x : BitVec 64) (h : Sep P 576 x 1) (o : Nat) (ho : o + 8 ≤ 576) :
    ¬ CatCrypt.Crypto.SecureCompilation.Memory64.InRange8 (P + BitVec.ofNat 64 o) x :=
  not_inRange_of_out (out_of_sep h (by simp)) ho (by decide)

theorem slot_byte' (S P : BitVec 64) (hsep : Sep (S + BitVec.ofInt 64 (-256)) 256 P 576)
    (o : Nat) (ho : o < 16) :
    Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-240)) 240
        (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) 1 ∧
      Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)) 112
        (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) 1 ∧
      Sep P 576 (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) 1 := by
  rw [a256, a128, a16o]
  refine ⟨sep_after _ 240 (240 + o) (by omega) (by omega) (by omega), ?_,
    sep_symm' (sep_shift hsep (240 + o) 1 (by decide) (by omega) (by decide))⟩
  rw [show S + BitVec.ofInt 64 (-256) + BitVec.ofNat 64 (240 + o)
      = S + BitVec.ofInt 64 (-256) + BitVec.ofNat 64 128 + BitVec.ofNat 64 (112 + o) by
    rw [add_ofNat_add, show 128 + (112 + o) = 240 + o by omega]]
  exact sep_after _ 112 (112 + o) (by omega) (by omega) (by omega)

theorem frame_byte (S P x : BitVec 64) (hx : Sep (S + BitVec.ofInt 64 (-256)) 256 x 1)
    (hx' : Sep P 576 x 1) :
    Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-240)) 240 x 1 ∧
      Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)) 112 x 1 ∧
      Sep (P + BitVec.ofNat 64 32) 544 x 1 ∧ Sep (S + BitVec.ofInt 64 (-16)) 16 x 1 := by
  refine ⟨?_, ?_, sep_into hx' 32 544 (by decide) (by decide) (by decide), ?_⟩
  · rw [a256]; exact sep_shrink hx 240 (by decide)
  · rw [a128]; exact sep_into hx 128 112 (by decide) (by decide) (by decide)
  · rw [a16]; exact sep_into hx 240 16 (by decide) (by decide) (by decide)

theorem setupSlots_lt (m : AMem) (P : BitVec 64) : ∀ q ∈ setupSlots m P, q.1 + 8 ≤ 576 := by
  intro q hq
  have h := List.mem_map_of_mem (f := Prod.fst) hq
  simp only [setupSlots, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at h
  omega

theorem b64 (n k : Nat) (h : 4 * (n + 1115) < 2 ^ 20) (hk : k ≤ 1115) : 4 * (n + k) < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.add_le_add_left hk n)) (Nat.lt_trans h (by decide))

theorem len_aux (n : Nat) (h : 4 * (n + 1115) < 2 ^ 20) : 4 * (n + 47 + 4 * 266) < 2 ^ 20 := by
  have e : n + 47 + 4 * 266 = n + 1111 := by rw [Nat.add_assoc]
  rw [e]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.add_le_add_left (by decide) n)) h

/-- **X25519 is a function.** `x25519Code` placed in any program whose instruction 0 is the
    ladder function and whose field-operation functions are at `fnIdx` meets `FnSpec` with
    `X25519Pre` and `X25519Post`. -/
theorem fnSpec_x25519 (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (hF : ∀ op, FnSpec prog base (addrOf base (fnIdx op)) (BufPre op.pre) (BufPost op.eval))
    (hL : FnSpec prog base (addrOf base 0) LadderPre LadderPost)
    (pre post : List PInst64) (hprog : prog = pre ++ x25519Code pre.length ++ post)
    (hlen : 4 * (pre.length + 1115) < 2 ^ 20) :
    FnSpec prog base (addrOf base pre.length) X25519Pre X25519Post := by
  intro st ⟨hsep, hspA, ha0A⟩
  generalize hS : st.regs.get "sp" = S at hsep hspA
  generalize hP : st.regs.get "a0" = P at hsep ha0A
  have hat := steps_mid prog pre post _ hprog
  have hL' := x25519Code_length pre.length
  have hfn : ∀ op, 4 * fnIdx op < 2 ^ 20 := fun op => by cases op <;> decide
  -- the prologue
  have g0 : prog[pre.length]? = some (.x (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) := by
    have := hat 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; rfl
  have g1 : prog[pre.length + 1]? = some (.x (.sd "ra" "sp" 0)) := by
    rw [hat 1 (by omega)]; rfl
  have g2 : prog[pre.length + 1 + 1]? = some (.x (.sd "s0" "sp" 8)) := by
    rw [show pre.length + 1 + 1 = pre.length + 2 by omega, hat 2 (by omega)]; rfl
  have g3 : prog[pre.length + 1 + 1 + 1]? = some (.x (.m (.base (.mv "s0" "a0")))) := by
    rw [show pre.length + 1 + 1 + 1 = pre.length + 3 by omega, hat 3 (by omega)]; rfl
  have k0 := steps_x prog base pre.length (by omega) _ g0 st
  have k1 := steps_x prog base (pre.length + 1) (by omega) _ g1
    (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16)))))
  have k2 := steps_x prog base (pre.length + 1 + 1) (by omega) _ g2
    (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) (.sd "ra" "sp" 0))
  have k3 := steps_x prog base (pre.length + 1 + 1 + 1) (by omega) _ g3
    (evalX (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16))))) (.sd "ra" "sp" 0))
      (.sd "s0" "sp" 8))
  generalize hst1 : evalX (evalX (evalX (evalX st (.m (.addi "sp" "sp" (BitVec.ofInt 12 (-16)))))
      (.sd "ra" "sp" 0)) (.sd "s0" "sp" 8)) (.m (.base (.mv "s0" "a0"))) = st1 at k3
  have hm1 : st1.mem = writeSlots st.mem (S + BitVec.ofInt 64 (-16))
      [(0, st.regs.get "ra"), (8, st.regs.get "s0")] := by
    rw [← hst1, ← hS]
    simp only [evalX, evalMInst64, evalRInst64, addr, writeSlots, seNeg16,
      RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true,
      or_self]
    rfl
  have hsp1 : st1.regs.get "sp" = S + BitVec.ofInt 64 (-16) := by
    rw [← hst1, ← hS]
    simp only [evalX, evalMInst64, evalRInst64, seNeg16, RState64.get_set_same,
      RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  have hs01 : st1.regs.get "s0" = P := by
    rw [← hst1, ← hP]
    simp only [evalX, evalMInst64, evalRInst64, RState64.get_set_same, RState64.get_set_other,
      ne_eq, String.reduceEq, not_false_eq_true, or_self]
  have hr1 : ∀ r, r ≠ "sp" → r ≠ "s0" → st1.regs.get r = st.regs.get r := by
    intro r h1 h2
    rw [← hst1]
    simp only [evalX, evalMInst64, evalRInst64]
    rw [RState64.get_set_other _ _ _ _ h2, RState64.get_set_other _ _ _ _ h1]
  -- the stack frame and the block
  have hframe : RiscvFeMulFnProof.Sep (S + BitVec.ofInt 64 (-16)) 16 P 576 := by
    rw [a16]; exact sep_shift hsep 240 16 (by decide) (by decide) (by decide)
  have hblk1 : ∀ o, o + 32 ≤ 576 →
      memLimbs4 st1.mem (P + BitVec.ofNat 64 o) = memLimbs4 st.mem (P + BitVec.ofNat 64 o) := by
    intro o ho
    rw [hm1, memLimbs4_writeSlots_sepN _ _ _ _ 16 (by decide) (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp)]
    exact sep_sub hframe o 32 (by decide) ho (by decide)
  have hK1 : memLimbs4 st1.mem P = memLimbs4 st.mem P := by
    have := hblk1 0 (by decide); simpa using this
  -- the set-up
  have hshape1 : prog = (pre ++ stepPro) ++ setup.map .x ++
      (([.x (.m (.base (.mv "a0" "s0"))),
        .jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 46 : Nat) : Int)))] ++
        (callsCode fnIdx (pre.length + 47) xSteps ++ stepEpi)) ++ post) := by
    rw [hprog]; simp [x25519Code, List.append_assoc]
  have r1 := steps_block_of (base := base) hshape1 (by simp [stepPro, setup_length]; omega) st1
  simp only [List.length_append, show stepPro.length = 4 from rfl, setup_length] at r1
  generalize hst2 : runX st1 setup = st2 at r1
  have hm2 : st2.mem = writeSlots st1.mem P (setupSlots st1.mem P) := by
    rw [← hst2, setup_mem, hs01]
  have hreg2 : ∀ r ∈ "sp" :: "ra" :: "s0" :: frameSlots.map Prod.fst,
      st2.regs.get r = st1.regs.get r := fun r hr => by
    rw [← hst2]; exact runX_frame _ _ _ (setup_writes r hr)
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := setup_vals st1.mem P
  rw [← hm2] at v0 v1 v2 v3 v4 v5
  -- the ladder call
  have g45 : prog[pre.length + 4 + 41]? = some (.x (.m (.base (.mv "a0" "s0")))) := by
    rw [show pre.length + 4 + 41 = pre.length + 45 by omega, hat 45 (by omega)]; rfl
  have k45 := steps_x prog base (pre.length + 4 + 41) (by omega) _ g45 st2
  generalize hst3 : evalX st2 (.m (.base (.mv "a0" "s0"))) = st3 at k45
  have hm3 : st3.mem = st2.mem := by rw [← hst3]; rfl
  have ha03 : st3.regs.get "a0" = P := by
    rw [← hst3]
    simp only [evalX, evalMInst64, evalRInst64, RState64.get_set_same, String.reduceEq,
      not_false_eq_true, or_self]
    rw [hreg2 "s0" (by simp), hs01]
  have hr3 : ∀ r, r ≠ "a0" → st3.regs.get r = st2.regs.get r := by
    intro r hr; rw [← hst3]; exact RState64.get_set_other _ _ _ _ hr
  have g46 : prog[pre.length + 4 + 41 + 1]? = some (.jal "ra"
      (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 4 + 41 + 1 : Nat) : Int)))) := by
    rw [show pre.length + 4 + 41 + 1 = pre.length + 46 by omega, hat 46 (by omega)]; rfl
  have ne := fun (r : String) (h : r ≠ "ra") =>
    RState64.get_set_other st3.regs "ra" r (addrOf base (pre.length + 4 + 41 + 1 + 1)) h
  have hsp3 : st3.regs.get "sp" = S + BitVec.ofInt 64 (-16) := by
    rw [hr3 "sp" (by decide), hreg2 "sp" (by simp), hsp1]
  obtain ⟨n4, st4, r4, Lh, Lfs, Lsp, -, Lfr⟩ := steps_call_at prog base hb (pre.length + 4 + 41 + 1)
    0 (by omega) (by decide) g46 hL st3 (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ne "a0" (by decide), ne "sp" (by decide)]
      · rw [ha03, hsp3, a256]; exact sep_shrink hsep 240 (by decide)
      · rw [ha03, hm3, v3]; decide
      · rw [ha03, hm3, v5]; decide
      · rw [hsp3]; exact hspA.add_ofInt_neg (k := 16) (by decide) (by decide)
      · rw [ha03]; exact ha0A)
  simp only [ne "a0" (by decide), ne "sp" (by decide), ha03, hm3, hsp3] at Lh Lsp Lfr
  have hs04 : st4.regs.get "s0" = P := by
    rw [Lfs ("s0", 0) (by decide), ne "s0" (by decide), hr3 "s0" (by decide),
      hreg2 "s0" (by simp), hs01]
  -- the inversion and the final multiplication
  have hl' : (pre ++ stepPro ++ setup.map PInst64.x ++ [PInst64.x (.m (.base (.mv "a0" "s0"))),
      PInst64.jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 46 : Nat) : Int)))]).length
      = pre.length + 47 := by
    simp [stepPro, setup_length]
  have hprog' : prog = (pre ++ stepPro ++ setup.map PInst64.x ++ [PInst64.x (.m (.base (.mv "a0" "s0"))),
      PInst64.jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 46 : Nat) : Int)))])
      ++ callsCode fnIdx (pre ++ stepPro ++ setup.map PInst64.x ++ [PInst64.x (.m (.base (.mv "a0" "s0"))),
      PInst64.jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 46 : Nat) : Int)))]).length
        xSteps ++ (stepEpi ++ post) := by
    rw [hl', hprog]; simp [x25519Code, List.append_assoc]
  have hsep112 : RiscvFeMulFnProof.Sep (S + BitVec.ofInt 64 (-16) + BitVec.ofInt 64 (-112)) 112 P 576 := by
    rw [a128]; exact sep_shift hsep 128 112 (by decide) (by decide) (by decide)
  have hlen' : 4 * (pre.length + 47 + 4 * xSteps.length) < 2 ^ 20 := by
    rw [xSteps_length]; exact len_aux _ hlen
  obtain ⟨n5, st5, r5, hinv5, hfs5, hsp5, hfr5⟩ := run_calls prog base hb fnIdx hfn hF P
    (S + BitVec.ofInt 64 (-16)) hsep112 xSteps _ _ (fun p => memLimbs4 st4.mem (P + BitVec.ofNat 64 (off p)))
    st4 hprog' (by rw [hl']; exact hlen') xSteps_wf hs04 (by rw [Lsp]) (fun _ _ => rfl)
    (pre_of_ms _ _ xSteps_ms)
  rw [hl', xSteps_length] at r5
  rw [show pre.length + 47 + 4 * 266 = pre.length + 1111 by rw [Nat.add_assoc]] at r5
  -- the epilogue
  generalize hmid : (pre ++ stepPro ++ setup.map PInst64.x ++ [PInst64.x (.m (.base (.mv "a0" "s0"))),
      PInst64.jal "ra" (BitVec.ofInt 21 (4 * ((0 : Nat) : Int) - 4 * ((pre.length + 46 : Nat) : Int)))])
    = mid at hl' hprog'
  have hprogE : prog = (mid ++ callsCode fnIdx mid.length xSteps) ++ stepEpi ++ post := by
    rw [hprog']; simp only [List.append_assoc]
  have hlE : (mid ++ callsCode fnIdx mid.length xSteps).length = pre.length + 1111 := by
    rw [List.length_append, callsCode_length, hl', xSteps_length, Nat.add_assoc]
  have hatE := steps_mid prog _ post stepEpi hprogE
  rw [hlE] at hatE
  have e0 : prog[pre.length + 1111]? = some (.x (.ld "ra" "sp" 0)) := by
    have := hatE 0 (by decide); rw [Nat.add_zero] at this; rw [this]; rfl
  have e1 : prog[pre.length + 1111 + 1]? = some (.x (.ld "s0" "sp" 8)) := by
    rw [hatE 1 (by decide)]; rfl
  have e2 : prog[pre.length + 1111 + 1 + 1]? = some (.x (.m (.addi "sp" "sp" 16))) := by
    rw [show pre.length + 1111 + 1 + 1 = pre.length + 1111 + 2 from rfl, hatE 2 (by decide)]; rfl
  have e3 : prog[pre.length + 1111 + 1 + 1 + 1]? = some (.jalr "zero" "ra" 0) := by
    rw [show pre.length + 1111 + 1 + 1 + 1 = pre.length + 1111 + 3 from rfl, hatE 3 (by decide)]; rfl
  have q0 := steps_x prog base (pre.length + 1111) (b64 _ 1111 hlen (by decide)) _ e0 st5
  have q1 := steps_x prog base (pre.length + 1111 + 1) (b64 _ 1112 hlen (by decide)) _ e1
    (evalX st5 (.ld "ra" "sp" 0))
  have q2 := steps_x prog base (pre.length + 1111 + 1 + 1) (b64 _ 1113 hlen (by decide)) _ e2
    (evalX (evalX st5 (.ld "ra" "sp" 0)) (.ld "s0" "sp" 8))
  generalize hst6 : evalX (evalX (evalX st5 (.ld "ra" "sp" 0)) (.ld "s0" "sp" 8))
      (.m (.addi "sp" "sp" 16)) = st6 at q2
  have hm6 : st6.mem = st5.mem := by rw [← hst6]; rfl
  -- the two saved words
  have hslot : ∀ o, o < 16 → o % 8 = 0 →
      read64 st5.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o)
        = read64 st1.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) := by
    intro o ho _
    refine read64_congr _ _ _ fun j hj => ?_
    rw [add_ofNat_add]
    obtain ⟨b1, b2, b3⟩ := slot_byte' S P hsep (o + j) (by omega)
    have b4 := sep_into b3 32 544 (by decide) (by decide) (by decide)
    rw [hfr5 _ b2 b4, Lfr _ b1 b4, hm2,
      writeSlots_out _ _ _ _ fun q hq => sep_P P _ b3 q.1 (setupSlots_lt _ _ q hq)]
  have hsaved : ∀ o v, (o, v) ∈ [(0, st.regs.get "ra"), (8, st.regs.get "s0")] →
      read64 st1.mem (S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 o) = v := by
    intro o v hmem
    rw [hm1]
    exact read64_writeSlots_mem _ _ _ o v hmem (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
  have hra6 : st6.regs.get "ra" = st.regs.get "ra" := by
    rw [← hst6]
    simp only [evalX, evalMInst64, addr, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp5]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (0 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 0 from rfl,
      hslot 0 (by decide) (by decide), hsaved 0 (st.regs.get "ra") (by simp)]
  have hs06 : st6.regs.get "s0" = st.regs.get "s0" := by
    rw [← hst6]
    simp only [evalX, evalMInst64, addr, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp5]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (8 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 8 from rfl,
      hslot 8 (by decide) (by decide), hsaved 8 (st.regs.get "s0") (by simp)]
  have hsp6 : st6.regs.get "sp" = S := by
    rw [← hst6]
    simp only [evalX, evalMInst64, RState64.get_set_same, RState64.get_set_other, ne_eq,
      String.reduceEq, not_false_eq_true, or_self, hsp5]
    rw [show S + BitVec.ofInt 64 (-16) + BitVec.signExtend 64 (16 : BitVec 12)
        = S + BitVec.ofInt 64 (-16) + BitVec.ofNat 64 16 from rfl, addr_p16]
  have hr6 : ∀ r, r ≠ "ra" → r ≠ "s0" → r ≠ "sp" → st6.regs.get r = st5.regs.get r := by
    intro r h1 h2 h3
    rw [← hst6]
    simp only [evalX, evalMInst64]
    rw [RState64.get_set_other _ _ _ _ h3, RState64.get_set_other _ _ _ _ h2,
      RState64.get_set_other _ _ _ _ h1]
  have q3 : steps prog base 1 ⟨addrOf base (pre.length + 1111 + 1 + 1 + 1), st6⟩
      = some ⟨st.regs.get "ra" &&& ~~~1, st6⟩ := by
    simp only [steps, step, fetch_addrOf prog base (pre.length + 1111 + 1 + 1 + 1) (b64 _ 1114 hlen (by decide)), e3,
      Option.bind_some, hra6]
    rw [set_zero _ _ (Or.inl rfl)]
    simp
  -- the value
  have hb2 : blockState st2.mem P = X25519State.init (x25519Clamp (memLimbs4 st.mem P))
      (fromNat (fe st.mem P "x1" % 2 ^ 255)) := by
    have hu : memLimbs4 st1.mem (P + BitVec.ofNat 64 32) = fe st.mem P "x1" := hblk1 32 (by decide)
    simp only [blockState, X25519State.init, v0, v1, v2, v3, v4, v5, hK1, hu]
    simp [fromNat]
  rw [hb2] at Lh
  obtain ⟨-, hx2, hz2, -⟩ := Lh
  have xv := xSteps_value (fun p => memLimbs4 st4.mem (P + BitVec.ofNat 64 (off p)))
  have hx5 := hinv5 "x2" (by decide)
  refine ⟨1 + 1 + 1 + 1 + 41 + 1 + (1 + n4) + n5 + 1 + 1 + 1 + 1, st6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show pre.length + 1 + 1 + 1 + 1 = pre.length + 4 by omega] at k3
    rw [show pre.length + 4 + 41 + 1 + 1 = pre.length + 47 by omega] at r4
    exact steps_trans (steps_trans (steps_trans (steps_trans (steps_trans (steps_trans
      (steps_trans (steps_trans (steps_trans (steps_trans (steps_trans k0 k1) k2) k3) r1) k45) r4)
      r5) q0) q1) q2) q3
  · rw [hP, hm6]
    show memLimbs4 st5.mem (P + BitVec.ofNat 64 (off "x2")) = _
    rw [hx5]
    unfold x25519
    simp only
    rw [← ladderN_eq, ← hx2, ← hz2]
    change _ = ZMod.val (fromNat (memLimbs4 st4.mem (P + BitVec.ofNat 64 (off "x2"))) *
      fromNat (memLimbs4 st4.mem (P + BitVec.ofNat 64 (off "z2"))) ^ (P25519 - 2))
    rw [← xv.1, fromNat_val _ xv.2]
  · intro q hq
    by_cases hq0 : q.1 = "s0"
    · rw [hq0, hs06]
    · obtain ⟨na0, -, -, nra⟩ := frame_ne q hq
      have hne : q.1 ≠ "sp" := by
        simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      rw [hr6 _ nra hq0 hne, hfs5 q hq, Lfs q hq, ne _ nra, hr3 _ na0,
        hreg2 _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr
          (List.mem_map_of_mem hq)))), hr1 _ hne hq0]
  · rw [hsp6, hS]
  · exact hra6
  · intro x hx hx'
    rw [hS] at hx
    rw [hP] at hx'
    obtain ⟨b1, b2, b3, b4⟩ := frame_byte S P x hx hx'
    rw [hm6, hfr5 x b2 b3, Lfr x b1 b3, hm2,
      writeSlots_out _ _ _ _ fun q hq => sep_P P x hx' q.1 (setupSlots_lt _ _ q hq), hm1,
      writeSlots_out _ _ _ _ fun q hq => not_inRange_of_out (out_of_sep b4 (by simp)) ?_ (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp


/-! ## The C interface -/

/-- Close `(o, ?v) ∈ l` for a literal list `l`, assigning `?v`. -/
local macro "mem_at" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem))

/-- The words the prologue stores in its frame, from the state `st` it starts in. -/
def wproSlots (st : MState64) : List (Nat × BitVec 64) :=
  let r := fun (b : String) (o : Nat) => read64 st.mem (st.regs.get b + BitVec.ofNat 64 o)
  [(0, st.regs.get "ra"), (8, st.regs.get "a0"),
    (16, r "a1" 0), (24, r "a1" 8), (32, r "a1" 16), (40, r "a1" 24),
    (48, r "a2" 0), (56, r "a2" 8), (64, r "a2" 16), (72, r "a2" 24)]

theorem wpro_mem (st : MState64) :
    (runX st wpro).mem
      = writeSlots st.mem (st.regs.get "sp" + BitVec.ofInt 64 (-592)) (wproSlots st) := by
  simp only [wpro, runX_cons, runX_nil, evalX, evalMInst64, addr]
  simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
    not_false_eq_true, or_self]
  simp only [wproSlots, writeSlots]
  rfl

theorem wpro_sp (st : MState64) :
    (runX st wpro).regs.get "sp" = st.regs.get "sp" + BitVec.ofInt 64 (-592) := by
  simp only [wpro, runX_cons, runX_nil, evalX, evalMInst64, RState64.get_set_same,
    RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  rfl

theorem wpro_a0 (st : MState64) :
    (runX st wpro).regs.get "a0"
      = st.regs.get "sp" + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 16 := by
  simp only [wpro, runX_cons, runX_nil, evalX, evalMInst64, RState64.get_set_same,
    RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  rfl

theorem wpro_writes : xWrites wpro = ["t0", "t1", "t2", "t3", "a3", "a4", "a5", "a6", "sp", "a0"] :=
  rfl

theorem wepi_mem (st : MState64) :
    (runX st wepi).mem = writeSlots st.mem (read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 8))
      [(0, read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 80)),
        (8, read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 88)),
        (16, read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 96)),
        (24, read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 104))] := by
  simp only [wepi, runX_cons, runX_nil, evalX, evalMInst64, addr]
  simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
    not_false_eq_true, or_self]
  simp only [writeSlots]
  rfl

theorem wepi_ra (st : MState64) :
    (runX st wepi).regs.get "ra" = read64 st.mem (st.regs.get "sp" + BitVec.ofNat 64 0) := by
  simp only [wepi, runX_cons, runX_nil, evalX, evalMInst64, addr, RState64.get_set_same,
    RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  rfl

theorem wepi_sp (st : MState64) :
    (runX st wepi).regs.get "sp" = st.regs.get "sp" + BitVec.ofNat 64 592 := by
  simp only [wepi, runX_cons, runX_nil, evalX, evalMInst64, RState64.get_set_same,
    RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  rfl

theorem wepi_writes : xWrites wepi = ["a0", "ra", "t0", "t1", "t2", "t3", "sp"] := rfl

theorem wproSlots_read (st : MState64) (B : BitVec 64) (o : Nat) (v : BitVec 64)
    (h : (o, v) ∈ wproSlots st) :
    read64 (writeSlots st.mem B (wproSlots st)) (B + BitVec.ofNat 64 o) = v := by
  refine read64_writeSlots_mem _ _ _ o v h ?_ ?_ ?_ <;>
    simp only [wproSlots, List.map_cons, List.map_nil] <;> decide

/-- Four words written at `p`, read back as a 256-bit integer. -/
theorem memLimbs4_write4 (m : AMem) (p w0 w1 w2 w3 : BitVec 64) :
    memLimbs4 (writeSlots m p [(0, w0), (8, w1), (16, w2), (24, w3)]) p
      = w0.toNat + 2 ^ 64 * w1.toNat + 2 ^ 128 * w2.toNat + 2 ^ 192 * w3.toNat := by
  have h := fun o v (hm : (o, v) ∈ [(0, w0), (8, w1), (16, w2), (24, w3)]) =>
    read64_writeSlots_mem m p _ o v hm (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
  unfold memLimbs4
  rw [h 0 w0 (by simp), h 8 w1 (by simp), h 16 w2 (by simp), h 24 w3 (by simp)]

theorem sep_ofs (Q : BitVec 64) (n k m : Nat) (hk0 : 0 < k) (hk : n ≤ k) (hm : k + m ≤ 2 ^ 64)
    (hk' : k < 2 ^ 64) : Sep Q n (Q + BitVec.ofNat 64 k) m := by
  have := Q.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem slot_sep (Q : BitVec 64) (t : Nat) (ht : t < 16) :
    Sep Q 256 (Q + BitVec.ofNat 64 (256 + t)) 1 ∧
      Sep (Q + BitVec.ofNat 64 272) 576 (Q + BitVec.ofNat 64 (256 + t)) 1 := by
  have := Q.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem w256 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-592) + BitVec.ofInt 64 (-256) = S + BitVec.ofInt 64 (-848) := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-592) + BitVec.ofInt 64 (-256) = BitVec.ofInt 64 (-848) by decide]

theorem w592 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-592) = S + BitVec.ofInt 64 (-848) + BitVec.ofNat 64 256 := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-848) + BitVec.ofNat 64 256 = BitVec.ofInt 64 (-592) by decide]

theorem w16 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 16
      = S + BitVec.ofInt 64 (-848) + BitVec.ofNat 64 272 := by
  rw [w592, add_ofNat_add]

theorem w0 (S : BitVec 64) : S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 592 = S := by
  rw [BitVec.add_assoc, show BitVec.ofInt 64 (-592) + BitVec.ofNat 64 592 = 0 by decide]
  simp

/-- The entry condition of `catcrypt_x25519(out, scalar, u)`: `sp` is 16-byte aligned and
    the three pointers `a0 = out`, `a1 = scalar`, `a2 = u` are 8-byte aligned. Nothing is
    required of where the buffers lie: the scalar and `u` are read before any store, and the
    output is written after the last load. The proof uses only the alignment of `sp`, to give
    the block function its own. -/
def X25519CPre (st : MState64) : Prop :=
  Aligned 16 (st.regs.get "sp") ∧ Aligned 8 (st.regs.get "a0") ∧
    Aligned 8 (st.regs.get "a1") ∧ Aligned 8 (st.regs.get "a2")

/-- The effect of `catcrypt_x25519`: the 32 bytes at `out` hold `X25519(k, u)` for the
    256-bit little-endian `k` at `scalar` and `u` at `u`, as its canonical integer; `s0..s11`,
    `sp` and `ra` are restored; no byte outside the 848 bytes below `sp` and the output
    changed. -/
def X25519CPost (st st' : MState64) : Prop :=
  memLimbs4 st'.mem (st.regs.get "a0")
      = (x25519 (memLimbs4 st.mem (st.regs.get "a1")) (memLimbs4 st.mem (st.regs.get "a2"))).val ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra" ∧
    ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-848)) 848 x 1 →
      Sep (st.regs.get "a0") 32 x 1 → st'.mem x = st.mem x

/-- **The C interface is a function.** `wrapCode j` placed in any program whose instruction
    `j` is the block function of `fnSpec_x25519` meets `FnSpec` with `X25519CPre` and
    `X25519CPost`. -/
theorem fnSpec_wrap (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0) (j : Nat)
    (hX : FnSpec prog base (addrOf base j) X25519Pre X25519Post) (hj : 4 * j < 2 ^ 20)
    (pre post : List PInst64) (hprog : prog = pre ++ wrapCode j pre.length ++ post)
    (hlen : 4 * (pre.length + 33) < 2 ^ 20) :
    FnSpec prog base (addrOf base pre.length) X25519CPre X25519CPost := by
  intro st ⟨hspA, _, _, _⟩
  generalize hS : st.regs.get "sp" = S at hspA
  have hat := steps_mid prog pre post _ hprog
  -- the prologue
  have hshape1 : prog = pre ++ wpro.map .x ++
      (([.jal "ra" (BitVec.ofInt 21 (4 * (j : Int) - 4 * ((pre.length + 20 : Nat) : Int)))] ++
        (wepi.map .x ++ [.jalr "zero" "ra" 0])) ++ post) := by
    rw [hprog]; simp [wrapCode, List.append_assoc]
  have r1 := steps_block_of (base := base) hshape1 (by rw [wpro_length]; omega) st
  rw [wpro_length] at r1
  generalize hst1 : runX st wpro = st1 at r1
  have hm1 : st1.mem = writeSlots st.mem (S + BitVec.ofInt 64 (-592)) (wproSlots st) := by
    rw [← hst1, wpro_mem, hS]
  have hsp1 : st1.regs.get "sp" = S + BitVec.ofInt 64 (-592) := by rw [← hst1, wpro_sp, hS]
  have ha01 : st1.regs.get "a0" = S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 16 := by
    rw [← hst1, wpro_a0, hS]
  have hr1 : ∀ r ∈ "ra" :: frameSlots.map Prod.fst, st1.regs.get r = st.regs.get r :=
    fun r hr => by
      rw [← hst1]; refine runX_frame _ _ _ ?_
      rw [wpro_writes]; revert r; decide
  -- the block in the frame
  have hslot := wproSlots_read st (S + BitVec.ofInt 64 (-592))
  have hK : memLimbs4 st1.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 16)
      = memLimbs4 st.mem (st.regs.get "a1") := by
    rw [hm1]; unfold memLimbs4
    simp only [add_ofNat_add, Nat.reduceAdd]
    rw [hslot 16 _ (by simp only [wproSlots]; mem_at), hslot 24 _ (by simp only [wproSlots]; mem_at), hslot 32 _ (by simp only [wproSlots]; mem_at), hslot 40 _ (by simp only [wproSlots]; mem_at)]
  have hU : fe st1.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 16) "x1"
      = memLimbs4 st.mem (st.regs.get "a2") := by
    rw [hm1]; unfold fe memLimbs4
    rw [show off "x1" = 32 from rfl]
    simp only [add_ofNat_add, Nat.reduceAdd]
    rw [hslot 48 _ (by simp only [wproSlots]; mem_at), hslot 56 _ (by simp only [wproSlots]; mem_at), hslot 64 _ (by simp only [wproSlots]; mem_at), hslot 72 _ (by simp only [wproSlots]; mem_at)]
  -- the call
  have g20 : prog[pre.length + 20]? = some (.jal "ra"
      (BitVec.ofInt 21 (4 * (j : Int) - 4 * ((pre.length + 20 : Nat) : Int)))) := by
    rw [hat 20 (by rw [wrapCode_length]; decide)]; rfl
  have ne := fun (r : String) (h : r ≠ "ra") =>
    RState64.get_set_other st1.regs "ra" r (addrOf base (pre.length + 20 + 1)) h
  obtain ⟨n2, st2, r2, Xv, Xfs, Xsp, -, Xfr⟩ := steps_call_at prog base hb (pre.length + 20) j
    (by omega) hj g20 hX st1 (by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [ne "a0" (by decide), ne "sp" (by decide), hsp1, ha01]
      · rw [w256, w16]; exact sep_ofs _ 256 272 576 (by decide) (by decide) (by decide) (by decide)
      · exact hspA.add_ofInt_neg (k := 592) (by decide) (by decide)
      · exact ((hspA.add_ofInt_neg (k := 592) (by decide) (by decide)).add_ofNat (k := 16)
          (by decide) (by decide)).of_dvd (by decide))
  simp only [ne "a0" (by decide), ne "sp" (by decide), hsp1, ha01] at Xv Xsp Xfr
  rw [hK, hU] at Xv
  -- bytes the callee leaves alone
  have hout : ∀ x, Sep (S + BitVec.ofInt 64 (-848)) 256 x 1 →
      Sep (S + BitVec.ofInt 64 (-848) + BitVec.ofNat 64 272) 576 x 1 → st2.mem x = st1.mem x :=
    fun x h1 h2 => Xfr x (by rw [w256]; exact h1) (by rw [w16]; exact h2)
  have hsaved : ∀ o, o + 8 ≤ 16 →
      read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 o)
        = read64 st1.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 o) := by
    intro o ho
    refine read64_congr _ _ _ fun i hi => ?_
    rw [w592, add_ofNat_add, add_ofNat_add]
    exact hout _ (slot_sep _ (o + i) (by omega)).1 (slot_sep _ (o + i) (by omega)).2
  -- the epilogue
  have hshape3 : prog = (pre ++ wpro.map .x ++
      [.jal "ra" (BitVec.ofInt 21 (4 * (j : Int) - 4 * ((pre.length + 20 : Nat) : Int)))]) ++
        wepi.map .x ++ ([.jalr "zero" "ra" 0] ++ post) := by
    rw [hprog]; simp [wrapCode, List.append_assoc]
  have r3 := steps_block_of (base := base) hshape3
    (by simp [wpro_length, wepi_length]; omega) st2
  simp only [List.length_append, wpro_length, wepi_length,
    List.length_map, List.length_cons, List.length_nil] at r3
  generalize hst3 : runX st2 wepi = st3 at r3
  have hO : read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 8) = st.regs.get "a0" := by
    rw [hsaved 8 (by decide), hm1, hslot 8 _ (by simp only [wproSlots]; mem_at)]
  have hra3 : st3.regs.get "ra" = st.regs.get "ra" := by
    rw [← hst3, wepi_ra, Xsp, hsaved 0 (by decide), hm1, hslot 0 _ (by simp only [wproSlots]; mem_at)]
  have hm3 : st3.mem = writeSlots st2.mem (st.regs.get "a0")
      [(0, read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 80)),
        (8, read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 88)),
        (16, read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 96)),
        (24, read64 st2.mem (S + BitVec.ofInt 64 (-592) + BitVec.ofNat 64 104))] := by
    rw [← hst3, wepi_mem, Xsp, hO]
  have e32 : prog[pre.length + 20 + 1 + 11]? = some (.jalr "zero" "ra" 0) := by
    rw [hat 32 (by rw [wrapCode_length]; decide)]; rfl
  have q4 : steps prog base 1 ⟨addrOf base (pre.length + 20 + 1 + 11), st3⟩
      = some ⟨st.regs.get "ra" &&& ~~~1, st3⟩ := by
    simp only [steps, step, fetch_addrOf prog base (pre.length + 20 + 1 + 11) (by omega), e32,
      Option.bind_some, hra3]
    rw [set_zero _ _ (Or.inl rfl)]
    simp
  refine ⟨20 + (1 + n2) + 11 + 1, st3, ?_, ?_, ?_, ?_, hra3, ?_⟩
  · exact steps_trans (steps_trans (steps_trans r1 r2) r3) q4
  · rw [hm3, memLimbs4_write4, ← Xv]
    unfold fe memLimbs4
    rw [show off "x2" = 64 from rfl]
    simp only [add_ofNat_add, Nat.reduceAdd]
  · intro q hq
    have hq' : q.1 ∉ xWrites wepi := by
      rw [wepi_writes]
      simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [← hst3, runX_frame _ _ _ hq', Xfs q hq, ne _ (frame_ne q hq).2.2.2,
      hr1 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hq))]
  · rw [← hst3, wepi_sp, Xsp, w0, hS]
  · intro x hx hxO
    rw [hS] at hx
    rw [hm3, writeSlots_out _ _ _ _ fun q hq => not_inRange_of_out (out_of_sep hxO (by simp)) ?_
      (by decide)]
    · rw [hout x (sep_shrink hx 256 (by decide))
          (sep_into hx 272 576 (by decide) (by decide) (by decide)), hm1,
        w592, writeSlots_out _ _ _ _ fun q hq => not_inRange_of_out
          (out_of_sep (sep_into hx 256 80 (by decide) (by decide) (by decide)) (by simp))
          ?_ (by decide)]
      simp only [wproSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp

/-! ## Bytes -/

/-- The `n` bytes from `p`. -/
def bytesAt (m : AMem) (p : BitVec 64) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

theorem bytesAt_length (m : AMem) (p : BitVec 64) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem toNat_read64 (m : AMem) (a : BitVec 64) :
    (read64 m a).toNat = (m a).toNat + 2 ^ 8 * (m (a + BitVec.ofNat 64 1)).toNat
      + 2 ^ 16 * (m (a + BitVec.ofNat 64 2)).toNat + 2 ^ 24 * (m (a + BitVec.ofNat 64 3)).toNat
      + 2 ^ 32 * (m (a + BitVec.ofNat 64 4)).toNat + 2 ^ 40 * (m (a + BitVec.ofNat 64 5)).toNat
      + 2 ^ 48 * (m (a + BitVec.ofNat 64 6)).toNat + 2 ^ 56 * (m (a + BitVec.ofNat 64 7)).toNat := by
  unfold read64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := (m a).isLt
  have := (m (a + BitVec.ofNat 64 1)).isLt; have := (m (a + BitVec.ofNat 64 2)).isLt
  have := (m (a + BitVec.ofNat 64 3)).isLt; have := (m (a + BitVec.ofNat 64 4)).isLt
  have := (m (a + BitVec.ofNat 64 5)).isLt; have := (m (a + BitVec.ofNat 64 6)).isLt
  have := (m (a + BitVec.ofNat 64 7)).isLt
  omega

/-- Four little-endian words at `p` are the 32 little-endian bytes at `p`. -/
theorem memLimbs4_eq_decodeLE (m : AMem) (p : BitVec 64) :
    memLimbs4 m p = decodeLE (bytesAt m p 32) := by
  simp only [memLimbs4, toNat_read64, add_ofNat_add, Nat.reduceAdd, bytesAt, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil, decodeLE]
  omega

/-! ## The program at bytes -/

theorem x25519Prog_length : x25519Prog.length = 4246 := by
  rw [x25519Prog, List.length_append, List.length_append, ladderProg_length, x25519Code_length,
    wrapCode_length]

theorem x25519Prog_ok : x25519Prog.all PInstOKb = true := by
  rw [x25519Prog, List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem x25519Prog_decode :
    decodePStream64 4246 (encodePBlock64 x25519Prog) = some x25519Prog := by
  rw [← x25519Prog_length]; exact decodePStream64_encode_b _ x25519Prog_ok

theorem x25519Prog_spec (base : BitVec 64) (hb : base &&& 3 = 0) :
    FnSpec x25519Prog base (addrOf base 3098) X25519Pre X25519Post := by
  have := fnSpec_x25519 x25519Prog base hb (fnSpecs' _ base) (ladderSpec' _ base hb) ladderProg
    (wrapCode 3098 4213) (by rw [ladderProg_length, x25519Prog, List.append_assoc])
    (by rw [ladderProg_length]; decide)
  rwa [ladderProg_length] at this

theorem x25519CProg_spec (base : BitVec 64) (hb : base &&& 3 = 0) :
    FnSpec x25519Prog base (addrOf base 4213) X25519CPre X25519CPost := by
  have hl : (ladderProg ++ x25519Code 3098).length = 4213 := by
    rw [List.length_append, ladderProg_length, x25519Code_length]
  have := fnSpec_wrap x25519Prog base hb 3098 (x25519Prog_spec base hb) (by decide)
    (ladderProg ++ x25519Code 3098) [] (by rw [hl, List.append_nil, x25519Prog, List.append_assoc])
    (by rw [hl]; decide)
  rwa [hl] at this

/-- The output of `catcrypt_x25519` as bytes: under `X25519CPost`, the 32 bytes at `out` are
    `x25519Bytes` of the 32 bytes at `scalar` and the 32 bytes at `u`. -/
theorem x25519C_bytes (st st' : MState64) (h : X25519CPost st st') :
    bytesAt st'.mem (st.regs.get "a0") 32
      = x25519Bytes (bytesAt st.mem (st.regs.get "a1") 32) (bytesAt st.mem (st.regs.get "a2") 32) := by
  have e := encodeLE_decodeLE (bytesAt st'.mem (st.regs.get "a0") 32)
  rw [bytesAt_length, ← memLimbs4_eq_decodeLE, h.1, memLimbs4_eq_decodeLE,
    memLimbs4_eq_decodeLE] at e
  rw [x25519Bytes]; exact e.symm

/-- **The encoded X25519 block function.** The bytes of `x25519Prog` decode as 4246
    instructions `prog` such that, loaded at any word-aligned `base`, the function at
    instruction 3098 meets `FnSpec` with `X25519Pre` and `X25519Post`: from every state whose
    256 bytes below `sp` are disjoint from the 576-byte state block at `a0`, holding the scalar
    `k` at offset 0 and the `u`-coordinate at offset 32, a run returns to `ra` with `x25519 k u`,
    the RFC 7748 function, at offset 64, `s0..s11`, `sp` and `ra` restored, and no byte outside
    the frame below `sp` and the block changed. -/
theorem x25519Bytes_correct :
    ∃ prog, decodePStream64 4246 (encodePBlock64 x25519Prog) = some prog ∧
      ∀ base : BitVec 64, base &&& 3 = 0 →
        FnSpec prog base (addrOf base 3098) X25519Pre X25519Post :=
  ⟨x25519Prog, x25519Prog_decode, x25519Prog_spec⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof.x25519Bytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519Bytes_correct

/-- **The encoded C function `catcrypt_x25519(out, scalar, u)`.** The bytes of `x25519Prog`
    decode as 4246 instructions `prog` such that, loaded at any word-aligned `base`, the
    function at instruction 4213 meets `FnSpec`: from every state with `sp` 16-byte aligned and
    `out`, `scalar`, `u` in `a0`, `a1`, `a2` 8-byte aligned, a run returns to `ra` with the 32
    bytes at `out` equal to `x25519Bytes` of the 32 bytes at `scalar` and at `u` (RFC 7748
    `X25519` on byte strings), `s0..s11`, `sp` and `ra` restored, and no byte outside the 848
    bytes below `sp` and the output changed. -/
theorem x25519CBytes_correct :
    ∃ prog, decodePStream64 4246 (encodePBlock64 x25519Prog) = some prog ∧
      ∀ base : BitVec 64, base &&& 3 = 0 →
        FnSpec prog base (addrOf base 4213) X25519CPre fun st st' =>
          bytesAt st'.mem (st.regs.get "a0") 32
              = x25519Bytes (bytesAt st.mem (st.regs.get "a1") 32)
                  (bytesAt st.mem (st.regs.get "a2") 32) ∧
            X25519CPost st st' :=
  ⟨x25519Prog, x25519Prog_decode, fun base hb =>
    fnSpec_weaken (x25519CProg_spec base hb) (fun _ h => h)
      fun st st' _ h => ⟨x25519C_bytes st st' h, h⟩⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof.x25519CBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms x25519CBytes_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519Proof
