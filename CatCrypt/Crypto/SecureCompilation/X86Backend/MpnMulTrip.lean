/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulShipped
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulLoopReach
public import CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem
public import CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms

@[expose] public section

set_option autoImplicit false

/-!
# The inner trip of the linked `mpn_mul_basecase_rt` on the address machine

The inner trip `MpnMulShipped.mulInner` of the linked multiply, run by `runBlockA`, as seven
straight segments `tS1` … `tS7`, each computed symbolically by the per-instruction state
equations `eA_*`. The carry idiom of the shipped code (`xor` with all ones for the
complement, `(p ^ q) ^ (p & q)` for the disjunction) is `FieldReduceIdioms.bSltu`
(`ltu_idiom`).

## Main results

* `mulInner_eq`: the inner trip is `tS1 ++ … ++ tS7`.
* `tS1_run` … `tS7_run`: the segments' effects on the registers and the memory.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulShipped
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms (bSltu)

/-! ## 1. Per-instruction state equations -/

/-- A register file with `d` set to `v`. -/
def upd (f : String → BitVec 64) (d : String) (v : BitVec 64) : String → BitVec 64 :=
  fun r => if r = d then v else f r

theorem upd_apply (f : String → BitVec 64) (d r : String) (v : BitVec 64) :
    upd f d v r = if r = d then v else f r := rfl

/-- The flags after an instruction (left unevaluated in the state equations). -/
def flA (sa : AState) (i : JInstr 64) : RFlags := (evalInstr sa.view i).flags

/-- The address `b + 8 x` of an indexed access with scale `8`. -/
def ix (b x : BitVec 64) : BitVec 64 := b + BitVec.ofInt 64 ((8 * x.toNat : Nat) : Int)

/-- The address `b + o` of a displacement access. -/
def at' (b : BitVec 64) (o : Int) : BitVec 64 := b + BitVec.ofInt 64 o

theorem eA_mov_reg (sa : AState) (d s : String) :
    evalInstrA sa (.mov d (.reg s)) = ⟨upd sa.regs d (sa.regs s), sa.flags, sa.mem⟩ := rfl

theorem eA_mov_imm (sa : AState) (d : String) (v : Nat) :
    evalInstrA sa (.mov d (.imm v)) = ⟨upd sa.regs d (BitVec.ofNat 64 v), sa.flags, sa.mem⟩ :=
  rfl

theorem eA_xor (sa : AState) (d s : String) :
    evalInstrA sa (.xor_ d (.reg s))
      = ⟨upd sa.regs d (sa.regs d ^^^ sa.regs s), flA sa (.xor_ d (.reg s)), sa.mem⟩ := rfl

theorem eA_and (sa : AState) (d s : String) :
    evalInstrA sa (.and_ d (.reg s))
      = ⟨upd sa.regs d (sa.regs d &&& sa.regs s), flA sa (.and_ d (.reg s)), sa.mem⟩ := rfl

theorem eA_sub (sa : AState) (d s : String) :
    evalInstrA sa (.sub d (.reg s))
      = ⟨upd sa.regs d (sa.regs d - sa.regs s), flA sa (.sub d (.reg s)), sa.mem⟩ := rfl

theorem eA_add (sa : AState) (d s : String) :
    evalInstrA sa (.add d (.reg s))
      = ⟨upd sa.regs d (sa.regs d + sa.regs s), flA sa (.add d (.reg s)), sa.mem⟩ := rfl

theorem eA_add_imm (sa : AState) (d : String) (v : Nat) :
    evalInstrA sa (.add d (.imm v))
      = ⟨upd sa.regs d (sa.regs d + BitVec.ofNat 64 v), flA sa (.add d (.imm v)), sa.mem⟩ := rfl

theorem eA_sub_imm (sa : AState) (d : String) (v : Nat) :
    evalInstrA sa (.sub d (.imm v))
      = ⟨upd sa.regs d (sa.regs d - BitVec.ofNat 64 v), flA sa (.sub d (.imm v)), sa.mem⟩ := rfl

theorem eA_imul (sa : AState) (d s : String) :
    evalInstrA sa (.imul d (.reg s))
      = ⟨upd sa.regs d (sa.regs d * sa.regs s), flA sa (.imul d (.reg s)), sa.mem⟩ := rfl

theorem eA_shr63 (sa : AState) (d : String) :
    evalInstrA sa (.shr d (.imm 63))
      = ⟨upd sa.regs d (sa.regs d >>> 63), flA sa (.shr d (.imm 63)), sa.mem⟩ := by
  have h : (x86_SHR (sa.regs d) (BitVec.ofNat 64 63)).word = sa.regs d >>> 63 := by
    simp [x86_SHR, shiftCount, rflags_OF, wshr]
  show (⟨_, _, _⟩ : AState) = _
  congr 1

theorem eA_cmp (sa : AState) (d : String) (v : JOperand) :
    evalInstrA sa (.cmp d v) = ⟨sa.regs, flA sa (.cmp d v), sa.mem⟩ := rfl

theorem eA_cmpMem (sa : AState) (d b : String) (o : Int) :
    evalInstrA sa (.cmpMem d b o) = ⟨sa.regs, flA sa (.cmpMem d b o), sa.mem⟩ := rfl

theorem eA_mulx (sa : AState) (H D S C : String) :
    evalInstrA sa (.mulx H D (.reg S) (.reg C))
      = ⟨upd (upd sa.regs D (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).1) H
          (x86_MULX_lo_hi (sa.regs S) (sa.regs C)).2, sa.flags, sa.mem⟩ := rfl

theorem eA_loadMem (sa : AState) (d b : String) (o : Int) :
    evalInstrA sa (.loadMem d b o)
      = ⟨upd sa.regs d (read64 sa.mem (at' (sa.regs b) o)), sa.flags, sa.mem⟩ := rfl

theorem eA_loadMemIdx (sa : AState) (d b x : String) :
    evalInstrA sa (.loadMemIdx d b x 8)
      = ⟨upd sa.regs d (read64 sa.mem (ix (sa.regs b) (sa.regs x))), sa.flags, sa.mem⟩ := rfl

theorem eA_storeMem (sa : AState) (b : String) (o : Int) (r : String) :
    evalInstrA sa (.storeMem b o (.reg r))
      = ⟨sa.regs, sa.flags, write64 sa.mem (at' (sa.regs b) o) (sa.regs r)⟩ := rfl

theorem eA_storeMemIdx (sa : AState) (b x r : String) :
    evalInstrA sa (.storeMemIdx b x 8 (.reg r))
      = ⟨sa.regs, sa.flags, write64 sa.mem (ix (sa.regs b) (sa.regs x)) (sa.regs r)⟩ := rfl

/-- The zero flag after `cmp d, 0`. -/
theorem cmp0_zf (sa : AState) (d : String) :
    (evalInstrA sa (.cmp d (.imm 0))).view.flagB (·.zf) = decide (sa.regs d = 0) := by
  simp only [evalInstrA, AState.view, evalInstr, JState.writeB5, JState.flagB, x86_CMP,
    x86_SUB, ZF_of_word, JOperand.eval, JState.get, Option.getD_some]
  simp [BitVec.toNat_eq]

/-! ## 2. Word identities of the shipped carry idiom -/

theorem xor_allOnes (x : BitVec 64) : x ^^^ 18446744073709551615#64 = ~~~x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]

theorem xor_xor_and (p q : BitVec 64) : (p ^^^ q) ^^^ (p &&& q) = p ||| q := by
  ext i hi; simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases p[i] <;> cases q[i] <;> rfl

/-- **The shipped carry idiom is `bSltu`.** -/
theorem ltu_idiom (a b : BitVec 64) :
    ((a ^^^ 18446744073709551615#64) &&& b ^^^ (a ^^^ b ^^^ 18446744073709551615#64) &&& (a - b)
        ^^^ (a ^^^ 18446744073709551615#64) &&& b
          &&& ((a ^^^ b ^^^ 18446744073709551615#64) &&& (a - b))) >>> 63 = bSltu a b := by
  rw [xor_allOnes, xor_allOnes, xor_xor_and]; rfl

/-! ## 3. The segments of the inner trip -/

def tS1 : List (JInstr 64) :=
  [ .mov "%r9" (.imm 18446744073709551615)
  , .mov "%r12" (.reg "%r10")
  , .xor_ "%r12" (.reg "%r9")
  , .mov "%r9" (.reg "%r12")
  , .and_ "%r9" (.reg "%rdi")
  , .mov "%r12" (.reg "%r9")
  , .mov "%r9" (.reg "%r10")
  , .xor_ "%r9" (.reg "%rdi")
  , .mov "%r13" (.imm 18446744073709551615)
  , .mov "%rsi" (.reg "%r9")
  , .xor_ "%rsi" (.reg "%r13")
  , .mov "%r9" (.reg "%r10")
  , .sub "%r9" (.reg "%rdi")
  , .mov "%r13" (.reg "%rsi")
  , .and_ "%r13" (.reg "%r9")
  , .mov "%rsi" (.reg "%r13")
  , .mov "%r9" (.reg "%r12")
  , .xor_ "%r9" (.reg "%rsi")
  , .mov "%r13" (.reg "%r12")
  , .and_ "%r13" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r9")
  , .xor_ "%rsi" (.reg "%r13")
  , .mov "%r9" (.imm 63)
  , .mov "%r9" (.reg "%rsi")
  , .shr "%r9" (.imm 63)
  , .mov "%rsi" (.reg "%r9")
  , .mov "%r9" (.imm 0)
  , .mov "%r12" (.reg "%r9")
  , .sub "%r12" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r12")
  , .mov "%r9" (.reg "%r10")
  , .and_ "%r9" (.reg "%rsi")
  , .mov "%r12" (.reg "%r9") ]

def tS2 : List (JInstr 64) :=
  [ .loadMem "%r14" "%rsp" 112
  , .loadMemIdx "%r9" "%r14" "%r12" 8
  , .mov "%r12" (.reg "%r9")
  , .and_ "%r12" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r12")
  , .loadMem "%r14" "%rsp" (-8)
  , .loadMemIdx "%r9" "%r14" "%rax" 8
  , .mov "%r12" (.reg "%rsi")
  , .imul "%r12" (.reg "%r9")
  , .mov "%r13" (.reg "%r12")
  , .mov "%r15" (.reg "%rdx")
  , .mov "%rdx" (.reg "%rsi")
  , .mulx "%r12" "%r12" (.reg "%rdx") (.reg "%r9")
  , .mov "%rdx" (.reg "%r15")
  , .mov "%r15" (.reg "%r12")
  , .storeMem "%rsp" 48 (.reg "%r15") ]

def tS3 : List (JInstr 64) :=
  [ .mov "%r9" (.reg "%rdi")
  , .loadMem "%r15" "%rsp" 24
  , .add "%r9" (.reg "%r15")
  , .mov "%r15" (.reg "%r9")
  , .storeMem "%rsp" 32 (.reg "%r15")
  , .loadMem "%r14" "%rsp" 120
  , .loadMem "%r15" "%rsp" 32
  , .loadMemIdx "%r9" "%r14" "%r15" 8 ]

def tS4 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%r13")
  , .add "%rsi" (.reg "%r9")
  , .mov "%r9" (.reg "%rsi")
  , .mov "%rsi" (.imm 18446744073709551615)
  , .mov "%rcx" (.reg "%r9")
  , .xor_ "%rcx" (.reg "%rsi")
  , .mov "%rsi" (.reg "%rcx")
  , .and_ "%rsi" (.reg "%r13")
  , .mov "%rcx" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r9")
  , .xor_ "%rsi" (.reg "%r13")
  , .mov "%r12" (.imm 18446744073709551615)
  , .mov "%rbp" (.reg "%rsi")
  , .xor_ "%rbp" (.reg "%r12")
  , .mov "%rsi" (.reg "%r9")
  , .sub "%rsi" (.reg "%r13")
  , .mov "%r12" (.reg "%rbp")
  , .and_ "%r12" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r12")
  , .mov "%rbp" (.reg "%rcx")
  , .xor_ "%rbp" (.reg "%rsi")
  , .mov "%r12" (.reg "%rcx")
  , .and_ "%r12" (.reg "%rsi")
  , .mov "%rcx" (.reg "%rbp")
  , .xor_ "%rcx" (.reg "%r12")
  , .mov "%rsi" (.imm 63)
  , .mov "%rsi" (.reg "%rcx")
  , .shr "%rsi" (.imm 63)
  , .mov "%r15" (.reg "%rsi")
  , .storeMem "%rsp" 16 (.reg "%r15") ]

def tS5 : List (JInstr 64) :=
  [ .mov "%rsi" (.reg "%rax")
  , .add "%rsi" (.reg "%r10")
  , .mov "%r15" (.reg "%rsi")
  , .storeMem "%rsp" 8 (.reg "%r15")
  , .loadMem "%r14" "%rsp" 120
  , .loadMem "%r15" "%rsp" 8
  , .loadMemIdx "%rsi" "%r14" "%r15" 8
  , .mov "%r12" (.reg "%r9")
  , .add "%r12" (.reg "%rsi")
  , .mov "%rsi" (.reg "%r12") ]

def tS6 : List (JInstr 64) :=
  [ .mov "%r12" (.imm 18446744073709551615)
  , .mov "%r13" (.reg "%rsi")
  , .xor_ "%r13" (.reg "%r12")
  , .mov "%r12" (.reg "%r13")
  , .and_ "%r12" (.reg "%r9")
  , .mov "%r13" (.reg "%r12")
  , .mov "%r12" (.reg "%rsi")
  , .xor_ "%r12" (.reg "%r9")
  , .mov "%rcx" (.imm 18446744073709551615)
  , .mov "%rbp" (.reg "%r12")
  , .xor_ "%rbp" (.reg "%rcx")
  , .mov "%rcx" (.reg "%rsi")
  , .sub "%rcx" (.reg "%r9")
  , .mov "%r9" (.reg "%rbp")
  , .and_ "%r9" (.reg "%rcx")
  , .mov "%rcx" (.reg "%r9")
  , .mov "%rbp" (.reg "%r13")
  , .xor_ "%rbp" (.reg "%rcx")
  , .mov "%r9" (.reg "%r13")
  , .and_ "%r9" (.reg "%rcx")
  , .mov "%rcx" (.reg "%rbp")
  , .xor_ "%rcx" (.reg "%r9")
  , .mov "%rbp" (.imm 63)
  , .mov "%rbp" (.reg "%rcx")
  , .shr "%rbp" (.imm 63)
  , .mov "%rcx" (.reg "%rbp") ]

def tS7 : List (JInstr 64) :=
  [ .loadMem "%rbp" "%rsp" 48
  , .loadMem "%r15" "%rsp" 16
  , .add "%rbp" (.reg "%r15")
  , .mov "%r9" (.reg "%rbp")
  , .add "%r9" (.reg "%rcx")
  , .mov "%rcx" (.reg "%r9")
  , .loadMem "%r14" "%rsp" 120
  , .loadMem "%r15" "%rsp" 8
  , .storeMemIdx "%r14" "%r15" 8 (.reg "%rsi")
  , .loadMem "%r14" "%rsp" 120
  , .loadMem "%r15" "%rsp" 32
  , .storeMemIdx "%r14" "%r15" 8 (.reg "%rcx")
  , .mov "%rbx" (.reg "%rbx")
  , .add "%r10" (.imm 1)
  , .sub "%r11" (.imm 1)
  , .cmp "%r11" (.imm 0) ]

theorem mulInner_eq : mulInner = tS1 ++ tS2 ++ tS3 ++ tS4 ++ tS5 ++ tS6 ++ tS7 := by
  simp only [mulInner, tS1, tS2, tS3, tS4, tS5, tS6, tS7, List.append_assoc, List.cons_append,
    List.nil_append]

theorem tS1_run (sa : AState) :
    (runBlockA sa tS1).regs "%rsi" = 0 - bSltu (sa.regs "%r10") (sa.regs "%rdi")
    ∧ (runBlockA sa tS1).regs "%r12"
        = sa.regs "%r10" &&& (0 - bSltu (sa.regs "%r10") (sa.regs "%rdi"))
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" →
        (runBlockA sa tS1).regs r = sa.regs r)
    ∧ (runBlockA sa tS1).mem = sa.mem := by
  simp only [tS1, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_xor, eA_and, eA_sub,
    eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]
    simp only [BitVec.zero_sub]
    rw [ltu_idiom]
    simp
  · simp only [String.reduceEq, ↓reduceIte]
    simp only [BitVec.zero_sub]
    rw [ltu_idiom]
    simp
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · simp

/-- A word stored at one displacement of a base does not change the word at another
    displacement at least eight bytes away. -/
theorem rd_at_ne (m : AMem) (p v : BitVec 64) (o o' : Int) (h : 8 ≤ (o - o').natAbs)
    (h' : (o - o').natAbs ≤ 2 ^ 64 - 8) :
    read64 (write64 m (at' p o) v) (at' p o') = read64 m (at' p o') :=
  read64_write64_of_disjoint m _ _ v (disjoint8_add_ofInt p o o' h h')

theorem rd_at_same (m : AMem) (p v : BitVec 64) (o : Int) :
    read64 (write64 m (at' p o) v) (at' p o) = v :=
  read64_write64_same m _ v

/-- The loads of the multiplicand limb and the row scalar, the low product, and the high
    product spilled to `48(%rsp)`. -/
theorem tS2_run (sa : AState) (UP VP : BitVec 64)
    (hup : read64 sa.mem (at' (sa.regs "%rsp") 112) = UP)
    (hvp : read64 sa.mem (at' (sa.regs "%rsp") (-8)) = VP) :
    (runBlockA sa tS2).regs "%rsi" = read64 sa.mem (ix UP (sa.regs "%r12")) &&& sa.regs "%rsi"
    ∧ (runBlockA sa tS2).regs "%r13" = (read64 sa.mem (ix UP (sa.regs "%r12")) &&& sa.regs "%rsi")
        * read64 sa.mem (ix VP (sa.regs "%rax"))
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rsi" → r ≠ "%r14" → r ≠ "%r15" →
        (runBlockA sa tS2).regs r = sa.regs r)
    ∧ (runBlockA sa tS2).mem = write64 sa.mem (at' (sa.regs "%rsp") 48)
        (x86_MULX_lo_hi (read64 sa.mem (ix UP (sa.regs "%r12")) &&& sa.regs "%rsi")
          (read64 sa.mem (ix VP (sa.regs "%rax")))).2 := by
  simp only [tS2, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_and, eA_imul, eA_mulx,
    eA_loadMem, eA_loadMemIdx, eA_storeMem, upd_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hup]
  · simp [hup, hvp]
  · intro r h1 h2 h3 h4 h5 h6
    by_cases hd : r = "%rdx"
    · subst hd; simp
    · simp [h1, h2, h3, h4, h5, h6, hd]
  · simp [hup, hvp]

/-- The scratch index `un + vn` spilled to `32(%rsp)` and the carry word `rp[un + vn]`. -/
theorem tS3_run (sa : AState) (VN RP : BitVec 64)
    (hvn : read64 sa.mem (at' (sa.regs "%rsp") 24) = VN)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 120) = RP) :
    (runBlockA sa tS3).regs "%r9"
        = read64 (write64 sa.mem (at' (sa.regs "%rsp") 32) (sa.regs "%rdi" + VN))
            (ix RP (sa.regs "%rdi" + VN))
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%r14" → r ≠ "%r15" → (runBlockA sa tS3).regs r = sa.regs r)
    ∧ (runBlockA sa tS3).mem = write64 sa.mem (at' (sa.regs "%rsp") 32) (sa.regs "%rdi" + VN) := by
  simp only [tS3, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add, eA_loadMem, eA_loadMemIdx,
    eA_storeMem, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp [hvn, rd_at_ne _ _ _ 32 120 (by decide) (by decide), rd_at_same, hrp]
  · intro r h1 h2 h3
    simp [h1, h2, h3]
  · simp [hvn]

/-- The first carry `bSltu (lo + cy) lo`, spilled to `16(%rsp)`; `%r9` holds `lo + cy`. -/
theorem tS4_run (sa : AState) :
    (runBlockA sa tS4).regs "%r9" = sa.regs "%r13" + sa.regs "%r9"
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%rsi" → r ≠ "%rcx" → r ≠ "%r12" → r ≠ "%rbp" → r ≠ "%r15" →
        (runBlockA sa tS4).regs r = sa.regs r)
    ∧ (runBlockA sa tS4).mem = write64 sa.mem (at' (sa.regs "%rsp") 16)
        (bSltu (sa.regs "%r13" + sa.regs "%r9") (sa.regs "%r13")) := by
  simp only [tS4, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_add, eA_xor, eA_and,
    eA_sub, eA_shr63, eA_storeMem, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro r h1 h2 h3 h4 h5 h6
    simp [h1, h2, h3, h4, h5, h6]
  · simp only [String.reduceEq, ↓reduceIte]
    rw [ltu_idiom]

/-- The output index `jd + t` spilled to `8(%rsp)`, the word `rp[jd + t]`, and the second sum. -/
theorem tS5_run (sa : AState) (RP : BitVec 64)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 120) = RP) :
    (runBlockA sa tS5).regs "%rsi"
        = sa.regs "%r9" + read64 (write64 sa.mem (at' (sa.regs "%rsp") 8)
            (sa.regs "%rax" + sa.regs "%r10")) (ix RP (sa.regs "%rax" + sa.regs "%r10"))
    ∧ (∀ r, r ≠ "%rsi" → r ≠ "%r14" → r ≠ "%r15" → r ≠ "%r12" →
        (runBlockA sa tS5).regs r = sa.regs r)
    ∧ (runBlockA sa tS5).mem
        = write64 sa.mem (at' (sa.regs "%rsp") 8) (sa.regs "%rax" + sa.regs "%r10") := by
  simp only [tS5, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add, eA_loadMem, eA_loadMemIdx,
    eA_storeMem, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp [rd_at_ne _ _ _ 8 120 (by decide) (by decide), rd_at_same, hrp]
  · intro r h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  · simp

/-- The second carry `bSltu s2 s1` in `%rcx`. -/
theorem tS6_run (sa : AState) :
    (runBlockA sa tS6).regs "%rcx" = bSltu (sa.regs "%rsi") (sa.regs "%r9")
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%rcx" → r ≠ "%r12" → r ≠ "%r13" → r ≠ "%rbp" →
        (runBlockA sa tS6).regs r = sa.regs r)
    ∧ (runBlockA sa tS6).mem = sa.mem := by
  simp only [tS6, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_mov_imm, eA_xor, eA_and,
    eA_sub, eA_shr63, upd_apply]
  refine ⟨?_, ?_, ?_⟩
  · simp only [String.reduceEq, ↓reduceIte]
    rw [ltu_idiom]
  · intro r h1 h2 h3 h4 h5
    simp [h1, h2, h3, h4, h5]
  · simp

/-- The carry-out `hi + k1 + k2`, the two output stores, the index and count steps. -/
theorem tS7_run (sa : AState) (HI K1 RP PI NC : BitVec 64)
    (hhi : read64 sa.mem (at' (sa.regs "%rsp") 48) = HI)
    (hk1 : read64 sa.mem (at' (sa.regs "%rsp") 16) = K1)
    (hrp : read64 sa.mem (at' (sa.regs "%rsp") 120) = RP)
    (hpi : read64 sa.mem (at' (sa.regs "%rsp") 8) = PI)
    (hnc : read64 sa.mem (at' (sa.regs "%rsp") 32) = NC)
    (hd1 : Disjoint8 (ix RP PI) (at' (sa.regs "%rsp") 120))
    (hd2 : Disjoint8 (ix RP PI) (at' (sa.regs "%rsp") 32)) :
    (runBlockA sa tS7).regs "%r10" = sa.regs "%r10" + 1
    ∧ (runBlockA sa tS7).regs "%r11" = sa.regs "%r11" - 1
    ∧ (∀ r, r ≠ "%r9" → r ≠ "%rcx" → r ≠ "%rbp" → r ≠ "%r14" → r ≠ "%r15" → r ≠ "%r10" →
        r ≠ "%r11" → (runBlockA sa tS7).regs r = sa.regs r)
    ∧ (runBlockA sa tS7).mem = write64 (write64 sa.mem (ix RP PI) (sa.regs "%rsi"))
        (ix RP NC) (HI + K1 + sa.regs "%rcx")
    ∧ (runBlockA sa tS7).view.flagB (·.zf) = decide (sa.regs "%r11" - 1 = 0) := by
  have hsplit : tS7 = tS7.dropLast ++ [.cmp "%r11" (.imm 0)] := rfl
  rw [hsplit, runBlockA_append, runBlockA_cons, runBlockA_nil, cmp0_zf]
  simp only [List.dropLast, tS7, runBlockA_cons, runBlockA_nil, eA_mov_reg, eA_add, eA_add_imm,
    eA_sub_imm, eA_loadMem, eA_storeMemIdx, eA_cmp, upd_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro r h1 h2 h3 h4 h5 h6 h7
    simp only [h1, h2, h3, h4, h5, h6, h7, String.reduceEq, ↓reduceIte]
    split <;> simp_all
  · simp [hhi, hk1, hrp, hpi, read64_write64_of_disjoint _ _ _ _ hd1,
      read64_write64_of_disjoint _ _ _ _ hd2, hnc]
  · simp

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip
