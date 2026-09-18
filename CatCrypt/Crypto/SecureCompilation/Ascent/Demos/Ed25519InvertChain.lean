/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedParts

/-!
# The addition chain of the shipped `ed25519_invert`

`Imported.Ed25519InvertShipped.ed25519InvertShippedBlock` is a `List CallSeg` of 265
calls to `fe25519_sqr` and `fe25519_mul`, the addition chain for `z ^ (p - 2)` modulo
`p = 2 ^ 255 - 19`. Each call takes its arguments from four field slots of the
function's frame, or from the input pointer the function keeps in `%rbx`, and writes one
of those slots. This module carries the step abstraction of such a chain, its callee
specifications, and the invariant that runs it over `Ed25519MaddShippedProof.segsRunA`.

## The abstraction

A `Step` is a square or a multiply with its destination slot and its arguments;
`segOfStep` is the call segment that carries it out. An `Env` records, for each slot, the
exponent of the input the slot holds, absent where the slot has not been written; `stepEnv`
doubles the exponent of a square's argument and adds those of a multiply's two arguments.
`ChainInv` states the machine state matches an environment: `%rsp` at the frame base,
`%rbx` at the input pointer, the output pointer in the slot at `%rsp + 128`, the input
value at the input pointer, and `z ^ e % p` in each slot whose exponent is `e`.

## Main definitions

* `Buf`, `bufOff`, `Src`, `Step`, `srcInstr`, `segOfStep`: the steps and their segments.
* `Env`, `Env.get`, `Env.set`, `srcExp`, `stepEnv`, `runEnv`: the exponents.
* `SqrEffect`, `MulEffect`, `ArgsBelowSep`, `InvertCallees`: the callee specifications.
* `srcAddr`, `ChainSep`, `ChainInv`: the argument addresses, the separation of the input
  buffer from the frame, and the invariant.

## Main results

* `pow_sq_mod`, `pow_mul_mod`, `pow_one_mod`: the exponent arithmetic modulo `pM`.
* `djBufBuf`, `djRedBuf`, `djBufInp`, `djRedInp`, `djBufSlot`, `djRedSlot`,
  `feO_bufSurvives`, `feO_inpSurvives`, `slotSurvives`: what a call writing one slot
  leaves untouched.
* `runSqrBody`, `runMulBody`: the registers and memory each segment body leaves.
* `chainStep`, `chainRun`: the invariant after one step and after a list of steps.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

/-! ## 1. The steps of the chain -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (mulSym sqrSym)

/-- One of the four field slots of the inversion frame. -/
inductive Buf where
  /-- The slot at `%rsp`. -/
  | b0
  /-- The slot at `%rsp + 32`. -/
  | b1
  /-- The slot at `%rsp + 64`. -/
  | b2
  /-- The slot at `%rsp + 96`. -/
  | b3
  deriving DecidableEq, Repr

/-- The byte offset of a field slot from `%rsp`. -/
def bufOff : Buf → Int
  | .b0 => 0
  | .b1 => 32
  | .b2 => 64
  | .b3 => 96

theorem bufOff_mem (b : Buf) :
    bufOff b = 0 ∨ bufOff b = 32 ∨ bufOff b = 64 ∨ bufOff b = 96 := by
  cases b <;> simp [bufOff]

theorem bufOff_ne : ∀ d b : Buf, d ≠ b → bufOff d ≠ bufOff b := by
  intro d b h
  cases d <;> cases b <;> first | exact absurd rfl h | decide

/-- An argument of a call: the function's input, or a field slot of the frame. -/
inductive Src where
  /-- The four-limb value at the function's input pointer. -/
  | inp
  /-- The four-limb value in a field slot. -/
  | buf (b : Buf)
  deriving DecidableEq, Repr

/-- One call of the chain: a square or a multiply, with its destination slot. -/
inductive Step where
  /-- A call to `fe25519_sqr` writing slot `d`. -/
  | sqr (d : Buf) (a : Src)
  /-- A call to `fe25519_mul` writing slot `d`. -/
  | mul (d : Buf) (a b : Src)
  deriving DecidableEq, Repr

/-- The instruction that puts the address of an argument in `r`. -/
def srcInstr (r : String) : Src → JInstr 64
  | .inp => .mov r (.reg "%rbx")
  | .buf b => .lea r "%rsp" "%rsp" 0 (bufOff b)

/-- The call segment of one step. -/
def segOfStep : Step → CallSeg
  | .sqr d a =>
      { body := [.lea "%rdi" "%rsp" "%rsp" 0 (bufOff d), srcInstr "%rsi" a]
        callee := some sqrSym }
  | .mul d a b =>
      { body := [.lea "%rdi" "%rsp" "%rsp" 0 (bufOff d), srcInstr "%rsi" a,
                 srcInstr "%rdx" b]
        callee := some mulSym }

/-- The exponent of the input held in each field slot, absent where the slot has not been
    written. -/
structure Env where
  /-- The exponent in the slot at `%rsp`. -/
  e0 : Option Nat
  /-- The exponent in the slot at `%rsp + 32`. -/
  e1 : Option Nat
  /-- The exponent in the slot at `%rsp + 64`. -/
  e2 : Option Nat
  /-- The exponent in the slot at `%rsp + 96`. -/
  e3 : Option Nat
  deriving DecidableEq, Repr

/-- The exponent in a slot. -/
def Env.get : Env → Buf → Option Nat
  | E, .b0 => E.e0
  | E, .b1 => E.e1
  | E, .b2 => E.e2
  | E, .b3 => E.e3

/-- The environment with the exponent of one slot replaced. -/
def Env.set : Env → Buf → Option Nat → Env
  | E, .b0, v => { E with e0 := v }
  | E, .b1, v => { E with e1 := v }
  | E, .b2, v => { E with e2 := v }
  | E, .b3, v => { E with e3 := v }

theorem Env.get_set_self (E : Env) (b : Buf) (v : Option Nat) : (E.set b v).get b = v := by
  cases b <;> rfl

theorem Env.get_set_of_ne (E : Env) {d b : Buf} (h : d ≠ b) (v : Option Nat) :
    (E.set d v).get b = E.get b := by
  cases d <;> cases b <;> first | exact absurd rfl h | rfl

/-- The exponent of an argument. -/
def srcExp (E : Env) : Src → Option Nat
  | .inp => some 1
  | .buf b => E.get b

/-- The environment after one step: a square doubles the exponent of its argument, a
    multiply adds the exponents of its two arguments. -/
def stepEnv (E : Env) : Step → Env
  | .sqr d a => E.set d ((srcExp E a).map (fun e => 2 * e))
  | .mul d a b => E.set d ((srcExp E a).bind fun e => (srcExp E b).map fun f => e + f)

/-- The environment after a list of steps. -/
def runEnv (E : Env) (steps : List Step) : Env := steps.foldl stepEnv E

@[simp] theorem runEnv_nil (E : Env) : runEnv E [] = E := rfl

theorem runEnv_cons (E : Env) (s : Step) (steps : List Step) :
    runEnv E (s :: steps) = runEnv (stepEnv E s) steps := rfl

/-! ## 2. Powers modulo the prime -/

theorem pow_sq_mod (z e : Nat) : (z ^ e % pM) ^ 2 % pM = z ^ (2 * e) % pM := by
  rw [← Nat.pow_mod, ← pow_mul]
  congr 1
  ring

theorem pow_mul_mod (z e f : Nat) : (z ^ e % pM) * (z ^ f % pM) % pM = z ^ (e + f) % pM := by
  rw [← Nat.mul_mod, ← pow_add]

theorem pow_one_mod {z : Nat} (hz : z < pM) : z ^ 1 % pM = z := by
  rw [pow_one, Nat.mod_eq_of_lt hz]

/-! ## 3. The frame of the chain -/

/-- The cells of the inversion frame, from the words the callees use below `%rsp` to the
    output-pointer slot at `%rsp + 128`, are disjoint from the input buffer. -/
structure ChainSep (SP IP : BitVec 64) : Prop where
  /-- Every aligned frame cell in `[-144, 128]` is disjoint from every limb at `IP`. -/
  si : RangeDisj SP (-144) 128 IP 0 24

theorem djBufBuf (SP : BitVec 64) {d b : Buf} (hdb : d ≠ b) :
    ∀ k, k < 4 → ∀ j ∈ limbOffs,
      Disjoint8 (SP + BitVec.ofInt 64 (bufOff d) + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (SP + BitVec.ofInt 64 (bufOff b + j)) := by
  intro k hk j hj
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rw [addI]
  have hne := bufOff_ne d b hdb
  rcases bufOff_mem d with h | h | h | h <;> rcases bufOff_mem b with h' | h' | h' | h' <;>
    rw [h, h'] at hne ⊢ <;>
    exact djSS _ _ _ (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)

theorem djRedBuf (SP : BitVec 64) (b : Buf) :
    ∀ k, k < 18 → ∀ j ∈ limbOffs,
      Disjoint8 (redBase SP + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (SP + BitVec.ofInt 64 (bufOff b + j)) := by
  intro k hk j hj
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rw [redBase, addI]
  rcases bufOff_mem b with h | h | h | h <;> rw [h] <;>
    exact djSS _ _ _ (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)

theorem djBufInp {SP IP : BitVec 64} (hsep : ChainSep SP IP) (d : Buf) :
    ∀ k, k < 4 → ∀ j ∈ limbOffs,
      Disjoint8 (SP + BitVec.ofInt 64 (bufOff d) + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (IP + BitVec.ofInt 64 (0 + j)) := by
  intro k hk j hj
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rw [addI]
  rcases bufOff_mem d with h | h | h | h <;> rw [h] <;>
    exact hsep.si _ _ (by omega) (by omega) (by omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)

theorem djRedInp {SP IP : BitVec 64} (hsep : ChainSep SP IP) :
    ∀ k, k < 18 → ∀ j ∈ limbOffs,
      Disjoint8 (redBase SP + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (IP + BitVec.ofInt 64 (0 + j)) := by
  intro k hk j hj
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rw [redBase, addI]
  exact hsep.si _ _ (by omega) (by omega) (by omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega)

theorem djBufSlot (SP : BitVec 64) (d : Buf) :
    ∀ k, k < 4 →
      Disjoint8 (SP + BitVec.ofInt 64 (bufOff d) + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (SP + BitVec.ofInt 64 128) := by
  intro k hk
  rw [addI]
  rcases bufOff_mem d with h | h | h | h <;> rw [h] <;>
    exact djSS _ _ _ (by omega) (by omega)

theorem djRedSlot (SP : BitVec 64) :
    ∀ k, k < 18 →
      Disjoint8 (redBase SP + BitVec.ofInt 64 ((8 * k : Nat) : Int))
        (SP + BitVec.ofInt 64 128) := by
  intro k hk
  rw [redBase, addI]
  exact djSS _ _ _ (by omega) (by omega)

/-- A slot other than the one a call writes keeps its value. -/
theorem feO_bufSurvives {m m' : AMem} {SP : BitVec 64} {d b : Buf} (hdb : d ≠ b)
    (hf : FrameCS m m' (SP + BitVec.ofInt 64 (bufOff d)) 4 SP) :
    feO m' SP (bufOff b) = feO m SP (bufOff b) :=
  feO_frameS hf (djBufBuf SP hdb) (djRedBuf SP b)

/-- The input buffer keeps its value across a call writing a slot. -/
theorem feO_inpSurvives {m m' : AMem} {SP IP : BitVec 64} {d : Buf} (hsep : ChainSep SP IP)
    (hf : FrameCS m m' (SP + BitVec.ofInt 64 (bufOff d)) 4 SP) :
    feO m' IP 0 = feO m IP 0 :=
  feO_frameS hf (djBufInp hsep d) (djRedInp hsep)

/-- The output-pointer slot keeps its value across a call writing a slot. -/
theorem slotSurvives {m m' : AMem} {SP : BitVec 64} {d : Buf}
    (hf : FrameCS m m' (SP + BitVec.ofInt 64 (bufOff d)) 4 SP) :
    read64 m' (SP + BitVec.ofInt 64 128) = read64 m (SP + BitVec.ofInt 64 128) :=
  read64_frameCS hf _ (djBufSlot SP d) (djRedSlot SP)

/-! ## 4. The callees of the chain -/

/-- The effect of a square call at one state: the square of the four-limb value at `%rsi`,
    reduced modulo `pM`, at `%rdi`, no memory outside the 32 bytes at `%rdi` and the
    eighteen words below `%rsp`, and `%rsp` and `%rbx` kept. -/
def SqrEffect (C : ACallModel) (f : String) (sa : AState) : Prop :=
  feO (C f sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM
    ∧ FrameCS sa.mem (C f sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
    ∧ (C f sa).regs "%rsp" = sa.regs "%rsp"
    ∧ (C f sa).regs "%rbx" = sa.regs "%rbx"

/-- The effect of a multiply call at one state: the product of the four-limb values at
    `%rsi` and at `%rdx`, reduced modulo `pM`, at `%rdi`, no memory outside the 32 bytes at
    `%rdi` and the eighteen words below `%rsp`, and `%rsp` and `%rbx` kept. -/
def MulEffect (C : ACallModel) (f : String) (sa : AState) : Prop :=
  feO (C f sa).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
    ∧ FrameCS sa.mem (C f sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
    ∧ (C f sa).regs "%rsp" = sa.regs "%rsp"
    ∧ (C f sa).regs "%rbx" = sa.regs "%rbx"

/-- The two argument buffers of a call lie outside the eighteen words below `%rsp`. -/
structure ArgsBelowSep (sa : AState) : Prop where
  /-- The first argument. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The second argument. -/
  js : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-144) (-8)

/-- The two callees of the inversion chain at their specifications. -/
structure InvertCallees (C : ACallModel) : Prop where
  /-- `fe25519_sqr` squares modulo `pM`, at every state. -/
  sqr : ∀ sa, SqrEffect C sqrSym sa
  /-- `fe25519_mul` multiplies modulo `pM`, at every state whose arguments lie outside the
      words below `%rsp`. -/
  mul : ∀ sa, ArgsBelowSep sa → MulEffect C mulSym sa

/-! ## 5. The bodies of the chain's segments -/

/-- The address an argument is read from, at the frame base `SP` and the input `IP`. -/
def srcAddr (SP IP : BitVec 64) : Src → BitVec 64
  | .inp => IP
  | .buf b => SP + BitVec.ofInt 64 (bufOff b)

theorem rangeDisj_narrow {a b : BitVec 64} {lo hi lo' hi' u1 u2 v1 v2 : Int}
    (h : RangeDisj a lo hi b lo' hi') (h1 : lo ≤ u1) (h2 : u2 ≤ hi) (h3 : lo' ≤ v1)
    (h4 : v2 ≤ hi') : RangeDisj a u1 u2 b v1 v2 :=
  fun o o' a1 a2 a3 b1 b2 b3 => h o o' (by omega) (by omega) a3 (by omega) (by omega) b3

/-- An argument buffer lies outside the eighteen words below the frame base. -/
theorem srcBelowSep {SP IP : BitVec 64} (hsep : ChainSep SP IP) (a : Src) :
    RangeDisj (srcAddr SP IP a) 0 24 SP (-144) (-8) := by
  cases a with
  | inp => exact rangeDisj_narrow hsep.si.symm (by omega) (by omega) (by omega) (by omega)
  | buf b =>
    refine rangeDisj_sameBase (p := SP) (d := bufOff b) (e := 0) 0 24 (-144) (-8) rfl
      (eq_add_ofInt_zero SP) fun o o' a1 a2 a3 b1 b2 b3 => ?_
    rcases bufOff_mem b with h | h | h | h <;> rw [h] <;> exact ⟨by omega, by omega⟩

theorem runSqrBody (sa : AState) (d : Buf) (a : Src) :
    let s' := runBlockA sa (segOfStep (.sqr d a)).body
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp" ∧ s'.regs "%rbx" = sa.regs "%rbx"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 (bufOff d)
      ∧ s'.regs "%rsi" = srcAddr (sa.regs "%rsp") (sa.regs "%rbx") a := by
  cases a with
  | inp =>
    refine ⟨rfl, rfl, rfl, ?_, rfl⟩
    show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (bufOff d) = _
    exact leaZero _ _
  | buf b =>
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (bufOff d) = _
      exact leaZero _ _
    · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (bufOff b) = _
      exact leaZero _ _

theorem runMulBody (sa : AState) (d : Buf) (a b : Src) :
    let s' := runBlockA sa (segOfStep (.mul d a b)).body
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp" ∧ s'.regs "%rbx" = sa.regs "%rbx"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 (bufOff d)
      ∧ s'.regs "%rsi" = srcAddr (sa.regs "%rsp") (sa.regs "%rbx") a
      ∧ s'.regs "%rdx" = srcAddr (sa.regs "%rsp") (sa.regs "%rbx") b := by
  have hdi : ∀ e : Buf,
      sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 (bufOff e)
        = sa.regs "%rsp" + BitVec.ofInt 64 (bufOff e) := fun e => leaZero _ _
  cases a with
  | inp =>
    cases b with
    | inp => exact ⟨rfl, rfl, rfl, hdi d, rfl, rfl⟩
    | buf c => exact ⟨rfl, rfl, rfl, hdi d, rfl, hdi c⟩
  | buf c =>
    cases b with
    | inp => exact ⟨rfl, rfl, rfl, hdi d, hdi c, rfl⟩
    | buf c' => exact ⟨rfl, rfl, rfl, hdi d, hdi c, hdi c'⟩

/-! ## 6. The invariant of the chain -/

/-- The state after some steps of the chain: `%rsp` at the frame base, `%rbx` at the input
    pointer, the output pointer in its slot, the input value at the input pointer, and each
    written field slot holding that power of the input modulo `2 ^ 255 - 19`. -/
structure ChainInv (SP IP OP : BitVec 64) (z : Nat) (E : Env) (sa : AState) : Prop where
  /-- The frame base. -/
  rsp : sa.regs "%rsp" = SP
  /-- The input pointer. -/
  rbx : sa.regs "%rbx" = IP
  /-- The output pointer in its slot. -/
  outp : read64 sa.mem (SP + BitVec.ofInt 64 128) = OP
  /-- The input value. -/
  inp : feO sa.mem IP 0 = z
  /-- The power of the input in each written slot. -/
  vals : ∀ b e, E.get b = some e → feO sa.mem SP (bufOff b) = z ^ e % pM

/-- The value an argument holds. -/
theorem srcVal {SP IP OP : BitVec 64} {z : Nat} {E : Env} {sa : AState} (hz : z < pM)
    (hinv : ChainInv SP IP OP z E sa) (a : Src) (e : Nat) (he : srcExp E a = some e) :
    feO sa.mem (srcAddr SP IP a) 0 = z ^ e % pM := by
  cases a with
  | inp =>
    have h1 : (1 : Nat) = e := Option.some.inj he
    subst h1
    rw [show srcAddr SP IP Src.inp = IP from rfl, hinv.inp, pow_one_mod hz]
  | buf b =>
    rw [show srcAddr SP IP (Src.buf b) = SP + BitVec.ofInt 64 (bufOff b) from rfl, feO_base,
      add_zero]
    exact hinv.vals b e he

/-- The invariant after a call writing one slot. -/
theorem chainInv_write {SP IP OP : BitVec 64} {z : Nat} {E : Env} {sa t : AState} {d : Buf}
    {v : Option Nat} (hsep : ChainSep SP IP) (hinv : ChainInv SP IP OP z E sa)
    (hrsp : t.regs "%rsp" = SP) (hrbx : t.regs "%rbx" = IP)
    (hfr : FrameCS sa.mem t.mem (SP + BitVec.ofInt 64 (bufOff d)) 4 SP)
    (hval : ∀ e, v = some e → feO t.mem SP (bufOff d) = z ^ e % pM) :
    ChainInv SP IP OP z (E.set d v) t := by
  refine ⟨hrsp, hrbx, ?_, ?_, ?_⟩
  · rw [slotSurvives hfr]; exact hinv.outp
  · rw [feO_inpSurvives hsep hfr]; exact hinv.inp
  · intro b e hb
    by_cases hdb : d = b
    · subst hdb
      rw [Env.get_set_self] at hb
      exact hval e hb
    · rw [Env.get_set_of_ne _ hdb] at hb
      rw [feO_bufSurvives hdb hfr]
      exact hinv.vals b e hb

/-- **One step of the chain.** -/
theorem chainStep {C : ACallModel} (hC : InvertCallees C) {SP IP OP : BitVec 64} {z : Nat}
    (hz : z < pM) (hsep : ChainSep SP IP) {E : Env} {sa : AState}
    (hinv : ChainInv SP IP OP z E sa) (s : Step) :
    ChainInv SP IP OP z (stepEnv E s) (segsRunA C sa [segOfStep s]) := by
  cases s with
  | sqr d a =>
    obtain ⟨hm, hrsp, hrbx, hrdi, hrsi⟩ := runSqrBody sa d a
    set sb := runBlockA sa (segOfStep (Step.sqr d a)).body with hsb
    obtain ⟨hv, hfr, hcr, hcb⟩ := hC.sqr sb
    rw [hinv.rsp] at hrsp hrdi
    rw [hinv.rsp, hinv.rbx] at hrsi
    rw [hrdi, hrsi, hm] at hv
    rw [hrdi, hrsp, hm] at hfr
    rw [hrsp] at hcr
    rw [hrbx, hinv.rbx] at hcb
    show ChainInv SP IP OP z (E.set d ((srcExp E a).map (fun e => 2 * e))) (C sqrSym sb)
    refine chainInv_write hsep hinv hcr hcb hfr fun e he => ?_
    obtain ⟨ea, hea, rfl⟩ := Option.map_eq_some_iff.1 he
    rw [feO_base, add_zero] at hv
    rw [hv, srcVal hz hinv a ea hea, pow_sq_mod]
  | mul d a b =>
    obtain ⟨hm, hrsp, hrbx, hrdi, hrsi, hrdx⟩ := runMulBody sa d a b
    set sb := runBlockA sa (segOfStep (Step.mul d a b)).body with hsb
    rw [hinv.rsp] at hrsp hrdi
    rw [hinv.rsp, hinv.rbx] at hrsi hrdx
    have hargs : ArgsBelowSep sb := ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep a,
      by rw [hrdx, hrsp]; exact srcBelowSep hsep b⟩
    obtain ⟨hv, hfr, hcr, hcb⟩ := hC.mul sb hargs
    rw [hrdi, hrsi, hrdx, hm] at hv
    rw [hrdi, hrsp, hm] at hfr
    rw [hrsp] at hcr
    rw [hrbx, hinv.rbx] at hcb
    show ChainInv SP IP OP z
      (E.set d ((srcExp E a).bind fun e => (srcExp E b).map fun f => e + f)) (C mulSym sb)
    refine chainInv_write hsep hinv hcr hcb hfr fun e he => ?_
    obtain ⟨ea, hea, he'⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨eb, heb, rfl⟩ := Option.map_eq_some_iff.1 he'
    rw [feO_base, add_zero] at hv
    rw [hv, srcVal hz hinv a ea hea, srcVal hz hinv b eb heb, pow_mul_mod]

/-- **The chain over a list of steps.** -/
theorem chainRun {C : ACallModel} (hC : InvertCallees C) {SP IP OP : BitVec 64} {z : Nat}
    (hz : z < pM) (hsep : ChainSep SP IP) :
    ∀ (steps : List Step) (E : Env) (sa : AState), ChainInv SP IP OP z E sa →
      ChainInv SP IP OP z (runEnv E steps) (segsRunA C sa (steps.map segOfStep)) := by
  intro steps
  induction steps with
  | nil => intro E sa h; exact h
  | cons s rest ih =>
    intro E sa h
    have h1 := chainStep hC hz hsep h s
    have h2 := ih (stepEnv E s) _ h1
    rw [runEnv_cons]
    refine cast (congrArg _ ?_) h2
    show segsRunA C (segsRunA C sa [segOfStep s]) (rest.map segOfStep)
      = segsRunA C sa ((s :: rest).map segOfStep)
    rw [List.map_cons, show (segOfStep s :: rest.map segOfStep)
      = [segOfStep s] ++ rest.map segOfStep from rfl, segsRunA_append]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
