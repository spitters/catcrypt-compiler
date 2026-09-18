/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof

/-!
# The shipped Ed25519 call sequences with their frames

`Ed25519InvertShippedProof.invertCallModel`, `Ed25519LeafCallees.maddCallModel` and
`Ed25519CompressShippedProof.compressCallModel` run each callee's imported block, which the
importer takes from between the function's frame instructions, and set `%rsp` (and, in the
first and last, the callee-saved registers) to their values at the call. The models here
run the callee's frame instructions as well: the return address `ra` pushed, the imported
prologue (`Imported.*Prologue`: each `pushq` and the stack allocation), the block, the
imported epilogue (the release and each `popq`), and the return. `%rsp` and the saved
registers are then restored by those instructions, which `CallFrame.framedCall_popped`
proves; the shipped `fe25519_mul` restores the callee-saved registers from its red zone,
which `mulShipped_saved` proves.

A push writes the stack below the caller's `%rsp`, so each callee specification here
carries the hypothesis that the callee's argument and output buffers lie outside the words
its call writes there (`CallSep`, `SqrSep`, `PackSepF`, `InvSep`).

## Main definitions

* `leafCall`: a call to a straight-line function.
* `sqrCall`, `addCall`, `subCall`, `mulCall`, `joinCall`, `packCall`, `invertCall`: the
  calls of the shipped functions.
* `maddCallModelF`, `invertCallModelF`, `compressCallModelF`: the call models.
* `MaddCalleesF`, `CompressCalleesF`: the callee specifications of the mixed addition and
  the compression under those hypotheses.
* `invertCallModelP`: the model that is `invertCallModelF` at every call meeting those
  hypotheses and `invertCallModel` elsewhere, through which the committed inversion chain
  applies to `invertCallModelF`.

## Main results

* `sqrFrame`, `addFrame`, `subFrame`, `mulFrame`, `joinFrame`, `packFrame`,
  `invertFrame`: the imported prologues and epilogues are `CallFrame.framePro` and
  `CallFrame.frameEpi` of the pushed registers and the allocation.
* `leafCall_frameC`: the frame theorem for a body that changes only the four words at its
  output.
* `mulShipped_saved`: the shipped `fe25519_mul` restores the callee-saved registers.
* `sqrCall_spec`, `addCall_spec`, `subCall_spec`, `mulCall_spec`, `joinCall_spec`,
  `packCall_spec`, `invertCall_spec`: the calls of the shipped functions.
* `maddShippedF_correct`, `invertShippedF_correct`, `compressShippedF_correct`: the
  mixed addition, the inversion and the compression over the framed callees.
-/

@[expose] public section

set_option autoImplicit false

set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519FramedCalls

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (calleeSavedRegs)

/-! ## Calls of straight-line functions -/

/-- A call to a function whose body is the straight-line block `blk`, between the prologue
    `pro` and the epilogue `epi`. -/
def leafCall (pro blk epi : List (JInstr 64)) (ra : BitVec 64) (sa : AState) : AState :=
  framedCall pro epi (fun s => runBlockA s blk) ra sa

/-- The slots a call writes lie among the eighteen words below the caller's `%rsp`. -/
theorem slotAddr_red (sp : BitVec 64) (k : Nat) (hk : k ≤ 17) :
    slotAddr sp k = redBase sp + BitVec.ofInt 64 ((8 * (17 - k) : Nat) : Int) := by
  rw [slotAddr, redBase, addI]
  congr 2
  omega

/-- A byte outside the eighteen words below the caller's `%rsp` is at the start of the body
    as at the call. -/
theorem entered_mem_red {sa E : AState} {rs : List String} {n : Nat} {ra : BitVec 64}
    (h : Entered sa E rs n ra) (hl : rs.length ≤ 16) (x : BitVec 64)
    (hx : ∀ k, k < 18 → ¬ InRange8 (redBase (sa.regs "%rsp") + BitVec.ofInt 64 (8 * k : Nat)) x) :
    E.mem x = sa.mem x :=
  h.mem x fun k hk => by rw [slotAddr_red _ k (by omega)]; exact hx _ (by omega)

/-- A four-limb value outside the eighteen words below the caller's `%rsp` is at the start
    of the body as at the call. -/
theorem entered_feO {sa E : AState} {rs : List String} {n : Nat} {ra : BitVec 64}
    (h : Entered sa E rs n ra) (hl : rs.length ≤ 16) {p : BitVec 64}
    (hp : RangeDisj p 0 24 (sa.regs "%rsp") (-144) (-8)) :
    feO E.mem p 0 = feO sa.mem p 0 := by
  simp only [feO]
  refine congrArg _ (List.map_congr_left fun j hj => h.read64_eq _ fun k hk => ?_)
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  exact (hp (0 + j) (-(8 * ((k : Int) + 1))) (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega) (by omega) (by omega) (by omega)).symm

/-- **A call whose body changes only the four words at `%rdi`.** For pushed registers `rs`,
    at most sixteen, without duplicates and without `%rsp`, a body that keeps `%rsp` and
    changes no byte outside the 32 bytes at the caller's `%rdi`, and an output buffer outside
    the eighteen words below the caller's `%rsp`, the call returns `%rsp` and the registers
    of `rs` at their values at the call and the memory as the body leaves it, and changes no
    byte outside the output and those eighteen words. -/
theorem leafCall_frameC (rs : List String) (n : Nat) (blk : List (JInstr 64))
    (ra : BitVec 64) (sa : AState) (hr : "%rsp" ∉ rs) (hnd : rs.Nodup) (hl : rs.length ≤ 16)
    (hfr : FrameC (entryState (framePro rs n) ra sa).mem
      (runBlockA (entryState (framePro rs n) ra sa) blk).mem (sa.regs "%rdi") 4)
    (hsp : (runBlockA (entryState (framePro rs n) ra sa) blk).regs "%rsp"
      = (entryState (framePro rs n) ra sa).regs "%rsp")
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)) :
    Popped sa (runBlockA (entryState (framePro rs n) ra sa) blk)
        (leafCall (framePro rs n) blk (frameEpi rs n) ra sa) rs
      ∧ FrameCS sa.mem (leafCall (framePro rs n) blk (frameEpi rs n) ra sa).mem
          (sa.regs "%rdi") 4 (sa.regs "%rsp") := by
  have ent := entered rs n ra sa hr (by omega)
  have P := framedCall_popped rs n (fun s => runBlockA s blk) ra sa hr hnd (by omega) hsp
    (fun k hk => read64_frameC hfr _ fun j hj => by
      rw [slotAddr]
      exact ho _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨P, fun x hx hy => ?_⟩
  rw [leafCall, P.mem, hfr x hx]
  exact entered_mem_red ent hl x hy

/-! ## The frames of the shipped functions -/

/-- The registers the shipped `fe25519_sqr` pushes, in order. -/
def sqrSaved : List String := ["%rbx", "%r12", "%r13", "%r14", "%r15", "%rbp"]

/-- The registers the shipped `fe25519_add` and `fe25519_sub` push, in order. -/
def addSaved : List String := ["%rbx", "%r12", "%r13", "%r14", "%r15"]

theorem sqrFrame : Fe25519SqrShipped.fe25519SqrShippedPrologue = framePro sqrSaved 0
    ∧ Fe25519SqrShipped.fe25519SqrShippedEpilogue = frameEpi sqrSaved 0 := ⟨rfl, rfl⟩

theorem addFrame : Fe25519AddShipped.fe25519AddShippedPrologue = framePro addSaved 0
    ∧ Fe25519AddShipped.fe25519AddShippedEpilogue = frameEpi addSaved 0 := ⟨rfl, rfl⟩

theorem subFrame : Fe25519SubShipped.fe25519SubShippedPrologue = framePro addSaved 0
    ∧ Fe25519SubShipped.fe25519SubShippedEpilogue = frameEpi addSaved 0 := ⟨rfl, rfl⟩

theorem mulFrame : Fe25519MulShipped.fe25519MulShippedPrologue = framePro [] 0
    ∧ Fe25519MulShipped.fe25519MulShippedEpilogue = frameEpi [] 0 := ⟨rfl, rfl⟩

theorem joinFrame : Ed25519Join16Shipped.ed25519Join16ShippedPrologue = framePro [] 112
    ∧ Ed25519Join16Shipped.ed25519Join16ShippedEpilogue = frameEpi [] 112 := ⟨rfl, rfl⟩

theorem packFrame : Ed25519PackSignShipped.ed25519PackSignShippedPrologue = framePro [] 64
    ∧ Ed25519PackSignShipped.ed25519PackSignShippedEpilogue = frameEpi [] 64 := ⟨rfl, rfl⟩

theorem invertFrame :
    Ed25519InvertShipped.ed25519InvertShippedPrologue = framePro ["%rbx"] 176
      ∧ Ed25519InvertShipped.ed25519InvertShippedEpilogue = frameEpi ["%rbx"] 176 :=
  ⟨rfl, rfl⟩

/-! ## The red-zone frame of the shipped `fe25519_mul` -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafFrame (framePrologue frameEpilogue) in
/-- **The shipped `fe25519_mul` restores the callee-saved registers.** When its output buffer
    is disjoint from the 48 bytes below `%rsp`, the block ends with each callee-saved
    register at its entry value: the red-zone prologue stores them, the body writes only the
    output, and the red-zone epilogue loads them back. -/
theorem mulShipped_saved (s : AState)
    (ho : RangeDisj (s.regs "%rdi") 0 24 (s.regs "%rsp") (-48) (-8)) :
    ∀ r ∈ calleeSavedRegs,
      (runBlockA s Fe25519MulShipped.fe25519MulShippedBlock).regs r = s.regs r := by
  rw [mulShipped_split, runBlockA_append, runBlockA_append]
  set s1 := runBlockA s framePrologue with hs1
  set s2 := runBlockA s1 mulCore with hs2
  have r1 : ∀ r, s1.regs r = s.regs r := framePrologue_regs s
  obtain ⟨-, hfr, hsp⟩ := mulCore_correct_addr s1
  rw [r1] at hfr hsp
  have m1 : s1.mem = write64 (write64 (write64 (write64 (write64 (write64 s.mem
      (s.regs "%rsp" + BitVec.ofInt 64 (-8)) (s.regs "%rbx"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-16)) (s.regs "%rbp"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-24)) (s.regs "%r12"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-32)) (s.regs "%r13"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-40)) (s.regs "%r14"))
      (s.regs "%rsp" + BitVec.ofInt 64 (-48)) (s.regs "%r15") := by
    rw [hs1]
    simp only [framePrologue, runBlockA_cons, runBlockA_nil, evalInstrA_storeMem]
    rfl
  have m2 : ∀ o : Int, -48 ≤ o → o ≤ -8 → o % 8 = 0 →
      read64 s2.mem (s.regs "%rsp" + BitVec.ofInt 64 o)
        = read64 s1.mem (s.regs "%rsp" + BitVec.ofInt 64 o) := fun o a1 a2 a3 =>
    read64_frameC hfr _ fun k hk => ho _ _ (by omega) (by omega) (by omega) a1 a2 a3
  have w : ∀ (m : AMem) (v : BitVec 64) (a b : Int), 8 ≤ (a - b).natAbs →
      (a - b).natAbs ≤ 2 ^ 64 - 8 →
      read64 (write64 m (s.regs "%rsp" + BitVec.ofInt 64 a) v)
          (s.regs "%rsp" + BitVec.ofInt 64 b)
        = read64 m (s.regs "%rsp" + BitVec.ofInt 64 b) :=
    fun m v a b h h' => read64_write64_of_disjoint _ _ _ _ (djSS _ _ _ h h')
  intro r hr
  simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [frameEpilogue, runBlockA_cons, runBlockA_nil,
      evalInstrA_loadMem, if_true, if_false] <;>
    rw [← hs2] at hsp <;>
    rw [hsp] <;>
    (first
      | rw [m2 (-8) (by omega) (by omega) (by omega)]
      | rw [m2 (-16) (by omega) (by omega) (by omega)]
      | rw [m2 (-24) (by omega) (by omega) (by omega)]
      | rw [m2 (-32) (by omega) (by omega) (by omega)]
      | rw [m2 (-40) (by omega) (by omega) (by omega)]
      | rw [m2 (-48) (by omega) (by omega) (by omega)]) <;>
    rw [m1] <;>
    repeat (first | rw [read64_write64_same] | (rw [w] <;> try decide))

/-! ## The calls of the shipped leaves -/

/-- The two argument buffers and the output buffer of a field call lie outside the eighteen
    words below `%rsp`. -/
structure CallSep (sa : AState) : Prop where
  /-- The first argument. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The second argument. -/
  js : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The output. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)

/-- The argument buffer and the output buffer of a square call lie outside the eighteen
    words below `%rsp`. -/
structure SqrSep (sa : AState) : Prop where
  /-- The argument. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The output. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)

/-- A call to the shipped `fe25519_sqr`: its prologue, block and epilogue. -/
def sqrCall (ra : BitVec 64) : AState → AState :=
  leafCall Fe25519SqrShipped.fe25519SqrShippedPrologue Fe25519SqrShipped.fe25519SqrShippedBlock
    Fe25519SqrShipped.fe25519SqrShippedEpilogue ra

/-- A call to the shipped `fe25519_add`: its prologue, block and epilogue. -/
def addCall (ra : BitVec 64) : AState → AState :=
  leafCall Fe25519AddShipped.fe25519AddShippedPrologue Fe25519AddShipped.fe25519AddShippedBlock
    Fe25519AddShipped.fe25519AddShippedEpilogue ra

/-- A call to the shipped `fe25519_sub`: its prologue, block and epilogue. -/
def subCall (ra : BitVec 64) : AState → AState :=
  leafCall Fe25519SubShipped.fe25519SubShippedPrologue Fe25519SubShipped.fe25519SubShippedBlock
    Fe25519SubShipped.fe25519SubShippedEpilogue ra

/-- A call to the shipped `fe25519_mul`: its prologue, block and epilogue. -/
def mulCall (ra : BitVec 64) : AState → AState :=
  leafCall Fe25519MulShipped.fe25519MulShippedPrologue Fe25519MulShipped.fe25519MulShippedBlock
    Fe25519MulShipped.fe25519MulShippedEpilogue ra

/-- A call to the shipped `ed25519_join16`: its prologue, block and epilogue. -/
def joinCall (ra : BitVec 64) : AState → AState :=
  leafCall Ed25519Join16Shipped.ed25519Join16ShippedPrologue
    Ed25519Join16Shipped.ed25519Join16ShippedBlock Ed25519Join16Shipped.ed25519Join16ShippedEpilogue
    ra

/-- A call to the shipped `ed25519_pack_sign`: its prologue, block and epilogue. -/
def packCall (ra : BitVec 64) : AState → AState :=
  leafCall Ed25519PackSignShipped.ed25519PackSignShippedPrologue
    Ed25519PackSignShipped.ed25519PackSignShippedBlock
    Ed25519PackSignShipped.ed25519PackSignShippedEpilogue ra

/-- **A call to the shipped `fe25519_sqr`.** When its argument and output lie outside the
    eighteen words below `%rsp`, the call leaves the square of the argument modulo
    `2 ^ 255 - 19` at the output, changes no byte outside the output and those words, and
    returns `%rsp` and the six pushed registers at their values at the call. -/
theorem sqrCall_spec (ra : BitVec 64) (sa : AState) (h : SqrSep sa) :
    feO (sqrCall ra sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0 ^ 2 % pM
      ∧ FrameCS sa.mem (sqrCall ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (sqrCall ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ sqrSaved, (sqrCall ra sa).regs r = sa.regs r := by
  have ent := entered sqrSaved 0 ra sa (by decide) (by decide)
  obtain ⟨hv, hfr, hsp⟩ := sqrShipped_correct_addr (entryState (framePro sqrSaved 0) ra sa)
  rw [ent.regs "%rdi" (by decide)] at hv hfr
  rw [ent.regs "%rsi" (by decide), entered_feO ent (by decide) h.is] at hv
  obtain ⟨P, hF⟩ := leafCall_frameC sqrSaved 0 _ ra sa (by decide) (by decide) (by decide) hfr
    hsp h.os
  rw [sqrCall, sqrFrame.1, sqrFrame.2]
  exact ⟨by rw [P.mem]; exact hv, hF, P.rsp, P.saved⟩

/-- **A call to the shipped `fe25519_add`.** When its arguments and output lie outside the
    eighteen words below `%rsp` and both arguments are below `2 ^ 255 - 19`, the call leaves
    their sum modulo that prime at the output; it changes no byte outside the output and
    those words, and returns `%rsp` and the five pushed registers at their values at the
    call. -/
theorem addCall_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (addCall ra sa).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + feO sa.mem (sa.regs "%rdx") 0) % pM)
      ∧ FrameCS sa.mem (addCall ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (addCall ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ addSaved, (addCall ra sa).regs r = sa.regs r := by
  have ent := entered addSaved 0 ra sa (by decide) (by decide)
  obtain ⟨hv, hfr, hsp⟩ := addShipped_correct_addr (entryState (framePro addSaved 0) ra sa)
  rw [ent.regs "%rdi" (by decide)] at hv hfr
  rw [ent.regs "%rsi" (by decide), ent.regs "%rdx" (by decide), entered_feO ent (by decide) h.is,
    entered_feO ent (by decide) h.js] at hv
  obtain ⟨P, hF⟩ := leafCall_frameC addSaved 0 _ ra sa (by decide) (by decide) (by decide) hfr
    hsp h.os
  rw [addCall, addFrame.1, addFrame.2]
  exact ⟨fun h1 h2 => by rw [P.mem]; exact hv h1 h2, hF, P.rsp, P.saved⟩

/-- **A call to the shipped `fe25519_sub`.** When its arguments and output lie outside the
    eighteen words below `%rsp` and both arguments are below `2 ^ 255 - 19`, the call leaves
    their difference modulo that prime at the output; it changes no byte outside the output
    and those words, and returns `%rsp` and the five pushed registers at their values at the
    call. -/
theorem subCall_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
        feO (subCall ra sa).mem (sa.regs "%rdi") 0
          = (feO sa.mem (sa.regs "%rsi") 0 + (pM - feO sa.mem (sa.regs "%rdx") 0)) % pM)
      ∧ FrameCS sa.mem (subCall ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (subCall ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ addSaved, (subCall ra sa).regs r = sa.regs r := by
  have ent := entered addSaved 0 ra sa (by decide) (by decide)
  obtain ⟨hv, hfr, hsp⟩ := subShipped_correct_addr (entryState (framePro addSaved 0) ra sa)
  rw [ent.regs "%rdi" (by decide)] at hv hfr
  rw [ent.regs "%rsi" (by decide), ent.regs "%rdx" (by decide), entered_feO ent (by decide) h.is,
    entered_feO ent (by decide) h.js] at hv
  obtain ⟨P, hF⟩ := leafCall_frameC addSaved 0 _ ra sa (by decide) (by decide) (by decide) hfr
    hsp h.os
  rw [subCall, subFrame.1, subFrame.2]
  exact ⟨fun h1 h2 => by rw [P.mem]; exact hv h1 h2, hF, P.rsp, P.saved⟩

/-- **A call to the shipped `fe25519_mul`.** When its arguments and output lie outside the
    eighteen words below `%rsp`, the call leaves the product of the arguments modulo
    `2 ^ 255 - 19` at the output, changes no byte outside the output and those words, and
    returns `%rsp` and the six callee-saved registers at their values at the call; the
    block saves and restores them in its red zone. An argument may coincide with the
    output. -/
theorem mulCall_spec (ra : BitVec 64) (sa : AState) (h : CallSep sa) :
    feO (mulCall ra sa).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 * feO sa.mem (sa.regs "%rdx") 0 % pM
      ∧ FrameCS sa.mem (mulCall ra sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
      ∧ (mulCall ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ r ∈ calleeSavedRegs, (mulCall ra sa).regs r = sa.regs r := by
  have ent := entered [] 0 ra sa (by simp) (by simp)
  have hEsp : (entryState (framePro [] 0) ra sa).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by
    rw [ent.rsp]; congr 2
  have hred : ∀ o : Int, (-48 : Int) ≤ o → o ≤ -8 → o % 8 = 0 →
      (-144 : Int) ≤ -8 + o ∧ -8 + o ≤ -8 ∧ (-8 + o) % 8 = 0 :=
    fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩
  obtain ⟨hv, hf, hsp⟩ := mulShipped_alias_addr (entryState (framePro [] 0) ra sa)
    (by rw [ent.regs "%rsi" (by decide), hEsp]; exact rangeDisj_frame (-8) h.is hred)
    (by rw [ent.regs "%rdx" (by decide), hEsp]; exact rangeDisj_frame (-8) h.js hred)
  have hsaved := mulShipped_saved (entryState (framePro [] 0) ra sa)
    (by rw [ent.regs "%rdi" (by decide), hEsp]; exact rangeDisj_frame (-8) h.os hred)
  rw [ent.regs "%rdi" (by decide), ent.regs "%rsi" (by decide), ent.regs "%rdx" (by decide),
    entered_feO ent (by decide) h.is, entered_feO ent (by decide) h.js] at hv
  rw [ent.regs "%rdi" (by decide), hEsp] at hf
  have P := framedCall_popped [] 0 (fun s => runBlockA s Fe25519MulShipped.fe25519MulShippedBlock)
    ra sa (by simp) (by simp) (by simp) hsp (fun k hk => absurd hk (by simp))
  rw [mulCall, mulFrame.1, mulFrame.2, leafCall]
  refine ⟨by rw [P.mem]; exact hv, fun x hx hy => ?_, P.rsp, fun r hr => ?_⟩
  · rw [P.mem, hf x hx fun i hi => ?_]
    · exact entered_mem_red ent (by decide) x hy
    · have h2 := hy (16 - i) (by omega)
      rw [redBase, addI, show (-144 : Int) + ((8 * (16 - i) : Nat) : Int)
        = -8 + (-(8 * (i + 1) : Nat) : Int) from by omega, ← addI] at h2
      exact h2
  · have hr0 : r ≠ "%rsp" := by
      simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P.other r (by simp) hr0, hsaved r hr, ent.regs r hr0]

/-- **A call to the shipped `ed25519_join16`.** When its buffers and the eighteen words
    below `%rsp` are pairwise disjoint, the call leaves the four input field elements in the
    four consecutive field slots at the output, changes no byte outside the 128 bytes there
    and those eighteen words, and returns `%rsp` at its value at the call. -/
theorem joinCall_spec (ra : BitVec 64) (sa : AState) (hsp : JoinSep sa) :
    (feO (joinCall ra sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0
      ∧ feO (joinCall ra sa).mem (sa.regs "%rdi") 32 = feO sa.mem (sa.regs "%rdx") 0
      ∧ feO (joinCall ra sa).mem (sa.regs "%rdi") 64 = feO sa.mem (sa.regs "%rcx") 0
      ∧ feO (joinCall ra sa).mem (sa.regs "%rdi") 96 = feO sa.mem (sa.regs "%r8") 0)
      ∧ FrameCS sa.mem (joinCall ra sa).mem (sa.regs "%rdi") 16 (sa.regs "%rsp")
      ∧ (joinCall ra sa).regs "%rsp" = sa.regs "%rsp" := by
  have ent := entered [] 112 ra sa (by simp) (by simp)
  have hEsp : (entryState (framePro [] 112) ra sa).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-120) := by
    rw [ent.rsp]; congr 2
  have er : ∀ r : String, r ≠ "%rsp" →
      (entryState (framePro [] 112) ra sa).regs r = sa.regs r := ent.regs
  have hstk : ∀ o : Int, (-24 : Int) ≤ o → o ≤ 104 → o % 8 = 0 →
      (-144 : Int) ≤ -120 + o ∧ -120 + o ≤ -8 ∧ (-120 + o) % 8 = 0 :=
    fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩
  have hsep := separated_joinCells (R := (entryState (framePro [] 112) ra sa).regs)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o1)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o2)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o3)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o4)
    (by rw [er _ (by decide), hEsp]; exact rangeDisj_frame (-120) hsp.os hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a12)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a13)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a14)
    (by rw [er _ (by decide), hEsp]; exact rangeDisj_frame (-120) hsp.a1s hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a23)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a24)
    (by rw [er _ (by decide), hEsp]; exact rangeDisj_frame (-120) hsp.a2s hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a34)
    (by rw [er _ (by decide), hEsp]; exact rangeDisj_frame (-120) hsp.a3s hstk)
    (by rw [er _ (by decide), hEsp]; exact rangeDisj_frame (-120) hsp.a4s hstk)
  obtain ⟨⟨v0, v1, v2, v3⟩, hf, hs⟩ :=
    joinShipped_correct_addr (entryState (framePro [] 112) ra sa) hsep
  rw [er "%rdi" (by decide)] at v0 v1 v2 v3 hf
  rw [er "%rsi" (by decide), entered_feO ent (by simp) hsp.a1s] at v0
  rw [er "%rdx" (by decide), entered_feO ent (by simp) hsp.a2s] at v1
  rw [er "%rcx" (by decide), entered_feO ent (by simp) hsp.a3s] at v2
  rw [er "%r8" (by decide), entered_feO ent (by simp) hsp.a4s] at v3
  rw [hEsp] at hf
  have P := framedCall_popped [] 112
    (fun s => runBlockA s Ed25519Join16Shipped.ed25519Join16ShippedBlock) ra sa (by simp)
    (by simp) (by simp) hs (fun k hk => absurd hk (by simp))
  rw [joinCall, joinFrame.1, joinFrame.2, leafCall]
  refine ⟨⟨by rw [P.mem]; exact v0, by rw [P.mem]; exact v1, by rw [P.mem]; exact v2,
    by rw [P.mem]; exact v3⟩, fun x hx hy => ?_, P.rsp⟩
  rw [P.mem, hf x hx fun o ho => ?_]
  · exact entered_mem_red ent (by simp) x hy
  · have key : ∀ (u : Int) (k : Nat), k < 18 →
        (-120 : Int) + u = (-144 : Int) + ((8 * k : Nat) : Int) →
        ¬ InRange8 (sa.regs "%rsp" + BitVec.ofInt 64 (-120) + BitVec.ofInt 64 u) x := by
      intro u k hk he
      rw [addI, he]
      have h2 := hy k hk
      rw [redBase, addI] at h2
      exact h2
    simp only [joinRspOffs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact key _ 16 (by omega) (by omega)
    · exact key _ 15 (by omega) (by omega)
    · exact key _ 14 (by omega) (by omega)
    · exact key _ 13 (by omega) (by omega)
    · exact key _ 12 (by omega) (by omega)
    · exact key _ 11 (by omega) (by omega)
    · exact key _ 10 (by omega) (by omega)
    · exact key _ 9 (by omega) (by omega)
    · exact key _ 2 (by omega) (by omega)
    · exact key _ 1 (by omega) (by omega)
    · exact key _ 0 (by omega) (by omega)
    · exact key _ 8 (by omega) (by omega)
    · exact key _ 7 (by omega) (by omega)
    · exact key _ 6 (by omega) (by omega)
    · exact key _ 5 (by omega) (by omega)
    · exact key _ 4 (by omega) (by omega)
    · exact key _ 3 (by omega) (by omega)

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof
  (PackSep rangeDisj_shift)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignLeaf

/-- The buffers of a pack call are those of `PackSep`, and the two input buffers are also
    disjoint from the return-address slot eight bytes below `%rsp`. -/
structure PackSepF (sa : AState) : Prop where
  /-- The buffers and the stack slots of the block. -/
  sep : PackSep sa
  /-- The first input and the return-address slot. -/
  ir : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-8) (-8)
  /-- The second input and the return-address slot. -/
  dr : RangeDisj (sa.regs "%rdx") 0 0 (sa.regs "%rsp") (-8) (-8)

/-- **A call to the shipped `ed25519_pack_sign`.** When its buffers are pairwise disjoint
    and disjoint from its stack slots and the return-address slot, the call copies the four
    words at `%rsi` to `%rdi` and adds the low bit of the word at `%rdx` into the top bit of
    the fourth. -/
theorem packCall_spec (ra : BitVec 64) (sa : AState) (h : PackSepF sa) :
    (∀ j ∈ [(0 : Int), 8, 16],
        read64 (packCall ra sa).mem (sa.regs "%rdi" + BitVec.ofInt 64 j)
          = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 j))
      ∧ read64 (packCall ra sa).mem (sa.regs "%rdi" + BitVec.ofInt 64 24)
        = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 24)
          + (read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 0) &&& 1) <<< 63 := by
  have ent := entered [] 64 ra sa (by simp) (by simp)
  have hEsp : (entryState (framePro [] 64) ra sa).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-72) := by
    rw [ent.rsp]; congr 2
  have er : ∀ r : String, r ≠ "%rsp" →
      (entryState (framePro [] 64) ra sa).regs r = sa.regs r := ent.regs
  have hs : Separated shippedBank (entryState (framePro [] 64) ra sa).regs packCells := by
    refine separated_packCells ?_ ?_ ?_ ?_ ?_ ?_
    · rw [er _ (by decide), er _ (by decide)]; exact h.sep.oi
    · rw [er _ (by decide), er _ (by decide)]; exact h.sep.od
    · rw [er _ (by decide), er _ (by decide)]; exact h.sep.id
    · rw [er _ (by decide), hEsp]; exact rangeDisj_shift (-72) (by decide) h.sep.os
    · rw [er _ (by decide), hEsp]; exact rangeDisj_shift (-72) (by decide) h.sep.is
    · rw [er _ (by decide), hEsp]; exact rangeDisj_shift (-72) (by decide) h.sep.ds
  obtain ⟨h0, h24, -, hsp⟩ :=
    packSignShipped_correct_addr (entryState (framePro [] 64) ra sa) hs
  rw [er "%rdi" (by decide), er "%rsi" (by decide)] at h0 h24
  rw [er "%rdx" (by decide)] at h24
  have hin : ∀ (p : BitVec 64) (lo hi : Int), RangeDisj p lo hi (sa.regs "%rsp") (-8) (-8) →
      ∀ j : Int, lo ≤ j → j ≤ hi → j % 8 = 0 →
      read64 (entryState (framePro [] 64) ra sa).mem (p + BitVec.ofInt 64 j)
        = read64 sa.mem (p + BitVec.ofInt 64 j) := by
    intro p lo hi hp j a1 a2 a3
    refine ent.read64_eq _ fun k hk => ?_
    obtain rfl : k = 0 := by simp at hk; omega
    rw [slotAddr_zero]
    exact (hp j (-8) a1 a2 a3 (by omega) (by omega) (by omega)).symm
  have P := framedCall_popped [] 64
    (fun s => runBlockA s Ed25519PackSignShipped.ed25519PackSignShippedBlock) ra sa (by simp)
    (by simp) (by simp) hsp (fun k hk => absurd hk (by simp))
  rw [packCall, packFrame.1, packFrame.2, leafCall]
  refine ⟨fun j hj => ?_, ?_⟩
  · have hj' : j = 0 ∨ j = 8 ∨ j = 16 := by simpa using hj
    rw [P.mem, h0 j hj, hin _ 0 24 h.ir j (by omega) (by omega) (by omega)]
  · rw [P.mem, h24, hin _ 0 24 h.ir 24 (by omega) (by omega) (by omega),
      hin _ 0 0 h.dr 0 (by omega) (by omega) (by omega)]

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-! ## The call model -/

/-- The call model of the shipped mixed addition in which each callee runs its shipped
    prologue, block and epilogue after the return address `ra` is pushed, and returns. -/
def maddCallModelF (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = addSym then addCall ra sa
  else if f = subSym then subCall ra sa
  else if f = mulSym then mulCall ra sa
  else if f = join16Sym then joinCall ra sa
  else sa

theorem maddCallModelF_addSym (ra : BitVec 64) (sa : AState) :
    maddCallModelF ra addSym sa = addCall ra sa := by simp [maddCallModelF]

theorem maddCallModelF_subSym (ra : BitVec 64) (sa : AState) :
    maddCallModelF ra subSym sa = subCall ra sa := by
  simp [maddCallModelF, addSym, subSym]

theorem maddCallModelF_mulSym (ra : BitVec 64) (sa : AState) :
    maddCallModelF ra mulSym sa = mulCall ra sa := by
  simp [maddCallModelF, addSym, subSym, mulSym]

theorem maddCallModelF_joinSym (ra : BitVec 64) (sa : AState) :
    maddCallModelF ra join16Sym sa = joinCall ra sa := by
  simp [maddCallModelF, addSym, subSym, mulSym, join16Sym]

/-- The four callees of the mixed addition at their specifications, the adder and the
    subtracter at every state whose arguments and output lie outside the eighteen words
    below `%rsp`. -/
structure MaddCalleesF (C : ACallModel) : Prop where
  /-- `fe25519_add` adds modulo `pM`. -/
  add : ∀ sa, CallSep sa → FieldEffect C addSym (fun x y => x + y) sa
  /-- `fe25519_sub` subtracts modulo `pM`. -/
  sub : ∀ sa, CallSep sa → FieldEffect C subSym (fun x y => x + (pM - y)) sa
  /-- `fe25519_mul` multiplies modulo `pM`. -/
  mul : FieldCalleeSep C mulSym fun x y => x * y
  /-- `ed25519_join16` concatenates four field elements. -/
  join : JoinCallee C join16Sym

/-- **The four shipped callees, framed, meet the specifications of the mixed addition.** -/
theorem maddCalleesF_maddCallModelF (ra : BitVec 64) : MaddCalleesF (maddCallModelF ra) := by
  refine ⟨fun sa h => ?_, fun sa h => ?_, fun sa h => ?_, fun sa h => ?_⟩
  · obtain ⟨hv, hf, hr, -⟩ := addCall_spec ra sa h
    unfold FieldEffect
    rw [maddCallModelF_addSym]
    exact ⟨hv, hf, hr⟩
  · obtain ⟨hv, hf, hr, -⟩ := subCall_spec ra sa h
    unfold FieldEffect
    rw [maddCallModelF_subSym]
    exact ⟨hv, hf, hr⟩
  · obtain ⟨hv, hf, hr, -⟩ := mulCall_spec ra sa ⟨h.is, h.js, h.os⟩
    unfold FieldEffect
    rw [maddCallModelF_mulSym]
    exact ⟨fun _ _ => hv, hf, hr⟩
  · obtain ⟨hv, hf, hr⟩ := joinCall_spec ra sa h
    unfold JoinEffect
    rw [maddCallModelF_joinSym]
    exact ⟨hv, hf, hr⟩

/-! ## The separation at the adder and subtracter calls -/

/-- The buffers of a call whose two arguments are at the input pointer lie outside the
    eighteen words below `%rsp`; the two arguments may coincide. -/
theorem argsRR {SP P : BitVec 64} {s : AState} (hrsp : s.regs "%rsp" = SP)
    (hin : inPtr s = P) (hX : CrossIn SP P) (d o1 o2 : Int)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 448) (hd32 : d % 32 = 0)
    (ha0 : 0 ≤ o1) (ha1 : o1 ≤ 192) (ha32 : o1 % 32 = 0)
    (hb0 : 0 ≤ o2) (hb1 : o2 ≤ 192) (hb32 : o2 % 32 = 0) :
    CallSep (runBlockA s
      [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
       .lea "%rsi" "%r10" "%r10" 0 o1, .lea "%rdx" "%r10" "%r10" 0 o2]) := by
  obtain ⟨-, hsp, hdi, hsi, hdx⟩ := runArgsRR s d o1 o2
  rw [hrsp] at hsp hdi
  rw [hin] at hsi hdx
  have hz := hsp.trans (eq_add_ofInt_zero SP)
  have hR := crossIn_rangeDisj hX
  exact
    { is := rangeDisj_twoBase 0 24 (-144) (-8) hR.symm hsi hz
        (fun o c1 c2 c3 => ⟨by omega, by omega, by omega⟩)
        (fun o c1 c2 c3 => ⟨by omega, by omega, by omega⟩)
      js := rangeDisj_twoBase 0 24 (-144) (-8) hR.symm hdx hz
        (fun o c1 c2 c3 => ⟨by omega, by omega, by omega⟩)
        (fun o c1 c2 c3 => ⟨by omega, by omega, by omega⟩)
      os := rangeDisj_sameBase 0 24 (-144) (-8) hdi hz
        (by intro o o' a1 a2 a3 b1 b2 b3; omega) }

/-- The buffers of a call whose two arguments are intermediate slots lie outside the
    eighteen words below `%rsp`. -/
theorem argsSS {SP : BitVec 64} {s : AState} (hrsp : s.regs "%rsp" = SP) (d o1 o2 : Int)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 448) (ha0 : 0 ≤ o1) (ha1 : o1 ≤ 448) (hb0 : 0 ≤ o2)
    (hb1 : o2 ≤ 448) :
    CallSep (runBlockA s
      [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
       .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%rsp" "%rsp" 0 o2]) := by
  obtain ⟨-, hsp, hdi, hsi, hdx⟩ := runArgsSS s d o1 o2
  rw [hrsp] at hsp hdi hsi hdx
  have hz := hsp.trans (eq_add_ofInt_zero SP)
  exact
    { is := rangeDisj_sameBase 0 24 (-144) (-8) hsi hz (by intro o o' a1 a2 a3 b1 b2 b3; omega)
      js := rangeDisj_sameBase 0 24 (-144) (-8) hdx hz (by intro o o' a1 a2 a3 b1 b2 b3; omega)
      os := rangeDisj_sameBase 0 24 (-144) (-8) hdi hz
        (by intro o o' a1 a2 a3 b1 b2 b3; omega) }

/-! ## The fifteen calls -/

/-- After the fifteen calls, over callees meeting `MaddCalleesF`, the result block at
    `%rsp + 448` holds the four coordinates of the mixed addition and the output pointer is
    still in its slot. -/
theorem maddCallsRunF {C : ACallModel} (hC : MaddCalleesF C) (sa : AState)
    (hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi"))
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    ∃ s : AState,
      segsRunA C sa ed25519MaddShippedBlock = segsRunA C s (maddTail 16)
        ∧ s.regs "%rsp" = sa.regs "%rsp"
        ∧ read64 s.mem (sa.regs "%rsp" + BitVec.ofInt 64 584) = sa.regs "%rdi"
        ∧ feO s.mem (sa.regs "%rsp") 448 = maddSV sa 10
        ∧ feO s.mem (sa.regs "%rsp") 480 = maddSV sa 11
        ∧ feO s.mem (sa.regs "%rsp") 512 = maddSV sa 12
        ∧ feO s.mem (sa.regs "%rsp") 544 = maddSV sa 13 := by
  obtain ⟨hadd, hsub, hmul, hjoin⟩ := hC
  obtain ⟨s0, hs0⟩ : ∃ s, runBlockA sa (mg 0).body = s := ⟨_, rfl⟩
  have i0 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 0 s0 := by rw [← hs0]; exact maddEntry sa hX _
  obtain ⟨s1, hs1⟩ : ∃ s, C addSym (runBlockA s0 (mg 1).body) = s := ⟨_, rfl⟩
  have i1 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 1 s1 := by
    rw [← hs1]
    exact stepRR (by omega) hX i0 0 32 0 1 0 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hadd _ (argsRR i0.rsp (inPtr_eq i0) hX 0 32 0 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (hb 1 (by omega)) (hb 0 (by omega)) rfl
  obtain ⟨s2, hs2⟩ : ∃ s, C mulSym (runBlockA s1 (mg 2).body) = s := ⟨_, rfl⟩
  have i2 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 2 s2 := by
    rw [← hs2]
    exact stepSR (by omega) hX i1 32 0 128 0 4 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSR i1.rsp (inPtr_eq i1) hX 32 0 128 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (maddSV_lt sa 0) (hb 4 (by omega)) rfl
  obtain ⟨s3, hs3⟩ : ∃ s, C subSym (runBlockA s2 (mg 3).body) = s := ⟨_, rfl⟩
  have i3 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 3 s3 := by
    rw [← hs3]
    exact stepRR (by omega) hX i2 64 32 0 1 0 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hsub _ (argsRR i2.rsp (inPtr_eq i2) hX 64 32 0 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (hb 1 (by omega)) (hb 0 (by omega)) rfl
  obtain ⟨s4, hs4⟩ : ∃ s, C mulSym (runBlockA s3 (mg 4).body) = s := ⟨_, rfl⟩
  have i4 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 4 s4 := by
    rw [← hs4]
    exact stepSR (by omega) hX i3 96 64 160 2 5 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSR i3.rsp (inPtr_eq i3) hX 96 64 160 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (maddSV_lt sa 2) (hb 5 (by omega)) rfl
  obtain ⟨s5, hs5⟩ : ∃ s, C mulSym (runBlockA s4 (mg 5).body) = s := ⟨_, rfl⟩
  have i5 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 5 s5 := by
    rw [← hs5]
    exact stepRR (by omega) hX i4 128 96 192 3 6 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepRR i4.rsp (inPtr_eq i4) hX 128 96 192 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (hb 3 (by omega)) (hb 6 (by omega)) rfl
  obtain ⟨s6, hs6⟩ : ∃ s, C addSym (runBlockA s5 (mg 6).body) = s := ⟨_, rfl⟩
  have i6 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 6 s6 := by
    rw [← hs6]
    exact stepRR (by omega) hX i5 160 64 64 2 2 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hadd _ (argsRR i5.rsp (inPtr_eq i5) hX 160 64 64 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
      (hb 2 (by omega)) (hb 2 (by omega)) rfl
  obtain ⟨s7, hs7⟩ : ∃ s, C subSym (runBlockA s6 (mg 7).body) = s := ⟨_, rfl⟩
  have i7 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 7 s7 := by
    rw [← hs7]
    exact stepSS (by omega) hX i6 192 32 96 1 3 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hsub _ (argsSS i6.rsp 192 32 96 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
      (maddSV_lt sa 1) (maddSV_lt sa 3) rfl
  obtain ⟨s8, hs8⟩ : ∃ s, C addSym (runBlockA s7 (mg 8).body) = s := ⟨_, rfl⟩
  have i8 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 8 s8 := by
    rw [← hs8]
    exact stepSS (by omega) hX i7 224 32 96 1 3 (by simp [slotOff]) (by omega) (by omega)
      (by simp [slotOff]) (by simp [slotOff])
      (hadd _ (argsSS i7.rsp 224 32 96 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
      (maddSV_lt sa 1) (maddSV_lt sa 3) rfl
  obtain ⟨s9, hs9⟩ : ∃ s, C addSym (runBlockA s8 (mg 9).body) = s := ⟨_, rfl⟩
  have i9 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 9 s9 := by
    rw [← hs9]
    exact stepSS (by omega) hX i8 256 160 128 5 4 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hadd _ (argsSS i8.rsp 256 160 128 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
      (maddSV_lt sa 5) (maddSV_lt sa 4) rfl
  obtain ⟨s10, hs10⟩ : ∃ s, C subSym (runBlockA s9 (mg 10).body) = s := ⟨_, rfl⟩
  have i10 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 10 s10 := by
    rw [← hs10]
    exact stepSS (by omega) hX i9 288 160 128 5 4 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hsub _ (argsSS i9.rsp 288 160 128 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)))
      (maddSV_lt sa 5) (maddSV_lt sa 4) rfl
  obtain ⟨s11, hs11⟩ : ∃ s, C mulSym (runBlockA s10 (mg 11).body) = s := ⟨_, rfl⟩
  have i11 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 11 s11 := by
    rw [← hs11]
    exact stepSS (by omega) hX i10 320 192 288 6 9 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSS i10.rsp 320 192 288 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)))
      (maddSV_lt sa 6) (maddSV_lt sa 9) rfl
  obtain ⟨s12, hs12⟩ : ∃ s, C mulSym (runBlockA s11 (mg 12).body) = s := ⟨_, rfl⟩
  have i12 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 12 s12 := by
    rw [← hs12]
    exact stepSS (by omega) hX i11 352 224 256 7 8 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSS i11.rsp 352 224 256 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)))
      (maddSV_lt sa 7) (maddSV_lt sa 8) rfl
  obtain ⟨s13, hs13⟩ : ∃ s, C mulSym (runBlockA s12 (mg 13).body) = s := ⟨_, rfl⟩
  have i13 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 13 s13 := by
    rw [← hs13]
    exact stepSS (by omega) hX i12 384 256 288 8 9 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSS i12.rsp 384 256 288 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)))
      (maddSV_lt sa 8) (maddSV_lt sa 9) rfl
  obtain ⟨s14, hs14⟩ : ∃ s, C mulSym (runBlockA s13 (mg 14).body) = s := ⟨_, rfl⟩
  have i14 : MaddInv (sa.regs "%rsp") (sa.regs "%rsi") (sa.regs "%rdi") (maddSV sa)
      (maddIn sa) 14 s14 := by
    rw [← hs14]
    exact stepSS (by omega) hX i13 416 192 224 6 7 (by simp [slotOff]) (by omega)
      (by omega) (by simp [slotOff]) (by simp [slotOff])
      (hmul _ (sepSS i13.rsp 416 192 224 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)))
      (maddSV_lt sa 6) (maddSV_lt sa 7) rfl
  obtain ⟨s15, hs15⟩ : ∃ s, C join16Sym (runBlockA s14 (mg 15).body) = s := ⟨_, rfl⟩
  obtain ⟨hj0, hj1, hj2, hj3, hj4, hj5⟩ : (C join16Sym (runBlockA s14 (mg 15).body)).regs "%rsp"
        = sa.regs "%rsp"
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 448 = maddSV sa 10
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 480 = maddSV sa 11
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 512 = maddSV sa 12
      ∧ feO (C join16Sym (runBlockA s14 (mg 15).body)).mem (sa.regs "%rsp") 544 = maddSV sa 13
      ∧ read64 (C join16Sym (runBlockA s14 (mg 15).body)).mem
          (sa.regs "%rsp" + BitVec.ofInt 64 584) = sa.regs "%rdi" := by
    obtain ⟨hm, hsp, hdi, hsi, hdx, hcx, hr8⟩ := runArgsJoin s14 448 320 352 384 416
    rw [i14.rsp] at hsp hdi hsi hdx hcx hr8
    exact joinStep i14 (hjoin _ (sepJoinCall i14.rsp)) hm hsp hdi hsi hdx hcx hr8
  refine ⟨s15, ?_, by rw [← hs15]; exact hj0, by rw [← hs15]; exact hj5,
    by rw [← hs15]; exact hj1, by rw [← hs15]; exact hj2, by rw [← hs15]; exact hj3,
    by rw [← hs15]; exact hj4⟩
  rw [← maddTail_zero, segsRunA_tail_plain C sa 0 (by omega) rfl, hs0,
    segsRunA_tail_call C s0 1 (by omega) addSym rfl, hs1,
    segsRunA_tail_call C s1 2 (by omega) mulSym rfl, hs2,
    segsRunA_tail_call C s2 3 (by omega) subSym rfl, hs3,
    segsRunA_tail_call C s3 4 (by omega) mulSym rfl, hs4,
    segsRunA_tail_call C s4 5 (by omega) mulSym rfl, hs5,
    segsRunA_tail_call C s5 6 (by omega) addSym rfl, hs6,
    segsRunA_tail_call C s6 7 (by omega) subSym rfl, hs7,
    segsRunA_tail_call C s7 8 (by omega) addSym rfl, hs8,
    segsRunA_tail_call C s8 9 (by omega) addSym rfl, hs9,
    segsRunA_tail_call C s9 10 (by omega) subSym rfl, hs10,
    segsRunA_tail_call C s10 11 (by omega) mulSym rfl, hs11,
    segsRunA_tail_call C s11 12 (by omega) mulSym rfl, hs12,
    segsRunA_tail_call C s12 13 (by omega) mulSym rfl, hs13,
    segsRunA_tail_call C s13 14 (by omega) mulSym rfl, hs14,
    segsRunA_tail_call C s14 15 (by omega) join16Sym rfl, hs15]

/-- **The shipped `ed25519_madd` over callees meeting `MaddCalleesF`.** For a state whose
    input point, output buffer and stack frame occupy pairwise disjoint eight-byte cells and
    whose seven input coordinates are below `2 ^ 255 - 19`, the four field elements at the
    output pointer after the block are the four coordinates of `maddSpecN` on those
    inputs. -/
theorem maddShippedF_correct_addr {C : ACallModel} (hC : MaddCalleesF C) (sa : AState)
    (hsep : Separated shippedBank sa.regs maddCells)
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 := by
  have hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi") :=
    fun o o' a b c d e f => djIS hsep o o' a b c d e f
  have hO : CrossOut (sa.regs "%rsp") (sa.regs "%rdi") :=
    fun o o' a b c d e f => djOS hsep o o' a b c d e f
  obtain ⟨s, hrun, hsp, hq, v10, v11, v12, v13⟩ := maddCallsRunF hC sa hX hb
  rw [hrun, maddTailCopy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [maddOutVal hO s hsp hq 0 (by omega), show (448 : Int) + slotOff 0 = 448 by simp [slotOff]]
    exact v10
  · rw [maddOutVal hO s hsp hq 1 (by omega), show (448 : Int) + slotOff 1 = 480 by simp [slotOff]]
    exact v11
  · rw [maddOutVal hO s hsp hq 2 (by omega), show (448 : Int) + slotOff 2 = 512 by simp [slotOff]]
    exact v12
  · rw [maddOutVal hO s hsp hq 3 (by omega), show (448 : Int) + slotOff 3 = 544 by simp [slotOff]]
    exact v13

/-- **The shipped `ed25519_madd` computes the mixed addition over the framed shipped
    callees.** Each callee runs its shipped prologue, block and epilogue after the return
    address `ra` is pushed; `%rsp` and the pushed registers are restored by the shipped
    `popq` instructions. For pairwise separated cells and input coordinates below
    `2 ^ 255 - 19`, the four field elements at the output pointer are the four coordinates
    of `maddSpecN`. -/
theorem maddShippedF_correct (ra : BitVec 64) (sa : AState)
    (hsep : Separated shippedBank sa.regs maddCells)
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA (maddCallModelF ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
        (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA (maddCallModelF ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA (maddCallModelF ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA (maddCallModelF ra) sa ed25519MaddShippedBlock).mem (sa.regs "%rdi")
          (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddShippedF_correct_addr (maddCalleesF_maddCallModelF ra) sa hsep hb

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (mulSym sqrSym)

/-! ## The call models -/

/-- The call model of the shipped inversion in which `fe25519_sqr` and `fe25519_mul` run
    their shipped prologue, block and epilogue after the return address `ra` is pushed, and
    return. -/
def invertCallModelF (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = sqrSym then sqrCall ra sa
  else if f = mulSym then mulCall ra sa
  else sa

theorem invertCallModelF_sqrSym (ra : BitVec 64) (sa : AState) :
    invertCallModelF ra sqrSym sa = sqrCall ra sa := by simp [invertCallModelF]

theorem invertCallModelF_mulSym (ra : BitVec 64) (sa : AState) :
    invertCallModelF ra mulSym sa = mulCall ra sa := by
  simp [invertCallModelF, sqrSym, mulSym]

open Classical in
/-- The model that is `invertCallModelF ra` at every square call satisfying `SqrSep` and
    every multiply call satisfying `CallSep`, and `Ed25519InvertShippedProof.invertCallModel`
    at every other call. It meets `InvertCallees`, and on the inversion block, whose calls
    all satisfy those conditions, it runs as `invertCallModelF ra`. -/
noncomputable def invertCallModelP (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = sqrSym then (if SqrSep sa then sqrCall ra sa else invertCallModel sqrSym sa)
  else if f = mulSym then (if CallSep sa then mulCall ra sa else invertCallModel mulSym sa)
  else sa

theorem invertCallModelP_sqr {ra : BitVec 64} {sa : AState} (h : SqrSep sa) :
    invertCallModelP ra sqrSym sa = invertCallModelF ra sqrSym sa := by
  simp [invertCallModelP, invertCallModelF, h]

theorem invertCallModelP_mul {ra : BitVec 64} {sa : AState} (h : CallSep sa) :
    invertCallModelP ra mulSym sa = invertCallModelF ra mulSym sa := by
  simp [invertCallModelP, invertCallModelF, h, sqrSym, mulSym]

theorem invertCallees_invertCallModelP (ra : BitVec 64) : InvertCallees (invertCallModelP ra) := by
  refine ⟨fun sa => ?_, fun sa hsp => ?_⟩
  · unfold SqrEffect
    by_cases h : SqrSep sa
    · rw [invertCallModelP_sqr h, invertCallModelF_sqrSym]
      obtain ⟨hv, hf, hr, hs⟩ := sqrCall_spec ra sa h
      exact ⟨hv, hf, hr, hs "%rbx" (by decide)⟩
    · have e : invertCallModelP ra sqrSym sa = invertCallModel sqrSym sa := by
        simp [invertCallModelP, h]
      rw [e]
      exact invertCallModel_sqr sa
  · unfold MulEffect
    by_cases h : CallSep sa
    · rw [invertCallModelP_mul h, invertCallModelF_mulSym]
      obtain ⟨hv, hf, hr, hs⟩ := mulCall_spec ra sa h
      exact ⟨hv, hf, hr, hs "%rbx" (by decide)⟩
    · have e : invertCallModelP ra mulSym sa = invertCallModel mulSym sa := by
        simp [invertCallModelP, h, sqrSym, mulSym]
      rw [e]
      exact invertCallModel_mul sa hsp

/-! ## The chain under the framed model -/

/-- The registers the framed callees and the inversion's call segments keep. -/
def keptRegs : List String := ["%rsp", "%rbp", "%r12", "%r13", "%r14", "%r15"]

theorem keptRegs_sqrSaved (r : String) (hr : r ∈ keptRegs) (h0 : r ≠ "%rsp") :
    r ∈ sqrSaved := by
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h0 | decide

theorem keptRegs_calleeSaved (r : String) (hr : r ∈ keptRegs) (h0 : r ≠ "%rsp") :
    r ∈ calleeSavedRegs := by
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h0 | decide

/-- The body of a step writes no register of `keptRegs`. -/
theorem segBody_kept (s : Step) (sa : AState) (r : String) (hr : r ∈ keptRegs) :
    (runBlockA sa (segOfStep s).body).regs r = sa.regs r := by
  refine runBlockA_regs_of_all _ _ _ ?_
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  cases s with
  | sqr d a =>
    cases a <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [segOfStep, srcInstr, dsts]
  | mul d a b =>
    cases a <;> cases b <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [segOfStep, srcInstr, dsts]

/-- A framed square call at a state satisfying `SqrSep` keeps the registers of
    `keptRegs`. -/
theorem sqrCall_kept (ra : BitVec 64) (sa : AState) (h : SqrSep sa) (r : String)
    (hr : r ∈ keptRegs) : (invertCallModelF ra sqrSym sa).regs r = sa.regs r := by
  obtain ⟨-, -, hsp, hs⟩ := sqrCall_spec ra sa h
  rw [invertCallModelF_sqrSym]
  by_cases h0 : r = "%rsp"
  · subst h0; exact hsp
  · exact hs r (keptRegs_sqrSaved r hr h0)

/-- A framed multiply call at a state satisfying `CallSep` keeps the registers of
    `keptRegs`. -/
theorem mulCall_kept (ra : BitVec 64) (sa : AState) (h : CallSep sa) (r : String)
    (hr : r ∈ keptRegs) : (invertCallModelF ra mulSym sa).regs r = sa.regs r := by
  obtain ⟨-, -, hsp, hs⟩ := mulCall_spec ra sa h
  rw [invertCallModelF_mulSym]
  by_cases h0 : r = "%rsp"
  · subst h0; exact hsp
  · exact hs r (keptRegs_calleeSaved r hr h0)

/-- The separation of the buffers at a step of the chain. -/
theorem stepSep {SP IP OP : BitVec 64} {z : Nat} {E : Env} {sa : AState}
    (hsep : ChainSep SP IP) (hinv : ChainInv SP IP OP z E sa) (s : Step) :
    match s with
    | .sqr _ _ => SqrSep (runBlockA sa (segOfStep s).body)
    | .mul _ _ _ => CallSep (runBlockA sa (segOfStep s).body) := by
  cases s with
  | sqr d a =>
    obtain ⟨-, hrsp, -, hrdi, hrsi⟩ := runSqrBody sa d a
    rw [hinv.rsp] at hrsp hrdi
    rw [hinv.rsp, hinv.rbx] at hrsi
    exact ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep a,
      by rw [hrdi, hrsp]; exact srcBelowSep hsep (.buf d)⟩
  | mul d a b =>
    obtain ⟨-, hrsp, -, hrdi, hrsi, hrdx⟩ := runMulBody sa d a b
    rw [hinv.rsp] at hrsp hrdi
    rw [hinv.rsp, hinv.rbx] at hrsi hrdx
    exact ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep a,
      by rw [hrdx, hrsp]; exact srcBelowSep hsep b,
      by rw [hrdi, hrsp]; exact srcBelowSep hsep (.buf d)⟩

/-- One step of the chain runs as under `invertCallModelP ra` and keeps the registers of
    `keptRegs`. -/
theorem stepF {ra : BitVec 64} {SP IP OP : BitVec 64} {z : Nat} {E : Env} {sa : AState}
    (hsep : ChainSep SP IP) (hinv : ChainInv SP IP OP z E sa) (s : Step) :
    segsRunA (invertCallModelP ra) sa [segOfStep s] = segsRunA (invertCallModelF ra) sa [segOfStep s]
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelF ra) sa [segOfStep s]).regs r = sa.regs r := by
  have hS := stepSep hsep hinv s
  cases s with
  | sqr d a =>
    refine ⟨invertCallModelP_sqr hS, fun r hr => ?_⟩
    show (invertCallModelF ra sqrSym (runBlockA sa (segOfStep (.sqr d a)).body)).regs r = _
    rw [sqrCall_kept ra _ hS r hr, segBody_kept _ _ r hr]
  | mul d a b =>
    refine ⟨invertCallModelP_mul hS, fun r hr => ?_⟩
    show (invertCallModelF ra mulSym (runBlockA sa (segOfStep (.mul d a b)).body)).regs r = _
    rw [mulCall_kept ra _ hS r hr, segBody_kept _ _ r hr]

/-- The chain over a list of steps runs as under `invertCallModelP ra` and keeps the
    registers of `keptRegs`. -/
theorem chainRunF (ra : BitVec 64) {SP IP OP : BitVec 64} {z : Nat} (hz : z < pM)
    (hsep : ChainSep SP IP) :
    ∀ (steps : List Step) (E : Env) (sa : AState), ChainInv SP IP OP z E sa →
      segsRunA (invertCallModelP ra) sa (steps.map segOfStep)
          = segsRunA (invertCallModelF ra) sa (steps.map segOfStep)
        ∧ ∀ r ∈ keptRegs,
          (segsRunA (invertCallModelF ra) sa (steps.map segOfStep)).regs r = sa.regs r := by
  intro steps
  induction steps with
  | nil => intro E sa _; exact ⟨rfl, fun _ _ => rfl⟩
  | cons s rest ih =>
    intro E sa h
    have e : ∀ C : ACallModel, segsRunA C sa ((s :: rest).map segOfStep)
        = segsRunA C (segsRunA C sa [segOfStep s]) (rest.map segOfStep) := fun C => by
      rw [List.map_cons, show (segOfStep s :: rest.map segOfStep)
        = [segOfStep s] ++ rest.map segOfStep from rfl, segsRunA_append]
    obtain ⟨e1, k1⟩ := stepF (ra := ra) hsep h s
    have h1 := chainStep (invertCallees_invertCallModelP ra) hz hsep h s
    obtain ⟨e2, k2⟩ := ih _ _ h1
    rw [e, e, e2, e1]
    refine ⟨rfl, fun r hr => ?_⟩
    rw [← e1, k2 r hr, e1, k1 r hr]

/-- **The inversion block under the framed model.** For a state whose input buffer is
    disjoint from the inversion frame, whose input is below `2 ^ 255 - 19`, and whose output
    buffer lies outside the eighteen words below `%rsp`, the block runs as under
    `invertCallModelP ra` and keeps the registers of `keptRegs`. -/
theorem invertF_run (ra : BitVec 64) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)) :
    segsRunA (invertCallModelP ra) sa Ed25519InvertShipped.ed25519InvertShippedBlock
        = segsRunA (invertCallModelF ra) sa Ed25519InvertShipped.ed25519InvertShippedBlock
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelF ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).regs r = sa.regs r := by
  simp only [invertBlock_eq, segsRunA_append]
  -- the first segment
  obtain ⟨-, hrsp, -, hrdi, hrsi⟩ := runEntryBody sa
  have hS1 : SqrSep (runBlockA sa
      [.mov "%rbx" (.reg "%rsi"), .storeMem "%rsp" 128 (.reg "%rdi"),
       .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%rbx")]) :=
    ⟨by rw [hrsi, hrsp]; exact srcBelowSep hsep .inp,
      by rw [hrdi, hrsp]; exact srcBelowSep hsep (.buf .b0)⟩
  have eS : ∀ C : ACallModel, segsRunA C sa Ed25519InvertShipped.ed25519InvertShippedSeg001
      = C sqrSym (runBlockA sa
        [.mov "%rbx" (.reg "%rsi"), .storeMem "%rsp" 128 (.reg "%rdi"),
         .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%rbx")]) := fun C => rfl
  have e1 : segsRunA (invertCallModelP ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001
      = segsRunA (invertCallModelF ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001 := by
    rw [eS, eS]; exact invertCallModelP_sqr hS1
  have k1 : ∀ r ∈ keptRegs, (segsRunA (invertCallModelF ra) sa
      Ed25519InvertShipped.ed25519InvertShippedSeg001).regs r = sa.regs r := by
    intro r hr
    rw [eS, sqrCall_kept ra _ hS1 r hr]
    refine runBlockA_regs_of_all _ _ _ ?_
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsts]
  have i1 := invertEntry (invertCallees_invertCallModelP ra) sa hsep
  -- the chain
  obtain ⟨e2, k2⟩ := chainRunF ra hz hsep invertSteps invertEnv1 _ i1
  have i2 := chainRun (invertCallees_invertCallModelP ra) hz hsep invertSteps invertEnv1 _ i1
  rw [invertEnv_final] at i2
  obtain ⟨s2, hs2⟩ : ∃ s, segsRunA (invertCallModelP ra)
      (segsRunA (invertCallModelP ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001)
      (invertSteps.map segOfStep) = s := ⟨_, rfl⟩
  have i2' : ChainInv _ _ _ _ _ s2 := hs2 ▸ i2
  -- the last segment
  obtain ⟨-, hrsp3, hrdi3, hrsi3, hrdx3⟩ := runExitBody s2
  rw [i2'.rsp] at hrsp3 hrdi3 hrsi3 hrdx3
  rw [i2'.outp] at hrdi3
  have hS3 : CallSep (runBlockA s2 [.loadMem "%rdi" "%rsp" 128,
      .lea "%rsi" "%rsp" "%rsp" 0 32, .lea "%rdx" "%rsp" "%rsp" 0 0]) :=
    ⟨by rw [hrsi3, hrsp3]; exact srcBelowSep hsep (.buf .b1),
      by rw [hrdx3, hrsp3]; exact srcBelowSep hsep (.buf .b0),
      by rw [hrdi3, hrsp3]; exact ho⟩
  have e3 : segsRunA (invertCallModelP ra) s2 Ed25519InvertShipped.ed25519InvertShippedSeg265
      = segsRunA (invertCallModelF ra) s2 Ed25519InvertShipped.ed25519InvertShippedSeg265 := by
    rw [segsRunA_exit, segsRunA_exit]
    exact invertCallModelP_mul hS3
  have k3 : ∀ r ∈ keptRegs, (segsRunA (invertCallModelF ra) s2
      Ed25519InvertShipped.ed25519InvertShippedSeg265).regs r = s2.regs r := by
    intro r hr
    rw [segsRunA_exit, mulCall_kept ra _ hS3 r hr]
    refine runBlockA_regs_of_all _ _ _ ?_
    simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsts]
  have e21 : segsRunA (invertCallModelF ra)
      (segsRunA (invertCallModelF ra) sa Ed25519InvertShipped.ed25519InvertShippedSeg001)
      (invertSteps.map segOfStep) = s2 :=
    (congrArg (fun x => segsRunA (invertCallModelF ra) x (invertSteps.map segOfStep))
      e1).symm.trans (e2.symm.trans hs2)
  refine ⟨?_, fun r hr => ?_⟩
  · exact (congrArg (fun x => segsRunA (invertCallModelP ra) x
      Ed25519InvertShipped.ed25519InvertShippedSeg265) hs2).trans
      (e3.trans (congrArg (fun x => segsRunA (invertCallModelF ra) x
        Ed25519InvertShipped.ed25519InvertShippedSeg265) e21.symm))
  · refine (congrArg (fun x => (segsRunA (invertCallModelF ra) x
      Ed25519InvertShipped.ed25519InvertShippedSeg265).regs r) e21).trans ?_
    refine (k3 r hr).trans ?_
    refine (congrArg (fun x => x.regs r) (hs2.symm.trans e2)).trans ?_
    refine (k2 r hr).trans ?_
    exact (congrArg (fun x => x.regs r) e1).trans (k1 r hr)

/-- **The shipped `ed25519_invert` over the framed shipped callees.** Each callee runs its
    shipped prologue, block and epilogue after the return address `ra` is pushed. For a
    state whose input buffer is disjoint from the inversion frame, whose input is below
    `2 ^ 255 - 19` and whose output buffer lies outside the eighteen words below `%rsp`, the
    four-limb value at the output pointer after the block is the input raised to
    `2 ^ 255 - 21` modulo `2 ^ 255 - 19`; the block changes no byte outside the inversion
    frame and the output, and keeps `%rsp`, `%rbp` and `%r12` to `%r15`. -/
theorem invertShippedF_correct (ra : BitVec 64) (sa : AState)
    (hsep : ChainSep (sa.regs "%rsp") (sa.regs "%rsi"))
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM)
    (ho : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)) :
    feO (segsRunA (invertCallModelF ra) sa
        Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
      ∧ InvertFrame sa.mem (segsRunA (invertCallModelF ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).mem (sa.regs "%rsp") (sa.regs "%rdi")
      ∧ ∀ r ∈ keptRegs, (segsRunA (invertCallModelF ra) sa
          Ed25519InvertShipped.ed25519InvertShippedBlock).regs r = sa.regs r := by
  obtain ⟨e, k⟩ := invertF_run ra sa hsep hz ho
  rw [← e]
  exact ⟨invertShipped_correct_addr (invertCallees_invertCallModelP ra) sa hsep hz,
    invertShipped_frame (invertCallees_invertCallModelP ra) sa hsep hz, by rw [e]; exact k⟩

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT (invertSym packSignSym)

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (limbsNat)

/-! ## The framed inversion call -/

/-- A call to the shipped `ed25519_invert`: its prologue, its block over the framed model
    of its own callees, and its epilogue. -/
def invertCall (ra : BitVec 64) : AState → AState :=
  framedCall Ed25519InvertShipped.ed25519InvertShippedPrologue
    Ed25519InvertShipped.ed25519InvertShippedEpilogue
    (fun s => segsRunA (invertCallModelF ra) s Ed25519InvertShipped.ed25519InvertShippedBlock) ra

/-- `m'` differs from `m` only in the forty-two words from `sp - 336` to `sp - 8` and the
    four words at `op`. -/
def InvertFrameF (m m' : AMem) (sp op : BitVec 64) : Prop :=
  ∀ x, (∀ k, k < 42 → ¬ InRange8 (sp + BitVec.ofInt 64 (-336 + ((8 * k : Nat) : Int))) x) →
    (∀ k, k < 4 → ¬ InRange8 (op + BitVec.ofInt 64 (8 * k : Nat)) x) → m' x = m x

/-- The buffers of an inversion call: the input is disjoint from the inversion frame 192
    bytes below `%rsp` and from the return-address and saved-`%rbx` slots, and the output
    lies outside the forty-two words below `%rsp`. -/
structure InvSep (sa : AState) : Prop where
  /-- The input and the inversion frame. -/
  chain : ChainSep (sa.regs "%rsp" + BitVec.ofInt 64 (-192)) (sa.regs "%rsi")
  /-- The input and the return-address and saved-`%rbx` slots. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-16) (-8)
  /-- The output and the words below `%rsp`. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-336) (-8)

/-- **A call to the shipped `ed25519_invert`.** For an input below `2 ^ 255 - 19` and
    buffers satisfying `InvSep`, the call leaves the input raised to `2 ^ 255 - 21` modulo
    `2 ^ 255 - 19` at the output, changes no byte outside the forty-two words below `%rsp`
    and the output, and returns `%rsp`, `%rbx` and `%r12` at their values at the call:
    `%rbx` by the shipped `popq`, `%r12` because neither the block nor its framed callees
    change it. -/
theorem invertCall_spec (ra : BitVec 64) (sa : AState) (h : InvSep sa)
    (hz : feO sa.mem (sa.regs "%rsi") 0 < pM) :
    feO (invertCall ra sa).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
      ∧ InvertFrameF sa.mem (invertCall ra sa).mem (sa.regs "%rsp") (sa.regs "%rdi")
      ∧ (invertCall ra sa).regs "%rsp" = sa.regs "%rsp"
      ∧ (invertCall ra sa).regs "%rbx" = sa.regs "%rbx"
      ∧ (invertCall ra sa).regs "%r12" = sa.regs "%r12" := by
  have ent := entered ["%rbx"] 176 ra sa (by decide) (by simp)
  have hEsp : (entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-192) := by
    rw [ent.rsp]; congr 2
  have er : ∀ r : String, r ≠ "%rsp" →
      (entryState (framePro ["%rbx"] 176) ra sa).regs r = sa.regs r := ent.regs
  have hin : feO (entryState (framePro ["%rbx"] 176) ra sa).mem (sa.regs "%rsi") 0
      = feO sa.mem (sa.regs "%rsi") 0 := by
    simp only [feO]
    refine congrArg _ (List.map_congr_left fun j hj => ent.read64_eq _ fun k hk => ?_)
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [List.length_cons, List.length_nil] at hk
    exact (h.is (0 + j) (-(8 * ((k : Int) + 1)))
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hj with rfl | rfl | rfl | rfl <;> omega) (by omega) (by omega)
      (by omega)).symm
  have hsepE : ChainSep ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp")
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsi") := by
    rw [hEsp, er _ (by decide)]; exact h.chain
  have hzE : feO (entryState (framePro ["%rbx"] 176) ra sa).mem
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsi") 0 < pM := by
    rw [er _ (by decide), hin]; exact hz
  have hoE : RangeDisj ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rdi") 0 24
      ((entryState (framePro ["%rbx"] 176) ra sa).regs "%rsp") (-144) (-8) := by
    rw [hEsp, er _ (by decide)]
    exact rangeDisj_shift (-192) (by decide)
      (rangeDisj_narrow h.os (le_refl _) (le_refl _) (by omega) (by omega))
  obtain ⟨hv, hf, hk⟩ := invertShippedF_correct ra _ hsepE hzE hoE
  rw [er "%rdi" (by decide), er "%rsi" (by decide), hin] at hv
  rw [er "%rdi" (by decide), hEsp] at hf
  have hs : ∀ k, k < ["%rbx"].length →
      read64 (segsRunA (invertCallModelF ra) (entryState (framePro ["%rbx"] 176) ra sa)
          Ed25519InvertShipped.ed25519InvertShippedBlock).mem
          (slotAddr (sa.regs "%rsp") (k + 1))
        = read64 (entryState (framePro ["%rbx"] 176) ra sa).mem
          (slotAddr (sa.regs "%rsp") (k + 1)) := by
    intro k hk
    obtain rfl : k = 0 := by simp at hk; omega
    refine read64_invertFrame hf _ (fun j hj => ?_) (fun j hj => ?_)
    · rw [redBase, addI, addI, slotAddr]
      exact djSS _ _ _ (by omega) (by omega)
    · rw [slotAddr]
      exact h.os _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have P := framedCall_popped ["%rbx"] 176
    (fun s => segsRunA (invertCallModelF ra) s Ed25519InvertShipped.ed25519InvertShippedBlock)
    ra sa (by decide) (by simp) (by simp) (hk "%rsp" (by decide)) hs
  rw [invertCall, invertFrame.1, invertFrame.2]
  refine ⟨by rw [P.mem]; exact hv, fun x hx hy => ?_, P.rsp, P.saved "%rbx" (by simp), ?_⟩
  · rw [P.mem, hf x (fun k hk => ?_) hy]
    · refine ent.mem x fun k hk => ?_
      simp only [List.length_cons, List.length_nil] at hk
      have h2 := hx (41 - k) (by omega)
      rwa [slotAddr, show -(8 * ((k : Int) + 1)) = (-336 : Int) + ((8 * (41 - k) : Nat) : Int)
        from by omega]
    · rw [redBase, addI, addI]
      have h2 := hx k (by omega)
      rwa [show (-192 : Int) + (-144 + ((8 * k : Nat) : Int)) = -336 + ((8 * k : Nat) : Int)
        from by omega]
  · rw [P.other "%r12" (by simp) (by decide), hk "%r12" (by decide), er _ (by decide)]

/-! ## The call model of the compression -/

/-- The call model of the shipped compression in which `ed25519_invert`, `fe25519_mul` and
    `ed25519_pack_sign` run their shipped prologue, block and epilogue after the return
    address `ra` is pushed, and return; the inversion's own callees run under
    `invertCallModelF ra`. -/
def compressCallModelF (ra : BitVec 64) : ACallModel := fun f sa =>
  if f = invertSym then invertCall ra sa
  else if f = mulSym then mulCall ra sa
  else if f = packSignSym then packCall ra sa
  else sa

theorem compressCallModelF_invertSym (ra : BitVec 64) (sa : AState) :
    compressCallModelF ra invertSym sa = invertCall ra sa := by simp [compressCallModelF]

theorem compressCallModelF_mulSym (ra : BitVec 64) (sa : AState) :
    compressCallModelF ra mulSym sa = mulCall ra sa := by
  simp [compressCallModelF, invertSym, mulSym]

theorem compressCallModelF_packSignSym (ra : BitVec 64) (sa : AState) :
    compressCallModelF ra packSignSym sa = packCall ra sa := by
  simp [compressCallModelF, invertSym, mulSym, packSignSym]

/-- The effect of an inversion call at one state: the power at `%rdi`, no memory outside
    the forty-two words below `%rsp` and the 32 bytes at `%rdi`, and `%rsp`, `%rbx` and
    `%r12` kept. -/
def InvEffectF (C : ACallModel) (f : String) (sa : AState) : Prop :=
  feO (C f sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0 ^ (pM - 2) % pM
    ∧ InvertFrameF sa.mem (C f sa).mem (sa.regs "%rsp") (sa.regs "%rdi")
    ∧ KeepsRegs C f sa

/-- The three callees of the compression at their specifications, over the framed calls. -/
structure CompressCalleesF (C : ACallModel) : Prop where
  /-- `ed25519_invert` inverts. -/
  inv : ∀ sa, InvSep sa → feO sa.mem (sa.regs "%rsi") 0 < pM → InvEffectF C invertSym sa
  /-- `fe25519_mul` multiplies modulo `pM` and keeps `%r12`. -/
  mul : ∀ sa, CallSep sa →
    MulEffect C mulSym sa ∧ (C mulSym sa).regs "%r12" = sa.regs "%r12"
  /-- `ed25519_pack_sign` packs. -/
  pack : ∀ sa, PackSepF sa → PackEffect C packSignSym sa

/-- **The three shipped callees, framed, meet the specifications of the compression.** -/
theorem compressCalleesF_compressCallModelF (ra : BitVec 64) :
    CompressCalleesF (compressCallModelF ra) := by
  refine ⟨fun sa h hz => ?_, fun sa h => ?_, fun sa h => ?_⟩
  · obtain ⟨hv, hf, h1, h2, h3⟩ := invertCall_spec ra sa h hz
    unfold InvEffectF KeepsRegs
    rw [compressCallModelF_invertSym]
    exact ⟨hv, hf, h1, h2, h3⟩
  · obtain ⟨hv, hf, h1, hs⟩ := mulCall_spec ra sa h
    unfold MulEffect
    rw [compressCallModelF_mulSym]
    exact ⟨⟨hv, hf, h1, hs "%rbx" (by decide)⟩, hs "%r12" (by decide)⟩
  · unfold PackEffect
    rw [compressCallModelF_packSignSym]
    exact packCall_spec ra sa h

/-- A word disjoint from the forty-two words below `sp` and from the 32 bytes at `sp` survives
    an inversion call writing the slot at `sp`. -/
theorem read64_invFrameF {m m' : AMem} {sp b : BitVec 64}
    (hf : InvertFrameF m m' sp (sp + BitVec.ofInt 64 0))
    (hd : ∀ o : Int, (-336 ≤ o ∧ o ≤ -8 ∨ 0 ≤ o ∧ o ≤ 24) → o % 8 = 0 →
      Disjoint8 (sp + BitVec.ofInt 64 o) b) :
    read64 m' b = read64 m b :=
  read64_congr _ _ _ fun i hi => hf _
    (fun k hk => not_inRange_of_disjoint _ _ i (hd _ (Or.inl ⟨by omega, by omega⟩) (by omega)) hi)
    (fun k hk => not_inRange_of_disjoint _ _ i (by
      rw [addI]; exact hd _ (Or.inr ⟨by omega, by omega⟩) (by omega)) hi)

/-- A four-limb value disjoint from the forty-two words below `sp` and from the 32 bytes at
    `sp` survives an inversion call writing the slot at `sp`. -/
theorem feO_invFrameF {m m' : AMem} {sp p : BitVec 64} {c : Int}
    (hf : InvertFrameF m m' sp (sp + BitVec.ofInt 64 0))
    (hd : ∀ o : Int, (-336 ≤ o ∧ o ≤ -8 ∨ 0 ≤ o ∧ o ≤ 24) → o % 8 = 0 →
      ∀ j ∈ limbOffs, Disjoint8 (sp + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 (c + j))) :
    feO m' p c = feO m p c := by
  simp only [feO]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  exact read64_invFrameF hf fun o ho h8 => hd o ho h8 j hj

/-! ## The compression -/

/-- **The shipped `ed25519_compress` over callees meeting `CompressCalleesF`.** For a state
    whose output and coordinate buffers are disjoint from the stack words the compression
    and its callees use, and whose third coordinate `Z` is below `2 ^ 255 - 19`, the
    four-limb value at the output pointer after the block is `y + 2 ^ 255 * (x % 2)`, where
    `x` and `y` are the first and second coordinates times `Z ^ (2 ^ 255 - 21)`, reduced
    modulo `2 ^ 255 - 19`. -/
theorem compressShippedF_correct_addr {C : ACallModel} (hC : CompressCalleesF C)
    (sa : AState) (hsep : CompressSep sa) (hz : feO sa.mem (sa.regs "%rcx") 0 < pM) :
    feO (segsRunA C sa Ed25519CompressShipped.ed25519CompressShippedBlock).mem
        (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM
        + 2 ^ 255 * (feO sa.mem (sa.regs "%rsi") 0
            * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM % 2) := by
  rw [segsRunA_compress]
  -- segment 1 and the inversion
  obtain ⟨m1, rsp1, rbx1, r121, rdi1, rsi1⟩ := runBody1 sa
  set b1 := runBlockA sa body1 with hb1
  have wr : ∀ (p : BitVec 64), RangeDisj p 0 24 (sa.regs "%rsp") (-336) 96 →
      feO b1.mem p 0 = feO sa.mem p 0 := fun p hp => by
    rw [m1, feO_write64]
    exact fun j hj => djBuf hp 96 (by omega) (by omega) (by omega) j hj
  have hinv : InvSep b1 := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · rw [rsp1, rsi1]
      exact (rangeDisj_shift (-192) (by decide)
        (rangeDisj_narrow hsep.zs (le_refl _) (le_refl _) (by omega) (by omega))).symm
    · rw [rsp1, rsi1]
      exact rangeDisj_narrow hsep.zs (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rsp1, rdi1]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 0) (e := 0) 0 24 (-336) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨hv1, hf1, k1rsp, k1rbx, k1r12⟩ :=
    hC.inv b1 hinv (by rw [rsi1, wr _ hsep.zs]; exact hz)
  set s1 := C invertSym b1 with hs1
  rw [rsi1, rdi1, wr _ hsep.zs, feO_base] at hv1
  rw [rsp1, rdi1] at hf1
  have inv : ∀ (p : BitVec 64), RangeDisj p 0 24 (sa.regs "%rsp") (-336) 96 →
      feO s1.mem p 0 = feO sa.mem p 0 := fun p hp => by
    rw [feO_invFrameF hf1 fun o ho h8 => djBuf hp o (by omega) (by omega) h8, wr p hp]
  -- segment 2 and the first multiply
  obtain ⟨m2, rsp2, r122, rdi2, rsi2, rdx2⟩ := runBody2 s1
  set b2 := runBlockA s1 body2 with hb2
  rw [k1rsp, rsp1] at rsp2 rdi2 rdx2
  rw [k1rbx, rbx1] at rsi2
  have hargs2 : CallSep b2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [rsi2, rsp2]
      exact rangeDisj_narrow hsep.xs (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rdx2, rsp2]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 0) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdi2, rsp2]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 32) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨⟨hv2, hf2, k2rsp, -⟩, k2r12⟩ := hC.mul b2 hargs2
  set s2 := C mulSym b2 with hs2
  rw [rsi2, rdx2, rdi2, m2, inv _ hsep.xs, feO_base, feO_base, hv1] at hv2
  rw [rdi2, rsp2, m2] at hf2
  have stk : ∀ c : Int, c % 8 = 0 → ∀ o : Int, (o ≤ c - 8 ∨ c + 32 ≤ o) →
      o % 8 = 0 → -336 ≤ o → o ≤ 96 → -336 ≤ c → c ≤ 96 →
      ∀ j ∈ limbOffs, Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 o)
        (sa.regs "%rsp" + BitVec.ofInt 64 (c + j)) := by
    intro c hc o ho h8 h0 h1 c0 c1
    refine djStack _ _ _ fun j hj => ?_
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> omega
  -- segment 3 and the second multiply
  obtain ⟨m3, rsp3, rdi3, rsi3, rdx3⟩ := runBody3 s2
  set b3 := runBlockA s2 body3 with hb3
  rw [k2rsp, rsp2] at rsp3 rdi3 rdx3
  rw [k2r12, r122, k1r12, r121] at rsi3
  have hargs3 : CallSep b3 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [rsi3, rsp3]
      exact rangeDisj_narrow hsep.ys (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rdx3, rsp3]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 0) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdi3, rsp3]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨⟨hv3, hf3, k3rsp, -⟩, -⟩ := hC.mul b3 hargs3
  set s3 := C mulSym b3 with hs3
  have y2 : feO s2.mem (sa.regs "%rdx") 0 = feO s1.mem (sa.regs "%rdx") 0 :=
    feO_mulFrame hf2 (by decide) fun o ho h8 => djBuf hsep.ys o (by omega) (by omega) h8
  have z2 : feO s2.mem (sa.regs "%rsp") (0 + 0) = feO s1.mem (sa.regs "%rsp") (0 + 0) :=
    feO_mulFrame hf2 (by decide) fun o ho h8 =>
      stk 0 (by decide) o (by omega) h8 (by omega) (by omega) (by omega) (by omega)
  rw [rsi3, rdx3, rdi3, m3, feO_base, feO_base, y2, z2, inv _ hsep.ys, hv1] at hv3
  rw [rdi3, rsp3, m3] at hf3
  -- segment 4 and the pack
  obtain ⟨m4, rsp4, rdi4, rsi4, rdx4⟩ := runBody4 s3
  set b4 := runBlockA s3 body4 with hb4
  rw [k3rsp, rsp3] at rsp4 rdi4 rsi4 rdx4
  have slot : read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 96) = sa.regs "%rdi" := by
    rw [read64_mulFrame hf3 (by decide) fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      read64_mulFrame hf2 (by decide) fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      read64_invFrameF hf1 fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      m1, read64_write64_same]
  rw [slot] at rdi4
  have hpack : PackSepF b4 := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [rdi4, rsi4]
      exact rangeDisj_shift 64 (by decide)
        (rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega))
    · rw [rdi4, rdx4]
      exact rangeDisj_shift 32 (by decide)
        (rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega))
    · rw [rsi4, rdx4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 32) 0 24 0 0 rfl rfl
        fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdi4, rsp4]
      exact rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rsi4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 0) 0 24 (-80) (-16) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdx4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 32) (e := 0) 0 0 (-80) (-16) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rsi4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 0) 0 24 (-8) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdx4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 32) (e := 0) 0 0 (-8) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨hw, hw24⟩ := hC.pack b4 hpack
  rw [rdi4, rsi4, rdx4, m4] at hw24
  rw [rdi4, rsi4, m4] at hw
  -- the value
  have hY : feO s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64) 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM := by
    rw [feO_base]; exact hv3
  have hX : feO s3.mem (sa.regs "%rsp") (32 + 0)
      = feO sa.mem (sa.regs "%rsi") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM := by
    rw [feO_mulFrame (c := 32 + 0) hf3 (by decide) fun o ho h8 =>
      stk (32 + 0) (by decide) o (by omega) h8 (by omega) (by omega) (by omega) (by omega)]
    exact hv2
  have hpar : (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 32 + BitVec.ofInt 64 0)).toNat
      % 2 = feO sa.mem (sa.regs "%rsi") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM % 2 := by
    rw [← hX, ← feO_base, feO_eq_limbsNat]
    unfold limbsNat
    omega
  have hlt :
      limbsNat (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 0))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 8))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 16))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 24))
      < 2 ^ 255 := by
    rw [← feO_eq_limbsNat, hY]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ pM_pos) (by unfold pM; omega)
  rw [feO_eq_limbsNat, hw 0 (by simp), hw 8 (by simp), hw 16 (by simp), hw24,
    limbsNat_packTop _ _ _ _ _ hlt, ← feO_eq_limbsNat, hY, hpar]

/-- **The shipped `ed25519_compress` over the framed shipped callees.** Each callee runs its
    shipped prologue, block and epilogue after the return address `ra` is pushed, and the
    inversion's own callees likewise; `%rsp` and the saved registers the compression relies
    on are restored by the shipped instructions. For a state whose output and coordinate
    buffers are disjoint from the stack words the compression and its callees use, and whose
    third coordinate `Z` is below `2 ^ 255 - 19`, the four-limb value at the output pointer
    after the block is `y + 2 ^ 255 * (x % 2)`, where `x` and `y` are the first and second
    coordinates times `Z ^ (2 ^ 255 - 21)`, reduced modulo `2 ^ 255 - 19`. -/
theorem compressShippedF_correct (ra : BitVec 64) (sa : AState) (hsep : CompressSep sa)
    (hz : feO sa.mem (sa.regs "%rcx") 0 < pM) :
    feO (segsRunA (compressCallModelF ra) sa
        Ed25519CompressShipped.ed25519CompressShippedBlock).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM
        + 2 ^ 255 * (feO sa.mem (sa.regs "%rsi") 0
            * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM % 2) :=
  compressShippedF_correct_addr (compressCalleesF_compressCallModelF ra) sa hsep hz

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519FramedCalls
