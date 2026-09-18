/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres

/-!
# The canonical form of the shipped `ed25519_pack_sign` and its name-keyed effect

`Imported.Ed25519PackSignShipped.ed25519PackSignShippedBlock` is the body of
`ed25519_pack_sign` as printed by the owned backend. Its memory operands include indexed
forms `(%r14, %rax, 8)` whose base is a pointer copied through a stack slot and whose index
holds a constant, so `AddrMemDerived.canonD shippedBank` rewrites each of them to the
displacement operand of its cell. This module carries that canonical block in seven parts
and the memory it leaves over the name-keyed machine.

## Main definitions

* `packCanon1` … `packCanon7`: the canonical block in seven parts.

## Main results

* `packCanon_eq`: the parts concatenate to `canonD shippedBank` of the shipped block.
* `packCanon1_mem` … `packCanon7_mem`, `packCanon5_rsi`, `packCanon5_rdx`: the memory and
  the registers each part leaves.
* `packSign_nameKeyed`: the canonical block copies the four limbs at the bank `%rsi` to the
  bank `%rdi`, with the low bit of the word at `(%rdx, 0)` added into the top bit of the
  fourth limb.

Provenance class: `@reimported`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignNameKeyed

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported

/-! ## The canonical block in seven parts -/

/-- The nine entry stores: the three arguments and the six callee-saved registers into the
    stack slots of the frame. -/
def packCanon1 : List (JInstr 64) :=
  [ .storeMem "%rsp" 56 (.reg "%rdi"), .storeMem "%rsp" 48 (.reg "%rsi"),
    .storeMem "%rsp" 40 (.reg "%rbx"), .storeMem "%rsp" 32 (.reg "%rbp"),
    .storeMem "%rsp" 24 (.reg "%r12"), .storeMem "%rsp" 16 (.reg "%r13"),
    .storeMem "%rsp" 8 (.reg "%r14"), .storeMem "%rsp" 0 (.reg "%r15"),
    .storeMem "%rsp" (-8) (.reg "%rdx") ]

/-- The copy of the first limb. -/
def packCanon2 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 56, .loadMem "%rcx" "%rsp" 48, .mov "%rax" (.imm 0),
    .mov "%r14" (.reg "%rcx"), .loadMem "%rsi" "%rsi" 0, .mov "%rax" (.imm 0),
    .mov "%r14" (.reg "%rbx"), .storeMem "%rdi" 0 (.reg "%rsi") ]

/-- The copy of the second limb. -/
def packCanon3 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 1), .loadMem "%r14" "%rsp" 48, .loadMem "%rsi" "%rsi" 8,
    .mov "%rax" (.imm 1), .loadMem "%r14" "%rsp" 56, .storeMem "%rdi" 8 (.reg "%rsi") ]

/-- The copy of the third limb. -/
def packCanon4 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 2), .loadMem "%r14" "%rsp" 48, .loadMem "%rsi" "%rsi" 16,
    .mov "%rax" (.imm 2), .loadMem "%r14" "%rsp" 56, .storeMem "%rdi" 16 (.reg "%rsi") ]

/-- The fourth limb into `%rsi` and the low bit of the first limb of the second input
    into `%rdx`. -/
def packCanon5 : List (JInstr 64) :=
  [ .mov "%rax" (.imm 3), .loadMem "%r14" "%rsp" 48, .loadMem "%rsi" "%rsi" 24,
    .mov "%rax" (.imm 0), .loadMem "%r14" "%rsp" (-8), .loadMem "%rcx" "%rdx" 0,
    .mov "%rdx" (.reg "%rcx"), .and_ "%rdx" (.imm 1) ]

/-- The sign bit into the top bit of the fourth limb, and the store of that limb. -/
def packCanon6 : List (JInstr 64) :=
  [ .mov "%rax" (.reg "%rdx"), .shl "%rax" (.imm 63), .mov "%rcx" (.reg "%rsi"),
    .add "%rcx" (.reg "%rax"), .mov "%rax" (.reg "%rcx"), .mov "%rcx" (.imm 3),
    .loadMem "%r14" "%rsp" 56, .storeMem "%rdi" 24 (.reg "%rax") ]

/-- The six loads restoring the callee-saved registers. -/
def packCanon7 : List (JInstr 64) :=
  [ .loadMem "%rbx" "%rsp" 40, .loadMem "%rbp" "%rsp" 32, .loadMem "%r12" "%rsp" 24,
    .loadMem "%r13" "%rsp" 16, .loadMem "%r14" "%rsp" 8, .loadMem "%r15" "%rsp" 0 ]

/-- The seven parts are the canonical form of the shipped block. -/
theorem packCanon_eq :
    canonD shippedBank Ed25519PackSignShipped.ed25519PackSignShippedBlock
      = packCanon1 ++ packCanon2 ++ packCanon3 ++ packCanon4 ++ packCanon5 ++ packCanon6
        ++ packCanon7 := rfl

/-! ## The effect of each part -/

theorem packCanon1_mem (s : JState 64) :
    (runBlock s packCanon1).mem
      = fun b o => if b = "%rsp" ∧ o = -8 then s.regs "%rdx"
        else if b = "%rsp" ∧ o = 0 then s.regs "%r15"
        else if b = "%rsp" ∧ o = 8 then s.regs "%r14"
        else if b = "%rsp" ∧ o = 16 then s.regs "%r13"
        else if b = "%rsp" ∧ o = 24 then s.regs "%r12"
        else if b = "%rsp" ∧ o = 32 then s.regs "%rbp"
        else if b = "%rsp" ∧ o = 40 then s.regs "%rbx"
        else if b = "%rsp" ∧ o = 48 then s.regs "%rsi"
        else if b = "%rsp" ∧ o = 56 then s.regs "%rdi"
        else s.mem b o := rfl

theorem packCanon2_mem (s : JState 64) :
    (runBlock s packCanon2).mem
      = fun b o => if b = "%rdi" ∧ o = 0 then s.mem "%rsi" 0 else s.mem b o := rfl

theorem packCanon3_mem (s : JState 64) :
    (runBlock s packCanon3).mem
      = fun b o => if b = "%rdi" ∧ o = 8 then s.mem "%rsi" 8 else s.mem b o := rfl

theorem packCanon4_mem (s : JState 64) :
    (runBlock s packCanon4).mem
      = fun b o => if b = "%rdi" ∧ o = 16 then s.mem "%rsi" 16 else s.mem b o := rfl

theorem packCanon5_mem (s : JState 64) : (runBlock s packCanon5).mem = s.mem := rfl

theorem packCanon5_rsi (s : JState 64) :
    (runBlock s packCanon5).regs "%rsi" = s.mem "%rsi" 24 := rfl

theorem packCanon5_rdx (s : JState 64) :
    (runBlock s packCanon5).regs "%rdx" = s.mem "%rdx" 0 &&& 1 := rfl

theorem packCanon6_mem (s : JState 64) :
    (runBlock s packCanon6).mem
      = fun (b : String) (o : Int) => if b = "%rdi" ∧ o = 24
        then s.regs "%rsi" + s.regs "%rdx" <<< 63 else s.mem b o := rfl

theorem packCanon7_mem (s : JState 64) : (runBlock s packCanon7).mem = s.mem := rfl

/-! ## The cells each part leaves untouched -/

theorem packCanon1_keep (s : JState 64) (b : String) (o : Int) (hb : b ≠ "%rsp") :
    (runBlock s packCanon1).mem b o = s.mem b o := by
  rw [packCanon1_mem]; simp [hb]

theorem packCanon2_keep (s : JState 64) (b : String) (o : Int) (h : ¬(b = "%rdi" ∧ o = 0)) :
    (runBlock s packCanon2).mem b o = s.mem b o := by
  rw [packCanon2_mem]; simp [h]

theorem packCanon3_keep (s : JState 64) (b : String) (o : Int) (h : ¬(b = "%rdi" ∧ o = 8)) :
    (runBlock s packCanon3).mem b o = s.mem b o := by
  rw [packCanon3_mem]; simp [h]

theorem packCanon4_keep (s : JState 64) (b : String) (o : Int) (h : ¬(b = "%rdi" ∧ o = 16)) :
    (runBlock s packCanon4).mem b o = s.mem b o := by
  rw [packCanon4_mem]; simp [h]

theorem packCanon6_keep (s : JState 64) (b : String) (o : Int) (h : ¬(b = "%rdi" ∧ o = 24)) :
    (runBlock s packCanon6).mem b o = s.mem b o := by
  rw [packCanon6_mem]; simp [h]

theorem packCanon2_out (s : JState 64) :
    (runBlock s packCanon2).mem "%rdi" 0 = s.mem "%rsi" 0 := rfl

theorem packCanon3_out (s : JState 64) :
    (runBlock s packCanon3).mem "%rdi" 8 = s.mem "%rsi" 8 := rfl

theorem packCanon4_out (s : JState 64) :
    (runBlock s packCanon4).mem "%rdi" 16 = s.mem "%rsi" 16 := rfl

theorem packCanon6_out (s : JState 64) :
    (runBlock s packCanon6).mem "%rdi" 24
      = s.regs "%rsi" + s.regs "%rdx" <<< 63 := rfl

/-! ## The block over the name-keyed machine -/

/-- **The canonical block over the name-keyed machine.** The four limbs at the bank `%rsi`
    reach the bank `%rdi`, and the low bit of the word at `(%rdx, 0)` is added into the top
    bit of the fourth limb. -/
theorem packSign_nameKeyed (st : JState 64) :
    (runBlock st (canonD shippedBank
        Ed25519PackSignShipped.ed25519PackSignShippedBlock)).mem "%rdi" 0 = st.mem "%rsi" 0
      ∧ (runBlock st (canonD shippedBank
          Ed25519PackSignShipped.ed25519PackSignShippedBlock)).mem "%rdi" 8
        = st.mem "%rsi" 8
      ∧ (runBlock st (canonD shippedBank
          Ed25519PackSignShipped.ed25519PackSignShippedBlock)).mem "%rdi" 16
        = st.mem "%rsi" 16
      ∧ (runBlock st (canonD shippedBank
          Ed25519PackSignShipped.ed25519PackSignShippedBlock)).mem "%rdi" 24
        = st.mem "%rsi" 24 + (st.mem "%rdx" 0 &&& 1) <<< 63 := by
  rw [packCanon_eq, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
    runBlock_append, runBlock_append]
  set s1 := runBlock st packCanon1 with hs1
  set s2 := runBlock s1 packCanon2 with hs2
  set s3 := runBlock s2 packCanon3 with hs3
  set s4 := runBlock s3 packCanon4 with hs4
  set s5 := runBlock s4 packCanon5 with hs5
  set s6 := runBlock s5 packCanon6 with hs6
  have k7 : ∀ (b : String) (o : Int), (runBlock s6 packCanon7).mem b o = s6.mem b o :=
    fun b o => by rw [packCanon7_mem]
  have k5 : ∀ (b : String) (o : Int), s5.mem b o = s4.mem b o :=
    fun b o => by rw [hs5, packCanon5_mem]
  have y : ∀ o : Int, s4.mem "%rsi" o = st.mem "%rsi" o := by
    intro o
    rw [hs4, packCanon4_keep _ _ _ (by simp), hs3, packCanon3_keep _ _ _ (by simp),
      hs2, packCanon2_keep _ _ _ (by simp), hs1, packCanon1_keep _ _ _ (by simp)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [k7, hs6, packCanon6_keep _ _ _ (by simp), k5, hs4,
      packCanon4_keep _ _ _ (by simp), hs3, packCanon3_keep _ _ _ (by simp), hs2,
      packCanon2_out, hs1, packCanon1_keep _ _ _ (by simp)]
  · rw [k7, hs6, packCanon6_keep _ _ _ (by simp), k5, hs4,
      packCanon4_keep _ _ _ (by simp), hs3, packCanon3_out, hs2,
      packCanon2_keep _ _ _ (by simp), hs1, packCanon1_keep _ _ _ (by simp)]
  · rw [k7, hs6, packCanon6_keep _ _ _ (by simp), k5, hs4, packCanon4_out, hs3,
      packCanon3_keep _ _ _ (by simp), hs2, packCanon2_keep _ _ _ (by simp), hs1,
      packCanon1_keep _ _ _ (by simp)]
  · rw [k7, hs6, packCanon6_out, hs5, packCanon5_rsi, packCanon5_rdx, y,
      show s4.mem "%rdx" 0 = st.mem "%rdx" 0 from by
        rw [hs4, packCanon4_keep _ _ _ (by simp), hs3, packCanon3_keep _ _ _ (by simp),
          hs2, packCanon2_keep _ _ _ (by simp), hs1, packCanon1_keep _ _ _ (by simp)]]

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignNameKeyed
