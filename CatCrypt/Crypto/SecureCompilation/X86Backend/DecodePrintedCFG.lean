/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr

@[expose] public section

set_option autoImplicit false

/-!
# The decoded bytes of a printed physical body simulate its run on the address machine

`VIR.JasminLsemAddrRun.runA` runs a printed physical body on the address machine, with the
program counter on the body's instructions. The function bytes of the body decode to a program
of the machine `RInstrAddrMem.aMachine` whose instructions are, in order, the frame `lea`, the
decoded instructions of each body instruction, the closing `lea` and `ret`; a conditional
branch decodes to a `jcc` to the decoded index of the first definition of its label. This
module relates the two runs instruction by instruction, for any control flow: instruction `k`
of the body corresponds to decoded index `posOf shs k`, an arm of
`DecodePrintedAddr` is simulated by its decoded instructions, a label by no instruction, and
a branch on the zero flag by its `jcc`, whose flag the compare before it fixes.

## The class

`printedAddrB` is decided on the body: it is decodable (`DecodeLayout.decodableLcmd`), ends in
the return, every other instruction is an `Lopn` read into an arm whose conditions hold, a
label, or a branch `Lcond Z`/`Lcond NZ` to a label the body defines, and every branch directly
follows a compare.

## The red-zone word

The widening multiply with coincident destinations saves a scratch register in the eight
bytes at `-128` from the stack register. The memories are related outside that word, and an
indexed load of the run must read outside it (`RunSafe`, `LoadSafeAt`), a condition on the
address-machine run alone.

## Main results

* `posOf`, `blkOf`, `expectedFrom_fundef`: the program the function bytes of a body decode
  to, as the frame `lea`, the decoded instructions of each body instruction with each branch
  resolved to the decoded index `posOf` of its target label, the closing `lea` and `ret`.
* `labelPos_fundef`: a label resolves to the decoded index of its first definition.
* `run_sim`: from instruction `k`, a terminating run of the address machine is matched by a
  path of the machine from `posOf shs k` to the closing `lea`, ending in `ACorr`.
* `printedAddr_sim_noCall`, `printedAddr_sim`: for every body in `printedAddrB`, every
  terminating run of the address machine from the identity correspondence is matched by a
  halting run of `aMachine` without a call on the
  decoded function bytes, with the stack register restored, every general-purpose name
  holding the value of its machine register, and the memories agreeing outside the red-zone
  word.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. The decoded program of a body, instruction by instruction -/

/-- The number of decoded instructions of a shape. -/
def nOf : DShape → Nat
  | .one .skip => 0
  | .one _ => 1
  | .ops pcs => pcs.length

/-- The decoded index of instruction `k` of a body with shapes `shs`: the frame `lea`, then
    the decoded instructions of the instructions before `k`. -/
def posOf (shs : List DShape) (k : Nat) : Nat := 1 + ((shs.take k).map nOf).sum

/-- The decoded instructions of one instruction of shape `sh` in `body`, a branch or a call
    resolved to the decoded index of the first definition of its target label. -/
def blkOf (body : Lcmd) (shs : List DShape) : DShape → List RInstr
  | .one (.jcc cc l) => [.jcc cc (posOf shs ((labelAt body l).getD 0))]
  | .one (.call l) => [.call (posOf shs ((labelAt body l).getD 0))]
  | sh => sh.ops'.map .op

theorem blkOf_length (body : Lcmd) (shs : List DShape) (sh : DShape) :
    (blkOf body shs sh).length = nOf sh := by
  rcases sh with (_ | _ | _ | _) | pcs <;> simp [blkOf, nOf, DShape.ops']

theorem decCount_dItems (P : Params) (off : Nat) (i : Linstr) (sh : DShape) :
    decCount (dItems P off i sh) = nOf sh := by
  rcases sh with (_ | _ | _ | _) | pcs
  · simp [dItems, decCount, nOf, Shape.dec]
  · simp [dItems, decCount, nOf, Shape.dec]
  · simp [dItems, decCount, nOf, Shape.dec]
  · simp [dItems, decCount, nOf, Shape.dec]
  · simp only [dItems, nOf]
    induction pcs with
    | nil => rfl
    | cons p ps ih => simp [decCount, ih]; omega

theorem decCount_itemsFromL (P : Params) :
    ∀ (b : Lcmd) (s : List DShape) (off : Nat), b.length = s.length →
      decCount (itemsFromL P off b s) = (s.map nOf).sum := by
  intro b
  induction b with
  | nil =>
    intro s off hl
    cases s with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons i b ih =>
    intro s off hl
    cases s with
    | nil => simp at hl
    | cons sh s =>
      simp only [itemsFromL, decCount_append, decCount_dItems, List.map_cons, List.sum_cons]
      rw [ih s _ (by simpa using hl)]

/-- The expected program of two item lists, one after the other. -/
theorem expectedFrom_append (all : List Item) :
    ∀ (xs ys : List Item), expectedFrom all (xs ++ ys)
      = (expectedFrom all xs).bind fun a => (expectedFrom all ys).map (a ++ ·) := by
  intro xs
  induction xs with
  | nil => intro ys; cases h : expectedFrom all ys <;> simp [expectedFrom, h]
  | cons it xs ih =>
    intro ys
    rw [List.cons_append, expectedFrom, expectedFrom]
    split
    · exact ih ys
    · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
    · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
    · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
    · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
    · split
      · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
      · rfl
    · split
      · rw [ih ys]; cases expectedFrom all xs <;> cases expectedFrom all ys <;> simp
      · rfl

/-- The label a shape branches to or calls. -/
def shTarget : DShape → Option LLabel
  | .one sh => sh.target
  | .ops _ => none

/-- The branch targets of the shapes `shs` of `body` resolve, in the item list `all`, to the
    decoded index of the first definition of their label. -/
def TargetsOK (body : Lcmd) (shs : List DShape) (all : List Item) : Prop :=
  ∀ sh ∈ shs, ∀ l, shTarget sh = some l →
    ∃ off, labelPos l 0 0 all = some (posOf shs ((labelAt body l).getD 0), off)

theorem expectedFrom_dItems {body : Lcmd} {shs : List DShape} {all : List Item} (P : Params)
    (off : Nat) (i : Linstr) (sh : DShape)
    (hT : ∀ l, shTarget sh = some l →
      ∃ o, labelPos l 0 0 all = some (posOf shs ((labelAt body l).getD 0), o)) :
    expectedFrom all (dItems P off i sh) = some (blkOf body shs sh) := by
  rcases sh with (_ | x | ⟨cc, l⟩ | l) | pcs
  · simp [dItems, expectedFrom, Shape.dec, blkOf, DShape.ops']
  · simp [dItems, expectedFrom, Shape.dec, blkOf, DShape.ops']
  · obtain ⟨o, ho⟩ := hT l rfl
    simp [dItems, expectedFrom, Shape.dec, Shape.target, blkOf, ho]
  · obtain ⟨o, ho⟩ := hT l rfl
    simp [dItems, expectedFrom, Shape.dec, Shape.target, blkOf, ho]
  · simp only [dItems, blkOf, DShape.ops']
    clear hT
    induction pcs with
    | nil => rfl
    | cons p ps ih => simp [expectedFrom, ih, List.map_map]

theorem expectedFrom_itemsFromL {body : Lcmd} {shs : List DShape} {all : List Item}
    (P : Params) (hT : TargetsOK body shs all) :
    ∀ (b : Lcmd) (s : List DShape) (off : Nat), b.length = s.length → (∀ sh ∈ s, sh ∈ shs) →
      expectedFrom all (itemsFromL P off b s) = some (s.flatMap (blkOf body shs)) := by
  intro b
  induction b with
  | nil =>
    intro s off hl _
    cases s with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons i b ih =>
    intro s off hl hs
    cases s with
    | nil => simp at hl
    | cons sh s =>
      simp only [itemsFromL, expectedFrom_append,
        expectedFrom_dItems P off i sh (hT sh (hs sh (by simp))), Option.bind_some,
        ih s _ (by simpa using hl) (fun x hx => hs x (by simp [hx])), Option.map_some,
        List.flatMap_cons]

/-- **The decoded program of a body.** When the branch targets resolve, the item list of the
    function bytes of `body` with shapes `shs` denotes the frame `lea`, the decoded
    instructions `blkOf` of each instruction, the closing `lea` and `ret`. -/
theorem expectedFrom_fundef (body : Lcmd) (shs : List DShape) (hl : body.length = shs.length)
    (hT : TargetsOK body shs (fundefItemsL body shs)) :
    expectedFrom (fundefItemsL body shs) (fundefItemsL body shs)
      = some (.op (leaFrame (-(Int.ofNat (Params.ofBody body).frame)))
        :: (shs.flatMap (blkOf body shs)
          ++ [.op (leaFrame (Int.ofNat (Params.ofBody body).frame)), .ret])) := by
  conv_lhs => arg 2; rw [fundefItemsL]
  rw [expectedFrom, show (mkLea (-(Int.ofNat (Params.ofBody body).frame))).dec
      = some (.op (leaFrame (-(Int.ofNat (Params.ofBody body).frame)))) from rfl]
  simp only [expectedFrom_append,
    expectedFrom_itemsFromL (Params.ofBody body) hT body shs 0 hl (fun _ h => h),
    Option.bind_some]
  simp [expectedFrom, mkLea, mkRet, leaFrame]

/-! ## 2. Labels -/

theorem shapesOf_spec (P : Params) :
    ∀ (b : Lcmd) (s : List DShape), shapesOf P b = some s →
      s.length = b.length ∧ ∀ k (hk : k < b.length) (hs : k < s.length),
        shapeOf P b[k].li_i = some s[k] := by
  intro b
  induction b with
  | nil =>
    intro s h
    simp only [shapesOf, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
  | cons i b ih =>
    intro s h
    simp only [shapesOf] at h
    split at h
    · rename_i sh s' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hl, hk⟩ := ih s' h2
      refine ⟨by simp [hl], fun k hk' hs => ?_⟩
      cases k with
      | zero => exact h1
      | succ k => exact hk k (by simpa using hk') (by simpa using hs)
    · cases h

theorem isLabelB_iff (l : LLabel) (i : LinstrR) : isLabelB l i = true ↔ labelOf i = some l := by
  cases i <;> simp [isLabelB, labelOf]

/-- The first definition of a label. -/
theorem labelAt_spec {body : Lcmd} {l : LLabel} {p : Nat} (h : labelAt body l = some p) :
    ∃ hp : p < body.length, isLabelB l body[p].li_i = true
      ∧ ∀ q (hq : q < p), isLabelB l (body[q]'(by omega)).li_i = false := by
  unfold labelAt at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hp, h1, h2⟩ := h
  exact ⟨hp, h1, fun q hq => by simpa using h2 q hq⟩

theorem dItems_label (P : Params) (off : Nat) (i : Linstr) (sh : DShape) :
    ∀ it ∈ dItems P off i sh, it.label = none ∨ it.label = labelOf i.li_i := by
  intro it hit
  cases sh with
  | one sh =>
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    exact Or.inr rfl
  | ops pcs =>
    simp only [dItems, List.mem_map] at hit
    obtain ⟨p, _, rfl⟩ := hit
    exact Or.inl rfl

theorem itemsFromL_noLabel (P : Params) (l : LLabel) :
    ∀ (b : Lcmd) (s : List DShape) (off : Nat), (∀ i ∈ b, isLabelB l i.li_i = false) →
      ∀ it ∈ itemsFromL P off b s, it.label ≠ some l := by
  intro b
  induction b with
  | nil => intro s off _ it hit; cases s <;> simp [itemsFromL] at hit
  | cons i b ih =>
    intro s off hb it hit
    cases s with
    | nil => simp [itemsFromL] at hit
    | cons sh s =>
      simp only [itemsFromL, List.mem_append] at hit
      rcases hit with hit | hit
      · rcases dItems_label P off i sh it hit with h | h
        · rw [h]; simp
        · rw [h]
          intro he
          have := (isLabelB_iff l i.li_i).mpr he
          rw [hb i (by simp)] at this
          cases this
      · exact ih s _ (fun j hj => hb j (by simp [hj])) it hit

/-- **A label resolves to the decoded index of its first definition.** -/
theorem labelPos_fundef {body : Lcmd} {shs : List DShape}
    (hs : shapesOf (Params.ofBody body) body = some shs) {l : LLabel} {p : Nat}
    (hp : labelAt body l = some p) :
    ∃ off, labelPos l 0 0 (fundefItemsL body shs) = some (posOf shs p, off) := by
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hs
  obtain ⟨hpl, hlab, hbefore⟩ := labelAt_spec hp
  have hps : p < shs.length := by omega
  have hsp := hsh p hpl hps
  have hlab' := (isLabelB_iff l _).mp hlab
  have hskip : shs[p] = .one .skip := by
    cases hb : body[p].li_i <;> rw [hb] at hsp hlab' <;> simp [shapeOf, labelOf] at hsp hlab'
    exact hsp.symm
  set P := Params.ofBody body
  have hsplit : itemsFromL P 0 body shs
      = itemsFromL P 0 (body.take p) (shs.take p)
        ++ itemsFromL P (0 + lenFrom P 0 (body.take p)) (body.drop p) (shs.drop p) := by
    rw [← itemsFromL_append P _ _ _ _ (by simp [List.length_take]; omega), List.take_append_drop,
      List.take_append_drop]
  have hpre : ∀ i ∈ body.take p, isLabelB l i.li_i = false := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hi
    simp only [List.length_take] at hq
    simpa using hbefore q (by omega)
  rw [List.drop_eq_getElem_cons hpl, List.drop_eq_getElem_cons hps, hskip] at hsplit
  unfold fundefItemsL
  rw [hsplit]
  simp only [labelPos, mkLea, reduceCtorEq, ite_false, Option.isSome_some, ite_true]
  rw [List.append_assoc, labelPos_append_of_ne _ _ _
    (itemsFromL_noLabel P l _ _ _ hpre), decCount_itemsFromL P _ _ _ (by simp; omega)]
  simp only [itemsFromL, dItems, List.cons_append, labelPos, hlab', ite_true]
  simp only [posOf, Option.some.injEq, Prod.mk.injEq]
  exact ⟨_, trivial, rfl⟩

/-! ## 3. Indexing the decoded program -/

theorem posOf_succ (shs : List DShape) (k : Nat) (hk : k < shs.length) :
    posOf shs (k + 1) = posOf shs k + nOf shs[k] := by
  simp only [posOf, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem posOf_le (shs : List DShape) (k : Nat) : 1 ≤ posOf shs k := by
  simp [posOf]

/-- The decoded program around instruction `k`: the instructions before it, its decoded
    instructions from index `posOf shs k`, and the instructions after it. -/
theorem prog_split (body : Lcmd) (shs : List DShape) (a b : JInstr 64) (k : Nat)
    (hk : k < shs.length) :
    ∃ A B, (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
        = A ++ blkOf body shs shs[k] ++ B ∧ A.length = posOf shs k := by
  refine ⟨.op a :: (shs.take k).flatMap (blkOf body shs),
    (shs.drop (k + 1)).flatMap (blkOf body shs) ++ [.op b, .ret], ?_, ?_⟩
  · generalize blkOf body shs = f
    have e : shs.flatMap f = (shs.take k).flatMap f ++ (f shs[k] ++ (shs.drop (k + 1)).flatMap f) := by
      conv_lhs => rw [← List.take_append_drop k shs]
      rw [List.flatMap_append, List.drop_eq_getElem_cons hk, List.flatMap_cons]
    rw [e]
    simp
  · simp [posOf, List.length_flatMap, blkOf_length, Nat.add_comm]

/-- The decoded program from the index of the last instruction of a body whose last shape is
    the skip: the closing `lea` and `ret`. -/
theorem prog_end (body : Lcmd) (shs : List DShape) (a b : JInstr 64) (hn : 0 < shs.length)
    (hlast : shs[shs.length - 1] = .one .skip) :
    (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs (shs.length - 1)]?
        = some (.op b)
      ∧ (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs
          (shs.length - 1) + 1]? = some .ret := by
  have hlen : posOf shs (shs.length - 1) = 1 + (shs.flatMap (blkOf body shs)).length := by
    have h1 := posOf_succ shs (shs.length - 1) (by omega)
    rw [hlast, show shs.length - 1 + 1 = shs.length by omega] at h1
    simp only [nOf, Nat.add_zero] at h1
    rw [← h1]
    simp [posOf, List.length_flatMap, blkOf_length]
  rw [hlen]
  generalize (shs.flatMap (blkOf body shs)) = L
  constructor
  · rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
    simp
  · rw [show 1 + L.length + 1 = (L.length + 1) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (by omega)]
    simp

/-! ## 4. The covered bodies -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (aMachine_step_op)

/-- An instruction of a printed body other than its closing return, in the covered fragment:
    an `Lopn` read into an arm whose conditions hold, a label, or a conditional branch on the
    zero flag (`Z` or `NZ`) to a label the body defines. -/
def instrOKB (body : Lcmd) (P : Params) : LinstrR → Bool
  | .Lopn ds o ss =>
      match classifyA (.Lopn ds o ss) with
      | some a => a.ok P
      | none => false
  | .Llabel _ _ => true
  | .Lcond (.reg cc) l => (condPol cc).isSome && (labelAt body l).isSome
  | _ => false

/-- A conditional branch at position `k` of `body` follows a compare. -/
def condPrevB (body : Lcmd) (k : Nat) : Bool :=
  match body[k]? with
  | some ⟨_, .Lcond _ _⟩ =>
      k != 0 && (match body[k - 1]? with
        | some j => (classifyA j.li_i).any cmpArmB
        | none => false)
  | _ => true

/-- **The covered printed bodies**: decodable, ending in the return, every other instruction
    in the covered fragment, and every conditional branch directly after a compare. -/
def printedAddrB (body : Lcmd) : Bool :=
  decodableLcmd body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => instrOKB body (Params.ofBody body) i.li_i)
    && (List.range body.length).all (condPrevB body)

/-- An indexed load at the program counter of `s`, read through `normA` (so tagged or
    untagged), reads an address whose eight bytes are disjoint from the red-zone word at
    `rsp`. -/
def LoadSafeAt (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  ∀ ii x D B I, body[s.reg.lpc]? = some ⟨ii, x⟩ →
    normA x = .Lopn [.reg D] "LOADIDX" [.arrIdx B I 8] →
    ∀ p vi, s.reg.getW B 64 = some p → s.reg.getW I 64 = some vi →
      Disjoint8 (redW rsp) (p + BitVec.ofNat 64 (8 * vi.toNat))

/-- Every state that a run of at most `fuel` steps of the address machine on `body` steps
    from satisfies `Q`. -/
def RunSafe (frame : String → Option (BitVec 64)) (body : Lcmd) (Q : LstateA → Prop) :
    Nat → LstateA → Bool → Prop
  | 0, _, _ => True
  | fuel + 1, s, zf =>
      Q s ∧ ∀ s' zf', stepA frame body s zf = some (s', zf') → RunSafe frame body Q fuel s' zf'

theorem acorr_setLpc {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorr rsp sa s)
    (p : Nat) : ACorr rsp sa (s.setLpc p) :=
  ⟨h.regs, h.sp, h.mem⟩

theorem blkOf_lopn {body : Lcmd} {shs : List DShape} {P : Params} {ds : List LOperand}
    {o : String} {ss : List LOperand} {sh : DShape} (h : shapeOf P (.Lopn ds o ss) = some sh) :
    blkOf body shs sh = sh.ops'.map .op ∧ nOf sh = sh.ops'.length := by
  rcases shapeOfBytes_ok (bs := encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB) h with
    ⟨q, rfl, -, -⟩ | ⟨pcs, rfl, -, -⟩
  · exact ⟨rfl, rfl⟩
  · simp [blkOf, nOf, DShape.ops']

theorem condPol_spec {cc : String} {pol : Bool} (h : condPol cc = some pol) :
    (ccNibble cc = 4 ∧ pol = true) ∨ (ccNibble cc = 5 ∧ pol = false) := by
  unfold condPol at h
  split at h
  · obtain rfl := Option.some.inj h; exact Or.inl ⟨by decide, rfl⟩
  · obtain rfl := Option.some.inj h; exact Or.inr ⟨by decide, rfl⟩
  · cases h

/-- The machine branch on the zero flag: to its target when the flag is the polarity of the
    condition, to the next index otherwise. -/
theorem step_jcc_pol (prog : List RInstr) (pc t : Nat) (sa : AState) (cc : String) (pol : Bool)
    (hpol : condPol cc = some pol) (hj : prog[pc]? = some (.jcc (ccNibble cc) t)) :
    RInstrSemantics.step aMachine prog pc sa
      = some (.go (if sa.flags.zf.getD false = pol then t else pc + 1) sa) := by
  have hf : (aMachine.view sa).flagB (·.zf) = sa.flags.zf.getD false := rfl
  rcases condPol_spec hpol with ⟨hn, rfl⟩ | ⟨hn, rfl⟩
  · rw [hn] at hj
    simp only [RInstrSemantics.step, hj, condtOfNibble_four, Option.map_some, condB_e, hf]
    cases sa.flags.zf.getD false <;> rfl
  · rw [hn] at hj
    simp only [RInstrSemantics.step, hj, condtOfNibble_five, Option.map_some, condB_ne, hf]
    cases sa.flags.zf.getD false <;> rfl

/-! ## 5. The run -/

/-- The instruction is a conditional branch. -/
def isCondB : LinstrR → Bool
  | .Lcond _ _ => true
  | _ => false

/-- The facts of a covered body that the simulation reads. -/
structure BodyFacts (body : Lcmd) (shs : List DShape) : Prop where
  /-- The shapes of the body. -/
  shapes : shapesOf (Params.ofBody body) body = some shs
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret
  /-- Every other instruction is in the covered fragment. -/
  instr : ∀ k (hk : k + 1 < body.length),
    instrOKB body (Params.ofBody body) (body[k]'(by omega)).li_i = true
  /-- Every conditional branch follows a compare. -/
  cond : ∀ k, k < body.length → condPrevB body k = true

theorem haltedA_eq_false {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs)
    {s : LstateA} {k : Nat} (hpc : s.reg.lpc = k) (hk : k + 1 < body.length) :
    haltedA body s = false := by
  have hok := hF.instr k hk
  unfold haltedA
  rw [hpc, List.getElem?_eq_getElem (by omega)]
  revert hok
  rcases body[k] with ⟨ii, li⟩
  cases li <;> simp [instrOKB]

theorem classifyA_label (k : LabelKind) (l : LLabel) : classifyA (.Llabel k l) = none := rfl

theorem classifyA_cond (c : LOperand) (l : LLabel) : classifyA (.Lcond c l) = none := rfl

/-- The instruction after a label or a branch is no conditional branch. -/
theorem not_cond_after {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs) {k : Nat}
    (hk : k + 1 < body.length) (h : classifyA (body[k]'(by omega)).li_i = none) :
    isCondB (body[k + 1]'hk).li_i = false := by
  have hc := hF.cond (k + 1) hk
  unfold condPrevB at hc
  rw [List.getElem?_eq_getElem hk] at hc
  revert hc
  rcases hb : body[k + 1] with ⟨ii, li⟩
  cases li <;> simp [isCondB, List.getElem?_eq_getElem (show k < body.length by omega), h]

/-- **The run on both machines.** From states related by `ACorr` at instruction `k` of a
    covered body, with the machine zero flag equal to the flag at a conditional branch, every
    terminating run of the address machine whose indexed loads avoid the red-zone word is
    matched by a path of the machine on the decoded program from the index of `k` to the index
    of the closing return, ending in states related by `ACorr`. -/
theorem run_sim {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs) (rsp : BitVec 64)
    (a b : JInstr 64) :
    ∀ (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = k → (hk : k < body.length) → ACorr rsp sa s →
      (isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf) →
      runA (frameP (Params.ofBody body) rsp) body fuel s zf = some t →
      RunSafe (frameP (Params.ofBody body) rsp) body (LoadSafeAt rsp body) fuel s zf →
      ∃ sa', Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
          (posOf shs k) sa (posOf shs (body.length - 1)) sa' ∧ ACorr rsp sa' t.1 := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  set prog : List RInstr := .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])
  obtain ⟨hl, hsh⟩ := shapesOf_spec P body shs hF.shapes
  -- the halt at the return
  have hhalt : ∀ (fuel : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = body.length - 1 → ACorr rsp sa s →
      runA frame body fuel s zf = some t →
      ∃ sa', Reaches aMachine prog (posOf shs (body.length - 1)) sa
          (posOf shs (body.length - 1)) sa' ∧ ACorr rsp sa' t.1 := by
    intro fuel sa s zf t hpc hc hrun
    have hh : haltedA body s = true := by
      unfold haltedA
      rw [hpc, List.getElem?_eq_getElem (by have := hF.pos; omega)]
      have := hF.last
      revert this
      rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
      intro h
      simp only at h
      subst h
      rfl
    rw [runA_halt _ _ _ _ _ hh] at hrun
    obtain rfl := Option.some.inj hrun
    exact ⟨sa, .refl _ _, hc⟩
  intro fuel
  induction fuel with
  | zero =>
    intro k sa s zf t hpc hk hc _ hrun _
    by_cases hkn : k + 1 < body.length
    · simp [runA, haltedA_eq_false hF hpc hkn] at hrun
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt 0 sa s zf t hpc hc hrun
  | succ f ih =>
    intro k sa s zf t hpc hk hc hz hrun hsafe
    by_cases hkn : k + 1 < body.length
    swap
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt (f + 1) sa s zf t hpc hc hrun
    rw [runA_step _ _ _ _ _ (haltedA_eq_false hF hpc hkn)] at hrun
    have hok := hF.instr k hkn
    have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
      rw [hpc]; exact List.getElem?_eq_getElem hk
    have hks : k < shs.length := by omega
    have hshk := hsh k hk hks
    obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
    rcases hbk : body[k] with ⟨ii, li⟩
    rw [hbk] at hok hget hshk hz
    simp only at hok hshk hz
    cases li with
    | Lopn ds o ss =>
      simp only [instrOKB] at hok
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        have hsafeA : ar.LoadSafe rsp s := by
          cases ar with
          | ldx D B' I =>
            intro p vi hp hvi
            exact hsafe.1 ii _ D B' I hget
              (by rw [← hia]; simp [AArm.instr, normA, width_tag]) p vi hp hvi
          | _ => trivial
        obtain ⟨s', zf', hst, hc', hzf'⟩ := AArm.sim P rsp ar hok sa s zf hc hsafeA
        have hstep : stepA frame body s zf = some (s', zf') := by
          simp only [stepA, hget]
          rw [← hia, AArm.tagAt_eq, hli]
          exact hst
        rw [hstep, Option.bind_some] at hrun
        have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
        have hz' : isCondB (body[k + 1]'hkn).li_i = true →
            (aMachine.runBlock sa (ar.js P)).flags.zf.getD false = zf' := by
          intro hcnd
          have hc2 := hF.cond (k + 1) hkn
          unfold condPrevB at hc2
          rw [List.getElem?_eq_getElem hkn] at hc2
          revert hc2 hcnd
          rcases body[k + 1] with ⟨ii', li'⟩
          cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk, hbk, hcl]
          exact hzf'
        obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf' t hpc' hkn hc' hz' hrun
          (hsafe.2 s' zf' hstep)
        refine ⟨sa', ?_, hC⟩
        obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
        have hops : shs[k].ops' = ar.js P := AArm.shape_ops hok (by rw [hia]; exact hshk)
        have hprog : prog = A ++ (ar.js P).map RInstr.op ++ B := by
          show RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]) = _
          rw [hsplit, hblk, hops]
        have h0 := reaches_ops aMachine A (ar.js P) B sa
        rw [← hprog, hA] at h0
        have hpos : posOf shs (k + 1) = posOf shs k + (ar.js P).length := by
          rw [posOf_succ shs k hks, hn, hops]
        rw [hpos] at hR
        exact h0.trans hR
      · cases hok
    | Llabel kd l =>
      have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
        unfold stepA
        rw [hget]
        simp only [hpc]
      rw [hstep, Option.bind_some] at hrun
      have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
        intro hcnd
        rw [not_cond_after hF hkn (by rw [hbk]; rfl)] at hcnd
        cases hcnd
      obtain ⟨sa', hR, hC⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t rfl hkn (acorr_setLpc hc _) hz'
        hrun (hsafe.2 _ _ hstep)
      refine ⟨sa', ?_, hC⟩
      rw [posOf_succ shs k hks] at hR
      have hsk : shs[k] = .one .skip := by
        simp [shapeOf] at hshk; exact hshk.symm
      rw [hsk] at hR
      simpa [nOf] using hR
    | Lcond c l =>
      cases c with
      | reg cc =>
        simp only [instrOKB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
          simp [shapeOf] at hshk; exact hshk.symm
        have hj : prog[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
          show (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs k]? = _
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sa.flags.zf.getD false = zf := hz rfl
        have hms := step_jcc_pol prog (posOf shs k) (posOf shs p) sa cc pol hpol hj
        rw [hzf] at hms
        by_cases hzp : zf = pol
        · have hstep : stepA frame body s zf = some (s.setLpc p, zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hp]
          rw [hstep, Option.bind_some] at hrun
          have hz' : isCondB (body[p]'hpl).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            revert hlabp hcnd
            rcases body[p] with ⟨ii', li'⟩
            cases li' <;> simp [isCondB, isLabelB]
          obtain ⟨sa', hR, hC⟩ := ih p sa (s.setLpc p) zf t rfl hpl (acorr_setLpc hc _) hz' hrun
            (hsafe.2 _ _ hstep)
          rw [ite_eq_left hzp] at hms
          exact ⟨sa', .next hms hR, hC⟩
        · have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hpc]
          rw [hstep, Option.bind_some] at hrun
          have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            rw [not_cond_after hF hkn (by rw [hbk]; rfl)] at hcnd
            cases hcnd
          obtain ⟨sa', hR, hC⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t rfl hkn (acorr_setLpc hc _)
            hz' hrun (hsafe.2 _ _ hstep)
          rw [ite_eq_right hzp] at hms
          rw [posOf_succ shs k hks, hsk] at hR
          exact ⟨sa', .next hms (by simpa [nOf] using hR), hC⟩
      | _ => simp [instrOKB] at hok
    | _ => simp [instrOKB] at hok

/-! ## 6. A covered body against its decoded bytes -/

/-- The facts of a body in the class `printedAddrB`. -/
theorem bodyFacts_of {body : Lcmd} (h : printedAddrB body = true) :
    ∃ shs, BodyFacts body shs := by
  simp only [printedAddrB, Bool.and_eq_true, Option.any_eq_true, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hdec, r, hlast, hret⟩, hins⟩, hcond⟩ := h
  have hdec' := hdec
  simp only [decodableLcmd, Bool.and_eq_true] at hdec'
  obtain ⟨shs, hs⟩ := Option.isSome_iff_exists.mp hdec'.1.1.1.1.1
  have hpos : 0 < body.length := by
    cases body with
    | nil => simp at hlast
    | cons _ _ => simp
  refine ⟨shs, ⟨hs, hpos, ?_, fun k hk => ?_, fun k hk => hcond k hk⟩⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    obtain rfl := Option.some.inj hlast
    revert hret
    unfold isRetB
    split <;> simp_all
  · have hm : (body[k]'(by omega)) ∈ body.dropLast := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    exact hins _ hm

/-- The branch targets of a covered body resolve to the decoded index of their label. -/
theorem targetsOK_of {body : Lcmd} {shs : List DShape} (hF : BodyFacts body shs) :
    TargetsOK body shs (fundefItemsL body shs) := by
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  intro sh hm l ht
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hshk := hsh k (by omega) hk
  by_cases hkn : k + 1 < body.length
  · have hok := hF.instr k hkn
    revert hshk hok
    rcases body[k] with ⟨ii, li⟩
    cases li with
    | Lcond c l' =>
      cases c with
      | reg cc =>
        simp only [shapeOf, Option.some.injEq, instrOKB, Bool.and_eq_true,
          Option.isSome_iff_exists]
        intro hsk hok
        rw [← hsk] at ht
        simp only [shTarget, Shape.target, Option.some.injEq] at ht
        subst ht
        obtain ⟨-, p, hp⟩ := hok
        obtain ⟨off, ho⟩ := labelPos_fundef hF.shapes hp
        exact ⟨off, by rw [hp]; exact ho⟩
      | _ => simp [instrOKB]
    | Lopn ds o ss =>
      intro hsk _
      rcases shapeOfBytes_ok (bs := encodeLopn _ _ (.Lopn ds o ss) _) hsk with
        ⟨q, he, -, -⟩ | ⟨pcs, he, -, -⟩ <;> rw [he] at ht <;> simp [shTarget, Shape.target] at ht
    | Llabel kd l' =>
      intro hsk _
      simp only [shapeOf, Option.some.injEq] at hsk
      rw [← hsk] at ht
      simp [shTarget, Shape.target] at ht
    | _ => simp [instrOKB]
  · have hk' : k = body.length - 1 := by omega
    subst hk'
    have hlast := hF.last
    revert hshk hlast
    rcases body[body.length - 1]'(by omega) with ⟨ii, li⟩
    intro hshk hlast
    simp only at hlast hshk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hshk
    rw [← hshk] at ht
    simp [shTarget, Shape.target] at ht

/-- The address of the frame after the prologue of `body`, from the entry machine state. -/
def frameRsp (body : Lcmd) (sa : AState) : BitVec 64 :=
  sa.regs "%rsp" + BitVec.ofInt 64 (-(Int.ofNat (Params.ofBody body).frame))

/-- **The decoded bytes of a covered printed body simulate its run on the address machine.**
    For every body in the class `printedAddrB`, from a machine state `sa` and an address state
    `s` at program counter `0` in which every general-purpose name `R` holds the value of the
    machine register `phys R` and the memories are equal, every terminating run of the
    address machine on the body, with frame words at their addresses below the entry stack
    register, whose indexed loads read outside the red-zone word, is matched by a halting run
    of the machine on the decoded function bytes. At the end the stack register is restored,
    every general-purpose name holds the value of its machine register, and the memories agree
    outside the red-zone word. The halting run makes no call. -/
theorem printedAddr_sim_noCall (body : Lcmd) (h : printedAddrB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool)
    (hrun : runA (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (LoadSafeAt (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ HaltsNoCall aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ R, gpOk R = true → t.1.reg.getW R 64 = some (sa'.regs (phys R)))
      ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → t.1.mem x = sa'.mem x) := by
  obtain ⟨shs, hF⟩ := bodyFacts_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrB, Bool.and_eq_true] at h
    exact h.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  set P := Params.ofBody body
  set F := P.frame
  set rsp := frameRsp body sa with hrsp
  set prog : List RInstr := .op (leaFrame (-(Int.ofNat F)))
    :: (shs.flatMap (blkOf body shs) ++ [.op (leaFrame (Int.ofNat F)), .ret]) with hprog
  have hdecode : decodeLprog (encodeLfundefBytes body) = some prog := by
    rw [decodeLprog_encodeLfundefBytes hdec, fundefLayout, fundefItems,
      show shapesD P body = shs by
        rw [shapesD, show shapesOf P body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_of hF)
  -- the prologue
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  have hc0 : ACorr rsp sa1 s :=
    { regs := fun R hR => by rw [hent R hR, hl1, ite_eq_right (fun e => (gpFacts hR).physNe e)]
      sp := by rw [hl1, ite_eq_left rfl, hrsp]; rfl
      mem := fun x _ => by rw [hmem, hm1] }
  have hz0 : isCondB (body[0]'hF.pos).li_i = true → sa1.flags.zf.getD false = zf := by
    intro hcnd
    have hc := hF.cond 0 hF.pos
    revert hc hcnd
    unfold condPrevB
    rw [List.getElem?_eq_getElem hF.pos]
    rcases body[0]'hF.pos with ⟨ii, li⟩
    cases li <;> simp [isCondB]
  obtain ⟨sa2, hR, hc2⟩ := run_sim hF rsp _ _ fuel 0 sa1 s zf t hpc hF.pos hc0 hz0 hrun hsafe
  -- the epilogue
  have hskip : shs[shs.length - 1]'(by have := hF.pos; omega) = .one .skip := by
    have hsk := hsh (body.length - 1) (by have := hF.pos; omega) (by have := hF.pos; omega)
    have hlast := hF.last
    revert hsk hlast
    rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
    intro hsk hlast
    simp only at hlast hsk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hsk
    simp only [hl] at hsk ⊢
    exact hsk.symm
  obtain ⟨he1, he2⟩ := prog_end body shs (leaFrame (-(Int.ofNat F))) (leaFrame (Int.ofNat F))
    (by have := hF.pos; omega) hskip
  rw [hl] at he1 he2
  obtain ⟨hl2, hm2⟩ := evalInstrA_leaFrame sa2 (Int.ofNat F)
  refine ⟨prog, evalInstrA sa2 (leaFrame (Int.ofNat F)), hdecode,
    ⟨posOf shs (body.length - 1) + 1, ?_, he2⟩, ?_, fun R hR => ?_, fun x hx => ?_⟩
  · have h01 : Reaches aMachine prog 0 sa 1 sa1 := .single (aMachine_step_op prog 0 sa _ rfl)
    have hpos0 : posOf shs 0 = 1 := by simp [posOf]
    rw [hpos0] at hR
    exact (h01.trans hR).trans (.single (aMachine_step_op prog _ sa2 _ he1))
  · rw [hl2, ite_eq_left rfl, hc2.sp, hrsp, frameRsp]
    simp [F, P, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · rw [hl2, ite_eq_right (fun e => (gpFacts hR).physNe e)]
    exact hc2.regs R hR
  · rw [hm2]
    exact hc2.mem x hx

/-- **The decoded bytes of a covered printed body simulate its run on the address
    machine.** The statement of `printedAddr_sim_noCall` with the halting run as a halting run
    through calls (`halts_of_haltsNoCall`). -/
theorem printedAddr_sim (body : Lcmd) (h : printedAddrB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R)))
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool)
    (hrun : runA (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (LoadSafeAt (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ R, gpOk R = true → t.1.reg.getW R 64 = some (sa'.regs (phys R)))
      ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → t.1.mem x = sa'.mem x) := by
  obtain ⟨prog, sa', hd, hh, h1, h2, h3⟩ :=
    printedAddr_sim_noCall body h sa s zf hpc hent hmem fuel t hrun hsafe
  exact ⟨prog, sa', hd, halts_of_haltsNoCall hh, h1, h2, h3⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
