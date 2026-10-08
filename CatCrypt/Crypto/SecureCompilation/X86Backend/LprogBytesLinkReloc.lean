/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig

/-!
# Decoding a function body with cross-function calls, followed by its callee

`LprogBytes.encodeLfundefBytesReloc symBase body` lays down a function whose remote
calls `Lcall _ (f, _)` (`f` nonempty) are the five-byte `call rel32` with displacement
`symBase f - instrEnd`, both counted from the first byte after the frame `leaq`. This
module decodes those bytes followed by the bytes `cb` of a callee block.

## The encoder as an item list

`encodeFromReloc` is the fold of `LprogBytes.encodeLcmdReloc` as a recursion
(`encodeLcmdReloc_eq_encodeFromReloc`). It agrees with `LprogBytesDecode.encodeFrom`
except at a remote call, where the displacement is `relocDisp` and the encoder's offset
advances by five. `itemsFromReloc` is the item list of a body: a remote call is an item
without target label, every other position is the item of `LprogBytesDecode.itemsFrom`.
`fundefItemsReloc` adds the frame `leaq`, the closing `leaq` and `ret`
(`encodeLfundefBytesReloc_eq_itemBytes`).

## Resolution

Byte offsets become instruction indices in `LprogBytesDecode.resolveAll`: a call ending
at byte offset `e` with displacement `d` receives the index of the first instruction of
the whole stream that starts at byte `e + d`. `branchOKReloc all k L` requires of a call
without target label that `e + d = L`, and of every other branch what
`LprogBytesDecode.branchOK` requires. `expectedReloc all k L` is the program of an item
list in which a call without target label is `call k`. With `L` the byte length of the
items and `k` their instruction count, the first instruction of `cb` starts at byte `L`
and has index `k` in the decoded stream.

## Main results

* `decodeLprog_items_linked`: the bytes of an item list followed by a nonempty block
  that decodes to `q` decode to `prog ++ shiftProg prog.length q`, where `prog` is
  `expectedReloc` of the items and each call without target label is
  `call prog.length`.
* `decodeLprog_fundefReloc_append`: the same for `encodeLfundefBytesReloc symBase body`.
* `relocDisp_lands`: the displacement of a remote call whose symbol base is the byte
  length of the function, less the frame `leaq`, ends on that byte length.
* `haltsC_fundefReloc_linked`: a run of the decoded caller with the callee block as an
  oracle at the target `prog.length` is a run through calls of the program the linked
  bytes decode to.
* `linkedProg_of_items`, `linkedProg_of_bytes`: the program of the relocated item list of
  a body with the facts `CallFacts` satisfies `LinkedProg`: the decoded instructions of
  each instruction of the covered fragment at the index `DecodePrintedCFG.posOf`, `call K`
  at the index of a remote call, and the closing `lea` and `ret`.
* `linked_step`, `linked_halt`, `linked_call`, `linked_seg`: the byte simulation of a step
  of the address machine, of the closing return and of a call of such a body on a program
  that satisfies `LinkedProg`, under every oracle.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The relocating body encoder as a recursion -/

/-- The displacement `encodeLcmdReloc` writes for a remote transfer to `f` at body offset
    `off`: the symbol base less the end of the five-byte instruction, `0` for a symbol
    without base. -/
def relocDisp (symBase : String → Option Int) (off : Nat) (f : String) : Int :=
  match symBase f with
  | some delta => delta - Int.ofNat (off + 5)
  | none => 0

/-- One step of the fold of `encodeLcmdReloc`. -/
def relocStep (symBase : String → Option Int) (P : Params)
    (acc : Nat × List (BitVec 8) × List (Nat × String)) (instr : Linstr) :
    Nat × List (BitVec 8) × List (Nat × String) :=
  match remoteSym instr.li_i with
  | some f =>
      match symBase f with
      | some delta =>
          (acc.1 + 5,
            acc.2.1 ++ encodeRemoteCF (delta - Int.ofNat (acc.1 + 5)) instr.li_i, acc.2.2)
      | none =>
          (acc.1 + 5, acc.2.1 ++ encodeRemoteCF 0 instr.li_i,
            acc.2.2 ++ [(acc.1 + remoteRel32FieldOff instr.li_i, f)])
  | none =>
      (acc.1 + P.lenAt acc.1 instr.li_i, acc.2.1 ++ P.encAt acc.1 instr.li_i, acc.2.2)

/-- The bytes of `encodeLcmdReloc` as a recursion from a starting offset. -/
def encodeFromReloc (symBase : String → Option Int) (P : Params) : Nat → Lcmd → List (BitVec 8)
  | _, [] => []
  | off, instr :: rest =>
      match remoteSym instr.li_i with
      | some f =>
          encodeRemoteCF (relocDisp symBase off f) instr.li_i
            ++ encodeFromReloc symBase P (off + 5) rest
      | none =>
          P.encAt off instr.li_i ++ encodeFromReloc symBase P (off + P.lenAt off instr.li_i) rest

theorem relocStep_fold_eq (symBase : String → Option Int) (P : Params) :
    ∀ (body : Lcmd) (off : Nat) (acc : List (BitVec 8)) (rl : List (Nat × String)),
      (body.foldl (relocStep symBase P) (off, acc, rl)).2.1
        = acc ++ encodeFromReloc symBase P off body := by
  intro body
  induction body with
  | nil => intro off acc rl; simp [encodeFromReloc]
  | cons instr rest ih =>
    intro off acc rl
    rw [List.foldl_cons]
    cases h : remoteSym instr.li_i with
    | none => simp only [relocStep, h, ih, encodeFromReloc, List.append_assoc]
    | some f =>
      cases hs : symBase f with
      | none => simp only [relocStep, h, hs, ih, encodeFromReloc, relocDisp, List.append_assoc]
      | some delta =>
        simp only [relocStep, h, hs, ih, encodeFromReloc, relocDisp, List.append_assoc]

/-- The bytes of `encodeLcmdReloc` are `encodeFromReloc` at offset `0` under the body's
    own parameters. -/
theorem encodeLcmdReloc_eq_encodeFromReloc (symBase : String → Option Int) (body : Lcmd) :
    (encodeLcmdReloc symBase body).1 = encodeFromReloc symBase (Params.ofBody body) 0 body := by
  have h := relocStep_fold_eq symBase (Params.ofBody body) body 0 [] []
  rw [List.nil_append] at h
  rw [← h]
  rfl

/-! ## 2. The item list of a body with remote calls -/

/-- What the relocating encoder needs of one body instruction: a remote transfer is a
    call, and every other instruction has the shape `sh`. -/
def RelocShapeOK (P : Params) (i : LinstrR) (sh : Shape) : Prop :=
  match remoteSym i with
  | some f => ∃ ra l, i = .Lcall ra (f, l)
  | none => ShapeOK P i sh

/-- The item list of a body under the relocating encoder, laid out from body offset
    `off`. A remote call carries no target label. -/
def itemsFromReloc (symBase : String → Option Int) (P : Params) :
    Nat → Lcmd → List Shape → List Item
  | off, instr :: body, sh :: shs =>
      match remoteSym instr.li_i with
      | some f =>
          { bytes := encCall32 (relocDisp symBase off f),
            dec := some (.call (wrap32 (relocDisp symBase off f))),
            label := none, target := none }
            :: itemsFromReloc symBase P (off + 5) body shs
      | none =>
          { bytes := P.encAt off instr.li_i, dec := sh.dec (P.dispAt off instr.li_i),
            label := labelOf instr.li_i, target := sh.target }
            :: itemsFromReloc symBase P (off + P.lenAt off instr.li_i) body shs
  | _, _, _ => []

theorem itemBytes_itemsFromReloc (symBase : String → Option Int) (P : Params) {body : Lcmd}
    {shs : List Shape}
    (h : List.Forall₂ (fun instr sh => RelocShapeOK P instr.li_i sh) body shs) :
    ∀ off, itemBytes (itemsFromReloc symBase P off body shs)
      = encodeFromReloc symBase P off body := by
  induction h with
  | nil => intro off; rfl
  | @cons instr sh _ _ hab _ ih =>
    intro off
    unfold RelocShapeOK at hab
    cases hr : remoteSym instr.li_i with
    | none =>
      simp only [itemsFromReloc, encodeFromReloc, hr, itemBytes, List.flatMap_cons]
      exact congrArg _ (ih _)
    | some f =>
      rw [hr] at hab
      obtain ⟨ra, l, hi⟩ := hab
      simp only [itemsFromReloc, encodeFromReloc, hr, itemBytes, List.flatMap_cons]
      rw [hi]
      exact congrArg _ (ih _)

theorem itemsFromReloc_ok (symBase : String → Option Int) (P : Params) {body : Lcmd}
    {shs : List Shape}
    (h : List.Forall₂ (fun instr sh => RelocShapeOK P instr.li_i sh) body shs) :
    ∀ off, ∀ it ∈ itemsFromReloc symBase P off body shs, ItemOK it := by
  induction h with
  | nil => intro off it hit; cases hit
  | @cons instr sh _ _ hab _ ih =>
    intro off it hit
    unfold RelocShapeOK at hab
    cases hr : remoteSym instr.li_i with
    | none =>
      rw [hr] at hab
      simp only [itemsFromReloc, hr, List.mem_cons] at hit
      rcases hit with rfl | hit
      · exact hab _
      · exact ih _ it hit
    | some f =>
      simp only [itemsFromReloc, hr, List.mem_cons] at hit
      rcases hit with rfl | hit
      · exact ItemOK_of_decode fun rest => decodeLinstr_call32_wrap _ rest
      · exact ih _ it hit

/-- The item list of a function that saves no register by `push`, under the relocating
    encoder: the frame `leaq`, the body, the closing `leaq`, `ret`. -/
def fundefItemsReloc (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List Shape) : List Item :=
  mkLea (-(Int.ofNat P.frame))
    :: (itemsFromReloc symBase P 0 body shs ++ [mkLea (Int.ofNat P.frame), mkRet])

/-- The function bytes of the relocating encoder are the bytes of `fundefItemsReloc`. -/
theorem encodeLfundefBytesReloc_eq_itemBytes (symBase : String → Option Int) (body : Lcmd)
    (shs : List Shape) (hsaves : calleeSavedToSave body = [])
    (hsh : List.Forall₂
      (fun instr sh => RelocShapeOK (Params.ofBody body) instr.li_i sh) body shs) :
    encodeLfundefBytesReloc symBase body
      = itemBytes (fundefItemsReloc symBase (Params.ofBody body) body shs) := by
  have hb := itemBytes_itemsFromReloc symBase (Params.ofBody body) hsh 0
  have hfr : (Params.ofBody body).frame = frameSize body := rfl
  simp only [itemBytes] at hb
  simp [encodeLfundefBytesReloc, fundefItemsReloc, hsaves, itemBytes, mkLea, mkRet,
    encodeLcmdReloc_eq_encodeFromReloc, hb, hfr]

theorem fundefItemsReloc_ok (symBase : String → Option Int) (P : Params) (body : Lcmd)
    (shs : List Shape) (hF0 : P.frame ≠ 0) (hF : P.frame < 2 ^ 31)
    (hsh : List.Forall₂ (fun instr sh => RelocShapeOK P instr.li_i sh) body shs) :
    ∀ it ∈ fundefItemsReloc symBase P body shs, ItemOK it := by
  intro it hit
  simp only [fundefItemsReloc, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hit
  rcases hit with rfl | hit | rfl | rfl
  · exact mkLea_ok _ (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [dispOk32, Int.ofNat_eq_natCast, decide_eq_true_eq]; omega)
  · exact itemsFromReloc_ok symBase P hsh 0 it hit
  · exact mkLea_ok _ (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [dispOk32, Int.ofNat_eq_natCast, decide_eq_true_eq]; omega)
  · exact mkRet_ok

/-- **The displacement of a remote call lands on the symbol.** For a symbol whose base is
    `L - pre` (`pre` the bytes in front of the body) and a call at body offset `off`, the
    byte offset `pre + off + 5` of the end of the call plus the decoded displacement is
    `L`, when `L` fits a signed 32-bit displacement. -/
theorem relocDisp_lands (symBase : String → Option Int) (f : String) (L pre off : Nat)
    (hsym : symBase f = some (Int.ofNat L - Int.ofNat pre)) (hL : L < 2 ^ 31)
    (hend : pre + off + 5 ≤ L) :
    ((pre + off + 5 : Nat) : Int) + wrap32 (relocDisp symBase off f) = (L : Int) := by
  have hd : relocDisp symBase off f = (L : Int) - (pre : Int) - ((off + 5 : Nat) : Int) := by
    simp only [relocDisp, hsym, Int.ofNat_eq_natCast]
  rw [hd, wrap32_of_dispOk32 _ (by
    simp only [dispOk32, decide_eq_true_eq]; omega)]
  omega

/-! ## 3. Resolution of an item list in front of a callee block -/

/-- The target of a call item: the pair `(k, L)` for a call without target label, the
    position of the label's definition in `all` otherwise. -/
def callTgt (all : List Item) (k L : Nat) (it : Item) : Option (Nat × Nat) :=
  match it.target with
  | none => some (k, L)
  | some l => labelPos l 0 0 all

/-- The program an item list denotes in front of a block whose first instruction has
    index `k`: a call without target label is `call k`; every other branch carries the
    index of the instruction following its target label's definition. -/
def expectedReloc (all : List Item) (k L : Nat) : List Item → Option (List RInstr)
  | [] => some []
  | it :: rest =>
      match it.dec with
      | none => expectedReloc all k L rest
      | some (.op i) => (expectedReloc all k L rest).map (.op i :: ·)
      | some .ret => (expectedReloc all k L rest).map (.ret :: ·)
      | some (.push r) => (expectedReloc all k L rest).map (.push r :: ·)
      | some (.pop r) => (expectedReloc all k L rest).map (.pop r :: ·)
      | some (.jcc cc _) =>
          match it.target.bind (fun l => labelPos l 0 0 all) with
          | some (j, _) => (expectedReloc all k L rest).map (.jcc cc j :: ·)
          | none => none
      | some (.call _) =>
          match callTgt all k L it with
          | some (j, _) => (expectedReloc all k L rest).map (.call j :: ·)
          | none => none

/-- Well-formedness of the branches of `items`, laid out from offset `off` inside `all`,
    in front of a block at byte offset `L`: a call without target label ends, with its
    displacement added, on `L`; every other branch satisfies the condition of
    `LprogBytesDecode.branchOK`. -/
def branchOKReloc (all : List Item) (k L : Nat) : Nat → List Item → Bool
  | _, [] => true
  | off, it :: rest =>
      (match it.dec with
        | some (.jcc _ d) =>
            match it.target.bind (fun l => labelPos l 0 0 all) with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && decide (j < decCount all)
            | none => false
        | some (.call d) =>
            match callTgt all k L it with
            | some (j, t) =>
                decide ((t : Int) = ((off + it.bytes.length : Nat) : Int) + d)
                  && (it.target.isNone || decide (j < decCount all))
            | none => false
        | _ => true)
      && branchOKReloc all k L (off + it.bytes.length) rest

/-- The definition of a label of `all` is found, in the layout of `all` followed by any
    layout, at the index of the instruction that follows it. -/
theorem findIdx?_label_append (all : List Item) (hok : ∀ it ∈ all, ItemOK it)
    (ys : List (Nat × Nat × DInstr)) (l : LLabel) (j t : Nat)
    (hl : labelPos l 0 0 all = some (j, t)) (hj : j < decCount all) (q : Int)
    (hq : (t : Int) = q) :
    (layoutAt 0 all ++ ys).findIdx? (fun z => decide ((z.1 : Int) = q)) = some j := by
  obtain ⟨y, hy⟩ : ∃ y, (layoutAt 0 all)[j]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by rw [layoutAt_length]; exact hj)⟩
  have hy1 : y.1 = t := (layoutAt_labelPos l all hok 0 0 j t hl).2 y (by simpa using hy)
  have hfind := findIdx?_of_pairwise _ (layoutAt_pairwise all hok 0) j y hy
  rw [hy1, hq] at hfind
  simp [List.findIdx?_append, hfind]

/-- Resolving the layout of `items` inside the layout of `all` followed by a layout `ys`
    in which byte offset `L` has index `k` yields the program `items` denotes. -/
theorem resolveAll_layout_reloc (all : List Item) (hok : ∀ it ∈ all, ItemOK it)
    (ys : List (Nat × Nat × DInstr)) (k L : Nat)
    (hcross : ∀ q : Int, q = (L : Int) →
      (layoutAt 0 all ++ ys).findIdx? (fun z => decide ((z.1 : Int) = q)) = some k) :
    ∀ items off, branchOKReloc all k L off items = true →
      resolveAll (layoutAt 0 all ++ ys) (layoutAt off items) = expectedReloc all k L items := by
  intro items
  induction items with
  | nil => intro off _; rfl
  | cons it rest ih =>
    intro off hbr
    simp only [branchOKReloc, Bool.and_eq_true] at hbr
    obtain ⟨hhead, htail⟩ := hbr
    have ih' := ih _ htail
    cases hdec : it.dec with
    | none => simpa [layoutAt, expectedReloc, hdec] using ih'
    | some x =>
      cases x with
      | op i => simp [layoutAt, expectedReloc, hdec, resolveAll, ih']
      | ret => simp [layoutAt, expectedReloc, hdec, resolveAll, ih']
      | push r => simp [layoutAt, expectedReloc, hdec, resolveAll, ih']
      | pop r => simp [layoutAt, expectedReloc, hdec, resolveAll, ih']
      | jcc cc d =>
        rw [hdec] at hhead
        simp only at hhead
        cases htgt : it.target.bind (fun l => labelPos l 0 0 all) with
        | none => rw [htgt] at hhead; simp at hhead
        | some p =>
          obtain ⟨j, t⟩ := p
          rw [htgt] at hhead
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hhead
          obtain ⟨ht, hj⟩ := hhead
          obtain ⟨l, _, hl⟩ :
              ∃ l, it.target = some l ∧ labelPos l 0 0 all = some (j, t) := by
            cases htg : it.target with
            | none => rw [htg] at htgt; simp at htgt
            | some l => exact ⟨l, rfl, by simpa [htg] using htgt⟩
          have hfind := findIdx?_label_append all hok ys l j t hl hj _ ht
          simp only [layoutAt, expectedReloc, hdec, resolveAll, htgt, hfind, ih']
      | call d =>
        rw [hdec] at hhead
        simp only at hhead
        cases htgt : callTgt all k L it with
        | none => rw [htgt] at hhead; simp at hhead
        | some p =>
          obtain ⟨j, t⟩ := p
          rw [htgt] at hhead
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hhead
          obtain ⟨ht, hj⟩ := hhead
          have hfind : (layoutAt 0 all ++ ys).findIdx?
              (fun z => decide ((z.1 : Int)
                = ((off + it.bytes.length : Nat) : Int) + d)) = some j := by
            cases htg : it.target with
            | none =>
              simp only [callTgt, htg, Option.some.injEq, Prod.mk.injEq] at htgt
              obtain ⟨rfl, rfl⟩ := htgt
              exact hcross _ ht.symm
            | some l =>
              simp only [callTgt, htg] at htgt
              simp only [htg, Option.isNone_some, Bool.false_eq_true, false_or] at hj
              exact findIdx?_label_append all hok ys l j t htgt hj _ ht
          simp only [layoutAt, expectedReloc, hdec, resolveAll, htgt, hfind, ih']

/-- The layout of a nonempty stream starts with an instruction at the stream's start
    offset. -/
theorem decodeAt_head_start (n off : Nat) (bs : List (BitVec 8))
    (xs : List (Nat × Nat × DInstr)) (hne : bs ≠ []) (h : decodeAt n off bs = some xs) :
    ∃ e x tl, xs = (off, e, x) :: tl := by
  have hemp : bs.isEmpty = false := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b t => rfl
  cases n with
  | zero => simp [decodeAt, hemp] at h
  | succ n =>
    rw [decodeAt] at h
    simp only [hemp, Bool.false_eq_true, if_false] at h
    cases hd : decodeLinstr bs with
    | none => simp [hd] at h
    | some p =>
      obtain ⟨x, r⟩ := p
      simp only [hd, Option.map_eq_some_iff] at h
      obtain ⟨tl, _, rfl⟩ := h
      exact ⟨_, _, _, rfl⟩

/-- **Decoding of an item list followed by its callee block.** Let `items` satisfy
    `ItemOK` and `branchOKReloc` at their own instruction count and byte length, and let
    the nonempty stream `cb` decode to `q`. The concatenated stream decodes to the
    program `prog` of the items followed by `q` with its targets raised by `prog.length`;
    a call without target label is `call prog.length` in `prog`, the index of the first
    instruction of `q` in the result. -/
theorem decodeLprog_items_linked (items : List Item) (hok : ∀ it ∈ items, ItemOK it)
    (cb : List (BitVec 8)) (q prog : List RInstr)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc items (decCount items) (itemBytes items).length 0 items = true)
    (hP : expectedReloc items (decCount items) (itemBytes items).length items = some prog) :
    prog.length = decCount items ∧
      decodeLprog (itemBytes items ++ cb) = some (prog ++ shiftProg prog.length q) := by
  unfold decodeLprog at hcb
  obtain ⟨xs₂, hd, hr⟩ := Option.bind_eq_some_iff.mp hcb
  obtain ⟨e, x, tl, rfl⟩ := decodeAt_head_start _ _ _ _ hne hd
  have hlt : ∀ z ∈ layoutAt 0 items, z.1 < (itemBytes items).length := fun z hz => by
    simpa using layoutAt_start_lt items hok 0 z hz
  have h₁ : resolveAll
      (layoutAt 0 items ++ offsetLayout (itemBytes items).length ((0, e, x) :: tl))
      (layoutAt 0 items) = some prog := by
    rw [resolveAll_layout_reloc items hok _ (decCount items) (itemBytes items).length
      (fun q hq => ?_) items 0 hbr]
    · exact hP
    · have := findIdx?_offset_append (layoutAt 0 items) ((0, e, x) :: tl)
        (itemBytes items).length 0 0 q hlt (by simpa using hq) (by simp [List.findIdx?_cons])
      simpa [layoutAt_length] using this
  have hlen : prog.length = decCount items := by
    rw [← layoutAt_length items 0]
    exact ((resolveAll_eq_some_iff _ _ _).mp h₁).length_eq.symm
  refine ⟨hlen, ?_⟩
  rw [hlen]
  exact decodeLprog_append_resolved items hok cb _ prog q hd hr h₁

/-! ## 4. The relocating function encoder in front of its callee -/

/-- **Decoding of a relocated function followed by its callee.** Let `body` save no
    register by `push`, have a nonzero frame below `2 ^ 31`, and consist of remote calls
    and instructions with shapes. Let its item list satisfy `branchOKReloc` at its own
    instruction count and byte length and denote `prog`, and let the nonempty stream `cb`
    decode to `q`. Then `encodeLfundefBytesReloc symBase body ++ cb` decodes to `prog`
    followed by `q` with its targets raised by `prog.length`, and each remote call of
    `body` is `call prog.length` in `prog`. -/
theorem decodeLprog_fundefReloc_append (symBase : String → Option Int) (body : Lcmd)
    (shs : List Shape) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hF : frameSize body < 2 ^ 31)
    (hsh : List.Forall₂
      (fun instr sh => RelocShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = true)
    (hP : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = some prog) :
    prog.length = decCount (fundefItemsReloc symBase (Params.ofBody body) body shs) ∧
      decodeLprog (encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ shiftProg prog.length q) := by
  have hbytes := encodeLfundefBytesReloc_eq_itemBytes symBase body shs hsaves hsh
  rw [hbytes] at hbr hP ⊢
  exact decodeLprog_items_linked _
    (fundefItemsReloc_ok symBase (Params.ofBody body) body shs hF0 hF hsh) cb q prog hcb hne
    hbr hP

/-! ## 5. The run of the linked bytes -/

/-- **A caller linked with its callee, over bytes.** Under the hypotheses of
    `decodeLprog_fundefReloc_append`, with `q` a block without `call`, a run of the
    decoded caller `prog` from index `0` under the oracle of the leaky runs of `q` at the
    target `prog.length` is a run through calls of the program the linked bytes decode
    to. -/
theorem haltsC_fundefReloc_linked (r : DoitRegime) (symBase : String → Option Int)
    (body : Lcmd) (shs : List Shape) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hF : frameSize body < 2 ^ 31)
    (hsh : List.Forall₂
      (fun instr sh => RelocShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = true)
    (hP : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body shs)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body shs))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsReloc symBase (Params.ofBody body) body shs) = some prog)
    (hq : ∀ tg, RInstr.call tg ∉ q) {s s' : AState}
    (h : HaltsO aMachine (oracleAt prog.length (runOf r q)) prog 0 s s') :
    ∃ linked, decodeLprog (encodeLfundefBytesReloc symBase body ++ cb) = some linked ∧
      HaltsC aMachine linked 0 s s' :=
  ⟨_, (decodeLprog_fundefReloc_append symBase body shs cb q prog hsaves hF0 hF hsh hcb hne
      hbr hP).2, haltsC_append_of_haltsO_runOf r prog q hq h⟩

/-! ## 6. The decoded program of a relocated body, instruction by instruction -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (aMachine_step_op)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrFrame (bodyNamesI stepA_congr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (labelAt isLabelB condPol)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem

/-- The program of two item lists, one after the other, in front of a callee block. -/
theorem expectedReloc_append (all : List Item) (k L : Nat) :
    ∀ (xs ys : List Item), expectedReloc all k L (xs ++ ys)
      = (expectedReloc all k L xs).bind fun a => (expectedReloc all k L ys).map (a ++ ·) := by
  intro xs
  induction xs with
  | nil => intro ys; cases h : expectedReloc all k L ys <;> simp [expectedReloc, h]
  | cons it xs ih =>
    intro ys
    rw [List.cons_append, expectedReloc, expectedReloc]
    split
    · exact ih ys
    · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
    · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
    · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
    · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
    · split
      · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
      · rfl
    · split
      · rw [ih ys]; cases expectedReloc all k L xs <;> cases expectedReloc all k L ys <;> simp
      · rfl

/-- The program of an item list has one instruction for each item that decodes. -/
theorem expectedReloc_length (all : List Item) (k L : Nat) :
    ∀ (xs : List Item) (A : List RInstr), expectedReloc all k L xs = some A →
      A.length = decCount xs := by
  intro xs
  induction xs with
  | nil =>
    intro A h
    obtain rfl := Option.some.inj h
    rfl
  | cons it xs ih =>
    intro A h
    rw [expectedReloc] at h
    split at h
    · rename_i hd
      rw [decCount, hd, ih A h]
      simp
    all_goals
      rename_i hd
      first
        | (obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h
           rw [decCount, hd, List.length_cons, ih A' hA']
           simp [Nat.add_comm])
        | (split at h
           · obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h
             rw [decCount, hd, List.length_cons, ih A' hA']
             simp [Nat.add_comm]
           · cases h)

/-- **The program around a run of items.** The program of `xs ++ (ms ++ ys)` is the program
    of `xs`, of length `decCount xs`, the program of `ms`, and the program of `ys`. -/
theorem expectedReloc_mid (all : List Item) (k L : Nat) (xs ms ys : List Item)
    (prog : List RInstr) (h : expectedReloc all k L (xs ++ (ms ++ ys)) = some prog) :
    ∃ A X B, expectedReloc all k L ms = some X ∧ expectedReloc all k L ys = some B
      ∧ prog = A ++ X ++ B ∧ A.length = decCount xs := by
  rw [expectedReloc_append, Option.bind_eq_some_iff] at h
  obtain ⟨A, hA, h⟩ := h
  obtain ⟨R, hR, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [expectedReloc_append, Option.bind_eq_some_iff] at hR
  obtain ⟨X, hX, hR⟩ := hR
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp hR
  exact ⟨A, X, B, hX, hB, by rw [List.append_assoc], expectedReloc_length all k L xs A hA⟩

/-- The shapes of a body are single shapes `ss`, instruction by instruction. -/
theorem shapesOf_one_forall₂ (P : Params) :
    ∀ (b : Lcmd) (ss : List Shape), shapesOf P b = some (ss.map DShape.one) →
      List.Forall₂ (fun i sh => shapeOf P i.li_i = some (DShape.one sh)) b ss := by
  intro b
  induction b with
  | nil =>
    intro ss h
    cases ss with
    | nil => exact .nil
    | cons _ _ => simp [shapesOf] at h
  | cons i b ih =>
    intro ss h
    simp only [shapesOf] at h
    split at h
    · rename_i sh s' h1 h2
      cases ss with
      | nil => simp at h
      | cons s0 ss =>
        simp only [List.map_cons, Option.some.injEq, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cons h1 (ih ss h2)
    · cases h

/-- The single shapes of a body meet the shape condition of the relocating encoder. -/
theorem relocShapeOK_of_shapes (P : Params) {b : Lcmd} {ss : List Shape}
    (h : shapesOf P b = some (ss.map DShape.one)) :
    List.Forall₂ (fun i sh => RelocShapeOK P i.li_i sh) b ss := by
  refine (shapesOf_one_forall₂ P b ss h).imp fun i sh hs => ?_
  unfold RelocShapeOK
  cases hr : remoteSym i.li_i with
  | none => exact shapeOf_ok P _ _ hs
  | some f =>
    revert hs hr
    cases i.li_i with
    | Lcall ra tg =>
      obtain ⟨f', l⟩ := tg
      intro _ hr
      simp only [remoteSym] at hr
      split at hr
      · cases hr
      · obtain rfl := Option.some.inj hr
        exact ⟨ra, l, rfl⟩
    | Lgoto tg => intro hs; simp [shapeOf] at hs
    | _ => intro _ hr; simp [remoteSym] at hr

/-- The item list of a body splits at every position. -/
theorem itemsFromReloc_split (symBase : String → Option Int) (P : Params) :
    ∀ (n : Nat) (b : Lcmd) (ss : List Shape) (off : Nat), ∃ off',
      itemsFromReloc symBase P off b ss
        = itemsFromReloc symBase P off (b.take n) (ss.take n)
          ++ itemsFromReloc symBase P off' (b.drop n) (ss.drop n) := by
  intro n
  induction n with
  | zero => intro b ss off; exact ⟨off, by simp [itemsFromReloc]⟩
  | succ n ih =>
    intro b ss off
    cases b with
    | nil => exact ⟨off, by simp [itemsFromReloc]⟩
    | cons i b =>
      cases ss with
      | nil => exact ⟨off, by simp [itemsFromReloc]⟩
      | cons s ss =>
        cases hr : remoteSym i.li_i with
        | none =>
          obtain ⟨off', h⟩ := ih b ss (off + P.lenAt off i.li_i)
          exact ⟨off', by simp only [List.take_succ_cons, List.drop_succ_cons, itemsFromReloc, hr,
            List.cons_append, h]⟩
        | some f =>
          obtain ⟨off', h⟩ := ih b ss (off + 5)
          exact ⟨off', by simp only [List.take_succ_cons, List.drop_succ_cons, itemsFromReloc, hr,
            List.cons_append, h]⟩

/-- The number of decoded instructions of the item list of a body with single shapes. -/
theorem decCount_itemsFromReloc (symBase : String → Option Int) (P : Params) {b : Lcmd}
    {ss : List Shape}
    (h : List.Forall₂ (fun i sh => shapeOf P i.li_i = some (DShape.one sh)) b ss) :
    ∀ off, decCount (itemsFromReloc symBase P off b ss)
      = ((ss.map DShape.one).map nOf).sum := by
  induction h with
  | nil => intro off; rfl
  | @cons i sh _ _ hab _ ih =>
    intro off
    cases hr : remoteSym i.li_i with
    | none =>
      simp only [itemsFromReloc, hr, decCount, ih, List.map_cons, List.sum_cons]
      cases sh <;> simp [Shape.dec, nOf]
    | some f =>
      simp only [itemsFromReloc, hr, decCount, ih, List.map_cons, List.sum_cons]
      revert hab hr
      cases i.li_i with
      | Lcall ra tg =>
        intro hab _
        simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hab
        subst hab
        simp [nOf]
      | _ => simp [remoteSym, shapeOf]

/-- No item of a body without a definition of the label `l` defines `l`. -/
theorem itemsFromReloc_noLabel (symBase : String → Option Int) (P : Params) (l : LLabel) :
    ∀ (b : Lcmd) (ss : List Shape) (off : Nat), (∀ i ∈ b, isLabelB l i.li_i = false) →
      ∀ it ∈ itemsFromReloc symBase P off b ss, it.label ≠ some l := by
  intro b
  induction b with
  | nil => intro ss off _ it hit; simp [itemsFromReloc] at hit
  | cons i b ih =>
    intro ss off hb it hit
    cases ss with
    | nil => simp [itemsFromReloc] at hit
    | cons s ss =>
      cases hr : remoteSym i.li_i with
      | none =>
        simp only [itemsFromReloc, hr, List.mem_cons] at hit
        rcases hit with rfl | hit
        · intro he
          have := (isLabelB_iff l i.li_i).mpr he
          rw [hb i (by simp)] at this
          cases this
        · exact ih ss _ (fun j hj => hb j (by simp [hj])) it hit
      | some f =>
        simp only [itemsFromReloc, hr, List.mem_cons] at hit
        rcases hit with rfl | hit
        · simp
        · exact ih ss _ (fun j hj => hb j (by simp [hj])) it hit

/-- **A label resolves, in the relocated item list, to the decoded index of its first
    definition.** -/
theorem labelPos_fundefItemsReloc (symBase : String → Option Int) {body : Lcmd}
    {ss : List Shape}
    (hs : shapesOf (Params.ofBody body) body = some (ss.map DShape.one)) {l : LLabel} {p : Nat}
    (hp : labelAt body l = some p) :
    ∃ off, labelPos l 0 0 (fundefItemsReloc symBase (Params.ofBody body) body ss)
      = some (posOf (ss.map DShape.one) p, off) := by
  have hR := shapesOf_one_forall₂ _ body ss hs
  obtain ⟨hpl, hlab, hbefore⟩ := labelAt_spec hp
  have hlab' := (isLabelB_iff l _).mp hlab
  have hlen : body.length = ss.length := hR.length_eq
  obtain ⟨off', hsplit⟩ := itemsFromReloc_split symBase (Params.ofBody body) p body ss 0
  have hpre : ∀ i ∈ body.take p, isLabelB l i.li_i = false := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hi
    simp only [List.length_take] at hq
    simpa using hbefore q (by omega)
  have hrem : remoteSym body[p].li_i = none := by
    revert hlab'
    cases body[p].li_i <;> simp [labelOf, remoteSym]
  rw [List.drop_eq_getElem_cons hpl, List.drop_eq_getElem_cons (by omega : p < ss.length)]
    at hsplit
  unfold fundefItemsReloc
  rw [hsplit]
  simp only [labelPos, mkLea, reduceCtorEq, if_false, Option.isSome_some, if_true]
  rw [List.append_assoc, labelPos_append_of_ne _ _ _
    (itemsFromReloc_noLabel symBase _ l _ _ _ hpre),
    decCount_itemsFromReloc symBase _ (List.forall₂_take p hR)]
  simp only [itemsFromReloc, hrem, List.cons_append, labelPos, hlab', if_true]
  simp only [posOf, List.map_take, Option.some.injEq, Prod.mk.injEq]
  exact ⟨_, trivial, rfl⟩

/-- The facts of a printed body with remote calls that the byte simulation reads: single
    shapes `ss`, the closing return, every other instruction a remote transfer or in the
    covered fragment `DecodePrintedCFG.instrOKB`, and every conditional branch directly
    after a compare. -/
structure CallFacts (body : Lcmd) (ss : List Shape) : Prop where
  /-- The shapes of the body are the single shapes `ss`. -/
  shapes : shapesOf (Params.ofBody body) body = some (ss.map DShape.one)
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret
  /-- Every other instruction is a remote transfer or in the covered fragment. -/
  instr : ∀ k (hk : k + 1 < body.length),
    remoteSym (body[k]'(by omega)).li_i ≠ none
      ∨ instrOKB body (Params.ofBody body) (body[k]'(by omega)).li_i = true
  /-- Every conditional branch follows a compare. -/
  cond : ∀ k, k < body.length → condPrevB body k = true

/-- The decoded program `prog` of a body with shapes `ds` in front of a callee block at
    index `K`: around an instruction of the covered fragment, `prog` holds its decoded
    instructions `DecodePrintedCFG.blkOf` from the index `DecodePrintedCFG.posOf`; the
    index of a remote transfer holds `call K`; and the index of the closing return holds
    the closing `lea` of the frame `F`, followed by `ret`. -/
structure LinkedProg (body : Lcmd) (ds : List DShape) (K F : Nat) (prog : List RInstr) :
    Prop where
  /-- The decoded instructions of an instruction of the covered fragment. -/
  blk : ∀ k (hk : k < body.length) (hs : k < ds.length),
    instrOKB body (Params.ofBody body) body[k].li_i = true →
    ∃ A B, prog = A ++ blkOf body ds ds[k] ++ B ∧ A.length = posOf ds k
  /-- The index of a remote transfer. -/
  call : ∀ k (hk : k < body.length), remoteSym body[k].li_i ≠ none →
    prog[posOf ds k]? = some (.call K)
  /-- The closing `lea` and `ret`. -/
  fin : prog[posOf ds (body.length - 1)]? = some (.op (leaFrame (Int.ofNat F)))
    ∧ prog[posOf ds (body.length - 1) + 1]? = some .ret

/-- **The decoded program of a relocated body.** For a body with the facts `CallFacts`,
    the program its relocated item list denotes in front of a callee block at index `K`
    satisfies `LinkedProg` at `K`. -/
theorem linkedProg_of_items (symBase : String → Option Int) {body : Lcmd} {ss : List Shape}
    (hF : CallFacts body ss) (K L : Nat) (prog : List RInstr)
    (hP : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body ss) K L
      (fundefItemsReloc symBase (Params.ofBody body) body ss) = some prog) :
    LinkedProg body (ss.map DShape.one) K (Params.ofBody body).frame prog := by
  have hR := shapesOf_one_forall₂ _ body ss hF.shapes
  have hlen : body.length = ss.length := hR.length_eq
  have hshk : ∀ k (hk : k < body.length) (hs : k < ss.length),
      shapeOf (Params.ofBody body) body[k].li_i = some (DShape.one ss[k]) := by
    intro k hk hs
    have := (shapesOf_spec _ body _ hF.shapes).2 k hk (by simpa using hs)
    simpa using this
  -- the program around position `k`
  have hpos : ∀ k (hk : k < body.length) (hs : k < ss.length), ∃ off A X B,
      expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body ss) K L
          (itemsFromReloc symBase (Params.ofBody body) off [body[k]] [ss[k]]) = some X
        ∧ prog = A ++ X ++ B ∧ A.length = posOf (ss.map DShape.one) k := by
    intro k hk hs
    obtain ⟨off, hsplit⟩ := itemsFromReloc_split symBase (Params.ofBody body) k body ss 0
    rw [List.drop_eq_getElem_cons hk, List.drop_eq_getElem_cons hs] at hsplit
    obtain ⟨off2, h1⟩ := itemsFromReloc_split symBase (Params.ofBody body) 1
      (body[k] :: body.drop (k + 1)) (ss[k] :: ss.drop (k + 1)) off
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
      at h1
    have hP' : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body ss) K L
        ((mkLea (-(Int.ofNat (Params.ofBody body).frame))
            :: itemsFromReloc symBase (Params.ofBody body) 0 (body.take k) (ss.take k))
          ++ (itemsFromReloc symBase (Params.ofBody body) off [body[k]] [ss[k]]
            ++ (itemsFromReloc symBase (Params.ofBody body) off2 (body.drop (k + 1))
                (ss.drop (k + 1))
              ++ [mkLea (Int.ofNat (Params.ofBody body).frame), mkRet]))) = some prog := by
      rw [← hP]
      congr 1
      rw [fundefItemsReloc, hsplit, h1]
      simp only [List.cons_append, List.append_assoc]
    obtain ⟨A, X, B, hX, -, hprog, hA⟩ := expectedReloc_mid _ K L _ _ _ prog hP'
    refine ⟨off, A, X, B, hX, hprog, ?_⟩
    rw [hA, decCount, decCount_itemsFromReloc symBase _ (List.forall₂_take k hR)]
    simp [posOf, mkLea, List.map_take]
  refine ⟨fun k hk hs hok => ?_, fun k hk hr => ?_, ?_⟩
  · have hs' : k < ss.length := by omega
    obtain ⟨off, A, X, B, hX, hprog, hA⟩ := hpos k hk hs'
    have hsh := hshk k hk hs'
    refine ⟨A, B, ?_, hA⟩
    rw [hprog, List.getElem_map]
    congr 2
    revert hX hsh hok
    rcases body[k] with ⟨ii, li⟩
    cases li with
    | Lopn ds o ss' =>
      intro _ hX hsh
      rcases shapeOfBytes_ok (bs := encodeLopn _ _ (.Lopn ds o ss') _) hsh with
        ⟨q, he, -, -⟩ | ⟨pcs, he, -, -⟩
      · simp only [DShape.one.injEq] at he
        rw [he] at hX ⊢
        simp only [itemsFromReloc, remoteSym, Shape.dec, expectedReloc, Option.map_some,
          Option.some.injEq] at hX
        rw [← hX]
        simp [blkOf, DShape.ops']
      · cases he
    | Llabel kd l =>
      intro _ hX hsh
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hsh
      rw [← hsh] at hX ⊢
      simp only [itemsFromReloc, remoteSym, Shape.dec, expectedReloc, Option.some.injEq] at hX
      rw [← hX]
      simp [blkOf, DShape.ops']
    | Lcond c l =>
      cases c with
      | reg cc =>
        intro hok hX hsh
        simp only [instrOKB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨-, p, hp⟩ := hok
        obtain ⟨o, ho⟩ := labelPos_fundefItemsReloc symBase hF.shapes hp
        simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at hsh
        rw [← hsh] at hX ⊢
        simp only [itemsFromReloc, remoteSym, Shape.dec, Shape.target, expectedReloc,
          Option.bind_some, ho, Option.map_some, Option.some.injEq] at hX
        rw [← hX]
        simp [blkOf, hp]
      | _ => intro hok; simp [instrOKB] at hok
    | _ => intro hok; simp [instrOKB] at hok
  · have hs' : k < ss.length := by omega
    obtain ⟨off, A, X, B, hX, hprog, hA⟩ := hpos k hk hs'
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hr
    simp only [itemsFromReloc, hf, expectedReloc, callTgt, Option.map_some,
      Option.some.injEq] at hX
    rw [hprog, ← hX, ← hA]
    simp
  · have hn : body.length - 1 < ss.length := by have := hF.pos; omega
    have hP' : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body ss) K L
        ((mkLea (-(Int.ofNat (Params.ofBody body).frame))
            :: itemsFromReloc symBase (Params.ofBody body) 0 body ss)
          ++ ([mkLea (Int.ofNat (Params.ofBody body).frame)] ++ [mkRet])) = some prog := by
      rw [← hP]
      rfl
    obtain ⟨A, X, B, hX, hB, hprog, hA⟩ := expectedReloc_mid _ K L _ _ _ prog hP'
    have hlast : nOf ((ss.map DShape.one)[body.length - 1]'(by simpa using hn)) = 0 := by
      have h1 := hshk (body.length - 1) (by have := hF.pos; omega) hn
      rw [hF.last] at h1
      simp only [shapeOf, Option.some.injEq, DShape.one.injEq] at h1
      rw [List.getElem_map, ← h1]
      rfl
    have hposL : posOf (ss.map DShape.one) (body.length - 1) = A.length := by
      have h2 : posOf (ss.map DShape.one) body.length
          = posOf (ss.map DShape.one) (body.length - 1) := by
        have h := posOf_succ (ss.map DShape.one) (body.length - 1) (by simpa using hn)
        have e : body.length - 1 + 1 = body.length := by have := hF.pos; omega
        rw [hlast, e] at h
        exact h
      rw [← h2, hA, decCount, decCount_itemsFromReloc symBase _ hR]
      rw [posOf, List.take_of_length_le (by simp [hlen])]
      simp [mkLea]
    simp only [expectedReloc, mkLea, mkRet, Option.map_some, Option.some.injEq] at hX hB
    rw [hposL, hprog, ← hX, ← hB]
    simp [leaFrame]

/-! ## 7. The byte simulation of the steps of a relocated body -/

/-- A path of the machine followed by a run under an oracle is a run under the oracle. -/
theorem haltsO_of_reaches {σ : Type} {M : Machine σ} {O : Nat → σ → σ → Prop}
    {prog : List RInstr} {pc pc' : Nat} {s s' s'' : σ} (h : Reaches M prog pc s pc' s')
    (hr : HaltsO M O prog pc' s' s'') : HaltsO M O prog pc s s'' := by
  induction h with
  | refl => exact hr
  | next hs _ ih => exact .go hs (ih hr)

/-- The instruction after a label or a branch is no conditional branch. -/
theorem CallFacts.not_cond_next {body : Lcmd} {ss : List Shape} (hF : CallFacts body ss)
    {k : Nat} (hk : k + 1 < body.length) (h : classifyA (body[k]'(by omega)).li_i = none) :
    isCondB (body[k + 1]'hk).li_i = false := by
  have hc := hF.cond (k + 1) hk
  unfold condPrevB at hc
  rw [List.getElem?_eq_getElem hk] at hc
  revert hc
  rcases hb : body[k + 1] with ⟨ii, li⟩
  cases li <;> simp [isCondB, List.getElem?_eq_getElem (show k < body.length by omega), h]

/-- **One step of the address machine on a relocated body, on the decoded program.** Let
    the body have the facts `CallFacts` and `prog` satisfy `LinkedProg`, and let `frame`
    agree with the frame of the body parameters at the names of the body. A step of the
    address machine, from an address state that corresponds to a byte state `sA` with the
    zero flag of a conditional branch and whose indexed load reads outside the red-zone
    word, reaches an address state at a position of the body that corresponds to a byte
    state `sA'` with the zero flag of a conditional branch, and the machine has a path on
    `prog` from the index of the start on `sA` to the index of the reached position on
    `sA'`. -/
theorem linked_step {body : Lcmd} {ss : List Shape} (hF : CallFacts body ss) {K : Nat}
    {prog : List RInstr}
    (hL : LinkedProg body (ss.map DShape.one) K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (sa : LstateA) (zf : Bool) (sa' : LstateA) (zf' : Bool) (sA : AState)
    (hsafe : LoadSafeAt rsp body sa)
    (hst : VIR.JasminLsemAddrRun.stepA frame body sa zf = some (sa', zf'))
    (hc : ACorr rsp sA sa)
    (hz : ∀ bi, body[sa.reg.lpc]? = some bi → isCondB bi.li_i = true →
      sA.flags.zf.getD false = zf) :
    ∃ sA', ACorr rsp sA' sa' ∧ sa'.reg.lpc < body.length
      ∧ (∀ bi, body[sa'.reg.lpc]? = some bi → isCondB bi.li_i = true →
          sA'.flags.zf.getD false = zf')
      ∧ Reaches aMachine prog (posOf (ss.map DShape.one) sa.reg.lpc) sA
          (posOf (ss.map DShape.one) sa'.reg.lpc) sA' := by
  rw [stepA_congr hfr] at hst
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body _ hF.shapes
  cases hb : body[sa.reg.lpc]? with
  | none => simp [VIR.JasminLsemAddrRun.stepA, hb] at hst
  | some bi =>
    obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
    have hkn : sa.reg.lpc + 1 < body.length := by
      by_contra hn
      have e : sa.reg.lpc = body.length - 1 := by omega
      have h1 := hF.last
      rw [(List.getElem?_eq_some_iff.mp (e ▸ hb)).2] at h1
      obtain ⟨ii, li⟩ := bi
      simp only at h1
      subst h1
      simp [VIR.JasminLsemAddrRun.stepA, hb] at hst
    have hok0 := hF.instr sa.reg.lpc hkn
    have hshk := hsh sa.reg.lpc hk (by omega)
    rw [hbk] at hok0 hshk
    have hnext : ∀ (sA' : AState) (bi' : Linstr),
        classifyA bi.li_i = none → body[sa.reg.lpc + 1]? = some bi' →
        isCondB bi'.li_i = true → sA'.flags.zf.getD false = zf' := by
      intro sA' bi' hcl hb' hcnd
      have := hF.not_cond_next hkn (by rw [hbk]; exact hcl)
      rw [(List.getElem?_eq_some_iff.mp hb').2, hcnd] at this
      cases this
    obtain ⟨ii, li⟩ := bi
    cases li with
    | Lopn dsts o srcs =>
      have hokI : instrOKB body (Params.ofBody body) (.Lopn dsts o srcs) = true :=
        hok0.resolve_left (fun h => h rfl)
      have hok := hokI
      simp only [instrOKB] at hok
      split at hok
      · rename_i ar hcl
        have hia := classifyA_instr hcl
        have hli := AArm.li_eq hok
        have hsafeA : ar.LoadSafe rsp sa := by
          cases ar with
          | ldx D B' I =>
            intro p vi hp hvi
            exact hsafe ii D B' I (by rw [hb, ← hia]; rfl) p vi hp hvi
          | _ => trivial
        obtain ⟨s', z', hst', hc', hzf'⟩ :=
          AArm.sim (Params.ofBody body) rsp ar hok sA sa zf hc hsafeA
        have hstep : VIR.JasminLsemAddrRun.stepA (frameP (Params.ofBody body) rsp) body sa zf
            = some (s', z') := by
          simp only [VIR.JasminLsemAddrRun.stepA, hb]
          rw [← hia, AArm.tagAt_eq, hli]
          exact hst'
        obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (hstep.symm.trans hst))
        subst e1
        subst e2
        have hpc' : s'.reg.lpc = sa.reg.lpc + 1 := fstepA_lpc _ _ _ _ _ _ hst'
        refine ⟨aMachine.runBlock sA (ar.js (Params.ofBody body)), hc',
          by rw [hpc']; exact hkn, ?_, ?_⟩
        · intro bi' hb' hcnd
          rw [hpc'] at hb'
          have hc2 := hF.cond (sa.reg.lpc + 1) hkn
          unfold condPrevB at hc2
          rw [hb'] at hc2
          obtain ⟨ii', li'⟩ := bi'
          revert hc2 hcnd
          cases li' <;> simp [isCondB, hb, hcl]
          exact hzf'
        · obtain ⟨A, B, hsplit, hA⟩ := hL.blk sa.reg.lpc hk (by omega) (by rw [hbk]; exact hokI)
          obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := ss.map DShape.one) hshk
          have hops : ((ss.map DShape.one)[sa.reg.lpc]'(by omega)).ops'
              = ar.js (Params.ofBody body) := AArm.shape_ops hok (by rw [hia]; exact hshk)
          rw [hblk, hops] at hsplit
          have h0 := reaches_ops aMachine A (ar.js (Params.ofBody body)) B sA
          rw [← hsplit, hA] at h0
          rw [hpc', posOf_succ _ sa.reg.lpc (by omega), hn, hops]
          exact h0
      · cases hok
    | Llabel kd l =>
      have hstep : VIR.JasminLsemAddrRun.stepA (frameP (Params.ofBody body) rsp) body sa zf
          = some (sa.setLpc (sa.reg.lpc + 1), zf) := by
        unfold VIR.JasminLsemAddrRun.stepA
        rw [hb]
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (hstep.symm.trans hst))
      subst e1
      subst e2
      refine ⟨sA, acorr_setLpc hc _, hkn, fun bi' hb' hcnd => hnext sA bi' rfl hb' hcnd, ?_⟩
      show Reaches aMachine prog (posOf (ss.map DShape.one) sa.reg.lpc) sA
        (posOf (ss.map DShape.one) (sa.reg.lpc + 1)) sA
      have hsk : (ss.map DShape.one)[sa.reg.lpc]'(by omega) = .one .skip := by
        simp only [shapeOf, Option.some.injEq] at hshk
        exact hshk.symm
      rw [posOf_succ _ sa.reg.lpc (by omega), hsk]
      exact .refl _ _
    | Lcond c l =>
      cases c with
      | reg cc =>
        have hokI : instrOKB body (Params.ofBody body) (.Lcond (.reg cc) l) = true :=
          hok0.resolve_left (fun h => h rfl)
        have hok := hokI
        simp only [instrOKB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : (ss.map DShape.one)[sa.reg.lpc]'(by omega)
            = .one (.jcc (ccNibble cc) l) := by
          simp only [shapeOf, Option.some.injEq] at hshk
          exact hshk.symm
        obtain ⟨A, B, hsplit, hA⟩ := hL.blk sa.reg.lpc hk (by omega) (by rw [hbk]; exact hokI)
        have hj : prog[posOf (ss.map DShape.one) sa.reg.lpc]?
            = some (.jcc (ccNibble cc) (posOf (ss.map DShape.one) p)) := by
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sA.flags.zf.getD false = zf := hz _ hb rfl
        have hms := step_jcc_pol prog _ _ sA cc pol hpol hj
        rw [hzf] at hms
        by_cases hzp : zf = pol
        · have hstep : VIR.JasminLsemAddrRun.stepA (frameP (Params.ofBody body) rsp) body sa zf
              = some (sa.setLpc p, zf) := by
            unfold VIR.JasminLsemAddrRun.stepA
            rw [hb]
            simp [hpol, hzp, hp]
          obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (hstep.symm.trans hst))
          subst e1
          subst e2
          rw [if_pos hzp] at hms
          refine ⟨sA, acorr_setLpc hc _, hpl, fun bi' hb' hcnd => ?_, .single hms⟩
          have hb'' : body[p]? = some bi' := hb'
          rw [← (List.getElem?_eq_some_iff.mp hb'').2] at hcnd
          revert hlabp hcnd
          rcases body[p] with ⟨ii', li'⟩
          cases li' <;> simp [isCondB, isLabelB]
        · have hstep : VIR.JasminLsemAddrRun.stepA (frameP (Params.ofBody body) rsp) body sa zf
              = some (sa.setLpc (sa.reg.lpc + 1), zf) := by
            unfold VIR.JasminLsemAddrRun.stepA
            rw [hb]
            simp [hpol, hzp]
          obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (hstep.symm.trans hst))
          subst e1
          subst e2
          rw [if_neg hzp] at hms
          refine ⟨sA, acorr_setLpc hc _, hkn, fun bi' hb' hcnd => hnext sA bi' rfl hb' hcnd, ?_⟩
          show Reaches aMachine prog (posOf (ss.map DShape.one) sa.reg.lpc) sA
            (posOf (ss.map DShape.one) (sa.reg.lpc + 1)) sA
          rw [posOf_succ _ sa.reg.lpc (by omega), hsk]
          exact .single hms
      | _ => simp [VIR.JasminLsemAddrRun.stepA, hb] at hst
    | _ => simp [VIR.JasminLsemAddrRun.stepA, hb] at hst

/-- **The closing return of a relocated body, on the decoded program**: from the index of
    the last position, `prog` runs the closing `lea` of the frame and halts at `ret`. -/
theorem linked_halt {body : Lcmd} {ss : List Shape} {K : Nat} {prog : List RInstr}
    (hL : LinkedProg body (ss.map DShape.one) K (Params.ofBody body).frame prog)
    (O : Nat → AState → AState → Prop) (sa : LstateA) (sA : AState)
    (hend : sa.reg.lpc + 1 = body.length) :
    HaltsO aMachine O prog (posOf (ss.map DShape.one) sa.reg.lpc) sA
      (evalInstrA sA (leaFrame (Int.ofNat (Params.ofBody body).frame))) := by
  have e : sa.reg.lpc = body.length - 1 := by omega
  rw [e]
  exact .go (aMachine_step_op prog _ sA _ hL.fin.1) (.ret hL.fin.2)

/-- **A call of a relocated body, on the decoded program**: the index of a call holds
    `call K`, and the index of the next position is the next index. -/
theorem linked_call {body : Lcmd} {ss : List Shape} (hF : CallFacts body ss) {K : Nat}
    {prog : List RInstr}
    (hL : LinkedProg body (ss.map DShape.one) K (Params.ofBody body).frame prog)
    (p : Nat) (bi : Linstr) (ra : Option String) (t : String × LLabel)
    (hb : body[p]? = some bi) (hbi : bi.li_i = .Lcall ra t) :
    prog[posOf (ss.map DShape.one) p]? = some (.call K)
      ∧ posOf (ss.map DShape.one) (p + 1) = posOf (ss.map DShape.one) p + 1 := by
  obtain ⟨hk, hbk⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body _ hF.shapes
  have hkn : p + 1 < body.length := by
    by_contra hn
    have e : p = body.length - 1 := by omega
    have h1 := hF.last
    rw [(List.getElem?_eq_some_iff.mp (e ▸ hb)).2, hbi] at h1
    cases h1
  have hrem : remoteSym body[p].li_i ≠ none := by
    rcases hF.instr p hkn with h | h
    · exact h
    · rw [hbk, hbi] at h
      simp [instrOKB] at h
  refine ⟨hL.call p hk hrem, ?_⟩
  have h1 := hsh p hk (by omega)
  rw [hbk, hbi] at h1
  obtain ⟨f, l⟩ := t
  simp only [shapeOf, Option.some.injEq] at h1
  rw [posOf_succ _ p (by omega), ← h1]
  rfl

/-- The facts `CallFacts` of a body from its single shapes, its closing return, the
    condition on every other instruction, and the check of the conditional branches. -/
theorem callFacts_of_checks {body : Lcmd} {ss : List Shape}
    (hs : shapesOf (Params.ofBody body) body = some (ss.map DShape.one))
    (hlast : body.getLast?.any (fun r => isRetB r.li_i) = true)
    (hall : ∀ i ∈ body.dropLast,
      remoteSym i.li_i ≠ none ∨ instrOKB body (Params.ofBody body) i.li_i = true)
    (hcond : (List.range body.length).all (condPrevB body) = true) : CallFacts body ss := by
  simp only [Option.any_eq_true] at hlast
  obtain ⟨r, hlast, hret⟩ := hlast
  have hpos : 0 < body.length := by
    cases body with
    | nil => simp at hlast
    | cons _ _ => simp
  refine ⟨hs, hpos, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    obtain rfl := Option.some.inj hlast
    revert hret
    unfold isRetB
    split <;> simp_all
  · exact hall _ (by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩)
  · exact List.all_eq_true.mp hcond k (List.mem_range.mpr hk)

/-- The end of the run of a relocated body: the byte state is the state after the closing
    `lea` of the frame `F`, from a byte state that corresponds to the address state. -/
def FinLea (rsp : BitVec 64) (F : Nat) (sa : LstateA) (sA' : AState) : Prop :=
  ∃ sA, ACorr rsp sA sa ∧ sA' = evalInstrA sA (leaFrame (Int.ofNat F))

/-- **The byte simulation of the segments of a relocated body.** Let the body have the
    facts `CallFacts`, `prog` satisfy `LinkedProg` at the index `K`, and `frame` agree
    with the frame of the body parameters at the names of the body. Under every oracle
    `O`, with the index `DecodePrintedCFG.posOf` of a position:

    * a step of the address machine, from an address state that corresponds to a byte
      state with the zero flag of a conditional branch and whose indexed load reads
      outside the red-zone word, reaches an address state at a position of the body that
      corresponds to a byte state with the zero flag of a conditional branch, and every
      run under `O` from the index of the reached position extends to a run from the
      index of the start;
    * at the closing return there is a run under `O` to a byte state that satisfies
      `FinLea` with the address state;
    * the index of a call holds `call K`, and the index of the position after a call is
      the index after the call. -/
theorem linked_seg {body : Lcmd} {ss : List Shape} (hF : CallFacts body ss) {K : Nat}
    {prog : List RInstr}
    (hL : LinkedProg body (ss.map DShape.one) K (Params.ofBody body).frame prog)
    (rsp : BitVec 64) {frame : String → Option (BitVec 64)}
    (hfr : ∀ q ∈ bodyNamesI body, frame q = frameP (Params.ofBody body) rsp q)
    (O : Nat → AState → AState → Prop) :
    (∀ sa zf sa' zf' sA, LoadSafeAt rsp body sa →
        VIR.JasminLsemAddrRun.stepA frame body sa zf = some (sa', zf') → ACorr rsp sA sa →
        (∀ bi, body[sa.reg.lpc]? = some bi → isCondB bi.li_i = true →
          sA.flags.zf.getD false = zf) →
        ∃ sA', ACorr rsp sA' sa' ∧ sa'.reg.lpc < body.length
          ∧ (∀ bi, body[sa'.reg.lpc]? = some bi → isCondB bi.li_i = true →
              sA'.flags.zf.getD false = zf')
          ∧ ∀ s'', HaltsO aMachine O prog (posOf (ss.map DShape.one) sa'.reg.lpc) sA' s'' →
              HaltsO aMachine O prog (posOf (ss.map DShape.one) sa.reg.lpc) sA s'')
      ∧ (∀ sa sA, sa.reg.lpc + 1 = body.length → ACorr rsp sA sa →
          ∃ sA', HaltsO aMachine O prog (posOf (ss.map DShape.one) sa.reg.lpc) sA sA'
            ∧ FinLea rsp (Params.ofBody body).frame sa sA')
      ∧ (∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
          prog[posOf (ss.map DShape.one) p]? = some (.call K))
      ∧ (∀ p bi ra t, body[p]? = some bi → bi.li_i = .Lcall ra t →
          posOf (ss.map DShape.one) (p + 1) = posOf (ss.map DShape.one) p + 1) := by
  refine ⟨fun sa zf sa' zf' sA hsafe hst hc hz => ?_, fun sa sA hend hc => ?_,
    fun p bi ra t hb hbi => (linked_call hF hL p bi ra t hb hbi).1,
    fun p bi ra t hb hbi => (linked_call hF hL p bi ra t hb hbi).2⟩
  · obtain ⟨sA', hc', hlen, hz', hR⟩ := linked_step hF hL rsp hfr sa zf sa' zf' sA hsafe hst hc hz
    exact ⟨sA', hc', hlen, hz', fun s'' hr => haltsO_of_reaches hR hr⟩
  · exact ⟨_, linked_halt hL O sa sA hend, sA, hc, rfl⟩

/-- **The decoded program of the linked bytes of a relocated body.** Under the hypotheses
    of `decodeLprog_fundefReloc_append` on a body with the facts `CallFacts`, the linked
    bytes decode to `prog` followed by the callee block, and `prog` satisfies `LinkedProg`
    at the index `prog.length` of the first instruction of the callee. -/
theorem linkedProg_of_bytes (symBase : String → Option Int) {body : Lcmd} {ss : List Shape}
    (hF : CallFacts body ss) (cb : List (BitVec 8)) (q prog : List RInstr)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : frameSize body ≠ 0) (hFr : frameSize body < 2 ^ 31)
    (hcb : decodeLprog cb = some q) (hne : cb ≠ [])
    (hbr : branchOKReloc (fundefItemsReloc symBase (Params.ofBody body) body ss)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body ss))
      (encodeLfundefBytesReloc symBase body).length 0
      (fundefItemsReloc symBase (Params.ofBody body) body ss) = true)
    (hP : expectedReloc (fundefItemsReloc symBase (Params.ofBody body) body ss)
      (decCount (fundefItemsReloc symBase (Params.ofBody body) body ss))
      (encodeLfundefBytesReloc symBase body).length
      (fundefItemsReloc symBase (Params.ofBody body) body ss) = some prog) :
    decodeLprog (encodeLfundefBytesReloc symBase body ++ cb)
        = some (prog ++ shiftProg prog.length q)
      ∧ LinkedProg body (ss.map DShape.one) prog.length (Params.ofBody body).frame prog := by
  obtain ⟨hlen, hdec⟩ := decodeLprog_fundefReloc_append symBase body ss cb q prog hsaves hF0
    hFr (relocShapeOK_of_shapes _ hF.shapes) hcb hne hbr hP
  refine ⟨hdec, ?_⟩
  rw [hlen]
  exact linkedProg_of_items symBase hF _ _ prog hP

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
