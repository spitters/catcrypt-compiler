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

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc
