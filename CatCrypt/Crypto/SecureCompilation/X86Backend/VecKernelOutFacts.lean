/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLinkedFn
public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode

@[expose] public section

set_option autoImplicit false

/-!
# Facts about the linked function of a vector kernel

Three facts about `Hax.LinkedFn.ofVecOut`, the linked function of a spec-carrying vector
kernel, stated over every kernel parameter.

* The argument registers of its layout, in the upper-case names of the region back half, are
  `RDI` and `RSI`, and the array positions of its layout are the destination of
  `outWords V.mode nOut` words at position `0` and the input of `ni` words at position `1`.
* The scalar positions of the block of a kernel of `emitKernel` are well formed: the block is
  that of a parsed text that passes the frame check with a frame below `2 ^ 31` bytes
  (`VecKernelImage.frameEnc_ok_of_framed`).
* Its bytes do not decode as a scalar program: the block is closed by `vzeroupper`, whose
  table entry under a lawful table begins with the EVEX or the two-byte VEX escape byte,
  which the scalar decoder `decodeLinstr` rejects, and every scalar position in front of it
  decodes to one instruction.

## Main results

* `upperArgs_ofVecOut`, `insArrArgs_ofVecOut`: the argument names and array positions of the
  layout of `LinkedFn.ofVecOut`.
* `ofVecKernel_scalarOK`: the scalar positions of an emitted kernel are well formed.
* `decodeAt_mixedEncode_none`: a mixed stream with an encodable vector instruction, whose
  scalar positions are well formed, does not decode at any fuel.
* `decodeLprog_lineBytes_none`, `decodeLprog_ofVecOut_none`,
  `decodeLprog_ofVecOut_ofVecKernel_none`: the bytes of a kernel block do not decode as a
  scalar program.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelOutFacts

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach (VInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelEmit (emitKernel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLink
  (VecKernelCallee ofVecKernel kernelOps_of_emitKernel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelLinkedFn (VecOutSem outWords
  vecOutLayout)
open CatCrypt.Crypto.SecureCompilation.CT (DoitRegime)
open CatCrypt.Crypto.Hax (LinkedFn insArrArgs)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax (Value)

/-! ## 1. The argument names and array positions of the layout -/

/-- The upper-case name of `%rdi` with its sigil dropped is `RDI`. -/
theorem upper_rdi : (("%rdi".drop 1).toString).toUpper = "RDI" := by native_decide

/-- The upper-case name of `%rsi` with its sigil dropped is `RSI`. -/
theorem upper_rsi : (("%rsi".drop 1).toString).toUpper = "RSI" := by native_decide

variable {r : DoitRegime} {V : VecShape} {inOffset : Nat → Nat} {inBound : Option Nat}
  {nOut : Nat} {Γ : JCtxt} {t : JasminTy} {c : Com jasminDialect Γ t} {inLen F : Nat}

/-- **The argument names of the layout of a vector kernel**: the registers of the layout of
    `LinkedFn.ofVecOut`, with the sigil dropped and in upper case, are `RDI` and `RSI`. -/
theorem upperArgs_ofVecOut (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F))
    (A : VecAsm) :
    (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A).layout.args.map
      (fun a => ((a.reg.drop 1).toString).toUpper) = ["RDI", "RSI"] := by
  simp only [LinkedFn.ofVecOut, vecOutLayout, List.map_cons, List.map_nil, upper_rdi,
    upper_rsi]

/-- **The array positions of the layout of a vector kernel**: the layout of
    `LinkedFn.ofVecOut` has the destination of `outWords V.mode nOut` words at position `0`,
    the input of `ni` words at position `1`, and no array past position `1`. -/
theorem insArrArgs_ofVecOut (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F))
    (A : VecAsm) :
    insArrArgs ((LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A).layout.args.map
      (·.kind)) = fun i => if i = 0 then some (outWords V.mode nOut)
        else if i = 1 then some ni else none := by
  funext i
  rcases i with _ | _ | i <;> rfl

/-! ## 2. The scalar positions of an emitted kernel -/

/-- **The scalar positions of an emitted kernel are well formed.** For a text `emitKernel`
    returns, the position `frameEnc` gives each scalar operation of the block of
    `ofVecKernel` decodes, in front of every continuation, to that operation. -/
theorem ofVecKernel_scalarOK {sym : String} {text : String}
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text) :
    ∀ i, Sum.inl i ∈ (ofVecKernel r h).ops → ItemOK (scalarItem frameEnc i) := by
  obtain ⟨_, _, ops, -, hops, hk, -, hfr, hF⟩ := kernelOps_of_emitKernel h
  have he : (ofVecKernel r h).ops = ops := by
    simp only [ofVecKernel, hk, Option.getD_some]
  rw [he]
  exact frameEnc_ok_of_framed hops hfr hF

/-! ## 3. The bytes of a kernel block do not decode as a scalar program -/

/-- The scalar decoder rejects a stream that opens a vector instruction. -/
theorem decodeLinstr_none_of_vecHead {bs : List (BitVec 8)} (h : VecHead bs) :
    decodeLinstr bs = none := by
  cases hd : decodeLinstr bs with
  | none => rfl
  | some p => exact absurd h (not_vecHead hd)

/-- **A mixed stream with an encodable vector instruction does not decode as a scalar
    program.** Let `A` be a lawful table, let every scalar position of `prog` be well formed,
    and let `prog` hold a vector instruction with an entry in `A`. Then the scalar decoder
    `decodeAt` fails on the bytes of `prog` at every fuel and offset: it decodes the scalar
    positions in front of the first encodable vector instruction one by one and then meets
    the escape byte of its entry. -/
theorem decodeAt_mixedEncode_none {A : VecAsm} (hA : A.Lawful) :
    ∀ (prog : List (Item ⊕ VInstr)), (∀ it, Sum.inl it ∈ prog → ItemOK it) →
      (∃ v, Sum.inr v ∈ prog ∧ A.Encodable v) →
      ∀ n off, decodeAt n off (mixedEncode A prog) = none
  | [], _, ⟨_, hv, _⟩, _, _ => by simp at hv
  | .inl it :: rest, hok, ⟨v, hv, hve⟩, n, off => by
    have hrest : ∀ it, Sum.inl it ∈ rest → ItemOK it := fun it' h' =>
      hok it' (List.mem_cons_of_mem _ h')
    have hvr : Sum.inr v ∈ rest := by simpa using hv
    have ih := decodeAt_mixedEncode_none hA rest hrest ⟨v, hvr, hve⟩
    have hit := hok it List.mem_cons_self
    have he : mixedEncode A (.inl it :: rest) = it.bytes ++ mixedEncode A rest := by
      simp [mixedEncode]
    rw [he]
    unfold ItemOK at hit
    cases hdec : it.dec with
    | none =>
      rw [hdec] at hit
      rw [hit, List.nil_append]
      exact ih n off
    | some x =>
      rw [hdec] at hit
      obtain ⟨hne, hx⟩ := hit
      have hnil : (it.bytes ++ mixedEncode A rest).isEmpty = false := by
        cases hb : it.bytes with
        | nil => exact absurd hb hne
        | cons _ _ => rfl
      cases n with
      | zero => simp only [decodeAt, hnil]; rfl
      | succ n => simp only [decodeAt, hnil, hx, ih, Option.map_none]; rfl
  | .inr w :: rest, hok, ⟨v, hv, hve⟩, n, off => by
    have hrest : ∀ it, Sum.inl it ∈ rest → ItemOK it := fun it' h' =>
      hok it' (List.mem_cons_of_mem _ h')
    have he : mixedEncode A (.inr w :: rest) = A.bytes w ++ mixedEncode A rest := by
      simp [mixedEncode]
    rw [he]
    cases hw : A.enc w with
    | some bs =>
      have hb : A.bytes w = bs := by simp [VecAsm.bytes, hw]
      rw [hb]
      have hhead := hA.vecHead hw (mixedEncode A rest)
      have hnil : (bs ++ mixedEncode A rest).isEmpty = false := by
        cases hbs : bs with
        | nil => exact absurd hbs (hA.ne_nil hw)
        | cons _ _ => rfl
      cases n with
      | zero => simp only [decodeAt, hnil]; rfl
      | succ n => simp only [decodeAt, hnil, decodeLinstr_none_of_vecHead hhead]; rfl
    | none =>
      have hb : A.bytes w = [] := by simp [VecAsm.bytes, hw]
      rw [hb, List.nil_append]
      have hvr : Sum.inr v ∈ rest := by
        rcases List.mem_cons.mp hv with h | h
        · cases h
          obtain ⟨bs, hbs⟩ := hve
          rw [hw] at hbs
          cases hbs
        · exact h
      exact decodeAt_mixedEncode_none hA rest hrest ⟨v, hvr, hve⟩ n off

/-- **The bytes of a kernel block do not decode as a scalar program**, for a lawful table
    with an entry for `vzeroupper` and well-formed positions of the scalar operations of the
    block: `lineBytes` closes every block with `vzeroupper`. -/
theorem decodeLprog_lineBytes_none {A : VecAsm} (hA : A.Lawful)
    (hz : A.Encodable .zeroUpper) {enc : JInstr 64 → List (BitVec 8)}
    {ops : List (JInstr 64 ⊕ VInstr)} (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) :
    decodeLprog (lineBytes A enc ops) = none := by
  have hok' : ∀ i, Sum.inl i ∈ ops ++ [.inr .zeroUpper] → ItemOK (scalarItem enc i) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hok i hi
    · simp at hi
  have hz' : ∃ v, Sum.inr v ∈ lineItems enc (ops ++ [.inr .zeroUpper]) ∧ A.Encodable v :=
    ⟨.zeroUpper, by simp [lineItems], hz⟩
  unfold decodeLprog lineBytes
  rw [decodeAt_mixedEncode_none hA _ (lineItems_ok hok') hz' _ 0, Option.bind_none]

/-- **The bytes of the linked function of a vector kernel do not decode as a scalar
    program**, for a lawful table under which the block of the kernel is encodable and
    well-formed positions of the scalar operations of the block. -/
theorem decodeLprog_ofVecOut_none (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    (k : VecKernelCallee r V.mode (kernelSig V inOffset inBound nOut c inLen F))
    {A : VecAsm} (hA : A.Lawful) (hbe : BlockEncodable A k.ops)
    (hok : ∀ i, Sum.inl i ∈ k.ops → ItemOK (scalarItem frameEnc i)) :
    decodeLprog (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem k A).bytes = none :=
  decodeLprog_lineBytes_none hA (hbe _ (by simp)) hok

/-- **The bytes of the linked function of an emitted vector kernel do not decode as a scalar
    program**, for a lawful table under which the block of the kernel is encodable. -/
theorem decodeLprog_ofVecOut_ofVecKernel_none {sym text : String}
    (h : emitKernel V sym inOffset nOut c inLen F inBound = .ok text)
    (name outN inN : String) (ni : Nat)
    (sem : List Value → Option Value)
    (sem_res : ∀ vals v, sem vals = some v →
      (dec (.arr (outWords V.mode nOut) (.word 64)) v).isSome = true)
    (hsem : VecOutSem V inOffset inBound nOut c (outWords V.mode nOut) ni sem)
    {A : VecAsm} (hA : A.Lawful) (hbe : BlockEncodable A (ofVecKernel r h).ops) :
    decodeLprog
      (LinkedFn.ofVecOut name outN inN ni sem sem_res hsem (ofVecKernel r h) A).bytes = none :=
  decodeLprog_ofVecOut_none name outN inN ni sem sem_res hsem _ hA hbe
    (ofVecKernel_scalarOK h)

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelOutFacts
