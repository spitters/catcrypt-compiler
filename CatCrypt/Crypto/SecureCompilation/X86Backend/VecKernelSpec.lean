/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig
public import CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit

@[expose] public section

set_option autoImplicit false

/-!
# A vector kernel given as text meets the callee specification

The text `VectorizeEmit.vectorizeEmit` returns for a straight-line scalar program `c` is
run on the machine `VecMach.x86VecMach` as the block of operations `VecMach.blockOfText` of
its parsed program, followed by `vzeroupper` and `ret`.

The regions of a kernel are the `inLen` bytes at `%rsi` (input), the `stride * nOut` bytes
at `%rdi` (output) and the `F` bytes below `%rsp` (frame). `framedB` is the check of the
parsed program against the regions: every load from the input lies in it, every store to
the output is at a multiple of the store width inside it, and the stack accesses and the
moves of `%rsp` keep the frame discipline `VecMach.TextFramed` inside `F` bytes. The
validator of the text does not bound the store offsets, so the theorems are conditional on
this check.

From a state whose regions are pairwise disjoint (`KernelRegions`) and whose input region
holds lane-wise the parameters of `c` (`LaneInputs`), the block ends in a state where
output `j` holds lane-wise the value of output `j` of `c` (`LaneOutputs`), `%rsp` and every
register but `%rax` have their entry values, and every byte outside the output region and
the frame is unchanged; the leakage is a function of the entry values of `%rsi`, `%rdi`
and `%rsp`. `kernelRun` is the callee of the block, from any vector state to any vector
state, and it meets the signature `kernelSig`.

## Main results

* `framedB`, `framedB_sound`: the frame check of a parsed text, and its soundness.
* `KernelRegions`, `kernelSep_of_regions`: disjoint regions give the separation
  `VecMach.KernelSep`.
* `block_of_textRun`: the block of a framed text against a run of the text model: outputs,
  registers and memory.
* `vectorKernel_block`: the block of the text of `vectorizeEmit` computes the scalar
  program lane-wise, keeps the registers and the memory outside its regions, and leaks a
  function of the three pointers.
* `kernelRun`, `kernelSig`: the callee of a kernel block and its signature.
* `calleeSpec_of_parsed`: the callee of the parsed text of `vectorizeEmit` meets
  `kernelSig`, given the frame check.
* `vectorKernel_calleeSpec`: the same from the text alone: it parses, and every block of
  its parsed program that passes the frame check meets `kernelSig`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmRenderValidated
open CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode MState lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AMem AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec
  InFrame)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The frame check -/

/-- The input offset `off` is the offset of a vector inside `inLen` bytes. -/
def InOff (m : Mode) (inLen off : Nat) : Prop := off + m.stride ≤ inLen

/-- The output offset `o` is the offset of one of `nOut` output vectors. -/
def OutOff (m : Mode) (nOut o : Nat) : Prop := m.stride ∣ o ∧ o < m.stride * nOut

/-- The check of an instruction with `dp` bytes of a frame of `F` bytes allocated:
    `VecMach.InstrFits` at the input region of `inLen` bytes and `nOut` output vectors. -/
def fitsB (m : Mode) (inLen nOut F dp : Nat) : ZmmTextModel.Instr → Bool
  | .ldIn off _ => decide (off + m.stride ≤ inLen)
  | .st _ off => decide (m.stride ∣ off) && decide (off < m.stride * nOut)
  | .ldS off _ => decide (m.stride ∣ off) && decide (off + m.stride ≤ dp)
  | .stS _ off => decide (m.stride ∣ off) && decide (off + m.stride ≤ dp)
  | .spSub n => decide (m.stride ∣ n) && decide (dp + n ≤ F)
  | .spAdd n => decide (m.stride ∣ n) && decide (n ≤ dp)
  | _ => true

/-- **The frame check of a parsed text**: every instruction passes `fitsB`, from `dp`
    allocated bytes, and nothing is allocated at the end. -/
def framedB (m : Mode) (inLen nOut F : Nat) : Nat → List ZmmTextModel.Instr → Bool
  | dp, [] => dp == 0
  | dp, i :: is => fitsB m inLen nOut F dp i && framedB m inLen nOut F (depthStep dp i) is

theorem fitsB_sound {m : Mode} {inLen nOut F dp : Nat}
    {i : ZmmTextModel.Instr}
    (h : fitsB m inLen nOut F dp i = true) :
    InstrFits m (InOff m inLen) (OutOff m nOut) F dp i := by
  cases i <;> first
    | trivial
    | simpa [fitsB, InstrFits, InOff, OutOff] using h

/-- **Soundness of the frame check.** -/
theorem framedB_sound {m : Mode} {inLen nOut F : Nat} :
    ∀ (prog : List ZmmTextModel.Instr) (dp : Nat), framedB m inLen nOut F dp prog = true →
      TextFramed m (InOff m inLen) (OutOff m nOut) F dp prog
  | [], dp, h => by
    show dp = 0
    simpa [framedB] using h
  | i :: is, dp, h => by
    simp only [framedB, Bool.and_eq_true] at h
    exact ⟨fitsB_sound h.1, framedB_sound is _ h.2⟩

/-! ## 2. Disjoint regions -/

/-- The `la` bytes from `a` and the `lb` bytes from `b` have no address in common. -/
def Apart (a : BitVec 64) (la : Nat) (b : BitVec 64) (lb : Nat) : Prop :=
  ∀ i < la, ∀ j < lb, a + BitVec.ofNat 64 i ≠ b + BitVec.ofNat 64 j

theorem add_toNat_sub (x y : BitVec 64) : x + BitVec.ofNat 64 (y - x).toNat = y := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  have := y.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
  omega

/-- Two vectors inside disjoint regions are disjoint. -/
theorem sepBytes_of_apart {n la lb : Nat} {a b : BitVec 64} {o i : Nat}
    (h : Apart a la b lb) (ho : o + n ≤ la) (hi : i + n ≤ lb) :
    SepBytes n (a + BitVec.ofNat 64 o) (b + BitVec.ofNat 64 i) := by
  constructor
  · refine Nat.le_of_not_lt fun hlt => h
      (o + (b + BitVec.ofNat 64 i - (a + BitVec.ofNat 64 o)).toNat) (by omega) i (by omega) ?_
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, add_toNat_sub]
  · refine Nat.le_of_not_lt fun hlt => h o (by omega)
      (i + (a + BitVec.ofNat 64 o - (b + BitVec.ofNat 64 i)).toNat) (by omega) ?_
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, add_toNat_sub]

/-- **The regions of a kernel at its entry state**: the `stride * nOut` bytes at `%rdi`,
    the `inLen` bytes at `%rsi` and the `F` bytes below `%rsp` are pairwise disjoint, and
    the output region and the frame have at most `2 ^ 64` bytes each. -/
structure KernelRegions (m : Mode) (inLen nOut F : Nat) (sa : AState) : Prop where
  out_in : Apart (sa.regs "%rdi") (m.stride * nOut) (sa.regs "%rsi") inLen
  out_frm : Apart (sa.regs "%rdi") (m.stride * nOut) (sa.regs "%rsp" - BitVec.ofNat 64 F) F
  frm_in : Apart (sa.regs "%rsp" - BitVec.ofNat 64 F) F (sa.regs "%rsi") inLen
  out_le : m.stride * nOut ≤ 2 ^ 64
  frm_le : F ≤ 2 ^ 64

theorem stride_pos (m : Mode) : 0 < m.stride := by
  cases m <;> decide

theorem outOff_le {m : Mode} {nOut o : Nat} (h : OutOff m nOut o) :
    o + m.stride ≤ m.stride * nOut := by
  cases m <;> simp only [OutOff, Mode.stride, Mode.act, Nat.reduceDiv] at h ⊢ <;> omega

/-- A vector of the frame as an offset from the low end of the frame. -/
theorem slot_eq (e : BitVec 64) {F p : Nat} (hp : p ≤ F) :
    e - BitVec.ofNat 64 p = e - BitVec.ofNat 64 F + BitVec.ofNat 64 (F - p) := by
  rw [sub_ofNat_add_ofNat _ (Nat.sub_le F p), Nat.sub_sub_self hp]

/-- **Disjoint regions give the separation of the vectors.** -/
theorem kernelSep_of_regions {m : Mode} {inLen nOut F : Nat} {sa : AState}
    (h : KernelRegions m inLen nOut F sa) :
    KernelSep m (InOff m inLen) (OutOff m nOut) F (sa.regs "%rsi") (sa.regs "%rdi")
      (sa.regs "%rsp") where
  out_in := fun _ _ ho hi => sepBytes_of_apart h.out_in (outOff_le ho) hi
  out_out := fun o o' ho ho' hne => by
    have hle := h.out_le
    have := (sa.regs "%rdi").isLt
    cases m <;>
      simp only [OutOff, Mode.stride, Mode.act, Nat.reduceDiv, SepBytes, BitVec.toNat_sub,
        BitVec.toNat_add, BitVec.toNat_ofNat] at ho ho' hle ⊢ <;> omega
  out_frm := fun o p ho hp => by
    rw [slot_eq _ hp.2.2]
    exact sepBytes_of_apart h.out_frm (outOff_le ho) (by have := hp.2.1; have := hp.2.2; omega)
  frm_in := fun p i hp hi => by
    rw [slot_eq _ hp.2.2]
    exact sepBytes_of_apart h.frm_in (by have := hp.2.1; have := hp.2.2; omega) hi
  frm_le := h.frm_le

/-- A byte of an output vector is a byte of the output region. -/
theorem outOff_foot {m : Mode} {nOut o : Nat} (di a : BitVec 64) (h : OutOff m nOut o)
    (ha : (a - (di + BitVec.ofNat 64 o)).toNat < m.stride) :
    (a - di).toNat < m.stride * nOut := by
  have := di.isLt
  have := a.isLt
  cases m <;>
    simp only [OutOff, Mode.stride, Mode.act, Nat.reduceDiv, BitVec.toNat_sub,
      BitVec.toNat_add, BitVec.toNat_ofNat] at h ha ⊢ <;> omega

/-- A byte of a vector of the frame is a byte of the frame. -/
theorem frameSlot_foot {m : Mode} {F p : Nat} (e a : BitVec 64) (hF : F ≤ 2 ^ 64)
    (h : FrameSlot m F p) (ha : (a - (e - BitVec.ofNat 64 p)).toNat < m.stride) :
    InFrame e F a := by
  obtain ⟨-, h1, h2⟩ := h
  have := e.isLt
  have := a.isLt
  unfold InFrame
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    at ha ⊢
  omega

/-! ## 3. The block of a framed text -/

variable (r : DoitRegime)

/-- **The block of a framed text against a run of the text model.** Let the parsed
    program pass the frame check, let the regions be disjoint at the state `s`, and let
    the text model run from `textInit` on the input region `memInput`. Then the program
    has a block of operations, and after it each value the model stored at an output
    offset is the vector of memory there, `%rsp` and every register but `%rax` have their
    entry values, and every byte outside the output region and the frame is unchanged. -/
theorem block_of_textRun {m : Mode} {prog : List ZmmTextModel.Instr}
    {ro : Std.HashMap String (Array (BitVec 64))} {inLen nOut F : Nat}
    (hfr : framedB m inLen nOut F 0 prog = true) (s : AState × VState)
    (hreg : KernelRegions m inLen nOut F s.1) {σ' : MState}
    (hrun : ZmmTextModel.run m (memInput m s.1) ro (textInit m s) prog = some σ') :
    ∃ ops, blockOfText m ro prog = some ops
      ∧ (∀ j < nOut, ∀ y, σ'.outAt (m.stride * j) = some y →
          readBytes m.stride ((x86VecMach r m).runBlock s ops).1.mem
            (s.1.regs "%rdi" + BitVec.ofNat 64 (m.stride * j)) = y)
      ∧ ((x86VecMach r m).runBlock s ops).1.regs "%rsp" = s.1.regs "%rsp"
      ∧ (∀ x, x ≠ "%rax" → ((x86VecMach r m).runBlock s ops).1.regs x = s.1.regs x)
      ∧ ∀ a, ¬ (a - s.1.regs "%rdi").toNat < m.stride * nOut →
          ¬ InFrame (s.1.regs "%rsp") F a →
          ((x86VecMach r m).runBlock s ops).1.mem a = s.1.mem a := by
  obtain ⟨ops, hops⟩ := blockOfText_of_run m prog _ _ hrun
  have hK := runBlock_textInit r m s (kernelSep_of_regions hreg) (framedB_sound _ _ hfr) hops
    hrun
  have hsp : ((x86VecMach r m).runBlock s ops).1.regs "%rsp" = s.1.regs "%rsp" := by
    simpa using hK.rsp
  refine ⟨ops, hops, ?_, hsp, ?_, ?_⟩
  · intro j hj y hy
    exact hK.out _ y ⟨Dvd.intro _ rfl, (Nat.mul_lt_mul_left (stride_pos m)).mpr hj⟩ hy
  · intro x hx
    by_cases hx' : x = "%rsp"
    · rw [hx']
      exact hsp
    · exact hK.keep x hx' hx
  · intro a ha1 ha2
    exact hK.mem a (fun o ho hlt => ha1 (outOff_foot _ a ho hlt))
      (fun p hp hlt => ha2 (frameSlot_foot _ a hreg.frm_le hp hlt))

/-! ## 4. The kernel theorem -/

/-- **The input region holds the parameters lane-wise.** For each active lane `k`, the
    lane `k` of the vector of memory at the offset of each parameter of the scalar program
    is the value of the parameter in the valuation `Vs k`, at most `B` when
    `inBound = some B`. -/
def LaneInputs (V : VecShape) (inOffset : Nat → Nat) (inBound : Option Nat) {Γ : JCtxt}
    (Vs : Nat → Ctxt.Valuation Γ) (sa : AState) : Prop :=
  (∀ B, inBound = some B → ∀ k < V.mode.act / V.laneW.bits,
    ∀ v : Ctxt.Var Γ (.reg V.laneW.bits), (v.lookup (Vs k)).toNat ≤ B) ∧
  (∀ k < V.mode.act / V.laneW.bits, ∀ v : Ctxt.Var Γ (.reg V.laneW.bits),
    lane V.laneW.bits (memInput V.mode sa (inOffset (varDepth v))) k = v.lookup (Vs k))

/-- **The output region holds the outputs lane-wise.** For each output `j < nOut` and each
    active lane `k`, the lane `k` of the vector of the memory of `sa'` at offset
    `stride * j` from the entry value of `%rdi` is the value of binding
    `nBinds c - nOut + j` of the scalar run of `c` from `Vs k`. -/
def LaneOutputs (V : VecShape) (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) (Vs : Nat → Ctxt.Valuation Γ) (sa sa' : AState) : Prop :=
  ∀ j < nOut, ∀ k < V.mode.act / V.laneW.bits, ∃ x,
    (bindWords V.laneW.bits (Vs k) c)[nBinds c - nOut + j]? = some (some x) ∧
    lane V.laneW.bits (readBytes V.mode.stride sa'.mem
      (sa.regs "%rdi" + BitVec.ofNat 64 (V.mode.stride * j))) k = x

/-- **The kernel theorem.** When `vectorizeEmit V` returns `text` for the scalar program
    `c`, the text parses to a program `prog` with data table `ro`, and for every input
    length `inLen` and frame size `F` at which `prog` passes the frame check, from every
    state `s` with disjoint regions whose input region holds lane-wise the parameters
    `Vs`, the program has a block of operations `ops` on `x86VecMach` after which:

    1. the output region holds lane-wise the outputs of `c` on `Vs`;
    2. `%rsp` has its entry value;
    3. every register but `%rax` has its entry value;
    4. every byte outside the output region and the frame has its entry value;
    5. the leakage of the block is its leakage from every state with the same `%rsi`,
       `%rdi` and `%rsp`. -/
theorem vectorKernel_block (V : VecShape) {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : vectorizeEmit V sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse V.mode text = .ok (prog, ro) ∧
      ∀ (inLen F : Nat), framedB V.mode inLen nOut F 0 prog = true →
      ∀ (Vs : Nat → Ctxt.Valuation Γ) (s : AState × VState),
        KernelRegions V.mode inLen nOut F s.1 → LaneInputs V inOffset inBound Vs s.1 →
        ∃ ops, blockOfText V.mode ro prog = some ops
          ∧ LaneOutputs V nOut c Vs s.1 ((x86VecMach r V.mode).runBlock s ops).1
          ∧ ((x86VecMach r V.mode).runBlock s ops).1.regs "%rsp" = s.1.regs "%rsp"
          ∧ (∀ x, x ≠ "%rax" →
              ((x86VecMach r V.mode).runBlock s ops).1.regs x = s.1.regs x)
          ∧ (∀ a, ¬ (a - s.1.regs "%rdi").toNat < V.mode.stride * nOut →
              ¬ InFrame (s.1.regs "%rsp") F a →
              ((x86VecMach r V.mode).runBlock s ops).1.mem a = s.1.mem a)
          ∧ ∀ s₂ : AState × VState, s.1.regs "%rsi" = s₂.1.regs "%rsi" →
              s.1.regs "%rdi" = s₂.1.regs "%rdi" → s.1.regs "%rsp" = s₂.1.regs "%rsp" →
              (x86VecMach r V.mode).blockLeak s ops = (x86VecMach r V.mode).blockLeak s₂ ops := by
  obtain ⟨-, -, prog, ro, hp, hsound⟩ := vectorizeEmit_sound V h
  refine ⟨prog, ro, hp, fun inLen F hfr Vs s hreg hin => ?_⟩
  obtain ⟨σ', hrun, hout⟩ :=
    hsound Vs (memInput V.mode s.1) hin.1 hin.2 (textInit V.mode s) rfl
  obtain ⟨ops, hops, ho, hsp, hkeep, hmem⟩ := block_of_textRun r hfr s hreg hrun
  refine ⟨ops, hops, ?_, hsp, hkeep, hmem,
    fun s₂ h1 h2 h3 => blockLeak_blockOfText_congr r V.mode prog ops s s₂ hops h1 h2 h3⟩
  intro j hj k hk
  obtain ⟨y, hy, hl⟩ := hout j hj
  obtain ⟨x, hx, hxl⟩ := hl k hk
  exact ⟨x, hx, by rw [ho j hj y hy]; exact hxl⟩

/-! ## 5. The callee -/

/-- The scalar state after a block followed by `vzeroupper` is the scalar state after the
    block. -/
theorem runBlock_zeroUpper_fst (m : Mode) :
    ∀ (ops : List (JInstr 64 ⊕ VInstr)) (s : AState × VState),
      ((x86VecMach r m).runBlock s (ops ++ [.inr .zeroUpper])).1 =
        ((x86VecMach r m).runBlock s ops).1
  | [], _ => rfl
  | _ :: ops, _ => runBlock_zeroUpper_fst m ops _

/-- `vzeroupper` after a block adds no leakage. -/
theorem blockLeak_zeroUpper (m : Mode) :
    ∀ (ops : List (JInstr 64 ⊕ VInstr)) (s : AState × VState),
      (x86VecMach r m).blockLeak s (ops ++ [.inr .zeroUpper]) =
        (x86VecMach r m).blockLeak s ops
  | [], _ => rfl
  | o :: ops, s => congrArg ((x86VecMach r m).opLeak s o ++ ·) (blockLeak_zeroUpper m ops _)

/-- **The callee of a kernel block**: the runs with leakage of the block followed by
    `vzeroupper` and `ret`, from the entry state with any vector state to the return state
    with any vector state. -/
def kernelRun (m : Mode) (ops : List (JInstr 64 ⊕ VInstr)) : CalleeRun :=
  fun s t s' => ∃ v v' : VState,
    (x86VecMach r m).RunL (fun _ _ => True) (lineProg (ops ++ [.inr .zeroUpper])) 0 (s, v) t
      (s', v')

/-- The runs of `kernelRun` are the block: the return state is the scalar state after the
    block from some vector state, and the trace is the leakage of the block. -/
theorem kernelRun_iff (m : Mode) (ops : List (JInstr 64 ⊕ VInstr)) (s : AState)
    (t : List CTLeak) (s' : AState) :
    kernelRun r m ops s t s' ↔ ∃ v : VState,
      s' = ((x86VecMach r m).runBlock (s, v) ops).1 ∧
        t = (x86VecMach r m).blockLeak (s, v) ops := by
  constructor
  · rintro ⟨v, v', hX⟩
    obtain ⟨-, ht, he⟩ := (runL_lineProg r m _ _ _ _ _).mp hX
    refine ⟨v, ?_, ?_⟩
    · rw [← runBlock_zeroUpper_fst]
      exact congrArg Prod.fst he
    · rw [ht, blockLeak_zeroUpper]
  · rintro ⟨v, rfl, rfl⟩
    refine ⟨v, ((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).2, ?_⟩
    rw [← runBlock_zeroUpper_fst, ← blockLeak_zeroUpper]
    exact (runL_lineProg r m _ _ _ _ _).mpr ⟨IsaMachine.blockOk_true _ _ _, rfl, rfl⟩

/-- **The signature of a vector kernel** for the scalar program `c` at lane shape `V`,
    with an input region of `inLen` bytes and a frame of `F` bytes. The arguments are the
    output pointer `%rdi` and the input pointer `%rsi`; there is no result register; the
    clobber set is `%rax`; the precondition is the disjointness of the regions and an
    input region that holds parameters lane-wise; the footprint is the output region and
    the frame; the postcondition is that the output region holds lane-wise the outputs of
    `c`; two entry states are publicly related when they agree on `%rsi`, `%rdi` and
    `%rsp`. -/
def kernelSig (V : VecShape) (inOffset : Nat → Nat) (inBound : Option Nat) (nOut : Nat)
    {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (inLen F : Nat) : CalleeSig where
  args := ["RDI", "RSI"]
  res := none
  clob := fun x => x == "%rax"
  pre := fun s => KernelRegions V.mode inLen nOut F s ∧
    ∃ Vs : Nat → Ctxt.Valuation Γ, LaneInputs V inOffset inBound Vs s
  foot := fun s a =>
    (a - s.regs "%rdi").toNat < V.mode.stride * nOut ∨ InFrame (s.regs "%rsp") F a
  post := fun s s' => ∀ Vs : Nat → Ctxt.Valuation Γ, LaneInputs V inOffset inBound Vs s →
    LaneOutputs V nOut c Vs s s'
  pub := fun s₁ s₂ => s₁.regs "%rsi" = s₂.regs "%rsi" ∧ s₁.regs "%rdi" = s₂.regs "%rdi" ∧
    s₁.regs "%rsp" = s₂.regs "%rsp"

/-- **The callee of the parsed text of `vectorizeEmit` meets its signature.** Let
    `vectorizeEmit V` return `text` for `c`, let `text` parse to `prog` with data table
    `ro` and operations `ops`, and let `prog` pass the frame check at an input length
    `inLen` and a frame size `F`. Then `kernelRun` of `ops` meets `kernelSig`. -/
theorem calleeSpec_of_parsed (V : VecShape) {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : vectorizeEmit V sym inOffset nOut c inBound = .ok text)
    {prog : List ZmmTextModel.Instr} {ro : Std.HashMap String (Array (BitVec 64))}
    {ops : List (JInstr 64 ⊕ VInstr)} (hp : parse V.mode text = .ok (prog, ro))
    (hops : blockOfText V.mode ro prog = some ops) {inLen F : Nat}
    (hfr : framedB V.mode inLen nOut F 0 prog = true) :
    CalleeSpec (kernelRun r V.mode ops) (kernelSig V inOffset inBound nOut c inLen F) := by
  have key : ∀ (s : AState) (v : VState) (Vs : Nat → Ctxt.Valuation Γ),
      KernelRegions V.mode inLen nOut F s → LaneInputs V inOffset inBound Vs s →
      LaneOutputs V nOut c Vs s ((x86VecMach r V.mode).runBlock (s, v) ops).1
        ∧ ((x86VecMach r V.mode).runBlock (s, v) ops).1.regs "%rsp" = s.regs "%rsp"
        ∧ (∀ x, x ≠ "%rax" →
            ((x86VecMach r V.mode).runBlock (s, v) ops).1.regs x = s.regs x)
        ∧ ∀ a, ¬ (a - s.regs "%rdi").toNat < V.mode.stride * nOut →
            ¬ InFrame (s.regs "%rsp") F a →
            ((x86VecMach r V.mode).runBlock (s, v) ops).1.mem a = s.mem a := by
    intro s v Vs hreg hin
    obtain ⟨prog', ro', hp', hk⟩ := vectorKernel_block r V h
    rw [hp] at hp'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hp')
    obtain ⟨ops', hops', h1, h2, h3, h4, -⟩ := hk inLen F hfr Vs (s, v) hreg hin
    rw [hops] at hops'
    cases hops'
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _
    exact ⟨_, _, (kernelRun_iff r V.mode ops s _ _).mpr ⟨⟨fun _ => 0, fun _ => 0⟩, rfl, rfl⟩⟩
  · rintro s t s' ⟨hreg, Vs, hin⟩ hX
    obtain ⟨v, rfl, -⟩ := (kernelRun_iff r V.mode ops s t s').mp hX
    exact (key s v Vs hreg hin).2.1
  · rintro s t s' ⟨hreg, Vs, hin⟩ hX x hx
    obtain ⟨v, rfl, -⟩ := (kernelRun_iff r V.mode ops s t s').mp hX
    exact (key s v Vs hreg hin).2.2.1 x (by simpa [kernelSig] using hx)
  · rintro s t s' ⟨hreg, Vs, hin⟩ hX a ha
    obtain ⟨v, rfl, -⟩ := (kernelRun_iff r V.mode ops s t s').mp hX
    exact (key s v Vs hreg hin).2.2.2 a (fun hlt => ha (Or.inl hlt)) (fun hf => ha (Or.inr hf))
  · rintro s t s' ⟨hreg, -⟩ hX Vs hin
    obtain ⟨v, rfl, -⟩ := (kernelRun_iff r V.mode ops s t s').mp hX
    exact (key s v Vs hreg hin).1
  · rintro s₁ s₂ t₁ t₂ s₁' s₂' - - ⟨h1, h2, h3⟩ hX₁ hX₂
    obtain ⟨v₁, -, rfl⟩ := (kernelRun_iff r V.mode ops s₁ t₁ s₁').mp hX₁
    obtain ⟨v₂, -, rfl⟩ := (kernelRun_iff r V.mode ops s₂ t₂ s₂').mp hX₂
    exact blockLeak_blockOfText_congr r V.mode prog ops (s₁, v₁) (s₂, v₂) hops h1 h2 h3

/-- **A vector kernel given as text meets the callee specification.** When
    `vectorizeEmit V` returns `text` for the scalar program `c`, the text parses, and for
    every block of operations of its parsed program and every input length and frame size
    at which the program passes the frame check, the callee of the block meets
    `kernelSig`. -/
theorem vectorKernel_calleeSpec (V : VecShape) {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : vectorizeEmit V sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse V.mode text = .ok (prog, ro) ∧
      ∀ (ops : List (JInstr 64 ⊕ VInstr)) (inLen F : Nat),
        blockOfText V.mode ro prog = some ops → framedB V.mode inLen nOut F 0 prog = true →
        CalleeSpec (kernelRun r V.mode ops) (kernelSig V inOffset inBound nOut c inLen F) := by
  obtain ⟨-, -, prog, ro, hp, -⟩ := vectorizeEmit_sound V h
  exact ⟨prog, ro, hp, fun ops inLen F hops hfr => calleeSpec_of_parsed r V h hp hops hfr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
